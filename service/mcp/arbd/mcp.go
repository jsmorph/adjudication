package mcp

import (
	"bytes"
	"context"
	"crypto/rand"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/url"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
)

const (
	mcpProtocolVersion = "2025-06-18"
	serverName         = "aard"
	serverVersion      = "0.1.0"

	DefaultListenAddr             = "127.0.0.1:19800"
	DefaultSessionTTL             = 30 * time.Minute
	DefaultSessionCleanupInterval = time.Minute

	waitToolName       = "wait_for_opportunity"
	waitToolDefault    = 30 * time.Second
	waitToolMax        = 30 * time.Second
	waitToolHTTPMargin = 2 * time.Second
)

type Options struct {
	ListenAddr             string
	CaseAPIBase            string
	BearerToken            string
	APIBearerToken         string
	SessionTTL             time.Duration
	DisableSessionExpiry   bool
	SessionCleanupInterval time.Duration
	AllowedOrigins         []string
	Log                    io.Writer
}

func Run(ctx context.Context, opts Options) error {
	if ctx == nil {
		ctx = context.Background()
	}
	listen := strings.TrimSpace(opts.ListenAddr)
	if listen == "" {
		listen = DefaultListenAddr
	}
	caseAPIBase, err := normalizeCaseAPIBase(opts.CaseAPIBase)
	if err != nil {
		return fmt.Errorf("invalid caseapi-base: %w", err)
	}
	if caseAPIBase == "" {
		return fmt.Errorf("caseapi-base is required")
	}
	sessionTTL := opts.SessionTTL
	if opts.DisableSessionExpiry {
		sessionTTL = 0
	} else if sessionTTL == 0 {
		sessionTTL = DefaultSessionTTL
	}
	if sessionTTL < 0 {
		return fmt.Errorf("session-ttl must be non-negative")
	}
	sessionCleanupInterval := opts.SessionCleanupInterval
	if sessionCleanupInterval == 0 {
		sessionCleanupInterval = DefaultSessionCleanupInterval
	}
	if sessionTTL > 0 && sessionCleanupInterval <= 0 {
		return fmt.Errorf("session-cleanup-interval must be positive when session expiry is enabled")
	}
	allowedOrigins, err := allowedOriginMap(opts.AllowedOrigins)
	if err != nil {
		return err
	}
	log := opts.Log
	if log == nil {
		log = io.Discard
	}
	handler := &mcpServer{
		caseAPIBase:    caseAPIBase,
		bearerToken:    strings.TrimSpace(opts.BearerToken),
		apiBearerToken: strings.TrimSpace(opts.APIBearerToken),
		allowedOrigins: allowedOrigins,
		client:         &http.Client{Timeout: waitToolMax + waitToolHTTPMargin},
		log:            log,
		sessionTTL:     sessionTTL,
		sessions:       map[string]*mcpSession{},
	}
	ln, err := net.Listen("tcp", listen)
	if err != nil {
		return err
	}
	cleanupCtx, cancelCleanup := context.WithCancel(context.Background())
	defer cancelCleanup()
	if sessionTTL > 0 {
		go handler.expireSessionsLoop(cleanupCtx, sessionCleanupInterval)
	}
	srv := &http.Server{Handler: handler, ReadHeaderTimeout: 10 * time.Second}
	done := make(chan error, 1)
	go func() {
		<-ctx.Done()
		shutdownCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()
		done <- srv.Shutdown(shutdownCtx)
	}()
	handler.logf("aard mcp listening on http://%s/mcp", listenerDisplayAddr(ln.Addr().String()))
	err = srv.Serve(ln)
	if errors.Is(err, http.ErrServerClosed) {
		shutdownErr := <-done
		if shutdownErr != nil {
			return shutdownErr
		}
		return nil
	}
	return err
}

func allowedOriginMap(values []string) (map[string]struct{}, error) {
	origins := map[string]struct{}{}
	for _, value := range values {
		origin := strings.TrimSpace(value)
		if origin == "" {
			return nil, fmt.Errorf("origin must not be empty")
		}
		origins[origin] = struct{}{}
	}
	return origins, nil
}

type mcpServer struct {
	caseAPIBase    string
	bearerToken    string
	apiBearerToken string
	allowedOrigins map[string]struct{}
	client         *http.Client
	log            io.Writer
	sessionTTL     time.Duration

	mu       sync.Mutex
	sessions map[string]*mcpSession
}

type mcpSession struct {
	ID             string
	CaseID         string
	AssignmentType string
	RoleID         string
	MemberID       string
	CreatedAt      time.Time
	LastSeen       time.Time
}

type rpcMessage struct {
	JSONRPC string           `json:"jsonrpc"`
	ID      *json.RawMessage `json:"id,omitempty"`
	Method  string           `json:"method"`
	Params  json.RawMessage  `json:"params,omitempty"`
}

type rpcResponse struct {
	JSONRPC string           `json:"jsonrpc"`
	ID      *json.RawMessage `json:"id,omitempty"`
	Result  any              `json:"result,omitempty"`
	Error   *rpcError        `json:"error,omitempty"`
}

type rpcError struct {
	Code    int    `json:"code"`
	Message string `json:"message"`
}

type toolCallParams struct {
	Name      string         `json:"name"`
	Arguments map[string]any `json:"arguments"`
}

func normalizeCaseAPIBase(value string) (string, error) {
	base := strings.TrimRight(strings.TrimSpace(value), "/")
	if base == "" {
		return "", nil
	}
	parsed, err := url.ParseRequestURI(base)
	if err != nil {
		return "", err
	}
	if parsed.Scheme == "" || parsed.Host == "" {
		return "", fmt.Errorf("absolute URL with scheme and host required")
	}
	return base, nil
}

func listenerDisplayAddr(addr string) string {
	host, port, err := net.SplitHostPort(addr)
	if err != nil {
		return addr
	}
	if host == "" || host == "0.0.0.0" || host == "::" {
		host = "127.0.0.1"
	}
	return net.JoinHostPort(host, port)
}

func (s *mcpServer) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	if r.URL.Path == "/health" {
		w.WriteHeader(http.StatusNoContent)
		return
	}
	if r.URL.Path != "/mcp" {
		http.NotFound(w, r)
		return
	}
	if !s.authorized(r) {
		http.Error(w, "unauthorized", http.StatusUnauthorized)
		return
	}
	if !s.originAllowed(r.Header.Get("Origin")) {
		http.Error(w, "forbidden origin", http.StatusForbidden)
		return
	}
	switch r.Method {
	case http.MethodPost:
		s.handlePost(w, r)
	case http.MethodGet:
		w.Header().Set("Allow", "POST, GET, DELETE")
		http.Error(w, "server-sent event stream is not supported", http.StatusMethodNotAllowed)
	case http.MethodDelete:
		s.handleDelete(w, r)
	default:
		w.Header().Set("Allow", "POST, GET, DELETE")
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
	}
}

func (s *mcpServer) authorized(r *http.Request) bool {
	if s.bearerToken == "" {
		return true
	}
	return strings.TrimSpace(r.Header.Get("Authorization")) == "Bearer "+s.bearerToken
}

func (s *mcpServer) originAllowed(origin string) bool {
	origin = strings.TrimSpace(origin)
	if origin == "" {
		return true
	}
	if _, ok := s.allowedOrigins[origin]; ok {
		return true
	}
	parsed, err := url.Parse(origin)
	if err != nil {
		return false
	}
	host := parsed.Hostname()
	return host == "localhost" || host == "127.0.0.1" || host == "::1"
}

func (s *mcpServer) handleDelete(w http.ResponseWriter, r *http.Request) {
	sessionID := strings.TrimSpace(r.Header.Get("Mcp-Session-Id"))
	if sessionID == "" {
		http.Error(w, "Mcp-Session-Id is required", http.StatusBadRequest)
		return
	}
	s.mu.Lock()
	_, existed := s.sessions[sessionID]
	if existed {
		delete(s.sessions, sessionID)
	}
	s.mu.Unlock()
	if existed {
		s.logf("mcp_session_deleted session_id=%s reason=delete", sessionID)
	}
	w.WriteHeader(http.StatusNoContent)
}

func (s *mcpServer) handlePost(w http.ResponseWriter, r *http.Request) {
	body := http.MaxBytesReader(w, r.Body, 4*1024*1024)
	var msg rpcMessage
	dec := json.NewDecoder(body)
	dec.UseNumber()
	if err := dec.Decode(&msg); err != nil {
		writeRPC(w, rpcResponse{JSONRPC: "2.0", Error: &rpcError{Code: -32700, Message: err.Error()}})
		return
	}
	if msg.JSONRPC != "2.0" || msg.Method == "" {
		writeRPC(w, rpcResponse{JSONRPC: "2.0", ID: msg.ID, Error: &rpcError{Code: -32600, Message: "invalid JSON-RPC request"}})
		return
	}
	if msg.ID == nil {
		w.WriteHeader(http.StatusAccepted)
		return
	}
	switch msg.Method {
	case "initialize":
		s.handleInitialize(w, r, msg)
	case "ping":
		writeRPC(w, rpcResponse{JSONRPC: "2.0", ID: msg.ID, Result: map[string]any{}})
	case "tools/list":
		session, ok := s.requireSession(w, r, msg)
		if ok {
			writeRPC(w, rpcResponse{JSONRPC: "2.0", ID: msg.ID, Result: map[string]any{"tools": stableToolSpecs(session)}})
		}
	case "tools/call":
		session, ok := s.requireSession(w, r, msg)
		if !ok {
			return
		}
		result, err := s.callTool(r.Context(), session, msg.Params)
		if err != nil {
			writeRPC(w, rpcResponse{JSONRPC: "2.0", ID: msg.ID, Error: &rpcError{Code: -32602, Message: err.Error()}})
			return
		}
		writeRPC(w, rpcResponse{JSONRPC: "2.0", ID: msg.ID, Result: result})
	default:
		writeRPC(w, rpcResponse{JSONRPC: "2.0", ID: msg.ID, Error: &rpcError{Code: -32601, Message: "method not found"}})
	}
}

func (s *mcpServer) handleInitialize(w http.ResponseWriter, r *http.Request, msg rpcMessage) {
	session, err := s.newSession(r)
	if err != nil {
		writeRPC(w, rpcResponse{JSONRPC: "2.0", ID: msg.ID, Error: &rpcError{Code: -32602, Message: err.Error()}})
		return
	}
	w.Header().Set("Mcp-Session-Id", session.ID)
	writeRPC(w, rpcResponse{
		JSONRPC: "2.0",
		ID:      msg.ID,
		Result: map[string]any{
			"protocolVersion": mcpProtocolVersion,
			"capabilities":    map[string]any{"tools": map[string]any{"listChanged": false}},
			"serverInfo":      map[string]any{"name": serverName, "version": serverVersion},
			"instructions":    sessionInstructions(session),
		},
	})
}

func (s *mcpServer) newSession(r *http.Request) (*mcpSession, error) {
	query := r.URL.Query()
	caseID := strings.TrimSpace(query.Get("case_id"))
	roleID := strings.TrimSpace(query.Get("role_id"))
	memberID := strings.TrimSpace(query.Get("member_id"))
	if caseID == "" {
		return nil, fmt.Errorf("case_id query parameter is required")
	}
	if (roleID == "" && memberID == "") || (roleID != "" && memberID != "") {
		return nil, fmt.Errorf("exactly one of role_id or member_id is required")
	}
	assignmentType := "council"
	if roleID != "" {
		assignmentType = "lawyer"
		if !validRoleID(roleID) {
			return nil, fmt.Errorf("role_id must be plaintiff, defendant, or observer")
		}
	}
	sessionID, err := randomSessionID()
	if err != nil {
		return nil, err
	}
	now := time.Now()
	session := &mcpSession{
		ID:             sessionID,
		CaseID:         caseID,
		AssignmentType: assignmentType,
		RoleID:         roleID,
		MemberID:       memberID,
		CreatedAt:      now,
		LastSeen:       now,
	}
	s.mu.Lock()
	s.sessions[sessionID] = session
	s.mu.Unlock()
	s.logf("mcp_session_created session_id=%s case_id=%s assignment_type=%s principal=%s", session.ID, session.CaseID, session.AssignmentType, session.principalID())
	return session, nil
}

func validRoleID(roleID string) bool {
	switch roleID {
	case "plaintiff", "defendant", "observer":
		return true
	default:
		return false
	}
}

func sessionInstructions(session *mcpSession) string {
	return fmt.Sprintf(
		"This MCP session is bound to case_id %s and %s %s. Call wait_for_opportunity first. If it returns state waiting, call wait_for_opportunity again with after_version. If it returns state ready, read the returned prompt, turn, limits, and tools, then complete exactly that opportunity. If wait_for_opportunity returns state done or failed, stop. If it returns state error, report the error and stop.",
		session.CaseID,
		session.AssignmentType,
		session.principalID(),
	)
}

func (s *mcpServer) requireSession(w http.ResponseWriter, r *http.Request, msg rpcMessage) (*mcpSession, bool) {
	sessionID := strings.TrimSpace(r.Header.Get("Mcp-Session-Id"))
	if sessionID == "" {
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusBadRequest)
		writeRPC(w, rpcResponse{JSONRPC: "2.0", ID: msg.ID, Error: &rpcError{Code: -32600, Message: "Mcp-Session-Id is required after initialize"}})
		return nil, false
	}
	now := time.Now()
	s.mu.Lock()
	session := s.sessions[sessionID]
	expired := false
	if session != nil {
		if s.sessionTTL > 0 && !session.LastSeen.Add(s.sessionTTL).After(now) {
			delete(s.sessions, sessionID)
			session = nil
			expired = true
		} else {
			session.LastSeen = now
		}
	}
	s.mu.Unlock()
	if session == nil {
		if expired {
			s.logf("mcp_session_deleted session_id=%s reason=expired", sessionID)
			http.Error(w, "expired MCP session", http.StatusNotFound)
		} else {
			http.Error(w, "unknown MCP session", http.StatusNotFound)
		}
		return nil, false
	}
	return session, true
}

func (s *mcpServer) expireSessionsLoop(ctx context.Context, interval time.Duration) {
	ticker := time.NewTicker(interval)
	defer ticker.Stop()
	for {
		select {
		case <-ctx.Done():
			return
		case now := <-ticker.C:
			s.expireIdleSessions(now)
		}
	}
}

func (s *mcpServer) expireIdleSessions(now time.Time) int {
	if s.sessionTTL <= 0 {
		return 0
	}
	expired := []string{}
	s.mu.Lock()
	for id, session := range s.sessions {
		if !session.LastSeen.Add(s.sessionTTL).After(now) {
			delete(s.sessions, id)
			expired = append(expired, id)
		}
	}
	s.mu.Unlock()
	sort.Strings(expired)
	for _, id := range expired {
		s.logf("mcp_session_deleted session_id=%s reason=expired", id)
	}
	return len(expired)
}

func stableToolSpecs(session *mcpSession) []map[string]any {
	tools := []map[string]any{currentOpportunityToolSpec(), waitForOpportunityToolSpec()}
	if session.AssignmentType == "council" {
		return append(tools,
			mcpToolSpec("get_case", "Return the current visible arbitration record for this council member.", emptyObjectSchema(), true),
			mcpToolSpec("list_evidence", "List visible immutable record evidence.", emptyObjectSchema(), true),
			mcpToolSpec("stat_evidence", "Return metadata and read limits for one visible evidence item.", evidenceIDSchema(), true),
			mcpToolSpec("read_evidence_range", "Read a bounded byte range from one visible evidence item as base64.", readEvidenceRangeSchema(), true),
			mcpToolSpec("submit_council_answer", "Submit one council answer for the current deliberation opportunity.", submitCouncilAnswerSchema(), false),
		)
	}
	if session.RoleID == "observer" {
		return append(tools,
			mcpToolSpec("case_status", "Return the current case phase, active turn, role status, and case counts.", emptyObjectSchema(), true),
			mcpToolSpec("get_case", "Return the current arbitration record.", emptyObjectSchema(), true),
			mcpToolSpec("get_case_result", "Return final case results, including council answers and rationales. If the case is pending, report pending status.", emptyObjectSchema(), true),
			mcpToolSpec("get_turn", "Return the current turn role, phase, deadline, and attempts.", emptyObjectSchema(), true),
			mcpToolSpec("list_events", "List recorded case events.", listEventsSchema(), true),
			mcpToolSpec("list_evidence", "List visible immutable record evidence.", emptyObjectSchema(), true),
			mcpToolSpec("stat_evidence", "Return metadata for one visible evidence item.", evidenceIDSchema(), true),
			mcpToolSpec("read_evidence_range", "Read a bounded byte range from one visible evidence item as base64.", readEvidenceRangeSchema(), true),
		)
	}
	return append(tools,
		mcpToolSpec("case_status", "Return the current case phase, active turn, role status, and case counts.", emptyObjectSchema(), true),
		mcpToolSpec("get_case", "Return the current visible arbitration record.", emptyObjectSchema(), true),
		mcpToolSpec("get_case_result", "Return final case results, including council answers and rationales. If the case is pending, report pending status.", emptyObjectSchema(), true),
		mcpToolSpec("send_work_notes", "Send private work notes for off-record operator analysis.", workNotesSchema(), false),
		mcpToolSpec("list_evidence", "List visible immutable record evidence.", emptyObjectSchema(), true),
		mcpToolSpec("stat_evidence", "Return metadata and read limits for one visible evidence item.", evidenceIDSchema(), true),
		mcpToolSpec("read_evidence_range", "Read a bounded byte range from one visible evidence item as base64.", readEvidenceRangeSchema(), true),
		mcpToolSpec("begin_evidence_upload", "Begin a chunked evidence upload.", beginEvidenceUploadSchema(), false),
		mcpToolSpec("write_evidence_chunk", "Write one base64 chunk into an upload session.", writeEvidenceChunkSchema(), false),
		mcpToolSpec("commit_evidence_upload", "Verify and admit a completed evidence upload.", commitEvidenceUploadSchema(), false),
		mcpToolSpec("submit_evidence", "Submit source evidence with provenance.", submittedEvidenceSchema(), false),
		mcpToolSpec("submit_decision", "Submit the final legal act for the current opportunity.", submitDecisionSchema(), false),
	)
}

func currentOpportunityToolSpec() map[string]any {
	return mcpToolSpec("get_current_opportunity", "Return current prompt, turn, tools, limits, remaining time, and attempts for this assignment.", emptyObjectSchema(), true)
}

func waitForOpportunityToolSpec() map[string]any {
	return map[string]any{
		"name":        waitToolName,
		"description": "Wait up to 30 seconds for this assignment to have a ready opportunity or case-status change. If state is waiting, call this tool again with after_version.",
		"inputSchema": map[string]any{
			"type": "object",
			"properties": map[string]any{
				"after_opportunity_id": map[string]any{"type": "string"},
				"after_version":        map[string]any{"type": "integer", "minimum": 0},
				"timeout_ms":           map[string]any{"type": "integer", "minimum": 1, "maximum": waitToolMax.Milliseconds()},
			},
			"additionalProperties": false,
		},
		"annotations": map[string]any{"readOnlyHint": true},
	}
}

func mcpToolSpec(name string, description string, schema map[string]any, readOnly bool) map[string]any {
	spec := map[string]any{"name": name, "description": description, "inputSchema": schema}
	if readOnly {
		spec["annotations"] = map[string]any{"readOnlyHint": true}
	}
	return spec
}

func emptyObjectSchema() map[string]any {
	return map[string]any{"type": "object", "properties": map[string]any{}, "additionalProperties": false}
}

func evidenceIDSchema() map[string]any {
	return map[string]any{"type": "object", "properties": map[string]any{"evidence_id": map[string]any{"type": "string"}}, "required": []string{"evidence_id"}, "additionalProperties": false}
}

func readEvidenceRangeSchema() map[string]any {
	return map[string]any{
		"type": "object",
		"properties": map[string]any{
			"evidence_id": map[string]any{"type": "string"},
			"offset":      map[string]any{"type": "integer", "minimum": 0},
			"length":      map[string]any{"type": "integer", "minimum": 1},
		},
		"required":             []string{"evidence_id", "offset", "length"},
		"additionalProperties": false,
	}
}

func workNotesSchema() map[string]any {
	return map[string]any{"type": "object", "properties": map[string]any{"notes": map[string]any{"type": "string"}}, "required": []string{"notes"}, "additionalProperties": false}
}

func beginEvidenceUploadSchema() map[string]any {
	return map[string]any{
		"type": "object",
		"properties": map[string]any{
			"title":               map[string]any{"type": "string"},
			"mime_type":           map[string]any{"type": "string"},
			"expected_size_bytes": map[string]any{"type": "integer", "minimum": 1},
			"expected_sha256":     map[string]any{"type": "string"},
			"source_url":          map[string]any{"type": "string"},
			"source_description":  map[string]any{"type": "string"},
			"retrieval_timestamp": map[string]any{"type": "string"},
			"relevance":           map[string]any{"type": "string"},
			"parent_evidence_id":  map[string]any{"type": "string"},
			"derivation_method":   map[string]any{"type": "string"},
		},
		"required":             []string{"title", "mime_type", "expected_size_bytes", "relevance"},
		"additionalProperties": false,
	}
}

func writeEvidenceChunkSchema() map[string]any {
	return map[string]any{"type": "object", "properties": map[string]any{"upload_id": map[string]any{"type": "string"}, "offset": map[string]any{"type": "integer", "minimum": 0}, "content_base64": map[string]any{"type": "string"}}, "required": []string{"upload_id", "offset", "content_base64"}, "additionalProperties": false}
}

func commitEvidenceUploadSchema() map[string]any {
	return map[string]any{"type": "object", "properties": map[string]any{"upload_id": map[string]any{"type": "string"}, "expected_sha256": map[string]any{"type": "string"}, "preferred_filename_ext": map[string]any{"type": "string"}}, "required": []string{"upload_id"}, "additionalProperties": false}
}

func submittedEvidenceSchema() map[string]any {
	return map[string]any{
		"type": "object",
		"properties": map[string]any{
			"title":                  map[string]any{"type": "string"},
			"source_url":             map[string]any{"type": "string"},
			"source_description":     map[string]any{"type": "string"},
			"retrieval_timestamp":    map[string]any{"type": "string"},
			"mime_type":              map[string]any{"type": "string"},
			"relevance":              map[string]any{"type": "string"},
			"content":                map[string]any{"type": "string"},
			"content_base64":         map[string]any{"type": "string"},
			"preferred_filename_ext": map[string]any{"type": "string"},
		},
		"required":             []string{"title", "mime_type", "relevance"},
		"additionalProperties": false,
	}
}

func submitDecisionSchema() map[string]any {
	return map[string]any{
		"type": "object",
		"properties": map[string]any{
			"kind":      map[string]any{"type": "string", "enum": []string{"tool", "pass"}},
			"tool_name": map[string]any{"type": "string", "enum": []string{"record_opening_statement", "submit_argument", "submit_rebuttal", "submit_surrebuttal", "deliver_closing_statement", "pass_phase_opportunity"}},
			"payload":   attorneyPayloadSchema(),
		},
		"required":             []string{"kind"},
		"additionalProperties": false,
	}
}

func attorneyPayloadSchema() map[string]any {
	return map[string]any{
		"type": "object",
		"properties": map[string]any{
			"text":              map[string]any{"type": "string"},
			"offered_evidence":  offeredEvidenceSchema(),
			"technical_reports": technicalReportsSchema(),
		},
		"additionalProperties": false,
	}
}

func offeredEvidenceSchema() map[string]any {
	return map[string]any{"type": "array", "items": map[string]any{"type": "object", "properties": map[string]any{"evidence_id": map[string]any{"type": "string"}, "label": map[string]any{"type": "string"}}, "required": []string{"evidence_id", "label"}, "additionalProperties": false}}
}

func technicalReportsSchema() map[string]any {
	return map[string]any{"type": "array", "items": map[string]any{"type": "object", "properties": map[string]any{"title": map[string]any{"type": "string"}, "summary": map[string]any{"type": "string"}}, "required": []string{"title", "summary"}, "additionalProperties": false}}
}

func listEventsSchema() map[string]any {
	return map[string]any{"type": "object", "properties": map[string]any{"offset": map[string]any{"type": "integer", "minimum": 0}, "limit": map[string]any{"type": "integer", "minimum": 1, "maximum": 1000}}, "additionalProperties": false}
}

func submitCouncilAnswerSchema() map[string]any {
	return map[string]any{"type": "object", "properties": map[string]any{"answer": map[string]any{"type": "integer", "minimum": 0, "maximum": 100}, "rationale": map[string]any{"type": "string"}}, "required": []string{"answer", "rationale"}, "additionalProperties": false}
}

func (s *mcpServer) callTool(ctx context.Context, session *mcpSession, params json.RawMessage) (map[string]any, error) {
	var call toolCallParams
	if len(params) > 0 {
		dec := json.NewDecoder(bytes.NewReader(params))
		dec.UseNumber()
		if err := dec.Decode(&call); err != nil {
			return nil, fmt.Errorf("decode tool call params: %w", err)
		}
	}
	call.Name = strings.TrimSpace(call.Name)
	if call.Name == "" {
		return nil, fmt.Errorf("tool name is required")
	}
	if call.Arguments == nil {
		call.Arguments = map[string]any{}
	}
	if call.Name == "get_current_opportunity" {
		status, err := s.getCurrent(ctx, session)
		if err != nil {
			return toolResult(map[string]any{"ok": false, "error": err.Error()}, true), nil
		}
		return toolResult(status, false), nil
	}
	if call.Name == waitToolName {
		result, err := s.waitForOpportunity(ctx, session, call.Arguments)
		if err != nil {
			return toolResult(waitErrorResult(session, err), true), nil
		}
		return toolResult(result, mapString(result["state"]) == "error"), nil
	}
	if call.Name == "case_status" && session.AssignmentType == "lawyer" {
		result, err := s.getLawyerStatus(ctx, session)
		if err != nil {
			return toolResult(map[string]any{"ok": false, "error": err.Error()}, true), nil
		}
		return toolResult(result, false), nil
	}
	if call.Name == "get_case_result" && session.AssignmentType == "lawyer" {
		result, err := s.getLawyerResult(ctx, session)
		if err != nil {
			return toolResult(map[string]any{"ok": false, "error": err.Error()}, true), nil
		}
		return toolResult(result, false), nil
	}
	status, err := s.getCurrent(ctx, session)
	if err != nil {
		return toolResult(map[string]any{"ok": false, "error": err.Error()}, true), nil
	}
	result, err := s.postTool(ctx, session, status, call.Name, call.Arguments)
	if err != nil {
		return toolResult(map[string]any{"ok": false, "error": err.Error()}, true), nil
	}
	ok, _ := result["ok"].(bool)
	return toolResult(result, !ok), nil
}

func (s *mcpServer) getCurrent(ctx context.Context, session *mcpSession) (map[string]any, error) {
	return s.getJSON(ctx, session.apiBase(s)+"/get", session.query())
}

func (s *mcpServer) getLawyerStatus(ctx context.Context, session *mcpSession) (map[string]any, error) {
	return s.getJSON(ctx, s.lawyerAPIBase()+"/status", session.query())
}

func (s *mcpServer) getLawyerResult(ctx context.Context, session *mcpSession) (map[string]any, error) {
	return s.getJSON(ctx, s.lawyerAPIBase()+"/result", session.query())
}

func (s *mcpServer) waitForOpportunity(ctx context.Context, session *mcpSession, args map[string]any) (map[string]any, error) {
	timeout, err := waitToolTimeout(args["timeout_ms"])
	if err != nil {
		return nil, err
	}
	waitCtx, cancel := context.WithTimeout(ctx, timeout+waitToolHTTPMargin)
	defer cancel()
	query := session.query()
	query.Set("timeout_ms", fmt.Sprintf("%d", timeout.Milliseconds()))
	if after := mapString(args["after_opportunity_id"]); after != "" {
		query.Set("after", after)
	}
	if afterVersion := mapNumberString(args["after_version"]); afterVersion != "" {
		query.Set("after_version", afterVersion)
	}
	value, err := s.getJSON(waitCtx, session.apiBase(s)+"/wait", query)
	if err != nil {
		return nil, err
	}
	state := waitToolState(value)
	value["state"] = state
	if version := waitVersion(value); version != nil {
		value["after_version"] = version
	}
	if opportunityID := currentOpportunityID(value); opportunityID != "" {
		value["after_opportunity_id"] = opportunityID
	}
	value["message"] = waitToolMessage(state)
	s.logf("%sapi_wait case_id=%s principal=%s state=%s wait_reason=%s opportunity_id=%s", session.AssignmentType, session.CaseID, session.principalID(), state, waitReason(value), currentOpportunityID(value))
	return value, nil
}

func (s *mcpServer) getJSON(ctx context.Context, rawURL string, query url.Values) (map[string]any, error) {
	u, err := url.Parse(rawURL)
	if err != nil {
		return nil, err
	}
	u.RawQuery = query.Encode()
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u.String(), nil)
	if err != nil {
		return nil, err
	}
	s.addAPIAuth(req)
	resp, err := s.client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	value, err := decodeJSONObject(resp.Body)
	if err != nil {
		return nil, err
	}
	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		value["ok"] = false
		value["state"] = "error"
		value["http_status"] = resp.StatusCode
		return value, nil
	}
	return value, nil
}

func (s *mcpServer) postTool(ctx context.Context, session *mcpSession, status map[string]any, tool string, arguments map[string]any) (map[string]any, error) {
	body := map[string]any{
		"case_id":   session.CaseID,
		"tool":      tool,
		"arguments": arguments,
	}
	if session.AssignmentType == "lawyer" {
		body["role_id"] = session.RoleID
		if session.RoleID != "observer" {
			opportunityID := currentOpportunityID(status)
			if opportunityID == "" {
				return nil, fmt.Errorf("current turn has no opportunity_id")
			}
			body["opportunity_id"] = opportunityID
		}
	} else {
		body["member_id"] = session.MemberID
		opportunityID := currentOpportunityID(status)
		if opportunityID == "" {
			return nil, fmt.Errorf("current turn has no opportunity_id")
		}
		body["opportunity_id"] = opportunityID
	}
	raw, err := json.Marshal(body)
	if err != nil {
		return nil, err
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, session.apiBase(s)+"/do", bytes.NewReader(raw))
	if err != nil {
		return nil, err
	}
	req.Header.Set("Content-Type", "application/json")
	s.addAPIAuth(req)
	resp, err := s.client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	value, err := decodeJSONObject(resp.Body)
	if err != nil {
		return nil, err
	}
	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		value["ok"] = false
		value["http_status"] = resp.StatusCode
	}
	s.logf("%sapi_do case_id=%s principal=%s opportunity_id=%s tool=%s http_status=%d ok=%v", session.AssignmentType, session.CaseID, session.principalID(), mapString(body["opportunity_id"]), tool, resp.StatusCode, value["ok"])
	return value, nil
}

func (s *mcpServer) addAPIAuth(req *http.Request) {
	if s.apiBearerToken != "" {
		req.Header.Set("Authorization", "Bearer "+s.apiBearerToken)
	}
}

func waitToolTimeout(value any) (time.Duration, error) {
	if value == nil {
		return waitToolDefault, nil
	}
	text := mapNumberString(value)
	if text == "" {
		return 0, fmt.Errorf("timeout_ms must be an integer")
	}
	ms, err := strconv.ParseInt(text, 10, 64)
	if err != nil || ms <= 0 {
		return 0, fmt.Errorf("timeout_ms must be a positive integer")
	}
	timeout := time.Duration(ms) * time.Millisecond
	if timeout > waitToolMax {
		return waitToolMax, nil
	}
	return timeout, nil
}

func waitToolState(value map[string]any) string {
	if ok, hasOK := value["ok"].(bool); hasOK && !ok {
		return "error"
	}
	switch strings.ToLower(mapString(value["status"])) {
	case "ready":
		return "ready"
	case "failed":
		return "failed"
	case "done", "terminal", "complete", "completed":
		return "done"
	}
	return "waiting"
}

func waitVersion(value map[string]any) any {
	wait, _ := value["wait"].(map[string]any)
	return wait["version"]
}

func waitReason(value map[string]any) string {
	wait, _ := value["wait"].(map[string]any)
	return mapString(wait["reason"])
}

func waitToolMessage(state string) string {
	switch state {
	case "ready":
		return "An opportunity is ready. Use the returned prompt, turn, limits, and tools to act."
	case "done":
		return "The case is done. Stop acting on this assignment."
	case "failed":
		return "The case failed. Stop acting on this assignment."
	case "error":
		return "This assignment cannot continue without operator attention."
	default:
		return "No opportunity is ready. Call wait_for_opportunity again with after_version."
	}
}

func waitErrorResult(session *mcpSession, err error) map[string]any {
	return map[string]any{"ok": false, "state": "error", "case_id": session.CaseID, "principal": session.principalID(), "error": map[string]any{"code": "wait_failed", "message": err.Error()}, "message": waitToolMessage("error")}
}

func currentOpportunityID(status map[string]any) string {
	turn, _ := status["turn"].(map[string]any)
	return mapString(turn["opportunity_id"])
}

func (session *mcpSession) apiBase(s *mcpServer) string {
	if session.AssignmentType == "council" {
		return s.councilAPIBase()
	}
	return s.lawyerAPIBase()
}

func (s *mcpServer) lawyerAPIBase() string {
	return s.caseAPIPath("/lawyerapi/v1")
}

func (s *mcpServer) councilAPIBase() string {
	return s.caseAPIPath("/councilapi/v1")
}

func (s *mcpServer) caseAPIPath(path string) string {
	return s.caseAPIBase + path
}

func (session *mcpSession) query() url.Values {
	query := url.Values{}
	query.Set("case_id", session.CaseID)
	if session.AssignmentType == "council" {
		query.Set("member_id", session.MemberID)
	} else {
		query.Set("role_id", session.RoleID)
	}
	return query
}

func (session *mcpSession) principalID() string {
	if session.MemberID != "" {
		return session.MemberID
	}
	return session.RoleID
}

func toolResult(value map[string]any, isError bool) map[string]any {
	return map[string]any{
		"content":           []map[string]any{{"type": "text", "text": toolResultText(value)}},
		"structuredContent": value,
		"isError":           isError,
	}
}

func toolResultText(value map[string]any) string {
	var b strings.Builder
	for _, key := range []string{"ok", "status", "state", "message", "after_version", "after_opportunity_id", "role_id", "member_id", "case_id"} {
		if text := mapNumberString(value[key]); text != "" {
			b.WriteString(key)
			b.WriteString(": ")
			b.WriteString(text)
			b.WriteByte('\n')
		}
	}
	if wait, ok := value["wait"].(map[string]any); ok {
		if reason := mapString(wait["reason"]); reason != "" {
			b.WriteString("wait_reason: ")
			b.WriteString(reason)
			b.WriteByte('\n')
		}
	}
	if turn, ok := value["turn"].(map[string]any); ok {
		for _, key := range []string{"phase", "opportunity_id", "remaining_ms", "attempts_remaining"} {
			if text := mapNumberString(turn[key]); text != "" {
				b.WriteString(key)
				b.WriteString(": ")
				b.WriteString(text)
				b.WriteByte('\n')
			}
		}
	}
	if b.Len() == 0 {
		raw, _ := json.Marshal(value)
		return string(raw)
	}
	raw, _ := json.Marshal(value)
	b.WriteString("json: ")
	b.Write(raw)
	return strings.TrimSpace(b.String())
}

func decodeJSONObject(r io.Reader) (map[string]any, error) {
	var value map[string]any
	dec := json.NewDecoder(r)
	dec.UseNumber()
	if err := dec.Decode(&value); err != nil {
		return nil, err
	}
	return value, nil
}

func writeRPC(w http.ResponseWriter, response rpcResponse) {
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(response)
}

func randomSessionID() (string, error) {
	var buf [16]byte
	if _, err := rand.Read(buf[:]); err != nil {
		return "", fmt.Errorf("generate session id: %w", err)
	}
	return hex.EncodeToString(buf[:]), nil
}

func (s *mcpServer) logf(format string, args ...any) {
	if s.log != nil {
		fmt.Fprintf(s.log, format+"\n", args...)
	}
}

func mapString(value any) string {
	if value == nil {
		return ""
	}
	if s, ok := value.(string); ok {
		return s
	}
	return fmt.Sprintf("%v", value)
}

func mapNumberString(value any) string {
	switch v := value.(type) {
	case nil:
		return ""
	case string:
		return v
	case json.Number:
		return v.String()
	case int, int64, float64, bool:
		return fmt.Sprintf("%v", v)
	default:
		return ""
	}
}
