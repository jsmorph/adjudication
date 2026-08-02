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
	"strconv"
	"strings"
	"sync"
	"time"
)

const (
	mcpProtocolVersion = "2025-06-18"
	serverName         = "adc"
	serverVersion      = "0.1.0"

	DefaultListenAddr             = "127.0.0.1:19880"
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
	cleanupInterval := opts.SessionCleanupInterval
	if cleanupInterval == 0 {
		cleanupInterval = DefaultSessionCleanupInterval
	}
	allowedOrigins, err := allowedOriginMap(opts.AllowedOrigins)
	if err != nil {
		return err
	}
	log := opts.Log
	if log == nil {
		log = io.Discard
	}
	handler := &server{
		caseAPIBase:    caseAPIBase,
		bearerToken:    strings.TrimSpace(opts.BearerToken),
		apiBearerToken: strings.TrimSpace(opts.APIBearerToken),
		allowedOrigins: allowedOrigins,
		client:         &http.Client{Timeout: waitToolMax + waitToolHTTPMargin},
		log:            log,
		sessionTTL:     sessionTTL,
		sessions:       map[string]*session{},
	}
	ln, err := net.Listen("tcp", listen)
	if err != nil {
		return err
	}
	cleanupCtx, cancelCleanup := context.WithCancel(context.Background())
	defer cancelCleanup()
	if sessionTTL > 0 {
		go handler.expireSessionsLoop(cleanupCtx, cleanupInterval)
	}
	httpServer := &http.Server{Handler: handler, ReadHeaderTimeout: 10 * time.Second}
	done := make(chan error, 1)
	go func() {
		<-ctx.Done()
		shutdownCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()
		done <- httpServer.Shutdown(shutdownCtx)
	}()
	handler.logf("adc mcp listening on http://%s/mcp", listenerDisplayAddr(ln.Addr().String()))
	err = httpServer.Serve(ln)
	if errors.Is(err, http.ErrServerClosed) {
		shutdownErr := <-done
		if shutdownErr != nil {
			return shutdownErr
		}
		return nil
	}
	return err
}

type server struct {
	caseAPIBase    string
	bearerToken    string
	apiBearerToken string
	allowedOrigins map[string]struct{}
	client         *http.Client
	log            io.Writer
	sessionTTL     time.Duration

	mu       sync.Mutex
	sessions map[string]*session
}

type session struct {
	ID          string
	CaseID      string
	RoleID      string
	PrincipalID string
	CreatedAt   time.Time
	LastSeen    time.Time
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

func allowedOriginMap(values []string) (map[string]struct{}, error) {
	out := map[string]struct{}{}
	for _, value := range values {
		origin := strings.TrimSpace(value)
		if origin == "" {
			return nil, fmt.Errorf("origin must not be empty")
		}
		out[origin] = struct{}{}
	}
	return out, nil
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

func (s *server) ServeHTTP(w http.ResponseWriter, r *http.Request) {
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
	case http.MethodDelete:
		s.handleDelete(w, r)
	default:
		w.Header().Set("Allow", "POST, DELETE")
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
	}
}

func (s *server) authorized(r *http.Request) bool {
	if s.bearerToken == "" {
		return true
	}
	return strings.TrimSpace(r.Header.Get("Authorization")) == "Bearer "+s.bearerToken
}

func (s *server) originAllowed(origin string) bool {
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

func (s *server) handleDelete(w http.ResponseWriter, r *http.Request) {
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

func (s *server) handlePost(w http.ResponseWriter, r *http.Request) {
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

func (s *server) handleInitialize(w http.ResponseWriter, r *http.Request, msg rpcMessage) {
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

func (s *server) newSession(r *http.Request) (*session, error) {
	query := r.URL.Query()
	caseID := strings.TrimSpace(query.Get("case_id"))
	roleID := strings.TrimSpace(query.Get("role_id"))
	principalID := strings.TrimSpace(query.Get("principal_id"))
	if caseID == "" {
		return nil, fmt.Errorf("case_id query parameter is required")
	}
	if !validRoleID(roleID) {
		return nil, fmt.Errorf("role_id must be plaintiff, defendant, juror, or observer")
	}
	if roleID == "juror" && principalID == "" {
		return nil, fmt.Errorf("principal_id is required for role_id=juror")
	}
	if roleID != "juror" && principalID != "" {
		return nil, fmt.Errorf("principal_id is only allowed for role_id=juror")
	}
	sessionID, err := randomSessionID()
	if err != nil {
		return nil, err
	}
	now := time.Now()
	session := &session{ID: sessionID, CaseID: caseID, RoleID: roleID, PrincipalID: principalID, CreatedAt: now, LastSeen: now}
	s.mu.Lock()
	s.sessions[sessionID] = session
	s.mu.Unlock()
	s.logf("mcp_session_created session_id=%s case_id=%s role_id=%s principal_id=%s", session.ID, session.CaseID, session.RoleID, session.PrincipalID)
	return session, nil
}

func validRoleID(roleID string) bool {
	switch strings.TrimSpace(roleID) {
	case "plaintiff", "defendant", "juror", "observer":
		return true
	default:
		return false
	}
}

func sessionInstructions(session *session) string {
	principal := session.RoleID
	if session.PrincipalID != "" {
		principal += "/" + session.PrincipalID
	}
	return fmt.Sprintf("This MCP session is bound to ADC case_id %s and role %s. Call wait_for_opportunity. If it returns state waiting, call it again. If it returns state ready, read the returned prompt and submit exactly one decision for that opportunity. If it returns state done or failed, stop.", session.CaseID, principal)
}

func (s *server) requireSession(w http.ResponseWriter, r *http.Request, msg rpcMessage) (*session, bool) {
	sessionID := strings.TrimSpace(r.Header.Get("Mcp-Session-Id"))
	if sessionID == "" {
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

func (s *server) expireSessionsLoop(ctx context.Context, interval time.Duration) {
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

func (s *server) expireIdleSessions(now time.Time) int {
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
	for _, id := range expired {
		s.logf("mcp_session_deleted session_id=%s reason=expired", id)
	}
	return len(expired)
}

func stableToolSpecs(session *session) []map[string]any {
	tools := []map[string]any{
		toolSpec("get_current_opportunity", "Return the current prompt, opportunity, tools, limits, remaining time, and attempts.", emptySchema(), true),
		waitToolSpec(),
		toolSpec("case_status", "Return current case status and current turn information.", emptySchema(), true),
	}
	if session.RoleID == "observer" {
		return append(tools,
			toolSpec("get_case_result", "Return final case results, or pending status if the case is still running.", emptySchema(), true),
		)
	}
	return append(tools,
		toolSpec("get_case", "Fetch the current visible case view.", emptySchema(), true),
		toolSpec("get_case_result", "Return final case results, or pending status if the case is still running.", emptySchema(), true),
		toolSpec("explain_decisions", "Fetch decision traces visible to this role.", emptySchema(), true),
		toolSpec("list_case_files", "List visible case file identifiers and metadata.", emptySchema(), true),
		toolSpec("read_case_text_file", "Read a visible text case file by file_id.", fileIDSchema(), true),
		toolSpec("request_case_file", "Fetch a visible case file as model content items.", fileIDSchema(), true),
		toolSpec("read_case_file_bytes", "Read a visible case file as base64 bytes.", fileIDSchema(), true),
		toolSpec("get_juror_context", "Fetch questionnaire and voir dire context for one juror.", jurorIDSchema(), true),
		toolSpec("send_work_notes", "Send private work notes outside the case record.", workNotesSchema(), false),
		toolSpec("submit_decision", "Submit one legal decision for the current opportunity.", submitDecisionSchema(), false),
		toolSpec("report_failure", "Report that this agent cannot continue the active opportunity.", failureSchema(), false),
	)
}

func waitToolSpec() map[string]any {
	return map[string]any{
		"name":        waitToolName,
		"description": "Wait up to 30 seconds for this role to have an opportunity or terminal case status.",
		"inputSchema": map[string]any{
			"type": "object",
			"properties": map[string]any{
				"timeout_ms": map[string]any{"type": "integer", "minimum": 1, "maximum": waitToolMax.Milliseconds()},
			},
			"additionalProperties": false,
		},
		"annotations": map[string]any{"readOnlyHint": true},
	}
}

func toolSpec(name, description string, schema map[string]any, readOnly bool) map[string]any {
	spec := map[string]any{"name": name, "description": description, "inputSchema": schema}
	if readOnly {
		spec["annotations"] = map[string]any{"readOnlyHint": true}
	}
	return spec
}

func emptySchema() map[string]any {
	return map[string]any{"type": "object", "properties": map[string]any{}, "additionalProperties": false}
}

func fileIDSchema() map[string]any {
	return map[string]any{"type": "object", "properties": map[string]any{"file_id": map[string]any{"type": "string"}}, "required": []string{"file_id"}, "additionalProperties": false}
}

func jurorIDSchema() map[string]any {
	return map[string]any{"type": "object", "properties": map[string]any{"juror_id": map[string]any{"type": "string"}}, "required": []string{"juror_id"}, "additionalProperties": false}
}

func workNotesSchema() map[string]any {
	return map[string]any{"type": "object", "properties": map[string]any{"notes": map[string]any{"type": "string"}}, "required": []string{"notes"}, "additionalProperties": false}
}

func failureSchema() map[string]any {
	return map[string]any{"type": "object", "properties": map[string]any{"message": map[string]any{"type": "string"}}, "required": []string{"message"}, "additionalProperties": false}
}

func submitDecisionSchema() map[string]any {
	return map[string]any{
		"type": "object",
		"properties": map[string]any{
			"kind":      map[string]any{"type": "string", "enum": []string{"tool", "pass"}},
			"tool_name": map[string]any{"type": "string"},
			"payload":   map[string]any{"type": "object"},
			"reason":    map[string]any{"type": "string"},
		},
		"required":             []string{"kind"},
		"additionalProperties": false,
	}
}

func (s *server) callTool(ctx context.Context, session *session, params json.RawMessage) (map[string]any, error) {
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
	if session.RoleID == "observer" && !observerToolAllowed(call.Name) {
		return toolResult(map[string]any{
			"ok":      false,
			"status":  "forbidden",
			"case_id": session.CaseID,
			"role_id": session.RoleID,
			"error":   map[string]any{"code": "tool_not_available", "message": "tool is not available for observer"},
		}, nil), nil
	}
	switch call.Name {
	case "get_current_opportunity":
		result, err := s.postRoleAPI(ctx, "/get", session.baseBody())
		return toolResult(result, err), nil
	case waitToolName:
		result, err := s.waitForOpportunity(ctx, session, call.Arguments)
		return toolResult(result, err), nil
	case "case_status":
		result, err := s.callRoleTool(ctx, session, "", "case_status", map[string]any{})
		return toolResult(result, err), nil
	case "get_case_result":
		result, err := s.postRoleAPI(ctx, "/result", session.baseBody())
		return toolResult(result, err), nil
	case "report_failure":
		body := session.baseBody()
		body["message"] = strings.TrimSpace(mapString(call.Arguments["message"]))
		result, err := s.postRoleAPI(ctx, "/fail", body)
		return toolResult(result, err), nil
	default:
		status, err := s.postRoleAPI(ctx, "/get", session.baseBody())
		if err != nil {
			return toolResult(status, err), nil
		}
		opportunityID := currentOpportunityID(status)
		result, err := s.callRoleTool(ctx, session, opportunityID, call.Name, call.Arguments)
		return toolResult(result, err), nil
	}
}

func observerToolAllowed(name string) bool {
	switch strings.TrimSpace(name) {
	case "get_current_opportunity", waitToolName, "case_status", "get_case_result":
		return true
	default:
		return false
	}
}

func (s *server) waitForOpportunity(ctx context.Context, session *session, args map[string]any) (map[string]any, error) {
	timeout, err := waitToolTimeout(args["timeout_ms"])
	if err != nil {
		return nil, err
	}
	body := session.baseBody()
	body["timeout_ms"] = int(timeout / time.Millisecond)
	waitCtx, cancel := context.WithTimeout(ctx, timeout+waitToolHTTPMargin)
	defer cancel()
	result, err := s.postRoleAPI(waitCtx, "/wait_for_opportunity", body)
	if result == nil {
		result = map[string]any{}
	}
	state := waitToolState(result)
	result["state"] = state
	result["message"] = waitToolMessage(state)
	if opportunityID := currentOpportunityID(result); opportunityID != "" {
		result["after_opportunity_id"] = opportunityID
	}
	s.logf("roleapi_wait case_id=%s role_id=%s principal_id=%s state=%s opportunity_id=%s", session.CaseID, session.RoleID, session.PrincipalID, state, currentOpportunityID(result))
	return result, err
}

func (s *server) callRoleTool(ctx context.Context, session *session, opportunityID string, tool string, arguments map[string]any) (map[string]any, error) {
	body := session.baseBody()
	body["tool"] = tool
	body["arguments"] = arguments
	if opportunityID != "" {
		body["opportunity_id"] = opportunityID
	}
	result, err := s.postRoleAPI(ctx, "/do", body)
	s.logf("roleapi_do case_id=%s role_id=%s principal_id=%s opportunity_id=%s tool=%s ok=%v", session.CaseID, session.RoleID, session.PrincipalID, opportunityID, tool, mapBool(result["ok"]))
	return result, err
}

func (s *server) postRoleAPI(ctx context.Context, path string, body map[string]any) (map[string]any, error) {
	raw, err := json.Marshal(body)
	if err != nil {
		return nil, err
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, s.caseAPIBase+roleAPIBasePath()+path, bytes.NewReader(raw))
	if err != nil {
		return nil, err
	}
	req.Header.Set("Content-Type", "application/json")
	if s.apiBearerToken != "" {
		req.Header.Set("Authorization", "Bearer "+s.apiBearerToken)
	}
	resp, err := s.client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	result, err := decodeJSONObject(resp.Body)
	if err != nil {
		return nil, err
	}
	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		result["ok"] = false
		result["http_status"] = resp.StatusCode
		return result, fmt.Errorf("role API returned HTTP %d", resp.StatusCode)
	}
	return result, nil
}

func roleAPIBasePath() string {
	return "/roleapi/v1"
}

func (session *session) baseBody() map[string]any {
	body := map[string]any{"case_id": session.CaseID, "role_id": session.RoleID}
	if session.PrincipalID != "" {
		body["principal_id"] = session.PrincipalID
	}
	return body
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
	case "active", "ready":
		return "ready"
	case "failed":
		return "failed"
	case "done", "terminal", "complete", "completed":
		return "done"
	default:
		return "waiting"
	}
}

func waitToolMessage(state string) string {
	switch state {
	case "ready":
		return "An opportunity is ready. Read the prompt, use support tools as needed, send work notes, and submit one decision."
	case "done":
		return "The case is done. Stop acting on this role."
	case "failed":
		return "The case failed. Stop acting on this role."
	case "error":
		return "This role cannot continue without operator attention."
	default:
		return "No opportunity is ready. Call wait_for_opportunity again."
	}
}

func currentOpportunityID(status map[string]any) string {
	if opportunity, ok := status["opportunity"].(map[string]any); ok {
		if id := mapString(opportunity["opportunity_id"]); id != "" {
			return id
		}
	}
	if turn, ok := status["current_turn"].(map[string]any); ok {
		return mapString(turn["opportunity_id"])
	}
	return ""
}

func toolResult(value map[string]any, err error) map[string]any {
	isError := err != nil
	if value == nil {
		value = map[string]any{}
	}
	if err != nil && value["error"] == nil {
		value["error"] = map[string]any{"code": "tool_failed", "message": err.Error()}
	}
	if ok, hasOK := value["ok"].(bool); hasOK && !ok {
		isError = true
	}
	return map[string]any{
		"content":           []map[string]any{{"type": "text", "text": toolResultText(value)}},
		"structuredContent": value,
		"isError":           isError,
	}
}

func toolResultText(value map[string]any) string {
	var b strings.Builder
	for _, key := range []string{"ok", "status", "state", "message", "case_id", "role_id", "principal_id", "after_opportunity_id"} {
		if text := mapNumberString(value[key]); text != "" {
			b.WriteString(key)
			b.WriteString(": ")
			b.WriteString(text)
			b.WriteByte('\n')
		}
	}
	if opportunity, ok := value["opportunity"].(map[string]any); ok {
		for _, key := range []string{"phase", "kind", "opportunity_id", "remaining_time_ms", "attempts_remaining"} {
			if text := mapNumberString(opportunity[key]); text != "" {
				b.WriteString(key)
				b.WriteString(": ")
				b.WriteString(text)
				b.WriteByte('\n')
			}
		}
	}
	raw, _ := json.Marshal(value)
	if b.Len() == 0 {
		return string(raw)
	}
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

func (s *server) logf(format string, args ...any) {
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

func mapBool(value any) bool {
	got, _ := value.(bool)
	return got
}
