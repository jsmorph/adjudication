package console

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"html/template"
	"io"
	"mime"
	"net/http"
	"net/url"
	"path"
	"sort"
	"strconv"
	"strings"
)

const (
	defaultEventTailBytes = 1 << 20
	maxEventTailBytes     = 8 << 20
	defaultEventLimit     = 100
	maxEventLimit         = 500
)

type App struct {
	cfg    Config
	client *Client
	tmpl   *template.Template
}

type ViewData struct {
	Title                string
	Systems              []SystemConfig
	System               SystemConfig
	Scope                ScopeConfig
	ScopeOptions         []ScopeConfig
	Cases                []map[string]any
	CaseID               string
	StatusFilter         string
	Record               map[string]any
	Result               map[string]any
	Artifacts            []Artifact
	EventIssues          []EventIssue
	RecentEvents         []CaseEvent
	Events               []EventRow
	EventNotice          string
	EventLimit           string
	EventBytes           string
	HasEvents            bool
	LogName              string
	LogMode              string
	LogBytes             string
	LogText              string
	LogNotice            string
	Evidence             []EvidenceEntry
	EvidenceID           string
	EvidenceNotice       string
	HasAttestationEvents bool
	ServicePath          string
	Method               string
	Payload              string
	Response             *Response
	Error                string
	Notice               string
	CreateTemplate       string
	AutoRefresh          bool
	CanManage            bool
	CaseAvailable        bool
}

type Artifact struct {
	Name string
	Size string
}

type EventIssue struct {
	Timestamp string
	Phase     string
	Type      string
	Member    string
	Process   string
	Reason    string
	Message   string
	LogPath   string
}

type CaseEvent struct {
	Timestamp string
	Phase     string
	Type      string
	Actor     string
	Message   string
}

type EventRow struct {
	Offset    string
	Timestamp string
	Phase     string
	Type      string
	Actor     string
	Message   string
	Raw       map[string]any
}

type recordFact struct {
	Label string
	Value string
}

type EvidenceEntry struct {
	ID         string
	Title      string
	MIMEType   string
	Size       string
	Status     string
	Visibility string
	Uses       string
}

func New(cfg Config) (*App, error) {
	normalized, err := cfg.normalized()
	if err != nil {
		return nil, err
	}
	tmpl, err := template.New("console").Funcs(template.FuncMap{
		"json":        prettyJSON,
		"boundedJSON": boundedJSON,
		"response":    responseText,
		"body":        compactBody,
		"field":       fieldText,
		"caseFacts":   caseListFacts,
		"recordValue": recordValue,
		"keys":        sortedKeys,
		"pathEscape":  url.PathEscape,
		"query":       queryEscape,
		"isLog":       isLogArtifactName,
		"join":        strings.Join,
	}).Parse(pageTemplates)
	if err != nil {
		return nil, err
	}
	return &App{
		cfg:    normalized,
		client: NewClient(normalized.RequestTimeout, normalized.MaxServiceBytes),
		tmpl:   tmpl,
	}, nil
}

func (a *App) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	if !a.authorized(r) {
		w.Header().Set("WWW-Authenticate", "Bearer")
		http.Error(w, "unauthorized", http.StatusUnauthorized)
		return
	}
	switch {
	case r.URL.Path == "/":
		a.handleIndex(w, r)
	case r.URL.Path == "/health":
		w.WriteHeader(http.StatusNoContent)
	default:
		a.handleSystem(w, r)
	}
}

func (a *App) authorized(r *http.Request) bool {
	token := strings.TrimSpace(a.cfg.WebBearerToken)
	if token == "" {
		return true
	}
	return r.Header.Get("Authorization") == "Bearer "+token
}

func (a *App) handleIndex(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodGet {
		http.Error(w, "use GET", http.StatusMethodNotAllowed)
		return
	}
	a.render(w, http.StatusOK, "index", ViewData{
		Title:   "Adjudication",
		Systems: a.systems(),
	})
}

func (a *App) handleSystem(w http.ResponseWriter, r *http.Request) {
	parts := splitPath(r.URL.Path)
	if len(parts) < 2 || parts[0] != "system" {
		http.NotFound(w, r)
		return
	}
	sys, ok := a.cfg.system(parts[1])
	if !ok {
		http.NotFound(w, r)
		return
	}
	if len(parts) == 3 && parts[2] == "request" {
		a.handleRawRequest(w, r, sys)
		return
	}
	if len(parts) < 4 {
		http.NotFound(w, r)
		return
	}
	scope, ok := sys.scope(parts[2])
	if !ok || parts[3] != "cases" {
		http.NotFound(w, r)
		return
	}
	if len(parts) == 4 {
		switch r.Method {
		case http.MethodGet:
			a.handleCaseList(w, r, sys, scope)
		case http.MethodPost:
			a.handleCreateCase(w, r, sys, scope)
		default:
			http.Error(w, "use GET or POST", http.StatusMethodNotAllowed)
		}
		return
	}
	if len(parts) == 5 && parts[4] == "new" && r.Method == http.MethodGet {
		a.handleNewCase(w, r, sys, scope)
		return
	}
	if len(parts) < 5 {
		http.NotFound(w, r)
		return
	}
	caseID, err := url.PathUnescape(parts[4])
	if err != nil || strings.TrimSpace(caseID) == "" {
		http.Error(w, "bad case id", http.StatusBadRequest)
		return
	}
	switch {
	case len(parts) == 5 && r.Method == http.MethodGet:
		a.handleCaseDetail(w, r, sys, scope, caseID, "")
	case len(parts) == 6 && parts[5] == "result" && r.Method == http.MethodGet:
		a.handleResult(w, r, sys, scope, caseID)
	case len(parts) == 6 && parts[5] == "artifacts" && r.Method == http.MethodGet:
		a.handleArtifactList(w, r, sys, scope, caseID)
	case len(parts) >= 7 && parts[5] == "artifacts" && proxyMethod(r.Method):
		name := strings.Join(parts[6:], "/")
		a.proxyService(w, r, sys, artifactPath(scope, caseID, name))
	case len(parts) == 6 && parts[5] == "events" && r.Method == http.MethodGet:
		a.handleEvents(w, r, sys, scope, caseID)
	case len(parts) == 6 && parts[5] == "log" && r.Method == http.MethodGet:
		a.handleLog(w, r, sys, scope, caseID)
	case len(parts) == 6 && parts[5] == "evidence" && r.Method == http.MethodGet:
		a.handleEvidence(w, r, sys, scope, caseID)
	case len(parts) == 7 && parts[5] == "evidence" && proxyMethod(r.Method):
		a.proxyService(w, r, sys, evidencePath(scope, caseID, parts[6]))
	case len(parts) == 7 && parts[5] == "attestation" && parts[6] == "events" && proxyMethod(r.Method):
		a.proxyService(w, r, sys, casePath(scope, caseID, "attestation/events"))
	case len(parts) == 6 && parts[5] == "manage" && r.Method == http.MethodPost:
		a.handleManageCase(w, r, sys, scope, caseID)
	default:
		http.NotFound(w, r)
	}
}

func (a *App) handleCaseList(w http.ResponseWriter, r *http.Request, sys SystemConfig, scope ScopeConfig) {
	status := strings.TrimSpace(r.URL.Query().Get("status"))
	servicePath := scope.BasePath
	if status != "" {
		servicePath += "?status=" + url.QueryEscape(status)
	}
	resp, err := a.client.JSON(r.Context(), sys, http.MethodGet, servicePath, nil)
	if err != nil {
		a.render(w, http.StatusBadGateway, "cases", baseView(sys, scope, a.systems(), status, err.Error()))
		return
	}
	data := baseView(sys, scope, a.systems(), status, "")
	data.Title = sys.Label + " " + scope.Label + " Cases"
	data.Response = &resp
	data.Cases = mapSlice(resp.JSON["cases"])
	if resp.StatusCode >= 400 {
		a.render(w, http.StatusBadGateway, "cases", data)
		return
	}
	a.render(w, http.StatusOK, "cases", data)
}

func (a *App) handleNewCase(w http.ResponseWriter, r *http.Request, sys SystemConfig, scope ScopeConfig) {
	data := baseView(sys, scope, a.systems(), "", "")
	data.Title = "Create " + sys.Label + " " + scope.Label + " Case"
	data.Payload = createTemplate(sys.ID, scope.ID)
	a.render(w, http.StatusOK, "new", data)
}

func (a *App) handleCreateCase(w http.ResponseWriter, r *http.Request, sys SystemConfig, scope ScopeConfig) {
	if err := r.ParseForm(); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	payload := strings.TrimSpace(r.Form.Get("payload"))
	if payload == "" {
		payload = "{}"
	}
	var parsed any
	if err := json.Unmarshal([]byte(payload), &parsed); err != nil {
		data := baseView(sys, scope, a.systems(), "", "invalid JSON: "+err.Error())
		data.Payload = payload
		a.render(w, http.StatusBadRequest, "new", data)
		return
	}
	resp, err := a.client.JSON(r.Context(), sys, http.MethodPost, scope.BasePath, []byte(payload))
	if err != nil {
		data := baseView(sys, scope, a.systems(), "", err.Error())
		data.Payload = payload
		a.render(w, http.StatusBadGateway, "new", data)
		return
	}
	caseID := responseCaseID(resp.JSON)
	if resp.StatusCode >= 200 && resp.StatusCode < 300 && caseID != "" {
		http.Redirect(w, r, caseURL(sys.ID, scope.ID, caseID), http.StatusSeeOther)
		return
	}
	data := baseView(sys, scope, a.systems(), "", "")
	data.Title = "Create Response"
	data.Payload = payload
	data.Response = &resp
	a.render(w, http.StatusBadGateway, "new", data)
}

func (a *App) handleCaseDetail(w http.ResponseWriter, r *http.Request, sys SystemConfig, scope ScopeConfig, caseID string, notice string) {
	record, recordErr := a.client.JSON(r.Context(), sys, http.MethodGet, casePath(scope, caseID, ""), nil)
	data := baseView(sys, scope, a.systems(), "", "")
	data.Title = sys.Label + " Case " + caseID
	data.CaseID = caseID
	data.Notice = notice
	data.Record = asMap(record.JSON["case"])
	data.Response = &record
	if recordErr != nil {
		data.Error = recordErr.Error()
		a.render(w, http.StatusBadGateway, "case", data)
		return
	}
	if record.StatusCode >= 400 {
		data.Error = fmt.Sprintf("case record returned HTTP %d: %s", record.StatusCode, responseMessage(record.Body))
		a.render(w, http.StatusBadGateway, "case", data)
		return
	}
	result, _ := a.client.JSON(r.Context(), sys, http.MethodGet, casePath(scope, caseID, "result"), nil)
	artifacts, _ := a.client.JSON(r.Context(), sys, http.MethodGet, casePath(scope, caseID, "artifacts"), nil)
	data.Result = result.JSON
	data.Artifacts = artifactsFrom(artifacts.JSON["artifacts"])
	data.HasEvents = artifactNamed(data.Artifacts, "events.ndjson")
	data.HasAttestationEvents = caseHasAttestationEvents(data.Record)
	data.EventIssues, data.RecentEvents, data.EventNotice = a.loadEventData(r.Context(), sys, scope, caseID, data.Artifacts)
	data.AutoRefresh = activeCase(data.Record, data.Result)
	data.CanManage = data.AutoRefresh
	data.CaseAvailable = true
	a.render(w, http.StatusOK, "case", data)
}

func (a *App) handleResult(w http.ResponseWriter, r *http.Request, sys SystemConfig, scope ScopeConfig, caseID string) {
	resp, err := a.client.JSON(r.Context(), sys, http.MethodGet, casePath(scope, caseID, "result"), nil)
	data := baseView(sys, scope, a.systems(), "", "")
	data.Title = sys.Label + " Result " + caseID
	data.CaseID = caseID
	data.Response = &resp
	if err != nil {
		data.Error = err.Error()
		a.render(w, http.StatusBadGateway, "response", data)
		return
	}
	data.AutoRefresh = activeResponse(resp.JSON)
	a.render(w, statusForView(resp.StatusCode), "response", data)
}

func (a *App) handleArtifactList(w http.ResponseWriter, r *http.Request, sys SystemConfig, scope ScopeConfig, caseID string) {
	resp, err := a.client.JSON(r.Context(), sys, http.MethodGet, casePath(scope, caseID, "artifacts"), nil)
	data := baseView(sys, scope, a.systems(), "", "")
	data.Title = sys.Label + " Artifacts " + caseID
	data.CaseID = caseID
	data.Response = &resp
	data.Artifacts = artifactsFrom(resp.JSON["artifacts"])
	if err != nil {
		data.Error = err.Error()
		a.render(w, http.StatusBadGateway, "artifacts", data)
		return
	}
	a.render(w, statusForView(resp.StatusCode), "artifacts", data)
}

func (a *App) handleEvents(w http.ResponseWriter, r *http.Request, sys SystemConfig, scope ScopeConfig, caseID string) {
	limit := boundedQueryInt(r, "limit", defaultEventLimit, 1, maxEventLimit)
	tailBytes := boundedQueryInt(r, "bytes", defaultEventTailBytes, 4096, maxEventTailBytes)
	record, _ := a.client.JSON(r.Context(), sys, http.MethodGet, casePath(scope, caseID, ""), nil)
	result, _ := a.client.JSON(r.Context(), sys, http.MethodGet, casePath(scope, caseID, "result"), nil)
	rows, notice, err := a.loadEventTailRows(r.Context(), sys, scope, caseID, int64(tailBytes), limit)
	data := baseView(sys, scope, a.systems(), "", "")
	data.Title = sys.Label + " Events " + caseID
	data.CaseID = caseID
	data.Record = asMap(record.JSON["case"])
	data.Result = result.JSON
	data.Events = rows
	data.EventNotice = notice
	data.EventLimit = strconv.Itoa(limit)
	data.EventBytes = strconv.Itoa(tailBytes)
	data.AutoRefresh = activeCase(data.Record, data.Result)
	if err != nil {
		data.Error = err.Error()
		a.render(w, http.StatusBadGateway, "events", data)
		return
	}
	a.render(w, http.StatusOK, "events", data)
}

func (a *App) handleLog(w http.ResponseWriter, r *http.Request, sys SystemConfig, scope ScopeConfig, caseID string) {
	name := strings.TrimSpace(r.URL.Query().Get("name"))
	mode := strings.ToLower(strings.TrimSpace(r.URL.Query().Get("mode")))
	if mode != "head" {
		mode = "tail"
	}
	byteCount := boundedQueryInt(r, "bytes", 65536, 1024, 4<<20)
	data := baseView(sys, scope, a.systems(), "", "")
	data.Title = sys.Label + " Log " + caseID
	data.CaseID = caseID
	data.LogName = name
	data.LogMode = mode
	data.LogBytes = strconv.Itoa(byteCount)
	if !validArtifactName(name) {
		data.Error = "log artifact name is required"
		a.render(w, http.StatusBadRequest, "log", data)
		return
	}
	text, notice, err := a.loadLogText(r.Context(), sys, scope, caseID, name, mode, int64(byteCount))
	data.LogText = text
	data.LogNotice = notice
	if err != nil {
		data.Error = err.Error()
		a.render(w, http.StatusBadGateway, "log", data)
		return
	}
	a.render(w, http.StatusOK, "log", data)
}

func (a *App) handleEvidence(w http.ResponseWriter, r *http.Request, sys SystemConfig, scope ScopeConfig, caseID string) {
	evidenceID := strings.TrimSpace(r.URL.Query().Get("id"))
	data := baseView(sys, scope, a.systems(), "", "")
	data.Title = sys.Label + " Evidence " + caseID
	data.CaseID = caseID
	data.EvidenceID = evidenceID
	data.Evidence, data.EvidenceNotice = a.loadEvidenceManifest(r.Context(), sys, scope, caseID)
	if evidenceID == "" {
		a.render(w, http.StatusOK, "evidence", data)
		return
	}
	resp, err := a.client.JSON(r.Context(), sys, http.MethodGet, evidencePath(scope, caseID, evidenceID), nil)
	data.Response = &resp
	if err != nil {
		data.Error = err.Error()
		a.render(w, http.StatusBadGateway, "evidence", data)
		return
	}
	a.render(w, statusForView(resp.StatusCode), "evidence", data)
}

func (a *App) loadEvidenceManifest(ctx context.Context, sys SystemConfig, scope ScopeConfig, caseID string) ([]EvidenceEntry, string) {
	resp, err := a.client.JSON(ctx, sys, http.MethodGet, artifactPath(scope, caseID, "evidence-manifest.json"), nil)
	if err != nil {
		return nil, "evidence-manifest.json request failed: " + err.Error()
	}
	if resp.StatusCode == http.StatusNotFound {
		return nil, "evidence-manifest.json is not available through the artifact API."
	}
	if resp.StatusCode >= 400 {
		message := fieldText(resp.JSON, "message")
		if message == "" {
			message = compactBody(resp.Body)
		}
		return nil, fmt.Sprintf("evidence-manifest.json returned HTTP %d: %s", resp.StatusCode, message)
	}
	entries := evidenceEntriesFrom(resp.JSON)
	if len(entries) == 0 {
		return nil, "evidence-manifest.json returned no evidence records."
	}
	return entries, ""
}

func (a *App) loadEventData(ctx context.Context, sys SystemConfig, scope ScopeConfig, caseID string, artifacts []Artifact) ([]EventIssue, []CaseEvent, string) {
	if !artifactNamed(artifacts, "events.ndjson") {
		return nil, nil, ""
	}
	rows, notice, err := a.loadEventTailRows(ctx, sys, scope, caseID, defaultEventTailBytes, defaultEventLimit)
	if err != nil {
		return nil, nil, "events.ndjson request failed: " + err.Error()
	}
	return eventIssuesFromRows(rows), recentEventsFromRows(rows, 8), notice
}

func (a *App) loadEventTailRows(ctx context.Context, sys SystemConfig, scope ScopeConfig, caseID string, tailBytes int64, limit int) ([]EventRow, string, error) {
	headers := http.Header{}
	headers.Set("Range", fmt.Sprintf("bytes=-%d", tailBytes))
	resp, err := a.client.ProxyWithHeaders(ctx, sys, http.MethodGet, artifactPath(scope, caseID, "events.ndjson"), nil, "", headers)
	if err != nil {
		return nil, "", err
	}
	defer resp.Body.Close()
	raw, err := io.ReadAll(io.LimitReader(resp.Body, tailBytes+1))
	if err != nil {
		return nil, "", err
	}
	if int64(len(raw)) > tailBytes {
		return nil, fmt.Sprintf("events.ndjson response exceeded %d bytes; the service did not return a bounded range", tailBytes), nil
	}
	if resp.StatusCode >= 400 {
		return nil, fmt.Sprintf("events.ndjson returned HTTP %d: %s", resp.StatusCode, responseMessage(raw)), nil
	}
	start, ok := contentRangeStart(resp.Header.Get("Content-Range"))
	dropFirst := resp.StatusCode == http.StatusPartialContent && ok && start > 0
	rows := eventRowsFromNDJSON(raw, start, dropFirst, limit)
	if len(rows) == 0 {
		return nil, fmt.Sprintf("events.ndjson returned no complete event records in the selected %d-byte range; increase the byte window.", tailBytes), nil
	}
	return rows, "", nil
}

func (a *App) loadLogText(ctx context.Context, sys SystemConfig, scope ScopeConfig, caseID string, name string, mode string, byteCount int64) (string, string, error) {
	headers := http.Header{}
	switch mode {
	case "head":
		headers.Set("Range", fmt.Sprintf("bytes=0-%d", byteCount-1))
	default:
		headers.Set("Range", fmt.Sprintf("bytes=-%d", byteCount))
	}
	resp, err := a.client.ProxyWithHeaders(ctx, sys, http.MethodGet, artifactPath(scope, caseID, name), nil, "", headers)
	if err != nil {
		return "", "", err
	}
	defer resp.Body.Close()
	raw, err := io.ReadAll(io.LimitReader(resp.Body, byteCount+1))
	if err != nil {
		return "", "", err
	}
	if int64(len(raw)) > byteCount {
		return "", fmt.Sprintf("%s response exceeded %d bytes; the service did not return a bounded range", name, byteCount), nil
	}
	if resp.StatusCode >= 400 {
		return "", fmt.Sprintf("%s returned HTTP %d: %s", name, resp.StatusCode, responseMessage(raw)), nil
	}
	return compactBody(raw), "", nil
}

func (a *App) handleManageCase(w http.ResponseWriter, r *http.Request, sys SystemConfig, scope ScopeConfig, caseID string) {
	resp, err := a.client.JSON(r.Context(), sys, http.MethodPost, casePath(scope, caseID, scope.ManageAction), nil)
	if err != nil {
		a.handleCaseDetail(w, r, sys, scope, caseID, err.Error())
		return
	}
	notice := fmt.Sprintf("%s returned HTTP %d", scope.ManageAction, resp.StatusCode)
	if resp.StatusCode >= 400 && len(resp.Body) > 0 {
		notice += ": " + strings.TrimSpace(string(resp.Body))
	}
	a.handleCaseDetail(w, r, sys, scope, caseID, notice)
}

func (a *App) handleRawRequest(w http.ResponseWriter, r *http.Request, sys SystemConfig) {
	data := ViewData{Title: sys.Label + " Service Request", Systems: a.systems(), System: sys, Method: http.MethodGet, ServicePath: "/clerk/v1/cases"}
	if r.Method == http.MethodGet {
		a.render(w, http.StatusOK, "request", data)
		return
	}
	if r.Method != http.MethodPost {
		http.Error(w, "use GET or POST", http.StatusMethodNotAllowed)
		return
	}
	if err := r.ParseForm(); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	method := strings.ToUpper(strings.TrimSpace(r.Form.Get("method")))
	servicePath := strings.TrimSpace(r.Form.Get("path"))
	payload := strings.TrimSpace(r.Form.Get("payload"))
	if method == "" {
		method = http.MethodGet
	}
	if servicePath == "" {
		servicePath = "/clerk/v1/cases"
	}
	data.Method = method
	data.ServicePath = servicePath
	data.Payload = payload
	var body []byte
	if payload != "" {
		body = []byte(payload)
	}
	resp, err := a.client.JSON(r.Context(), sys, method, servicePath, body)
	if err != nil {
		data.Error = err.Error()
		a.render(w, http.StatusBadGateway, "request", data)
		return
	}
	data.Response = &resp
	a.render(w, statusForView(resp.StatusCode), "request", data)
}

func (a *App) proxyService(w http.ResponseWriter, r *http.Request, sys SystemConfig, servicePath string) {
	resp, err := a.client.ProxyWithHeaders(r.Context(), sys, r.Method, servicePath, nil, "", proxyRequestHeaders(r.Header))
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadGateway)
		return
	}
	defer resp.Body.Close()
	copyHeader(w.Header(), resp.Header)
	if w.Header().Get("Content-Type") == "" {
		w.Header().Set("Content-Type", "application/octet-stream")
	}
	w.WriteHeader(resp.StatusCode)
	_, _ = io.Copy(w, resp.Body)
}

func proxyMethod(method string) bool {
	return method == http.MethodGet || method == http.MethodHead
}

func proxyRequestHeaders(src http.Header) http.Header {
	out := http.Header{}
	for _, key := range []string{"Range", "If-Range", "If-Modified-Since", "If-None-Match"} {
		for _, value := range src.Values(key) {
			out.Add(key, value)
		}
	}
	return out
}

func (a *App) render(w http.ResponseWriter, status int, name string, data ViewData) {
	w.Header().Set("Content-Type", "text/html; charset=utf-8")
	w.WriteHeader(status)
	if err := a.tmpl.ExecuteTemplate(w, name, data); err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
	}
}

func (a *App) systems() []SystemConfig {
	systems := make([]SystemConfig, 0, len(a.cfg.Systems))
	for _, sys := range a.cfg.Systems {
		systems = append(systems, sys)
	}
	sort.Slice(systems, func(i, j int) bool { return systems[i].ID < systems[j].ID })
	return systems
}

func baseView(sys SystemConfig, scope ScopeConfig, systems []SystemConfig, status string, errText string) ViewData {
	return ViewData{Systems: systems, System: sys, Scope: scope, ScopeOptions: sys.Scopes, StatusFilter: status, Error: errText}
}

func splitPath(p string) []string {
	p = strings.Trim(p, "/")
	if p == "" {
		return nil
	}
	return strings.Split(p, "/")
}

func casePath(scope ScopeConfig, caseID string, suffix string) string {
	p := path.Join(scope.BasePath, url.PathEscape(caseID))
	if strings.TrimSpace(suffix) != "" {
		p = path.Join(p, suffix)
	}
	return p
}

func artifactPath(scope ScopeConfig, caseID string, name string) string {
	return path.Join(scope.BasePath, url.PathEscape(caseID), "artifacts", name)
}

func evidencePath(scope ScopeConfig, caseID string, evidenceID string) string {
	return path.Join(scope.BasePath, url.PathEscape(caseID), "evidence", url.PathEscape(evidenceID))
}

func caseURL(systemID string, scopeID string, caseID string) string {
	return "/system/" + url.PathEscape(systemID) + "/" + url.PathEscape(scopeID) + "/cases/" + url.PathEscape(caseID)
}

func queryEscape(value string) template.URL {
	return template.URL(url.QueryEscape(value))
}

func responseCaseID(m map[string]any) string {
	if id := fieldText(m, "case_id"); id != "" {
		return id
	}
	if rec := asMap(m["case"]); rec != nil {
		return fieldText(rec, "case_id")
	}
	return ""
}

func mapSlice(v any) []map[string]any {
	items, ok := v.([]any)
	if !ok {
		return nil
	}
	out := make([]map[string]any, 0, len(items))
	for _, item := range items {
		if m := asMap(item); m != nil {
			out = append(out, m)
		}
	}
	return out
}

func asMap(v any) map[string]any {
	if m, ok := v.(map[string]any); ok {
		return m
	}
	return nil
}

func artifactsFrom(v any) []Artifact {
	var out []Artifact
	for _, item := range mapSlice(v) {
		name := fieldText(item, "name")
		if name == "" {
			continue
		}
		out = append(out, Artifact{Name: name, Size: fieldText(item, "size_bytes")})
	}
	if items, ok := v.([]any); ok && len(out) == 0 {
		for _, item := range items {
			name := strings.TrimSpace(fmt.Sprint(item))
			if name != "" {
				out = append(out, Artifact{Name: name})
			}
		}
	}
	return out
}

func artifactNamed(artifacts []Artifact, name string) bool {
	for _, artifact := range artifacts {
		if artifact.Name == name {
			return true
		}
	}
	return false
}

func validArtifactName(name string) bool {
	name = strings.TrimSpace(name)
	if name == "" || strings.HasPrefix(name, "/") {
		return false
	}
	clean := path.Clean(name)
	return clean == name && clean != "." && !strings.HasPrefix(clean, "../") && !strings.Contains(clean, "/../")
}

func caseHasAttestationEvents(record map[string]any) bool {
	execution := asMap(record["execution"])
	if execution == nil {
		return false
	}
	return fieldText(execution, "mode") == "attested"
}

func evidenceEntriesFrom(v any) []EvidenceEntry {
	root := v
	if m := asMap(v); m != nil {
		root = m["evidence"]
	}
	var out []EvidenceEntry
	for _, item := range mapSlice(root) {
		id := firstNonEmpty(fieldText(item, "evidence_id"), fieldText(item, "id"))
		if id == "" {
			continue
		}
		out = append(out, EvidenceEntry{
			ID:         id,
			Title:      firstNonEmpty(fieldText(item, "title"), fieldText(item, "original_name"), fieldText(item, "name")),
			MIMEType:   fieldText(item, "mime_type"),
			Size:       fieldText(item, "size_bytes"),
			Status:     fieldText(item, "admissibility_status"),
			Visibility: fieldText(item, "record_visibility"),
			Uses:       stringListText(item["uses"]),
		})
	}
	if items, ok := root.([]any); ok && len(out) == 0 {
		for _, item := range items {
			id := strings.TrimSpace(fmt.Sprint(item))
			if id != "" {
				out = append(out, EvidenceEntry{ID: id})
			}
		}
	}
	return out
}

func stringListText(value any) string {
	items, ok := value.([]any)
	if !ok {
		return ""
	}
	out := make([]string, 0, len(items))
	for _, item := range items {
		text := strings.TrimSpace(fmt.Sprint(item))
		if text != "" {
			out = append(out, text)
		}
	}
	return strings.Join(out, ", ")
}

func eventRowsFromNDJSON(raw []byte, baseOffset int64, dropFirst bool, max int) []EventRow {
	if dropFirst {
		idx := bytes.IndexByte(raw, '\n')
		if idx < 0 {
			return nil
		}
		raw = raw[idx+1:]
		baseOffset += int64(idx + 1)
	}
	var rows []EventRow
	for pos := 0; pos <= len(raw); {
		next := bytes.IndexByte(raw[pos:], '\n')
		end := len(raw)
		if next >= 0 {
			end = pos + next
		}
		line := bytes.TrimSpace(raw[pos:end])
		if len(line) > 0 {
			var event map[string]any
			if err := json.Unmarshal(line, &event); err == nil {
				rows = append(rows, eventRowFrom(event, baseOffset+int64(pos)))
			}
		}
		if next < 0 {
			break
		}
		pos = end + 1
	}
	if max > 0 && len(rows) > max {
		rows = rows[len(rows)-max:]
	}
	for i, j := 0, len(rows)-1; i < j; i, j = i+1, j-1 {
		rows[i], rows[j] = rows[j], rows[i]
	}
	return rows
}

func eventRowFrom(event map[string]any, offset int64) EventRow {
	summary, ok := caseEventFrom(event)
	if !ok {
		summary = fallbackCaseEvent(event)
	}
	return EventRow{
		Offset:    strconv.FormatInt(offset, 10),
		Timestamp: summary.Timestamp,
		Phase:     summary.Phase,
		Type:      summary.Type,
		Actor:     summary.Actor,
		Message:   summary.Message,
		Raw:       event,
	}
}

func fallbackCaseEvent(event map[string]any) CaseEvent {
	payload := asMap(event["payload"])
	message := ""
	if payload != nil {
		message = eventMessage(payload)
	}
	return CaseEvent{
		Timestamp: fieldText(event, "timestamp"),
		Phase:     fieldText(event, "phase"),
		Type:      firstNonEmpty(fieldText(event, "type"), fieldText(event, "action"), "event"),
		Actor:     firstNonEmpty(fieldText(event, "role"), fieldText(payload, "role")),
		Message:   limitText(message, 240),
	}
}

func recentEventsFromRows(rows []EventRow, max int) []CaseEvent {
	if max <= 0 {
		return nil
	}
	if len(rows) > max {
		rows = rows[:max]
	}
	out := make([]CaseEvent, 0, len(rows))
	for _, row := range rows {
		out = append(out, CaseEvent{
			Timestamp: row.Timestamp,
			Phase:     row.Phase,
			Type:      row.Type,
			Actor:     row.Actor,
			Message:   row.Message,
		})
	}
	return out
}

func eventIssuesFromRows(rows []EventRow) []EventIssue {
	var out []EventIssue
	seen := map[string]int{}
	for _, row := range rows {
		issue, ok := eventIssueFrom(row.Raw)
		if !ok {
			continue
		}
		key := issue.Member + "\x00" + issue.Message
		if existing, ok := seen[key]; ok {
			if eventIssueScore(issue) > eventIssueScore(out[existing]) {
				out[existing] = issue
			}
			continue
		}
		seen[key] = len(out)
		out = append(out, issue)
	}
	return out
}

func eventIssueScore(issue EventIssue) int {
	score := 0
	for _, value := range []string{issue.Process, issue.Reason, issue.LogPath} {
		if strings.TrimSpace(value) != "" {
			score++
		}
	}
	if strings.Contains(issue.Type, "failed") {
		score++
	}
	return score
}

func caseEventFrom(event map[string]any) (CaseEvent, bool) {
	eventType := fieldText(event, "type")
	if eventType == "" {
		return adcActionEventFrom(event)
	}
	payload := asMap(event["payload"])
	actor := firstNonEmpty(fieldText(payload, "member_id"), fieldText(payload, "role"), fieldText(event, "role"))
	message := eventMessage(payload)
	return CaseEvent{
		Timestamp: fieldText(event, "timestamp"),
		Phase:     fieldText(event, "phase"),
		Type:      eventType,
		Actor:     actor,
		Message:   limitText(message, 240),
	}, true
}

func adcActionEventFrom(event map[string]any) (CaseEvent, bool) {
	action := fieldText(event, "action")
	if action == "" {
		return CaseEvent{}, false
	}
	return CaseEvent{
		Timestamp: fieldText(event, "timestamp"),
		Phase:     firstNonEmpty(fieldText(event, "phase"), adcActionPhase(event)),
		Type:      action,
		Actor:     fieldText(event, "role"),
		Message:   limitText(adcActionMessage(event), 240),
	}, true
}

func adcActionPhase(event map[string]any) string {
	response := asMap(event["response"])
	if response == nil {
		return ""
	}
	if caseData := asMap(response["case"]); caseData != nil {
		if phase := fieldText(caseData, "phase"); phase != "" {
			return phase
		}
	}
	if state := asMap(response["state"]); state != nil {
		if caseData := asMap(state["case"]); caseData != nil {
			if phase := fieldText(caseData, "phase"); phase != "" {
				return phase
			}
		}
	}
	return ""
}

func adcActionMessage(event map[string]any) string {
	action := fieldText(event, "action")
	payload := asMap(event["payload"])
	if payload != nil {
		if reason := fieldText(payload, "reason"); reason != "" {
			return reason
		}
		if summary := adcPayloadSummary(payload); summary != "" {
			return summary
		}
	}
	response := asMap(event["response"])
	if response != nil {
		if result := fieldText(response, "result_kind"); result != "" {
			return result
		}
		if errText := fieldText(response, "error"); errText != "" {
			return errText
		}
		if summary := adcResponseSummary(action, response); summary != "" {
			return summary
		}
	}
	var parts []string
	if turn := fieldText(event, "turn"); turn != "" {
		parts = append(parts, "turn "+turn)
	}
	if step := fieldText(event, "step"); step != "" {
		parts = append(parts, "step "+step)
	}
	return strings.Join(parts, " ")
}

func adcPayloadSummary(payload map[string]any) string {
	var parts []string
	for _, key := range []string{
		"file_id",
		"juror_id",
		"vote",
		"damages",
		"confidence",
		"exchange_id",
		"asked_by",
		"allowed",
		"tool_name",
		"kind",
		"party",
		"report_id",
		"exhibit_id",
	} {
		text := fieldText(payload, key)
		if text == "" {
			continue
		}
		if key == "tool_name" {
			key = "tool"
		}
		parts = append(parts, key+"="+limitText(text, 120))
		if len(parts) == 4 {
			break
		}
	}
	return strings.Join(parts, " ")
}

func adcResponseSummary(action string, response map[string]any) string {
	switch action {
	case "list_case_files":
		if items, ok := response["files"].([]any); ok {
			return fmt.Sprintf("files=%d", len(items))
		}
	case "get_case":
		if caseData := asMap(response["case"]); caseData != nil {
			var parts []string
			if status := fieldText(caseData, "status"); status != "" {
				parts = append(parts, "status="+status)
			}
			if phase := fieldText(caseData, "phase"); phase != "" {
				parts = append(parts, "phase="+phase)
			}
			return strings.Join(parts, " ")
		}
	}
	return ""
}

func eventMessage(payload map[string]any) string {
	if payload == nil {
		return ""
	}
	if message := firstNonEmpty(fieldText(payload, "message"), fieldText(payload, "cause"), fieldText(payload, "agent_error")); message != "" {
		return message
	}
	if evidenceID := fieldText(payload, "evidence_id"); evidenceID != "" {
		if byteCount := fieldText(payload, "byte_count"); byteCount != "" {
			return evidenceID + " (" + byteCount + " bytes)"
		}
		return evidenceID
	}
	if nested := asMap(payload["payload"]); nested != nil {
		if vote := fieldText(nested, "vote"); vote != "" {
			return "vote=" + vote
		}
		if answer := fieldText(nested, "answer"); answer != "" {
			return "answer=" + answer
		}
	}
	if actionType := fieldText(payload, "action_type"); actionType != "" {
		if opportunityID := fieldText(payload, "opportunity_id"); opportunityID != "" {
			return actionType + " " + opportunityID
		}
		return actionType
	}
	return ""
}

func eventIssueFrom(event map[string]any) (EventIssue, bool) {
	eventType := fieldText(event, "type")
	payload := asMap(event["payload"])
	reason := fieldText(payload, "reason")
	message := firstNonEmpty(fieldText(payload, "message"), fieldText(payload, "cause"), fieldText(payload, "agent_error"))
	if !strings.Contains(eventType, "failed") && !strings.Contains(reason, "failed") && message == "" {
		return EventIssue{}, false
	}
	return EventIssue{
		Timestamp: fieldText(event, "timestamp"),
		Phase:     fieldText(event, "phase"),
		Type:      eventType,
		Member:    firstNonEmpty(fieldText(payload, "member_id"), fieldText(payload, "role")),
		Process:   fieldText(payload, "process_name"),
		Reason:    reason,
		Message:   limitText(message, 1600),
		LogPath:   fieldText(payload, "agent_error_log"),
	}, true
}

func sortedKeys(m map[string]any) []string {
	keys := make([]string, 0, len(m))
	for key := range m {
		keys = append(keys, key)
	}
	sort.Strings(keys)
	return keys
}

func fieldText(v any, key string) string {
	m, ok := v.(map[string]any)
	if !ok || m == nil {
		return ""
	}
	value := m[key]
	if value == nil {
		return ""
	}
	return strings.TrimSpace(fmt.Sprint(value))
}

func caseListFacts(record map[string]any) string {
	if record == nil {
		return ""
	}
	var facts []recordFact
	seen := map[string]bool{}
	addScalarFacts(&facts, seen, "", record, []string{
		"case_status",
		"phase",
		"resolution",
		"final_reason",
		"mode",
		"exit_code",
	})
	if summary := asMap(record["summary"]); summary != nil {
		for _, fact := range recordFacts(summary) {
			switch fact.Label {
			case "case.status", "case.phase", "case.resolution", "case.final_reason", "case.council_members", "case.vote_tally", "case.answers", "case.case_files", "case.technical_reports", "resolution", "final_reason", "vote_tally", "answers", "events":
				addRecordFact(&facts, seen, fact.Label, fact.Value)
			}
			if len(facts) >= 6 {
				break
			}
		}
	}
	if len(facts) == 0 {
		return ""
	}
	parts := make([]string, 0, len(facts))
	for _, fact := range facts {
		parts = append(parts, fact.Label+"="+fact.Value)
	}
	return limitText(strings.Join(parts, "; "), 500)
}

func recordValue(sys SystemConfig, scope ScopeConfig, caseID string, key string, value any) template.HTML {
	if value == nil {
		return ""
	}
	if html, ok := structuredRecordValue(value); ok {
		return html
	}
	text := strings.TrimSpace(fmt.Sprint(value))
	if text == "" {
		return ""
	}
	if name := logArtifactName(key, text); name != "" {
		href := caseURL(sys.ID, scope.ID, caseID) + "/log?name=" + url.QueryEscape(name)
		return template.HTML(`<a href="` + template.HTMLEscapeString(href) + `">` + template.HTMLEscapeString(text) + `</a>`)
	}
	return template.HTML(template.HTMLEscapeString(text))
}

func structuredRecordValue(value any) (template.HTML, bool) {
	facts := recordFacts(value)
	var label string
	switch v := value.(type) {
	case map[string]any:
		label = fmt.Sprintf("full JSON (%d keys)", len(v))
	case []any:
		label = fmt.Sprintf("full JSON (%d items)", len(v))
	default:
		return "", false
	}
	var b strings.Builder
	if len(facts) > 0 {
		b.WriteString(`<dl class="record-facts">`)
		for _, fact := range facts {
			b.WriteString(`<dt>`)
			b.WriteString(template.HTMLEscapeString(fact.Label))
			b.WriteString(`</dt><dd>`)
			b.WriteString(template.HTMLEscapeString(fact.Value))
			b.WriteString(`</dd>`)
		}
		b.WriteString(`</dl>`)
	}
	b.WriteString(`<details class="record-details"><summary>`)
	b.WriteString(template.HTMLEscapeString(label))
	b.WriteString(`</summary><pre>`)
	b.WriteString(template.HTMLEscapeString(boundedJSON(value)))
	b.WriteString(`</pre></details>`)
	return template.HTML(b.String()), true
}

func recordFacts(value any) []recordFact {
	switch v := value.(type) {
	case map[string]any:
		return mapRecordFacts(v)
	case []any:
		return []recordFact{{Label: "items", Value: fmt.Sprint(len(v))}}
	default:
		return nil
	}
}

func mapRecordFacts(m map[string]any) []recordFact {
	var facts []recordFact
	seen := map[string]bool{}
	addScalarFacts(&facts, seen, "", m, []string{
		"status",
		"case_status",
		"phase",
		"final_reason",
		"resolution",
		"council_backend",
		"started_at",
		"finished_at",
		"caption",
		"question",
		"proposition",
		"error",
	})
	addMapFact(&facts, seen, "answers", m["answers"])
	addMapFact(&facts, seen, "vote_tally", m["vote_tally"])
	if finalState := asMap(m["final_state"]); finalState != nil {
		if caseState := asMap(finalState["case"]); caseState != nil {
			addScalarFacts(&facts, seen, "case.", caseState, []string{
				"status",
				"case_status",
				"phase",
				"final_reason",
				"resolution",
				"question",
				"proposition",
			})
			addMapFact(&facts, seen, "case.answers", caseState["answers"])
			addMapFact(&facts, seen, "case.vote_tally", caseState["vote_tally"])
			addCountFacts(&facts, seen, caseState, "case.", []string{
				"council",
				"council_members",
				"events",
				"evidence",
				"submitted_evidence",
				"offered_evidence",
				"case_files",
				"attorneys",
				"technical_reports",
			})
		}
	}
	addCountFacts(&facts, seen, m, "", []string{
		"council",
		"council_members",
		"events",
		"evidence",
		"submitted_evidence",
		"offered_evidence",
		"case_files",
		"attorneys",
		"technical_reports",
	})
	return facts
}

func addScalarFacts(facts *[]recordFact, seen map[string]bool, prefix string, m map[string]any, keys []string) {
	for _, key := range keys {
		if text, ok := scalarFactText(m[key]); ok {
			addRecordFact(facts, seen, prefix+key, limitText(text, 500))
		}
	}
}

func addMapFact(facts *[]recordFact, seen map[string]bool, label string, value any) {
	if m := asMap(value); m != nil {
		if text := conciseMapText(m, 10); text != "" {
			addRecordFact(facts, seen, label, text)
		}
	}
}

func addCountFacts(facts *[]recordFact, seen map[string]bool, m map[string]any, prefix string, keys []string) {
	for _, key := range keys {
		if text, ok := countFactText(m[key]); ok {
			addRecordFact(facts, seen, prefix+key, text)
		}
	}
}

func addRecordFact(facts *[]recordFact, seen map[string]bool, label string, value string) {
	value = strings.TrimSpace(value)
	if label == "" || value == "" || seen[label] {
		return
	}
	seen[label] = true
	*facts = append(*facts, recordFact{Label: label, Value: value})
}

func scalarFactText(value any) (string, bool) {
	switch v := value.(type) {
	case nil:
		return "", false
	case map[string]any, []any:
		return "", false
	case string:
		text := strings.TrimSpace(v)
		return text, text != ""
	default:
		text := strings.TrimSpace(fmt.Sprint(value))
		return text, text != ""
	}
}

func conciseMapText(m map[string]any, maxKeys int) string {
	keys := sortedKeys(m)
	if maxKeys > 0 && len(keys) > maxKeys {
		keys = keys[:maxKeys]
	}
	parts := make([]string, 0, len(keys)+1)
	for _, key := range keys {
		text, ok := scalarFactText(m[key])
		if !ok {
			continue
		}
		parts = append(parts, key+"="+limitText(text, 120))
	}
	if len(m) > len(keys) {
		parts = append(parts, fmt.Sprintf("+%d more", len(m)-len(keys)))
	}
	return strings.Join(parts, ", ")
}

func countFactText(value any) (string, bool) {
	items, ok := value.([]any)
	if !ok {
		if m := asMap(value); m != nil {
			return fmt.Sprint(len(m)), true
		}
		return "", false
	}
	text := fmt.Sprint(len(items))
	if counts := arrayFieldCounts(items, "status"); counts != "" {
		text += " (" + counts + ")"
	} else if counts := arrayFieldCounts(items, "vote"); counts != "" {
		text += " (" + counts + ")"
	}
	return text, true
}

func arrayFieldCounts(items []any, field string) string {
	counts := map[string]int{}
	for _, item := range items {
		m := asMap(item)
		if m == nil {
			continue
		}
		value := fieldText(m, field)
		if value == "" {
			continue
		}
		counts[value]++
	}
	if len(counts) == 0 {
		return ""
	}
	keys := make([]string, 0, len(counts))
	for key := range counts {
		keys = append(keys, key)
	}
	sort.Strings(keys)
	parts := make([]string, 0, len(keys))
	for _, key := range keys {
		parts = append(parts, fmt.Sprintf("%s=%d", key, counts[key]))
	}
	return strings.Join(parts, ", ")
}

func logArtifactName(key string, text string) string {
	if key != "stdout_log" && key != "stderr_log" {
		return ""
	}
	return matchingLogArtifactName(text)
}

func isLogArtifactName(text string) bool {
	return matchingLogArtifactName(text) != ""
}

func matchingLogArtifactName(text string) string {
	for _, name := range []string{
		"clerk.stdout",
		"clerk.stderr",
		"service-logs/adc.stdout",
		"service-logs/adc.stderr",
		"service-logs/aar.stdout",
		"service-logs/aar.stderr",
		"service-logs/aard.stdout",
		"service-logs/aard.stderr",
	} {
		if text == name || strings.HasSuffix(text, "/"+name) {
			return name
		}
	}
	return ""
}

func prettyJSON(v any) string {
	if v == nil {
		return ""
	}
	raw, err := json.MarshalIndent(v, "", "  ")
	if err != nil {
		return fmt.Sprint(v)
	}
	return string(raw)
}

func boundedJSON(v any) string {
	text := prettyJSON(v)
	const max = 12000
	if len(text) <= max {
		return text
	}
	return fmt.Sprintf("[JSON not rendered: formatted value is %d bytes, limit is %d bytes]", len(text), max)
}

func responseText(resp *Response) string {
	if resp == nil {
		return ""
	}
	text := ""
	if resp.JSON != nil {
		text = prettyJSON(resp.JSON)
	} else {
		text = compactBody(resp.Body)
	}
	const max = 12000
	if len(text) <= max {
		return text
	}
	return fmt.Sprintf("[response body not rendered: formatted response is %d bytes, limit is %d bytes]", len(text), max)
}

func contentRangeStart(value string) (int64, bool) {
	value = strings.TrimSpace(value)
	if !strings.HasPrefix(value, "bytes ") {
		return 0, false
	}
	value = strings.TrimPrefix(value, "bytes ")
	dash := strings.IndexByte(value, '-')
	if dash < 0 {
		return 0, false
	}
	start, err := strconv.ParseInt(value[:dash], 10, 64)
	if err != nil || start < 0 {
		return 0, false
	}
	return start, true
}

func responseMessage(raw []byte) string {
	var m map[string]any
	if err := json.Unmarshal(bytes.TrimSpace(raw), &m); err == nil {
		if text := fieldText(m, "message"); text != "" {
			return text
		}
		if errData := asMap(m["error"]); errData != nil {
			if text := fieldText(errData, "message"); text != "" {
				return text
			}
			if text := fieldText(errData, "code"); text != "" {
				return text
			}
		}
		if text := fieldText(m, "error"); text != "" {
			return text
		}
	}
	return compactBody(raw)
}

func boundedQueryInt(r *http.Request, key string, fallback int, minValue int, maxValue int) int {
	text := strings.TrimSpace(r.URL.Query().Get(key))
	if text == "" {
		return fallback
	}
	value, err := strconv.Atoi(text)
	if err != nil {
		return fallback
	}
	if value < minValue {
		return minValue
	}
	if value > maxValue {
		return maxValue
	}
	return value
}

func activeCase(record map[string]any, result map[string]any) bool {
	return activeResponse(result) || activeStatus(fieldText(record, "status"))
}

func activeResponse(m map[string]any) bool {
	return activeStatus(fieldText(m, "status")) ||
		activeStatus(fieldText(m, "case_status")) ||
		activeStatus(fieldText(m, "phase"))
}

func activeStatus(status string) bool {
	switch strings.ToLower(strings.TrimSpace(status)) {
	case "active", "arguments", "closings", "deliberation", "open", "openings", "pending", "queued", "rebuttals", "running", "starting", "surrebuttals":
		return true
	default:
		return false
	}
}

func firstNonEmpty(values ...string) string {
	for _, value := range values {
		if strings.TrimSpace(value) != "" {
			return strings.TrimSpace(value)
		}
	}
	return ""
}

func limitText(text string, max int) string {
	text = strings.TrimSpace(text)
	if max <= 0 || len(text) <= max {
		return text
	}
	return text[:max] + fmt.Sprintf("\n[truncated to %d of %d bytes]", max, len(text))
}

func createTemplate(systemID string, scopeID string) string {
	switch systemID {
	case "adc":
		return `{
  "mode": "run",
  "case_id": "adc-web-YYYYMMDDHHMMSS",
  "complaint_path": "/path/to/carve/adc/examples/ex1/complaint.md",
  "openclaw_auth": "codex",
  "juror_personas": "/path/to/carve/common/data/personas/pool.jsonl"
}`
	case "arb":
		if scopeID == "direct" {
			return `{
  "case_id": "arb-api-web-YYYYMMDDHHMMSS",
  "complaint_path": "/path/to/carve/arb/examples/ex01/complaint.md",
  "council_backend": "councilapi"
}`
		}
		return `{
  "case_id": "arb-web-YYYYMMDDHHMMSS",
  "example": "ex01",
  "out_dir": "arb-web-YYYYMMDDHHMMSS",
  "openclaw_auth": "codex",
  "council_pool_path": "/path/to/carve/arb/pool.jsonl"
}`
	case "arbd":
		if scopeID == "direct" {
			return `{
  "case_id": "arbd-api-web-YYYYMMDDHHMMSS",
  "complaint_path": "/path/to/carve/arbd/examples/ex1/complaint.md",
  "council_backend": "councilapi"
}`
		}
		return `{
  "case_id": "arbd-web-YYYYMMDDHHMMSS",
  "example": "ex1",
  "out_dir": "arbd-web-YYYYMMDDHHMMSS",
  "openclaw_auth": "codex",
  "council_pool_path": "/path/to/carve/common/data/personas/pool.jsonl"
}`
	default:
		return "{}"
	}
}

func statusForView(serviceStatus int) int {
	if serviceStatus >= 500 {
		return http.StatusBadGateway
	}
	if serviceStatus >= 400 {
		return http.StatusOK
	}
	return http.StatusOK
}

func copyHeader(dst http.Header, src http.Header) {
	for key, values := range src {
		if strings.EqualFold(key, "Content-Length") {
			continue
		}
		for _, value := range values {
			dst.Add(key, value)
		}
	}
	if ct := dst.Get("Content-Type"); ct != "" {
		if media, _, err := mime.ParseMediaType(ct); err == nil {
			dst.Set("Content-Type", media)
		}
	}
}

func compactBody(body []byte) string {
	body = bytes.TrimSpace(body)
	if len(body) == 0 {
		return ""
	}
	var value any
	dec := json.NewDecoder(bytes.NewReader(body))
	dec.UseNumber()
	if err := dec.Decode(&value); err == nil {
		return prettyJSON(value)
	}
	return string(body)
}
