package console

import (
	"encoding/json"
	"io"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
)

func TestListCasesForwardsBearerAndRendersRows(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/clerk/v1/cases" {
			t.Fatalf("path = %s", r.URL.Path)
		}
		if r.Header.Get("Authorization") != "Bearer service-token" {
			t.Fatalf("authorization = %q", r.Header.Get("Authorization"))
		}
		writeTestJSON(w, map[string]any{
			"ok": true,
			"cases": []map[string]any{{
				"case_id":    "case-1",
				"run_id":     "run-case-1",
				"status":     "running",
				"created_at": "2026-07-10T00:00:00Z",
				"summary": map[string]any{
					"final_state": map[string]any{
						"case": map[string]any{
							"phase":  "post_verdict",
							"status": "judgment_entered",
						},
					},
				},
			}},
		})
	}))
	defer api.Close()
	app := testApp(t, api.URL, "service-token")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	if !strings.Contains(body, "case-1") || !strings.Contains(body, "running") || !strings.Contains(body, "case.phase=post_verdict") {
		t.Fatalf("body missing case row: %s", body)
	}
}

func TestIndexDoesNotExposeADCAlias(t *testing.T) {
	app, err := New(DefaultConfig())
	if err != nil {
		t.Fatal(err)
	}
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	for _, unwanted := range []string{
		"ADC API Alias",
		"/system/adc/api/cases",
	} {
		if strings.Contains(body, unwanted) {
			t.Fatalf("body includes %q: %s", unwanted, body)
		}
	}
}

func TestDirectCreateTemplatesOmitOutputDir(t *testing.T) {
	for _, systemID := range []string{"arb", "arbd"} {
		body := createTemplate(systemID, "direct")
		if strings.Contains(body, `"out_dir"`) {
			t.Fatalf("%s direct template includes out_dir: %s", systemID, body)
		}
	}
}

func TestCreateTemplatesUseExplicitCorePaths(t *testing.T) {
	body := createTemplate("adc", "clerk")
	for _, unwanted := range []string{`"out_dir"`} {
		if strings.Contains(body, unwanted) {
			t.Fatalf("ADC template includes %s: %s", unwanted, body)
		}
	}
	for _, want := range []string{
		`"openclaw_auth": "codex"`,
		`"complaint_path": "/path/to/carve/adc/examples/ex1/complaint.md"`,
		`"juror_personas": "/path/to/carve/common/data/personas/pool.jsonl"`,
	} {
		if !strings.Contains(body, want) {
			t.Fatalf("ADC template missing %s: %s", want, body)
		}
	}
	for systemID, want := range map[string]string{
		"arb":  `"council_pool_path": "/path/to/carve/arb/pool.jsonl"`,
		"arbd": `"council_pool_path": "/path/to/carve/common/data/personas/pool.jsonl"`,
	} {
		body := createTemplate(systemID, "clerk")
		if !strings.Contains(body, want) {
			t.Fatalf("%s template missing %s: %s", systemID, want, body)
		}
	}
}

func TestCreateCasePostsRawJSONAndRedirects(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost || r.URL.Path != "/clerk/v1/cases" {
			t.Fatalf("request = %s %s", r.Method, r.URL.Path)
		}
		raw, err := io.ReadAll(r.Body)
		if err != nil {
			t.Fatal(err)
		}
		var payload map[string]any
		if err := json.Unmarshal(raw, &payload); err != nil {
			t.Fatalf("bad payload: %v", err)
		}
		if payload["case_id"] != "case-2" {
			t.Fatalf("payload = %#v", payload)
		}
		writeTestJSON(w, map[string]any{"ok": true, "case": map[string]any{"case_id": "case-2", "status": "starting"}})
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodPost, "/system/arb/clerk/cases", strings.NewReader("payload=%7B%22case_id%22%3A%22case-2%22%7D"))
	req.Header.Set("Content-Type", "application/x-www-form-urlencoded")
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusSeeOther {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	if got := rec.Header().Get("Location"); got != "/system/arb/clerk/cases/case-2" {
		t.Fatalf("location = %q", got)
	}
}

func TestArtifactProxyUsesServiceAPI(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/clerk/v1/cases/case-3/artifacts/digest.md" {
			t.Fatalf("path = %s", r.URL.Path)
		}
		w.Header().Set("Content-Type", "text/markdown; charset=utf-8")
		_, _ = w.Write([]byte("# Digest\n"))
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/case-3/artifacts/digest.md", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	if rec.Body.String() != "# Digest\n" {
		t.Fatalf("body = %q", rec.Body.String())
	}
}

func TestArtifactProxyForwardsRangeHeaders(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/clerk/v1/cases/case-3/artifacts/events.ndjson" {
			t.Fatalf("path = %s", r.URL.Path)
		}
		if r.Header.Get("Range") != "bytes=5-9" {
			t.Fatalf("range = %q", r.Header.Get("Range"))
		}
		if r.Header.Get("If-Range") != `"abc"` {
			t.Fatalf("if-range = %q", r.Header.Get("If-Range"))
		}
		w.Header().Set("Accept-Ranges", "bytes")
		w.Header().Set("Content-Range", "bytes 5-9/20")
		w.WriteHeader(http.StatusPartialContent)
		_, _ = w.Write([]byte("56789"))
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/case-3/artifacts/events.ndjson", nil)
	req.Header.Set("Range", "bytes=5-9")
	req.Header.Set("If-Range", `"abc"`)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusPartialContent {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	if rec.Header().Get("Content-Range") != "bytes 5-9/20" {
		t.Fatalf("content-range = %q", rec.Header().Get("Content-Range"))
	}
	if rec.Body.String() != "56789" {
		t.Fatalf("body = %q", rec.Body.String())
	}
}

func TestArtifactProxyPreservesNestedArtifactName(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/api/v1/cases/case-3/artifacts/service-logs/aar.stderr" {
			t.Fatalf("path = %s", r.URL.Path)
		}
		w.Header().Set("Content-Type", "text/plain")
		_, _ = w.Write([]byte("stderr\n"))
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/direct/cases/case-3/artifacts/service-logs%2Faar.stderr", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	if rec.Body.String() != "stderr\n" {
		t.Fatalf("body = %q", rec.Body.String())
	}
}

func TestCaseDetailLinksStructuredLogFields(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/clerk/v1/cases/case-log":
			writeTestJSON(w, map[string]any{
				"ok": true,
				"case": map[string]any{
					"case_id":    "case-log",
					"status":     "failed",
					"stdout_log": "/tmp/run/case-log/clerk.stdout",
					"stderr_log": "/tmp/run/case-log/clerk.stderr",
				},
			})
		case "/clerk/v1/cases/case-log/result":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-log", "status": "failed"})
		case "/clerk/v1/cases/case-log/artifacts":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-log", "artifacts": []map[string]any{{"name": "clerk.stderr", "size_bytes": 11}}})
		default:
			t.Fatalf("path = %s", r.URL.Path)
		}
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/case-log", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	for _, want := range []string{
		`href="/system/arb/clerk/cases/case-log/log?name=clerk.stdout"`,
		`href="/system/arb/clerk/cases/case-log/log?name=clerk.stderr"`,
		"/tmp/run/case-log/clerk.stderr",
	} {
		if !strings.Contains(body, want) {
			t.Fatalf("body missing %q: %s", want, body)
		}
	}
}

func TestLogViewerReadsTailRange(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/clerk/v1/cases/case-log/artifacts/clerk.stderr" {
			t.Fatalf("path = %s", r.URL.Path)
		}
		if r.Header.Get("Range") != "bytes=-4096" {
			t.Fatalf("range = %q", r.Header.Get("Range"))
		}
		w.Header().Set("Content-Type", "text/plain")
		w.Header().Set("Content-Range", "bytes 20-35/36")
		w.WriteHeader(http.StatusPartialContent)
		_, _ = w.Write([]byte("last log line\n"))
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/case-log/log?name=clerk.stderr&bytes=4096", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	for _, want := range []string{
		"ARB Log case-log",
		"last log line",
		`href="/system/arb/clerk/cases/case-log/artifacts/clerk.stderr"`,
		`<option value="tail" selected>tail</option>`,
	} {
		if !strings.Contains(body, want) {
			t.Fatalf("body missing %q: %s", want, body)
		}
	}
}

func TestUnknownCaseOmitsActionsAndShowsServiceError(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/clerk/v1/cases/missing-case" {
			t.Fatalf("unexpected request after missing case: %s", r.URL.Path)
		}
		w.WriteHeader(http.StatusNotFound)
		writeTestJSON(w, map[string]any{"ok": false, "error": map[string]any{"code": "unknown_case", "message": "unknown case_id"}})
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/missing-case", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusBadGateway {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	for _, want := range []string{
		"case record returned HTTP 404: unknown case_id",
		"unknown_case",
		"Case Response",
	} {
		if !strings.Contains(body, want) {
			t.Fatalf("body missing %q: %s", want, body)
		}
	}
	for _, unwanted := range []string{
		"/result",
		"/artifacts",
		"/evidence",
		"/manage",
	} {
		if strings.Contains(body, unwanted) {
			t.Fatalf("body includes stale action %q: %s", unwanted, body)
		}
	}
}

func TestArtifactListLinksNestedLogsToViewer(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/clerk/v1/cases/case-log/artifacts" {
			t.Fatalf("path = %s", r.URL.Path)
		}
		writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-log", "artifacts": []map[string]any{{"name": "service-logs/adc.stderr", "size_bytes": 42}}})
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/case-log/artifacts", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	for _, want := range []string{
		`href="/system/arb/clerk/cases/case-log/log?name=service-logs%2Fadc.stderr"`,
		`href="/system/arb/clerk/cases/case-log/artifacts/service-logs%2Fadc.stderr"`,
	} {
		if !strings.Contains(body, want) {
			t.Fatalf("body missing %q: %s", want, body)
		}
	}
	if strings.Contains(body, "service-logs%252Fadc.stderr") {
		t.Fatalf("body double-encodes nested log name: %s", body)
	}
}

func TestCaseDetailCompactsStructuredFieldsAndRefreshesRunningCase(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/clerk/v1/cases/case-running":
			writeTestJSON(w, map[string]any{
				"ok": true,
				"case": map[string]any{
					"case_id": "case-running",
					"status":  "running",
					"summary": map[string]any{
						"answers": map[string]any{"C5": 73},
						"events":  []any{"one", "two"},
					},
				},
			})
		case "/clerk/v1/cases/case-running/result":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-running", "status": "running"})
		case "/clerk/v1/cases/case-running/artifacts":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-running", "artifacts": []map[string]any{{"name": "events.ndjson", "size_bytes": 256}}})
		case "/clerk/v1/cases/case-running/artifacts/events.ndjson":
			if r.Header.Get("Range") != "bytes=-1048576" {
				t.Fatalf("range = %q", r.Header.Get("Range"))
			}
			w.Header().Set("Content-Type", "application/x-ndjson")
			_, _ = w.Write([]byte(`{"timestamp":"2026-07-10T18:35:21Z","phase":"openings","type":"run_initialized","payload":{"role":"system"}}` + "\n"))
			_, _ = w.Write([]byte(`{"timestamp":"2026-07-10T18:35:42Z","phase":"openings","type":"evidence_read","role":"plaintiff","payload":{"evidence_id":"ev_deadline","byte_count":820}}` + "\n"))
			_, _ = w.Write([]byte(`{"timestamp":"2026-07-10T18:36:02Z","phase":"arguments","type":"opportunity_ready","payload":{"role":"plaintiff","message":"plaintiff may file argument"}}` + "\n"))
			_, _ = w.Write([]byte(`{"timestamp":"2026-07-10T18:52:41Z","phase":"deliberation","type":"council_vote","payload":{"member_id":"C1","payload":{"vote":"demonstrated"}}}` + "\n"))
		default:
			t.Fatalf("path = %s", r.URL.Path)
		}
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/case-running", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	for _, want := range []string{
		`<meta http-equiv="refresh" content="10">`,
		`action="/system/arb/clerk/cases/case-running/manage"`,
		"<dt>answers</dt><dd>C5=73</dd>",
		"<dt>events</dt><dd>2</dd>",
		"<summary>full JSON (2 keys)</summary>",
		"Recent Events",
		"opportunity_ready",
		"plaintiff may file argument",
		"ev_deadline (820 bytes)",
		"vote=demonstrated",
	} {
		if !strings.Contains(body, want) {
			t.Fatalf("body missing %q: %s", want, body)
		}
	}
	if strings.Contains(body, "map[answers") {
		t.Fatalf("body contains fmt map rendering: %s", body)
	}
	if strings.Contains(body, "object (2 keys)") {
		t.Fatalf("body contains placeholder structured value: %s", body)
	}
	if strings.Contains(body, "attestation events") {
		t.Fatalf("local case includes attestation events link: %s", body)
	}
}

func TestEventsPageReadsTailRange(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/clerk/v1/cases/case-events":
			writeTestJSON(w, map[string]any{"ok": true, "case": map[string]any{"case_id": "case-events", "status": "running"}})
		case "/clerk/v1/cases/case-events/result":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-events", "status": "running"})
		case "/clerk/v1/cases/case-events/artifacts/events.ndjson":
			if r.Header.Get("Range") != "bytes=-8192" {
				t.Fatalf("range = %q", r.Header.Get("Range"))
			}
			w.Header().Set("Content-Type", "application/x-ndjson")
			w.Header().Set("Content-Range", "bytes 100-420/421")
			w.WriteHeader(http.StatusPartialContent)
			_, _ = w.Write([]byte(`{"partial":` + "\n"))
			_, _ = w.Write([]byte(`{"timestamp":"2026-07-10T18:36:02Z","phase":"arguments","type":"opportunity_ready","payload":{"role":"plaintiff","message":"plaintiff may file argument"}}` + "\n"))
			_, _ = w.Write([]byte(`{"timestamp":"2026-07-10T18:52:41Z","phase":"deliberation","type":"council_vote","payload":{"member_id":"C1","payload":{"vote":"demonstrated"}}}` + "\n"))
		default:
			t.Fatalf("path = %s", r.URL.Path)
		}
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/case-events/events?limit=1&bytes=8192", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	for _, want := range []string{
		`<meta http-equiv="refresh" content="10">`,
		"raw events.ndjson",
		"council_vote",
		"vote=demonstrated",
		"<summary>JSON</summary>",
	} {
		if !strings.Contains(body, want) {
			t.Fatalf("body missing %q: %s", want, body)
		}
	}
	for _, unwanted := range []string{
		"opportunity_ready",
		"partial",
	} {
		if strings.Contains(body, unwanted) {
			t.Fatalf("body includes %q: %s", unwanted, body)
		}
	}
}

func TestCaseDetailOmitsLargeStructuredRecordValue(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/clerk/v1/cases/case-large-record":
			writeTestJSON(w, map[string]any{
				"ok": true,
				"case": map[string]any{
					"case_id": "case-large-record",
					"status":  "completed",
					"summary": map[string]any{
						"final_state": map[string]any{
							"case": map[string]any{
								"status": "judgment_entered",
								"phase":  "post_verdict",
							},
						},
						"events": []any{"one", "two", "three"},
						"text":   strings.Repeat("x", 13000),
					},
				},
			})
		case "/clerk/v1/cases/case-large-record/result":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-large-record", "status": "done"})
		case "/clerk/v1/cases/case-large-record/artifacts":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-large-record", "artifacts": []map[string]any{}})
		default:
			t.Fatalf("path = %s", r.URL.Path)
		}
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/case-large-record", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	for _, want := range []string{
		"<dt>case.status</dt><dd>judgment_entered</dd>",
		"<dt>case.phase</dt><dd>post_verdict</dd>",
		"<dt>events</dt><dd>3</dd>",
		"JSON not rendered",
	} {
		if !strings.Contains(body, want) {
			t.Fatalf("body missing %q: %s", want, body)
		}
	}
	if strings.Contains(body, strings.Repeat("x", 1000)) {
		t.Fatalf("large structured record was embedded: %s", body)
	}
}

func TestCaseDetailLinksAttestationEventsForAttestedCase(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/clerk/v1/cases/case-attested":
			writeTestJSON(w, map[string]any{
				"ok": true,
				"case": map[string]any{
					"case_id": "case-attested",
					"status":  "running",
					"execution": map[string]any{
						"mode": "attested",
					},
				},
			})
		case "/clerk/v1/cases/case-attested/result":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-attested", "status": "pending"})
		case "/clerk/v1/cases/case-attested/artifacts":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-attested", "artifacts": []map[string]any{}})
		default:
			t.Fatalf("path = %s", r.URL.Path)
		}
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/case-attested", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	if !strings.Contains(body, `href="/system/arb/clerk/cases/case-attested/attestation/events"`) {
		t.Fatalf("body missing attestation events link: %s", body)
	}
}

func TestCaseDetailSummarizesFailureEvents(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/clerk/v1/cases/case-failure":
			writeTestJSON(w, map[string]any{"ok": true, "case": map[string]any{"case_id": "case-failure", "status": "completed"}})
		case "/clerk/v1/cases/case-failure/result":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-failure", "status": "done"})
		case "/clerk/v1/cases/case-failure/artifacts":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-failure", "artifacts": []map[string]any{{"name": "events.ndjson", "size_bytes": 512}}})
		case "/clerk/v1/cases/case-failure/artifacts/events.ndjson":
			w.Header().Set("Content-Type", "application/x-ndjson")
			_, _ = w.Write([]byte(`{"timestamp":"2026-07-10T15:27:32Z","phase":"deliberation","type":"opportunity_failed","payload":{"member_id":"C2","process_name":"pi-C2","reason":"agent_exited","message":"Council member C2 failed: provider rejected function.arguments","agent_error_log":"/tmp/run/logs/pi-C2.stdout"}}` + "\n"))
			_, _ = w.Write([]byte(`{"timestamp":"2026-07-10T15:27:32Z","phase":"deliberation","type":"council_member_removed","payload":{"member_id":"C2","cause":"Council member C2 failed: provider rejected function.arguments","failure_reason":"agent_exited"}}` + "\n"))
		default:
			t.Fatalf("path = %s", r.URL.Path)
		}
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/case-failure", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	for _, want := range []string{
		"Failure Events",
		"opportunity_failed",
		"pi-C2",
		"provider rejected function.arguments",
		"/tmp/run/logs/pi-C2.stdout",
	} {
		if !strings.Contains(body, want) {
			t.Fatalf("body missing %q: %s", want, body)
		}
	}
	if count := strings.Count(body, "<td>pi-C2</td>"); count != 1 {
		t.Fatalf("failure process row count = %d body=%s", count, body)
	}
	if strings.Contains(body, `action="/system/arb/clerk/cases/case-failure/manage"`) {
		t.Fatalf("completed case includes manage action: %s", body)
	}
}

func TestCaseDetailSummarizesADCActionEvents(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/clerk/v1/cases/adc-events":
			writeTestJSON(w, map[string]any{"ok": true, "case": map[string]any{"case_id": "adc-events", "status": "running"}})
		case "/clerk/v1/cases/adc-events/result":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "adc-events", "status": "pending"})
		case "/clerk/v1/cases/adc-events/artifacts":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "adc-events", "artifacts": []map[string]any{{"name": "events.ndjson", "size_bytes": 512}}})
		case "/clerk/v1/cases/adc-events/artifacts/events.ndjson":
			w.Header().Set("Content-Type", "application/x-ndjson")
			_, _ = w.Write([]byte(`{"action":"list_case_files","payload":{},"response":{"files":[{"file_id":"file-0001"},{"file_id":"file-0002"}],"ok":true},"role":"defendant","step":1,"timestamp":"2026-07-10 15:30:51.833","turn":2}` + "\n"))
			_, _ = w.Write([]byte(`{"action":"read_case_text_file","payload":{"file_id":"file-0001"},"response":{"ok":true},"role":"defendant","step":2,"timestamp":"2026-07-10 15:30:54.539","turn":2}` + "\n"))
			_, _ = w.Write([]byte(`{"action":"pass_turn","payload":{"kind":"pass","reason":"No supported Rule 12 ground fits."},"response":{"ok":true,"result_kind":"pass_recorded","state":{"case":{"phase":"pretrial"}}},"role":"defendant","step":3,"timestamp":"2026-07-10 15:31:30.121","turn":2}` + "\n"))
			_, _ = w.Write([]byte(`{"action":"get_juror_context","payload":{"juror_id":"J9"},"response":{"ok":true},"role":"defendant","step":1,"timestamp":"2026-07-10 15:32:00.000","turn":3}` + "\n"))
			_, _ = w.Write([]byte(`{"action":"decide_voir_dire_question","payload":{"allowed":true,"exchange_id":"vdq-18","juror_id":"J9"},"response":{"ok":true,"state":{"case":{"phase":"voir_dire"}}},"role":"judge","step":1,"timestamp":"2026-07-10 15:33:00.000","turn":4}` + "\n"))
			_, _ = w.Write([]byte(`{"action":"submit_juror_vote","payload":{"confidence":"high","damages":108000,"juror_id":"J3","vote":"plaintiff"},"response":{"ok":true,"state":{"case":{"phase":"deliberation"}}},"role":"juror","step":1,"timestamp":"2026-07-10 15:34:00.000","turn":5}` + "\n"))
		default:
			t.Fatalf("path = %s", r.URL.Path)
		}
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/adc-events", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	for _, want := range []string{
		"Recent Events",
		"pass_turn",
		"No supported Rule 12 ground fits.",
		"read_case_text_file",
		"file_id=file-0001",
		"list_case_files",
		"files=2",
		"defendant",
		"pretrial",
		"get_juror_context",
		"juror_id=J9",
		"decide_voir_dire_question",
		"exchange_id=vdq-18",
		"voir_dire",
		"submit_juror_vote",
		"juror_id=J3 vote=plaintiff damages=108000 confidence=high",
	} {
		if !strings.Contains(body, want) {
			t.Fatalf("body missing %q: %s", want, body)
		}
	}
}

func TestEvidencePageRendersNonJSONEvidence(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/clerk/v1/cases/case-4/artifacts/evidence-manifest.json":
			writeTestJSON(w, map[string]any{"ok": true, "evidence": []map[string]any{{
				"evidence_id":          "E1",
				"title":                "First exhibit",
				"mime_type":            "text/plain",
				"size_bytes":           15,
				"admissibility_status": "case_packet",
				"record_visibility":    "juror_visible",
				"uses":                 []string{"complaint_attachment", "exhibit:PX-1", "admitted_exhibit:PX-1"},
			}}})
			return
		case "/clerk/v1/cases/case-4/evidence/E1":
		default:
			t.Fatalf("path = %s", r.URL.Path)
		}
		w.Header().Set("Content-Type", "text/plain; charset=utf-8")
		_, _ = w.Write([]byte("evidence bytes\n"))
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/case-4/evidence?id=E1", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	if !strings.Contains(rec.Body.String(), "evidence bytes") {
		t.Fatalf("body = %s", rec.Body.String())
	}
}

func TestEvidencePageListsManifestEntries(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/clerk/v1/cases/case-5/artifacts/evidence-manifest.json" {
			t.Fatalf("path = %s", r.URL.Path)
		}
		writeTestJSON(w, map[string]any{"ok": true, "evidence": []map[string]any{{
			"evidence_id":          "ev_123",
			"title":                "Deadline thread",
			"mime_type":            "text/plain",
			"size_bytes":           820,
			"admissibility_status": "case_packet",
			"record_visibility":    "juror_visible",
			"uses":                 []string{"complaint_attachment", "exhibit:PX-2"},
		}}})
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/case-5/evidence", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	for _, want := range []string{
		"Evidence Manifest",
		`href="/system/arb/clerk/cases/case-5/evidence?id=ev_123"`,
		"Deadline thread",
		"case_packet",
		"complaint_attachment, exhibit:PX-2",
	} {
		if !strings.Contains(body, want) {
			t.Fatalf("body missing %q: %s", want, body)
		}
	}
}

func TestResponseTextOmitsLargeResponses(t *testing.T) {
	got := responseText(&Response{JSON: map[string]any{"text": strings.Repeat("x", 13000)}})
	if !strings.Contains(got, "response body not rendered") {
		t.Fatalf("response text = %s", got)
	}
	if strings.Contains(got, strings.Repeat("x", 1000)) {
		t.Fatalf("large response was embedded: %s", got)
	}
}

func TestCaseDetailOmitsLargeEmbeddedResult(t *testing.T) {
	api := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/clerk/v1/cases/case-large":
			writeTestJSON(w, map[string]any{"ok": true, "case": map[string]any{"case_id": "case-large", "status": "completed"}})
		case "/clerk/v1/cases/case-large/result":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-large", "status": "done", "text": strings.Repeat("x", 13000)})
		case "/clerk/v1/cases/case-large/artifacts":
			writeTestJSON(w, map[string]any{"ok": true, "case_id": "case-large", "artifacts": []map[string]any{}})
		default:
			t.Fatalf("path = %s", r.URL.Path)
		}
	}))
	defer api.Close()
	app := testApp(t, api.URL, "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/system/arb/clerk/cases/case-large", nil)
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	body := rec.Body.String()
	if !strings.Contains(body, "JSON not rendered") {
		t.Fatalf("body does not report omitted result: %s", body)
	}
	if strings.Contains(body, strings.Repeat("x", 1000)) {
		t.Fatalf("large result was embedded: %s", body)
	}
}

func TestRawRequestRejectsAbsoluteURL(t *testing.T) {
	app := testApp(t, "http://127.0.0.1:1", "")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodPost, "/system/arb/request", strings.NewReader("method=GET&path=https%3A%2F%2Fexample.com%2F"))
	req.Header.Set("Content-Type", "application/x-www-form-urlencoded")
	app.ServeHTTP(rec, req)
	if rec.Code != http.StatusBadGateway {
		t.Fatalf("status = %d body=%s", rec.Code, rec.Body.String())
	}
	if !strings.Contains(rec.Body.String(), "service path must start with /") {
		t.Fatalf("body = %s", rec.Body.String())
	}
}

func testApp(t *testing.T, arbURL string, token string) *App {
	t.Helper()
	cfg := DefaultConfig()
	for id, sys := range cfg.Systems {
		sys.BaseURL = ""
		if id == "arb" {
			sys.BaseURL = arbURL
			sys.BearerToken = token
		}
		cfg.Systems[id] = sys
	}
	app, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}
	return app
}

func writeTestJSON(w http.ResponseWriter, value any) {
	w.Header().Set("Content-Type", "application/json")
	raw, _ := json.Marshal(value)
	_, _ = w.Write(raw)
}
