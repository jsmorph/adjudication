package runner

import (
	"context"
	"crypto/rand"
	"encoding/json"
	"fmt"
	"math/big"
	"net/http"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"time"

	openaiapi "adjudication/common/openai"
	"adjudication/common/persona"
	xproxy "adjudication/common/xproxy"
)

func maybeStartXProxy(configPath string, port int) (*xproxy.XProxyServer, error) {
	if port <= 0 {
		port = xproxy.DefaultPort
	}
	if xproxyHealthy(port) {
		return nil, nil
	}
	server, err := xproxy.StartXProxyServer(xproxy.XProxyOptions{
		ConfigPath: configPath,
		Port:       port,
	})
	if err != nil {
		return nil, err
	}
	deadline := time.Now().Add(5 * time.Second)
	for time.Now().Before(deadline) {
		if xproxyHealthy(port) {
			return server, nil
		}
		time.Sleep(50 * time.Millisecond)
	}
	_ = server.Close()
	return nil, fmt.Errorf("xproxy did not become healthy on 127.0.0.1:%d", port)
}

func xproxyHealthy(port int) bool {
	client := http.Client{Timeout: 500 * time.Millisecond}
	resp, err := client.Get(fmt.Sprintf("http://127.0.0.1:%d/healthz", port))
	if err != nil {
		return false
	}
	defer resp.Body.Close()
	return resp.StatusCode == http.StatusOK
}

func newXProxyClient(port int, timeout time.Duration) (*openaiapi.Client, error) {
	if port <= 0 {
		port = xproxy.DefaultPort
	}
	return openaiapi.New("xproxy", fmt.Sprintf("http://127.0.0.1:%d/v1", port), false, timeout)
}

func loadCaseFiles(dir string) ([]CaseFile, error) {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil, fmt.Errorf("read case dir: %w", err)
	}
	out := make([]CaseFile, 0, len(entries))
	for _, entry := range entries {
		if entry.IsDir() {
			continue
		}
		name := entry.Name()
		if skipCaseFile(name) {
			continue
		}
		file, err := loadCaseFile(filepath.Join(dir, name), name)
		if err != nil {
			return nil, err
		}
		out = append(out, file)
	}
	slices.SortFunc(out, func(a, b CaseFile) int {
		return strings.Compare(a.FileID, b.FileID)
	})
	return out, nil
}

func loadCaseFilesFromPaths(paths []string) ([]CaseFile, error) {
	if len(paths) == 0 {
		return nil, fmt.Errorf("no case files specified")
	}
	out := make([]CaseFile, 0, len(paths))
	seen := map[string]string{}
	for _, rawPath := range paths {
		path := strings.TrimSpace(rawPath)
		if path == "" {
			return nil, fmt.Errorf("case file path must not be empty")
		}
		name := filepath.Base(path)
		if prior, ok := seen[name]; ok {
			return nil, fmt.Errorf("duplicate case file name %q from %s and %s", name, prior, path)
		}
		file, err := loadCaseFile(path, name)
		if err != nil {
			return nil, err
		}
		seen[name] = path
		out = append(out, file)
	}
	slices.SortFunc(out, func(a, b CaseFile) int {
		return strings.Compare(a.FileID, b.FileID)
	})
	return out, nil
}

func loadCaseFile(path string, name string) (CaseFile, error) {
	mimeType, readable := caseFileKind(name)
	info, err := os.Stat(path)
	if err != nil {
		return CaseFile{}, fmt.Errorf("stat case file %s: %w", name, err)
	}
	if info.IsDir() {
		return CaseFile{}, fmt.Errorf("case file %s is a directory", name)
	}
	file := CaseFile{
		FileID:       name,
		Name:         name,
		Path:         path,
		MimeType:     mimeType,
		TextReadable: readable,
		SizeBytes:    int(info.Size()),
	}
	if readable {
		raw, err := os.ReadFile(path)
		if err != nil {
			return CaseFile{}, fmt.Errorf("read case file %s: %w", name, err)
		}
		file.Text = string(raw)
	}
	return file, nil
}

func caseFileKind(name string) (string, bool) {
	switch strings.ToLower(filepath.Ext(name)) {
	case ".txt":
		return "text/plain", true
	case ".md":
		return "text/markdown", true
	case ".pem":
		return "application/x-pem-file", true
	case ".b64":
		return "text/plain", true
	default:
		return "application/octet-stream", false
	}
}

func skipCaseFile(name string) bool {
	switch name {
	case ".gitignore", "README.md", "complaint.md", "situation.md", "sign.sh", "confession.sig", "samantha_private.pem":
		return true
	default:
		return false
	}
}

func councilPoolMeta(path string, baseDir string) ([]persona.Spec, error) {
	specs, err := persona.LoadRecordsFile(path, baseDir)
	if err != nil {
		return nil, err
	}
	return specs, nil
}

func sampleCouncil(path string, baseDir string, count int) ([]CouncilSeat, error) {
	specs, err := councilPoolMeta(path, baseDir)
	if err != nil {
		return nil, err
	}
	if count <= 0 {
		return nil, fmt.Errorf("council size must be positive")
	}
	if count > len(specs) {
		return nil, fmt.Errorf("council size %d exceeds available pool %d", count, len(specs))
	}
	indexes := make([]int, len(specs))
	for i := range specs {
		indexes[i] = i
	}
	out := make([]CouncilSeat, 0, count)
	for i := 0; i < count; i++ {
		n, err := rand.Int(rand.Reader, big.NewInt(int64(len(indexes))))
		if err != nil {
			return nil, fmt.Errorf("sample council pool: %w", err)
		}
		pick := int(n.Int64())
		spec := specs[indexes[pick]]
		indexes = append(indexes[:pick], indexes[pick+1:]...)
		out = append(out, CouncilSeat{
			MemberID:    fmt.Sprintf("C%d", i+1),
			Model:       spec.Model,
			PersonaFile: spec.File,
			PersonaText: spec.Text,
		})
	}
	return out, nil
}

func councilSeatMaps(council []CouncilSeat) []map[string]any {
	out := make([]map[string]any, 0, len(council))
	for _, seat := range council {
		out = append(out, map[string]any{
			"member_id":        seat.MemberID,
			"model":            seat.Model,
			"persona_filename": seat.PersonaFile,
			"status":           "seated",
		})
	}
	return out
}

func caseFileMetas(files []CaseFile) []CaseFileMeta {
	out := make([]CaseFileMeta, 0, len(files))
	for _, file := range files {
		out = append(out, CaseFileMeta{
			FileID:       file.FileID,
			Name:         file.Name,
			MimeType:     file.MimeType,
			TextReadable: file.TextReadable,
		})
	}
	return out
}

func appendJSONLine(path string, value any) error {
	wire, err := json.Marshal(value)
	if err != nil {
		return fmt.Errorf("marshal event: %w", err)
	}
	f, err := os.OpenFile(path, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0o644)
	if err != nil {
		return fmt.Errorf("open %s: %w", path, err)
	}
	defer f.Close()
	if _, err := f.Write(append(wire, '\n')); err != nil {
		return fmt.Errorf("write %s: %w", path, err)
	}
	return nil
}

func writeJSONFile(path string, value any) error {
	wire, err := json.MarshalIndent(value, "", "  ")
	if err != nil {
		return fmt.Errorf("marshal %s: %w", path, err)
	}
	wire = append(wire, '\n')
	if err := os.WriteFile(path, wire, 0o644); err != nil {
		return fmt.Errorf("write %s: %w", path, err)
	}
	return nil
}

func mapString(value any) string {
	if value == nil {
		return ""
	}
	return strings.TrimSpace(fmt.Sprintf("%v", value))
}

func mapAny(value any) map[string]any {
	out, _ := value.(map[string]any)
	if out == nil {
		return map[string]any{}
	}
	return out
}

func mapList(value any) []map[string]any {
	switch v := value.(type) {
	case []map[string]any:
		return v
	case []any:
		out := make([]map[string]any, 0, len(v))
		for _, raw := range v {
			entry, _ := raw.(map[string]any)
			if entry != nil {
				out = append(out, entry)
			}
		}
		return out
	default:
		return nil
	}
}

func cloneMap(in map[string]any) map[string]any {
	out := make(map[string]any, len(in))
	for key, value := range in {
		out[key] = value
	}
	return out
}

func withTimeout(ctx context.Context, timeout time.Duration) (context.Context, context.CancelFunc) {
	if timeout <= 0 {
		return context.WithCancel(ctx)
	}
	return context.WithTimeout(ctx, timeout)
}
