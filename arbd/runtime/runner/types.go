package runner

import (
	"adjudication/arbd/runtime/lean"
	"adjudication/arbd/runtime/spec"
)

type Policy struct {
	CouncilSize           int    `json:"council_size"`
	JudgmentStandard      string `json:"judgment_standard"`
	MaxOpeningChars       int    `json:"max_opening_chars"`
	MaxArgumentChars      int    `json:"max_argument_chars"`
	MaxRebuttalChars      int    `json:"max_rebuttal_chars"`
	MaxSurrebuttalChars   int    `json:"max_surrebuttal_chars"`
	MaxClosingChars       int    `json:"max_closing_chars"`
	MaxExhibitsPerFiling  int    `json:"max_exhibits_per_filing"`
	MaxExhibitsPerSide    int    `json:"max_exhibits_per_side"`
	MaxExhibitBytes       int    `json:"max_exhibit_bytes"`
	MaxReportsPerFiling   int    `json:"max_reports_per_filing"`
	MaxReportsPerSide     int    `json:"max_reports_per_side"`
	MaxReportTitleBytes   int    `json:"max_report_title_bytes"`
	MaxReportSummaryBytes int    `json:"max_report_summary_bytes"`
}

type RuntimeLimits struct {
	CouncilLLMTimeoutSeconds  int   `json:"council_llm_timeout_seconds"`
	AttorneyACPTimeoutSeconds int   `json:"attorney_acp_timeout_seconds"`
	MaxResponseBytes          int   `json:"max_response_bytes"`
	InvalidAttemptLimit       int   `json:"invalid_attempt_limit"`
	CouncilMaxOutputTokens    int64 `json:"council_max_output_tokens"`
}

type AttorneyRoleConfig struct {
	Model       string
	ACPCommand  string
	ACPEndpoint string
	SessionCwd  string
}

type AttorneyRunInfo struct {
	Role          string `json:"role"`
	Model         string `json:"model"`
	SearchEnabled bool   `json:"search_enabled"`
	ACPTransport  string `json:"acp_transport"`
	ACPCommand    string `json:"acp_command,omitempty"`
	ACPEndpoint   string `json:"acp_endpoint,omitempty"`
	SessionCwd    string `json:"-"`
}

type Config struct {
	RunID                    string
	ComplaintPath            string
	CaseFilePaths            []string
	OutputDir                string
	CommonRoot               string
	CouncilPoolPath          string
	AttorneyModel            string
	AttorneyInstructionsPath string
	PlaintiffAttorney        AttorneyRoleConfig
	DefendantAttorney        AttorneyRoleConfig
	Policy                   Policy
	Runtime                  RuntimeLimits
	XProxyConfigPath         string
	XProxyPort               int
	ACPCommand               string
	ACPArgs                  []string
	ACPEnv                   []string
	Engine                   lean.Engine
}

type Result struct {
	RunID            string            `json:"run_id"`
	StartedAt        string            `json:"started_at"`
	FinishedAt       string            `json:"finished_at"`
	Status           string            `json:"status"`
	Phase            string            `json:"phase"`
	Complaint        spec.Complaint    `json:"complaint"`
	JudgmentStandard string            `json:"judgment_standard"`
	Answers          map[string]int    `json:"answers"`
	Attorneys        []AttorneyRunInfo `json:"attorneys"`
	CaseFiles        []CaseFileMeta    `json:"case_files"`
	Council          []CouncilSeat     `json:"council"`
	Events           []Event           `json:"events"`
	FinalState       map[string]any    `json:"final_state"`
	FinalReason      string            `json:"final_reason"`
}

type CaseFile struct {
	FileID       string
	Name         string
	Path         string
	MimeType     string
	TextReadable bool
	SizeBytes    int
	Text         string
}

type CaseFileMeta struct {
	FileID       string `json:"file_id"`
	Name         string `json:"name"`
	MimeType     string `json:"mime_type"`
	TextReadable bool   `json:"text_readable"`
}

type CouncilSeat struct {
	MemberID    string `json:"member_id"`
	Model       string `json:"model"`
	PersonaFile string `json:"persona_file"`
	PersonaText string `json:"-"`
}

type Opportunity struct {
	ID           string
	Role         string
	Phase        string
	MayPass      bool
	Objective    string
	AllowedTools []string
}

type Event struct {
	Timestamp string         `json:"timestamp"`
	Turn      int            `json:"turn"`
	Role      string         `json:"role"`
	Phase     string         `json:"phase"`
	Type      string         `json:"type"`
	Payload   map[string]any `json:"payload,omitempty"`
}

type runContext struct {
	cfg             Config
	complaint       spec.Complaint
	state           map[string]any
	caseFiles       []CaseFile
	fileByID        map[string]CaseFile
	council         []CouncilSeat
	attorneys       map[string]AttorneyRunInfo
	acpSessions     map[string]*acpPersistentSession
	workProductDirs map[string]string
	events          []Event
	turn            int
}
