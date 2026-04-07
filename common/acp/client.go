package acp

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"net/url"
	"os/exec"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

type Config struct {
	Command  string
	Args     []string
	Cwd      string
	Env      []string
	Endpoint string
}

type Client struct {
	cmd        *exec.Cmd
	conn       net.Conn
	writer     io.WriteCloser
	stderrBuf  bytes.Buffer
	nextID     atomic.Int64
	mu         sync.Mutex
	pending    map[int64]chan rpcResponse
	handlers   map[int]func(Notification)
	methods    map[string]func(context.Context, map[string]any) (map[string]any, error)
	nextHandle int
	closed     bool
	done       chan struct{}
	readErr    error
}

type InitializeResponse struct {
	ProtocolVersion int `json:"protocolVersion"`
	AgentInfo       struct {
		Name    string `json:"name"`
		Title   string `json:"title"`
		Version string `json:"version"`
	} `json:"agentInfo"`
}

type NewSessionResponse struct {
	SessionID string `json:"sessionId"`
}

type PromptResponse struct {
	StopReason string `json:"stopReason"`
}

type TextBlock struct {
	Type string `json:"type"`
	Text string `json:"text"`
}

type PromptRequest struct {
	SessionID string      `json:"sessionId"`
	Prompt    []TextBlock `json:"prompt"`
}

type Notification struct {
	Method string
	Params map[string]any
}

type rpcRequest struct {
	JSONRPC string `json:"jsonrpc"`
	ID      int64  `json:"id"`
	Method  string `json:"method"`
	Params  any    `json:"params,omitempty"`
}

type rpcResponse struct {
	JSONRPC string          `json:"jsonrpc"`
	ID      int64           `json:"id"`
	Result  json.RawMessage `json:"result,omitempty"`
	Error   *rpcError       `json:"error,omitempty"`
}

type rpcError struct {
	Code    int    `json:"code"`
	Message string `json:"message"`
}

func NewClient(cfg Config) (*Client, error) {
	command := strings.TrimSpace(cfg.Command)
	endpoint := strings.TrimSpace(cfg.Endpoint)
	switch {
	case command != "" && endpoint != "":
		return nil, fmt.Errorf("acp command and endpoint are mutually exclusive")
	case command == "" && endpoint == "":
		return nil, fmt.Errorf("acp command or endpoint is required")
	}
	if endpoint != "" {
		return newEndpointClient(endpoint)
	}
	cmd := exec.Command(command, cfg.Args...)
	if strings.TrimSpace(cfg.Cwd) != "" {
		cmd.Dir = cfg.Cwd
	}
	if len(cfg.Env) > 0 {
		cmd.Env = append(cmd.Environ(), cfg.Env...)
	}
	stdin, err := cmd.StdinPipe()
	if err != nil {
		return nil, fmt.Errorf("acp stdin pipe: %w", err)
	}
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return nil, fmt.Errorf("acp stdout pipe: %w", err)
	}
	stderr, err := cmd.StderrPipe()
	if err != nil {
		return nil, fmt.Errorf("acp stderr pipe: %w", err)
	}
	if err := cmd.Start(); err != nil {
		return nil, fmt.Errorf("start acp command: %w", err)
	}
	c := &Client{
		cmd:      cmd,
		writer:   stdin,
		pending:  map[int64]chan rpcResponse{},
		handlers: map[int]func(Notification){},
		methods:  map[string]func(context.Context, map[string]any) (map[string]any, error){},
		done:     make(chan struct{}),
	}
	go c.readStdout(stdout)
	go func() {
		_, _ = io.Copy(&c.stderrBuf, stderr)
	}()
	return c, nil
}

func newEndpointClient(endpoint string) (*Client, error) {
	network, address, err := parseEndpoint(endpoint)
	if err != nil {
		return nil, err
	}
	conn, err := net.DialTimeout(network, address, 5*time.Second)
	if err != nil {
		return nil, fmt.Errorf("connect acp endpoint %s: %w", endpoint, err)
	}
	c := &Client{
		conn:     conn,
		writer:   conn,
		pending:  map[int64]chan rpcResponse{},
		handlers: map[int]func(Notification){},
		methods:  map[string]func(context.Context, map[string]any) (map[string]any, error){},
		done:     make(chan struct{}),
	}
	go c.readStdout(conn)
	return c, nil
}

func parseEndpoint(endpoint string) (string, string, error) {
	u, err := url.Parse(strings.TrimSpace(endpoint))
	if err != nil {
		return "", "", fmt.Errorf("parse acp endpoint %q: %w", endpoint, err)
	}
	if u.Scheme != "tcp" {
		return "", "", fmt.Errorf("unsupported acp endpoint transport %q", u.Scheme)
	}
	if u.Host == "" {
		return "", "", fmt.Errorf("acp endpoint %q must include host:port", endpoint)
	}
	if u.Path != "" && u.Path != "/" {
		return "", "", fmt.Errorf("acp endpoint %q must not include a path", endpoint)
	}
	if u.RawQuery != "" || u.Fragment != "" || u.User != nil {
		return "", "", fmt.Errorf("acp endpoint %q must not include query, fragment, or user info", endpoint)
	}
	return "tcp", u.Host, nil
}

func (c *Client) Close() error {
	c.mu.Lock()
	if c.closed {
		c.mu.Unlock()
		return nil
	}
	c.closed = true
	writer := c.writer
	conn := c.conn
	cmd := c.cmd
	c.mu.Unlock()
	if writer != nil {
		_ = writer.Close()
	}
	if conn != nil {
		_ = conn.Close()
	}
	if cmd != nil && cmd.Process != nil {
		_ = cmd.Process.Kill()
	}
	<-c.done
	if cmd == nil {
		return nil
	}
	err := cmd.Wait()
	if err == nil {
		return nil
	}
	var exitErr *exec.ExitError
	if errors.As(err, &exitErr) {
		return nil
	}
	return err
}

func (c *Client) Stderr() string {
	return strings.TrimSpace(c.stderrBuf.String())
}

func (c *Client) OnNotification(handler func(Notification)) func() {
	c.mu.Lock()
	defer c.mu.Unlock()
	id := c.nextHandle
	c.nextHandle++
	c.handlers[id] = handler
	return func() {
		c.mu.Lock()
		defer c.mu.Unlock()
		delete(c.handlers, id)
	}
}

func (c *Client) HandleMethod(method string, handler func(context.Context, map[string]any) (map[string]any, error)) {
	method = strings.TrimSpace(method)
	if method == "" {
		return
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	c.methods[method] = handler
}

func (c *Client) Initialize(ctx context.Context, protocolVersion int) (InitializeResponse, error) {
	var out InitializeResponse
	if protocolVersion <= 0 {
		protocolVersion = 1
	}
	resp, err := c.request(ctx, "initialize", map[string]any{"protocolVersion": protocolVersion})
	if err != nil {
		return out, err
	}
	if err := decodeResult(resp, &out); err != nil {
		return out, err
	}
	return out, nil
}

func (c *Client) NewSession(ctx context.Context, cwd string) (NewSessionResponse, error) {
	var out NewSessionResponse
	resp, err := c.request(ctx, "session/new", map[string]any{
		"cwd":        cwd,
		"mcpServers": []any{},
	})
	if err != nil {
		return out, err
	}
	if err := decodeResult(resp, &out); err != nil {
		return out, err
	}
	return out, nil
}

func (c *Client) Prompt(ctx context.Context, req PromptRequest) (PromptResponse, error) {
	var out PromptResponse
	resp, err := c.request(ctx, "session/prompt", req)
	if err != nil {
		return out, err
	}
	if err := decodeResult(resp, &out); err != nil {
		return out, err
	}
	return out, nil
}

func (c *Client) request(ctx context.Context, method string, params any) (rpcResponse, error) {
	id := c.nextID.Add(1)
	ch := make(chan rpcResponse, 1)
	c.mu.Lock()
	if c.closed {
		c.mu.Unlock()
		return rpcResponse{}, fmt.Errorf("acp client is closed")
	}
	c.pending[id] = ch
	c.mu.Unlock()
	wire, err := json.Marshal(rpcRequest{
		JSONRPC: "2.0",
		ID:      id,
		Method:  method,
		Params:  params,
	})
	if err != nil {
		c.removePending(id)
		return rpcResponse{}, fmt.Errorf("marshal acp request: %w", err)
	}
	if _, err := c.writer.Write(append(wire, '\n')); err != nil {
		c.removePending(id)
		return rpcResponse{}, fmt.Errorf("write acp request: %w", err)
	}
	select {
	case <-ctx.Done():
		c.removePending(id)
		return rpcResponse{}, ctx.Err()
	case resp := <-ch:
		if resp.Error != nil {
			return rpcResponse{}, fmt.Errorf("acp %s failed: %s", method, resp.Error.Message)
		}
		return resp, nil
	case <-c.done:
		return rpcResponse{}, c.transportClosedError()
	}
}

func (c *Client) removePending(id int64) {
	c.mu.Lock()
	defer c.mu.Unlock()
	delete(c.pending, id)
}

func decodeResult[T any](resp rpcResponse, out *T) error {
	if len(resp.Result) == 0 {
		return fmt.Errorf("acp response missing result")
	}
	if err := json.Unmarshal(resp.Result, out); err != nil {
		return fmt.Errorf("decode acp result: %w", err)
	}
	return nil
}

func (c *Client) readStdout(r io.Reader) {
	defer close(c.done)
	reader := bufio.NewReader(r)
	for {
		line, err := reader.ReadBytes('\n')
		if len(line) > 0 {
			c.handleLine(bytes.TrimSpace(line))
		}
		if err != nil {
			if err != io.EOF {
				c.readErr = err
			}
			c.failPending(err)
			return
		}
	}
}

func (c *Client) handleLine(line []byte) {
	if len(line) == 0 {
		return
	}
	var envelope map[string]json.RawMessage
	if err := json.Unmarshal(line, &envelope); err != nil {
		c.readErr = fmt.Errorf("decode acp line: %w", err)
		return
	}
	if methodRaw, ok := envelope["method"]; ok {
		var method string
		if err := json.Unmarshal(methodRaw, &method); err != nil {
			c.readErr = fmt.Errorf("decode acp method: %w", err)
			return
		}
		params := map[string]any{}
		if paramsRaw, ok := envelope["params"]; ok && len(paramsRaw) > 0 {
			if err := json.Unmarshal(paramsRaw, &params); err != nil {
				c.readErr = fmt.Errorf("decode acp params: %w", err)
				return
			}
		}
		if idRaw, ok := envelope["id"]; ok && len(idRaw) > 0 {
			var id int64
			if err := json.Unmarshal(idRaw, &id); err != nil {
				c.readErr = fmt.Errorf("decode acp request id: %w", err)
				return
			}
			go c.handleRequest(id, method, params)
			return
		}
		c.dispatch(Notification{Method: method, Params: params})
		return
	}
	var resp rpcResponse
	if err := json.Unmarshal(line, &resp); err != nil {
		c.readErr = fmt.Errorf("decode acp response: %w", err)
		return
	}
	c.mu.Lock()
	ch := c.pending[resp.ID]
	if ch != nil {
		delete(c.pending, resp.ID)
	}
	c.mu.Unlock()
	if ch != nil {
		ch <- resp
	}
}

func (c *Client) handleRequest(id int64, method string, params map[string]any) {
	c.mu.Lock()
	handler := c.methods[method]
	c.mu.Unlock()
	if handler == nil {
		_ = c.writeJSON(map[string]any{
			"jsonrpc": "2.0",
			"id":      id,
			"error": map[string]any{
				"code":    -32601,
				"message": fmt.Sprintf("method not handled: %s", method),
			},
		})
		return
	}
	result, err := handler(context.Background(), params)
	if err != nil {
		_ = c.writeJSON(map[string]any{
			"jsonrpc": "2.0",
			"id":      id,
			"error": map[string]any{
				"code":    -32000,
				"message": err.Error(),
			},
		})
		return
	}
	_ = c.writeJSON(map[string]any{
		"jsonrpc": "2.0",
		"id":      id,
		"result":  result,
	})
}

func (c *Client) dispatch(note Notification) {
	c.mu.Lock()
	handlers := make([]func(Notification), 0, len(c.handlers))
	for _, h := range c.handlers {
		handlers = append(handlers, h)
	}
	c.mu.Unlock()
	for _, h := range handlers {
		h(note)
	}
}

func (c *Client) failPending(err error) {
	c.mu.Lock()
	defer c.mu.Unlock()
	for id, ch := range c.pending {
		delete(c.pending, id)
		msg := "acp transport closed"
		if err != nil && err != io.EOF {
			msg = err.Error()
		}
		ch <- rpcResponse{Error: &rpcError{Message: msg}}
	}
}

func (c *Client) transportClosedError() error {
	if c.readErr != nil && c.readErr != io.EOF {
		return fmt.Errorf("acp transport closed: %w", c.readErr)
	}
	if stderr := c.Stderr(); stderr != "" {
		return fmt.Errorf("acp transport closed: %s", stderr)
	}
	return fmt.Errorf("acp transport closed")
}

func (c *Client) writeJSON(v any) error {
	wire, err := json.Marshal(v)
	if err != nil {
		return err
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	if c.closed {
		return fmt.Errorf("acp client is closed")
	}
	_, err = c.writer.Write(append(wire, '\n'))
	return err
}
