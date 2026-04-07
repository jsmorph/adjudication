package acp

import (
	"bufio"
	"context"
	"encoding/json"
	"fmt"
	"net"
	"testing"
)

func TestCloseSuppressesIntentionalKill(t *testing.T) {
	t.Parallel()

	client, err := NewClient(Config{
		Command: "sleep",
		Args:    []string{"60"},
	})
	if err != nil {
		t.Fatalf("NewClient returned error: %v", err)
	}
	if err := client.Close(); err != nil {
		t.Fatalf("Close returned error: %v", err)
	}
}

func TestTCPEndpointRoundTrip(t *testing.T) {
	t.Parallel()

	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("Listen returned error: %v", err)
	}
	defer listener.Close()

	serverDone := make(chan error, 1)
	go func() {
		conn, err := listener.Accept()
		if err != nil {
			serverDone <- err
			return
		}
		defer conn.Close()

		reader := bufio.NewReader(conn)
		for i := 0; i < 2; i++ {
			line, err := reader.ReadBytes('\n')
			if err != nil {
				serverDone <- err
				return
			}
			var req map[string]any
			if err := json.Unmarshal(line, &req); err != nil {
				serverDone <- err
				return
			}
			id, _ := req["id"].(float64)
			method, _ := req["method"].(string)
			var result any
			switch method {
			case "initialize":
				result = map[string]any{
					"protocolVersion": 1,
					"agentInfo": map[string]any{
						"name":    "test-agent",
						"title":   "Test Agent",
						"version": "1",
					},
				}
			case "session/new":
				result = map[string]any{"sessionId": "session-1"}
			default:
				serverDone <- fmt.Errorf("unexpected method %q", method)
				return
			}
			resp, err := json.Marshal(map[string]any{
				"jsonrpc": "2.0",
				"id":      int64(id),
				"result":  result,
			})
			if err != nil {
				serverDone <- err
				return
			}
			if _, err := conn.Write(append(resp, '\n')); err != nil {
				serverDone <- err
				return
			}
		}
		serverDone <- nil
	}()

	client, err := NewClient(Config{Endpoint: "tcp://" + listener.Addr().String()})
	if err != nil {
		t.Fatalf("NewClient returned error: %v", err)
	}
	defer client.Close()

	initResp, err := client.Initialize(context.Background(), 1)
	if err != nil {
		t.Fatalf("Initialize returned error: %v", err)
	}
	if initResp.ProtocolVersion != 1 {
		t.Fatalf("Initialize protocol version = %d, want 1", initResp.ProtocolVersion)
	}

	sessionResp, err := client.NewSession(context.Background(), "/tmp")
	if err != nil {
		t.Fatalf("NewSession returned error: %v", err)
	}
	if sessionResp.SessionID != "session-1" {
		t.Fatalf("NewSession session id = %q, want session-1", sessionResp.SessionID)
	}

	if err := <-serverDone; err != nil {
		t.Fatalf("test server returned error: %v", err)
	}
}
