#!/usr/bin/env bash
set -euo pipefail

backend_addr="${BACKEND_ADDR:-127.0.0.1:17001}"
proxy_addr="${PROXY_ADDR:-127.0.0.1:17000}"
out_dir="${OUT_DIR:-out/ex6-proxy-demo}"
pi_home="$(mktemp -d)"
backend_pid=""
proxy_pid=""

cleanup() {
  set +e
  if [ -n "$proxy_pid" ]; then
    kill "$proxy_pid" 2>/dev/null || true
    wait "$proxy_pid" 2>/dev/null || true
  fi
  if [ -n "$backend_pid" ]; then
    kill "$backend_pid" 2>/dev/null || true
    wait "$backend_pid" 2>/dev/null || true
  fi
  rm -rf "$pi_home"
}

wait_for_port() {
  local host="${1%:*}"
  local port="${1##*:}"
  for _ in $(seq 1 50); do
    if (echo >/dev/tcp/"$host"/"$port") >/dev/null 2>&1; then
      return 0
    fi
    sleep 0.1
  done
  printf 'port did not open: %s\n' "$1" >&2
  exit 1
}

trap cleanup EXIT INT TERM

mkdir -p "$pi_home/.pi/agent" .bin

make build
go -C ../../acptools build -o "$(pwd)/.bin/acpproxy" ./cmd/acpproxy

.bin/aar stage-attorney-pi-home \
  --dir "$pi_home" \
  --model 'openai://gpt-5?tools=search'

PI_ACP_CLIENT_TOOLS="$(
  .bin/aar attorney-tools --include-workspace-writer
)"

rm -rf "$out_dir"

.bin/acpproxy serve-stdio \
  --listen "$backend_addr" \
  --command ../common/pi-container/acp-podman.sh \
  --env "PI_CONTAINER_HOME_DIR=$pi_home" \
  --env "PI_ACP_CLIENT_TOOLS=$PI_ACP_CLIENT_TOOLS" &
backend_pid=$!

.bin/acpproxy forward \
  --listen "$proxy_addr" \
  --upstream "tcp://$backend_addr" &
proxy_pid=$!

wait_for_port "$backend_addr"
wait_for_port "$proxy_addr"

.bin/aar case \
  --complaint examples/ex6/complaint.md \
  --out-dir "$out_dir" \
  --attorney-model 'openai://gpt-5?tools=search' \
  --plaintiff-acp-endpoint "tcp://$proxy_addr"
