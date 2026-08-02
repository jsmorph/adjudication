#!/bin/sh
set -eu

mode="${ARB_EXEC_MODE:-attest-only}"
work_root="${ARB_EXEC_WORK_ROOT:-/var/lib/arbattest-aard}"
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
output_prefix="${OUTPUT_PREFIX:?OUTPUT_PREFIX is required}"
input_prefix="${INPUT_PREFIX:-}"
aard_example=""
aard_input_mode="example"
aard_case_id="${AARD_CASE_ID:-}"
case_packet_key=""
case_packet_sha384=""
case_packet_bytes=""
case_manifest_key=""
case_manifest_sha384=""

case "$mode" in
    aard)
        aard_input_mode="${AARD_INPUT_MODE:-example}"
        case "$aard_input_mode" in
            example|case-packet) ;;
            *)
                echo "error: invalid AARD_INPUT_MODE: $aard_input_mode" >&2
                exit 1
                ;;
        esac
        case "$aard_input_mode" in
            example) aard_example="${AARD_EXAMPLE:-ex1}" ;;
            *) aard_example="${AARD_EXAMPLE:-}" ;;
        esac
        if [ -n "$aard_example" ]; then
            case "$aard_example" in
                .*|*/*|*..*)
                    echo "error: invalid AARD_EXAMPLE: $aard_example" >&2
                    exit 1
                    ;;
            esac
        fi
        if [ "$aard_input_mode" = "example" ] && [ -z "$aard_example" ]; then
            echo "error: AARD_EXAMPLE is required for example input mode" >&2
            exit 1
        fi
        if [ -n "$aard_case_id" ]; then
            case "$aard_case_id" in
                .*|*/*|*..*)
                    echo "error: invalid AARD_CASE_ID: $aard_case_id" >&2
                    exit 1
                    ;;
            esac
        fi
        ;;
esac

run_id="${RUN_ID:-}"
if [ -z "$run_id" ]; then
    case "$mode" in
        aard)
            case "$aard_input_mode" in
                example) run_id="aard-$aard_example-$stamp" ;;
                *) run_id="aard-case-$stamp" ;;
            esac
            ;;
        *) run_id="run-$stamp" ;;
    esac
fi

export TPM2TOOLS_TCTI="${TPM2TOOLS_TCTI:-device:/dev/tpmrm0}"
export TSS2_TCTI="${TSS2_TCTI:-device:/dev/tpmrm0}"
export TPM_DEVICE="${TPM_DEVICE:-/dev/tpm0}"

case "$output_prefix" in
    s3://*) ;;
    *) echo "error: OUTPUT_PREFIX must start with s3://" >&2; exit 1 ;;
esac

output_prefix="${output_prefix%/}"
run_dir="$work_root/$run_id"
mkdir -p "$run_dir"

log="$run_dir/run.log"
manifest="$run_dir/manifest.json"
manifest_hash_file="$run_dir/manifest.sha384"
attestation="$run_dir/attestation.b64"
aard_archive_key=""
aard_archive_sha384=""
aard_archive_bytes=""

imds_token=""
imds_token_error="$run_dir/imds-token.err"
if imds_token="$(curl -fsS -X PUT \
    -H 'X-aws-ec2-metadata-token-ttl-seconds: 21600' \
    http://169.254.169.254/latest/api/token 2>"$imds_token_error")"; then
    rm -f "$imds_token_error"
else
    imds_token=""
fi

imds_get() {
    path="$1"
    if [ -n "$imds_token" ]; then
        curl -fsS -H "X-aws-ec2-metadata-token: $imds_token" "http://169.254.169.254/$path"
    else
        curl -fsS "http://169.254.169.254/$path"
    fi
}

json_string() {
    printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g'
}

create_aard_archive() {
    src_dir="$1"
    archive="$2"
    rm -f "$archive"
    tar -czf "$archive" \
        --exclude='./pi-*' \
        --exclude='./openclaw-*-codex' \
        -C "$src_dir" \
        .
}

upload_aard_archive() {
    src_dir="$1"
    object_name="$2"
    archive="$run_dir/$object_name"
    create_aard_archive "$src_dir" "$archive"
    set -- $(sha384sum "$archive")
    aard_archive_sha384="$1"
    set -- $(wc -c < "$archive")
    aard_archive_bytes="$1"
    aard_archive_key="$output_prefix/$object_name"
    aws s3 cp "$archive" "$aard_archive_key" --no-progress
}

upload_events_if_changed() {
    events_path="$1"
    events_key="$2"
    stamp_file="$3"
    if [ ! -f "$events_path" ]; then
        return 0
    fi
    set -- $(stat -c '%s %Y' "$events_path")
    events_stamp="$1:$2"
    previous_stamp=""
    if [ -f "$stamp_file" ]; then
        previous_stamp="$(cat "$stamp_file")"
    fi
    if [ "$events_stamp" != "$previous_stamp" ]; then
        if ! aws s3 cp "$events_path" "$events_key" --no-progress; then
            return 1
        fi
        if ! printf '%s\n' "$events_stamp" > "$stamp_file"; then
            return 1
        fi
    fi
    return 0
}

reject_packet_path() {
    echo "error: invalid case packet path: $1" >&2
    exit 1
}

validate_packet_path() {
    value="$1"
    if [ -z "$value" ]; then
        reject_packet_path "$value"
    fi
    if [ "$(printf '%s' "$value" | tr -d '\n')" != "$value" ]; then
        reject_packet_path "$value"
    fi
    case "$value" in
        /*|.|..|./*|*/.|*/./*|*//*|../*|*/..|*/../*)
            reject_packet_path "$value"
            ;;
    esac
}

download_case_packet() {
    packet_name="${AARD_CASE_PACKET:-case.tar.gz}"
    manifest_name="${AARD_CASE_MANIFEST:-case-packet.json}"
    case "$packet_name" in
        ""|.*|*/*|*..*)
            echo "error: invalid AARD_CASE_PACKET: $packet_name" >&2
            exit 1
            ;;
    esac
    case "$manifest_name" in
        ""|.*|*/*|*..*)
            echo "error: invalid AARD_CASE_MANIFEST: $manifest_name" >&2
            exit 1
            ;;
    esac
    expected_packet_sha384="${AARD_CASE_PACKET_SHA384:-}"
    expected_manifest_sha384="${AARD_CASE_MANIFEST_SHA384:-}"
    if [ -z "$expected_packet_sha384" ]; then
        echo "error: AARD_CASE_PACKET_SHA384 is required for case-packet input mode" >&2
        exit 1
    fi
    if [ -z "$expected_manifest_sha384" ]; then
        echo "error: AARD_CASE_MANIFEST_SHA384 is required for case-packet input mode" >&2
        exit 1
    fi
    packet_path="$run_dir/$packet_name"
    manifest_path="$run_dir/$manifest_name"
    case_packet_key="$input_prefix/$packet_name"
    case_manifest_key="$input_prefix/$manifest_name"
    aws s3 cp "$case_packet_key" "$packet_path" --no-progress
    aws s3 cp "$case_manifest_key" "$manifest_path" --no-progress
    set -- $(sha384sum "$packet_path")
    case_packet_sha384="$1"
    set -- $(wc -c < "$packet_path")
    case_packet_bytes="$1"
    set -- $(sha384sum "$manifest_path")
    case_manifest_sha384="$1"
    if [ -n "$expected_packet_sha384" ] && [ "$case_packet_sha384" != "$expected_packet_sha384" ]; then
        echo "error: case packet hash mismatch" >&2
        exit 1
    fi
    if [ -n "$expected_manifest_sha384" ] && [ "$case_manifest_sha384" != "$expected_manifest_sha384" ]; then
        echo "error: case manifest hash mismatch" >&2
        exit 1
    fi
}

extract_case_packet() {
    packet_path="$1"
    dest_dir="$2"
    members="$run_dir/case-packet-members.txt"
    mkdir -p "$dest_dir"
    tar -tzf "$packet_path" > "$members"
    while IFS= read -r member; do
        validate_packet_path "$member"
    done < "$members"
    tar -xzf "$packet_path" -C "$dest_dir"
}

read_case_packet_args() {
    extract_dir="$1"
    args_file="$extract_dir/control/case-args.txt"
    case_packet_files_file="$run_dir/case-packet-files.txt"
    case_file_mode=""
    case_packet_complaint=""
    : > "$case_packet_files_file"
    if [ ! -f "$args_file" ]; then
        echo "error: case packet is missing control/case-args.txt" >&2
        exit 1
    fi
    while IFS= read -r line || [ -n "$line" ]; do
        case "$line" in
            case_file_mode=*)
                case_file_mode="${line#case_file_mode=}"
                ;;
            complaint=*)
                case_packet_complaint="${line#complaint=}"
                validate_packet_path "$case_packet_complaint"
                ;;
            file=*)
                file_path="${line#file=}"
                validate_packet_path "$file_path"
                printf '%s\n' "$extract_dir/$file_path" >> "$case_packet_files_file"
                ;;
            "")
                ;;
            *)
                echo "error: invalid case packet control line: $line" >&2
                exit 1
                ;;
        esac
    done < "$args_file"
    case "$case_file_mode" in
        auto|explicit) ;;
        *)
            echo "error: invalid case packet file mode: $case_file_mode" >&2
            exit 1
            ;;
    esac
    if [ -z "$case_packet_complaint" ]; then
        echo "error: case packet complaint path is missing" >&2
        exit 1
    fi
    if [ ! -f "$extract_dir/$case_packet_complaint" ]; then
        echo "error: case packet complaint file is missing" >&2
        exit 1
    fi
    case_packet_complaint="$extract_dir/$case_packet_complaint"
    case_packet_file_mode="$case_file_mode"
}

start_time="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
if ! instance_id="$(imds_get latest/meta-data/instance-id)"; then
    echo "error: failed to read EC2 instance ID from IMDS" >&2
    exit 1
fi
if ! ami_id="$(imds_get latest/meta-data/ami-id)"; then
    echo "error: failed to read EC2 AMI ID from IMDS" >&2
    exit 1
fi

case "$mode" in
    attest-only)
        {
            printf 'mode=%s\n' "$mode"
            printf 'run_id=%s\n' "$run_id"
            printf 'instance_id=%s\n' "$instance_id"
            printf 'ami_id=%s\n' "$ami_id"
        } > "$log"
        ;;
    aard)
        : "${INPUT_PREFIX:?INPUT_PREFIX is required for ARB_EXEC_MODE=aard}"
        secrets_dir="$run_dir/secrets"
        aard_out="$run_dir/aard"
        event_upload_interval="${AARD_EVENTS_UPLOAD_INTERVAL_SECONDS:-60}"
        case "$event_upload_interval" in
            ""|0|*[!0-9]*)
                echo "error: invalid AARD_EVENTS_UPLOAD_INTERVAL_SECONDS: $event_upload_interval" >&2
                exit 1
                ;;
        esac
        mkdir -p "$secrets_dir" "$aard_out"
        aws s3 cp "$input_prefix/auth.json" "$secrets_dir/auth.json" --no-progress
        aws s3 cp "$input_prefix/keys.sh" "$secrets_dir/keys.sh" --no-progress
        . "$secrets_dir/keys.sh"
        : "${OPENROUTER_API_KEY:?OPENROUTER_API_KEY is required}"
        export OPENROUTER_API_KEY
        set -- /usr/local/bin/aard-run-entrypoint \
            --out-dir "$aard_out" \
            --openclaw-auth codex \
            --openclaw-codex-auth "$secrets_dir/auth.json" \
            --openclaw-network host \
            --docker docker \
            --podman docker \
            --pi-image agentcourt-pi-sandbox:latest
        if [ -n "$aard_case_id" ]; then
            set -- "$@" --case-id "$aard_case_id"
        fi
        if [ -n "$run_id" ]; then
            set -- "$@" --run-id "$run_id"
        fi
        case "$aard_input_mode" in
            example)
                set -- "$@" "$aard_example"
                ;;
            case-packet)
                download_case_packet
                case_extract="$run_dir/case-packet"
                extract_case_packet "$packet_path" "$case_extract"
                read_case_packet_args "$case_extract"
                set -- "$@" --complaint "$case_packet_complaint"
                if [ "$case_packet_file_mode" = "explicit" ]; then
                    while IFS= read -r file_path; do
                        if [ ! -f "$file_path" ]; then
                            echo "error: explicit case file is missing: $file_path" >&2
                            exit 1
                        fi
                        set -- "$@" --file "$file_path"
                    done < "$case_packet_files_file"
                fi
                if [ -n "$aard_example" ]; then
                    set -- "$@" "$aard_example"
                fi
                ;;
            *)
                echo "error: unsupported AARD_INPUT_MODE: $aard_input_mode" >&2
                exit 1
                ;;
        esac
        events_path="$aard_out/events.ndjson"
        events_key="$output_prefix/events.ndjson"
        events_stamp_file="$run_dir/events.ndjson.stamp"
        events_error_file="$run_dir/events.ndjson.err"
        set +e
        "$@" > "$log" 2>&1 &
        aard_pid=$!
        set -e
        next_event_upload=0
        while kill -0 "$aard_pid" 2>/dev/null; do
            now_epoch="$(date -u +%s)"
            if [ "$now_epoch" -ge "$next_event_upload" ]; then
                if ! upload_events_if_changed "$events_path" "$events_key" "$events_stamp_file"; then
                    printf 'error: failed to upload %s\n' "$events_key" > "$events_error_file"
                    if kill -0 "$aard_pid" 2>/dev/null; then
                        if ! kill "$aard_pid" 2>/dev/null; then
                            printf 'error: failed to terminate aard after events upload failure\n' >> "$events_error_file"
                        fi
                    fi
                    break
                fi
                next_event_upload=$((now_epoch + event_upload_interval))
            fi
            sleep 5
        done
        set +e
        wait "$aard_pid"
        aard_status=$?
        set -e
        events_failed=0
        if [ -f "$events_error_file" ]; then
            events_failed=1
            cat "$events_error_file" >> "$log"
        fi
        if ! upload_events_if_changed "$events_path" "$events_key" "$events_stamp_file"; then
            events_failed=1
            echo "error: failed to upload final events.ndjson" >> "$events_error_file"
            echo "error: failed to upload final events.ndjson" >> "$log"
        fi
        if [ "$events_failed" -ne 0 ] && [ "$aard_status" -eq 0 ]; then
            aard_status=1
        fi
        if [ "$aard_status" -ne 0 ]; then
            aws s3 cp "$log" "$output_prefix/run.log" --no-progress
            if ! upload_aard_archive "$aard_out" "aard-partial.tar.gz"; then
                echo "error: failed to upload partial AARD archive after aard exit status $aard_status" >&2
                exit 1
            fi
            if [ "$events_failed" -ne 0 ]; then
                cat "$events_error_file" >&2
                exit 1
            fi
            echo "error: aard failed with exit status $aard_status" >&2
            exit "$aard_status"
        fi
        if ! upload_aard_archive "$aard_out" "aard-output.tar.gz"; then
            aws s3 cp "$log" "$output_prefix/run.log" --no-progress
            echo "error: failed to upload AARD archive" >&2
            exit 1
        fi
        ;;
    *)
        echo "error: unsupported ARB_EXEC_MODE: $mode" >&2
        exit 1
        ;;
esac

end_time="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
set -- $(sha384sum "$log")
log_sha384="$1"

cat > "$manifest" <<EOF
{
  "run_id": "$(json_string "$run_id")",
  "mode": "$(json_string "$mode")",
  "input_mode": "$(json_string "$aard_input_mode")",
  "aard_example": "$(json_string "$aard_example")",
  "aard_case_id": "$(json_string "$aard_case_id")",
  "started_at": "$(json_string "$start_time")",
  "finished_at": "$(json_string "$end_time")",
  "instance_id": "$(json_string "$instance_id")",
  "ami_id": "$(json_string "$ami_id")",
  "input_prefix": "$(json_string "$input_prefix")",
  "output_prefix": "$(json_string "$output_prefix")",
  "case_packet_key": "$(json_string "$case_packet_key")",
  "case_packet_sha384": "$(json_string "$case_packet_sha384")",
  "case_packet_bytes": "$(json_string "$case_packet_bytes")",
  "case_manifest_key": "$(json_string "$case_manifest_key")",
  "case_manifest_sha384": "$(json_string "$case_manifest_sha384")",
  "aard_archive_key": "$(json_string "$aard_archive_key")",
  "aard_archive_sha384": "$(json_string "$aard_archive_sha384")",
  "aard_archive_bytes": "$(json_string "$aard_archive_bytes")",
  "container_image_id": "$(json_string "${ARB_EXEC_IMAGE_ID:-}")",
  "container_image_tar_sha384": "$(json_string "${ARB_EXEC_IMAGE_TAR_SHA384:-}")",
  "log_sha384": "$(json_string "$log_sha384")"
}
EOF

set -- $(sha384sum "$manifest")
manifest_sha384="$1"
printf '%s\n' "$manifest_sha384" > "$manifest_hash_file"

attestation_raw="$run_dir/attestation.bin"
nitro-tpm-attest --user-data "$manifest_hash_file" > "$attestation_raw"
base64 "$attestation_raw" | tr -d '\n' > "$attestation"
printf '\n' >> "$attestation"

aws s3 cp "$log" "$output_prefix/run.log"
aws s3 cp "$manifest" "$output_prefix/manifest.json"
aws s3 cp "$manifest_hash_file" "$output_prefix/manifest.sha384"
aws s3 cp "$attestation" "$output_prefix/attestation.b64"

printf 'OUTPUT_PREFIX=%s\n' "$output_prefix"
printf 'MANIFEST_SHA384=%s\n' "$manifest_sha384"
printf 'ATTESTATION END\n'
