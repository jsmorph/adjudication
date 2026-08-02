#!/usr/bin/env bash
set -euo pipefail

usage() {
  printf 'Usage: %s COMPLAINT.md\n' "${0##*/}" >&2
}

if [ "$#" -ne 1 ]; then
  usage
  exit 2
fi

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
service_root="$(CDPATH= cd -- "$script_dir/../../.." && pwd)"

complaint_arg="$1"
if [ ! -f "$complaint_arg" ]; then
  printf 'error: complaint file does not exist: %s\n' "$complaint_arg" >&2
  exit 2
fi
complaint_dir="$(CDPATH= cd -- "$(dirname -- "$complaint_arg")" && pwd)"
complaint_name="$(basename -- "$complaint_arg")"
complaint_path="$complaint_dir/$complaint_name"

case_slug="${complaint_name%.*}"
case_slug="${case_slug//[^A-Za-z0-9_.-]/-}"
case "$case_slug" in
  ""|.*|*..*)
    printf 'error: invalid complaint-derived case slug: %s\n' "$case_slug" >&2
    exit 2
    ;;
esac

dev_host="${DEV_HOST:-dev}"
aws_region="${AWS_REGION:-us-east-2}"
exec_ami="${EXEC_AMI:-ami-011f957fe91cf7b81}"
input_root="${INPUT_ROOT:-s3://agentcourt-data/arbattest/adc-inputs}"
output_root="${OUTPUT_ROOT:-s3://agentcourt-data/arbattest/adc-runs}"
out_root="${OUT_ROOT:-$service_root/out/adc-attested}"
expected_pcr4="${EXPECTED_PCR4:-83AC49DFAA5D76939970E1568472FF463FBE90C4038D000D31F6C0520F583D1DD51CE0C103CEB26E4B773AAD99A4B3B4}"
expected_pcr7="${EXPECTED_PCR7:-98441C7F7625D10058C47683AEC486CE311C633235EB555593A7EE791121E3578AE72D04ECEF661F272D59058B77AF35}"

stamp="$(date -u +%Y%m%dT%H%M%SZ)"
case_id="${CASE_ID:-adc-$case_slug-$stamp}"
run_id="${RUN_ID:-run-$case_id}"
input_prefix="${INPUT_PREFIX:-$input_root/$case_id}"
output_prefix="${OUTPUT_PREFIX:-$output_root/$run_id}"
out_dir="${OUT_DIR:-$out_root/$run_id}"

mkdir -p "$out_root"

printf 'COMPLAINT=%s\n' "$complaint_path"
printf 'CASE_ID=%s\n' "$case_id"
printf 'INPUT_PREFIX=%s\n' "$input_prefix"
printf 'RUN_ID=%s\n' "$run_id"
printf 'OUTPUT_PREFIX=%s\n' "$output_prefix"
printf 'OUT_DIR=%s\n' "$out_dir"

ssh "$dev_host" "set -eu
AWS_DEFAULT_REGION='$aws_region' aws s3 cp /home/ec2-user/arbattest-secrets/auth.json '$input_prefix/auth.json' --no-progress
AWS_DEFAULT_REGION='$aws_region' aws s3 cp /home/ec2-user/arbattest-secrets/keys.sh '$input_prefix/keys.sh' --no-progress
AWS_DEFAULT_REGION='$aws_region' aws s3 ls '$input_prefix/'"

uv run "$script_dir/run-adc-attested.py" \
  --complaint "$complaint_path" \
  --case-id "$case_id" \
  --run-id "$run_id" \
  --input-prefix "$input_prefix" \
  --exec-ami "$exec_ami" \
  --output-prefix "$output_prefix" \
  --out-dir "$out_dir" \
  --verify \
  --expected-pcr4 "$expected_pcr4" \
  --expected-pcr7 "$expected_pcr7"
