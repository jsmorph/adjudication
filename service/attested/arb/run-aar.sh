#!/bin/sh
set -eu

export AWS_DEFAULT_REGION="${AWS_DEFAULT_REGION:-us-east-2}"

image_tar_s3="${IMAGE_TAR_S3:-s3://agentcourt-data/arbattest/images/arb-glue-poc.tar}"
: "${INPUT_PREFIX:?INPUT_PREFIX is required}"
input_prefix="${INPUT_PREFIX%/}"
aar_input_mode="${AAR_INPUT_MODE:-example}"
case "$aar_input_mode" in
    example|case-packet) ;;
    *)
        echo "error: invalid AAR_INPUT_MODE: $aar_input_mode" >&2
        exit 1
        ;;
esac
case "$aar_input_mode" in
    example) aar_example="${AAR_EXAMPLE:-ex01}" ;;
    *) aar_example="${AAR_EXAMPLE:-}" ;;
esac
if [ -n "$aar_example" ]; then
    case "$aar_example" in
        .*|*/*|*..*)
            echo "error: invalid AAR_EXAMPLE: $aar_example" >&2
            exit 1
            ;;
    esac
fi
if [ "$aar_input_mode" = "example" ] && [ -z "$aar_example" ]; then
    echo "error: AAR_EXAMPLE is required for example input mode" >&2
    exit 1
fi
aar_case_id="${AAR_CASE_ID:-}"
if [ -n "$aar_case_id" ]; then
    case "$aar_case_id" in
        .*|*/*|*..*)
            echo "error: invalid AAR_CASE_ID: $aar_case_id" >&2
            exit 1
            ;;
    esac
fi
case_packet="${AAR_CASE_PACKET:-}"
case_manifest="${AAR_CASE_MANIFEST:-}"
case_packet_sha384="${AAR_CASE_PACKET_SHA384:-}"
case_manifest_sha384="${AAR_CASE_MANIFEST_SHA384:-}"
if [ "$aar_input_mode" = "case-packet" ]; then
    case_packet="${case_packet:-case.tar.gz}"
    case_manifest="${case_manifest:-case-packet.json}"
    case "$case_packet" in
        ""|.*|*/*|*..*)
            echo "error: invalid AAR_CASE_PACKET: $case_packet" >&2
            exit 1
            ;;
    esac
    case "$case_manifest" in
        ""|.*|*/*|*..*)
            echo "error: invalid AAR_CASE_MANIFEST: $case_manifest" >&2
            exit 1
            ;;
    esac
    if [ -z "$case_packet_sha384" ]; then
        echo "error: AAR_CASE_PACKET_SHA384 is required for case-packet input mode" >&2
        exit 1
    fi
    if [ -z "$case_manifest_sha384" ]; then
        echo "error: AAR_CASE_MANIFEST_SHA384 is required for case-packet input mode" >&2
        exit 1
    fi
fi
if [ -n "$case_packet_sha384" ] && [ "${#case_packet_sha384}" -ne 96 ]; then
    echo "error: invalid AAR_CASE_PACKET_SHA384 length" >&2
    exit 1
fi
if [ -n "$case_manifest_sha384" ] && [ "${#case_manifest_sha384}" -ne 96 ]; then
    echo "error: invalid AAR_CASE_MANIFEST_SHA384 length" >&2
    exit 1
fi
output_root="${OUTPUT_ROOT:-s3://agentcourt-data/arbattest/aar-runs}"
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
case "$aar_input_mode" in
    example) default_run_name="$aar_example" ;;
    *) default_run_name="case" ;;
esac
run_id="${RUN_ID:-aar-$default_run_name-$stamp}"
output_prefix="${OUTPUT_PREFIX:-$output_root/$run_id}"
work_root="${WORK_ROOT:-/var/lib/arbattest-aar}"
image_ref="${IMAGE_REF:-arb-glue:poc}"

mkdir -p "$work_root"

i=0
while ! docker info >/dev/null 2>&1; do
    i=$((i + 1))
    if [ "$i" -ge 60 ]; then
        echo "error: Docker daemon did not become ready" >&2
        exit 1
    fi
    sleep 1
done

image_tar="$work_root/image.tar"
aws s3 cp "$image_tar_s3" "$image_tar" --no-progress
set -- $(sha384sum "$image_tar")
image_tar_sha384="$1"
docker load -i "$image_tar"
image_id="$(docker image inspect "$image_ref" --format '{{.Id}}')"

if [ ! -e /dev/tpm0 ]; then
    echo "error: /dev/tpm0 is required for nitro-tpm-attest" >&2
    exit 1
fi

device_args="--device /dev/tpm0"
if [ -e /dev/tpmrm0 ]; then
    device_args="$device_args --device /dev/tpmrm0"
fi

docker run --rm \
    --network host \
    $device_args \
    -v /var/run/docker.sock:/var/run/docker.sock \
    -v "$work_root:$work_root" \
    -e AWS_DEFAULT_REGION \
    -e INPUT_PREFIX="$input_prefix" \
    -e OUTPUT_PREFIX="$output_prefix" \
    -e RUN_ID="$run_id" \
    -e AAR_INPUT_MODE="$aar_input_mode" \
    -e AAR_EXAMPLE="$aar_example" \
    -e AAR_CASE_ID="$aar_case_id" \
    -e AAR_CASE_PACKET="$case_packet" \
    -e AAR_CASE_MANIFEST="$case_manifest" \
    -e AAR_CASE_PACKET_SHA384="$case_packet_sha384" \
    -e AAR_CASE_MANIFEST_SHA384="$case_manifest_sha384" \
    -e ARB_EXEC_MODE=aar \
    -e ARB_EXEC_WORK_ROOT="$work_root" \
    -e ARB_EXEC_IMAGE_ID="$image_id" \
    -e ARB_EXEC_IMAGE_TAR_SHA384="$image_tar_sha384" \
    "$image_ref"

printf 'INPUT_PREFIX=%s\n' "$input_prefix"
printf 'AAR_INPUT_MODE=%s\n' "$aar_input_mode"
printf 'AAR_EXAMPLE=%s\n' "$aar_example"
printf 'AAR_CASE_ID=%s\n' "$aar_case_id"
printf 'AAR_CASE_PACKET=%s\n' "$case_packet"
printf 'AAR_CASE_MANIFEST=%s\n' "$case_manifest"
printf 'OUTPUT_PREFIX=%s\n' "$output_prefix"
