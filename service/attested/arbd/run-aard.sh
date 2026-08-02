#!/bin/sh
set -eu

export AWS_DEFAULT_REGION="${AWS_DEFAULT_REGION:-us-east-2}"

image_tar_s3="${IMAGE_TAR_S3:-s3://agentcourt-data/arbattest/images/arbd-glue-poc.tar}"
: "${INPUT_PREFIX:?INPUT_PREFIX is required}"
input_prefix="${INPUT_PREFIX%/}"
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
aard_case_id="${AARD_CASE_ID:-}"
if [ -n "$aard_case_id" ]; then
    case "$aard_case_id" in
        .*|*/*|*..*)
            echo "error: invalid AARD_CASE_ID: $aard_case_id" >&2
            exit 1
            ;;
    esac
fi
case_packet="${AARD_CASE_PACKET:-}"
case_manifest="${AARD_CASE_MANIFEST:-}"
case_packet_sha384="${AARD_CASE_PACKET_SHA384:-}"
case_manifest_sha384="${AARD_CASE_MANIFEST_SHA384:-}"
if [ "$aard_input_mode" = "case-packet" ]; then
    case_packet="${case_packet:-case.tar.gz}"
    case_manifest="${case_manifest:-case-packet.json}"
    case "$case_packet" in
        ""|.*|*/*|*..*)
            echo "error: invalid AARD_CASE_PACKET: $case_packet" >&2
            exit 1
            ;;
    esac
    case "$case_manifest" in
        ""|.*|*/*|*..*)
            echo "error: invalid AARD_CASE_MANIFEST: $case_manifest" >&2
            exit 1
            ;;
    esac
    if [ -z "$case_packet_sha384" ]; then
        echo "error: AARD_CASE_PACKET_SHA384 is required for case-packet input mode" >&2
        exit 1
    fi
    if [ -z "$case_manifest_sha384" ]; then
        echo "error: AARD_CASE_MANIFEST_SHA384 is required for case-packet input mode" >&2
        exit 1
    fi
fi
if [ -n "$case_packet_sha384" ] && [ "${#case_packet_sha384}" -ne 96 ]; then
    echo "error: invalid AARD_CASE_PACKET_SHA384 length" >&2
    exit 1
fi
if [ -n "$case_manifest_sha384" ] && [ "${#case_manifest_sha384}" -ne 96 ]; then
    echo "error: invalid AARD_CASE_MANIFEST_SHA384 length" >&2
    exit 1
fi
output_root="${OUTPUT_ROOT:-s3://agentcourt-data/arbattest/aard-runs}"
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
case "$aard_input_mode" in
    example) default_run_name="$aard_example" ;;
    *) default_run_name="case" ;;
esac
run_id="${RUN_ID:-aard-$default_run_name-$stamp}"
output_prefix="${OUTPUT_PREFIX:-$output_root/$run_id}"
work_root="${WORK_ROOT:-/var/lib/arbattest-aard}"
image_ref="${IMAGE_REF:-arbd-glue:poc}"

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
    -e AARD_INPUT_MODE="$aard_input_mode" \
    -e AARD_EXAMPLE="$aard_example" \
    -e AARD_CASE_ID="$aard_case_id" \
    -e AARD_CASE_PACKET="$case_packet" \
    -e AARD_CASE_MANIFEST="$case_manifest" \
    -e AARD_CASE_PACKET_SHA384="$case_packet_sha384" \
    -e AARD_CASE_MANIFEST_SHA384="$case_manifest_sha384" \
    -e ARB_EXEC_MODE=aard \
    -e ARB_EXEC_WORK_ROOT="$work_root" \
    -e ARB_EXEC_IMAGE_ID="$image_id" \
    -e ARB_EXEC_IMAGE_TAR_SHA384="$image_tar_sha384" \
    "$image_ref"

printf 'INPUT_PREFIX=%s\n' "$input_prefix"
printf 'AARD_INPUT_MODE=%s\n' "$aard_input_mode"
printf 'AARD_EXAMPLE=%s\n' "$aard_example"
printf 'AARD_CASE_ID=%s\n' "$aard_case_id"
printf 'AARD_CASE_PACKET=%s\n' "$case_packet"
printf 'AARD_CASE_MANIFEST=%s\n' "$case_manifest"
printf 'OUTPUT_PREFIX=%s\n' "$output_prefix"
