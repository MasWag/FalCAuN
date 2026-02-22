#!/usr/bin/env sh
set -eu

if ! command -v ktlint >/dev/null 2>&1; then
    echo "ktlint is not installed. Please install ktlint 1.8.0 or newer." >&2
    exit 127
fi

SCRIPT_DIR=$(cd -- "$(dirname -- "$0")" && pwd)

ktlint "$SCRIPT_DIR/**/*.kt" "$SCRIPT_DIR/**/*.kts"
