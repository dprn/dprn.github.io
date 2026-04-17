#!/usr/bin/env bash
# Minify css/resume.css -> css/resume.min.css using clean-css-cli (via npx, no install needed)
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
SRC="$DIR/resume.css"
OUT="$DIR/resume.min.css"

echo "Minifying $SRC -> $OUT"
npx --yes clean-css-cli "$SRC" -o "$OUT"
echo "Done."
