#!/usr/bin/env bash
# Serve the built static site over HTTP (required for MyST; file:// will not work).
# Run from repository root after ./setup-book.sh. Leave this terminal open while browsing.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HTML="$ROOT/book/_build/html"
if [[ ! -f "$HTML/index.html" ]]; then
  echo "No built site at $HTML — run ./setup-book.sh first."
  exit 1
fi
cd "$HTML"
PORT="${PORT:-8844}"
echo "Serving MyST output at http://localhost:${PORT}/"
echo "Leave this window open. Press Ctrl+C to stop."
exec python3 -m http.server "$PORT"
