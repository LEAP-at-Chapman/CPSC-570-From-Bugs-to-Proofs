#!/usr/bin/env bash
# Create book/.venv, install Jupyter Book dependencies, and build static HTML.
#
# Preview: MyST uses absolute paths like /build/... — do not open index.html via
# file:// (use jupyter-book start or a local HTTP server; see README).
#
# GitHub project Pages (this repo): build with BASE_URL set, e.g.
#   BASE_URL=/CPSC-570-From-Bugs-to-Proofs ./setup-book.sh
# or run: ./book/scripts/build-github-pages.sh
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BOOK="$ROOT/book"

bash "$BOOK/setup.sh"

# shellcheck disable=SC1091
source "$BOOK/.venv/bin/activate"
cd "$BOOK"
echo ""
echo "Building static HTML ..."
if [[ -n "${BASE_URL:-}" ]]; then
  echo "(BASE_URL is set to: ${BASE_URL})"
fi
jupyter-book build --html

echo ""
echo "Built: $BOOK/_build/html/"
echo ""
echo "Preview (keep the server terminal open — otherwise the browser shows ERR_CONNECTION_REFUSED):"
echo "  ./serve-book.sh"
echo "  then open http://localhost:8844/  (override port: PORT=9000 ./serve-book.sh)"
echo "Alternatives:  cd \"$BOOK\" && source .venv/bin/activate && jupyter-book start"
