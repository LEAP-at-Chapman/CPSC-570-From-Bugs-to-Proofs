#!/usr/bin/env bash
# Create book/.venv, install Jupyter Book dependencies, and build static HTML.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BOOK="$ROOT/book"

bash "$BOOK/setup.sh"

# shellcheck disable=SC1091
source "$BOOK/.venv/bin/activate"
cd "$BOOK"
echo ""
echo "Building static HTML ..."
jupyter-book build --html

echo ""
echo "Done. Open: $BOOK/_build/html/index.html"
echo "  macOS:  open \"$BOOK/_build/html/index.html\""
echo "  Linux:  xdg-open \"$BOOK/_build/html/index.html\""
