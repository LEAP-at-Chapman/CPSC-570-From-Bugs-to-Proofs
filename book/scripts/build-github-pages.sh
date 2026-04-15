#!/usr/bin/env bash
# Build HTML with BASE_URL for https://<org>.github.io/<repo>/
# Run from repo root: ./book/scripts/build-github-pages.sh
# (Requires book/.venv — run ./setup-book.sh or book/setup.sh first.)
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

export BASE_URL="/CPSC-570-From-Bugs-to-Proofs"

# shellcheck disable=SC1091
source "$ROOT/.venv/bin/activate"
echo "Building with BASE_URL=${BASE_URL} ..."
jupyter-book build --html
echo "Output: $ROOT/_build/html/ (ready for ghp-import to gh-pages)"
