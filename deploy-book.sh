#!/usr/bin/env bash
# Build with BASE_URL for GitHub Pages and push HTML to the gh-pages branch (requires git + gh auth).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT"

if ! command -v ghp-import >/dev/null 2>&1; then
  echo "ghp-import not found. Install with: pip install ghp-import"
  echo "(or use book/requirements.txt from book/.venv: source book/.venv/bin/activate)"
  exit 1
fi

bash "$ROOT/book/scripts/build-github-pages.sh"
echo ""
echo "Publishing to gh-pages branch ..."
ghp-import -n -p -f "$ROOT/book/_build/html"
echo "Done. After GitHub Pages picks up gh-pages, the site should appear at:"
echo "  https://leap-at-chapman.github.io/CPSC-570-From-Bugs-to-Proofs/"
