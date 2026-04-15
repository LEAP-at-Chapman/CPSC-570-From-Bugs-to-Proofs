#!/usr/bin/env bash
# Local Jupyter Book 2 setup and suggested Git workflow for chapter contributions.
# Run from repository root: ./book/scripts/student-book-setup.sh
# (Same entry point: ./scripts/student-book-setup.sh)
# Install + build from repo root without Git hints: ./setup-book.sh

set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ ! -f "$ROOT/setup.sh" ]]; then
  echo "Expected book/setup.sh (this script should live in book/scripts/)."
  exit 1
fi

bash "$ROOT/setup.sh"

# shellcheck disable=SC1091
source "$ROOT/.venv/bin/activate"

echo ""
echo "Building static HTML (output in book/_build/html) ..."
jupyter-book build --html

echo ""
echo "---- Local preview ----"
echo "  From repo root:  ./serve-book.sh   then open http://localhost:8844/"
echo "  (Leave the server running; ERR_CONNECTION_REFUSED means nothing is listening on that port.)"
echo "  Or: cd \"$ROOT\" && source .venv/bin/activate && jupyter-book start"
echo ""
echo "  For GitHub Pages, rebuild with BASE_URL (see README or book/scripts/build-github-pages.sh)."
echo ""

if ! command -v git >/dev/null 2>&1; then
  echo "Git not found; install Git to contribute via pull request."
  exit 0
fi

if git rev-parse --git-dir >/dev/null 2>&1; then
  REPO_ROOT="$(git rev-parse --show-toplevel)"
  BRANCH_DEFAULT="$(git symbolic-ref refs/remotes/origin/HEAD 2>/dev/null | sed 's@^refs/remotes/origin/@@' || true)"
  if [[ -z "${BRANCH_DEFAULT}" ]]; then
    BRANCH_DEFAULT="main"
  fi
  echo "---- Contributing your chapter ----"
  echo "1. Create a branch (example):"
  echo "     cd \"$REPO_ROOT\""
  echo "     git fetch origin"
  echo "     git checkout ${BRANCH_DEFAULT}"
  echo "     git pull --ff-only origin ${BRANCH_DEFAULT}"
  echo "     git checkout -b book/07-haskell"
  echo ""
  echo "2. Edit files under book/content/ (see book/book-chapters.md and"
  echo "   book/book-chapter-assignments.md)."
  echo ""
  echo "3. Rebuild locally:"
  echo "     cd \"$ROOT\""
  echo "     source .venv/bin/activate"
  echo "     jupyter-book build --html"
  echo ""
  echo "4. Commit and push to your fork (or origin if you have write access):"
  echo "     git status"
  echo "     git add book/ setup-book.sh serve-book.sh deploy-book.sh README.md .github/"
  echo "     git commit -m \"Book: progress on Haskell chapter\""
  echo "     git push -u origin HEAD"
  echo ""
  echo "5. Open a pull request on GitHub and request your assigned reviewer."
else
  echo "This directory is not a Git clone yet."
  echo "Fork the course repo on GitHub, then:"
  echo "  git clone https://github.com/<YOUR_USER>/CPSC-570-From-Bugs-to-Proofs.git"
  echo "  cd CPSC-570-From-Bugs-to-Proofs"
  echo "  git remote add upstream https://github.com/LEAP-at-Chapman/CPSC-570-From-Bugs-to-Proofs.git"
  echo "  ./book/scripts/student-book-setup.sh"
fi
