#!/usr/bin/env bash
# Python environment for Jupyter Book 2 (MyST).

set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT"

if ! command -v python3 >/dev/null 2>&1; then
  echo "Python 3 is required."
  exit 1
fi

if [[ ! -d .venv ]]; then
  echo "Creating virtual environment in .venv ..."
  python3 -m venv .venv
fi

# shellcheck disable=SC1091
source .venv/bin/activate
python -m pip install -U pip
pip install -r requirements.txt

jupyter-book --version

echo ""
echo "Build static site:  jupyter-book build --html"
echo "Live preview:       jupyter-book start"
echo "Open after build:   open _build/html/index.html"
