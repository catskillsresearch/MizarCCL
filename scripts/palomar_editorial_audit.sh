#!/usr/bin/env bash
# Editorial audit wrapper: cursor-sdk venv (local or scott1964 fallback).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

pick_python() {
  if [[ -x .venv-editorial/bin/python ]]; then
    echo .venv-editorial/bin/python
    return
  fi
  local sibling="$ROOT/../scott1964/.venv-ocr/bin/python"
  if [[ -x "$sibling" ]]; then
    "$sibling" -c "import cursor_sdk" 2>/dev/null && {
      echo "$sibling"
      return
    }
  fi
  python3 -m venv .venv-editorial
  .venv-editorial/bin/pip install -r scripts/requirements-editorial.txt
  echo .venv-editorial/bin/python
}

exec "$(pick_python)" scripts/palomar_editorial_audit.py "$@"
