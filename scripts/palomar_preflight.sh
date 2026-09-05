#!/usr/bin/env bash
# Exec shared Palomar preflight from ../palomar-preflight (or CI checkout / legacy vendor).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

find_toolkit() {
  local root="$1" d
  for d in \
    "${PALOMAR_PREFLIGHT_ROOT:-}" \
    "$(dirname "$root")/palomar-preflight" \
    "$root/palomar-preflight" \
    "$root/vendor/palomar-preflight"; do
    [[ -n "$d" && -f "$d/palomar_preflight.sh" ]] && {
      cd "$d" && pwd
      return 0
    }
  done
  echo "error: palomar-preflight not found; set PALOMAR_PREFLIGHT_ROOT or checkout toolkit" >&2
  return 1
}

toolkit_supports_cli() {
  bash "$1/palomar_preflight.sh" --help 2>&1 | grep -q -- '--project-root'
}

TOOLKIT="$(find_toolkit "$ROOT")"
SORRY_PATHS="MizarCCL/HIDDEN.lean MizarCCL/TARSKI.lean Solution.lean"
EXTRA_PRINT_NAMES=(
  PreSet
  PreSet.Equiv
  PreSet.instSetoid
  PreSet.Mem
  TarskiSet
  TarskiSet.mem
  instMembership
  TARSKI.subset
  TARSKI.instHasSubset
)

if toolkit_supports_cli "$TOOLKIT"; then
  args=(
    --project-root "$ROOT"
    --sorry-paths "$SORRY_PATHS"
    --closure-prefix PreSet
    --closure-prefix TarskiSet
    --closure-prefix instMembership
  )
  for name in "${EXTRA_PRINT_NAMES[@]}"; do
    args+=(--extra-print-name "$name")
  done
  export PALOMAR_CHECK_DECL_KINDS=0
  exec bash "$TOOLKIT/palomar_preflight.sh" "${args[@]}" "$@"
fi

export PALOMAR_PROJECT_ROOT="$ROOT"
export PALOMAR_SORRY_PATHS="$SORRY_PATHS"
export PALOMAR_CHECK_DECL_KINDS=0
export PALOMAR_CLOSURE_PREFIXES="PreSet TarskiSet instMembership"
export PALOMAR_EXTRA_PRINT_NAMES="${EXTRA_PRINT_NAMES[*]}"
exec bash "$TOOLKIT/palomar_preflight.sh" "$@"
