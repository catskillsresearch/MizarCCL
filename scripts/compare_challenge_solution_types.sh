#!/usr/bin/env bash
# Diff Challenge vs Solution declaration types for every comparator.json name.
set -euo pipefail
cd "$(dirname "$0")/.."

mapfile -t NAMES < <(python3 - <<'PY'
import json
with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)
declarations = cfg.get("declarations")
if declarations is None:
    declarations = cfg.get("theorem_names", []) + cfg.get("definition_names", [])
for name in declarations:
    print(name)
PY
)

# Palomar Comparator also rejects shared extra constants whose
# *values* differ (e.g. a sorry PreSet.instSetoid vs the real one).
mapfile -t SHARED < <(printf '%s\n' \
  PreSet \
  PreSet.Equiv \
  PreSet.instSetoid \
  PreSet.Mem \
  TarskiSet \
  TarskiSet.mem \
  instMembership \
  TARSKI.subset \
  TARSKI.instHasSubset)

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

write_lean() {
  local module="$1" out="$2"
  {
    echo "import ${module}"
    echo "set_option pp.all true"
    echo "set_option pp.explicit true"
    echo "set_option pp.universes true"
    echo "set_option pp.funBinderTypes true"
    for n in "${NAMES[@]}"; do
      echo "#check ${n}"
    done
    for n in "${SHARED[@]}"; do
      echo "#print ${n}"
    done
  } >"${out}"
}

write_lean Challenge "${tmp}/ChallengeTypes.lean"
write_lean Solution "${tmp}/SolutionTypes.lean"

lake env lean "${tmp}/ChallengeTypes.lean" 2>/dev/null \
  | grep -vE 'LEAN_PATH|trace:|warning:|declaration uses' \
  >"${tmp}/challenge.txt" || true
lake env lean "${tmp}/SolutionTypes.lean" 2>/dev/null \
  | grep -vE 'LEAN_PATH|trace:|warning:|declaration uses' \
  >"${tmp}/solution.txt" || true

if [[ "${PALOMAR_QUIET:-}" != 1 ]]; then
  echo "== Challenge (pp.all) =="
  cat "${tmp}/challenge.txt"
  echo
  echo "== Solution (pp.all) =="
  cat "${tmp}/solution.txt"
  echo
fi
if diff -u "${tmp}/challenge.txt" "${tmp}/solution.txt"; then
  echo "OK: Challenge and Solution types match exactly."
else
  echo "FAIL: type/universe/instance mismatch — Palomar Comparator will reject this."
  exit 1
fi
