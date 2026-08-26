#!/usr/bin/env bash
# Reproduce the repository-side mechanical checks needed before Palomar submission.
set -euo pipefail
cd "$(dirname "$0")/.."

step() {
  printf '\n== %s ==\n' "$1"
}

step "Validate Comparator configuration"
python3 - <<'PY'
import json

with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)

required = ("challenge_module", "solution_module", "theorem_names",
            "definition_names", "permitted_axioms")
missing = [key for key in required if key not in cfg]
if missing:
    raise SystemExit(f"Missing comparator keys: {', '.join(missing)}")

names = cfg["theorem_names"] + cfg["definition_names"]
duplicates = sorted({name for name in names if names.count(name) > 1})
if duplicates:
    raise SystemExit(f"Duplicate Comparator names: {', '.join(duplicates)}")
print(f"OK: {len(cfg['theorem_names'])} theorem targets and "
      f"{len(cfg['definition_names'])} definition targets.")
PY

step "Reject git submodules (Palomar cannot preserve them)"
if [[ -e .gitmodules ]]; then
  echo "FAIL: .gitmodules is present; Palomar cannot preserve submodules."
  exit 1
fi
echo "OK: no .gitmodules."

step "Match formalization.yaml MML pin to the used-module vendor"
python3 - <<'PY'
import re
from pathlib import Path

pin = Path("vendor/MML_PIN").read_text(encoding="utf-8").strip()
if pin != "047822c4d814630b28eec8ca6b455e9eb912d5ff":
    raise SystemExit(f"Unexpected vendor/MML_PIN: {pin}")
queue = Path("mizarccl_translation_order.yaml").read_text(encoding="utf-8")
wanted = ["vendor/mml/hidden.miz"] + re.findall(
    r"^    file: (vendor/mml/[A-Za-z0-9_]+\.miz)$", queue, re.M
)
missing = [rel for rel in wanted if not Path(rel).is_file()]
if missing:
    raise SystemExit(
        "Missing vendored sources:\n  " + "\n  ".join(missing[:20])
    )
readme = Path("vendor/README.md").read_text(encoding="utf-8")
meta = Path("formalization.yaml").read_text(encoding="utf-8")
if pin not in readme:
    raise SystemExit("vendor/README.md is missing vendor/MML_PIN")
if pin not in meta:
    raise SystemExit("formalization.yaml is missing vendor/MML_PIN")
print(
    f"OK: {len(wanted)} vendored .miz files and formalization.yaml "
    f"record pin {pin}."
)
PY

step "Build Lean project"
lake build

step "Compare Challenge/Solution declaration types"
PALOMAR_QUIET=1 bash scripts/compare_challenge_solution_types.sh

step "Reject proof holes in Solution sources"
if rg -n --glob '*.lean' \
    '(^|:=|by)[[:space:]]+sorry([[:space:];]|$)|^[[:space:]]*sorry([[:space:];]|$)' \
    MizarCCL/HIDDEN.lean MizarCCL/TARSKI.lean Solution.lean; then
  echo "FAIL: Solution proof sources contain sorry."
  exit 1
fi
echo "OK: Solution proof sources contain no sorry."

step "Check permitted theorem axioms"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 - "$tmp/Axioms.lean" <<'PY'
import json
import sys

with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)
with open(sys.argv[1], "w", encoding="utf-8") as out:
    out.write(f"import {cfg['solution_module']}\n")
    for name in cfg["theorem_names"]:
        out.write(f"#print axioms {name}\n")
PY
lake env lean "$tmp/Axioms.lean" >"$tmp/axioms.txt"
python3 - "$tmp/axioms.txt" <<'PY'
import json
import re
import sys

with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)
allowed = set(cfg["permitted_axioms"])
text = open(sys.argv[1], encoding="utf-8").read()
reports = re.findall(
    r"^'(.+)' depends on axioms: \[([^\]]*)\]$", text, re.MULTILINE
)
axiom_free = re.findall(
    r"^'(.+)' does not depend on any axioms$", text, re.MULTILINE
)
reported = {name for name, _ in reports} | set(axiom_free)
expected = set(cfg["theorem_names"])
if reported != expected:
    missing = sorted(expected - reported)
    extra = sorted(reported - expected)
    raise SystemExit(f"Axiom report mismatch; missing={missing}, extra={extra}")
for name, raw in reports:
    used = {item.strip() for item in raw.split(",") if item.strip()}
    forbidden = sorted(used - allowed)
    if forbidden:
        raise SystemExit(f"{name} uses forbidden axioms: {', '.join(forbidden)}")
print(f"OK: all theorem targets use only {sorted(allowed)}.")
PY

step "Check patch formatting"
git diff --check
echo "OK: Palomar preflight passed."
