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
import re

with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)

allowed_keys = {
    "challenge_module",
    "solution_module",
    "theorem_names",
    "definition_names",
    "permitted_axioms",
    "enable_nanoda",
}
unknown = sorted(set(cfg) - allowed_keys)
if unknown:
    raise SystemExit(f"Unknown comparator.json keys: {', '.join(unknown)}")

for key in ("challenge_module", "solution_module", "theorem_names", "permitted_axioms"):
    if key not in cfg:
        raise SystemExit(f"Missing comparator.json key: {key}")

challenge = cfg["challenge_module"]
solution = cfg["solution_module"]
theorems = cfg["theorem_names"]
definitions = cfg.get("definition_names", [])
axioms = cfg["permitted_axioms"]

if challenge == solution:
    raise SystemExit("challenge_module and solution_module must differ")

module_part = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
for key in ("challenge_module", "solution_module"):
    name = cfg[key]
    if not isinstance(name, str) or not name:
        raise SystemExit(f"{key} must be a nonempty string")
    if not all(module_part.fullmatch(part) for part in name.split(".")):
        raise SystemExit(f"{key} is not a safe dotted Lean module name: {name!r}")

if not isinstance(theorems, list) or not theorems or not all(
    isinstance(name, str) and name for name in theorems
):
    raise SystemExit("theorem_names must be a nonempty array of nonempty strings")

if definitions is not None:
    if not isinstance(definitions, list) or not all(
        isinstance(name, str) and name for name in definitions
    ):
        raise SystemExit("definition_names must be an array of nonempty strings")

allowed_axioms = {"propext", "Quot.sound", "Classical.choice"}
if not isinstance(axioms, list) or not all(isinstance(x, str) for x in axioms):
    raise SystemExit("permitted_axioms must be an array of strings")
extra = sorted(set(axioms) - allowed_axioms)
if extra:
    raise SystemExit(
        "permitted_axioms exceeds Palomar allowlist "
        f"(forbidden: {', '.join(extra)})"
    )

declarations = theorems + definitions
duplicates = sorted({name for name in declarations if declarations.count(name) > 1})
if duplicates:
    raise SystemExit(f"Duplicate Comparator names: {', '.join(duplicates)}")

print(
    f"OK: challenge_module={challenge}, solution_module={solution}, "
    f"{len(theorems)} theorems, {len(definitions)} definitions, "
    f"{len(declarations)} declarations."
)
PY

step "Challenge import discipline (Init / Mathlib only)"
python3 - <<'PY'
import re
from pathlib import Path

text = Path("Challenge.lean").read_text(encoding="utf-8")
imports = re.findall(r"^import\s+(\S+)", text, re.MULTILINE)
for imp in imports:
    if imp.startswith("MizarCCL") or imp.startswith("Solution"):
        raise SystemExit(f"Forbidden Challenge import: {imp}")
    if not (imp.startswith("Init") or imp.startswith("Std")
            or imp.startswith("Lean") or imp.startswith("Mathlib")):
        raise SystemExit(
            f"Challenge import not allowlisted (Init/Mathlib/Std/Lean): {imp}"
        )
print(f"OK: Challenge has {len(imports)} explicit import(s) (Init-only if zero).")
PY

step "Challenge surface size limits"
python3 - <<'PY'
from pathlib import Path

path = Path("Challenge.lean")
lines = path.read_text(encoding="utf-8").count("\n") + 1
size = path.stat().st_size
if lines >= 1000:
    raise SystemExit(f"Challenge.lean too long: {lines} lines (limit 1000)")
if size >= 100 * 1024:
    raise SystemExit(f"Challenge.lean too large: {size} bytes (limit 100 KiB)")
print(f"OK: Challenge.lean is {lines} lines, {size} bytes.")
PY

step "Exactly one Lake manifest at repository root"
if [[ -f lakefile.toml && -f lakefile.lean ]]; then
  echo "FAIL: both lakefile.toml and lakefile.lean present."
  exit 1
fi
if [[ ! -f lakefile.toml && ! -f lakefile.lean ]]; then
  echo "FAIL: no lakefile.toml or lakefile.lean at repository root."
  exit 1
fi
if [[ ! -f lake-manifest.json ]]; then
  echo "FAIL: lake-manifest.json is missing."
  exit 1
fi
if [[ ! -f lean-toolchain ]]; then
  echo "FAIL: lean-toolchain is missing."
  exit 1
fi
echo "OK: Lake config, manifest, and toolchain present."

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
python3 - <<'PY'
import re
from pathlib import Path

# Match proof holes, not mentions in comments/docstrings.
pattern = re.compile(
    r"(^|:=|by)\s+sorry([\s;]|$)|^\s*sorry([\s;]|$)",
    re.MULTILINE,
)
files = [
    Path("MizarCCL/HIDDEN.lean"),
    Path("MizarCCL/TARSKI.lean"),
    Path("Solution.lean"),
]
hits = []
for path in files:
    if not path.is_file():
        raise SystemExit(f"Missing Palomar proof source: {path}")
    text = path.read_text(encoding="utf-8")
    for match in pattern.finditer(text):
        line = text.count("\n", 0, match.start()) + 1
        hits.append(f"{path}:{line}")
if hits:
    print("FAIL: Solution proof sources contain sorry:")
    for hit in hits:
        print(f"  {hit}")
    raise SystemExit(1)
print("OK: Solution proof sources contain no sorry.")
PY

step "Check permitted theorem axioms"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 - "$tmp/Axioms.lean" <<'PY'
import json
import sys

with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)
theorems = cfg["theorem_names"]
with open(sys.argv[1], "w", encoding="utf-8") as out:
    out.write(f"import {cfg['solution_module']}\n")
    for name in theorems:
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
theorems = cfg["theorem_names"]
text = open(sys.argv[1], encoding="utf-8").read()
reports = re.findall(
    r"^'(.+)' depends on axioms: \[([^\]]*)\]$", text, re.MULTILINE
)
axiom_free = re.findall(
    r"^'(.+)' does not depend on any axioms$", text, re.MULTILINE
)
reported = {name for name, _ in reports} | set(axiom_free)
expected = set(theorems)
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
