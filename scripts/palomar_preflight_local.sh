#!/usr/bin/env bash
set -euo pipefail
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
