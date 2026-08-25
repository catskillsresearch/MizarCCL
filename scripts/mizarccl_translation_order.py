#!/usr/bin/env python3
"""Rebuild mizarccl_translation_order.yaml from vendor/MML environs."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MML_DIR = ROOT / "vendor" / "MML" / "mml"
LAR_PATH = ROOT / "vendor" / "MML" / "mml.lar"
OUT = ROOT / "mizarccl_translation_order.yaml"
PIN = "047822c4d814630b28eec8ca6b455e9eb912d5ff"

KEYWORD_RE = re.compile(
    r"^\s*(vocabularies|notations|constructors|registrations|"
    r"requirements|definitions|equalities|expansions|theorems|schemes)\b(.*)$"
)
IDENT_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*")
ARTICLE_KINDS = {
    "notations", "constructors", "registrations", "definitions",
    "equalities", "expansions", "theorems", "schemes",
}


def parse_article_deps(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8", errors="replace")
    match = re.search(r"^environ\s*\n(.*?)^begin\b", text, re.S | re.M)
    if not match:
        return []
    current = None
    names: list[str] = []
    seen: set[str] = set()
    for raw in match.group(1).splitlines():
        line = raw.split("::", 1)[0]
        km = KEYWORD_RE.match(line)
        if km:
            current = km.group(1)
            rest = km.group(2)
        else:
            rest = line
            if current is None:
                continue
        if current not in ARTICLE_KINDS:
            continue
        for name in IDENT_RE.findall(rest):
            name = name.upper()
            if name not in seen:
                seen.add(name)
                names.append(name)
    return names


def main() -> None:
    files = {p.stem.upper(): p for p in MML_DIR.glob("*.miz")}
    graph = {}
    for art, path in files.items():
        graph[art] = [
            n for n in parse_article_deps(path) if n != art and n in files
        ]
    seeds = sorted(
        a for a in files if a.startswith("YELLOW") or a.startswith("WAYBEL")
    )
    used: set[str] = set()
    stack = list(seeds)
    while stack:
        art = stack.pop()
        if art in used:
            continue
        used.add(art)
        stack.extend(d for d in graph[art] if d not in used)
    lar = [
        ln.strip().upper()
        for ln in LAR_PATH.read_text(encoding="utf-8").splitlines()
        if ln.strip()
    ]
    order = [a for a in ("TARSKI",) if a in used]
    order += [a for a in lar if a in used and a != "TARSKI"]
    pos = {a: i for i, a in enumerate(order)}
    lines = [
        "# MizarCCL translation queue.",
        "#",
        "# Full Mizar 7.13.01 / MML 4.181.1147 is vendored at vendor/MML",
        f"# (git submodule, rev {PIN}).",
        "# This file is the used-module closure of the 58 YELLOW* / WAYBEL*",
        "# articles, ordered least-dependent → most-dependent.",
        "#",
        "# An article A is used if it is a YELLOW*/WAYBEL* seed or appears in",
        "# another used article's environ under notations, constructors,",
        "# registrations, definitions, equalities, expansions, theorems, or",
        "# schemes. vocabularies (symbol lexicons) and requirements (BOOLE,",
        "# SUBSET, ...) are omitted; they are not article proofs.",
        "# TARSKI is the axiomatic root and is not listed in mml.lar; it is",
        "# placed first. Remaining articles follow vendor/MML/mml.lar.",
        "#",
        "# Palomar headlines: one key theorem per YELLOW*/WAYBEL* article.",
        "# Translate every article in translation_order, not only the seeds.",
        "#",
        "source: vendor/MML",
        f"mml_revision: {PIN}",
        "mizar_version: 7.13.01",
        "mml_version: 4.181.1147",
        f"seed_count: {len(seeds)}",
        f"used_count: {len(order)}",
        "order: least-dependent-first",
        "palomar_seeds:",
    ]
    for seed in seeds:
        lines.append(f"  - {seed}")
    lines.append("translation_order:")
    for i, art in enumerate(order, 1):
        deps = [d for d in graph[art] if d in used]
        lines.append(f"  - name: {art}")
        lines.append(f"    file: vendor/MML/mml/{art.lower()}.miz")
        lines.append(f"    role: {'seed' if art in set(seeds) else 'used'}")
        lines.append(f"    index: {i}")
        if not deps:
            lines.append("    depends_on: []")
        else:
            lines.append("    depends_on:")
            for dep in sorted(deps, key=lambda x: pos[x]):
                lines.append(f"      - {dep}")
    OUT.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"wrote {OUT} ({len(order)} articles, {len(seeds)} seeds)")


if __name__ == "__main__":
    main()
