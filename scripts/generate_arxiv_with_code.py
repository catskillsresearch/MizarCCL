#!/usr/bin/env python3
"""Append complete Lean source to arxiv.md → arxiv_with_code.md (build artifact)."""

from __future__ import annotations

from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

FILE_ROLES: dict[str, str] = {
    "MizarCCL/HIDDEN.lean": "Mizar HIDDEN (TarskiSet, membership)",
    "MizarCCL/TARSKI.lean": "Mizar TARSKI translation (proofs)",
}


def paper_title(arxiv_text: str) -> str:
    first = arxiv_text.splitlines()[0] if arxiv_text else "# TARSKI"
    if first.startswith("# "):
        return first[2:].strip()
    return first.strip()


def narrative_body(arxiv_text: str) -> str:
    body = arxiv_text
    if body.startswith("# "):
        idx = body.find("\n---\n")
        if idx != -1:
            body = body[idx + len("\n---\n") :]
        else:
            body = body[body.find("\n") + 1 :]
    return body.rstrip()


def strip_lean_code_section(body: str) -> str:
    markers = ("\n## Lean Code\n", "\n## Lean Code\r\n")
    for marker in markers:
        idx = body.find(marker)
        if idx != -1:
            return body[:idx].rstrip() + "\n"
    if body.startswith("## Lean Code\n"):
        return ""
    return body


def lean_files_from_root() -> list[str]:
    return ["MizarCCL/HIDDEN.lean", "MizarCCL/TARSKI.lean"]


def sanitize_fence_content(content: str) -> str:
    return content.replace("```", "'''")


def role_for(path: str) -> str:
    return FILE_ROLES.get(path, Path(path).stem)


def main() -> None:
    arxiv_path = ROOT / "arxiv.md"
    arxiv = arxiv_path.read_text(encoding="utf-8")
    title = paper_title(arxiv)
    body = strip_lean_code_section(narrative_body(arxiv))
    files = lean_files_from_root()

    total_lines = 0
    file_line_counts: list[tuple[str, int]] = []
    for f in files:
        n = len((ROOT / f).read_text(encoding="utf-8").splitlines())
        file_line_counts.append((f, n))
        total_lines += n

    parts: list[str] = []
    parts.append(
        "<!-- AUTO-GENERATED: run scripts/generate_arxiv_with_code.sh to refresh -->\n"
        "<!-- AGENTS: do not read or grep this file. Use arxiv.md; see .cursorignore -->\n"
    )
    parts.append(f"# {title} — full narrative + complete Lean source\n\n")
    parts.append(
        "> **Generated artifact — not for agents.** Inventory and narrative live in "
        "[`arxiv.md`](arxiv.md). Regenerate with `scripts/generate_arxiv_with_code.sh`.\n\n"
    )
    parts.append(
        f"*Generated {date.today().isoformat()} from `arxiv.md` and {len(files)} library "
        f"`.lean` files ({total_lines} lines).*\n\n"
    )
    parts.append("---\n\n")
    parts.append("# Narrative + Lean source (from arxiv.md)\n\n")
    parts.append(body)
    parts.append("\n\n---\n\n")
    parts.append("# Appendix A: Complete Lean source\n\n")
    parts.append("| Role | File | Lines |\n")
    parts.append("| --- | --- | ---: |\n")
    for f, n in file_line_counts:
        parts.append(f"| {role_for(f)} | `{f}` | {n} |\n")
    parts.append(
        f"\n**Total:** {len(files)} files, {total_lines} lines of Lean.\n\n"
    )

    for f, n in file_line_counts:
        content = sanitize_fence_content((ROOT / f).read_text(encoding="utf-8").rstrip()) + "\n"
        parts.append(f"## `{f}`\n\n")
        parts.append(f"*{n} lines.*\n\n")
        parts.append("```lean\n")
        parts.append(content)
        parts.append("```\n\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts), encoding="utf-8")
    print(f"Wrote {out} ({len(out.read_text(encoding='utf-8').splitlines())} lines)")


if __name__ == "__main__":
    main()
