#!/usr/bin/env python3
"""Deterministic editorial pre-checks before Palomar LLM audit."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    yaml = None  # type: ignore[assignment]

ROOT = Path(__file__).resolve().parent.parent

AI_NAME_PATTERNS = re.compile(
    r"(?i)\b("
    r"gpt[-\s]?\d|claude|codex|openai|anthropic|chatgpt|"
    r"auto[-\s]?review|language model|llm|cursor agent|"
    r"copilot|gemini|deepseek"
    r")\b"
)

DOCSTRING_BEFORE_DECL = re.compile(
    r"/--[\s\S]*?-/\s*\n\s*(?:@[^\n]+\n\s*)*(?:theorem|def)\s+(\w+)",
    re.MULTILINE,
)


def load_formalization(path: Path) -> dict:
    if yaml is None:
        raise SystemExit("PyYAML is required: pip install pyyaml")
    text = path.read_text(encoding="utf-8")
    doc = yaml.safe_load(text)
    if not isinstance(doc, dict):
        raise SystemExit(f"{path} must contain one top-level mapping")
    return doc


def load_comparator(path: Path) -> dict:
    with path.open(encoding="utf-8") as f:
        return json.load(f)


def check_human_only(names: list[str], field: str) -> list[str]:
    errors: list[str] = []
    for name in names:
        if not isinstance(name, str) or not name.strip():
            errors.append(f"{field} contains empty name")
        elif AI_NAME_PATTERNS.search(name):
            errors.append(f"{field} must name humans only; suspicious entry: {name!r}")
    return errors


def check_license(formalization: dict) -> list[str]:
    errors: list[str] = []
    declared = formalization.get("project", {}).get("license")
    licence_files = list(ROOT.glob("LICENSE*")) + list(ROOT.glob("Licence*"))
    if not licence_files:
        errors.append("missing root licence file")
        return errors
    if declared != "Apache-2.0":
        errors.append(f"project.license must be Apache-2.0, got {declared!r}")
    return errors


def check_required_fields(formalization: dict) -> list[str]:
    errors: list[str] = []
    if formalization.get("version") != "v0.4":
        errors.append(f"formalization.yaml version must be v0.4, got {formalization.get('version')!r}")
    project = formalization.get("project", {})
    for key in ("name", "description", "authors", "license", "responsible_maintainers"):
        if key not in project:
            errors.append(f"missing project.{key}")
    desc = project.get("description", "")
    if not isinstance(desc, str) or not desc.strip():
        errors.append("project.description must be nonempty")
    classification = formalization.get("classification", {})
    arxiv = classification.get("arxiv")
    if not isinstance(arxiv, list) or not arxiv:
        errors.append("classification.arxiv must be a nonempty list")
    automation = formalization.get("automation", {})
    methods = automation.get("methods")
    if not isinstance(methods, list) or not methods:
        errors.append("automation.methods must be a nonempty list")
    review = formalization.get("review", {})
    if not review.get("status"):
        errors.append("review.status must be nonempty")
    sources = formalization.get("sources")
    if not isinstance(sources, list) or not sources:
        errors.append("sources must be a nonempty list")
    return errors


def comparator_declarations(cfg: dict) -> list[str]:
    return list(cfg.get("theorem_names", [])) + list(cfg.get("definition_names", []))


def short_name(full: str) -> str:
    return full.split(".")[-1]


def check_main_results(formalization: dict, cfg: dict) -> list[str]:
    errors: list[str] = []
    compared = set(comparator_declarations(cfg))
    for entry in formalization.get("status", {}).get("main_results", []) or []:
        decl = entry.get("declaration")
        if decl and decl not in compared:
            errors.append(f"main_results declaration {decl!r} not in comparator.json")
    return errors


def check_alignment(formalization: dict, challenge_text: str) -> list[str]:
    errors: list[str] = []
    for entry in formalization.get("alignment", {}).get("statements", []) or []:
        lean = entry.get("lean")
        if lean and lean not in challenge_text:
            errors.append(f"alignment statement lean name {lean!r} not found in Challenge.lean")
    return errors


def challenge_docstrings(challenge_text: str) -> set[str]:
    return set(DOCSTRING_BEFORE_DECL.findall(challenge_text))


def narrative_before_decl(challenge_text: str, name: str) -> bool:
    if name in challenge_docstrings(challenge_text):
        return True
    pattern = re.compile(
        rf"(?:/--[\s\S]*?-/|/-![\s\S]*?-/)\s*\n(?:[^\n]*\n){{0,8}}\s*(?:theorem|def)\s+{re.escape(name)}\b",
        re.MULTILINE,
    )
    return pattern.search(challenge_text) is not None


def check_docstrings(cfg: dict, challenge_text: str) -> list[str]:
    """Require auditable docstrings on lift-related compared declarations."""
    errors: list[str] = []
    required = ["ulift", "ulift_eq_iff", "ulift_mem_iff", "th3"]
    for name in required:
        if not narrative_before_decl(challenge_text, name):
            errors.append(
                f"compared declaration TARSKI.{name} lacks narrative/docstring in Challenge.lean"
            )
    return errors


def check_scaffold_disclaimers(formalization: dict) -> list[str]:
    errors: list[str] = []
    scope = str(formalization.get("status", {}).get("scope", ""))
    if "deferred" in scope.lower() or "scaffold" in scope.lower():
        combined = scope
        for key in ("known_gaps", "limitations"):
            for item in formalization.get(key, []) or []:
                combined += " " + str(item)
        if "research-interest" not in combined.lower() and "notability" not in combined.lower():
            errors.append(
                "deferred/scaffold scope should mention research-interest or notability limits"
            )
    return errors


def main() -> int:
    formalization_path = ROOT / "formalization.yaml"
    comparator_path = ROOT / "comparator.json"
    challenge_path = ROOT / "Challenge.lean"

    formalization = load_formalization(formalization_path)
    cfg = load_comparator(comparator_path)
    challenge_text = challenge_path.read_text(encoding="utf-8")

    errors: list[str] = []
    errors.extend(check_required_fields(formalization))
    errors.extend(
        check_human_only(formalization.get("project", {}).get("authors", []), "project.authors")
    )
    errors.extend(
        check_human_only(
            formalization.get("project", {}).get("responsible_maintainers", []),
            "project.responsible_maintainers",
        )
    )
    errors.extend(check_license(formalization))
    errors.extend(check_main_results(formalization, cfg))
    errors.extend(check_alignment(formalization, challenge_text))
    errors.extend(check_docstrings(cfg, challenge_text))
    errors.extend(check_scaffold_disclaimers(formalization))

    if errors:
        print("FAIL: editorial pre-checks:")
        for err in errors:
            print(f"  {err}")
        return 1

    print(
        f"OK: editorial pre-checks passed "
        f"({len(comparator_declarations(cfg))} compared declarations)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
