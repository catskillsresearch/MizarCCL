#!/usr/bin/env python3
"""Concatenate the MizarCCL translation_order articles into one .miz file.

Reads ``translation_order`` from ``mizarccl_translation_order.yaml`` and
writes ``waybel_yellow.miz``. Each article is preceded by

    :: Module <STEM>

where ``<STEM>`` is the source filename root in uppercase
(``vendor/mml/tarski.miz`` → ``TARSKI``).
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_YAML = ROOT / "mizarccl_translation_order.yaml"
DEFAULT_OUT = ROOT / "waybel_yellow.miz"


def load_translation_order_files(yaml_path: Path) -> list[Path]:
    """Return repo-relative article paths in ``translation_order`` order.

    The queue YAML is hand-written and this repo does not depend on PyYAML,
    so only the ``- name:`` / ``file:`` pairs under ``translation_order``
    are scanned.
    """
    in_order = False
    files: list[Path] = []
    pending_name: str | None = None

    for raw in yaml_path.read_text(encoding="utf-8").splitlines():
        if not in_order:
            if raw.startswith("translation_order:"):
                in_order = True
            continue
        if raw and not raw[0].isspace() and not raw.startswith("#"):
            break
        stripped = raw.strip()
        if stripped.startswith("- name:"):
            pending_name = stripped.split(":", 1)[1].strip()
            continue
        if stripped.startswith("file:") and pending_name is not None:
            rel = stripped.split(":", 1)[1].strip()
            files.append(Path(rel))
            pending_name = None

    if pending_name is not None:
        raise SystemExit(
            f"{yaml_path}: article {pending_name!r} has no file: entry"
        )
    if not files:
        raise SystemExit(f"{yaml_path}: translation_order is empty")
    return files


def module_banner(article_path: Path) -> str:
    return f":: Module {article_path.stem.upper()}"


def concatenate(articles: list[Path], repo_root: Path) -> str:
    chunks: list[str] = []
    missing: list[Path] = []
    for rel in articles:
        src = repo_root / rel
        if not src.is_file():
            missing.append(rel)
            continue
        body = src.read_text(encoding="utf-8")
        if body and not body.endswith("\n"):
            body += "\n"
        chunks.append(f"{module_banner(rel)}\n{body}")
    if missing:
        listing = "\n".join(f"  {p}" for p in missing)
        raise SystemExit(f"missing {len(missing)} article(s):\n{listing}")
    return "".join(chunks)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--yaml",
        type=Path,
        default=DEFAULT_YAML,
        help="queue YAML (default: repo mizarccl_translation_order.yaml)",
    )
    parser.add_argument(
        "--output",
        "-o",
        type=Path,
        default=DEFAULT_OUT,
        help="destination .miz (default: repo waybel_yellow.miz)",
    )
    args = parser.parse_args(argv)

    yaml_path = args.yaml if args.yaml.is_absolute() else ROOT / args.yaml
    out_path = args.output if args.output.is_absolute() else ROOT / args.output

    articles = load_translation_order_files(yaml_path)
    text = concatenate(articles, ROOT)
    out_path.write_text(text, encoding="utf-8")
    print(f"wrote {out_path} ({len(articles)} articles, {len(text)} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
