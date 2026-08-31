[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/MizarCCL/build.yml?label=Lean%204)](https://github.com/catskillsresearch/MizarCCL/actions/workflows/build.yml)

# MizarCCL

1–1 Lean 4 translation of the Mizar articles needed for the YELLOW* /
WAYBEL* family (continuous lattices / Way-below / Tychonoff). The
used-module slice of Mizar 7.13.01 / MML 4.181.1147 is vendored as
ordinary files (no git submodule).

This is **not** the earlier idiomatic Mathlib paraphrase of `YELLOW_17`.
That Palomar extract is abandoned: a faithful translation needs the
`environ` graph, not a headline file in isolation.

## Repository

- GitHub: https://github.com/catskillsresearch/MizarCCL
- Mizar pin: `047822c4d814630b28eec8ca6b455e9eb912d5ff`
  (Mizar 7.13.01 / MML 4.181.1147), in `vendor/MML_PIN`.
  Palomar vendors `hidden.miz` plus the 368-article used queue as
  ordinary files under `vendor/mml/` (no git submodule).
  See `vendor/README.md`.
- Translation queue: `mizarccl_translation_order.yaml`
  (368 used articles, least-dependent first; 58 YELLOW*/WAYBEL* seeds).
- Environ graph: `waybel_yellow_dependencies.yaml`
- Lean package: `MizarCCL` (`MizarCCL.lean` imports every translated
  article; first: `MizarCCL/TARSKI.lean`)

Palomar: **submission deferred** until all 368 queue articles are
translated. Until then, `Challenge.lean` / `Solution.lean` /
`comparator.json` are an experimental local Comparator/editorial-audit
surface and may change freely to test translated results. The current
experiment compares the TARSKI scaffold plus `SETWISEO:59`, the
finite-union homomorphism theorem. The TARSKI portion compares
`TARSKI.ulift_eq_iff` and `TARSKI.ulift_mem_iff`, making its
cross-universe lift an auditable equality and membership embedding
rather than an unspecified map. The scaffold remains foundational
and is not claimed to meet Palomar's research-interest threshold.
At submission, Comparator will compare **one capstone theorem per
seed** (58 YELLOW*/WAYBEL* files in `palomar_seeds` in
`mizarccl_translation_order.yaml`) — not full seed exports and not
per-prefix kits along the way. Packaging rules and workflow:
`docs/PALOMAR_EDITORIAL_AUDIT.md`. During translation use
`bash scripts/palomar_preflight.sh --mechanical-only` only.

## Setup

Same layout as sibling Palomar repos (`scott1982`, etc.): `lean-toolchain` pins
**v4.33.0** (shared elan cache under `~/.elan/toolchains/`), and `lakefile.toml`
defines the Lake package. Open this repository root in Cursor/VS Code — the
folder that contains `Challenge.lean` and `lean-toolchain`, not the inner
`MizarCCL/` library directory.

```bash
lake build
```

Optional full MML clone for regenerating the queue (gitignored):

```bash
git clone https://github.com/MizarSystem/MML.git vendor/MML
git -C vendor/MML checkout "$(cat vendor/MML_PIN)"
```

Rebuild the used-module queue:

```bash
python3 scripts/mizarccl_translation_order.py
```

## Palomar preflight

Mechanical Comparator checks plus **Cursor SDK editorial audit** using
vendored [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy)
prompts. See `docs/PALOMAR_EDITORIAL_AUDIT.md`.

```bash
# CI / translation (no API key):
bash scripts/palomar_preflight.sh --mechanical-only

# Full gate (CURSOR_API_KEY or ../tokens_ssto.yaml):
bash scripts/palomar_preflight.sh
```

Substantive editorial passes use **`gpt-5.6-sol`**; classification/metadata use
**`composer-2.5`**. Policy sync auto-updates `vendor/palomar-policy/` from upstream.
The interim TARSKI scaffold is expected to fail editorial notability until
capstone theorems are selected.

## License

The Lean package (`MizarCCL/`, Challenge, Solution) is **Apache-2.0**,
same as `scott_models`. See `LICENSE`.

Vendored Mizar articles in `vendor/mml/` remain © Association of
Mizar Users under **GPL-3.0-or-later** or **CC-BY-SA-3.0**
(`doc/COPYING.*` and the notices in each `.miz` file).
