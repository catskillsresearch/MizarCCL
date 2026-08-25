# Handoff — MizarCCL

1–1 Lean 4 translation of the Mizar articles used by the YELLOW* /
WAYBEL* family. GitHub: `catskillsresearch/MizarCCL`. Vendored Mizar:
`vendor/MML`. Queue: `mizarccl_translation_order.yaml`.

The earlier idiomatic `YELLOW_17` Palomar extract (Mathlib Tychonoff)
is abandoned. Do not submit that kit.

## Resume Protocol (read this first)

1. Read this `HANDOFF.md`.
2. Init the vendor: `git submodule update --init --recursive`.
   Confirm `vendor/MML` is `047822c4d814630b28eec8ca6b455e9eb912d5ff`.
3. Read `vendor/README.md` and `mizarccl_translation_order.yaml`.
4. Translate the next unused article in `translation_order` 1–1
   (not Mathlib-paraphrase). Palomar headlines come later: one key
   theorem per YELLOW*/WAYBEL* seed.
5. Old `arxiv.md` / `Yellow17.lean` / Challenge–Solution are the
   abandoned extract; do not extend them.

## Current status (2026-08-25)

- Repo renamed: `catskillsresearch/yellow17` →
  `catskillsresearch/MizarCCL` (via a brief `LeanMizar` name).
- Full Mizar 7.13.01 / MML 4.181.1147 vendored at `vendor/MML`
  (`047822c4d814630b28eec8ca6b455e9eb912d5ff`).
- Used-module queue: **368** articles (58 YELLOW*/WAYBEL* seeds).
  First: `TARSKI`. First seed: `YELLOW_0` (index 232). `YELLOW17` is
  index 362. Last: `WAYBEL35`. Same closure is in
  `waybel_yellow_dependencies.yaml` (10280 direct environ edges).
- No 1–1 Lean translation has started. Abandon the Palomar
  `yellow17` submission.

## On finishing a work item

1. `lake build` green; Solution sources have zero `sorry`; axiom audit
   of compared theorems ⊆ `{propext, Classical.choice, Quot.sound}`.
2. Challenge/Solution types match (`compare_challenge_solution_types.sh`).
3. Append a dated checkpoint below; update status lines above.
4. Update the corresponding section / catalog row in `arxiv.md`.
   In Markdown tables, escape literal `|` as `\|`.

## Context-cost hygiene

- Filter shell output (`| grep -vE 'LEAN_PATH|trace:' | tail`).
- Prefer appending to the end of this file over rewriting its middle.
- Never read `arxiv_with_code.md` (PDF-pipeline artifact).

## Choice discipline

Data constructions should stay choice-free when possible. Compactness /
Tychonoff may use `Classical.choice`; call it out in the proof note.

---

## Checkpoints

### 2026-08-25 — Palomar/arxiv extract

- Created this repository from the `scott_models` Palomar kit pattern.
- Copied `mml/yellow17.miz` from `MizarSystem/MML` at
  `047822c4d814630b28eec8ca6b455e9eb912d5ff`.
- `Challenge.lean` / `comparator.json` list all 24 `Yellow17` theorems and
  both definitions. `Solution.lean` imports `Yellow17`.
- `lake build` green. `scripts/palomar_preflight.sh` passed: Challenge /
  Solution types match; Solution has no `sorry`; compared theorems use
  only `{propext, Classical.choice, Quot.sound}`.
- `scripts/build_arxiv_pdf.sh` wrote `arxiv.pdf` / `view.pdf` (9 pages,
  fonts embedded).
- Git remote already set: `https://github.com/catskillsresearch/yellow17.git`
  (no commits yet).

### 2026-08-25 — `arxiv.md` inventory + Compendium

- Expanded `arxiv.md` with the translation-session Mizar inventory
  (FM `(1)`–`(24)` vs `Th1`–`Th22` / `Lm1` / `ElProductEx` / Tichonov)
  and the completeness notes (merged wrappers; headline via Mathlib).
- Bibliographic tie: Gierz et al., *A Compendium of Continuous Lattices*
  (1980), **§III-1** (Lawson compactness via Tychonoff) and
  **§VI-2–VI-3** (compact semilattices / fundamental theorem).
  Also listed in `formalization.yaml` as background.

### 2026-08-25 — waybel/yellow environ graph

- Parsed `environ` in all 58 `yellow*.miz` / `waybel*.miz` files under
  `../MML/mml`.
- Wrote `waybel_yellow_dependencies.yaml`: union of environ article
  names, restricted to the YELLOW*/WAYBEL* family (requirements and
  self-vocabulary dropped). Articles ordered least-dependent →
  most-dependent (58 nodes, 704 edges). Roots: `YELLOW_0`, `YELLOW18`.
  Sink: `WAYBEL33` (47 transitive family deps). `YELLOW17` depends on
  `YELLOW_1`, `WAYBEL_3`, `YELLOW_6`, `WAYBEL_7`, `WAYBEL18`.
- Wrote `waybel_yellow_dependencies.mmd` (Mermaid `flowchart TB`;
  `A --> B` means A depends on B).

### 2026-08-25 — Palomar license SPDX

- Palomar rejected `project.license` because `CC-BY-SA-3.0-or-later`
  is not an SPDX identifier. Aligned the machine-readable license with
  Mizar’s dual grant as `GPL-3.0-or-later OR CC-BY-SA-3.0` in
  `formalization.yaml` and `LICENSE`.

### 2026-08-25 — LeanMizar rename + vendor MML

- Renamed GitHub repo to
  https://github.com/catskillsresearch/LeanMizar
  (old `yellow17` URL redirects). Local folder is still
  `Desktop/yellow17`.
- Added submodule `vendor/MML` at
  `047822c4d814630b28eec8ca6b455e9eb912d5ff` (1153 articles +
  processor).
- Built `leanmizar_translation_order.yaml`: environ closure of 58
  YELLOW*/WAYBEL* seeds, excluding vocabularies/requirements, ordered
  by `mml.lar` with `TARSKI` first (368 articles, 0 forward edges).
  `YELLOW17` alone closes to 233 articles. Regenerator:
  `scripts/leanmizar_translation_order.py`.
- Palomar plan: key theorem per seed after the 1–1 prefix exists.
  Do not resubmit the idiomatic `YELLOW_17` kit.

### 2026-08-25 — Rename to MizarCCL

- Renamed GitHub repo again:
  https://github.com/catskillsresearch/MizarCCL
  (`yellow17` and `LeanMizar` URLs redirect). Local folder renamed to
  `Desktop/MizarCCL`.
- Queue files are now `mizarccl_translation_order.yaml` and
  `scripts/mizarccl_translation_order.py`.

### 2026-08-25 — Full WAYBEL/YELLOW environ closure YAML

- Replaced the intra-family-only `waybel_yellow_dependencies.yaml`
  (58 YELLOW*/WAYBEL* nodes) with the transitive environ closure
  rooted at those 58 seeds: **368** articles under `vendor/MML/mml`,
  least-dependent → most-dependent (`TARSKI` first, then `mml.lar`),
  10280 direct edges, 0 forward edges. Unreached MML articles are
  omitted. Same used-set as `mizarccl_translation_order.yaml`.
