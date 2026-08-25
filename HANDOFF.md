# Handoff — yellow17 (Mizar `YELLOW_17` / Palomar)

Lean 4 translation of Bartłomiej Skorulski, *The Tichonov Theorem*.
Library: `Yellow17`. Inventory: `arxiv.md`. Palomar kit: `Challenge.lean`,
`Solution.lean`, `comparator.json`, `formalization.yaml`.

## Resume Protocol (read this first)

1. Read this `HANDOFF.md`.
2. Read `arxiv.md` (this article: translation notes, catalog, axioms).
3. Mizar source and pin: `yellow17.miz`, `mml/FROZEN.txt`, `PROVENANCE.md`.
4. Build: `lake build` (filter: `| grep -vE 'LEAN_PATH|trace:' | tail`).
5. Palomar type check: `bash scripts/compare_challenge_solution_types.sh`.
   It `#check`s every `comparator.json` name from Challenge and from
   Solution with `pp.all` / `pp.explicit` and diffs.
6. Full preflight: `bash scripts/palomar_preflight.sh`.
7. PDF: `bash scripts/build_arxiv_pdf.sh` (writes `arxiv.pdf` / `view.pdf`).

## Current status (2026-08-25)

- `Yellow17.lean` sorry-free translation of `YELLOW_17`.
- Palomar Challenge restates every theorem and both definitions.
- Headline axioms: `{propext, Classical.choice, Quot.sound}`.
- MML copy pinned at `047822c4d814630b28eec8ca6b455e9eb912d5ff`.

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
