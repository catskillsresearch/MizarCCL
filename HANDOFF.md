# Handoff — MizarCCL

1–1 Lean 4 translation of the Mizar articles used by the YELLOW* /
WAYBEL* family. GitHub: `catskillsresearch/MizarCCL`. Vendored Mizar:
`vendor/MML`. Queue: `mizarccl_translation_order.yaml`.

The earlier idiomatic `YELLOW_17` Palomar extract (Mathlib Tychonoff)
is abandoned. Do not submit that kit.

## Resume Protocol (read this first)

1. Read this `HANDOFF.md`.
2. Confirm `vendor/MML_PIN` is `047822c4d814630b28eec8ca6b455e9eb912d5ff`
   and `vendor/mml/` has `hidden.miz` plus the 368 queue articles.
   There is no git submodule. An optional full clone may live at
   gitignored `vendor/MML`.
3. Read `vendor/README.md` and `mizarccl_translation_order.yaml`.
4. Translate the next unused article in `translation_order` 1–1
   (not Mathlib-paraphrase). Palomar headlines come later: one key
   theorem per YELLOW*/WAYBEL* seed.
5. Palomar surface is now TARSKI (`Challenge.lean` / `Solution.lean`).
   The old YELLOW_17 extract is gone; do not restore it.

## Current status (2026-08-27)

- Repo renamed: `catskillsresearch/yellow17` →
  `catskillsresearch/MizarCCL` (via a brief `LeanMizar` name).
- Used Mizar slice (no submodule): `vendor/mml/` has `hidden.miz`
  plus the 368 queue articles at pin
  `047822c4d814630b28eec8ca6b455e9eb912d5ff` (`vendor/MML_PIN`).
- Used-module queue: **368** articles (58 YELLOW*/WAYBEL* seeds).
  First: `TARSKI`. First seed: `YELLOW_0` (index 232). `YELLOW17` is
  index 362. Last: `WAYBEL35`. Same closure is in
  `waybel_yellow_dependencies.yaml` (10280 direct environ edges).
- 1–1 Lean package `MizarCCL` started. `lake build` default is
  `MizarCCL` (no Mathlib). Root `MizarCCL.lean` imports translated
  articles. First article: `TARSKI` (`MizarCCL/TARSKI.lean`), with
  `HIDDEN` defining `TarskiSet` (Aczel quotient; no `axiom`/`sorry`).
  Next unused: `XREGULAR`. Palomar Challenge/Solution expose TARSKI.

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

### 2026-08-25 — Drop leftover top-level `mml/`

- Removed Palomar-era `mml/yellow17.miz` and `mml/FROZEN.txt`. The
  library lives only at `vendor/MML`. Retargeted `PROVENANCE.md`,
  `formalization.yaml`, `arxiv.md`, and `scripts/palomar_preflight.sh`
  to the submodule pin.

### 2026-08-25 — `MizarCCL` package + TARSKI

- Retargeted Lake to library `MizarCCL` (dropped Mathlib / Yellow17 /
  Challenge / Solution as default targets).
- `MizarCCL/HIDDEN.lean`: Mizar built-ins `set` and `∈` (`mizarMem`).
- `MizarCCL/TARSKI.lean`: 1–1 of `vendor/MML/mml/tarski.miz`.
  Axioms: extensionality, singleton, upair, union, regularity,
  Fraenkel, Tarski–Grothendieck. Definitions: `⊆`, Kuratowski `pair`,
  `are_equipotent`. Proved: `upair_comm`, `subset_refl`.
  `#print axioms` of proved theorems ⊆ those constructors plus
  `{set, mizarMem}`; no `Classical.choice`.
- `MizarCCL.lean` imports HIDDEN and TARSKI. `lake build` green.

### 2026-08-25 — HIDDEN/`TarskiSet` without `axiom`

- `MizarCCL/HIDDEN.lean` no longer posts `axiom set` / `axiom mizarMem`.
  `TarskiSet.{u}` is `Quotient` of Aczel `PreSet.{u}` by extensional
  `Equiv`. Membership is defined. `set` is not a synonym for `Type`.
- `MizarCCL/TARSKI.lean` proves the article over that model: `th1`–
  `def 6`, `sch 1`, regularity, union. `th3` is universe-polymorphic:
  `universeSet : TarskiSet.{u+1}` contains every `ulift X`, and is
  closed under subsets (`subset_of_mem_universe`). Full Mizar (iii)
  power-set witness and (iv) inaccessibility are not theorems of
  `Type u`.
- No `axiom` / `admit` / `sorry` in `MizarCCL/`. `#print axioms` of
  public theorems ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice only in regularity / Fraenkel). `lake build` green.

### 2026-08-25 — Palomar surface for TARSKI

- Retargeted Challenge / Solution / `comparator.json` /
  `formalization.yaml` / `arxiv.md` from the abandoned YELLOW_17
  extract to the 12 Mizar-labelled TARSKI theorems (`th1`–`th3`,
  `def1`–`def6`, `sch1`, `upair_comm`, `subset_refl`) and 7
  constructors. `Solution.lean` imports `MizarCCL.TARSKI`.
- Lake default targets include `MizarCCL`, `Challenge`, `Solution`.
- Named `TARSKI.instHasSubset` so Challenge/Solution types match
  under `pp.explicit`.
- `scripts/palomar_preflight.sh` passed: types match; Solution /
  `MizarCCL/*.lean` have no `sorry`; axioms ⊆
  `{propext, Classical.choice, Quot.sound}`.

### 2026-08-25 — Palomar-safe used-module vendor

- Removed the `vendor/MML` git submodule (Palomar cannot preserve
  submodules). Checked in `vendor/mml/` as ordinary files:
  `hidden.miz` plus the 368 queue articles. Pin in `vendor/MML_PIN`.
- `formalization.yaml` cites Trybulec `TARSKI` with relationship
  `adapts` (universe-polymorphic `TARSKI:3`). Dropped the
  self-notes `other` source.
- Optional full MML clone stays at gitignored `vendor/MML` for
  queue regeneration only.

### 2026-08-25 — Apache-2.0 for Palomar

- Palomar could not repair the dual SPDX
  `GPL-3.0-or-later OR CC-BY-SA-3.0`. Root `LICENSE` is now the
  Apache-2.0 text from `scott_models`; `project.license` is
  `Apache-2.0`. Vendored `.miz` files keep the AMU notices.

### 2026-08-25 — Challenge compiles without Lake

- Palomar runs `lean Challenge.lean` with only the stdlib path, so
  `import MizarCCL.HIDDEN` failed. `Challenge.lean` is now Init-only.
  Shared carriers are copied verbatim from `HIDDEN.lean` (not
  `sorry`); Palomar Comparator rejects extra constants whose values
  differ (`PreSet.instSetoid`). `compare_challenge_solution_types.sh`
  `#print`s those shared names. Named `instMembership` in HIDDEN.

### 2026-08-25 — `TARSKI.instHasSubset` matches Solution

- Challenge `subset` is the real predicate `∀ x, x ∈ X → x ∈ Y`, not
  `sorry`, so `instHasSubset` agrees with `MizarCCL/TARSKI.lean`.
  Preflight `#print`s `TARSKI.subset` and `TARSKI.instHasSubset`.

### 2026-08-26 — Kuratowski injectivity and simp lemmas

- Marked `singleton_iff`, `upair_iff`, and `union_iff` `@[simp]`.
- Added `pair_inj`: `[x₁,y₁] = [x₂,y₂] ↔ x₁ = x₂ ∧ y₁ = y₂`.

### 2026-08-27 — Single-file Mizar payload

- `scripts/build_waybel_yellow_miz.py` concatenates
  `translation_order` from `mizarccl_translation_order.yaml` into
  `waybel_yellow.miz`. Each article is preceded by
  `:: Module <STEM>` (filename root in caps). `hidden.miz` is not
  on the queue and is omitted.

### 2026-08-27 — XBOOLE_0 and XBOOLE_1

- `MizarCCL/XBOOLE_0.lean`: Separation from `TARSKI:sch 1`, empty
  set, `∪` `∩` `\`, `∆`, `misses`/`meets`, `⊂`, `c=`-comparable,
  equality via double inclusion, `th1`–`th7`, registrations.
  Environ import is `TARSKI` only. Mathlib is not used: these
  constructors live on untyped `TarskiSet`, not `Set α`.
- `MizarCCL/XBOOLE_1.lean`: `th1`–`th117` plus `Lm1`–`Lm5`,
  following the Mizar article (membership via `def 3`–`def 5`,
  inclusion, extensionality). Environ imports `TARSKI` and
  `XBOOLE_0`.
- No `sorry` / `axiom` in `MizarCCL/`. `#print axioms` of sampled
  theorems ⊆ `{propext, Classical.choice, Quot.sound}`. `lake build`
  green. Challenge/Solution types still match (Palomar remains
  TARSKI). Next unused: `ENUMSET1`.

### 2026-08-27 — ENUMSET1

- `MizarCCL/ENUMSET1.lean`: `enumset3`–`enumset10` as
  `union(upair(prefix, singleton last))`, `def1`–`def8`, `th1`–`th87`,
  `lm1`–`lm9`. Membership lemmas use `lm1` plus a local `or_assoc`
  (Lean 4.33 Init has no `Or.assoc`). No Lean insert notation.
  Environ: `TARSKI`, `XBOOLE_0`, `XBOOLE_1`. Do not `open XBOOLE_0`
  (shadows union/diff).
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (`th86` uses choice via difference). No `sorry`.

### 2026-08-27 — XTUPLE_0

- `MizarCCL/XTUPLE_0.lean`: pair attribute `isPair`, `fst`/`snd`,
  `triple`/`quadruple` and their projections, `proj1`/`proj2` and
  3-/4-place set projections, Boolean identities `th22`–`th45`.
  Kuratowski injectivity is `th1` (from `TARSKI.pair_inj`). `proj1`
  is Separation on `union (union X)` as in `Pre1`/`Def4`. Duplicate
  Mizar labels `Th32`/`Th34`/`Th36` (quadruples) are `th40`/`th42`/`th44`.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from `fst`/`proj1`). `lake build` green. Challenge/Solution
  types still match. Next unused: `XREGULAR`.
