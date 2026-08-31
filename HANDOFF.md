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
   (not Mathlib-paraphrase). See **Palomar submission policy** below;
   do not expand Challenge/Solution per article during translation.
5. `Challenge.lean` / `Solution.lean` / `comparator.json` are an interim
   TARSKI scaffold for local Comparator discipline only. The old
   YELLOW_17 extract is gone; do not restore it.
6. Palomar editorial audit: `docs/PALOMAR_EDITORIAL_AUDIT.md`.
   Vendored policy under `vendor/palomar-policy/`; full preflight uses
   `gpt-5.6-sol`. CI runs `--mechanical-only` until capstones exist.

## Palomar submission policy

**Defer Palomar registry validation/submission** until the full
used-module queue is translated:

- All **368** articles in `mizarccl_translation_order.yaml` have 1–1
  Lean modules under `MizarCCL/`, are imported from `MizarCCL.lean`,
  and `lake build` is green with zero `sorry` in `MizarCCL/`.

**At submission time**, Comparator compares **one capstone theorem per
seed** — the biggest or most representative headline from each of the
**58** YELLOW*/WAYBEL* seed files listed as `palomar_seeds` in the queue
YAML (`yellow_*.miz` / `waybel_*.miz`). Not every theorem in those
files, and not per-prefix Palomar kits along the way.

**Until then:**

- Continue sequential 1–1 article translation only.
- Keep the current TARSKI Challenge/Solution/comparator as a development
  scaffold; do **not** treat `scripts/palomar_preflight.sh` green as
  “submit now.”
- Finishing a queue article does **not** require updating Challenge,
  Solution, or `comparator.json` unless explicitly working on the
  capstone phase after the queue is complete.

## Current status (2026-08-31)

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
  Next unused: `FRAENKEL` (sequential). `SETWISEO`, `ORDERS_1`, `ORDINAL2` /
  `ORDINAL3`, `FINSET_1` / `FINSUB_1`, `WELLSET1`, and `PARTFUN2` are
  done, as are `MULTOP_1` / `FUNCT_4` / `FUNCT_3` / `SYSREL` /
  `FUNCOP_1`.
  Palomar Challenge/Solution/comparator: interim TARSKI scaffold only,
  currently 14 compared theorems and 7 definitions, including
  `ulift_eq_iff` / `ulift_mem_iff` (submission deferred; see Palomar
  submission policy). Full preflight now includes vendored PalomarPolicy
  sync + `gpt-5.6-sol` editorial audit (`docs/PALOMAR_EDITORIAL_AUDIT.md`);
  expect notability failure on the scaffold until capstones.

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

### 2026-08-27 — XREGULAR

- `MizarCCL/XREGULAR.lean`: `th1` (nonempty set has a disjoint
  element, from `TARSKI:2`), depth-1..5 chain forms `th2`–`th6`,
  and no 3–6 cycles `th7`–`th10`. Imports `ENUMSET1` only (no
  `XTUPLE_0`, matching the Mizar environ).
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
  `lake build` green. Challenge/Solution types still match. Next
  unused: `ZFMISC_1` (power set / products; ~2400 lines).

### 2026-08-27 — ZFMISC_1

- `MizarCCL/ZFMISC_1.lean`: `bool` as the Aczel family of subsets
  (`def1`), Cartesian `product` by Separation on
  `bool (bool (X ∪ Y))` (`def2`), 3-/4-fold products, `lm1`–`lm21`,
  `th1`–`th26` and `th28`–`th138` (`th27` canceled in Mizar).
  `isTrivial` is `def10`. `th112` is the universe of `TarskiSet.{u}`
  inside `{u+1}`, subset-closed; Mizar `bool`-closure and
  inaccessibility are not claimed (need `bool (ulift N) = ulift (bool N)`
  and `TARSKI:3`(iv)). Imports `XREGULAR` and `XTUPLE_0`.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from Separation / `product`). No `sorry`. `lake build`
  green. Challenge/Solution types still match. Next unused: `SUBSET_1`.

### 2026-08-27 — SUBSET_1

- `MizarCCL/SUBSET_1.lean`: `isElement` is membership when `X` is
  nonempty and emptiness when `X` is empty (`def1`); not a Lean
  subtype. `isSubset Y X` is `Y ⊆ X` (`Element of bool X`).
  `emptyOf` / `hash` / `compl` are `{}E`, `[#]E`, `A\``. `choose`
  is `the Element of S`. `isProper` is `A ≠ E`. Numbered `th1`–`th48`,
  `lm1`–`lm3`, schemes `sch_SubsetEx`, `sch_SubsetEq`,
  `sch_SubsetEx2`, `sch_SubComp`. Imports `ZFMISC_1` only.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from `∅` / `\` / `choose` / Separation). No `sorry`.
  `lake build` green. Challenge/Solution types still match. Next
  unused: `SETFAM_1`.

### 2026-08-27 — SETFAM_1

- `MizarCCL/SETFAM_1.lean`: `meet` by Separation on `union X`
  (`def1`); `isFiner` / `isCoarser`; pairwise `familyUnion` /
  `familyIntersection` / `familyDifference` (`def4`–`def6`) by
  Separation on a `bool` of unions; `isSubsetFamily` is
  `F ⊆ bool D`; `complement` via `SUBSET_1.sch_SubsetEx`;
  `Intersect` is `meet` if nonempty else the ambient set;
  `isCover`, `withNonemptyElements`, `isEmptyMembered`,
  `withProperSubsets`. Numbered `th1`–`th49`. Imports `SUBSET_1`
  only.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from Separation / `meet` / `∅`). No `sorry`. `lake build`
  green. Challenge/Solution types still match. Next unused: `RELAT_1`.

### 2026-08-27 — RELAT_1

- `MizarCCL/RELAT_1.lean`: relations as sets of Kuratowski pairs
  (`isRelation` / `def1`). `dom` / `rng` are `XTUPLE_0.proj1` /
  `proj2`; `field` is their union. `converse`, `comp`, `id`,
  `restrict`, `restrictRng`, `image`, `invimage`, `Im` / `Coim`.
  `isXdefined` / `isXvalued` (`def18`/`def19`); `isEmptyYielding`
  is Mizar `non-empty` (`def9`); `isEmptyYieldingSet` is
  empty-yielding (`def15`). Numbered `th1`–`th186` except canceled
  `4`–`6`, `116`–`117`, `136`–`137`. Schemes `sch_RelExistence`,
  `sch_ExtensionalityR`. Imports `SUBSET_1` only.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from Separation / `comp` / `id` / `restrict` / `image`).
  No `sorry`. `lake build` green. Challenge/Solution types still
  match. Next unused: `FUNCT_1`.

### 2026-08-27 — FUNCT_1

- `MizarCCL/FUNCT_1.lean`: a function is a function-like relation
  (`isFunction` / `def1`). Application `f.x` is `apply` (`def2`).
  Mizar `g*f` is `RELAT_1.comp f g` (apply `f` then `g`). Inverse
  of a one-to-one function is `converse`. Restriction, image, and
  inverse image are re-characterized via `apply`. `the_value_of`
  a nonempty constant; `isFunctional`; `isCompatible`. Numbered
  `th1`–`th111` except canceled `th30`. Schemes `sch_GraphFunc`,
  `sch_FuncEx`, `sch_Lambda`, `sch_LambdaB`,
  `sch_NonUniqBoundFuncEx`. Imports `RELAT_1` and `SETFAM_1`.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from `apply` / Separation / `the_value_of` / `th111`).
  No `sorry`. `lake build` green. Challenge/Solution types still
  match. Next unused: `GRFUNC_1`.

### 2026-08-27 — GRFUNC_1

- `MizarCCL/GRFUNC_1.lean`: a subset of a function is a function
  (`th1`). Graph characterizations of inclusion, singleton and
  two-point graphs, unions when domains miss or both sit in a
  function, restrictions, inverse of the empty function, and
  compatibility downward along subsets. Numbered `th1`–`th35`
  except canceled `th18`, `th19`. Locals `lm1`–`lm3`. Imports
  `FUNCT_1` and `ENUMSET1`.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from `apply` / Separation). No `sorry`. `lake build`
  green. Challenge/Solution types still match. Next unused:
  `RELAT_2`.

### 2026-08-27 — RELAT_2

- `MizarCCL/RELAT_2.lean`: reflexive / irreflexive / symmetric /
  antisymmetric / asymmetric / connected / strongly connected /
  transitive, both `in X` (`def1`–`def8`) and on `field R`
  (`def9`–`def16`). Official `th1`–`th4`, `th12`–`th13`, `th22`,
  `th27`–`th28`, `th30`–`th31`. Canceled `th5`–`th11`, `th14`–`th21`,
  `th23`–`th26`, `th29`. Registrations as helpers (`empty_is*`,
  `id_is*`, converse / union / inter / diff closures). Import is
  `RELAT_1` only.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from `id` / `converse` / Separation). No `sorry`.
  `lake build` green. Challenge/Solution types still match. Next
  unused: `ORDINAL1`.

### 2026-08-27 — ORDINAL1

- `MizarCCL/ORDINAL1.lean`: ordinals as epsilon-transitive
  epsilon-connected sets (`def4`). Successor, trichotomy, least
  ordinal, transfinite induction, limit ordinals, T-sequences,
  uniqueness/existence of transfinite recursion, `On` / `Lim` /
  `omega` / naturals. Numbered `th5`–`th37` except canceled
  `th1`–`th4`. Schemes `sch_OrdinalMin`, `sch_TransfiniteInd`,
  `sch_TSUniq`, `sch_TSExist`, `sch_FuncTS`, `sch_ALFA`. `th36`
  builds a limit above an ordinal via a `Nat`-indexed successor
  chain (Lean model; Mizar uses universe bool-closure). Imports
  `FUNCT_1` and `XREGULAR`.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from Separation / `apply` / `omega` / `On`). No `sorry`.
  `lake build` green. Challenge/Solution types still match. Next
  unused: `WELLORD1`.

### 2026-08-27 — WELLORD1

- `MizarCCL/WELLORD1.lean`: well-orderings, initial segments
  (`R-Seg`), `|_2` restriction, transfinite induction, order
  isomorphisms, and comparability of well-orders (`th52`).
  Locals `lm1`–`lm5`. Numbered `th1`–`th54` (`th38` / `th53` /
  `th54` unlabeled). Defs `seg` / well-founded / well-ordering /
  `restrict2` / isomorphism / `areIsomorphic` /
  `canonical_isomorphism_of`. Imports `FUNCT_1` and `RELAT_2`.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from `apply` / Separation / `canonical_isomorphism_of`).
  No `sorry`. `lake build` green. Challenge/Solution types still
  match. Next unused: `RELSET_1`.

### 2026-08-27 — RELSET_1

- `MizarCCL/RELSET_1.lean`: `Relation of X,Y` as a subset of
  `[:X,Y:]` (`isRelationOf`). Domain/range/field, converse,
  composition, restriction, image/invimage, identity, and
  schemes `sch_RelOnSetEx` / `sch_RelOnDomEx` / `sch_ImEx` /
  `sch_RelEq`. Numbered `th1`–`th32` (`Th13`, `Th15`, `Th22`
  labeled). Import is `RELAT_1` only.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from `id` / `restrict` / Separation). No `sorry`.
  `lake build` green. Challenge/Solution types still match. Next
  unused: `PARTFUN1`.

### 2026-08-27 — PARTFUN1

- `MizarCCL/PARTFUN1.lean`: partial functions as Function ∧
  `Relation of X,Y`. Clip `<:f,X,Y:>`, totals, `PFuncs`,
  tolerance, `TotFuncs`, `id` as a total relation of `X`,
  `p/.i`. Numbered `th1`–`th80` (`th38` unlabeled inverse of
  clip). Schemes `sch_LambdaC` / `sch_PartFuncEx` /
  `sch_LambdaR` / `sch_LambdaC9`. Locals `lm1`–`lm4`. Import
  is `GRFUNC_1`, `RELAT_2`, and `RELSET_1`.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from `apply` / `clip` / `PFuncs` / `TotFuncs` /
  Separation). No `sorry`. `lake build` green. Challenge/Solution
  types still match. Next unused: `MCART_1`.

### 2026-08-27 — MCART_1

- `MizarCCL/MCART_1.lean`: tuples, projections, Cartesian
  products. Pair/triple/quad characterizations, `product3` /
  `product4` membership and monotonicity, `pr1`/`pr2`, nested
  projections `fst11`/`fst12`/`snd21`/`snd22`, image of a
  relation, `sch_BiFuncEx`. Numbered `th7`–`th92` (canceled
  `1`–`6`, `25`, `27`–`29`, `44`, `46`, `71`, `82` omitted).
  Locals `lm1`–`lm3`. Import is `FUNCT_1`, `ENUMSET1`, and
  `XREGULAR`.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from `pr1`/`pr2` / `sch_Lambda` / Separation). No
  `sorry`. `lake build` green. Challenge/Solution types still
  match. Next unused: `FUNCT_2`.

### 2026-08-27 — WELLORD2

- `MizarCCL/WELLORD2.lean`: inclusion order `RelIncl`, order
  types, equipotence, Zermelo (`th17` via Hartogs + transfinite
  enumeration, not Mizar TG-class inaccessibility), Axiom of Choice
  (`th18`), and addenda on `RelIncl`. Numbered `th7`–`th17`
  (`1`–`6` canceled), `lm1`, defs `RelIncl` / `order_type_of` /
  `def1`–`def2`. Imports `WELLORD1`, `MCART_1`, and `ORDINAL1`.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from `RelIncl` / Separation / `sch_TSExist` / `sch_Lambda`).
  No `sorry`. `lake build` green. Challenge/Solution types still
  match. Next unused: `FUNCT_2`.

### 2026-08-27 — FUNCT_2

- `MizarCCL/FUNCT_2.lean`: functions from a set to a set.
  `isQuasiTotal` / `isFunctionOf` / `Funcs`, onto / bijective /
  permutation, image/preimage families, `composeAlong` (`p/*f`),
  `FUNCTION_DOMAIN`, `Action`. Numbered `th1`–`th125` (canceled
  `th37` omitted; Def7/Def8 absent in Mizar). Schemes `FuncEx1` /
  `Lambda1` / `FuncExD` / `LambdaD` / `Lambda1C` / `LambdaSep1`–
  `2` / `FunctRealEx` / `KappaMD` / `MChoice`. Imports `PARTFUN1`,
  `MCART_1`, and `SETFAM_1`.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`
  (choice from `Funcs` / Separation / schemes). No `sorry`.
  `lake build` green. Challenge/Solution types still match. Next
  unused: `BINOP_1`.

### 2026-08-27 — BINOP_1

- `MizarCCL/BINOP_1.lean`: binary operations. `apply2` (`f.(a,b)`),
  `UnOp`/`BinOp`, commutative/associative/idempotent, unities,
  distributivity, schemes (`FuncEx2`/`Lambda2`/…), addenda.
  Numbered `th1`–`th20` (canceled attr redefines omitted). Import
  is `FUNCT_2` only.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
  No `sorry`. `lake build` green. Challenge/Solution types still
  match. Next unused: `DOMAIN_1`.

### 2026-08-27 — DOMAIN_1

- `MizarCCL/DOMAIN_1.lean`: domains and Cartesian products.
  Pair/triple/quad domain facts, Fraenkel schemes, enumset subset
  redefines, projection coherence. Numbered `th1`–`th34`, schemes
  Fraenkel1–6 / SubsetD / SubsetFD / SubsetFD2 / AndScheme.
  Imports `MCART_1` and `ORDINAL1`.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
  No `sorry`. `lake build` green. Challenge/Solution types still
  match. Next unused: `FUNCT_3`.

### 2026-08-27 — MULTOP_1 (parallel frontier)

- `MizarCCL/MULTOP_1.lean`: three- and four-argument operations.
  `apply3` / `apply4`, `TriOp` / `QuaOp`, `th1`–`th6`, schemes
  FuncEx3D / TriOpEx / Lambda3D / TriOpLambda / FuncEx4D /
  QuaOpEx / Lambda4D / QuaOpLambda. Import is `FUNCT_2` only.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
  No `sorry`. `lake build` green. Challenge/Solution types still
  match. Sequential next unused remains `FUNCT_3`.

### 2026-08-27 — FUNCT_3

- `MizarCCL/FUNCT_3.lean`: basic functions and operations on
  functions. `imageFunc` / `invimageFunc`, `chi` / `incl` / `pr1` /
  `pr2` / `delta` / `complex` / `productFunc`, schemes FuncEx3 /
  Lambda3, numbered `th1`–`th80` (absolute Mizar theorem slots),
  AMI_1 addenda, registrations (`productFunc_oneToOne`,
  `exists_idempotent_binop`, `idempotent_reduce`). Imports
  `BINOP_1` and `DOMAIN_1`.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
  No `sorry`. `lake build` green. Challenge/Solution types still
  match. Next unused: `FUNCOP_1`.

### 2026-08-27 — SYSREL (parallel frontier)

- `MizarCCL/SYSREL.lean`: some properties of binary relations.
  Locals `lm1`/`lm2`, numbered `th1`–`th40`, closure `CL`.
  Import is `RELAT_1` only. Nothing canceled.
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
  No `sorry`. `lake build` green. Challenge/Solution types still
  match. Sequential next unused remains `FUNCOP_1`.

### 2026-08-27 — FUNCOP_1

- `MizarCCL/FUNCOP_1.lean`: binary operations applied to functions.
  `tilde` (`f~`), `mapsTo` / `mapsTo2`, `applied` / `appliedRight` /
  `appliedLeft`, `IFEQ`, `dotArrow`, function-/relation-yielding.
  Locals `lm1`/`lm2`, defs `def1`–`def8`, numbered `th1`–`th89`.
  Imports `FUNCT_3` and `WELLORD1`. Note: unlabeled `th46` stated
  with `x ∈ X` (Mizar bare form used only under that hyp in-tree).
- Sampled `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
  No `sorry`. `lake build` green. Challenge/Solution types still
  match. Next unused: `FUNCT_4` (also unlocks `ORDINAL2`, `PARTFUN2`).

### 2026-08-28 — FUNCT_4

- `MizarCCL/FUNCT_4.lean`: function override, domain swap, paired
  function products, two-point maps, and range-value updates.
  Definitions `override`, `swapDom`, `productPair`, `pairMapsTo`, and
  `rangeUpdate`; numbered `th1`–`th125` cover all absolute Mizar
  theorem slots. Late registrations preserve nonemptiness,
  empty-yielding, partial-function bounds, function-yielding,
  defined/valued/total, and compatibility properties.
- Imports are `FUNCOP_1` and `ORDINAL1`. Root `MizarCCL.lean` now
  imports `FUNCT_4`.
- Representative `#print axioms` checks (definitions, `th39`, `th72`,
  `th100`, `th104`, `th121`, `th125`) are exactly within
  `{propext, Classical.choice, Quot.sound}`. No `sorry`; full
  `lake build` green; Challenge/Solution types match.
- Next unused: `ORDINAL2`. Incomplete parallel files remain
  `WELLSET1` and `PARTFUN2`.

### 2026-08-28 — FUNCT_4 audit follow-up

- Corrected theorem indexing at `th66`–`th84`: the Def4 redefinition is
  now `pairMapsTo_isFunctionOf`, each numbered theorem again matches its
  absolute Mizar slot, and `th84` explicitly captures the two-point
  override evaluation theorem.
- Re-ran the full build, Challenge/Solution type comparison, zero-`sorry`
  scan, and representative axiom checks including `th66` and `th84`;
  all pass with axioms within
  `{propext, Classical.choice, Quot.sound}`.

### 2026-08-28 — ORDINAL2

- `MizarCCL/ORDINAL2.lean`: ordinal sequences, sequence suprema and
  infima, limits, ordinal addition/multiplication/exponentiation, and
  transfinite recursion. Definitions `def1`–`def17`, numbered
  `th1`–`th50`, all twenty schemes, `lm1`, and all ten registrations
  cover the complete Mizar article; there are no canceled slots.
- Mizar typing predicates are explicit hypotheses. Overloaded sequence
  `sup` / `inf` are `sequenceSup` / `sequenceInf`; guarded `lim` is
  totalized to the empty ordinal outside its defining guard.

### 2026-08-28 — WELLSET1 and PARTFUN2

- `MizarCCL/WELLSET1.lean`: `th1`–`th6`, `lm1`, and
  `sch_RSeparation`; `th6` keeps Zermelo's theorem statement while
  reusing the axiom-free `WELLORD2.th17` construction.
- `MizarCCL/PARTFUN2.lean`: all `th1`–`th61`, five Mizar redefinitions,
  and schemes `PartFuncExD`, `LambdaPFD`, and `UnPartFuncD`.
- Root `MizarCCL.lean` imports all three modules. Full `lake build`,
  Challenge/Solution type comparison, and zero-placeholder scans pass.
  Representative axiom audits are within
  `{propext, Classical.choice, Quot.sound}`. Next unused: `ORDINAL3`.

### 2026-08-28 — ORDINAL3

- `MizarCCL/ORDINAL3.lean`: ordinal arithmetic order laws,
  pointwise ordinal-sequence addition/multiplication, subtraction,
  Euclidean division and remainder, and natural-ordinal arithmetic.
- Numbered `th1`–`th75` cover all absolute Mizar theorem slots.
  Definitions `def1`–`def7` cover four sequence operations and
  `ordinalSub` / `ordinalDiv` / `ordinalMod`; `lm1`, all four
  registration claims, and both natural commutativity redefinitions
  are represented. The source defines no schemes and has no canceled
  slots.
- Root `MizarCCL.lean` imports `ORDINAL3`. Full `lake build`,
  Challenge/Solution type comparison, zero-placeholder scan, and
  representative axiom audits pass; axioms remain within
  `{propext, Classical.choice, Quot.sound}`. Next unused: `FINSET_1`.

### 2026-08-28 — FINSET_1

- `MizarCCL/FINSET_1.lean`: the finite/infinite attributes, closure
  under set and relation constructions, finite induction, centered
  families, finite-yielding relations/functions, and finite-membered
  families.
- Numbered `th1`–`th15` cover every absolute Mizar theorem slot.
  Definitions `def1`–`def6`, lemmas `lm1`–`lm3`, schemes
  `sch_OLambdaC` / `sch_Finite`, the antonym notation, and all 54
  registration claims are represented. There are no canceled slots.
- Root `MizarCCL.lean` imports `FINSET_1`. Full `lake build`,
  Challenge/Solution type comparison, zero-placeholder scan, and
  representative axiom audits pass; axioms remain within
  `{propext, Classical.choice, Quot.sound}`. Next unused: `FINSUB_1`.

### 2026-08-28 — FINSUB_1

- `MizarCCL/FINSUB_1.lean`: union/intersection/difference-closed and
  pre-Boolean families, the finite-subset family `Fin`, and the
  `Finite_Subset` mode.
- Numbered `th1`–`th18` cover all absolute Mizar theorem slots.
  Definitions `def1`–`def5`, four operation redefinitions, the mode,
  and all six registration claims are represented. The source has no
  lemmas, local schemes, or canceled slots.
- Root `MizarCCL.lean` imports `FINSUB_1`. Full `lake build`,
  Challenge/Solution type comparison, zero-placeholder scan, and
  representative axiom audits pass; axioms remain within
  `{propext, Classical.choice, Quot.sound}`. Next unused: `ORDERS_1`.

### 2026-08-29 — ORDERS_1

- `MizarCCL/ORDERS_1.lean`: choice functions, order attributes,
  Zorn's lemma (`th63` / `th64`), subset-inclusion maximality
  (`th65`–`th68`), Hausdorff linear-extension (`th69`), the
  `ZornMax` / `ZornMin` schemes, and the finite-image / order-type
  addenda (`th85`–`th88`).
- Numbered `th1`–`th88` cover all absolute Mizar theorem slots.
  Definitions `def1`–`def14`, lemmas `lm1`–`lm17`, both schemes, and
  the registration claims (empty and identity relations, converse
  and restriction preservation, finite relations, RelIncl order
  type) are represented. There are no canceled slots.
- Root `MizarCCL.lean` imports `ORDERS_1`. Full `lake build`,
  Challenge/Solution type comparison, zero-placeholder scan, and
  representative axiom audits (`th1`, `th63`, `th69`, `sch_ZornMax`,
  `th85`) pass; axioms remain within
  `{propext, Classical.choice, Quot.sound}`. Next unused: `SETWISEO`.

### 2026-08-31 — Palomar deferral and capstone policy

- Decision: **no Palomar registry submission** until all 368 queue
  articles are translated and green in `MizarCCL/`.
- Submission scope: **one capstone theorem per seed** (58 YELLOW*/
  WAYBEL* files in `palomar_seeds`), not full seed exports or
  intermediate per-article Palomar kits.
- Documented in Resume Protocol, Palomar submission policy (above),
  `.cursor/rules/handoff-discipline.mdc`, queue YAML header, README,
  and `formalization.yaml` `status.scope`.
- TARSKI Challenge/Solution/comparator remains an interim development
  scaffold only.

### 2026-08-31 — TARSKI lift audit strengthened after Palomar review

- Palomar's first AI verification accepted the mechanics but correctly
  noted that the compared type of `ulift` alone did not rule out a
  constant or unspecified map.
- Added sorry-free `TARSKI.ulift_eq_iff` and
  `TARSKI.ulift_mem_iff`: lifting reflects equality and preserves and
  reflects membership. Both are now in the interim Comparator surface.
- Narrowed all Palomar-facing prose: `th3` is explicitly the weakened
  universe-polymorphic (i)–(ii) fragment, not Mizar's inaccessible
  single-sort clauses (iii)–(iv), and the TARSKI scaffold is not
  claimed to clear the research-interest threshold.
- Full build, Challenge/Solution type comparison, zero-placeholder
  scan, and permitted-axiom checks pass. Both lift laws audit to
  `{propext, Quot.sound}`.

### 2026-08-31 — Palomar editorial audit in preflight

- Vendored [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy)
  under `vendor/palomar-policy/` with pin `vendor/PALOMAR_POLICY_PIN`.
  `scripts/palomar_policy_sync.py` checks upstream and auto-updates before
  full preflight (revert via `git checkout -- vendor/palomar-policy
  vendor/PALOMAR_POLICY_PIN`).
- Added `scripts/palomar_editorial_checks.py`,
  `scripts/palomar_mechanical_report.py`, and
  `scripts/palomar_editorial_audit.py` via **Cursor SDK**
  (`CURSOR_API_KEY` or `../tokens_ssto.yaml`). Substantive passes use
  `gpt-5.6-sol`; classification/metadata use `composer-2.5`.
- `scripts/palomar_preflight.sh`: full run = mechanical + editorial LLM
  audit; `--mechanical-only` for CI/translation; `--no-policy-sync` for
  offline reproducibility. Docs: `docs/PALOMAR_EDITORIAL_AUDIT.md`.
- CI runs mechanical preflight only. Interim TARSKI scaffold still expected
  to fail editorial notability until 58 capstones are selected.

### 2026-08-31 — SETWISEO

- `MizarCCL/SETWISEO.lean`: finite-subset function construction and
  induction, commutative-associative finite folds, image invariance,
  distributivity and homomorphism laws, the finite-union semilattice,
  and the singleton map.
- Numbered `th1`, `th2`, and `th6`–`th59` cover all 56 noncanceled
  absolute Mizar theorem slots; slots 3–5 are canceled. Definitions
  `def1`–`def6`, lemmas `lm1`–`lm2`, `FinSubFuncEx`, and all three
  `FinSubInd` schemes are represented, including the exact `Def3` /
  `Th16` auxiliary-function characterizations.
- Root `MizarCCL.lean` imports `SETWISEO`. Full `lake build`,
  mechanical Palomar preflight, Challenge/Solution type comparison,
  zero-placeholder scan, and representative axiom audits (`th1`,
  `FinSubFuncEx`, `def3`, `th16`, `th26`, `th30`, `def5`, `th53`,
  `th59`) pass; axioms remain within
  `{propext, Classical.choice, Quot.sound}`. Next unused: `FRAENKEL`.
