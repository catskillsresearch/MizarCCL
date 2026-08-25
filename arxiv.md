# The Tychonoff Theorem (Mizar YELLOW_17)

---

## Abstract

This note is the write-up of a Lean 4 translation of Bartłomiej
Skorulski, *The Tichonov Theorem* (Mizar article `YELLOW_17`, received
23 May 2000; Formalized Mathematics 9(2), 373–376). The source file is
`mml/yellow17.miz` from the [Mizar Mathematical
Library](https://github.com/MizarSystem/MML.git) at revision
`047822c4d814630b28eec8ca6b455e9eb912d5ff`. The headline result is
Tychonoff’s theorem: a dependent product of compact spaces is compact.
That theorem is the topological engine behind the compactness of the
Lawson topology on a continuous lattice and the product theory of
compact semilattices in Gierz–Hofmann–Keimel–Lawson–Mislove–Scott,
*A Compendium of Continuous Lattices* [GHKLMS80, §III-1, §VI-2–VI-3].
The Lean development is sorry-free. The compared theorems audit to
`{propext, Classical.choice, Quot.sound}`.

---

## 1. Introduction

Skorulski’s Mizar article develops the product topology on a
set-coded family of spaces and proves compactness of the product from
Alexander’s subbasis theorem. This package translates that article into
idiomatic Lean 4 against Mathlib 4.33, and packages the translation for
Palomar.

We do **not** claim Tychonoff’s theorem as original. Tychonoff proved
compactness of products of closed intervals in 1930 and stated the
general theorem in 1935 [Tyc30]. The compared claim is a
machine-checked Lean rendering of `YELLOW_17`, with Mathlib supplying
the Alexander/Tychonoff infrastructure that Mizar built from untyped
products.

The translation is **complete as a catalog** of the article’s named
results (`Th1`–`Th22`, `Lm1`, scheme `ElProductEx`, and the unnamed
Tichonov Theorem) but is **not one-to-one**. Mizar `Th8`–`Th13` are
topological-carrier wrappers of `Th1`–`Th7` and are merged. The
headline proof cites Mathlib’s `isCompact_univ_pi` /
`Pi.compactSpace` rather than replaying Skorulski’s
`Th15`+`Th22`+`ElProductEx` choice-function argument; those lemmas are
nonetheless stated and proved. Lean is slightly more general: Mizar
assumes a nonempty index set and nonempty factors; the Lean statements
allow empty index types.

The Mizar source is copied from
[`MizarSystem/MML`](https://github.com/MizarSystem/MML.git)
(`mml/yellow17.miz`) and is licensed GPL-3.0-or-later or
CC-BY-SA-3.0 by the Association of Mizar Users. Pin and
copy date: `mml/FROZEN.txt`. This repository uses the same dual
license.

## 2. Relation to the Compendium

In domain theory the reason one wants Tychonoff is not general
topology for its own sake. *A Compendium of Continuous Lattices*
[GHKLMS80] characterises continuous lattices as exactly the compact
Hausdorff Lawson semilattices:

- **§III-1 (The Lawson topology).** The Lawson topology $\lambda(L)$
  is the common refinement of the Scott topology and the lower
  topology. For a continuous lattice it is compact Hausdorff. The
  compactness argument realises $\lambda(L)$ as (a closed subspace of)
  a product of compact two-point spaces, and therefore invokes
  Tychonoff.
- **§VI-2 (Compact topological semilattices)** and **§VI-3 (The
  fundamental theorem of compact semilattices).** A complete lattice
  admits a compact Hausdorff topology making meet jointly continuous
  if and only if it is a continuous lattice; that topology is then
  uniquely $\lambda(L)$. Products of compact Lawson semilattices are
  again compact Lawson semilattices, again by Tychonoff on the
  underlying spaces.

Skorulski’s `YELLOW_17`, and the Lean theorems
`yellow17_tychonoff` / `yellow17_tychonoff_sets`, supply the
space-level product theorem that those Compendium sections use. This
package does **not** formalize the Lawson topology or the fundamental
theorem; it formalizes the topological lemma they rest on.

(The 2003 successor *Continuous Lattices and Domains* [GHKLMS03]
reorganizes the same material as Chapters II–III and VI. We cite the
1980 Compendium, which is the reference used throughout the
`YELLOW_*` / `WAYBEL_*` Mizar development.)

## 3. Representation

Mizar codes a family as a function `F` and the product as the set
`product F` of functions on `dom F`. Projections are `proj(F,i)` and
updates are `f+*(i,xi)`.

Lean uses a dependent product `∀ i, X i`, evaluation `Function.eval`,
updates `Function.update`, and cylinders `eval i ⁻¹' U`. The open
cylinder family `cylinderSubbasis X` is the product prebasis.

## 4. Mizar inventory

Formalized Mathematics numbers the printed propositions `(1)`–`(24)`;
the `.miz` file uses `Th1`–`Th22`, lemma `Lm1`, scheme `ElProductEx`,
and one unnamed Tichonov Theorem. The table is the inventory from the
translation session. In Markdown tables, literal `|` is written `\|`.

| FM | Mizar | Lean | Notes |
| --- | --- | --- | --- |
| (1), (9) | `Th1`, `Th9` | `eval_singleton_inter_mem` | Same fact; `Th9` is only the topological-carrier wrapper of `Th1` |
| (2) | `Th2` | `update_mem_univ_pi` | Direct |
| (3) | `Th3` | `range_eval_eq_univ` | Only the surjectivity half. `rng proj ⊆ F.i` is definitional for `eval` |
| (4), (10) | `Th4`, `Th10` | `preimage_eval_univ` | Merged |
| (5), (11) | `Th5`, `Th11` | `update_mem_eval_singleton` | Merged |
| (8) | `Th8` | `eval_apply` | `rfl` |
| — | `Lm1` | (folded into next) | Used only to prove `Th6` |
| (6), (13) | `Th6`, `Th13` | `mem_preimage_eval_update_iff` | Merged with `Lm1` |
| (7), (12) | `Th7`, `Th12` | `eval_singleton_subset_eval_*` | Split into same-axis / off-axis / iff |
| scheme | `ElProductEx` | `elProductEx` / `_spec` | Present; unused by the Lean headline |
| (14) | (cover lemma) | (Mathlib) | “`F` is a cover iff the carrier is ⊆ `⋃ F`” |
| (15) | `Th14` | `isCompact_iff_finite_open_subcover` | Iff, via Mathlib |
| (16) | `Th15` | `isCompact_of_subbasis_finite_subcover` | **Only Alexander’s “if”**. Mizar’s converse is the trivial “compact ⇒ every open cover has a finite subcover” |
| (17) | `Th16` | `mem_cylinderSubbasis_iff` | Direct, plus extra `pi_eq_generateFrom_cylinderSubbasis` |
| (18) | `Th17` | `cylinder_of_singleton_subset` | Direct |
| (19) | `Th18` | `univ_subset_iUnion_preimage_eval` | Direct |
| (20) | `Th19` | `univ_subset_sUnion_of_fiber_cover_no_strict` | Stated and proved. **Not used** to prove Tychonoff |
| (21) | `Th20` | `exists_cylinder_containing_fiber_of_finite` | Same |
| (22) | `Th21` | `exists_proper_open_cylinder_of_fiber_cover` | Same |
| (23) | `Th22` | `exists_point_fiber_not_finitely_covered` | Same |
| (24) | Tichonov | `yellow17_tychonoff_sets` | `IsCompact (univ.pi s)` via `isCompact_univ_pi` |
| (24) | Tichonov | `yellow17_tychonoff` | `CompactSpace (∀ i, X i)` via `Pi.compactSpace` |
| (24) | Tichonov | `yellow17_tychonoff'` | Implication form matching the Mizar statement |

So every named Mizar result has a Lean counterpart, but there are not
22 separate Lean theorems matching `Th1`–`Th22` one-for-one.

**Complete?**

- Yes for the **statements**: product lemmas, cylinder subbasis,
  compactness criteria, and Tychonoff are all there, and
  `lake build` is green.
- No for a **Mizar-faithful proof of Tychonoff**. In the `.miz` file,
  Tychonoff is `Th15` + `Th22` + `ElProductEx` + a choice function
  through the cover. In Lean the headline does not replay that chain;
  `Th19`–`Th22` are combinatorial leftovers.

**Proof note (Tychonoff).** Axioms of the three headlines:
`{propext, Classical.choice, Quot.sound}`. Choice is expected for
classical compactness of arbitrary products (Kelley: Tychonoff for
$T_2$ spaces is equivalent to AC). The Compendium’s Lawson-compactness
argument in §III-1 inherits that choice.

**Proof note (Th15).** Mizar states an iff. Lean records the Alexander
direction used to test compactness on a generating family
(`isCompact_generateFrom`). The converse is the ordinary
finite-subcover property (`Th14`).

## 5. Palomar statement of record

`Challenge.lean` restates every `Yellow17` theorem and definition with
`sorry`. `Solution.lean` imports `Yellow17.lean`. `comparator.json`
lists all 24 theorems and both definitions (`elProductEx`,
`cylinderSubbasis`). Types must match under `pp.all` / `pp.explicit`
(`scripts/compare_challenge_solution_types.sh`).

## 6. Build

Toolchain: Lean / mathlib **v4.33.0**.

```
lake exe cache get
lake build
bash scripts/palomar_preflight.sh
bash scripts/build_arxiv_pdf.sh
```

`lake build` typechecks `Yellow17`, `Challenge`, and `Solution`.
Narrative inventory: this file. Metadata: `comparator.json`,
`formalization.yaml`. MML pin: `mml/FROZEN.txt`.

## References

- **[GHKLMS80]** G. Gierz, K. H. Hofmann, K. Keimel, J. D. Lawson,
  M. Mislove, and D. S. Scott. *A Compendium of Continuous Lattices*.
  Springer-Verlag, Berlin, 1980. DOI
  [10.1007/978-3-642-67678-9](https://doi.org/10.1007/978-3-642-67678-9).
  **§III-1** (Lawson topology; compactness via Tychonoff);
  **§VI-2–VI-3** (compact topological semilattices and the fundamental
  theorem).
- **[GHKLMS03]** G. Gierz, K. H. Hofmann, K. Keimel, J. D. Lawson,
  M. Mislove, and D. S. Scott. *Continuous Lattices and Domains*.
  Encyclopedia of Mathematics and its Applications 93. Cambridge
  University Press, 2003. Successor of [GHKLMS80]; same material
  reorganized as Chapters II–III and VI.
- **[Sko01]** Bartłomiej Skorulski. *The Tichonov Theorem*. Formalized
  Mathematics 9(2), 373–376, 2001. Mizar article `YELLOW_17`, received
  23 May 2000. Source:
  [`mml/yellow17.miz`](https://github.com/MizarSystem/MML/blob/047822c4d814630b28eec8ca6b455e9eb912d5ff/mml/yellow17.miz)
  in [MizarSystem/MML](https://github.com/MizarSystem/MML.git)
  at `047822c4d814630b28eec8ca6b455e9eb912d5ff` (Mizar 7.13.01 /
  MML 4.181.1147).
- **[Tyc30]** Andrey Tychonoff. *Über die topologische Erweiterung von
  Räumen*. Mathematische Annalen 102 (1930), 544–561.
- The mathlib Tychonoff and Alexander theorems
  (`isCompact_univ_pi`, `Pi.compactSpace`, `isCompact_generateFrom`).

## Lean Code

- [`Yellow17.lean`](Yellow17.lean) — proofs
- [`Challenge.lean`](Challenge.lean) — Palomar statements
- [`Solution.lean`](Solution.lean) — re-export of the proofs
