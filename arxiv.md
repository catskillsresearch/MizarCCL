# Tarski–Grothendieck Set Theory (Mizar TARSKI)

---

## Abstract

This note is the write-up of a Lean 4 translation of Andrzej Trybulec,
*Tarski Grothendieck Set Theory* (Mizar article `TARSKI`, received
1 January 1989). The source file is `vendor/MML/mml/tarski.miz` from
the [Mizar Mathematical Library](https://github.com/MizarSystem/MML.git)
at revision `047822c4d814630b28eec8ca6b455e9eb912d5ff`. The article
is the axiomatic root of the MML: extensionality, singleton and
unordered pair, inclusion, union, regularity, the Fraenkel scheme,
the Kuratowski pair, equipotence, and the Tarski–Grothendieck
universe axiom. The Lean development defines a model (`TarskiSet`)
and proves those statements; it is sorry-free. Compared theorems
audit to `{propext, Classical.choice, Quot.sound}`.

---

## 1. Introduction

`TARSKI` is the first article of the Mizar Mathematical Library and
the first item of the MizarCCL translation queue (368 used articles
in the YELLOW* / WAYBEL* environ closure). Mizar treats `set` as an
untyped sort with a primitive membership predicate `in`. This
package does **not** post `axiom set` and does **not** use `set` as
a synonym for `Type`. The carrier is a defined type `TarskiSet.{u}`:
Aczel pre-sets indexed by `Type u`, quotiented by extensional
equivalence. Membership is defined.

The compared claim is a machine-checked Lean rendering of the
Mizar-labelled items `TARSKI:1`–`TARSKI:3`, `TARSKI:def 1`–`def 6`,
and `TARSKI:sch 1`. `TARSKI:3` is universe-polymorphic: the
collection of all `TarskiSet.{u}` lives in `TarskiSet.{u+1}`. Mizar’s
power-set witness (iii) and inaccessibility clause (iv) are not
theorems of `Type u` and are not claimed.

The Mizar source is vendored from
[`MizarSystem/MML`](https://github.com/MizarSystem/MML.git)
as `vendor/MML/mml/tarski.miz` and is licensed GPL-3.0-or-later or
CC-BY-SA-3.0 by the Association of Mizar Users. Pin:
`vendor/MML` @ `047822c4d814630b28eec8ca6b455e9eb912d5ff`. This
repository uses the same dual license.

## 2. Representation

A pre-set is a family of pre-sets indexed by a `Type u`. Two
pre-sets are equivalent when their families are mutually dense under
that relation. `TarskiSet.{u}` is the quotient. Lean notation
`x ∈ X` is Mizar `x in X`. Inclusion `X ⊆ Y` is Mizar `X c= Y`.
The constructors `{y}`, `{y,z}`, `union X`, and `[x,y]` are
definitions on the quotient (singleton, unordered pair, union,
Kuratowski pair). A lift `ulift` embeds `TarskiSet.{u}` into
`TarskiSet.{u+1}`.

## 3. Mizar inventory

The table is the inventory of the article. In Markdown tables,
literal `|` is written `\|`.

| Mizar | Lean | Notes |
| --- | --- | --- |
| `TARSKI:1` | `th1` | Extensionality |
| `TARSKI:def 1` | `def1` / `singleton` | `x ∈ {y}` iff `x = y` |
| `TARSKI:def 2` | `def2` / `upair` | `x ∈ {y,z}` iff `x = y` or `x = z` |
| commutativity | `upair_comm` | `{y,z} = {z,y}` |
| `TARSKI:def 3` | `def3` / `subset` | `X ⊆ Y` iff every element of `X` is in `Y` |
| reflexivity | `subset_refl` | `X ⊆ X` |
| `TARSKI:def 4` | `def4` / `union` | `x ∈ union X` iff some `Y` has `x ∈ Y` and `Y ∈ X` |
| `TARSKI:2` | `th2` | Regularity; uses `Classical.choice` |
| `TARSKI:sch 1` | `sch1` | Fraenkel; uses `Classical.choice` |
| `TARSKI:def 5` | `def5` / `pair` | `[x,y] = {{x,y},{x}}` |
| `TARSKI:def 6` | `def6` / `are_equipotent` | Functional graph of a bijection |
| `TARSKI:3` | `th3` / `ulift` | Universe of all `u`-sets in `u+1`; subset-closed. Not Mizar (iii)–(iv) |

**Complete?**

- Yes for the **statements** of `TARSKI:1`–`2`, `def 1`–`6`, and
  `sch 1`, and for clauses (i)–(ii) of `TARSKI:3` in the
  universe-polymorphic reading.
- No for a **single-sort inaccessible** as in Mizar (iii)–(iv).
  Lean does not treat `Type u` as a ZFC inaccessible.

**Proof note (choice).** `#print axioms` of `th2` and `sch1` includes
`Classical.choice` (well-founded descent on pre-set membership;
selection of a Fraenkel image). The remaining compared theorems
use at most `{propext, Quot.sound}`. There is no project-defined
`axiom` and no `sorry` outside `Challenge.lean`.

## 4. Palomar statement of record

`Challenge.lean` restates every compared `TARSKI` theorem and
constructor with `sorry`. `Solution.lean` imports
`MizarCCL/TARSKI.lean`. `comparator.json` lists 12 theorems and
7 definitions. Types must match under `pp.all` / `pp.explicit`
(`scripts/compare_challenge_solution_types.sh`).

## 5. Build

Toolchain: Lean **v4.33.0**. No Mathlib.

```
lake build
bash scripts/palomar_preflight.sh
bash scripts/build_arxiv_pdf.sh
```

`lake build` typechecks `MizarCCL`, `Challenge`, and `Solution`.
Narrative inventory: this file. Metadata: `comparator.json`,
`formalization.yaml`. MML pin: `vendor/MML` @
`047822c4d814630b28eec8ca6b455e9eb912d5ff`.

## References

- **[Tar38]** Alfred Tarski. *Über unerreichbare Kardinalzahlen*.
  Fundamenta Mathematicae 30 (1938), 68–69.
- **[Tar39]** Alfred Tarski. *On Well-ordered Subsets of any Set*.
  Fundamenta Mathematicae 32 (1939), 176–183.
- **[Try89]** Andrzej Trybulec. *Tarski Grothendieck Set Theory*.
  Mizar article `TARSKI`, received 1 January 1989. Source:
  [`mml/tarski.miz`](https://github.com/MizarSystem/MML/blob/047822c4d814630b28eec8ca6b455e9eb912d5ff/mml/tarski.miz)
  in [MizarSystem/MML](https://github.com/MizarSystem/MML.git)
  at `047822c4d814630b28eec8ca6b455e9eb912d5ff` (Mizar 7.13.01 /
  MML 4.181.1147).

## Lean Code

- [`MizarCCL/HIDDEN.lean`](MizarCCL/HIDDEN.lean) — `TarskiSet` and `∈`
- [`MizarCCL/TARSKI.lean`](MizarCCL/TARSKI.lean) — proofs
- [`Challenge.lean`](Challenge.lean) — Palomar statements
- [`Solution.lean`](Solution.lean) — re-export of the proofs
