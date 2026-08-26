import MizarCCL.HIDDEN

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under GNU GPL-3.0-or-later or CC-BY-SA-3.0.
See `doc/COPYING.*` and the notices in `vendor/MML/mml/tarski.miz`.
Authors: Andrzej Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Tarski-Grothendieck set theory

1–1 Lean rendering of Mizar article `TARSKI`
(`vendor/MML/mml/tarski.miz`, Mizar 7.13.01 / MML 4.181.1147).

Mizar labels: `TARSKI:1`–`TARSKI:3`, `TARSKI:def 1`–`def 6`,
`TARSKI:sch 1`. Theorems without proofs, `correctness` of `means`
constructors, and the Fraenkel scheme (`thus thesis`) are Lean axioms.
That is unavoidable: this article *is* the axiomatic root.

`[x,y]` is an `equals` abbreviation and `c=` / `are_equipotent` are
`means` predicates, so those are definitions. Commutativity of
`{y,z}` and reflexivity of `c=` are proved.
-/

namespace TARSKI

/-! ## TARSKI:1 — Extensionality -/

/-- Mizar `TARSKI:1`. -/
axiom extensionality {X Y : set} : (∀ x, x ∈ X ↔ x ∈ Y) → X = Y

@[inherit_doc extensionality]
theorem th1 {X Y : set} : (∀ x, x ∈ X ↔ x ∈ Y) → X = Y :=
  extensionality

/-! ## TARSKI:def 1 — singleton `{ y }` -/

/-- Mizar constructor `{ y }`. -/
axiom singleton : set → set

noncomputable instance : Singleton set set where
  singleton := singleton

/-- Mizar `TARSKI:def 1`. -/
axiom singleton_iff (y x : set) : x ∈ (singleton y) ↔ x = y

@[inherit_doc singleton_iff]
theorem def1 (y x : set) : x ∈ ({y} : set) ↔ x = y :=
  singleton_iff y x

/-! ## TARSKI:def 2 — unordered pair `{ y, z }` -/

/-- Mizar constructor `{ y, z }`. -/
axiom upair : set → set → set

/-- Mizar `TARSKI:def 2`. -/
axiom upair_iff (y z x : set) : x ∈ upair y z ↔ x = y ∨ x = z

@[inherit_doc upair_iff]
theorem def2 (y z x : set) : x ∈ upair y z ↔ x = y ∨ x = z :=
  upair_iff y z x

/-- Mizar `commutativity` on `{ y, z }`. -/
theorem upair_comm (y z : set) : upair y z = upair z y :=
  extensionality fun x =>
    (upair_iff y z x).trans <| Or.comm.trans (upair_iff z y x).symm

/-! ## TARSKI:def 3 — inclusion `c=` -/

/-- Mizar predicate `c=`. -/
def subset (X Y : set) : Prop := ∀ x, x ∈ X → x ∈ Y

instance : HasSubset set where
  Subset := subset

/-- Mizar `TARSKI:def 3`. -/
theorem subset_iff (X Y : set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y :=
  Iff.rfl

@[inherit_doc subset_iff]
theorem def3 (X Y : set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y :=
  subset_iff X Y

/-- Mizar `reflexivity` on `c=`. -/
@[refl]
theorem subset_refl (X : set) : X ⊆ X := fun _ hx => hx

/-! ## TARSKI:def 4 — `union X` -/

/-- Mizar constructor `union`. -/
axiom union : set → set

/-- Mizar `TARSKI:def 4`. -/
axiom union_iff (X x : set) : x ∈ union X ↔ ∃ Y, x ∈ Y ∧ Y ∈ X

@[inherit_doc union_iff]
theorem def4 (X x : set) : x ∈ union X ↔ ∃ Y, x ∈ Y ∧ Y ∈ X :=
  union_iff X x

/-! ## TARSKI:2 — Regularity -/

/-- Mizar `TARSKI:2`. -/
axiom regularity {x X : set} : x ∈ X → ∃ Y, Y ∈ X ∧ ¬∃ x, x ∈ X ∧ x ∈ Y

@[inherit_doc regularity]
theorem th2 {x X : set} : x ∈ X → ∃ Y, Y ∈ X ∧ ¬∃ x, x ∈ X ∧ x ∈ Y :=
  regularity

/-! ## TARSKI:sch 1 — Fraenkel (replacement) -/

/-- Mizar scheme `Fraenkel` / `TARSKI:sch 1`. -/
axiom fraenkel (A : set) (P : set → set → Prop)
    (functional : ∀ x y z, P x y → P x z → y = z) :
    ∃ X : set, ∀ x, x ∈ X ↔ ∃ y, y ∈ A ∧ P y x

@[inherit_doc fraenkel]
theorem sch1 (A : set) (P : set → set → Prop)
    (functional : ∀ x y z, P x y → P x z → y = z) :
    ∃ X : set, ∀ x, x ∈ X ↔ ∃ y, y ∈ A ∧ P y x :=
  fraenkel A P functional

/-! ## TARSKI:def 5 — ordered pair `[x,y]` (Kuratowski) -/

/-- Mizar `[x,y]`, defined `equals {{x,y},{x}}`. -/
noncomputable def pair (x y : set) : set := upair (upair x y) (singleton x)

/-- Mizar `TARSKI:def 5`. -/
theorem pair_eq (x y : set) : pair x y = upair (upair x y) (singleton x) :=
  rfl

@[inherit_doc pair_eq]
theorem def5 (x y : set) : pair x y = upair (upair x y) (singleton x) :=
  pair_eq x y

/-! ## TARSKI:def 6 — equipotence -/

/-- Mizar predicate `are_equipotent`. -/
def are_equipotent (X Y : set) : Prop :=
  ∃ Z : set,
    (∀ x, x ∈ X → ∃ y, y ∈ Y ∧ pair x y ∈ Z) ∧
    (∀ y, y ∈ Y → ∃ x, x ∈ X ∧ pair x y ∈ Z) ∧
    ∀ x y z u, pair x y ∈ Z → pair z u ∈ Z → (x = z ↔ y = u)

/-- Mizar `TARSKI:def 6`. -/
theorem are_equipotent_iff (X Y : set) :
    are_equipotent X Y ↔
      ∃ Z : set,
        (∀ x, x ∈ X → ∃ y, y ∈ Y ∧ pair x y ∈ Z) ∧
        (∀ y, y ∈ Y → ∃ x, x ∈ X ∧ pair x y ∈ Z) ∧
        ∀ x y z u, pair x y ∈ Z → pair z u ∈ Z → (x = z ↔ y = u) :=
  Iff.rfl

@[inherit_doc are_equipotent_iff]
theorem def6 (X Y : set) :
    are_equipotent X Y ↔
      ∃ Z : set,
        (∀ x, x ∈ X → ∃ y, y ∈ Y ∧ pair x y ∈ Z) ∧
        (∀ y, y ∈ Y → ∃ x, x ∈ X ∧ pair x y ∈ Z) ∧
        ∀ x y z u, pair x y ∈ Z → pair z u ∈ Z → (x = z ↔ y = u) :=
  are_equipotent_iff X Y

/-! ## TARSKI:3 — Tarski–Grothendieck universes -/

/-- Mizar `TARSKI:3`. For every set `N` there is a universe `M`
containing `N`, closed under subsets and (a set containing) the power
set, and such that every proper subset of `M` is an element of `M`. -/
axiom tarski_grothendieck (N : set) :
    ∃ M : set,
      N ∈ M ∧
      (∀ X Y, X ∈ M → Y ⊆ X → Y ∈ M) ∧
      (∀ X, X ∈ M → ∃ Z, Z ∈ M ∧ ∀ Y, Y ⊆ X → Y ∈ Z) ∧
      (∀ X, X ⊆ M → are_equipotent X M ∨ X ∈ M)

@[inherit_doc tarski_grothendieck]
theorem th3 (N : set) :
    ∃ M : set,
      N ∈ M ∧
      (∀ X Y, X ∈ M → Y ⊆ X → Y ∈ M) ∧
      (∀ X, X ∈ M → ∃ Z, Z ∈ M ∧ ∀ Y, Y ⊆ X → Y ∈ Z) ∧
      (∀ X, X ⊆ M → are_equipotent X M ∨ X ∈ M) :=
  tarski_grothendieck N

end TARSKI
