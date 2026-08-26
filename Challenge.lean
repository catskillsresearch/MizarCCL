/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under GNU GPL-3.0-or-later or CC-BY-SA-3.0.
See `doc/COPYING.*` and the notices in `vendor/mml/tarski.miz`.
Authors: Andrzej Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/

import MizarCCL.HIDDEN

/-!
# Tarski–Grothendieck set theory (Mizar `TARSKI`)

Palomar Challenge: statements of the Lean 4 translation of Andrzej
Trybulec, *Tarski Grothendieck Set Theory* (Mizar `TARSKI`). Proofs
are `sorry`; see `MizarCCL/TARSKI.lean`.
-/

universe u

namespace TARSKI

/-! ## Constructors (Mizar `func` / `pred`) -/

def singleton (y : TarskiSet.{u}) : TarskiSet.{u} :=
  sorry

def upair (y z : TarskiSet.{u}) : TarskiSet.{u} :=
  sorry

def subset (X Y : TarskiSet.{u}) : Prop :=
  sorry

instance instHasSubset : HasSubset TarskiSet.{u} where
  Subset := subset

def union (X : TarskiSet.{u}) : TarskiSet.{u} :=
  sorry

def pair (x y : TarskiSet.{u}) : TarskiSet.{u} :=
  sorry

def are_equipotent (X Y : TarskiSet.{u}) : Prop :=
  sorry

def ulift (x : TarskiSet.{u}) : TarskiSet.{u + 1} :=
  sorry

/-! ## TARSKI:1 — Extensionality -/

theorem th1 {X Y : TarskiSet.{u}} : (∀ x, x ∈ X ↔ x ∈ Y) → X = Y := by
  sorry

/-! ## TARSKI:def 1 — singleton `{ y }` -/

theorem def1 (y x : TarskiSet.{u}) : x ∈ singleton y ↔ x = y := by
  sorry

/-! ## TARSKI:def 2 — unordered pair `{ y, z }` -/

theorem def2 (y z x : TarskiSet.{u}) : x ∈ upair y z ↔ x = y ∨ x = z := by
  sorry

theorem upair_comm (y z : TarskiSet.{u}) : upair y z = upair z y := by
  sorry

/-! ## TARSKI:def 3 — inclusion `c=` -/

theorem def3 (X Y : TarskiSet.{u}) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by
  sorry

@[refl]
theorem subset_refl (X : TarskiSet.{u}) : X ⊆ X := by
  sorry

/-! ## TARSKI:def 4 — `union X` -/

theorem def4 (X x : TarskiSet.{u}) : x ∈ union X ↔ ∃ Y, x ∈ Y ∧ Y ∈ X := by
  sorry

/-! ## TARSKI:2 — Regularity -/

theorem th2 {X x : TarskiSet.{u}} (hx : x ∈ X) :
    ∃ Y, Y ∈ X ∧ ¬∃ z, z ∈ X ∧ z ∈ Y := by
  sorry

/-! ## TARSKI:sch 1 — Fraenkel -/

theorem sch1 (A : TarskiSet.{u}) (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (functional : ∀ x y z, P x y → P x z → y = z) :
    ∃ X : TarskiSet.{u}, ∀ x, x ∈ X ↔ ∃ y, y ∈ A ∧ P y x := by
  sorry

/-! ## TARSKI:def 5 — ordered pair `[x,y]` (Kuratowski) -/

theorem def5 (x y : TarskiSet.{u}) :
    pair x y = upair (upair x y) (singleton x) := by
  sorry

/-! ## TARSKI:def 6 — equipotence -/

theorem def6 (X Y : TarskiSet.{u}) :
    are_equipotent X Y ↔
      ∃ Z : TarskiSet.{u},
        (∀ x, x ∈ X → ∃ y, y ∈ Y ∧ pair x y ∈ Z) ∧
        (∀ y, y ∈ Y → ∃ x, x ∈ X ∧ pair x y ∈ Z) ∧
        ∀ x y z u, pair x y ∈ Z → pair z u ∈ Z → (x = z ↔ y = u) := by
  sorry

/-! ## TARSKI:3 — Tarski–Grothendieck universes -/

theorem th3 (N : TarskiSet.{u}) :
    ∃ M : TarskiSet.{u + 1},
      ulift N ∈ M ∧
      (∀ X Y : TarskiSet.{u + 1}, X ∈ M → Y ⊆ X → Y ∈ M) ∧
      (∀ X : TarskiSet.{u}, ulift X ∈ M) := by
  sorry

end TARSKI
