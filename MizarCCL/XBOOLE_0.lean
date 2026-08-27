import MizarCCL.TARSKI

/-
Copyright (c) 2002-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/xboole_0.miz`.
Authors: Library Committee (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Boolean properties of sets — definitions

1–1 Lean rendering of Mizar article `XBOOLE_0`
(`vendor/mml/xboole_0.miz`, Mizar 7.13.01 / MML 4.181.1147).

Environ imports `TARSKI` (notations, constructors, theorems, schemes).
No Mathlib: these constructors live on untyped `TarskiSet`.
-/

universe u

open TarskiSet TARSKI

namespace XBOOLE_0

/-! ## XBOOLE_0:sch Separation -/

/-- Mizar `the set`: an arbitrary inhabitant used only to feed
Separation when constructing the empty set. -/
def theSet : TarskiSet.{u} :=
  TARSKI.singleton (mk (.mk PEmpty fun e => nomatch e))

/-- `XBOOLE_0:sch Separation`. Fraenkel with `Q[x,y] := x = y ∧ P[y]`. -/
theorem sch_separation (A : TarskiSet.{u}) (P : TarskiSet.{u} → Prop) :
    ∃ X : TarskiSet.{u}, ∀ x, x ∈ X ↔ x ∈ A ∧ P x := by
  have functional : ∀ x y z : TarskiSet.{u},
      (x = y ∧ P y) → (x = z ∧ P z) → y = z := by
    intro _ y z h1 h2
    exact h1.1.symm.trans h2.1
  obtain ⟨X, hX⟩ := sch1 A (fun y x => y = x ∧ P x) functional
  refine ⟨X, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨y, hyA, rfl, hP⟩ := (hX x).mp hx
    exact ⟨hyA, hP⟩
  · intro ⟨hxA, hP⟩
    exact (hX x).mpr ⟨x, hxA, rfl, hP⟩

/-! ## XBOOLE_0:def 1 — `X is empty` -/

def isEmpty (X : TarskiSet.{u}) : Prop := ¬ ∃ x, x ∈ X

theorem def1 (X : TarskiSet.{u}) : isEmpty X ↔ ¬ ∃ x, x ∈ X := Iff.rfl

/-- Existence of an empty set: Separation from `theSet` with `False`. -/
theorem empty_exists : ∃ Y : TarskiSet.{u}, isEmpty Y := by
  obtain ⟨Y, hY⟩ := sch_separation theSet (fun _ => False)
  exact ⟨Y, fun ⟨x, hx⟩ => (hY x).mp hx |>.2⟩

/-! ## XBOOLE_0:def 2 — `{}` is the empty set -/

noncomputable def emptySet : TarskiSet.{u} :=
  Classical.choose empty_exists

theorem emptySet_isEmpty : isEmpty (emptySet : TarskiSet.{u}) :=
  Classical.choose_spec empty_exists

noncomputable instance : EmptyCollection TarskiSet.{u} where
  emptyCollection := emptySet

theorem empty_iff (x : TarskiSet.{u}) : x ∈ (∅ : TarskiSet.{u}) ↔ False :=
  ⟨fun hx => emptySet_isEmpty ⟨x, hx⟩, fun h => h.elim⟩

/-- `Lm1`: an empty set equals `{}`. -/
theorem empty_eq {X : TarskiSet.{u}} (h : isEmpty X) : X = (∅ : TarskiSet.{u}) :=
  extensionality fun x =>
    ⟨fun hx => (h ⟨x, hx⟩).elim, fun hx => (emptySet_isEmpty ⟨x, hx⟩).elim⟩

/-! ## XBOOLE_0:def 3 — union `X ∪ Y` -/

def unionSet (X Y : TarskiSet.{u}) : TarskiSet.{u} :=
  union (upair X Y)

@[simp] theorem unionSet_iff (X Y x : TarskiSet.{u}) :
    x ∈ unionSet X Y ↔ x ∈ X ∨ x ∈ Y := by
  constructor
  · intro h
    obtain ⟨Z, hxZ, hZ⟩ := (union_iff _ _).mp h
    rcases (upair_iff X Y Z).mp hZ with hZX | hZY
    · exact Or.inl (hZX ▸ hxZ)
    · exact Or.inr (hZY ▸ hxZ)
  · intro h
    refine (union_iff _ _).mpr ?_
    cases h with
    | inl hX => exact ⟨X, hX, (upair_iff _ _ _).mpr (Or.inl rfl)⟩
    | inr hY => exact ⟨Y, hY, (upair_iff _ _ _).mpr (Or.inr rfl)⟩

theorem unionSet_unique {X Y A1 A2 : TarskiSet.{u}}
    (h1 : ∀ x, x ∈ A1 ↔ x ∈ X ∨ x ∈ Y)
    (h2 : ∀ x, x ∈ A2 ↔ x ∈ X ∨ x ∈ Y) : A1 = A2 :=
  extensionality fun x => (h1 x).trans (h2 x).symm

theorem unionSet_comm (X Y : TarskiSet.{u}) : unionSet X Y = unionSet Y X :=
  extensionality fun x =>
    (unionSet_iff X Y x).trans <| Or.comm.trans (unionSet_iff Y X x).symm

theorem unionSet_idem (X : TarskiSet.{u}) : unionSet X X = X :=
  extensionality fun x =>
    (unionSet_iff X X x).trans ⟨Or.rec id id, Or.inl⟩

noncomputable instance : Union TarskiSet.{u} where
  union := unionSet

theorem def3 (X Y x : TarskiSet.{u}) : x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y :=
  unionSet_iff X Y x

theorem union_comm (X Y : TarskiSet.{u}) : X ∪ Y = Y ∪ X :=
  unionSet_comm X Y

theorem union_idem (X : TarskiSet.{u}) : X ∪ X = X :=
  unionSet_idem X

/-! ## XBOOLE_0:def 4 — intersection `X ∩ Y` -/

noncomputable def interSet (X Y : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (sch_separation X (fun x => x ∈ Y))

theorem interSet_spec (X Y : TarskiSet.{u}) :
    ∀ x, x ∈ interSet X Y ↔ x ∈ X ∧ x ∈ Y :=
  Classical.choose_spec (sch_separation X (fun x => x ∈ Y))

@[simp] theorem interSet_iff (X Y x : TarskiSet.{u}) :
    x ∈ interSet X Y ↔ x ∈ X ∧ x ∈ Y :=
  interSet_spec X Y x

theorem interSet_comm (X Y : TarskiSet.{u}) : interSet X Y = interSet Y X :=
  extensionality fun x =>
    (interSet_iff X Y x).trans <| and_comm.trans (interSet_iff Y X x).symm

theorem interSet_idem (X : TarskiSet.{u}) : interSet X X = X :=
  extensionality fun x =>
    (interSet_iff X X x).trans ⟨And.left, fun hx => ⟨hx, hx⟩⟩

noncomputable instance : Inter TarskiSet.{u} where
  inter := interSet

theorem def4 (X Y x : TarskiSet.{u}) : x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y :=
  interSet_iff X Y x

theorem inter_comm (X Y : TarskiSet.{u}) : X ∩ Y = Y ∩ X :=
  interSet_comm X Y

theorem inter_idem (X : TarskiSet.{u}) : X ∩ X = X :=
  interSet_idem X

/-! ## XBOOLE_0:def 5 — difference `X \ Y` -/

noncomputable def sdiffSet (X Y : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (sch_separation X (fun x => x ∉ Y))

theorem sdiffSet_spec (X Y : TarskiSet.{u}) :
    ∀ x, x ∈ sdiffSet X Y ↔ x ∈ X ∧ x ∉ Y :=
  Classical.choose_spec (sch_separation X (fun x => x ∉ Y))

@[simp] theorem sdiffSet_iff (X Y x : TarskiSet.{u}) :
    x ∈ sdiffSet X Y ↔ x ∈ X ∧ x ∉ Y :=
  sdiffSet_spec X Y x

noncomputable instance : SDiff TarskiSet.{u} where
  sdiff := sdiffSet

theorem def5 (X Y x : TarskiSet.{u}) : x ∈ X \ Y ↔ x ∈ X ∧ x ∉ Y :=
  sdiffSet_iff X Y x

/-! ## XBOOLE_0:def 6 — symmetric difference `X ∆ Y` -/

noncomputable def symmdiff (X Y : TarskiSet.{u}) : TarskiSet.{u} :=
  (X \ Y) ∪ (Y \ X)

theorem symmdiff_comm (X Y : TarskiSet.{u}) : symmdiff X Y = symmdiff Y X :=
  unionSet_comm (X \ Y) (Y \ X)

infixl:70 " ∆ " => symmdiff

theorem def6 (X Y : TarskiSet.{u}) : X ∆ Y = (X \ Y) ∪ (Y \ X) := rfl

/-! ## XBOOLE_0:def 7 — `X misses Y` -/

def misses (X Y : TarskiSet.{u}) : Prop := X ∩ Y = (∅ : TarskiSet.{u})

theorem misses_symm {X Y : TarskiSet.{u}} (h : misses X Y) : misses Y X :=
  (interSet_comm Y X).trans h

theorem def7 (X Y : TarskiSet.{u}) : misses X Y ↔ X ∩ Y = (∅ : TarskiSet.{u}) :=
  Iff.rfl

/-- Antonym `meets`. -/
def meets (X Y : TarskiSet.{u}) : Prop := ¬ misses X Y

theorem misses_of {X Y : TarskiSet.{u}} (h : ¬ meets X Y) : misses X Y :=
  Classical.not_not.mp h

/-! ## XBOOLE_0:def 8 — proper inclusion `X ⊂ Y` -/

def ssubset (X Y : TarskiSet.{u}) : Prop := X ⊆ Y ∧ X ≠ Y

instance instHasSSubset : HasSSubset TarskiSet.{u} where
  SSubset := ssubset

theorem def8 (X Y : TarskiSet.{u}) : X ⊂ Y ↔ X ⊆ Y ∧ X ≠ Y := Iff.rfl

theorem ssubset_irrefl (X : TarskiSet.{u}) : ¬ X ⊂ X := fun h => h.2 rfl

theorem ssubset_asymm {X Y : TarskiSet.{u}} (h : X ⊂ Y) : ¬ Y ⊂ X := by
  intro hYX
  have : ∀ x, x ∈ X ↔ x ∈ Y := fun x => ⟨h.1 x, hYX.1 x⟩
  exact h.2 (extensionality this)

/-! ## XBOOLE_0:def 9 — `c=`-comparable -/

def are_ccomparable (X Y : TarskiSet.{u}) : Prop := X ⊆ Y ∨ Y ⊆ X

theorem are_ccomparable_refl (X : TarskiSet.{u}) : are_ccomparable X X :=
  Or.inl (subset_refl X)

theorem are_ccomparable_symm {X Y : TarskiSet.{u}} (h : are_ccomparable X Y) :
    are_ccomparable Y X :=
  h.symm

theorem def9 (X Y : TarskiSet.{u}) : are_ccomparable X Y ↔ X ⊆ Y ∨ Y ⊆ X :=
  Iff.rfl

/-! ## XBOOLE_0:def 10 — equality via double inclusion -/

theorem eq_iff_subset {X Y : TarskiSet.{u}} : X = Y ↔ X ⊆ Y ∧ Y ⊆ X := by
  constructor
  · rintro rfl
    exact ⟨subset_refl _, subset_refl _⟩
  · intro ⟨hXY, hYX⟩
    exact extensionality fun x => ⟨hXY x, hYX x⟩

theorem def10 {X Y : TarskiSet.{u}} : X = Y ↔ X ⊆ Y ∧ Y ⊆ X :=
  eq_iff_subset

/-! ## Theorems -/

private theorem xor_of_not_iff {p q r : Prop} (h : ¬p ↔ (q ↔ r)) :
    p ↔ q ∧ ¬r ∨ r ∧ ¬q := by
  constructor
  · intro hp
    have niff : ¬ (q ↔ r) := fun hqr => h.mpr hqr hp
    by_cases hq : q
    · exact Or.inl ⟨hq, fun hr => niff ⟨fun _ => hr, fun _ => hq⟩⟩
    · have hr : r := Classical.byContradiction fun hr =>
        niff ⟨fun hq' => (hq hq').elim, fun hr' => (hr hr').elim⟩
      exact Or.inr ⟨hr, hq⟩
  · intro hxor
    have niff : ¬ (q ↔ r) := by
      cases hxor with
      | inl hqr => exact fun hiff => hqr.2 (hiff.mp hqr.1)
      | inr hrq => exact fun hiff => hrq.2 (hiff.mpr hrq.1)
    exact Classical.not_not.mp fun hp => niff (h.mp hp)

/-- `XBOOLE_0:1` -/
theorem th1 (X Y x : TarskiSet.{u}) :
    x ∈ X ∆ Y ↔ ¬ (x ∈ X ↔ x ∈ Y) := by
  have hmem : x ∈ X ∆ Y ↔ x ∈ X \ Y ∨ x ∈ Y \ X := def3 (X \ Y) (Y \ X) x
  constructor
  · intro h
    intro hiff
    cases hmem.mp h with
    | inl hx =>
      have ⟨hxX, hxY⟩ := (def5 X Y x).mp hx
      exact hxY (hiff.mp hxX)
    | inr hx =>
      have ⟨hxY, hxX⟩ := (def5 Y X x).mp hx
      exact hxX (hiff.mpr hxY)
  · intro h
    apply hmem.mpr
    by_cases hxX : x ∈ X
    · refine Or.inl ((def5 X Y x).mpr ⟨hxX, ?_⟩)
      intro hxY
      exact h ⟨fun _ => hxY, fun _ => hxX⟩
    · have hxY : x ∈ Y :=
        Classical.byContradiction fun hxY =>
          h ⟨fun hX => (hxX hX).elim, fun hY => (hxY hY).elim⟩
      exact Or.inr ((def5 Y X x).mpr ⟨hxY, hxX⟩)

/-- `XBOOLE_0:2` -/
theorem th2 {X Y Z : TarskiSet.{u}}
    (h : ∀ x, x ∉ X ↔ (x ∈ Y ↔ x ∈ Z)) : X = Y ∆ Z := by
  apply extensionality
  intro x
  have hchar : x ∈ X ↔ x ∈ Y ∧ x ∉ Z ∨ x ∈ Z ∧ x ∉ Y :=
    xor_of_not_iff (h x)
  exact hchar.trans <|
    (or_congr (def5 Y Z x).symm (def5 Z Y x).symm).trans
      (def3 (Y \ Z) (Z \ Y) x).symm

/-! ## Registrations -/

theorem emptySet_empty : isEmpty (∅ : TarskiSet.{u}) :=
  emptySet_isEmpty

theorem singleton_nonempty (x1 : TarskiSet.{u}) : ¬ isEmpty (TARSKI.singleton x1) :=
  fun h => h ⟨x1, (singleton_iff x1 x1).mpr rfl⟩

theorem upair_nonempty (x1 x2 : TarskiSet.{u}) : ¬ isEmpty (upair x1 x2) :=
  fun h => h ⟨x1, (upair_iff x1 x2 x1).mpr (Or.inl rfl)⟩

theorem nonempty_exists : ∃ X : TarskiSet.{u}, ¬ isEmpty X :=
  ⟨TARSKI.singleton theSet, singleton_nonempty theSet⟩

theorem union_nonempty_left {D X : TarskiSet.{u}} (hD : ¬ isEmpty D) :
    ¬ isEmpty (D ∪ X) := by
  obtain ⟨x, hx⟩ := Classical.not_not.mp hD
  exact fun hempty => hempty ⟨x, (def3 D X x).mpr (Or.inl hx)⟩

theorem union_nonempty_right {D X : TarskiSet.{u}} (hD : ¬ isEmpty D) :
    ¬ isEmpty (X ∪ D) := by
  rw [show X ∪ D = D ∪ X from unionSet_comm X D]
  exact union_nonempty_left hD

/-! ## `XBOOLE_0:3` and following -/

/-- `XBOOLE_0:3` (`Th3`). -/
theorem th3 (X Y : TarskiSet.{u}) : meets X Y ↔ ∃ x, x ∈ X ∧ x ∈ Y := by
  constructor
  · intro hmeets
    have hne : X ∩ Y ≠ (∅ : TarskiSet.{u}) := hmeets
    have hnotempty : ¬ isEmpty (X ∩ Y) := fun hempty => hne (empty_eq hempty)
    obtain ⟨x, hx⟩ := Classical.not_not.mp hnotempty
    exact ⟨x, (def4 X Y x).mp hx⟩
  · intro ⟨x, hxX, hxY⟩
    have hx : x ∈ X ∩ Y := (def4 X Y x).mpr ⟨hxX, hxY⟩
    intro hmiss
    have : isEmpty (X ∩ Y) := hmiss ▸ emptySet_isEmpty
    exact this ⟨x, hx⟩

/-- `XBOOLE_0:4` -/
theorem th4 (X Y : TarskiSet.{u}) : meets X Y ↔ ∃ x, x ∈ X ∩ Y := by
  constructor
  · intro hmeets
    have hne : X ∩ Y ≠ (∅ : TarskiSet.{u}) := hmeets
    have hnotempty : ¬ isEmpty (X ∩ Y) := fun hempty => hne (empty_eq hempty)
    obtain ⟨x, hx⟩ := Classical.not_not.mp hnotempty
    exact ⟨x, hx⟩
  · intro ⟨x, hx⟩
    intro hmiss
    have : isEmpty (X ∩ Y) := hmiss ▸ emptySet_isEmpty
    exact this ⟨x, hx⟩

/-- `XBOOLE_0:5` -/
theorem th5 {X Y x : TarskiSet.{u}} (hmiss : misses X Y) (hx : x ∈ X ∪ Y) :
    x ∈ X ∧ x ∉ Y ∨ x ∈ Y ∧ x ∉ X := by
  have hxy : ¬ (x ∈ X ∧ x ∈ Y) := by
    intro ⟨hxX, hxY⟩
    exact (th3 X Y).mpr ⟨x, hxX, hxY⟩ hmiss
  rcases (def3 X Y x).mp hx with hxX | hxY
  · exact Or.inl ⟨hxX, fun hxY => hxy ⟨hxX, hxY⟩⟩
  · exact Or.inr ⟨hxY, fun hxX => hxy ⟨hxX, hxY⟩⟩

/-! ## Schemes Extensionality and SetEq -/

theorem sch_extensionality {X Y : TarskiSet.{u}} {P : TarskiSet.{u} → Prop}
    (hX : ∀ x, x ∈ X ↔ P x) (hY : ∀ x, x ∈ Y ↔ P x) : X = Y :=
  extensionality fun x => (hX x).trans (hY x).symm

theorem sch_setEq {P : TarskiSet.{u} → Prop} {X1 X2 : TarskiSet.{u}}
    (h1 : ∀ x, x ∈ X1 ↔ P x) (h2 : ∀ x, x ∈ X2 ↔ P x) : X1 = X2 :=
  sch_extensionality h1 h2

/-! ## Addenda -/

private theorem exists_not_of_not_forall {α : Sort _} {P : α → Prop}
    (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
  Classical.byContradiction fun hex =>
    h fun x => Classical.byContradiction fun hx => hex ⟨x, hx⟩

/-- `XBOOLE_0:6` -/
theorem th6 {X Y : TarskiSet.{u}} (h : X ⊂ Y) : ∃ x, x ∈ Y ∧ x ∉ X := by
  have hne : ¬ ∀ x, x ∈ X ↔ x ∈ Y := fun hall => h.2 (extensionality hall)
  obtain ⟨x, hx⟩ := exists_not_of_not_forall hne
  have hxY : x ∈ Y :=
    Classical.byContradiction fun hxY =>
      hx ⟨fun hxX => (hxY (h.1 x hxX)).elim, fun hY => (hxY hY).elim⟩
  exact ⟨x, hxY, fun hxX => hx ⟨fun _ => hxY, fun _ => hxX⟩⟩

/-- `XBOOLE_0:7` -/
theorem th7 {X : TarskiSet.{u}} (h : X ≠ (∅ : TarskiSet.{u})) : ∃ x, x ∈ X :=
  Classical.byContradiction fun hex => h (empty_eq hex)

end XBOOLE_0
