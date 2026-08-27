import MizarCCL.ZFMISC_1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/subset_1.miz`.
Authors: Zinaida Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Properties of Subsets

1–1 Lean rendering of Mizar article `SUBSET_1`
(`vendor/mml/subset_1.miz`). `Element of X` is membership when `X`
is nonempty and the empty set when `X` is empty. `Subset of X` is
`Element of bool X`, which is `Y ⊆ X` because `bool X` is never
empty. Modes are predicates on `TarskiSet`, not Lean subtypes.
-/

universe u

open TarskiSet TARSKI

namespace SUBSET_1

variable {E X Y A B C x x1 x2 x3 x4 x5 x6 x7 x8 z : TarskiSet.{u}}

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

private theorem ne_empty_not_empty {X : TarskiSet.{u}}
    (h : X ≠ (∅ : TarskiSet.{u})) : ¬ XBOOLE_0.isEmpty X :=
  fun he => h (XBOOLE_0.empty_eq he)

private theorem not_empty_ne {X : TarskiSet.{u}}
    (h : ¬ XBOOLE_0.isEmpty X) : X ≠ (∅ : TarskiSet.{u}) :=
  fun he => h (he ▸ XBOOLE_0.emptySet_isEmpty)

private theorem empty_union (X : TarskiSet.{u}) :
    (∅ : TarskiSet.{u}) ∪ X = X :=
  XBOOLE_1.th12 (X := (∅ : TarskiSet.{u})) (Y := X) XBOOLE_1.th2

private theorem diff_empty (X : TarskiSet.{u}) :
    X \ (∅ : TarskiSet.{u}) = X :=
  eq_of_mem fun x =>
    (XBOOLE_0.def5 X ∅ x).trans
      ⟨And.left, fun hx => ⟨hx, fun h => (XBOOLE_0.empty_iff x).mp h⟩⟩

private theorem diff_self (X : TarskiSet.{u}) :
    X \ X = (∅ : TarskiSet.{u}) :=
  (XBOOLE_1.th37 (X := X) (Y := X)).mpr (subset_refl X)

private theorem not_iff_xor {p q : Prop} : ¬ (p ↔ q) ↔ p ∧ ¬q ∨ q ∧ ¬p := by
  constructor
  · intro h
    by_cases hp : p
    · exact Or.inl ⟨hp, fun hq => h ⟨fun _ => hq, fun _ => hp⟩⟩
    · have hq : q := Classical.byContradiction fun hq =>
        h ⟨fun hp' => (hp hp').elim, fun hq' => (hq hq').elim⟩
      exact Or.inr ⟨hq, hp⟩
  · intro h hiff
    cases h with
    | inl hpq => exact hpq.2 (hiff.mp hpq.1)
    | inr hqp => exact hqp.2 (hiff.mpr hqp.1)

private theorem misses_not_mem {A B x : TarskiSet.{u}}
    (h : XBOOLE_0.misses A B) (hx : x ∈ A) : x ∉ B :=
  fun hxB =>
    (XBOOLE_0.empty_iff x).mp
      (h ▸ (XBOOLE_0.def4 A B x).mpr ⟨hx, hxB⟩)

/-! ## Registrations: `bool` and enumerations are nonempty -/

theorem bool_nonempty (X : TarskiSet.{u}) :
    ¬ XBOOLE_0.isEmpty (ZFMISC_1.bool X) :=
  fun he => he ⟨∅, (ZFMISC_1.def1 X ∅).mpr XBOOLE_1.th2⟩

theorem enumset3_nonempty (x1 x2 x3 : TarskiSet.{u}) :
    ¬ XBOOLE_0.isEmpty (ENUMSET1.enumset3 x1 x2 x3) :=
  fun h => h ⟨x1, (ENUMSET1.def1 x1 x2 x3 x1).mpr (Or.inl rfl)⟩

theorem enumset4_nonempty (x1 x2 x3 x4 : TarskiSet.{u}) :
    ¬ XBOOLE_0.isEmpty (ENUMSET1.enumset4 x1 x2 x3 x4) :=
  fun h => h ⟨x1, (ENUMSET1.def2 x1 x2 x3 x4 x1).mpr (Or.inl rfl)⟩

theorem enumset5_nonempty (x1 x2 x3 x4 x5 : TarskiSet.{u}) :
    ¬ XBOOLE_0.isEmpty (ENUMSET1.enumset5 x1 x2 x3 x4 x5) :=
  fun h => h ⟨x1, (ENUMSET1.def3 x1 x2 x3 x4 x5 x1).mpr (Or.inl rfl)⟩

theorem enumset6_nonempty (x1 x2 x3 x4 x5 x6 : TarskiSet.{u}) :
    ¬ XBOOLE_0.isEmpty (ENUMSET1.enumset6 x1 x2 x3 x4 x5 x6) :=
  fun h => h ⟨x1, (ENUMSET1.def4 x1 x2 x3 x4 x5 x6 x1).mpr (Or.inl rfl)⟩

theorem enumset7_nonempty (x1 x2 x3 x4 x5 x6 x7 : TarskiSet.{u}) :
    ¬ XBOOLE_0.isEmpty (ENUMSET1.enumset7 x1 x2 x3 x4 x5 x6 x7) :=
  fun h => h ⟨x1, (ENUMSET1.def5 x1 x2 x3 x4 x5 x6 x7 x1).mpr (Or.inl rfl)⟩

theorem enumset8_nonempty (x1 x2 x3 x4 x5 x6 x7 x8 : TarskiSet.{u}) :
    ¬ XBOOLE_0.isEmpty (ENUMSET1.enumset8 x1 x2 x3 x4 x5 x6 x7 x8) :=
  fun h => h ⟨x1, (ENUMSET1.def6 x1 x2 x3 x4 x5 x6 x7 x8 x1).mpr (Or.inl rfl)⟩

theorem enumset9_nonempty (x1 x2 x3 x4 x5 x6 x7 x8 x9 : TarskiSet.{u}) :
    ¬ XBOOLE_0.isEmpty (ENUMSET1.enumset9 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
  fun h => h ⟨x1, (ENUMSET1.def7 x1 x2 x3 x4 x5 x6 x7 x8 x9 x1).mpr (Or.inl rfl)⟩

theorem enumset10_nonempty
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : TarskiSet.{u}) :
    ¬ XBOOLE_0.isEmpty
        (ENUMSET1.enumset10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
  fun h => h ⟨x1, (ENUMSET1.def8 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x1).mpr
    (Or.inl rfl)⟩

/-! ## `Element of X` (`SUBSET_1:def 1`) -/

/-- Mizar `Element of X`: membership if `X` is nonempty, otherwise
the empty set. Not a Lean subtype (the empty case would be uninhabited). -/
def isElement (x X : TarskiSet.{u}) : Prop :=
  XBOOLE_0.isEmpty X ∧ XBOOLE_0.isEmpty x ∨
    ¬ XBOOLE_0.isEmpty X ∧ x ∈ X

theorem def1 (x X : TarskiSet.{u}) :
    isElement x X ↔
      XBOOLE_0.isEmpty X ∧ XBOOLE_0.isEmpty x ∨
        ¬ XBOOLE_0.isEmpty X ∧ x ∈ X :=
  Iff.rfl

theorem isElement_of {x X : TarskiSet.{u}} (hx : x ∈ X) : isElement x X :=
  Or.inr ⟨fun he => he ⟨x, hx⟩, hx⟩

theorem isElement_mem {x X : TarskiSet.{u}} (hne : ¬ XBOOLE_0.isEmpty X)
    (h : isElement x X) : x ∈ X :=
  h.elim (fun ⟨he, _⟩ => (hne he).elim) And.right

theorem isElement_iff_mem {x X : TarskiSet.{u}}
    (hne : ¬ XBOOLE_0.isEmpty X) : isElement x X ↔ x ∈ X :=
  ⟨isElement_mem hne, isElement_of⟩

theorem isElement_iff_empty {x X : TarskiSet.{u}}
    (he : XBOOLE_0.isEmpty X) : isElement x X ↔ XBOOLE_0.isEmpty x :=
  ⟨fun h => h.elim And.right (fun ⟨hne, _⟩ => (hne he).elim),
    fun hx => Or.inl ⟨he, hx⟩⟩

theorem def1_exists (X : TarskiSet.{u}) : ∃ x, isElement x X := by
  by_cases h : XBOOLE_0.isEmpty X
  · exact ⟨∅, Or.inl ⟨h, XBOOLE_0.emptySet_isEmpty⟩⟩
  · obtain ⟨x, hx⟩ := Classical.not_not.mp h
    exact ⟨x, isElement_of hx⟩

/-! ## `Subset of X` is `Element of bool X` -/

def isSubset (Y X : TarskiSet.{u}) : Prop := Y ⊆ X

theorem isSubset_iff_element (Y X : TarskiSet.{u}) :
    isSubset Y X ↔ isElement Y (ZFMISC_1.bool X) :=
  (ZFMISC_1.def1 X Y).symm.trans (isElement_iff_mem (bool_nonempty X)).symm

theorem nonempty_subset_exists {X : TarskiSet.{u}}
    (hX : ¬ XBOOLE_0.isEmpty X) :
    ∃ A, isSubset A X ∧ ¬ XBOOLE_0.isEmpty A :=
  ⟨X, subset_refl X, hX⟩

theorem product_nonempty {X Y : TarskiSet.{u}}
    (hX : ¬ XBOOLE_0.isEmpty X) (hY : ¬ XBOOLE_0.isEmpty Y) :
    ¬ XBOOLE_0.isEmpty (ZFMISC_1.product X Y) := by
  obtain ⟨x, hx⟩ := Classical.not_not.mp hX
  obtain ⟨y, hy⟩ := Classical.not_not.mp hY
  exact fun he =>
    he ⟨TARSKI.pair x y,
      (ZFMISC_1.def2 X Y (TARSKI.pair x y)).mpr ⟨x, y, hx, hy, rfl⟩⟩

theorem product3_nonempty {X Y Z : TarskiSet.{u}}
    (hX : ¬ XBOOLE_0.isEmpty X) (hY : ¬ XBOOLE_0.isEmpty Y)
    (hZ : ¬ XBOOLE_0.isEmpty Z) :
    ¬ XBOOLE_0.isEmpty (ZFMISC_1.product3 X Y Z) :=
  product_nonempty (product_nonempty hX hY) hZ

theorem product4_nonempty {X1 X2 X3 X4 : TarskiSet.{u}}
    (h1 : ¬ XBOOLE_0.isEmpty X1) (h2 : ¬ XBOOLE_0.isEmpty X2)
    (h3 : ¬ XBOOLE_0.isEmpty X3) (h4 : ¬ XBOOLE_0.isEmpty X4) :
    ¬ XBOOLE_0.isEmpty (ZFMISC_1.product4 X1 X2 X3 X4) :=
  product_nonempty (product3_nonempty h1 h2 h3) h4

theorem element_of_subset {D X x : TarskiSet.{u}}
    (hX : isSubset X D) (hXne : ¬ XBOOLE_0.isEmpty X)
    (hx : isElement x X) : isElement x D :=
  isElement_of (hX x (isElement_mem hXne hx))

/-- `Lm1`. -/
theorem lm1 {E X x : TarskiSet.{u}} (hX : isSubset X E) (hx : x ∈ X) :
    x ∈ E :=
  hX x hx

theorem empty_subset_exists (E : TarskiSet.{u}) :
    ∃ A, isSubset A E ∧ XBOOLE_0.isEmpty A :=
  ⟨∅, XBOOLE_1.th2, XBOOLE_0.emptySet_isEmpty⟩

/-! ## `{}E` and `[#] E` -/

noncomputable def emptyOf (_E : TarskiSet.{u}) : TarskiSet.{u} := ∅

theorem emptyOf_isSubset (E : TarskiSet.{u}) : isSubset (emptyOf E) E :=
  XBOOLE_1.th2

theorem emptyOf_empty (E : TarskiSet.{u}) : XBOOLE_0.isEmpty (emptyOf E) :=
  XBOOLE_0.emptySet_isEmpty

def hash (E : TarskiSet.{u}) : TarskiSet.{u} := E

theorem hash_isSubset (E : TarskiSet.{u}) : isSubset (hash E) E :=
  subset_refl E

/-- `SUBSET_1:1` -/
theorem th1 : isSubset (∅ : TarskiSet.{u}) X :=
  emptyOf_isSubset X

/-- `SUBSET_1:2` (`Th2`) -/
theorem th2 {E A B : TarskiSet.{u}} (hA : isSubset A E)
    (h : ∀ x, isElement x E → x ∈ A → x ∈ B) : A ⊆ B :=
  fun x hxA => h x (isElement_of (lm1 hA hxA)) hxA

/-- `SUBSET_1:3` (`Th3`) -/
theorem th3 {E A B : TarskiSet.{u}} (hA : isSubset A E) (hB : isSubset B E)
    (h : ∀ x, isElement x E → (x ∈ A ↔ x ∈ B)) : A = B :=
  XBOOLE_0.eq_iff_subset.mpr
    ⟨th2 hA fun x hxE hxA => (h x hxE).mp hxA,
      th2 hB fun x hxE hxB => (h x hxE).mpr hxB⟩

/-- `SUBSET_1:4` (`Th4`) -/
theorem th4 {E A : TarskiSet.{u}} (hA : isSubset A E)
    (hne : A ≠ (∅ : TarskiSet.{u})) :
    ∃ x, isElement x E ∧ x ∈ A := by
  obtain ⟨x, hx⟩ := XBOOLE_0.th7 hne
  exact ⟨x, isElement_of (lm1 hA hx), hx⟩

/-! ## Complement `A\`` and Boolean closure of subsets -/

noncomputable def compl (E A : TarskiSet.{u}) : TarskiSet.{u} := E \ A

theorem compl_isSubset (E A : TarskiSet.{u}) : isSubset (compl E A) E :=
  XBOOLE_1.th36

theorem compl_involutive {E A : TarskiSet.{u}} (hA : isSubset A E) :
    compl E (compl E A) = A := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    have ⟨hxE, hxnot⟩ := (XBOOLE_0.def5 E (E \ A) x).mp hx
    have : ¬ (x ∈ E ∧ x ∉ A) :=
      fun h => hxnot ((XBOOLE_0.def5 E A x).mpr h)
    by_cases hxA : x ∈ A
    · exact hxA
    · exact (this ⟨hxE, hxA⟩).elim
  · intro hxA
    exact (XBOOLE_0.def5 E (E \ A) x).mpr
      ⟨hA x hxA, fun hxEA => ((XBOOLE_0.def5 E A x).mp hxEA).2 hxA⟩

theorem union_isSubset {E A B : TarskiSet.{u}}
    (hA : isSubset A E) (hB : isSubset B E) : isSubset (A ∪ B) E :=
  XBOOLE_1.th8 hA hB

theorem symdiff_isSubset {E A B : TarskiSet.{u}}
    (hA : isSubset A E) (hB : isSubset B E) : isSubset (A ∆ B) E :=
  XBOOLE_1.th8 (XBOOLE_1.th1 XBOOLE_1.th36 hA)
    (XBOOLE_1.th1 XBOOLE_1.th36 hB)

theorem diff_isSubset_of (X Y : TarskiSet.{u}) : isSubset (X \ Y) X :=
  XBOOLE_1.th36

theorem diff_isSubset {E A X : TarskiSet.{u}} (hA : isSubset A E) :
    isSubset (A \ X) E :=
  XBOOLE_1.th1 XBOOLE_1.th36 hA

theorem inter_isSubset {E A X : TarskiSet.{u}} (hA : isSubset A E) :
    isSubset (A ∩ X) E :=
  XBOOLE_1.th1 XBOOLE_1.th17 hA

theorem inter_isSubset' {E A X : TarskiSet.{u}} (hA : isSubset A E) :
    isSubset (X ∩ A) E :=
  XBOOLE_0.inter_comm X A ▸ inter_isSubset hA

/-- `SUBSET_1:5` -/
theorem th5 {E A B C : TarskiSet.{u}} (hA : isSubset A E)
    (hB : isSubset B E) (hC : isSubset C E)
    (h : ∀ x, isElement x E → (x ∈ A ↔ x ∈ B ∨ x ∈ C)) :
    A = B ∪ C := by
  have hBC : isSubset (B ∪ C) E := union_isSubset hB hC
  refine th3 hA hBC fun x hx => ?_
  constructor
  · intro hxA
    exact (XBOOLE_0.def3 B C x).mpr ((h x hx).mp hxA)
  · intro hxU
    exact (h x hx).mpr ((XBOOLE_0.def3 B C x).mp hxU)

/-- `SUBSET_1:6` -/
theorem th6 {E A B C : TarskiSet.{u}} (hA : isSubset A E)
    (hB : isSubset B E) (_hC : isSubset C E)
    (h : ∀ x, isElement x E → (x ∈ A ↔ x ∈ B ∧ x ∈ C)) :
    A = B ∩ C := by
  have hBC : isSubset (B ∩ C) E := inter_isSubset hB
  refine th3 hA hBC fun x hx => ?_
  constructor
  · intro hxA
    exact (XBOOLE_0.def4 B C x).mpr ((h x hx).mp hxA)
  · intro hxI
    exact (h x hx).mpr ((XBOOLE_0.def4 B C x).mp hxI)

/-- `SUBSET_1:7` -/
theorem th7 {E A B C : TarskiSet.{u}} (hA : isSubset A E)
    (hB : isSubset B E)
    (h : ∀ x, isElement x E → (x ∈ A ↔ x ∈ B ∧ x ∉ C)) :
    A = B \ C := by
  have hBC : isSubset (B \ C) E := diff_isSubset hB
  refine th3 hA hBC fun x hx => ?_
  constructor
  · intro hxA
    exact (XBOOLE_0.def5 B C x).mpr ((h x hx).mp hxA)
  · intro hxD
    exact (h x hx).mpr ((XBOOLE_0.def5 B C x).mp hxD)

/-- `SUBSET_1:8` -/
theorem th8 {E A B C : TarskiSet.{u}} (hA : isSubset A E)
    (hB : isSubset B E) (hC : isSubset C E)
    (h : ∀ x, isElement x E → (x ∈ A ↔ ¬ (x ∈ B ↔ x ∈ C))) :
    A = B ∆ C := by
  have hBC : isSubset (B ∆ C) E := symdiff_isSubset hB hC
  refine th3 hA hBC fun x hx => ?_
  constructor
  · intro hxA
    have hxor := (not_iff_xor.mp ((h x hx).mp hxA))
    have hmem :=
      hxor.elim
        (fun hb => Or.inl ((XBOOLE_0.def5 B C x).mpr hb))
        (fun hc => Or.inr ((XBOOLE_0.def5 C B x).mpr hc))
    exact (XBOOLE_0.def3 (B \ C) (C \ B) x).mpr hmem
  · intro hxD
    apply (h x hx).mpr
    have hmem := (XBOOLE_0.def3 (B \ C) (C \ B) x).mp hxD
    have hxor : x ∈ B ∧ x ∉ C ∨ x ∈ C ∧ x ∉ B :=
      hmem.elim
        (fun hd => Or.inl ((XBOOLE_0.def5 B C x).mp hd))
        (fun hd => Or.inr ((XBOOLE_0.def5 C B x).mp hd))
    exact not_iff_xor.mpr hxor

/-- `SUBSET_1:9` -/
theorem th9 : hash E = compl E (emptyOf E) :=
  (diff_empty E).symm

/-- `SUBSET_1:10` (`Th10`) -/
theorem th10 {E A : TarskiSet.{u}} (hA : isSubset A E) :
    A ∪ compl E A = hash E :=
  (XBOOLE_1.th45 (X := A) (Y := E) hA).symm

/-- `SUBSET_1:11` -/
theorem th11 {E A : TarskiSet.{u}} (hA : isSubset A E) :
    A ∪ hash E = hash E :=
  XBOOLE_1.th12 (X := A) (Y := E) hA

/-- `SUBSET_1:12` (`Th12`) -/
theorem th12 {E A B : TarskiSet.{u}} (hA : isSubset A E) (hB : isSubset B E) :
    A ⊆ B ↔ compl E B ⊆ compl E A := by
  constructor
  · intro h
    exact XBOOLE_1.th34 (X := A) (Y := B) (Z := E) h
  · intro h
    have hB' : compl E (compl E B) = B := compl_involutive hB
    have hA' : compl E (compl E A) = A := compl_involutive hA
    exact hA' ▸ hB' ▸ XBOOLE_1.th34 (X := compl E B) (Y := compl E A) (Z := E) h

/-- `SUBSET_1:13` -/
theorem th13 {E A B : TarskiSet.{u}} (hA : isSubset A E) :
    A \ B = A ∩ compl E B := by
  have h1 : A ∩ compl E B = (A ∩ E) \ B :=
    XBOOLE_1.th49 (X := A) (Y := E) (Z := B)
  have h2 : A ∩ E = A := XBOOLE_1.th28 (X := A) (Y := E) hA
  exact (h2 ▸ h1).symm

/-- `SUBSET_1:14` -/
theorem th14 {E A B : TarskiSet.{u}} (hB : isSubset B E) :
    compl E (A \ B) = compl E A ∪ B := by
  have h1 : compl E (A \ B) = (E \ A) ∪ (E ∩ B) :=
    XBOOLE_1.th52 (X := E) (Y := A) (Z := B)
  have h2 : E ∩ B = B :=
    (XBOOLE_0.inter_comm E B).trans (XBOOLE_1.th28 (X := B) (Y := E) hB)
  exact h1.trans (congrArg (fun s => (E \ A) ∪ s) h2)

/-- `SUBSET_1:15` -/
theorem th15 {E A B : TarskiSet.{u}} (hA : isSubset A E) (_hB : isSubset B E) :
    compl E (A ∆ B) = A ∩ B ∪ compl E A ∩ compl E B := by
  have h102 : E \ (A ∆ B) =
      (E \ (A ∪ B)) ∪ (E ∩ A ∩ B) :=
    XBOOLE_1.th102 (X := E) (Y := A) (Z := B)
  have hEA : E ∩ A = A :=
    (XBOOLE_0.inter_comm E A).trans (XBOOLE_1.th28 (X := A) (Y := E) hA)
  have hcap : E ∩ A ∩ B = A ∩ B := by
    have : (E ∩ A) ∩ B = A ∩ B := congrArg (fun s => s ∩ B) hEA
    exact this
  have h53 : E \ (A ∪ B) = (E \ A) ∩ (E \ B) :=
    XBOOLE_1.th53 (X := E) (Y := A) (Z := B)
  have hcomm : (E \ (A ∪ B)) ∪ (A ∩ B) = (A ∩ B) ∪ (E \ (A ∪ B)) :=
    XBOOLE_0.union_comm _ _
  exact (h102.trans (hcap ▸ rfl)).trans (hcomm.trans (h53 ▸ rfl))

/-- `SUBSET_1:16` -/
theorem th16 {E A B : TarskiSet.{u}} (hA : isSubset A E) (hB : isSubset B E)
    (h : A ⊆ compl E B) : B ⊆ compl E A :=
  (compl_involutive hB) ▸ (th12 hA (compl_isSubset E B)).mp h

/-- `SUBSET_1:17` -/
theorem th17 {E A B : TarskiSet.{u}} (hA : isSubset A E) (hB : isSubset B E)
    (h : compl E A ⊆ B) : compl E B ⊆ A :=
  (compl_involutive hA) ▸ (th12 (compl_isSubset E A) hB).mp h

/-- `SUBSET_1:18` -/
theorem th18 {E A : TarskiSet.{u}} (_hA : isSubset A E) :
    A ⊆ compl E A ↔ A = emptyOf E := by
  constructor
  · intro h
    exact XBOOLE_1.th38 (X := A) (Y := E) h
  · intro h
    exact h ▸ XBOOLE_1.th2

/-- `SUBSET_1:19` -/
theorem th19 {E A : TarskiSet.{u}} (hA : isSubset A E) :
    compl E A ⊆ A ↔ A = hash E := by
  constructor
  · intro h
    have hunion : A ∪ compl E A = A :=
      (XBOOLE_0.union_comm A (compl E A)).trans
        (XBOOLE_1.th12 (X := compl E A) (Y := A) h)
    exact hunion.symm.trans (th10 hA)
  · intro h
    have : compl E A = (∅ : TarskiSet.{u}) :=
      h ▸ diff_self E
    exact this ▸ XBOOLE_1.th2

/-- `SUBSET_1:20` -/
theorem th20 {E A X : TarskiSet.{u}} (_hA : isSubset A E)
    (h1 : X ⊆ A) (h2 : X ⊆ compl E A) : X = (∅ : TarskiSet.{u}) :=
  XBOOLE_1.th67 (X := X) (Y := A) (Z := compl E A) h1 h2
    (XBOOLE_0.misses_symm (XBOOLE_1.th79 (X := E) (Y := A)))

/-- `SUBSET_1:21` -/
theorem th21 {E A B : TarskiSet.{u}} (hA : isSubset A E) (hB : isSubset B E) :
    compl E (A ∪ B) ⊆ compl E A :=
  (th12 hA (union_isSubset hA hB)).mp XBOOLE_1.th7

/-- `SUBSET_1:22` -/
theorem th22 {E A B : TarskiSet.{u}} (hA : isSubset A E) (_hB : isSubset B E) :
    compl E A ⊆ compl E (A ∩ B) :=
  (th12 (inter_isSubset hA) hA).mp XBOOLE_1.th17

/-- `SUBSET_1:23` (`Th23`) -/
theorem th23 {E A B : TarskiSet.{u}} (hA : isSubset A E) (_hB : isSubset B E) :
    XBOOLE_0.misses A B ↔ A ⊆ compl E B := by
  constructor
  · intro hmiss x hxA
    exact (XBOOLE_0.def5 E B x).mpr ⟨lm1 hA hxA, misses_not_mem hmiss hxA⟩
  · intro hsub
    refine XBOOLE_0.empty_eq fun ⟨x, hx⟩ => ?_
    have ⟨hxA, hxB⟩ := (XBOOLE_0.def4 A B x).mp hx
    exact ((XBOOLE_0.def5 E B x).mp (hsub x hxA)).2 hxB

/-- `SUBSET_1:24` -/
theorem th24 {E A B : TarskiSet.{u}} (hA : isSubset A E) (hB : isSubset B E) :
    XBOOLE_0.misses A (compl E B) ↔ A ⊆ B :=
  (th23 hA (compl_isSubset E B)).trans
    (Iff.of_eq (congrArg (fun s => A ⊆ s) (compl_involutive hB)))

/-- `SUBSET_1:25` -/
theorem th25 {E A B : TarskiSet.{u}} (hA : isSubset A E) (hB : isSubset B E)
    (h1 : XBOOLE_0.misses A B)
    (h2 : XBOOLE_0.misses (compl E A) (compl E B)) : A = compl E B := by
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · exact (th23 hA hB).mp h1
  · intro x hxB'
    have hxE : x ∈ E := (XBOOLE_0.def5 E B x).mp hxB' |>.1
    have hxA' : x ∉ compl E A := misses_not_mem (XBOOLE_0.misses_symm h2) hxB'
    have : ¬ (x ∈ E ∧ x ∉ A) :=
      fun h => hxA' ((XBOOLE_0.def5 E A x).mpr h)
    by_cases hxA : x ∈ A
    · exact hxA
    · exact (this ⟨hxE, hxA⟩).elim

/-- `SUBSET_1:26` -/
theorem th26 {E A B C : TarskiSet.{u}} (hA : isSubset A E)
    (_hB : isSubset B E) (hC : isSubset C E)
    (hAB : A ⊆ B) (hmiss : XBOOLE_0.misses C B) : A ⊆ compl E C :=
  (th23 hA hC).mp (XBOOLE_1.th63 (X := A) (Y := B) (Z := C) hAB
    (XBOOLE_0.misses_symm hmiss))

/-! ## Additional theorems -/

/-- `SUBSET_1:27` -/
theorem th27 {A B : TarskiSet.{u}}
    (h : ∀ a, isElement a A → a ∈ B) : A ⊆ B :=
  fun a ha => h a (isElement_of ha)

/-- `SUBSET_1:28` -/
theorem th28 {E A : TarskiSet.{u}} (hA : isSubset A E)
    (h : ∀ x, isElement x E → x ∈ A) : E = A :=
  XBOOLE_0.eq_iff_subset.mpr
    ⟨fun a ha => h a (isElement_of ha), hA⟩

/-- `SUBSET_1:29` -/
theorem th29 {E B x : TarskiSet.{u}} (hne : E ≠ (∅ : TarskiSet.{u}))
    (hx : isElement x E) (h : x ∉ B) : x ∈ compl E B :=
  (XBOOLE_0.def5 E B x).mpr ⟨isElement_mem (ne_empty_not_empty hne) hx, h⟩

/-- `SUBSET_1:30` (`Th30`) -/
theorem th30 {E A B : TarskiSet.{u}} (hA : isSubset A E) (_hB : isSubset B E)
    (h : ∀ x, isElement x E → (x ∈ A ↔ x ∉ B)) : A = compl E B := by
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro x hxA
    have hxE : x ∈ E := lm1 hA hxA
    have hxB : x ∉ B := (h x (isElement_of hxE)).mp hxA
    exact (XBOOLE_0.def5 E B x).mpr ⟨hxE, hxB⟩
  · intro x hx
    have hxE : x ∈ E := (XBOOLE_0.def5 E B x).mp hx |>.1
    have hxB : x ∉ B := (XBOOLE_0.def5 E B x).mp hx |>.2
    exact (h x (isElement_of hxE)).mpr hxB

/-- `SUBSET_1:31` -/
theorem th31 {E A B : TarskiSet.{u}} (hA : isSubset A E) (hB : isSubset B E)
    (h : ∀ x, isElement x E → (x ∉ A ↔ x ∈ B)) : A = compl E B :=
  th30 hA hB fun x hx =>
    ⟨fun hxA hxB => (h x hx).mpr hxB hxA,
      fun hxB => Classical.byContradiction fun hnot =>
        hxB ((h x hx).mp hnot)⟩

/-- `SUBSET_1:32` -/
theorem th32 {E A B : TarskiSet.{u}} (hA : isSubset A E) (hB : isSubset B E)
    (h : ∀ x, isElement x E → ¬ (x ∈ A ↔ x ∈ B)) : A = compl E B :=
  th30 hA hB fun x hx =>
    ⟨fun hxA hxB => h x hx ⟨fun _ => hxB, fun _ => hxA⟩,
      fun hxB => Classical.byContradiction fun hxA =>
        h x hx ⟨fun hA => (hxA hA).elim, fun hB => (hxB hB).elim⟩⟩

/-- `SUBSET_1:33` -/
theorem th33 {X x1 : TarskiSet.{u}} (hne : X ≠ (∅ : TarskiSet.{u}))
    (h1 : isElement x1 X) : isSubset (TARSKI.singleton x1) X :=
  (ZFMISC_1.th31 (x := x1) (X := X)).mpr
    (isElement_mem (ne_empty_not_empty hne) h1)

/-- `SUBSET_1:34` -/
theorem th34 {X x1 x2 : TarskiSet.{u}} (hne : X ≠ (∅ : TarskiSet.{u}))
    (h1 : isElement x1 X) (h2 : isElement x2 X) :
    isSubset (upair x1 x2) X := by
  have hx1 := isElement_mem (ne_empty_not_empty hne) h1
  have hx2 := isElement_mem (ne_empty_not_empty hne) h2
  intro x hx
  rcases (upair_iff x1 x2 x).mp hx with h | h
  · exact h ▸ hx1
  · exact h ▸ hx2

/-- `SUBSET_1:35` -/
theorem th35 {X x1 x2 x3 : TarskiSet.{u}} (hne : X ≠ (∅ : TarskiSet.{u}))
    (h1 : isElement x1 X) (h2 : isElement x2 X) (h3 : isElement x3 X) :
    isSubset (ENUMSET1.enumset3 x1 x2 x3) X := by
  have hx1 := isElement_mem (ne_empty_not_empty hne) h1
  have hx2 := isElement_mem (ne_empty_not_empty hne) h2
  have hx3 := isElement_mem (ne_empty_not_empty hne) h3
  intro x hx
  rcases (ENUMSET1.def1 x1 x2 x3 x).mp hx with h | h | h
  · exact h ▸ hx1
  · exact h ▸ hx2
  · exact h ▸ hx3

/-- `SUBSET_1:36` -/
theorem th36 {X x1 x2 x3 x4 : TarskiSet.{u}}
    (hne : X ≠ (∅ : TarskiSet.{u}))
    (h1 : isElement x1 X) (h2 : isElement x2 X)
    (h3 : isElement x3 X) (h4 : isElement x4 X) :
    isSubset (ENUMSET1.enumset4 x1 x2 x3 x4) X := by
  have nE := ne_empty_not_empty hne
  have hx1 := isElement_mem nE h1
  have hx2 := isElement_mem nE h2
  have hx3 := isElement_mem nE h3
  have hx4 := isElement_mem nE h4
  intro x hx
  rcases (ENUMSET1.def2 x1 x2 x3 x4 x).mp hx with h | h | h | h
  · exact h ▸ hx1
  · exact h ▸ hx2
  · exact h ▸ hx3
  · exact h ▸ hx4

/-- `SUBSET_1:37` -/
theorem th37 {X x1 x2 x3 x4 x5 : TarskiSet.{u}}
    (hne : X ≠ (∅ : TarskiSet.{u}))
    (h1 : isElement x1 X) (h2 : isElement x2 X) (h3 : isElement x3 X)
    (h4 : isElement x4 X) (h5 : isElement x5 X) :
    isSubset (ENUMSET1.enumset5 x1 x2 x3 x4 x5) X := by
  have nE := ne_empty_not_empty hne
  intro x hx
  rcases (ENUMSET1.def3 x1 x2 x3 x4 x5 x).mp hx with h | h | h | h | h
  · exact h ▸ isElement_mem nE h1
  · exact h ▸ isElement_mem nE h2
  · exact h ▸ isElement_mem nE h3
  · exact h ▸ isElement_mem nE h4
  · exact h ▸ isElement_mem nE h5

/-- `SUBSET_1:38` -/
theorem th38 {X x1 x2 x3 x4 x5 x6 : TarskiSet.{u}}
    (hne : X ≠ (∅ : TarskiSet.{u}))
    (h1 : isElement x1 X) (h2 : isElement x2 X) (h3 : isElement x3 X)
    (h4 : isElement x4 X) (h5 : isElement x5 X) (h6 : isElement x6 X) :
    isSubset (ENUMSET1.enumset6 x1 x2 x3 x4 x5 x6) X := by
  have nE := ne_empty_not_empty hne
  intro x hx
  rcases (ENUMSET1.def4 x1 x2 x3 x4 x5 x6 x).mp hx with
    h | h | h | h | h | h
  · exact h ▸ isElement_mem nE h1
  · exact h ▸ isElement_mem nE h2
  · exact h ▸ isElement_mem nE h3
  · exact h ▸ isElement_mem nE h4
  · exact h ▸ isElement_mem nE h5
  · exact h ▸ isElement_mem nE h6

/-- `SUBSET_1:39` -/
theorem th39 {X x1 x2 x3 x4 x5 x6 x7 : TarskiSet.{u}}
    (hne : X ≠ (∅ : TarskiSet.{u}))
    (h1 : isElement x1 X) (h2 : isElement x2 X) (h3 : isElement x3 X)
    (h4 : isElement x4 X) (h5 : isElement x5 X) (h6 : isElement x6 X)
    (h7 : isElement x7 X) :
    isSubset (ENUMSET1.enumset7 x1 x2 x3 x4 x5 x6 x7) X := by
  have nE := ne_empty_not_empty hne
  intro x hx
  rcases (ENUMSET1.def5 x1 x2 x3 x4 x5 x6 x7 x).mp hx with
    h | h | h | h | h | h | h
  · exact h ▸ isElement_mem nE h1
  · exact h ▸ isElement_mem nE h2
  · exact h ▸ isElement_mem nE h3
  · exact h ▸ isElement_mem nE h4
  · exact h ▸ isElement_mem nE h5
  · exact h ▸ isElement_mem nE h6
  · exact h ▸ isElement_mem nE h7

/-- `SUBSET_1:40` -/
theorem th40 {X x1 x2 x3 x4 x5 x6 x7 x8 : TarskiSet.{u}}
    (hne : X ≠ (∅ : TarskiSet.{u}))
    (h1 : isElement x1 X) (h2 : isElement x2 X) (h3 : isElement x3 X)
    (h4 : isElement x4 X) (h5 : isElement x5 X) (h6 : isElement x6 X)
    (h7 : isElement x7 X) (h8 : isElement x8 X) :
    isSubset (ENUMSET1.enumset8 x1 x2 x3 x4 x5 x6 x7 x8) X := by
  have nE := ne_empty_not_empty hne
  intro x hx
  rcases (ENUMSET1.def6 x1 x2 x3 x4 x5 x6 x7 x8 x).mp hx with
    h | h | h | h | h | h | h | h
  · exact h ▸ isElement_mem nE h1
  · exact h ▸ isElement_mem nE h2
  · exact h ▸ isElement_mem nE h3
  · exact h ▸ isElement_mem nE h4
  · exact h ▸ isElement_mem nE h5
  · exact h ▸ isElement_mem nE h6
  · exact h ▸ isElement_mem nE h7
  · exact h ▸ isElement_mem nE h8

/-- `SUBSET_1:41` -/
theorem th41 (hx : x ∈ X) : isSubset (TARSKI.singleton x) X :=
  (ZFMISC_1.th31 (x := x) (X := X)).mpr hx

/-! ## Schemes -/

/-- `SUBSET_1:sch SubsetEx`. -/
theorem sch_SubsetEx (A : TarskiSet.{u}) (P : TarskiSet.{u} → Prop) :
    ∃ X, isSubset X A ∧ ∀ x, x ∈ X ↔ x ∈ A ∧ P x := by
  obtain ⟨X, hX⟩ := XBOOLE_0.sch_separation A P
  exact ⟨X, fun x hx => (hX x).mp hx |>.1, hX⟩

/-- `SUBSET_1:sch SubsetEq`. -/
theorem sch_SubsetEq {X X1 X2 : TarskiSet.{u}} (h1 : isSubset X1 X)
    (h2 : isSubset X2 X) (P : TarskiSet.{u} → Prop)
    (H1 : ∀ y, isElement y X → (y ∈ X1 ↔ P y))
    (H2 : ∀ y, isElement y X → (y ∈ X2 ↔ P y)) : X1 = X2 :=
  th3 h1 h2 fun y hy => (H1 y hy).trans (H2 y hy).symm

theorem misses_irrefl {A : TarskiSet.{u}} (hA : ¬ XBOOLE_0.isEmpty A) :
    ¬ XBOOLE_0.misses A A := by
  obtain ⟨x, hx⟩ := Classical.not_not.mp hA
  intro hmiss
  exact (XBOOLE_0.empty_iff x).mp
    (hmiss ▸ (XBOOLE_0.def4 A A x).mpr ⟨hx, hx⟩)

theorem meets_refl {A : TarskiSet.{u}} (hA : ¬ XBOOLE_0.isEmpty A) :
    XBOOLE_0.meets A A :=
  fun h => misses_irrefl hA h

/-- Mizar `choose S` = `the Element of S`. -/
noncomputable def choose (S : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (def1_exists S)

theorem choose_isElement (S : TarskiSet.{u}) : isElement (choose S) S :=
  Classical.choose_spec (def1_exists S)

/-! ## Addenda -/

/-- `Lm2`. -/
theorem lm2 (h : ∀ x, x ∈ X → x ∈ Y) : isSubset X Y :=
  h

/-- `Lm3`. -/
theorem lm3 {E A x : TarskiSet.{u}} (hA : isSubset A E) (hx : x ∈ A) :
    isElement x E :=
  isElement_of (lm1 hA hx)

/-- Second `SubsetEx` (from `SETWISEO`). -/
theorem sch_SubsetEx2 {A : TarskiSet.{u}} (hA : ¬ XBOOLE_0.isEmpty A)
    (P : TarskiSet.{u} → Prop) :
    ∃ B, isSubset B A ∧ ∀ x, isElement x A → (x ∈ B ↔ P x) := by
  obtain ⟨B, hsub, hB⟩ := sch_SubsetEx A P
  refine ⟨B, hsub, fun x hx => ?_⟩
  have hxA : x ∈ A := isElement_mem hA hx
  exact ⟨fun h => (hB x).mp h |>.2, fun hP => (hB x).mpr ⟨hxA, hP⟩⟩

/-- `SUBSET_1:sch SubComp`. -/
theorem sch_SubComp {A F1 F2 : TarskiSet.{u}} (h1 : isSubset F1 A)
    (h2 : isSubset F2 A) (P : TarskiSet.{u} → Prop)
    (H1 : ∀ X, isElement X A → (X ∈ F1 ↔ P X))
    (H2 : ∀ X, isElement X A → (X ∈ F2 ↔ P X)) : F1 = F2 := by
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro x hx
    exact (H2 x (lm3 h1 hx)).mpr ((H1 x (lm3 h1 hx)).mp hx)
  · intro x hx
    exact (H1 x (lm3 h2 hx)).mpr ((H2 x (lm3 h2 hx)).mp hx)

/-- `SUBSET_1:42` -/
theorem th42 {E A B : TarskiSet.{u}} (hA : isSubset A E) (hB : isSubset B E)
    (h : compl E A = compl E B) : A = B :=
  (compl_involutive hA).symm.trans ((congrArg (compl E) h).trans
    (compl_involutive hB))

theorem subset_of_empty {A E : TarskiSet.{u}}
    (hE : XBOOLE_0.isEmpty E) (hA : isSubset A E) : XBOOLE_0.isEmpty A :=
  fun ⟨x, hx⟩ => hE ⟨x, hA x hx⟩

/-! ## `proper` (`A ≠ E`) -/

def isProper (A E : TarskiSet.{u}) : Prop := A ≠ E

theorem hash_not_proper (E : TarskiSet.{u}) : ¬ isProper (hash E) E :=
  fun h => h rfl

theorem nonproper_exists (E : TarskiSet.{u}) :
    ∃ A, isSubset A E ∧ ¬ isProper A E :=
  ⟨hash E, hash_isSubset E, hash_not_proper E⟩

theorem nonproper_nonempty {E A : TarskiSet.{u}}
    (hE : ¬ XBOOLE_0.isEmpty E) (hnp : ¬ isProper A E) :
    ¬ XBOOLE_0.isEmpty A :=
  (Classical.not_not.mp hnp) ▸ hE

theorem empty_proper {E : TarskiSet.{u}} (hE : ¬ XBOOLE_0.isEmpty E) :
    isProper (emptyOf E) E :=
  fun h => hE (h ▸ XBOOLE_0.emptySet_isEmpty)

theorem proper_exists {E : TarskiSet.{u}} (hE : ¬ XBOOLE_0.isEmpty E) :
    ∃ A, isSubset A E ∧ isProper A E :=
  ⟨emptyOf E, emptyOf_isSubset E, empty_proper hE⟩

theorem subset_of_empty_not_proper {A E : TarskiSet.{u}}
    (hE : XBOOLE_0.isEmpty E) (hA : isSubset A E) : ¬ isProper A E :=
  fun h => h ((XBOOLE_0.empty_eq (subset_of_empty hE hA)).trans
    (XBOOLE_0.empty_eq hE).symm)

/-- `SUBSET_1:43` -/
theorem th43 {X Y A z : TarskiSet.{u}} (hz : z ∈ A)
    (hA : A ⊆ ZFMISC_1.product X Y) :
    ∃ x y, isElement x X ∧ isElement y Y ∧ z = TARSKI.pair x y := by
  obtain ⟨x, y, hx, hy, heq⟩ := ZFMISC_1.th84 hA hz
  exact ⟨x, y, isElement_of hx, isElement_of hy, heq⟩

/-- `SUBSET_1:44` -/
theorem th44 {X A B : TarskiSet.{u}} (_hA : isSubset A X) (hB : isSubset B X)
    (hss : A ⊂ B) :
    ∃ p, isElement p X ∧ p ∈ B ∧ A ⊆ B \ TARSKI.singleton p := by
  have hne : B \ A ≠ (∅ : TarskiSet.{u}) :=
    XBOOLE_1.th105 (X := A) (Y := B) hss
  have hsub : isSubset (B \ A) X :=
    XBOOLE_1.th1 (XBOOLE_1.th36 (X := B) (Y := A)) hB
  obtain ⟨p, hpE, hp⟩ := th4 hsub hne
  have ⟨hpB, hpA⟩ := (XBOOLE_0.def5 B A p).mp hp
  exact ⟨p, hpE, hpB, ZFMISC_1.th34 (Y := A) (X := B) (x := p) hss.1 hpA⟩

theorem isTrivial_elements {X : TarskiSet.{u}}
    (hne : ¬ XBOOLE_0.isEmpty X) :
    ZFMISC_1.isTrivial X ↔ ∀ x y, isElement x X → isElement y X → x = y :=
  ⟨fun htr x y hx hy =>
      htr x y (isElement_mem hne hx) (isElement_mem hne hy),
    fun h x y hx hy => h x y (isElement_of hx) (isElement_of hy)⟩

theorem trivial_subset_exists {X : TarskiSet.{u}}
    (hne : ¬ XBOOLE_0.isEmpty X) :
    ∃ A, isSubset A X ∧ ¬ XBOOLE_0.isEmpty A ∧ ZFMISC_1.isTrivial A :=
  let x := choose X
  have hx : x ∈ X := isElement_mem hne (choose_isElement X)
  ⟨TARSKI.singleton x, th41 hx, XBOOLE_0.singleton_nonempty x,
    ZFMISC_1.singleton_trivial x⟩

theorem subset_of_trivial {X Y : TarskiSet.{u}} (hY : isSubset Y X)
    (htr : ZFMISC_1.isTrivial X) : ZFMISC_1.isTrivial Y :=
  ZFMISC_1.th130 hY htr

theorem nontrivial_subset_exists {X : TarskiSet.{u}}
    (hntr : ¬ ZFMISC_1.isTrivial X) :
    ∃ A, isSubset A X ∧ ¬ ZFMISC_1.isTrivial A :=
  ⟨hash X, hash_isSubset X, hntr⟩

/-- `SUBSET_1:45` -/
theorem th45 {D A : TarskiSet.{u}} (hA : isSubset A D)
    (hntr : ¬ ZFMISC_1.isTrivial A) :
    ∃ d1 d2, isElement d1 D ∧ isElement d2 D ∧
      d1 ∈ A ∧ d2 ∈ A ∧ d1 ≠ d2 := by
  have : ∃ d1 d2, d1 ∈ A ∧ d2 ∈ A ∧ d1 ≠ d2 :=
    Classical.byContradiction fun h =>
      hntr fun a b ha hb =>
        Classical.byContradiction fun hne => h ⟨a, b, ha, hb, hne⟩
  obtain ⟨d1, d2, h1, h2, hne⟩ := this
  exact ⟨d1, d2, lm3 hA h1, lm3 hA h2, h1, h2, hne⟩

/-- `SUBSET_1:46` (`Th46`) -/
theorem th46 {X : TarskiSet.{u}} (hne : ¬ XBOOLE_0.isEmpty X)
    (htr : ZFMISC_1.isTrivial X) :
    ∃ x, isElement x X ∧ X = TARSKI.singleton x := by
  obtain ⟨x, hx⟩ := ZFMISC_1.th131 hne htr
  have : x ∈ X :=
    hx.symm ▸ (singleton_iff x x).mpr rfl
  exact ⟨x, isElement_of this, hx⟩

/-- `SUBSET_1:47` -/
theorem th47 {X A : TarskiSet.{u}} (hA : isSubset A X)
    (hAne : ¬ XBOOLE_0.isEmpty A) (htr : ZFMISC_1.isTrivial A) :
    ∃ x, isElement x X ∧ A = TARSKI.singleton x := by
  obtain ⟨s, _, heq⟩ := th46 hAne htr
  have hsA : s ∈ A :=
    heq.symm ▸ (singleton_iff s s).mpr rfl
  exact ⟨s, lm3 hA hsA, heq⟩

/-- `SUBSET_1:48` -/
theorem th48 {X x : TarskiSet.{u}} (hntr : ¬ ZFMISC_1.isTrivial X)
    (_hx : isElement x X) : ∃ y, y ∈ X ∧ x ≠ y := by
  have : ∃ d1 d2, d1 ∈ X ∧ d2 ∈ X ∧ d1 ≠ d2 :=
    Classical.byContradiction fun h =>
      hntr fun a b ha hb =>
        Classical.byContradiction fun hne => h ⟨a, b, ha, hb, hne⟩
  obtain ⟨d1, d2, h1, h2, hne⟩ := this
  by_cases hxd1 : x = d1
  · exact ⟨d2, h2, fun h => hne (hxd1.symm.trans h)⟩
  · exact ⟨d1, h1, hxd1⟩

end SUBSET_1
