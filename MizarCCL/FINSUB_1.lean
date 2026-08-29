import MizarCCL.FINSET_1

/-
Copyright (c) 1990-2012 Association of Mizar Users.
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and `vendor/mml/finsub_1.miz`.
Authors: Andrzej Trybulec, Agata Darmochwał (Mizar),
  Lars Warren Ericson (Lean 4).
-/

/-!
# Boolean Domains

Faithful 1–1 rendering of Mizar article `FINSUB_1` (queue index 32).
The file contains all 18 absolute theorem slots, five numbered definitions,
four operation redefinitions, the `Finite_Subset` mode, and all six claims
in five registration blocks. The source has no schemes or canceled items.
-/

universe u

open TarskiSet TARSKI XBOOLE_0

namespace FINSUB_1

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

private theorem subset_refl (A : TarskiSet.{u}) : A ⊆ A :=
  fun _ h => h

/-- `FINSUB_1:def 1`: closure under union. -/
def isCupClosed (A : TarskiSet.{u}) : Prop :=
  ∀ X Y, X ∈ A → Y ∈ A → X ∪ Y ∈ A

theorem def1 (A : TarskiSet.{u}) :
    isCupClosed A ↔ ∀ X Y, X ∈ A → Y ∈ A → X ∪ Y ∈ A :=
  Iff.rfl

/-- `FINSUB_1:def 2`: closure under intersection. -/
def isCapClosed (A : TarskiSet.{u}) : Prop :=
  ∀ X Y, X ∈ A → Y ∈ A → X ∩ Y ∈ A

theorem def2 (A : TarskiSet.{u}) :
    isCapClosed A ↔ ∀ X Y, X ∈ A → Y ∈ A → X ∩ Y ∈ A :=
  Iff.rfl

/-- `FINSUB_1:def 3`: closure under difference. -/
def isDiffClosed (A : TarskiSet.{u}) : Prop :=
  ∀ X Y, X ∈ A → Y ∈ A → X \ Y ∈ A

theorem def3 (A : TarskiSet.{u}) :
    isDiffClosed A ↔ ∀ X Y, X ∈ A → Y ∈ A → X \ Y ∈ A :=
  Iff.rfl

/-- `FINSUB_1:def 4`: a pre-Boolean family. -/
def isPreBoolean (A : TarskiSet.{u}) : Prop :=
  isCupClosed A ∧ isDiffClosed A

theorem def4 (A : TarskiSet.{u}) :
    isPreBoolean A ↔ isCupClosed A ∧ isDiffClosed A :=
  Iff.rfl

/-! The two implications in the first registration block. -/

theorem preBoolean_isCupClosed {A : TarskiSet.{u}} (h : isPreBoolean A) :
    isCupClosed A :=
  h.1

theorem preBoolean_isDiffClosed {A : TarskiSet.{u}} (h : isPreBoolean A) :
    isDiffClosed A :=
  h.2

theorem cupClosed_diffClosed_isPreBoolean {A : TarskiSet.{u}}
    (hc : isCupClosed A) (hd : isDiffClosed A) : isPreBoolean A :=
  ⟨hc, hd⟩

/-- Registration: a nonempty union-, intersection-, and difference-closed
family exists. -/
theorem exists_nonempty_closed :
    ∃ A : TarskiSet.{u}, A ≠ (∅ : TarskiSet.{u}) ∧
      isCupClosed A ∧ isCapClosed A ∧ isDiffClosed A := by
  let A := TARSKI.singleton (∅ : TarskiSet.{u})
  have hne : A ≠ (∅ : TarskiSet.{u}) := by
    intro h
    have hm : (∅ : TarskiSet.{u}) ∈ A := (singleton_iff _ _).mpr rfl
    exact (XBOOLE_0.empty_iff (∅ : TarskiSet.{u})).mp
      (Eq.subst (motive := fun S => (∅ : TarskiSet.{u}) ∈ S) h hm)
  refine ⟨A, hne, ?_, ?_, ?_⟩
  · intro X Y hX hY
    have hx0 : X = (∅ : TarskiSet.{u}) := (singleton_iff _ _).mp hX
    have hy0 : Y = (∅ : TarskiSet.{u}) := (singleton_iff _ _).mp hY
    rw [hx0, hy0]
    exact (singleton_iff _ _).mpr (XBOOLE_0.union_idem _)
  · intro X Y hX _
    have hx0 : X = (∅ : TarskiSet.{u}) := (singleton_iff _ _).mp hX
    rw [hx0]
    exact (singleton_iff _ _).mpr
      (XBOOLE_1.th3 (XBOOLE_1.th17 (X := (∅ : TarskiSet.{u})) (Y := Y)))
  · intro X Y hX _
    have hx0 : X = (∅ : TarskiSet.{u}) := (singleton_iff _ _).mp hX
    rw [hx0]
    exact (singleton_iff _ _).mpr
      (XBOOLE_1.th3 (fun x hx => (XBOOLE_0.empty_iff x).mp
        ((XBOOLE_0.def5 (∅ : TarskiSet.{u}) Y x).mp hx).1 |>.elim))

/-- `FINSUB_1:1` (`Th1`). -/
theorem th1 (A : TarskiSet.{u}) :
    isPreBoolean A ↔
      ∀ X Y, X ∈ A → Y ∈ A → X ∪ Y ∈ A ∧ X \ Y ∈ A := by
  constructor
  · intro h X Y hX hY
    exact ⟨h.1 X Y hX hY, h.2 X Y hX hY⟩
  · intro h
    exact ⟨fun X Y hX hY => (h X Y hX hY).1,
      fun X Y hX hY => (h X Y hX hY).2⟩

/-! Operation redefinitions on elements of a nonempty pre-Boolean family. -/

theorem union_mem {A X Y : TarskiSet.{u}} (hA : isPreBoolean A)
    (hX : X ∈ A) (hY : Y ∈ A) : X ∪ Y ∈ A :=
  hA.1 X Y hX hY

theorem diff_mem {A X Y : TarskiSet.{u}} (hA : isPreBoolean A)
    (hX : X ∈ A) (hY : Y ∈ A) : X \ Y ∈ A :=
  hA.2 X Y hX hY

/-- `FINSUB_1:2` (`Th2`). -/
theorem th2 {A X Y : TarskiSet.{u}} (hA : isPreBoolean A)
    (hX : X ∈ A) (hY : Y ∈ A) : X ∩ Y ∈ A := by
  rw [← XBOOLE_1.th48]
  exact diff_mem hA hX (diff_mem hA hX hY)

/-- `FINSUB_1:3` (`Th3`). -/
theorem th3 {A X Y : TarskiSet.{u}} (hA : isPreBoolean A)
    (hX : X ∈ A) (hY : Y ∈ A) : X ∆ Y ∈ A := by
  rw [XBOOLE_0.def6]
  exact union_mem hA (diff_mem hA hX hY) (diff_mem hA hY hX)

/-- `FINSUB_1:4` (unlabeled). -/
theorem th4 {A : TarskiSet.{u}} (_hne : A ≠ (∅ : TarskiSet.{u}))
    (h : ∀ X Y, X ∈ A → Y ∈ A → X ∆ Y ∈ A ∧ X \ Y ∈ A) :
    isPreBoolean A := by
  apply (th1 A).mpr
  intro X Y hX hY
  have hYX : Y \ X ∈ A := (h Y X hY hX).2
  exact ⟨Eq.subst (motive := fun Z => Z ∈ A) XBOOLE_1.th98.symm
      (h X (Y \ X) hX hYX).1,
    (h X Y hX hY).2⟩

/-- `FINSUB_1:5` (unlabeled). -/
theorem th5 {A : TarskiSet.{u}} (_hne : A ≠ (∅ : TarskiSet.{u}))
    (h : ∀ X Y, X ∈ A → Y ∈ A → X ∆ Y ∈ A ∧ X ∩ Y ∈ A) :
    isPreBoolean A := by
  apply (th1 A).mpr
  intro X Y hX hY
  have hs : X ∆ Y ∈ A := (h X Y hX hY).1
  have hi : X ∩ Y ∈ A := (h X Y hX hY).2
  exact ⟨Eq.subst (motive := fun Z => Z ∈ A) XBOOLE_1.th94.symm
      (h (X ∆ Y) (X ∩ Y) hs hi).1,
    Eq.subst (motive := fun Z => Z ∈ A) XBOOLE_1.th100.symm
      (h X (X ∩ Y) hX hi).1⟩

/-- `FINSUB_1:6` (unlabeled). -/
theorem th6 {A : TarskiSet.{u}} (_hne : A ≠ (∅ : TarskiSet.{u}))
    (h : ∀ X Y, X ∈ A → Y ∈ A → X ∆ Y ∈ A ∧ X ∪ Y ∈ A) :
    isPreBoolean A := by
  apply (th1 A).mpr
  intro X Y hX hY
  have hs : X ∆ Y ∈ A := (h X Y hX hY).1
  have hu : X ∪ Y ∈ A := (h X Y hX hY).2
  have hi : X ∩ Y ∈ A :=
    Eq.subst (motive := fun Z => Z ∈ A) XBOOLE_1.th95.symm
      (h (X ∆ Y) (X ∪ Y) hs hu).1
  exact ⟨hu, Eq.subst (motive := fun Z => Z ∈ A) XBOOLE_1.th100.symm
    (h X (X ∩ Y) hX hi).1⟩

theorem inter_mem {A X Y : TarskiSet.{u}} (hA : isPreBoolean A)
    (hX : X ∈ A) (hY : Y ∈ A) : X ∩ Y ∈ A :=
  th2 hA hX hY

theorem symmDiff_mem {A X Y : TarskiSet.{u}} (hA : isPreBoolean A)
    (hX : X ∈ A) (hY : Y ∈ A) : X ∆ Y ∈ A :=
  th3 hA hX hY

/-- `FINSUB_1:7` (`Th7`). -/
theorem th7 {A : TarskiSet.{u}} (hne : A ≠ (∅ : TarskiSet.{u}))
    (hA : isPreBoolean A) : (∅ : TarskiSet.{u}) ∈ A := by
  obtain ⟨x, hx⟩ := XBOOLE_0.th7 hne
  have hd := diff_mem hA hx hx
  exact Eq.subst (motive := fun Z => Z ∈ A)
    ((XBOOLE_1.th37 (X := x) (Y := x)).mpr (subset_refl x)) hd

/-- `FINSUB_1:8` (`Th8`). -/
theorem th8 (A : TarskiSet.{u}) : isPreBoolean (ZFMISC_1.bool A) := by
  apply (th1 _).mpr
  intro X Y hX hY
  have hXA := (ZFMISC_1.def1 A X).mp hX
  have hYA := (ZFMISC_1.def1 A Y).mp hY
  constructor
  · exact (ZFMISC_1.def1 A (X ∪ Y)).mpr (XBOOLE_1.th8 hXA hYA)
  · exact (ZFMISC_1.def1 A (X \ Y)).mpr
      (fun x hx => hXA x ((XBOOLE_0.def5 X Y x).mp hx).1)

/-- Registration: every power set is pre-Boolean. -/
theorem bool_isPreBoolean (A : TarskiSet.{u}) :
    isPreBoolean (ZFMISC_1.bool A) :=
  th8 A

/-- `FINSUB_1:9` (unlabeled). -/
theorem th9 {A B : TarskiSet.{u}}
    (hneA : A ≠ (∅ : TarskiSet.{u})) (hA : isPreBoolean A)
    (hneB : B ≠ (∅ : TarskiSet.{u})) (hB : isPreBoolean B) :
    A ∩ B ≠ (∅ : TarskiSet.{u}) ∧ isPreBoolean (A ∩ B) := by
  have heA := th7 hneA hA
  have heB := th7 hneB hB
  have hne : A ∩ B ≠ (∅ : TarskiSet.{u}) := by
    intro he
    exact (XBOOLE_0.empty_iff (∅ : TarskiSet.{u})).mp
      (Eq.subst (motive := fun S => (∅ : TarskiSet.{u}) ∈ S) he
        ((XBOOLE_0.def4 A B ∅).mpr ⟨heA, heB⟩))
  refine ⟨hne, (th1 _).mpr ?_⟩
  intro X Y hX hY
  have hXA := (XBOOLE_0.def4 A B X).mp hX
  have hYA := (XBOOLE_0.def4 A B Y).mp hY
  exact ⟨(XBOOLE_0.def4 A B (X ∪ Y)).mpr
      ⟨union_mem hA hXA.1 hYA.1, union_mem hB hXA.2 hYA.2⟩,
    (XBOOLE_0.def4 A B (X \ Y)).mpr
      ⟨diff_mem hA hXA.1 hYA.1, diff_mem hB hXA.2 hYA.2⟩⟩

/-! ## The set of all finite subsets -/

/-- `FINSUB_1:def 5`: the family `Fin A` of finite subsets of `A`. -/
noncomputable def Fin (A : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (XBOOLE_0.sch_separation (ZFMISC_1.bool A) FINSET_1.isFinite)

theorem def5 (A X : TarskiSet.{u}) :
    X ∈ Fin A ↔ X ⊆ A ∧ FINSET_1.isFinite X := by
  exact (Classical.choose_spec
    (XBOOLE_0.sch_separation (ZFMISC_1.bool A) FINSET_1.isFinite) X).trans
      (and_congr (ZFMISC_1.def1 A X) Iff.rfl)

theorem Fin_isPreBoolean (A : TarskiSet.{u}) : isPreBoolean (Fin A) := by
  apply (th1 _).mpr
  intro X Y hX hY
  have hx := (def5 A X).mp hX
  have hy := (def5 A Y).mp hY
  exact ⟨(def5 A (X ∪ Y)).mpr
      ⟨XBOOLE_1.th8 hx.1 hy.1, FINSET_1.union_isFinite hx.2 hy.2⟩,
    (def5 A (X \ Y)).mpr
      ⟨fun z hz => hx.1 z ((XBOOLE_0.def5 X Y z).mp hz).1,
        FINSET_1.diff_isFinite hx.2⟩⟩

/-- Registration: `Fin A` is nonempty. -/
theorem Fin_nonempty (A : TarskiSet.{u}) :
    Fin A ≠ (∅ : TarskiSet.{u}) := by
  intro h
  have hm : (∅ : TarskiSet.{u}) ∈ Fin A :=
    (def5 A ∅).mpr ⟨XBOOLE_1.th2, FINSET_1.empty_isFinite⟩
  exact (XBOOLE_0.empty_iff (∅ : TarskiSet.{u})).mp
    (Eq.subst (motive := fun S => (∅ : TarskiSet.{u}) ∈ S) h hm)

/-- Registration: every element of `Fin A` is finite. -/
theorem mem_Fin_isFinite {A X : TarskiSet.{u}} (hX : X ∈ Fin A) :
    FINSET_1.isFinite X :=
  (def5 A X).mp hX |>.2

/-- `FINSUB_1:10` (`Th10`). -/
theorem th10 {A B : TarskiSet.{u}} (hAB : A ⊆ B) : Fin A ⊆ Fin B := by
  intro X hX
  have hx := (def5 A X).mp hX
  exact (def5 B X).mpr ⟨XBOOLE_1.th1 hx.1 hAB, hx.2⟩

/-- `FINSUB_1:11` (unlabeled). -/
theorem th11 (A B : TarskiSet.{u}) :
    Fin (A ∩ B) = Fin A ∩ Fin B := by
  apply eq_of_mem
  intro X
  constructor
  · intro hX
    have hx := (def5 (A ∩ B) X).mp hX
    have hsA : X ⊆ A := XBOOLE_1.th1 hx.1 XBOOLE_1.th17
    have hsB : X ⊆ B := XBOOLE_1.th1 hx.1
      (fun x h => (XBOOLE_0.def4 A B x).mp h |>.2)
    exact (XBOOLE_0.def4 (Fin A) (Fin B) X).mpr
      ⟨(def5 A X).mpr ⟨hsA, hx.2⟩, (def5 B X).mpr ⟨hsB, hx.2⟩⟩
  · intro hX
    have hx := (XBOOLE_0.def4 (Fin A) (Fin B) X).mp hX
    have ha := (def5 A X).mp hx.1
    have hb := (def5 B X).mp hx.2
    exact (def5 (A ∩ B) X).mpr
      ⟨XBOOLE_1.th19 ha.1 hb.1, ha.2⟩

/-- `FINSUB_1:12` (unlabeled). -/
theorem th12 (A B : TarskiSet.{u}) :
    Fin A ∪ Fin B ⊆ Fin (A ∪ B) :=
  XBOOLE_1.th8 (th10 XBOOLE_1.th7)
    (th10 (fun x hx => (XBOOLE_0.def3 A B x).mpr (Or.inr hx)))

/-- `FINSUB_1:13` (`Th13`). -/
theorem th13 (A : TarskiSet.{u}) : Fin A ⊆ ZFMISC_1.bool A :=
  fun X hX => (ZFMISC_1.def1 A X).mpr ((def5 A X).mp hX).1

/-- `FINSUB_1:14` (`Th14`). -/
theorem th14 {A : TarskiSet.{u}} (hA : FINSET_1.isFinite A) :
    Fin A = ZFMISC_1.bool A := by
  apply XBOOLE_0.def10.mpr
  refine ⟨th13 A, ?_⟩
  intro X hX
  have hs := (ZFMISC_1.def1 A X).mp hX
  exact (def5 A X).mpr ⟨hs, FINSET_1.subset_isFinite hs hA⟩

/-- `FINSUB_1:15` (unlabeled). -/
theorem th15 :
    Fin (∅ : TarskiSet.{u}) =
      TARSKI.singleton (∅ : TarskiSet.{u}) := by
  rw [th14 FINSET_1.empty_isFinite]
  exact ZFMISC_1.th1

/-! ## Finite subsets -/

/-- Mizar mode `Finite_Subset of A`. -/
def isFiniteSubsetOf (X A : TarskiSet.{u}) : Prop :=
  X ∈ Fin A

/-- `FINSUB_1:16` (unlabeled). -/
theorem th16 {A X : TarskiSet.{u}} (hX : isFiniteSubsetOf X A) :
    FINSET_1.isFinite X :=
  (def5 A X).mp hX |>.2

/-- `FINSUB_1:17` (unlabeled). -/
theorem th17 {A X : TarskiSet.{u}} (hX : isFiniteSubsetOf X A) :
    X ⊆ A :=
  (def5 A X).mp hX |>.1

/-- `FINSUB_1:18` (unlabeled). -/
theorem th18 {A X : TarskiSet.{u}} (hX : X ⊆ A)
    (hA : FINSET_1.isFinite A) : isFiniteSubsetOf X A :=
  (def5 A X).mpr ⟨hX, FINSET_1.subset_isFinite hX hA⟩

end FINSUB_1
