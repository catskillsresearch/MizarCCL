import MizarCCL.FUNCOP_1
import MizarCCL.ORDINAL1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/ordinal2.miz`.
Authors: Grzegorz Bancerek (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Sequences of Ordinal Numbers. Beginnings of Ordinal Arithmetics

1–1 Lean rendering of Mizar article `ORDINAL2`
(`vendor/mml/ordinal2.miz`). Imports `FUNCOP_1` and `ORDINAL1`
(last queue deps actually used).

Transfinite recursion schemes `TSExist1` / `OSExist` reduce to
`ORDINAL1.sch_TSExist` with a three-case step (empty / successor /
limit), matching Mizar’s clauses.

All absolute theorem slots `1`–`50`, definitions `1`–`17`, all twenty
schemes, and all ten registrations are represented.  This article has no
canceled theorem, definition, or scheme slots.

Mizar's ordinal and T-sequence types are predicates on the common
`TarskiSet` carrier here, so their typing obligations are explicit
hypotheses.  Mizar's overloaded sequence `sup`/`inf` are named
`sequenceSup`/`sequenceInf`; guarded `lim` is totalized by the empty ordinal
outside its defining existence guard.
-/

universe u

open TarskiSet TARSKI

namespace ORDINAL2

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

private theorem subset_refl (X : TarskiSet.{u}) : X ⊆ X :=
  fun _ hx => hx

/-! ## `ORDINAL2:sch OrdinalInd` -/

/-- `ORDINAL2:sch 1` (`OrdinalInd`). -/
theorem sch_OrdinalInd (P : TarskiSet.{u} → Prop)
    (h0 : P (∅ : TarskiSet.{u}))
    (hs : ∀ A, ORDINAL1.isOrdinal A → P A → P (ORDINAL1.succ A))
    (hl : ∀ A, ORDINAL1.isOrdinal A → A ≠ (∅ : TarskiSet.{u}) →
      ORDINAL1.isLimitOrdinal A → (∀ B, B ∈ A → P B) → P A)
    (A : TarskiSet.{u}) (hA : ORDINAL1.isOrdinal A) : P A := by
  refine ORDINAL1.sch_TransfiniteInd P ?_ A hA
  intro A hA hIH
  by_cases hEmp : A = (∅ : TarskiSet.{u})
  · exact Eq.subst (motive := P) hEmp.symm h0
  · by_cases hLim : ORDINAL1.isLimitOrdinal A
    · exact hl A hA hEmp hLim hIH
    · obtain ⟨B, hBord, heq⟩ := (ORDINAL1.th29 hA).mp hLim
      have hBin : B ∈ A :=
        Eq.subst (motive := fun s => B ∈ s) heq.symm (ORDINAL1.th6 B)
      exact Eq.subst (motive := P) heq.symm (hs B hBord (hIH B hBin))

/-! ## Early theorems -/

/-- `ORDINAL2:1` (`Th1`). -/
theorem th1 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) :
    A ⊆ B ↔ ORDINAL1.succ A ⊆ ORDINAL1.succ B :=
  (ORDINAL1.th22 hA hB).symm.trans (ORDINAL1.th21 hA (ORDINAL1.th17 hB))

/-- `ORDINAL2:2` (`Th2`). -/
theorem th2 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    TARSKI.union (ORDINAL1.succ A) = A := by
  apply eq_of_mem; intro x; constructor
  · intro hx
    obtain ⟨X, hxX, hX⟩ := (TARSKI.def4 (ORDINAL1.succ A) x).mp hx
    exact (ORDINAL1.th22 (ORDINAL1.th13 (ORDINAL1.th17 hA) hX) hA).mp hX x hxX
  · intro hx
    exact (TARSKI.def4 (ORDINAL1.succ A) x).mpr ⟨A, hx, ORDINAL1.th6 A⟩

/-- `ORDINAL2:3` (unlabeled). -/
theorem th3 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ORDINAL1.succ A ⊆ ZFMISC_1.bool A := by
  intro x hx
  have hxord := ORDINAL1.th13 (ORDINAL1.th17 hA) hx
  have hxsub : x ⊆ A :=
    Or.elim ((ORDINAL1.th8 x A).mp hx) (fun h => hA.1 x h)
      (fun heq => Eq.subst (motive := fun s => s ⊆ A) heq.symm (subset_refl A))
  exact (ZFMISC_1.def1 A x).mpr hxsub

/-- `ORDINAL2:4` (unlabeled). -/
theorem th4 : ORDINAL1.isLimitOrdinal (∅ : TarskiSet.{u}) :=
  Eq.subst (motive := fun s => (∅ : TarskiSet.{u}) = s) ZFMISC_1.th2.symm rfl

/-- `ORDINAL2:5` (`Th5`). -/
theorem th5 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    TARSKI.union A ⊆ A := by
  intro x hx
  obtain ⟨Y, hxY, hY⟩ := (TARSKI.def4 A x).mp hx
  exact hA.1 Y hY x hxY

/-- `ORDINAL2:def 1` — `last L`. -/
noncomputable def last (L : TarskiSet.{u}) : TarskiSet.{u} :=
  FUNCT_1.apply L (TARSKI.union (RELAT_1.dom L))

theorem def1 (L : TarskiSet.{u}) :
    last L = FUNCT_1.apply L (TARSKI.union (RELAT_1.dom L)) := rfl

/-- `ORDINAL2:6` (unlabeled). -/
theorem th6 {L A : TarskiSet.{u}} (_hL : ORDINAL1.isTSequence L)
    (hA : ORDINAL1.isOrdinal A) (hdom : RELAT_1.dom L = ORDINAL1.succ A) :
    last L = FUNCT_1.apply L A :=
  congrArg (FUNCT_1.apply L)
    ((congrArg TARSKI.union hdom).trans (th2 hA))

/-- `ORDINAL2:7` (unlabeled). -/
theorem th7 (X : TarskiSet.{u}) : ORDINAL1.On X ⊆ X :=
  fun x hx => ((ORDINAL1.def9 X x).mp hx).1

/-- `ORDINAL2:8` (`Th8`). -/
theorem th8 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ORDINAL1.On A = A := by
  apply eq_of_mem; intro x; constructor
  · intro hx; exact ((ORDINAL1.def9 A x).mp hx).1
  · intro hx; exact (ORDINAL1.def9 A x).mpr ⟨hx, ORDINAL1.th13 hA hx⟩

/-- `ORDINAL2:9` (`Th9`). -/
theorem th9 {X Y : TarskiSet.{u}} (h : X ⊆ Y) :
    ORDINAL1.On X ⊆ ORDINAL1.On Y := by
  intro x hx
  have ⟨hxX, hord⟩ := (ORDINAL1.def9 X x).mp hx
  exact (ORDINAL1.def9 Y x).mpr ⟨h x hxX, hord⟩

/-- `ORDINAL2:10` (unlabeled). -/
theorem th10 (X : TarskiSet.{u}) : ORDINAL1.Lim X ⊆ X :=
  fun x hx => ((ORDINAL1.def10 X x).mp hx).1

/-- `ORDINAL2:11` (unlabeled). -/
theorem th11 {X Y : TarskiSet.{u}} (h : X ⊆ Y) :
    ORDINAL1.Lim X ⊆ ORDINAL1.Lim Y := by
  intro x hx
  have ⟨hxX, hlim⟩ := (ORDINAL1.def10 X x).mp hx
  exact (ORDINAL1.def10 Y x).mpr ⟨h x hxX, hlim⟩

/-- `ORDINAL2:12` (unlabeled).

Mizar `Lim` witnesses are typed ordinals; Lean `ORDINAL1.Lim` stores
only `isLimitOrdinal`. Ordinality is an explicit hypothesis. -/
theorem th12 {X x : TarskiSet.{u}} (hx : x ∈ ORDINAL1.Lim X)
    (hord : ORDINAL1.isOrdinal x) : x ∈ ORDINAL1.On X :=
  (ORDINAL1.def9 X x).mpr ⟨((ORDINAL1.def10 X x).mp hx).1, hord⟩

/-! ## `ORDINAL2:13` — meet of ordinals is ordinal -/

/-- `ORDINAL2:13` (`Th13`). -/
theorem th13 {X : TarskiSet.{u}}
    (h : ∀ x, x ∈ X → ORDINAL1.isOrdinal x) :
    ORDINAL1.isOrdinal (SETFAM_1.meet X) := by
  by_cases hEmp : X = (∅ : TarskiSet.{u})
  · have hme : SETFAM_1.meet X = (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => SETFAM_1.meet s = (∅ : TarskiSet.{u}))
        hEmp.symm SETFAM_1.def1_empty
    exact Eq.subst (motive := ORDINAL1.isOrdinal) hme.symm
      ORDINAL1.empty_isOrdinal
  · obtain ⟨x0, hx0⟩ := XBOOLE_0.th7 hEmp
    have hx0ord := h x0 hx0
    obtain ⟨A, hAord, hAX, hleast⟩ :=
      ORDINAL1.sch_OrdinalMin (fun A => A ∈ X) ⟨x0, hx0ord, hx0⟩
    have hmeet : SETFAM_1.meet X = A := by
      apply eq_of_mem; intro z; constructor
      · intro hz
        exact ((SETFAM_1.def1 (x := z) hEmp).mp hz) A hAX
      · intro hz
        refine (SETFAM_1.def1 (x := z) hEmp).mpr ?_
        intro Y hY
        have hYord := h Y hY
        exact (hleast Y hYord hY) z hz
    exact Eq.subst (motive := ORDINAL1.isOrdinal) hmeet.symm hAord

/-! ## `inf` / `sup` (`ORDINAL2:def 2`–`def 3`) -/

/-- `ORDINAL2:def 2` — `inf X`. -/
noncomputable def inf (X : TarskiSet.{u}) : TarskiSet.{u} :=
  SETFAM_1.meet (ORDINAL1.On X)

theorem inf_isOrdinal (X : TarskiSet.{u}) :
    ORDINAL1.isOrdinal (inf X) :=
  th13 (fun x hx => ((ORDINAL1.def9 X x).mp hx).2)

theorem def2 (X : TarskiSet.{u}) : inf X = SETFAM_1.meet (ORDINAL1.On X) :=
  rfl

private theorem on_sub_succ_union (X : TarskiSet.{u}) :
    ORDINAL1.On X ⊆ ORDINAL1.succ (TARSKI.union (ORDINAL1.On X)) := by
  intro x hx
  have hxord := ((ORDINAL1.def9 X x).mp hx).2
  have hxsub : x ⊆ TARSKI.union (ORDINAL1.On X) := ZFMISC_1.th74 hx
  exact (ORDINAL1.th22 hxord
    (ORDINAL1.th23 (fun a ha => ((ORDINAL1.def9 X a).mp ha).2))).mpr hxsub

private theorem sup_exists (X : TarskiSet.{u}) :
    ∃ A, ORDINAL1.isOrdinal A ∧ ORDINAL1.On X ⊆ A ∧
      ∀ B, ORDINAL1.isOrdinal B → ORDINAL1.On X ⊆ B → A ⊆ B := by
  let U := TARSKI.union (ORDINAL1.On X)
  have hUord : ORDINAL1.isOrdinal U :=
    ORDINAL1.th23 (fun a ha => ((ORDINAL1.def9 X a).mp ha).2)
  have hP : ORDINAL1.On X ⊆ ORDINAL1.succ U := on_sub_succ_union X
  obtain ⟨A, hAord, hAP, hleast⟩ :=
    ORDINAL1.sch_OrdinalMin (fun A => ORDINAL1.On X ⊆ A)
      ⟨ORDINAL1.succ U, ORDINAL1.th17 hUord, hP⟩
  exact ⟨A, hAord, hAP, fun B hBord hB => hleast B hBord hB⟩

/-- `ORDINAL2:def 3` — `sup X`. -/
noncomputable def sup (X : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (sup_exists X)

theorem sup_isOrdinal (X : TarskiSet.{u}) :
    ORDINAL1.isOrdinal (sup X) :=
  (Classical.choose_spec (sup_exists X)).1

theorem def3 (X : TarskiSet.{u}) :
    ORDINAL1.On X ⊆ (sup X) ∧
      ∀ A, ORDINAL1.isOrdinal A → ORDINAL1.On X ⊆ A → (sup X) ⊆ A :=
  let h := Classical.choose_spec (sup_exists X)
  ⟨h.2.1, h.2.2⟩

/-- `ORDINAL2:14` (unlabeled). -/
theorem th14 {A X : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) (hAX : A ∈ X) :
    inf X ⊆ A := by
  have hOn : A ∈ ORDINAL1.On X := (ORDINAL1.def9 X A).mpr ⟨hAX, hA⟩
  exact SETFAM_1.th3 hOn

/-- `ORDINAL2:15` (unlabeled). -/
theorem th15 {X D : TarskiSet.{u}} (hD : ORDINAL1.isOrdinal D)
    (hne : ORDINAL1.On X ≠ (∅ : TarskiSet.{u}))
    (h : ∀ A, ORDINAL1.isOrdinal A → A ∈ X → D ⊆ A) :
    D ⊆ inf X := by
  intro x hx
  refine (SETFAM_1.def1 (x := x) hne).mpr ?_
  intro Y hY
  have ⟨hYX, hYord⟩ := (ORDINAL1.def9 X Y).mp hY
  exact h Y hYord hYX x hx

/-- `ORDINAL2:16` (unlabeled). -/
theorem th16 {A X Y : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hAX : A ∈ X) (hXY : X ⊆ Y) : inf Y ⊆ inf X := by
  have hOnne : ORDINAL1.On X ≠ (∅ : TarskiSet.{u}) := fun hempty =>
    (XBOOLE_0.empty_iff A).mp
      (Eq.subst (motive := fun s => A ∈ s) hempty
        ((ORDINAL1.def9 X A).mpr ⟨hAX, hA⟩))
  exact SETFAM_1.th6 hOnne (th9 hXY)

/-- `ORDINAL2:17` (unlabeled). -/
theorem th17 {A X : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) (hAX : A ∈ X) :
    inf X ∈ X := by
  obtain ⟨B, hBord, hBX, hleast⟩ :=
    ORDINAL1.sch_OrdinalMin (fun B => B ∈ X) ⟨A, hA, hAX⟩
  have hBon : B ∈ ORDINAL1.On X := (ORDINAL1.def9 X B).mpr ⟨hBX, hBord⟩
  have hOnne : ORDINAL1.On X ≠ (∅ : TarskiSet.{u}) := fun hempty =>
    (XBOOLE_0.empty_iff B).mp
      (Eq.subst (motive := fun s => B ∈ s) hempty hBon)
  have hmeet : SETFAM_1.meet (ORDINAL1.On X) = B := by
    apply eq_of_mem; intro z; constructor
    · intro hz
      exact ((SETFAM_1.def1 (x := z) hOnne).mp hz) B hBon
    · intro hz
      refine (SETFAM_1.def1 (x := z) hOnne).mpr ?_
      intro Y hY
      have ⟨hYX, hYord⟩ := (ORDINAL1.def9 X Y).mp hY
      exact (hleast Y hYord hYX) z hz
  exact Eq.subst (motive := fun s => s ∈ X) hmeet.symm hBX

/-- `ORDINAL2:18` (`Th18`). -/
theorem th18 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) : sup A = A := by
  have hOn : ORDINAL1.On A = A := th8 hA
  have ⟨hsub, hleast⟩ := def3 A
  have h1 : A ⊆ (sup A) :=
    Eq.subst (motive := fun s => s ⊆ (sup A)) hOn hsub
  have h2 : (sup A) ⊆ A :=
    hleast A hA (Eq.subst (motive := fun s => s ⊆ A) hOn.symm (subset_refl A))
  exact (XBOOLE_0.def10).mpr ⟨h2, h1⟩

/-- `ORDINAL2:19` (`Th19`). -/
theorem th19 {A X : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) (hAX : A ∈ X) :
    A ∈ (sup X) := by
  have hOn : A ∈ ORDINAL1.On X := (ORDINAL1.def9 X A).mpr ⟨hAX, hA⟩
  exact (def3 X).1 A hOn

/-- `ORDINAL2:20` (`Th20`). -/
theorem th20 {X D : TarskiSet.{u}} (hD : ORDINAL1.isOrdinal D)
    (h : ∀ A, ORDINAL1.isOrdinal A → A ∈ X → A ∈ D) :
    (sup X) ⊆ D := by
  have hOn : ORDINAL1.On X ⊆ D := by
    intro x hx
    have ⟨hxX, hord⟩ := (ORDINAL1.def9 X x).mp hx
    exact h x hord hxX
  exact (def3 X).2 D hD hOn

/-- `ORDINAL2:21` (unlabeled). -/
theorem th21 {A X : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hAsup : A ∈ (sup X)) :
    ∃ B, ORDINAL1.isOrdinal B ∧ B ∈ X ∧ A ⊆ B := by
  refine Classical.byContradiction fun hne => ?_
  have hne' : ∀ B, ORDINAL1.isOrdinal B → B ∈ X → ¬ A ⊆ B :=
    fun B hBord hBX hsub => hne ⟨B, hBord, hBX, hsub⟩
  have hall : ∀ B, ORDINAL1.isOrdinal B → B ∈ X → B ∈ A := by
    intro B hBord hBX
    have hnsub := hne' B hBord hBX
    exact Or.elim (ORDINAL1.th16 hA hBord)
      (fun hsub => (hnsub hsub).elim)
      (fun hBA => hBA)
  have hsup : (sup X) ⊆ A := th20 hA hall
  exact ORDINAL1.th5 hAsup hsup

/-- `ORDINAL2:22` (unlabeled). -/
theorem th22 {X Y : TarskiSet.{u}} (h : X ⊆ Y) : (sup X) ⊆ (sup Y) := by
  have hOn : ORDINAL1.On X ⊆ ORDINAL1.On Y := th9 h
  have hY : ORDINAL1.On Y ⊆ (sup Y) := (def3 Y).1
  exact (def3 X).2 (sup Y) (sup_isOrdinal Y) (XBOOLE_1.th1 hOn hY)

/-- `ORDINAL2:23` (unlabeled). -/
theorem th23 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    (sup (TARSKI.singleton A)) = ORDINAL1.succ A := by
  have hOnsub : ORDINAL1.On (TARSKI.singleton A) ⊆ ORDINAL1.succ A := by
    intro x hx
    have ⟨hxS, _⟩ := (ORDINAL1.def9 (TARSKI.singleton A) x).mp hx
    exact Eq.subst (motive := fun s => s ∈ ORDINAL1.succ A)
      ((singleton_iff A x).mp hxS).symm (ORDINAL1.th6 A)
  have hleast : ∀ B, ORDINAL1.isOrdinal B →
      ORDINAL1.On (TARSKI.singleton A) ⊆ B → ORDINAL1.succ A ⊆ B := by
    intro B hBord hOn
    have hAin : A ∈ TARSKI.singleton A := (singleton_iff A A).mpr rfl
    have hAOn : A ∈ ORDINAL1.On (TARSKI.singleton A) :=
      (ORDINAL1.def9 (TARSKI.singleton A) A).mpr ⟨hAin, hA⟩
    exact (ORDINAL1.th21 hA hBord).mp (hOn A hAOn)
  have ⟨hsub, hl⟩ := def3 (TARSKI.singleton A)
  have h1 : (sup (TARSKI.singleton A)) ⊆ ORDINAL1.succ A :=
    hl (ORDINAL1.succ A) (ORDINAL1.th17 hA) hOnsub
  have h2 : ORDINAL1.succ A ⊆ (sup (TARSKI.singleton A)) :=
    hleast (sup (TARSKI.singleton A)) (sup_isOrdinal _) hsub
  exact (XBOOLE_0.def10).mpr ⟨h1, h2⟩

/-- `ORDINAL2:24` (unlabeled). -/
theorem th24 (X : TarskiSet.{u}) : (inf X) ⊆ (sup X) := by
  by_cases hEmp : ORDINAL1.On X = (∅ : TarskiSet.{u})
  · have hinf : inf X = (∅ : TarskiSet.{u}) :=
      Eq.trans (congrArg SETFAM_1.meet hEmp) SETFAM_1.def1_empty
    exact Eq.subst (motive := fun s => s ⊆ (sup X)) hinf.symm
      (XBOOLE_1.th2 (X := (sup X)))
  · intro x hx
    obtain ⟨y0, hy0⟩ := XBOOLE_0.th7 hEmp
    have hy0ord := ((ORDINAL1.def9 X y0).mp hy0).2
    have hxY : x ∈ y0 :=
      ((SETFAM_1.def1 (x := x) hEmp).mp
        (Eq.subst (motive := fun s => x ∈ s) (def2 X) hx)) y0 hy0
    have hy0sup : y0 ∈ (sup X) := (def3 X).1 y0 hy0
    have hy0sub : y0 ⊆ (sup X) :=
      (sup_isOrdinal X).1 y0 hy0sup
    exact hy0sub x hxY

/-! ## `TSLambda` / Ordinal-yielding / `OSLambda` -/

/-- `ORDINAL2:sch 2` (`TSLambda`). -/
theorem sch_TSLambda {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (F : TarskiSet.{u} → TarskiSet.{u}) :
    ∃ L, ORDINAL1.isTSequence L ∧ RELAT_1.dom L = A ∧
      ∀ B, ORDINAL1.isOrdinal B → B ∈ A → FUNCT_1.apply L B = F B := by
  obtain ⟨f, hf, hdom, hv⟩ := FUNCT_1.sch_Lambda A
    (fun x => F (sup (TARSKI.union (TARSKI.singleton x))))
  have hTS : ORDINAL1.isTSequence f :=
    ⟨hf, Eq.subst (motive := ORDINAL1.isOrdinal) hdom.symm hA⟩
  refine ⟨f, hTS, hdom, ?_⟩
  intro B hBord hBA
  have happ := hv B hBA
  have h1 : TARSKI.union (TARSKI.singleton B) = B := ZFMISC_1.th25
  have h2 : (sup B) = B := th18 hBord
  exact happ.trans
    (congrArg F ((congrArg (fun s => (sup s)) h1).trans h2))

/-- `ORDINAL2:def 4` — Ordinal-yielding. -/
def isOrdinalYielding (f : TarskiSet.{u}) : Prop :=
  ∃ A, ORDINAL1.isOrdinal A ∧ RELAT_1.rng f ⊆ A

theorem def4 (f : TarskiSet.{u}) :
    isOrdinalYielding f ↔
      ∃ A, ORDINAL1.isOrdinal A ∧ RELAT_1.rng f ⊆ A :=
  Iff.rfl

/-- Ordinal-Sequence mode. -/
def isOrdinalSequence (IT : TarskiSet.{u}) : Prop :=
  ORDINAL1.isTSequence IT ∧ isOrdinalYielding IT

theorem empty_isOrdinalSequence :
    isOrdinalSequence (∅ : TarskiSet.{u}) :=
  ⟨ORDINAL1.empty_isTSequence,
    ⟨(∅ : TarskiSet.{u}), ORDINAL1.empty_isOrdinal,
      Eq.subst (motive := fun s => s ⊆ (∅ : TarskiSet.{u}))
        RELAT_1.th38.2.symm (subset_refl (∅ : TarskiSet.{u}))⟩⟩

theorem tsequence_of_ordinal_yielding {L A : TarskiSet.{u}}
    (hL : ORDINAL1.isTSequenceOf L A) (hA : ORDINAL1.isOrdinal A) :
    isOrdinalYielding L :=
  ⟨A, hA, hL.2⟩

theorem restrict_ordinal_yielding {L A : TarskiSet.{u}}
    (hL : isOrdinalSequence L) :
    isOrdinalYielding (RELAT_1.restrict L A) := by
  obtain ⟨B, hBord, hsub⟩ := hL.2
  exact ⟨B, hBord, XBOOLE_1.th1 (RELAT_1.th70 (R := L) (X := A)) hsub⟩

theorem restrict_ordinal_sequence {L A : TarskiSet.{u}}
    (hL : isOrdinalSequence L) (hA : ORDINAL1.isOrdinal A) :
    isOrdinalSequence (RELAT_1.restrict L A) :=
  ⟨ORDINAL1.restrict_isTSequence hL.1 hA, restrict_ordinal_yielding hL⟩

/-- `ORDINAL2:25` (`Th25`). -/
theorem th25 {fi A : TarskiSet.{u}} (hfi : isOrdinalSequence fi)
    (hA : A ∈ RELAT_1.dom fi) :
    ORDINAL1.isOrdinal (FUNCT_1.apply fi A) := by
  have hin : FUNCT_1.apply fi A ∈ RELAT_1.rng fi :=
    (FUNCT_1.def3 hfi.1.1.2).mpr ⟨A, hA, rfl⟩
  obtain ⟨B, hBord, hsub⟩ := hfi.2
  exact ORDINAL1.th13 hBord (hsub _ hin)

/-- Apply of Ordinal-Sequence at an ordinal (registration). -/
theorem apply_ordinal_sequence {fi a : TarskiSet.{u}}
    (hfi : isOrdinalSequence fi) (ha : ORDINAL1.isOrdinal a) :
    ORDINAL1.isOrdinal (FUNCT_1.apply fi a) := by
  by_cases hd : a ∈ RELAT_1.dom fi
  · exact th25 hfi hd
  · exact Eq.subst (motive := ORDINAL1.isOrdinal)
      (FUNCT_1.apply_of_not_mem hd).symm ORDINAL1.empty_isOrdinal

/-- `ORDINAL2:sch 3` (`OSLambda`). -/
theorem sch_OSLambda {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (F : TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ B, ORDINAL1.isOrdinal B → B ∈ A → ORDINAL1.isOrdinal (F B)) :
    ∃ fi, isOrdinalSequence fi ∧ RELAT_1.dom fi = A ∧
      ∀ B, ORDINAL1.isOrdinal B → B ∈ A → FUNCT_1.apply fi B = F B := by
  obtain ⟨L, hLTS, hdom, hv⟩ := sch_TSLambda hA F
  have hOY : isOrdinalYielding L := by
    refine ⟨sup (RELAT_1.rng L), (sup_isOrdinal _), ?_⟩
    intro x hx
    obtain ⟨y, hy, heq⟩ := (FUNCT_1.def3 hLTS.1.2).mp hx
    have hyord : ORDINAL1.isOrdinal y :=
      ORDINAL1.th13 (Eq.subst (motive := ORDINAL1.isOrdinal) hdom.symm hA) hy
    have hyA : y ∈ A := Eq.subst (motive := fun s => y ∈ s) hdom hy
    have hxeq : x = F y := heq.trans (hv y hyord hyA)
    have hxord : ORDINAL1.isOrdinal x :=
      Eq.subst (motive := ORDINAL1.isOrdinal) hxeq.symm (hF y hyord hyA)
    have hOn : x ∈ ORDINAL1.On (RELAT_1.rng L) :=
      (ORDINAL1.def9 (RELAT_1.rng L) x).mpr ⟨hx, hxord⟩
    exact (def3 (RELAT_1.rng L)).1 x hOn
  exact ⟨L, ⟨hLTS, hOY⟩, hdom, hv⟩

/-! ## Transfinite recursion step and `TSExist1` / `TSUniq1` -/

/-- Three-case recursion step used by `TSExist1`. -/
noncomputable def tsStep (B0 : TarskiSet.{u})
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (L : TarskiSet.{u}) : TarskiSet.{u} := by
  classical
  exact
    if h : RELAT_1.dom L = (∅ : TarskiSet.{u}) then B0
    else if h' : ∃ C0, ORDINAL1.isOrdinal C0 ∧ RELAT_1.dom L = ORDINAL1.succ C0 then
      C (Classical.choose h') (FUNCT_1.apply L (Classical.choose h'))
    else
      D (RELAT_1.dom L) L

private theorem tsStep_empty (B0 : TarskiSet.{u})
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u}) :
    tsStep B0 C D (∅ : TarskiSet.{u}) = B0 := by
  classical
  unfold tsStep
  have hdom : RELAT_1.dom (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) :=
    RELAT_1.th38.1
  simp only [hdom, ↓reduceDIte]

private theorem tsStep_succ {B0 C0 : TarskiSet.{u}}
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (L : TarskiSet.{u}) (hC0 : ORDINAL1.isOrdinal C0)
    (hdom : RELAT_1.dom L = ORDINAL1.succ C0) :
    tsStep B0 C D L = C C0 (FUNCT_1.apply L C0) := by
  classical
  unfold tsStep
  have hne : RELAT_1.dom L ≠ (∅ : TarskiSet.{u}) := fun he =>
    ORDINAL1.succ_nonempty C0
      (Eq.subst (motive := XBOOLE_0.isEmpty) (he.symm.trans hdom)
        XBOOLE_0.emptySet_isEmpty)
  have hex : ∃ D0, ORDINAL1.isOrdinal D0 ∧ RELAT_1.dom L = ORDINAL1.succ D0 :=
    ⟨C0, hC0, hdom⟩
  simp only [dif_neg hne, dif_pos hex]
  have hch := Classical.choose_spec hex
  have heqC : Classical.choose hex = C0 :=
    ORDINAL1.th7 (hch.2.symm.trans hdom)
  exact Eq.subst (motive := fun s =>
      C s (FUNCT_1.apply L s) = C C0 (FUNCT_1.apply L C0)) heqC.symm rfl

private theorem tsStep_limit {B0 A : TarskiSet.{u}}
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (L : TarskiSet.{u}) (_hA : ORDINAL1.isOrdinal A)
    (hdom : RELAT_1.dom L = A) (hne : A ≠ (∅ : TarskiSet.{u}))
    (hlim : ORDINAL1.isLimitOrdinal A) :
    tsStep B0 C D L = D A L := by
  classical
  unfold tsStep
  have hdomA : RELAT_1.dom L ≠ (∅ : TarskiSet.{u}) :=
    Eq.subst (motive := fun s => s ≠ (∅ : TarskiSet.{u})) hdom.symm hne
  have hnSucc : ¬ ∃ C0, ORDINAL1.isOrdinal C0 ∧ RELAT_1.dom L = ORDINAL1.succ C0 := by
    intro ⟨C0, hC0, heq⟩
    have hAeq : A = ORDINAL1.succ C0 := hdom.symm.trans heq
    have hnL : ¬ ORDINAL1.isLimitOrdinal (ORDINAL1.succ C0) :=
      (ORDINAL1.th29 (ORDINAL1.th17 hC0)).mpr ⟨C0, hC0, rfl⟩
    exact hnL (Eq.subst (motive := ORDINAL1.isLimitOrdinal) hAeq hlim)
  simp only [dif_neg hdomA, dif_neg hnSucc]
  exact congrArg (fun s => D s L) hdom

private theorem relation_eq_empty_of_dom {R : TarskiSet.{u}}
    (hR : RELAT_1.isRelation R)
    (hdom : RELAT_1.dom R = (∅ : TarskiSet.{u})) : R = (∅ : TarskiSet.{u}) :=
  (RELAT_1.th41 hR (Or.inl hdom)).symm ▸ rfl

/-- `ORDINAL2:sch 5` (`TSExist1`). -/
theorem sch_TSExist1 {A B0 : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u}) :
    ∃ L, ORDINAL1.isTSequence L ∧ RELAT_1.dom L = A ∧
      ((∅ : TarskiSet.{u}) ∈ A →
        FUNCT_1.apply L (∅ : TarskiSet.{u}) = B0) ∧
      (∀ B, ORDINAL1.isOrdinal B → ORDINAL1.succ B ∈ A →
        FUNCT_1.apply L (ORDINAL1.succ B) =
          C B (FUNCT_1.apply L B)) ∧
      (∀ B, ORDINAL1.isOrdinal B → B ∈ A → B ≠ (∅ : TarskiSet.{u}) →
        ORDINAL1.isLimitOrdinal B →
        FUNCT_1.apply L B = D B (RELAT_1.restrict L B)) := by
  let H := tsStep B0 C D
  obtain ⟨L, hLTS, hdom, hH⟩ := ORDINAL1.sch_TSExist H hA
  refine ⟨L, hLTS, hdom, ?_, ?_, ?_⟩
  · intro h0
    have happ := hH (∅ : TarskiSet.{u}) (RELAT_1.restrict L (∅ : TarskiSet.{u}))
      h0 rfl
    have hdR : RELAT_1.dom (RELAT_1.restrict L (∅ : TarskiSet.{u})) =
        (∅ : TarskiSet.{u}) :=
      RELAT_1.th62 (R := L) (X := (∅ : TarskiSet.{u}))
        (XBOOLE_1.th2 (X := RELAT_1.dom L))
    have hre : RELAT_1.restrict L (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) :=
      relation_eq_empty_of_dom (FUNCT_1.restrict_isFunction hLTS.1).1 hdR
    exact happ.trans
      (Eq.subst (motive := fun s => H s = B0) hre.symm (tsStep_empty B0 C D))
  · intro B hBord hsucc
    have happ := hH (ORDINAL1.succ B) (RELAT_1.restrict L (ORDINAL1.succ B))
      hsucc rfl
    have hdomR : RELAT_1.dom (RELAT_1.restrict L (ORDINAL1.succ B)) =
        ORDINAL1.succ B :=
      RELAT_1.th62 (R := L) (X := ORDINAL1.succ B)
        (Eq.subst (motive := fun s => ORDINAL1.succ B ⊆ s) hdom.symm
          (hA.1 (ORDINAL1.succ B) hsucc))
    have hstep := tsStep_succ (B0 := B0) (C0 := B) C D
      (RELAT_1.restrict L (ORDINAL1.succ B)) hBord hdomR
    have happB : FUNCT_1.apply (RELAT_1.restrict L (ORDINAL1.succ B)) B =
        FUNCT_1.apply L B :=
      FUNCT_1.th49 hLTS.1.2 (ORDINAL1.th6 B)
    exact happ.trans (hstep.trans (congrArg (C B) happB))
  · intro B hBord hBin hne hlim
    have happ := hH B (RELAT_1.restrict L B) hBin rfl
    have hdomR : RELAT_1.dom (RELAT_1.restrict L B) = B :=
      RELAT_1.th62 (R := L) (X := B)
        (Eq.subst (motive := fun s => B ⊆ s) hdom.symm (hA.1 B hBin))
    have hstep := tsStep_limit (B0 := B0) (A := B) C D
      (RELAT_1.restrict L B) hBord hdomR hne hlim
    exact happ.trans hstep

/-- `ORDINAL2:sch 4` (`TSUniq1`). -/
theorem sch_TSUniq1 {A B0 : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    {L1 L2 : TarskiSet.{u}}
    (hL1 : ORDINAL1.isTSequence L1) (hL2 : ORDINAL1.isTSequence L2)
    (hd1 : RELAT_1.dom L1 = A) (hd2 : RELAT_1.dom L2 = A)
    (h01 : (∅ : TarskiSet.{u}) ∈ A →
      FUNCT_1.apply L1 (∅ : TarskiSet.{u}) = B0)
    (hs1 : ∀ B, ORDINAL1.isOrdinal B → ORDINAL1.succ B ∈ A →
      FUNCT_1.apply L1 (ORDINAL1.succ B) = C B (FUNCT_1.apply L1 B))
    (hl1 : ∀ B, ORDINAL1.isOrdinal B → B ∈ A → B ≠ (∅ : TarskiSet.{u}) →
      ORDINAL1.isLimitOrdinal B →
      FUNCT_1.apply L1 B = D B (RELAT_1.restrict L1 B))
    (h02 : (∅ : TarskiSet.{u}) ∈ A →
      FUNCT_1.apply L2 (∅ : TarskiSet.{u}) = B0)
    (hs2 : ∀ B, ORDINAL1.isOrdinal B → ORDINAL1.succ B ∈ A →
      FUNCT_1.apply L2 (ORDINAL1.succ B) = C B (FUNCT_1.apply L2 B))
    (hl2 : ∀ B, ORDINAL1.isOrdinal B → B ∈ A → B ≠ (∅ : TarskiSet.{u}) →
      ORDINAL1.isLimitOrdinal B →
      FUNCT_1.apply L2 B = D B (RELAT_1.restrict L2 B)) :
    L1 = L2 := by
  let H := tsStep B0 C D
  have hH1 : ∀ B L, B ∈ A → L = RELAT_1.restrict L1 B →
      FUNCT_1.apply L1 B = H L := by
    intro B L hB hL
    have hBord := ORDINAL1.th13 hA hB
    by_cases hEmp : B = (∅ : TarskiSet.{u})
    · have h0 : (∅ : TarskiSet.{u}) ∈ A :=
        Eq.subst (motive := fun s => s ∈ A) hEmp hB
      have happ : FUNCT_1.apply L1 B = B0 :=
        Eq.subst (motive := fun s => FUNCT_1.apply L1 s = B0) hEmp.symm (h01 h0)
      have hdR : RELAT_1.dom L = (∅ : TarskiSet.{u}) := by
        have h := RELAT_1.th62 (R := L1) (X := B)
          (Eq.subst (motive := fun s => B ⊆ s) hd1.symm (hA.1 B hB))
        exact (Eq.subst (motive := fun s => RELAT_1.dom s = B) hL.symm h).trans hEmp
      have hre : L = (∅ : TarskiSet.{u}) :=
        relation_eq_empty_of_dom
          (Eq.subst (motive := RELAT_1.isRelation) hL.symm
            (FUNCT_1.restrict_isFunction hL1.1).1) hdR
      exact happ.trans
        (Eq.subst (motive := fun s => B0 = H s) hre.symm
          (tsStep_empty B0 C D).symm)
    · by_cases hLim : ORDINAL1.isLimitOrdinal B
      · have happ := hl1 B hBord hB hEmp hLim
        have hdomR : RELAT_1.dom L = B :=
          Eq.subst (motive := fun s => RELAT_1.dom s = B) hL.symm
            (RELAT_1.th62 (R := L1) (X := B)
              (Eq.subst (motive := fun s => B ⊆ s) hd1.symm (hA.1 B hB)))
        exact happ.trans
          ((congrArg (D B) hL.symm).trans
            (tsStep_limit (B0 := B0) (A := B) C D L hBord hdomR hEmp hLim).symm)
      · obtain ⟨C0, hC0, heq⟩ := (ORDINAL1.th29 hBord).mp hLim
        have hsucc : ORDINAL1.succ C0 ∈ A :=
          Eq.subst (motive := fun s => s ∈ A) heq hB
        have happ : FUNCT_1.apply L1 B = C C0 (FUNCT_1.apply L1 C0) :=
          Eq.subst (motive := fun s => FUNCT_1.apply L1 s =
            C C0 (FUNCT_1.apply L1 C0)) heq.symm (hs1 C0 hC0 hsucc)
        have hdomR : RELAT_1.dom L = ORDINAL1.succ C0 :=
          (Eq.subst (motive := fun s => RELAT_1.dom s = B) hL.symm
            (RELAT_1.th62 (R := L1) (X := B)
              (Eq.subst (motive := fun s => B ⊆ s) hd1.symm (hA.1 B hB)))).trans heq
        have happC : FUNCT_1.apply L C0 = FUNCT_1.apply L1 C0 :=
          Eq.subst (motive := fun s => FUNCT_1.apply s C0 = FUNCT_1.apply L1 C0)
            hL.symm (FUNCT_1.th49 hL1.1.2
              (Eq.subst (motive := fun s => C0 ∈ s) heq.symm (ORDINAL1.th6 C0)))
        exact happ.trans
          ((congrArg (C C0) happC.symm).trans
            (tsStep_succ (B0 := B0) (C0 := C0) C D L hC0 hdomR).symm)
  have hH2 : ∀ B L, B ∈ A → L = RELAT_1.restrict L2 B →
      FUNCT_1.apply L2 B = H L := by
    intro B L hB hL
    have hBord := ORDINAL1.th13 hA hB
    by_cases hEmp : B = (∅ : TarskiSet.{u})
    · have h0 : (∅ : TarskiSet.{u}) ∈ A :=
        Eq.subst (motive := fun s => s ∈ A) hEmp hB
      have happ : FUNCT_1.apply L2 B = B0 :=
        Eq.subst (motive := fun s => FUNCT_1.apply L2 s = B0) hEmp.symm (h02 h0)
      have hdR : RELAT_1.dom L = (∅ : TarskiSet.{u}) := by
        have h := RELAT_1.th62 (R := L2) (X := B)
          (Eq.subst (motive := fun s => B ⊆ s) hd2.symm (hA.1 B hB))
        exact (Eq.subst (motive := fun s => RELAT_1.dom s = B) hL.symm h).trans hEmp
      have hre : L = (∅ : TarskiSet.{u}) :=
        relation_eq_empty_of_dom
          (Eq.subst (motive := RELAT_1.isRelation) hL.symm
            (FUNCT_1.restrict_isFunction hL2.1).1) hdR
      exact happ.trans
        (Eq.subst (motive := fun s => B0 = H s) hre.symm
          (tsStep_empty B0 C D).symm)
    · by_cases hLim : ORDINAL1.isLimitOrdinal B
      · have happ := hl2 B hBord hB hEmp hLim
        have hdomR : RELAT_1.dom L = B :=
          Eq.subst (motive := fun s => RELAT_1.dom s = B) hL.symm
            (RELAT_1.th62 (R := L2) (X := B)
              (Eq.subst (motive := fun s => B ⊆ s) hd2.symm (hA.1 B hB)))
        exact happ.trans
          ((congrArg (D B) hL.symm).trans
            (tsStep_limit (B0 := B0) (A := B) C D L hBord hdomR hEmp hLim).symm)
      · obtain ⟨C0, hC0, heq⟩ := (ORDINAL1.th29 hBord).mp hLim
        have hsucc : ORDINAL1.succ C0 ∈ A :=
          Eq.subst (motive := fun s => s ∈ A) heq hB
        have happ : FUNCT_1.apply L2 B = C C0 (FUNCT_1.apply L2 C0) :=
          Eq.subst (motive := fun s => FUNCT_1.apply L2 s =
            C C0 (FUNCT_1.apply L2 C0)) heq.symm (hs2 C0 hC0 hsucc)
        have hdomR : RELAT_1.dom L = ORDINAL1.succ C0 :=
          (Eq.subst (motive := fun s => RELAT_1.dom s = B) hL.symm
            (RELAT_1.th62 (R := L2) (X := B)
              (Eq.subst (motive := fun s => B ⊆ s) hd2.symm (hA.1 B hB)))).trans heq
        have happC : FUNCT_1.apply L C0 = FUNCT_1.apply L2 C0 :=
          Eq.subst (motive := fun s => FUNCT_1.apply s C0 = FUNCT_1.apply L2 C0)
            hL.symm (FUNCT_1.th49 hL2.1.2
              (Eq.subst (motive := fun s => C0 ∈ s) heq.symm (ORDINAL1.th6 C0)))
        exact happ.trans
          ((congrArg (C C0) happC.symm).trans
            (tsStep_succ (B0 := B0) (C0 := C0) C D L hC0 hdomR).symm)
  exact ORDINAL1.sch_TSUniq H hA hL1 hL2 hd1 hd2 hH1 hH2

/-! ## Recursion result and definition schemes -/

/-- The common witness predicate occurring literally in `TSResult`, `TSDef`,
and their ordinal-valued variants. -/
def RecWitness (A x B0 : TarskiSet.{u})
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u}) : Prop :=
  ∃ L, ORDINAL1.isTSequence L ∧ x = last L ∧
    RELAT_1.dom L = ORDINAL1.succ A ∧
    FUNCT_1.apply L (∅ : TarskiSet.{u}) = B0 ∧
    (∀ E, ORDINAL1.isOrdinal E → ORDINAL1.succ E ∈ ORDINAL1.succ A →
      FUNCT_1.apply L (ORDINAL1.succ E) =
        C E (FUNCT_1.apply L E)) ∧
    (∀ E, ORDINAL1.isOrdinal E → E ∈ ORDINAL1.succ A →
      E ≠ (∅ : TarskiSet.{u}) → ORDINAL1.isLimitOrdinal E →
      FUNCT_1.apply L E = D E (RELAT_1.restrict L E))

private theorem empty_mem_succ (A : TarskiSet.{u})
    (hA : ORDINAL1.isOrdinal A) :
    (∅ : TarskiSet.{u}) ∈ ORDINAL1.succ A :=
  (ORDINAL1.th21 ORDINAL1.empty_isOrdinal (ORDINAL1.th17 hA)).mpr
    ((th1 ORDINAL1.empty_isOrdinal hA).mp XBOOLE_1.th2)

/-- `ORDINAL2:sch 7` (`TSDef`). -/
theorem sch_TSDef {A B0 : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u}) :
    (∃ x, RecWitness A x B0 C D) ∧
      ∀ x1 x2, RecWitness A x1 B0 C D →
        RecWitness A x2 B0 C D → x1 = x2 := by
  obtain ⟨L, hL, hdom, h0, hs, hl⟩ :=
    sch_TSExist1 (A := ORDINAL1.succ A) (B0 := B0)
      (ORDINAL1.th17 hA) C D
  have hempty := empty_mem_succ A hA
  have hw : RecWitness A (last L) B0 C D :=
    ⟨L, hL, rfl, hdom, h0 hempty, hs, hl⟩
  refine ⟨⟨last L, hw⟩, ?_⟩
  intro x1 x2 hx1 hx2
  obtain ⟨L1, hL1, hx1, hd1, h01, hs1, hl1⟩ := hx1
  obtain ⟨L2, hL2, hx2, hd2, h02, hs2, hl2⟩ := hx2
  have heq := sch_TSUniq1 (A := ORDINAL1.succ A) (B0 := B0)
    (ORDINAL1.th17 hA) C D
    hL1 hL2 hd1 hd2 (fun _ => h01)
    hs1 hl1 (fun _ => h02) hs2 hl2
  exact hx1.trans ((congrArg last heq).trans hx2.symm)

private theorem prefix_recWitness {L A B0 : TarskiSet.{u}}
    (hL : ORDINAL1.isTSequence L) (hA : ORDINAL1.isOrdinal A)
    (hAin : A ∈ RELAT_1.dom L)
    (h0 : (∅ : TarskiSet.{u}) ∈ RELAT_1.dom L →
      FUNCT_1.apply L (∅ : TarskiSet.{u}) = B0)
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hs : ∀ E, ORDINAL1.isOrdinal E →
      ORDINAL1.succ E ∈ RELAT_1.dom L →
      FUNCT_1.apply L (ORDINAL1.succ E) = C E (FUNCT_1.apply L E))
    (hl : ∀ E, ORDINAL1.isOrdinal E → E ∈ RELAT_1.dom L →
      E ≠ (∅ : TarskiSet.{u}) → ORDINAL1.isLimitOrdinal E →
      FUNCT_1.apply L E = D E (RELAT_1.restrict L E)) :
    RecWitness A (FUNCT_1.apply L A) B0 C D := by
  let K := RELAT_1.restrict L (ORDINAL1.succ A)
  have hsub : ORDINAL1.succ A ⊆ RELAT_1.dom L :=
    (ORDINAL1.th21 hA hL.2).mp hAin
  have hKdom : RELAT_1.dom K = ORDINAL1.succ A :=
    RELAT_1.th62 (R := L) (X := ORDINAL1.succ A) hsub
  have hK : ORDINAL1.isTSequence K :=
    ORDINAL1.restrict_isTSequence hL (ORDINAL1.th17 hA)
  have hlast : FUNCT_1.apply L A = last K := by
    have hkapp : FUNCT_1.apply K A = FUNCT_1.apply L A :=
      FUNCT_1.th49 hL.1.2 (ORDINAL1.th6 A)
    exact hkapp.symm.trans (th6 hK hA hKdom).symm
  refine ⟨K, hK, hlast, hKdom, ?_, ?_, ?_⟩
  · have he : (∅ : TarskiSet.{u}) ∈ ORDINAL1.succ A :=
      empty_mem_succ A hA
    exact (FUNCT_1.th49 hL.1.2 he).trans (h0 (hsub _ he))
  · intro E hE hEs
    exact (FUNCT_1.th49 hL.1.2 hEs).trans
      ((hs E hE (hsub _ hEs)).trans
        (congrArg (C E) (FUNCT_1.th49 hL.1.2
          (((ORDINAL1.th17 hA).1 (ORDINAL1.succ E) hEs)
            E (ORDINAL1.th6 E))).symm))
  · intro E hE hEin hne hlim
    have hEsub : E ⊆ ORDINAL1.succ A :=
      (ORDINAL1.th17 hA).1 E hEin
    have hr : RELAT_1.restrict K E = RELAT_1.restrict L E :=
      (FUNCT_1.th51 (f := L) (X := E) (Y := ORDINAL1.succ A) hEsub).2
    exact (FUNCT_1.th49 hL.1.2 hEin).trans
      ((hl E hE (hsub _ hEin) hne hlim).trans
        (congrArg (D E) hr.symm))

/-- `ORDINAL2:sch 6` (`TSResult`). -/
theorem sch_TSResult {L A B0 : TarskiSet.{u}}
    (F : TarskiSet.{u} → TarskiSet.{u})
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hchar : ∀ E, ORDINAL1.isOrdinal E → ∀ x,
      x = F E ↔ RecWitness E x B0 C D)
    (hL : ORDINAL1.isTSequence L) (hdom : RELAT_1.dom L = A)
    (h0 : (∅ : TarskiSet.{u}) ∈ A →
      FUNCT_1.apply L (∅ : TarskiSet.{u}) = B0)
    (hs : ∀ E, ORDINAL1.isOrdinal E → ORDINAL1.succ E ∈ A →
      FUNCT_1.apply L (ORDINAL1.succ E) = C E (FUNCT_1.apply L E))
    (hl : ∀ E, ORDINAL1.isOrdinal E → E ∈ A →
      E ≠ (∅ : TarskiSet.{u}) → ORDINAL1.isLimitOrdinal E →
      FUNCT_1.apply L E = D E (RELAT_1.restrict L E)) :
    ∀ E, ORDINAL1.isOrdinal E → E ∈ RELAT_1.dom L →
      FUNCT_1.apply L E = F E := by
  intro E hE hEin
  apply (hchar E hE (FUNCT_1.apply L E)).mpr
  exact prefix_recWitness hL hE hEin
    (fun he => h0 (Eq.subst (motive := fun s => (∅ : TarskiSet.{u}) ∈ s)
      hdom he)) C D
    (fun B hB hBs => hs B hB
      (Eq.subst (motive := fun s => ORDINAL1.succ B ∈ s) hdom hBs))
    (fun B hB hBin hn hlm => hl B hB
      (Eq.subst (motive := fun s => B ∈ s) hdom hBin) hn hlm)

/-- `ORDINAL2:sch 8` (`TSResult0`). -/
theorem sch_TSResult0 {B0 : TarskiSet.{u}}
    (F : TarskiSet.{u} → TarskiSet.{u})
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hchar : ∀ E, ORDINAL1.isOrdinal E → ∀ x,
      x = F E ↔ RecWitness E x B0 C D) :
    F (∅ : TarskiSet.{u}) = B0 := by
  obtain ⟨L, hL, hx, hd, h0, _hs, _hl⟩ :=
    (hchar (∅ : TarskiSet.{u}) ORDINAL1.empty_isOrdinal
      (F (∅ : TarskiSet.{u}))).mp rfl
  have hlst := th6 hL ORDINAL1.empty_isOrdinal hd
  exact hx.trans (hlst.trans h0)

/-- `ORDINAL2:sch 9` (`TSResultS`). -/
theorem sch_TSResultS {B0 : TarskiSet.{u}}
    (F : TarskiSet.{u} → TarskiSet.{u})
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hchar : ∀ E, ORDINAL1.isOrdinal E → ∀ x,
      x = F E ↔ RecWitness E x B0 C D) :
    ∀ E, ORDINAL1.isOrdinal E → F (ORDINAL1.succ E) = C E (F E) := by
  intro E hE
  obtain ⟨L, hL, hx, hd, h0, hs, hl⟩ :=
    (hchar (ORDINAL1.succ E) (ORDINAL1.th17 hE)
      (F (ORDINAL1.succ E))).mp rfl
  have hlast := th6 hL (ORDINAL1.th17 hE) hd
  have htop : ORDINAL1.succ E ∈ ORDINAL1.succ (ORDINAL1.succ E) :=
    ORDINAL1.th6 _
  have hrec := hs E hE htop
  have hprev : FUNCT_1.apply L E = F E := by
    apply (hchar E hE (FUNCT_1.apply L E)).mpr
    exact prefix_recWitness hL hE
      (Eq.subst (motive := fun s => E ∈ s) hd.symm
        ((ORDINAL1.th17 (ORDINAL1.th17 hE)).1 (ORDINAL1.succ E) htop E
          (ORDINAL1.th6 E)))
      (fun _ => h0) C D
      (fun B hB hBin => hs B hB
        (Eq.subst (motive := fun s => ORDINAL1.succ B ∈ s) hd hBin))
      (fun B hB hBin hn hlm => hl B hB
        (Eq.subst (motive := fun s => B ∈ s) hd hBin) hn hlm)
  exact hx.trans (hlast.trans (hrec.trans (congrArg (C E) hprev)))

/-- `ORDINAL2:sch 10` (`TSResultL`). -/
theorem sch_TSResultL {L A B0 : TarskiSet.{u}}
    (F : TarskiSet.{u} → TarskiSet.{u})
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hchar : ∀ E, ORDINAL1.isOrdinal E → ∀ x,
      x = F E ↔ RecWitness E x B0 C D)
    (hA : ORDINAL1.isOrdinal A) (hne : A ≠ (∅ : TarskiSet.{u}))
    (hlim : ORDINAL1.isLimitOrdinal A)
    (hL : ORDINAL1.isTSequence L) (hdom : RELAT_1.dom L = A)
    (hv : ∀ E, ORDINAL1.isOrdinal E → E ∈ A →
      FUNCT_1.apply L E = F E) :
    F A = D A L := by
  obtain ⟨W, hW, hx, hdW, h0W, hsW, hlW⟩ :=
    (hchar A hA (F A)).mp rfl
  have hAin : A ∈ ORDINAL1.succ A := ORDINAL1.th6 A
  have hWA := hlW A hA hAin hne hlim
  have hlast := th6 hW hA hdW
  have hrestDom : RELAT_1.dom (RELAT_1.restrict W A) = A :=
    RELAT_1.th62 (R := W) (X := A)
      (Eq.subst (motive := fun s => A ⊆ s) hdW.symm
        ((ORDINAL1.th17 hA).1 A hAin))
  have hrestTS : ORDINAL1.isTSequence (RELAT_1.restrict W A) :=
    ORDINAL1.restrict_isTSequence hW hA
  have hWL : RELAT_1.restrict W A = L := by
    apply FUNCT_1.th2 hrestTS.1 hL.1 (hrestDom.trans hdom.symm)
    intro E hEd
    have hEA : E ∈ A :=
      Eq.subst (motive := fun s => E ∈ s) hrestDom hEd
    have hEord := ORDINAL1.th13 hA hEA
    have hEW : E ∈ RELAT_1.dom W :=
      Eq.subst (motive := fun s => E ∈ s) hdW.symm
        ((ORDINAL1.th17 hA).1 A hAin E hEA)
    have hpre : FUNCT_1.apply W E = F E := by
      apply (hchar E hEord (FUNCT_1.apply W E)).mpr
      exact prefix_recWitness hW hEord hEW (fun _ => h0W) C D
        (fun B hB hBin => hsW B hB
          (Eq.subst (motive := fun s => ORDINAL1.succ B ∈ s) hdW hBin))
        (fun B hB hBin hn hlm => hlW B hB
          (Eq.subst (motive := fun s => B ∈ s) hdW hBin) hn hlm)
    exact (FUNCT_1.th47 hW.1.2 hEd).trans
      (hpre.trans (hv E hEord hEA).symm)
  exact hx.trans (hlast.trans (hWA.trans (congrArg (D A) hWL)))

/-- `ORDINAL2:sch 11` (`OSExist`). -/
theorem sch_OSExist {A B0 : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB0 : ORDINAL1.isOrdinal B0)
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hC : ∀ E x, ORDINAL1.isOrdinal E → ORDINAL1.isOrdinal x →
      ORDINAL1.isOrdinal (C E x))
    (hD : ∀ E L, ORDINAL1.isOrdinal E → ORDINAL1.isTSequence L →
      ORDINAL1.isOrdinal (D E L)) :
    ∃ fi, isOrdinalSequence fi ∧ RELAT_1.dom fi = A ∧
      ((∅ : TarskiSet.{u}) ∈ A →
        FUNCT_1.apply fi (∅ : TarskiSet.{u}) = B0) ∧
      (∀ E, ORDINAL1.isOrdinal E → ORDINAL1.succ E ∈ A →
        FUNCT_1.apply fi (ORDINAL1.succ E) =
          C E (FUNCT_1.apply fi E)) ∧
      (∀ E, ORDINAL1.isOrdinal E → E ∈ A →
        E ≠ (∅ : TarskiSet.{u}) → ORDINAL1.isLimitOrdinal E →
        FUNCT_1.apply fi E = D E (RELAT_1.restrict fi E)) := by
  let CC := fun E x => C E (sup (TARSKI.union (TARSKI.singleton x)))
  obtain ⟨L, hL, hd, h0, hs, hl⟩ :=
    sch_TSExist1 (A := A) (B0 := B0) hA CC D
  have hord : ∀ y, y ∈ RELAT_1.dom L →
      ORDINAL1.isOrdinal (FUNCT_1.apply L y) := by
    intro y hy
    have hyA : y ∈ A := Eq.subst (motive := fun s => y ∈ s) hd hy
    have hyord := ORDINAL1.th13 hA hyA
    by_cases he : y = (∅ : TarskiSet.{u})
    · exact Eq.subst (motive := fun s =>
        ORDINAL1.isOrdinal (FUNCT_1.apply L s)) he.symm
        (Eq.subst (motive := ORDINAL1.isOrdinal)
          (h0 (Eq.subst (motive := fun s => s ∈ A) he hyA)).symm hB0)
    · by_cases hlim : ORDINAL1.isLimitOrdinal y
      · exact Eq.subst (motive := ORDINAL1.isOrdinal)
          (hl y hyord hyA he hlim).symm
          (hD y (RELAT_1.restrict L y) hyord
            (ORDINAL1.restrict_isTSequence hL hyord))
      · obtain ⟨E, hE, hey⟩ := (ORDINAL1.th29 hyord).mp hlim
        have hsIn : ORDINAL1.succ E ∈ A :=
          Eq.subst (motive := fun s => s ∈ A) hey hyA
        exact Eq.subst (motive := ORDINAL1.isOrdinal)
          ((Eq.subst (motive := fun s => FUNCT_1.apply L s =
            CC E (FUNCT_1.apply L E)) hey.symm (hs E hE hsIn))).symm
          (hC E (sup (TARSKI.union
            (TARSKI.singleton (FUNCT_1.apply L E)))) hE (sup_isOrdinal _))
  have hOY : isOrdinalYielding L := by
    refine ⟨sup (RELAT_1.rng L), sup_isOrdinal _, ?_⟩
    intro x hx
    obtain ⟨y, hy, heq⟩ := (FUNCT_1.def3 hL.1.2).mp hx
    have hxord : ORDINAL1.isOrdinal x :=
      Eq.subst (motive := ORDINAL1.isOrdinal) heq.symm (hord y hy)
    exact (def3 (RELAT_1.rng L)).1 x
      ((ORDINAL1.def9 _ x).mpr ⟨hx, hxord⟩)
  refine ⟨L, ⟨hL, hOY⟩, hd, h0, ?_, hl⟩
  intro E hE hsIn
  have hEin : E ∈ RELAT_1.dom L :=
    Eq.subst (motive := fun s => E ∈ s) hd.symm
      (hA.1 (ORDINAL1.succ E) hsIn E (ORDINAL1.th6 E))
  have hvord := hord E hEin
  have hsingle : TARSKI.union (TARSKI.singleton (FUNCT_1.apply L E)) =
      FUNCT_1.apply L E := ZFMISC_1.th25
  have hsup : sup (TARSKI.union (TARSKI.singleton (FUNCT_1.apply L E))) =
      FUNCT_1.apply L E :=
    (congrArg sup hsingle).trans (th18 hvord)
  exact (hs E hE hsIn).trans (congrArg (C E) hsup)

/-- Common ordinal-valued witness predicate in the `OS*` schemes. -/
def OSRecWitness (A x B0 : TarskiSet.{u})
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u}) : Prop :=
  ∃ fi, isOrdinalSequence fi ∧ x = last fi ∧
    RELAT_1.dom fi = ORDINAL1.succ A ∧
    FUNCT_1.apply fi (∅ : TarskiSet.{u}) = B0 ∧
    (∀ E, ORDINAL1.isOrdinal E → ORDINAL1.succ E ∈ ORDINAL1.succ A →
      FUNCT_1.apply fi (ORDINAL1.succ E) =
        C E (FUNCT_1.apply fi E)) ∧
    (∀ E, ORDINAL1.isOrdinal E → E ∈ ORDINAL1.succ A →
      E ≠ (∅ : TarskiSet.{u}) → ORDINAL1.isLimitOrdinal E →
      FUNCT_1.apply fi E = D E (RELAT_1.restrict fi E))

private theorem prefix_OSRecWitness {fi A B0 : TarskiSet.{u}}
    (hfi : isOrdinalSequence fi) (hA : ORDINAL1.isOrdinal A)
    (hAin : A ∈ RELAT_1.dom fi)
    (h0 : (∅ : TarskiSet.{u}) ∈ RELAT_1.dom fi →
      FUNCT_1.apply fi (∅ : TarskiSet.{u}) = B0)
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hs : ∀ E, ORDINAL1.isOrdinal E →
      ORDINAL1.succ E ∈ RELAT_1.dom fi →
      FUNCT_1.apply fi (ORDINAL1.succ E) = C E (FUNCT_1.apply fi E))
    (hl : ∀ E, ORDINAL1.isOrdinal E → E ∈ RELAT_1.dom fi →
      E ≠ (∅ : TarskiSet.{u}) → ORDINAL1.isLimitOrdinal E →
      FUNCT_1.apply fi E = D E (RELAT_1.restrict fi E)) :
    OSRecWitness A (FUNCT_1.apply fi A) B0 C D := by
  let K := RELAT_1.restrict fi (ORDINAL1.succ A)
  have hsub : ORDINAL1.succ A ⊆ RELAT_1.dom fi :=
    (ORDINAL1.th21 hA hfi.1.2).mp hAin
  have hKdom : RELAT_1.dom K = ORDINAL1.succ A :=
    RELAT_1.th62 (R := fi) (X := ORDINAL1.succ A) hsub
  have hKOS : isOrdinalSequence K :=
    restrict_ordinal_sequence hfi (ORDINAL1.th17 hA)
  have hlast : FUNCT_1.apply fi A = last K := by
    have hkapp : FUNCT_1.apply K A = FUNCT_1.apply fi A :=
      FUNCT_1.th49 hfi.1.1.2 (ORDINAL1.th6 A)
    exact hkapp.symm.trans (th6 hKOS.1 hA hKdom).symm
  refine ⟨K, hKOS, hlast, hKdom, ?_, ?_, ?_⟩
  · have he := empty_mem_succ A hA
    exact (FUNCT_1.th49 hfi.1.1.2 he).trans (h0 (hsub _ he))
  · intro E hE hEs
    have hEin : E ∈ ORDINAL1.succ A :=
      ((ORDINAL1.th17 hA).1 (ORDINAL1.succ E) hEs) E (ORDINAL1.th6 E)
    exact (FUNCT_1.th49 hfi.1.1.2 hEs).trans
      ((hs E hE (hsub _ hEs)).trans
        (congrArg (C E) (FUNCT_1.th49 hfi.1.1.2 hEin).symm))
  · intro E hE hEin hn hlm
    have hEsub : E ⊆ ORDINAL1.succ A :=
      (ORDINAL1.th17 hA).1 E hEin
    have hr : RELAT_1.restrict K E = RELAT_1.restrict fi E :=
      (FUNCT_1.th51 (f := fi) (X := E) (Y := ORDINAL1.succ A) hEsub).2
    exact (FUNCT_1.th49 hfi.1.1.2 hEin).trans
      ((hl E hE (hsub _ hEin) hn hlm).trans (congrArg (D E) hr.symm))

/-- `ORDINAL2:sch 12` (`OSResult`). -/
theorem sch_OSResult {fi A B0 : TarskiSet.{u}}
    (F : TarskiSet.{u} → TarskiSet.{u})
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hchar : ∀ E, ORDINAL1.isOrdinal E → ∀ x, ORDINAL1.isOrdinal x →
      (x = F E ↔ OSRecWitness E x B0 C D))
    (hfi : isOrdinalSequence fi) (hdom : RELAT_1.dom fi = A)
    (h0 : (∅ : TarskiSet.{u}) ∈ A →
      FUNCT_1.apply fi (∅ : TarskiSet.{u}) = B0)
    (hs : ∀ E, ORDINAL1.isOrdinal E → ORDINAL1.succ E ∈ A →
      FUNCT_1.apply fi (ORDINAL1.succ E) = C E (FUNCT_1.apply fi E))
    (hl : ∀ E, ORDINAL1.isOrdinal E → E ∈ A →
      E ≠ (∅ : TarskiSet.{u}) → ORDINAL1.isLimitOrdinal E →
      FUNCT_1.apply fi E = D E (RELAT_1.restrict fi E)) :
    ∀ E, ORDINAL1.isOrdinal E → E ∈ RELAT_1.dom fi →
      FUNCT_1.apply fi E = F E := by
  intro E hE hEin
  apply (hchar E hE (FUNCT_1.apply fi E) (th25 hfi hEin)).mpr
  exact prefix_OSRecWitness hfi hE hEin
    (fun he => h0 (Eq.subst (motive := fun s =>
      (∅ : TarskiSet.{u}) ∈ s) hdom he)) C D
    (fun B hB hBin => hs B hB
      (Eq.subst (motive := fun s => ORDINAL1.succ B ∈ s) hdom hBin))
    (fun B hB hBin hn hlm => hl B hB
      (Eq.subst (motive := fun s => B ∈ s) hdom hBin) hn hlm)

/-- `ORDINAL2:sch 13` (`OSDef`). -/
theorem sch_OSDef {A B0 : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB0 : ORDINAL1.isOrdinal B0)
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hC : ∀ E x, ORDINAL1.isOrdinal E → ORDINAL1.isOrdinal x →
      ORDINAL1.isOrdinal (C E x))
    (hD : ∀ E L, ORDINAL1.isOrdinal E → ORDINAL1.isTSequence L →
      ORDINAL1.isOrdinal (D E L)) :
    (∃ x, ORDINAL1.isOrdinal x ∧ OSRecWitness A x B0 C D) ∧
      ∀ x1 x2, ORDINAL1.isOrdinal x1 → ORDINAL1.isOrdinal x2 →
        OSRecWitness A x1 B0 C D → OSRecWitness A x2 B0 C D →
        x1 = x2 := by
  obtain ⟨fi, hfi, hd, h0, hs, hl⟩ :=
    sch_OSExist (A := ORDINAL1.succ A) (B0 := B0)
      (ORDINAL1.th17 hA) hB0 C D hC hD
  have hlastord : ORDINAL1.isOrdinal (last fi) := by
    rw [th6 hfi.1 hA hd]
    exact th25 hfi (Eq.subst (motive := fun s =>
      A ∈ s) hd.symm (ORDINAL1.th6 _))
  have hw : OSRecWitness A (last fi) B0 C D :=
    ⟨fi, hfi, rfl, hd, h0 (empty_mem_succ A hA), hs, hl⟩
  refine ⟨⟨last fi, hlastord, hw⟩, ?_⟩
  intro x1 x2 _ _ hx1 hx2
  obtain ⟨L1, hL1, hx1, hd1, h01, hs1, hl1⟩ := hx1
  obtain ⟨L2, hL2, hx2, hd2, h02, hs2, hl2⟩ := hx2
  have heq := sch_TSUniq1 (A := ORDINAL1.succ A) (B0 := B0)
    (ORDINAL1.th17 hA) C D hL1.1 hL2.1 hd1 hd2
    (fun _ => h01) hs1 hl1 (fun _ => h02) hs2 hl2
  exact hx1.trans ((congrArg last heq).trans hx2.symm)

/-- `ORDINAL2:sch 14` (`OSResult0`). -/
theorem sch_OSResult0 {B0 : TarskiSet.{u}}
    (F : TarskiSet.{u} → TarskiSet.{u})
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ E, ORDINAL1.isOrdinal (F E))
    (hchar : ∀ E, ORDINAL1.isOrdinal E → ∀ x, ORDINAL1.isOrdinal x →
      (x = F E ↔ OSRecWitness E x B0 C D)) :
    F (∅ : TarskiSet.{u}) = B0 := by
  obtain ⟨fi, hfi, hx, hd, h0, _hs, _hl⟩ :=
    (hchar (∅ : TarskiSet.{u}) ORDINAL1.empty_isOrdinal
      (F (∅ : TarskiSet.{u})) (hF _)).mp rfl
  exact hx.trans ((th6 hfi.1 ORDINAL1.empty_isOrdinal hd).trans h0)

/-- `ORDINAL2:sch 15` (`OSResultS`). -/
theorem sch_OSResultS {B0 : TarskiSet.{u}}
    (F : TarskiSet.{u} → TarskiSet.{u})
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ E, ORDINAL1.isOrdinal (F E))
    (hchar : ∀ E, ORDINAL1.isOrdinal E → ∀ x, ORDINAL1.isOrdinal x →
      (x = F E ↔ OSRecWitness E x B0 C D)) :
    ∀ E, ORDINAL1.isOrdinal E → F (ORDINAL1.succ E) = C E (F E) := by
  intro E hE
  obtain ⟨fi, hfi, hx, hd, h0, hs, hl⟩ :=
    (hchar (ORDINAL1.succ E) (ORDINAL1.th17 hE)
      (F (ORDINAL1.succ E)) (hF _)).mp rfl
  have htop : ORDINAL1.succ E ∈ ORDINAL1.succ (ORDINAL1.succ E) :=
    ORDINAL1.th6 _
  have hprev : FUNCT_1.apply fi E = F E := by
    apply (hchar E hE (FUNCT_1.apply fi E)
      (apply_ordinal_sequence hfi hE)).mpr
    exact prefix_OSRecWitness hfi hE
      (Eq.subst (motive := fun s => E ∈ s) hd.symm
        ((ORDINAL1.th17 (ORDINAL1.th17 hE)).1
          (ORDINAL1.succ E) htop E (ORDINAL1.th6 E)))
      (fun _ => h0) C D
      (fun B hB hBin => hs B hB
        (Eq.subst (motive := fun s => ORDINAL1.succ B ∈ s) hd hBin))
      (fun B hB hBin hn hlm => hl B hB
        (Eq.subst (motive := fun s => B ∈ s) hd hBin) hn hlm)
  exact hx.trans ((th6 hfi.1 (ORDINAL1.th17 hE) hd).trans
    ((hs E hE htop).trans (congrArg (C E) hprev)))

/-- `ORDINAL2:sch 16` (`OSResultL`). -/
theorem sch_OSResultL {fi A B0 : TarskiSet.{u}}
    (F : TarskiSet.{u} → TarskiSet.{u})
    (C : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (D : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ E, ORDINAL1.isOrdinal (F E))
    (hchar : ∀ E, ORDINAL1.isOrdinal E → ∀ x, ORDINAL1.isOrdinal x →
      (x = F E ↔ OSRecWitness E x B0 C D))
    (hA : ORDINAL1.isOrdinal A) (hne : A ≠ (∅ : TarskiSet.{u}))
    (hlim : ORDINAL1.isLimitOrdinal A)
    (hfi : isOrdinalSequence fi) (hdom : RELAT_1.dom fi = A)
    (hv : ∀ E, ORDINAL1.isOrdinal E → E ∈ A →
      FUNCT_1.apply fi E = F E) :
    F A = D A fi := by
  obtain ⟨W, hW, hx, hdW, h0W, hsW, hlW⟩ :=
    (hchar A hA (F A) (hF A)).mp rfl
  have hAin : A ∈ ORDINAL1.succ A := ORDINAL1.th6 A
  have hrestDom : RELAT_1.dom (RELAT_1.restrict W A) = A :=
    RELAT_1.th62 (R := W) (X := A)
      (Eq.subst (motive := fun s => A ⊆ s) hdW.symm
        ((ORDINAL1.th17 hA).1 A hAin))
  have hrestOS : isOrdinalSequence (RELAT_1.restrict W A) :=
    restrict_ordinal_sequence hW hA
  have hEq : RELAT_1.restrict W A = fi := by
    apply FUNCT_1.th2 hrestOS.1.1 hfi.1.1
      (hrestDom.trans hdom.symm)
    intro E hEd
    have hEA : E ∈ A :=
      Eq.subst (motive := fun s => E ∈ s) hrestDom hEd
    have hEord := ORDINAL1.th13 hA hEA
    have hEW : E ∈ RELAT_1.dom W :=
      Eq.subst (motive := fun s => E ∈ s) hdW.symm
        ((ORDINAL1.th17 hA).1 A hAin E hEA)
    have hpre : FUNCT_1.apply W E = F E := by
      apply (hchar E hEord (FUNCT_1.apply W E)
        (apply_ordinal_sequence hW hEord)).mpr
      exact prefix_OSRecWitness hW hEord hEW (fun _ => h0W) C D
        (fun B hB hBin => hsW B hB
          (Eq.subst (motive := fun s => ORDINAL1.succ B ∈ s) hdW hBin))
        (fun B hB hBin hn hlm => hlW B hB
          (Eq.subst (motive := fun s => B ∈ s) hdW hBin) hn hlm)
    exact (FUNCT_1.th47 hW.1.1.2 hEd).trans
      (hpre.trans (hv E hEord hEA).symm)
  exact hx.trans ((th6 hW.1 hA hdW).trans
    ((hlW A hA hAin hne hlim).trans (congrArg (D A) hEq)))

/-! ## Sequence suprema, infima, limsup, and liminf -/

/-- `ORDINAL2:def 5` — `sup L`. -/
noncomputable def sequenceSup (L : TarskiSet.{u}) : TarskiSet.{u} :=
  sup (RELAT_1.rng L)

/-- `ORDINAL2:def 6` — `inf L`. -/
noncomputable def sequenceInf (L : TarskiSet.{u}) : TarskiSet.{u} :=
  inf (RELAT_1.rng L)

theorem def5 (L : TarskiSet.{u}) :
    sequenceSup L = sup (RELAT_1.rng L) := rfl

theorem def6 (L : TarskiSet.{u}) :
    sequenceInf L = inf (RELAT_1.rng L) := rfl

theorem sequenceSup_isOrdinal (L : TarskiSet.{u}) :
    ORDINAL1.isOrdinal (sequenceSup L) := sup_isOrdinal _

theorem sequenceInf_isOrdinal (L : TarskiSet.{u}) :
    ORDINAL1.isOrdinal (sequenceInf L) := inf_isOrdinal _

/-- `ORDINAL2:26` (the defining equalities for sequence `sup` and `inf`). -/
theorem th26 (L : TarskiSet.{u}) :
    sequenceSup L = sup (RELAT_1.rng L) ∧
      sequenceInf L = inf (RELAT_1.rng L) :=
  ⟨rfl, rfl⟩

private theorem tailSup_exists (L : TarskiSet.{u})
    (hL : ORDINAL1.isTSequence L) :
    ∃ fi, isOrdinalSequence fi ∧ RELAT_1.dom fi = RELAT_1.dom L ∧
      ∀ A, ORDINAL1.isOrdinal A → A ∈ RELAT_1.dom L →
        FUNCT_1.apply fi A =
          sequenceSup (RELAT_1.restrict L
            (XBOOLE_0.sdiffSet (RELAT_1.dom L) A)) :=
  sch_OSLambda hL.2
    (fun A => sequenceSup (RELAT_1.restrict L
      (XBOOLE_0.sdiffSet (RELAT_1.dom L) A)))
    (fun _ _ _ => sequenceSup_isOrdinal _)

private theorem tailInf_exists (L : TarskiSet.{u})
    (hL : ORDINAL1.isTSequence L) :
    ∃ fi, isOrdinalSequence fi ∧ RELAT_1.dom fi = RELAT_1.dom L ∧
      ∀ A, ORDINAL1.isOrdinal A → A ∈ RELAT_1.dom L →
        FUNCT_1.apply fi A =
          sequenceInf (RELAT_1.restrict L
            (XBOOLE_0.sdiffSet (RELAT_1.dom L) A)) :=
  sch_OSLambda hL.2
    (fun A => sequenceInf (RELAT_1.restrict L
      (XBOOLE_0.sdiffSet (RELAT_1.dom L) A)))
    (fun _ _ _ => sequenceInf_isOrdinal _)

/-- Canonical witness used in `ORDINAL2:def 7`. -/
noncomputable def tailSupSequence (L : TarskiSet.{u})
    (hL : ORDINAL1.isTSequence L) : TarskiSet.{u} :=
  Classical.choose (tailSup_exists L hL)

/-- Canonical witness used in `ORDINAL2:def 8`. -/
noncomputable def tailInfSequence (L : TarskiSet.{u})
    (hL : ORDINAL1.isTSequence L) : TarskiSet.{u} :=
  Classical.choose (tailInf_exists L hL)

/-- `ORDINAL2:def 7` — `lim_sup L`. -/
noncomputable def limSup (L : TarskiSet.{u})
    (hL : ORDINAL1.isTSequence L) : TarskiSet.{u} :=
  sequenceInf (tailSupSequence L hL)

/-- `ORDINAL2:def 8` — `lim_inf L`. -/
noncomputable def limInf (L : TarskiSet.{u})
    (hL : ORDINAL1.isTSequence L) : TarskiSet.{u} :=
  sequenceSup (tailInfSequence L hL)

theorem limSup_isOrdinal (L : TarskiSet.{u})
    (hL : ORDINAL1.isTSequence L) :
    ORDINAL1.isOrdinal (limSup L hL) :=
  sequenceInf_isOrdinal _

theorem limInf_isOrdinal (L : TarskiSet.{u})
    (hL : ORDINAL1.isTSequence L) :
    ORDINAL1.isOrdinal (limInf L hL) :=
  sequenceSup_isOrdinal _

theorem def7 (L : TarskiSet.{u}) (hL : ORDINAL1.isTSequence L) :
    ∃ fi, isOrdinalSequence fi ∧
      limSup L hL = sequenceInf fi ∧
      RELAT_1.dom fi = RELAT_1.dom L ∧
      ∀ A, ORDINAL1.isOrdinal A → A ∈ RELAT_1.dom L →
        FUNCT_1.apply fi A =
          sequenceSup (RELAT_1.restrict L
            (XBOOLE_0.sdiffSet (RELAT_1.dom L) A)) := by
  let h := Classical.choose_spec (tailSup_exists L hL)
  exact ⟨tailSupSequence L hL, h.1, rfl, h.2.1, h.2.2⟩

theorem def8 (L : TarskiSet.{u}) (hL : ORDINAL1.isTSequence L) :
    ∃ fi, isOrdinalSequence fi ∧
      limInf L hL = sequenceSup fi ∧
      RELAT_1.dom fi = RELAT_1.dom L ∧
      ∀ A, ORDINAL1.isOrdinal A → A ∈ RELAT_1.dom L →
        FUNCT_1.apply fi A =
          sequenceInf (RELAT_1.restrict L
            (XBOOLE_0.sdiffSet (RELAT_1.dom L) A)) := by
  let h := Classical.choose_spec (tailInf_exists L hL)
  exact ⟨tailInfSequence L hL, h.1, rfl, h.2.1, h.2.2⟩

/-! ## Limits of ordinal sequences -/

/-- `ORDINAL2:def 9` — `A is_limes_of fi`. -/
def isLimesOf (A fi : TarskiSet.{u}) : Prop :=
  (A = (∅ : TarskiSet.{u}) →
    ∃ B, ORDINAL1.isOrdinal B ∧ B ∈ RELAT_1.dom fi ∧
      ∀ C, ORDINAL1.isOrdinal C → B ⊆ C → C ∈ RELAT_1.dom fi →
        FUNCT_1.apply fi C = (∅ : TarskiSet.{u})) ∧
  (A ≠ (∅ : TarskiSet.{u}) →
    ∀ B C, ORDINAL1.isOrdinal B → ORDINAL1.isOrdinal C →
      B ∈ A → A ∈ C →
      ∃ D, ORDINAL1.isOrdinal D ∧ D ∈ RELAT_1.dom fi ∧
        ∀ E, ORDINAL1.isOrdinal E → D ⊆ E → E ∈ RELAT_1.dom fi →
          B ∈ FUNCT_1.apply fi E ∧ FUNCT_1.apply fi E ∈ C)

theorem def9 (A fi : TarskiSet.{u}) :
    isLimesOf A fi ↔
      ((A = (∅ : TarskiSet.{u}) →
        ∃ B, ORDINAL1.isOrdinal B ∧ B ∈ RELAT_1.dom fi ∧
          ∀ C, ORDINAL1.isOrdinal C → B ⊆ C →
            C ∈ RELAT_1.dom fi →
            FUNCT_1.apply fi C = (∅ : TarskiSet.{u})) ∧
       (A ≠ (∅ : TarskiSet.{u}) →
        ∀ B C, ORDINAL1.isOrdinal B → ORDINAL1.isOrdinal C →
          B ∈ A → A ∈ C →
          ∃ D, ORDINAL1.isOrdinal D ∧ D ∈ RELAT_1.dom fi ∧
            ∀ E, ORDINAL1.isOrdinal E → D ⊆ E →
              E ∈ RELAT_1.dom fi →
              B ∈ FUNCT_1.apply fi E ∧ FUNCT_1.apply fi E ∈ C)) :=
  Iff.rfl

private theorem common_upper_in_dom {fi B D : TarskiSet.{u}}
    (hfi : isOrdinalSequence fi) (hB : B ∈ RELAT_1.dom fi)
    (hD : D ∈ RELAT_1.dom fi) :
    ∃ E, ORDINAL1.isOrdinal E ∧ E ∈ RELAT_1.dom fi ∧ B ⊆ E ∧ D ⊆ E := by
  have hBo := ORDINAL1.th13 hfi.1.2 hB
  have hDo := ORDINAL1.th13 hfi.1.2 hD
  rcases ORDINAL1.th15 hBo hDo with h | h
  · exact ⟨D, hDo, hD, h, subset_refl D⟩
  · exact ⟨B, hBo, hB, subset_refl B, h⟩

private theorem limes_unique {fi A1 A2 : TarskiSet.{u}}
    (hfi : isOrdinalSequence fi) (hA1 : ORDINAL1.isOrdinal A1)
    (hA2 : ORDINAL1.isOrdinal A2)
    (hl1 : isLimesOf A1 fi) (hl2 : isLimesOf A2 fi) : A1 = A2 := by
  have not_mem : ∀ X Y, ORDINAL1.isOrdinal X → ORDINAL1.isOrdinal Y →
      isLimesOf X fi → isLimesOf Y fi → ¬ X ∈ Y := by
    intro X Y hX hY hx hy hXY
    have hYne : Y ≠ (∅ : TarskiSet.{u}) := fun he =>
      (XBOOLE_0.empty_iff X).mp
        (Eq.subst (motive := fun s => X ∈ s) he hXY)
    obtain ⟨D, hDo, hDd, hDY⟩ :=
      hy.2 hYne X (ORDINAL1.succ Y) hX (ORDINAL1.th17 hY)
        hXY (ORDINAL1.th6 Y)
    by_cases hXe : X = (∅ : TarskiSet.{u})
    · obtain ⟨B, hBo, hBd, hBX⟩ := hx.1 hXe
      obtain ⟨E, hEo, hEd, hBE, hDE⟩ :=
        common_upper_in_dom hfi hBd hDd
      have hz := hBX E hEo hBE hEd
      have hxy := (hDY E hEo hDE hEd).1
      exact (XBOOLE_0.empty_iff X).mp
        (Eq.subst (motive := fun s => X ∈ s) hz hxy)
    · obtain ⟨x, hxX⟩ := XBOOLE_0.th7 hXe
      have hxo := ORDINAL1.th13 hX hxX
      obtain ⟨C0, hCo, hCd, hCX⟩ :=
        hx.2 hXe x (ORDINAL1.succ X) hxo (ORDINAL1.th17 hX)
          hxX (ORDINAL1.th6 X)
      obtain ⟨E, hEo, hEd, hCE, hDE⟩ :=
        common_upper_in_dom hfi hCd hDd
      have h1 := (hDY E hEo hDE hEd).1
      have h2 := (hCX E hEo hCE hEd).2
      rcases (ORDINAL1.th8 (FUNCT_1.apply fi E) X).mp h2 with hin | heq
      · exact ORDINAL1.th5 h1 (hX.1 _ hin)
      · exact ORDINAL1.th5
          (Eq.subst (motive := fun s => X ∈ s) heq h1) (subset_refl X)
  rcases ORDINAL1.th14 hA1 hA2 with h12 | heq | h21
  · exact (not_mem A1 A2 hA1 hA2 hl1 hl2 h12).elim
  · exact heq
  · exact (not_mem A2 A1 hA2 hA1 hl2 hl1 h21).elim

/-- `ORDINAL2:def 10` — `lim fi`; Mizar introduces this functor only under
the `given A such that A is_limes_of fi` guard.  The empty ordinal is the
irrelevant value outside that guard. -/
noncomputable def lim (fi : TarskiSet.{u}) : TarskiSet.{u} := by
  classical
  exact if h : ∃ A, ORDINAL1.isOrdinal A ∧ isLimesOf A fi
    then Classical.choose h
    else (∅ : TarskiSet.{u})

theorem lim_isOrdinal (fi : TarskiSet.{u}) :
    ORDINAL1.isOrdinal (lim fi) := by
  classical
  unfold lim
  split
  · rename_i h
    exact (Classical.choose_spec h).1
  · exact ORDINAL1.empty_isOrdinal

theorem def10 {fi : TarskiSet.{u}}
    (hfi : isOrdinalSequence fi)
    (hex : ∃ A, ORDINAL1.isOrdinal A ∧ isLimesOf A fi) :
    isLimesOf (lim fi) fi ∧
      ∀ A, ORDINAL1.isOrdinal A → isLimesOf A fi → A = lim fi := by
  classical
  have hs : ORDINAL1.isOrdinal (Classical.choose hex) ∧
      isLimesOf (Classical.choose hex) fi :=
    Classical.choose_spec hex
  have heq : lim fi = Classical.choose hex := by
    unfold lim
    simp only [dif_pos hex]
  refine ⟨Eq.subst (motive := fun s => isLimesOf s fi) heq.symm hs.2, ?_⟩
  intro A hA hlim
  exact (limes_unique hfi hA hs.1 hlim hs.2).trans heq.symm

/-- `ORDINAL2:def 11` — `lim(A,fi)`. -/
noncomputable def limAt (A fi : TarskiSet.{u}) : TarskiSet.{u} :=
  lim (RELAT_1.restrict fi A)

theorem def11 (A fi : TarskiSet.{u}) :
    limAt A fi = lim (RELAT_1.restrict fi A) := rfl

theorem limAt_isOrdinal (A fi : TarskiSet.{u}) :
    ORDINAL1.isOrdinal (limAt A fi) :=
  lim_isOrdinal _

/-- `ORDINAL2:def 12` — increasing ordinal sequence. -/
def isIncreasing (L : TarskiSet.{u}) : Prop :=
  ∀ A B, ORDINAL1.isOrdinal A → ORDINAL1.isOrdinal B →
    A ∈ B → B ∈ RELAT_1.dom L →
    FUNCT_1.apply L A ∈ FUNCT_1.apply L B

/-- `ORDINAL2:def 13` — continuous ordinal sequence. -/
def isContinuous (L : TarskiSet.{u}) : Prop :=
  ∀ A, ORDINAL1.isOrdinal A → A ∈ RELAT_1.dom L →
    A ≠ (∅ : TarskiSet.{u}) → ORDINAL1.isLimitOrdinal A →
    isLimesOf (FUNCT_1.apply L A) (RELAT_1.restrict L A)

theorem def12 (L : TarskiSet.{u}) :
    isIncreasing L ↔
      ∀ A B, ORDINAL1.isOrdinal A → ORDINAL1.isOrdinal B →
        A ∈ B → B ∈ RELAT_1.dom L →
        FUNCT_1.apply L A ∈ FUNCT_1.apply L B :=
  Iff.rfl

theorem def13 (L : TarskiSet.{u}) :
    isContinuous L ↔
      ∀ A, ORDINAL1.isOrdinal A → A ∈ RELAT_1.dom L →
        A ≠ (∅ : TarskiSet.{u}) → ORDINAL1.isLimitOrdinal A →
        isLimesOf (FUNCT_1.apply L A) (RELAT_1.restrict L A) :=
  Iff.rfl

/-! ## Ordinal addition -/

private theorem add_exists (A B : TarskiSet.{u})
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B) :
    ∃ x, ORDINAL1.isOrdinal x ∧
      OSRecWitness B x A
        (fun _ y => ORDINAL1.succ y)
        (fun _ L => sequenceSup L) :=
  (sch_OSDef hB hA
    (fun _ y => ORDINAL1.succ y)
    (fun _ L => sequenceSup L)
    (fun _ y _ hy => ORDINAL1.th17 hy)
    (fun _ L _ _ => sequenceSup_isOrdinal L)).1

/-- `ORDINAL2:def 14` — ordinal addition `A +^ B`.  Outside the Mizar
ordinal typing discipline the value is the empty ordinal. -/
noncomputable def ordinalAdd (A B : TarskiSet.{u}) : TarskiSet.{u} := by
  classical
  exact if h : ORDINAL1.isOrdinal A ∧ ORDINAL1.isOrdinal B
    then Classical.choose (add_exists A B h.1 h.2)
    else (∅ : TarskiSet.{u})

theorem ordinalAdd_isOrdinal (A B : TarskiSet.{u}) :
    ORDINAL1.isOrdinal (ordinalAdd A B) := by
  classical
  unfold ordinalAdd
  split
  · rename_i h
    exact (Classical.choose_spec (add_exists A B h.1 h.2)).1
  · exact ORDINAL1.empty_isOrdinal

theorem def14 {A B : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B) :
    OSRecWitness B (ordinalAdd A B) A
      (fun _ y => ORDINAL1.succ y)
      (fun _ L => sequenceSup L) := by
  classical
  have hp : ORDINAL1.isOrdinal A ∧ ORDINAL1.isOrdinal B := ⟨hA, hB⟩
  unfold ordinalAdd
  rw [dif_pos hp]
  exact (Classical.choose_spec (add_exists A B hp.1 hp.2)).2

/-- `ORDINAL2:27` (`Th27`). -/
theorem th27 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ordinalAdd A (∅ : TarskiSet.{u}) = A := by
  obtain ⟨fi, hfi, hx, hd, h0, _hs, _hl⟩ :=
    def14 hA ORDINAL1.empty_isOrdinal
  exact hx.trans ((th6 hfi.1 ORDINAL1.empty_isOrdinal hd).trans h0)

/-- `ORDINAL2:28` (`Th28`). -/
theorem th28 {A B : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B) :
    ordinalAdd A (ORDINAL1.succ B) =
      ORDINAL1.succ (ordinalAdd A B) := by
  obtain ⟨fi, hfi, hx, hd, h0, hs, hl⟩ :=
    def14 hA (ORDINAL1.th17 hB)
  have htop : ORDINAL1.succ B ∈ ORDINAL1.succ (ORDINAL1.succ B) :=
    ORDINAL1.th6 _
  have hBin : B ∈ RELAT_1.dom fi :=
    Eq.subst (motive := fun s => B ∈ s) hd.symm
      ((ORDINAL1.th17 (ORDINAL1.th17 hB)).1
        (ORDINAL1.succ B) htop B (ORDINAL1.th6 B))
  have hpref : OSRecWitness B (FUNCT_1.apply fi B) A
      (fun _ y => ORDINAL1.succ y) (fun _ L => sequenceSup L) :=
    prefix_OSRecWitness hfi hB hBin (fun _ => h0)
      (fun _ y => ORDINAL1.succ y) (fun _ L => sequenceSup L)
      (fun E hE hEin => hs E hE
        (Eq.subst (motive := fun s => ORDINAL1.succ E ∈ s) hd hEin))
      (fun E hE hEin hn hlm => hl E hE
        (Eq.subst (motive := fun s => E ∈ s) hd hEin) hn hlm)
  have hprev : FUNCT_1.apply fi B = ordinalAdd A B :=
    (sch_OSDef hB hA
      (fun _ y => ORDINAL1.succ y) (fun _ L => sequenceSup L)
      (fun _ y _ hy => ORDINAL1.th17 hy)
      (fun _ L _ _ => sequenceSup_isOrdinal L)).2
      _ _ (apply_ordinal_sequence hfi hB) (ordinalAdd_isOrdinal A B)
      hpref (def14 hA hB)
  exact hx.trans ((th6 hfi.1 (ORDINAL1.th17 hB) hd).trans
    ((hs B hB htop).trans (congrArg ORDINAL1.succ hprev)))

/-- `ORDINAL2:29` (`Th29`). -/
theorem th29 {A B fi : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hne : B ≠ (∅ : TarskiSet.{u})) (hlim : ORDINAL1.isLimitOrdinal B)
    (hfi : isOrdinalSequence fi) (hdom : RELAT_1.dom fi = B)
    (hv : ∀ E, ORDINAL1.isOrdinal E → E ∈ B →
      FUNCT_1.apply fi E = ordinalAdd A E) :
    ordinalAdd A B = sequenceSup fi := by
  obtain ⟨W, hW, hx, hdW, h0W, hsW, hlW⟩ := def14 hA hB
  have hBin : B ∈ ORDINAL1.succ B := ORDINAL1.th6 B
  have hrestDom : RELAT_1.dom (RELAT_1.restrict W B) = B :=
    RELAT_1.th62 (R := W) (X := B)
      (Eq.subst (motive := fun s => B ⊆ s) hdW.symm
        ((ORDINAL1.th17 hB).1 B hBin))
  have hrestOS : isOrdinalSequence (RELAT_1.restrict W B) :=
    restrict_ordinal_sequence hW hB
  have hEq : RELAT_1.restrict W B = fi := by
    apply FUNCT_1.th2 hrestOS.1.1 hfi.1.1
      (hrestDom.trans hdom.symm)
    intro E hEd
    have hEB : E ∈ B :=
      Eq.subst (motive := fun s => E ∈ s) hrestDom hEd
    have hE := ORDINAL1.th13 hB hEB
    have hEW : E ∈ RELAT_1.dom W :=
      Eq.subst (motive := fun s => E ∈ s) hdW.symm
        ((ORDINAL1.th17 hB).1 B hBin E hEB)
    have hpref : OSRecWitness E (FUNCT_1.apply W E) A
        (fun _ y => ORDINAL1.succ y) (fun _ L => sequenceSup L) :=
      prefix_OSRecWitness hW hE hEW (fun _ => h0W)
        (fun _ y => ORDINAL1.succ y) (fun _ L => sequenceSup L)
        (fun C hC hCin => hsW C hC
          (Eq.subst (motive := fun s => ORDINAL1.succ C ∈ s) hdW hCin))
        (fun C hC hCin hn hlm => hlW C hC
          (Eq.subst (motive := fun s => C ∈ s) hdW hCin) hn hlm)
    have happ : FUNCT_1.apply W E = ordinalAdd A E :=
      (sch_OSDef hE hA
        (fun _ y => ORDINAL1.succ y) (fun _ L => sequenceSup L)
        (fun _ y _ hy => ORDINAL1.th17 hy)
        (fun _ L _ _ => sequenceSup_isOrdinal L)).2
        _ _ (apply_ordinal_sequence hW hE) (ordinalAdd_isOrdinal A E)
        hpref (def14 hA hE)
    exact (FUNCT_1.th47 hW.1.1.2 hEd).trans
      (happ.trans (hv E hE hEB).symm)
  exact hx.trans ((th6 hW.1 hB hdW).trans
    ((hlW B hB hBin hne hlim).trans (congrArg sequenceSup hEq)))

/-- `ORDINAL2:30` (`Th30`). -/
theorem th30 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ordinalAdd (∅ : TarskiSet.{u}) A = A := by
  let P := fun B : TarskiSet.{u} =>
    ordinalAdd (∅ : TarskiSet.{u}) B = B
  have h0 : P (∅ : TarskiSet.{u}) :=
    th27 ORDINAL1.empty_isOrdinal
  have hs : ∀ B, ORDINAL1.isOrdinal B → P B → P (ORDINAL1.succ B) := by
    intro B hB ih
    exact (th28 ORDINAL1.empty_isOrdinal hB).trans
      (congrArg ORDINAL1.succ ih)
  have hl : ∀ B, ORDINAL1.isOrdinal B → B ≠ (∅ : TarskiSet.{u}) →
      ORDINAL1.isLimitOrdinal B → (∀ E, E ∈ B → P E) → P B := by
    intro B hB hne hlim ih
    obtain ⟨fi, hfi, hd, hv⟩ :=
      sch_OSLambda hB (fun E => ordinalAdd (∅ : TarskiSet.{u}) E)
        (fun E _ _ => ordinalAdd_isOrdinal (∅ : TarskiSet.{u}) E)
    have hrng : RELAT_1.rng fi = B := by
      apply eq_of_mem
      intro x
      constructor
      · intro hx
        obtain ⟨y, hy, heq⟩ := (FUNCT_1.def3 hfi.1.1.2).mp hx
        have hyB : y ∈ B := Eq.subst (motive := fun s => y ∈ s) hd hy
        have hyo := ORDINAL1.th13 hB hyB
        have hvy := hv y hyo hyB
        have hiy : ordinalAdd (∅ : TarskiSet.{u}) y = y := ih y hyB
        have hxy : x = y := heq.trans (hvy.trans hiy)
        exact Eq.subst (motive := fun s => s ∈ B) hxy.symm hyB
      · intro hx
        have hxo := ORDINAL1.th13 hB hx
        have hxd : x ∈ RELAT_1.dom fi :=
          Eq.subst (motive := fun s => x ∈ s) hd.symm hx
        have happ : FUNCT_1.apply fi x = x :=
          (hv x hxo hx).trans (ih x hx)
        exact (FUNCT_1.def3 hfi.1.1.2).mpr ⟨x, hxd, happ.symm⟩
    exact (th29 ORDINAL1.empty_isOrdinal hB hne hlim hfi hd hv).trans
      ((congrArg sup hrng).trans (th18 hB))
  exact sch_OrdinalInd P h0 hs hl A hA

/-- `ORDINAL2:Lm1`. -/
theorem lm1 : FUNCT_3.one = ORDINAL1.succ (∅ : TarskiSet.{u}) := by
  apply eq_of_mem
  intro x
  rw [ORDINAL1.th8, FUNCT_3.one]
  constructor
  · intro hx
    exact Or.inr ((singleton_iff (∅ : TarskiSet.{u}) x).mp hx)
  · intro hx
    rcases hx with hx | hx
    · exact ((XBOOLE_0.empty_iff x).mp hx).elim
    · exact (singleton_iff (∅ : TarskiSet.{u}) x).mpr hx

/-- `ORDINAL2:31` (unlabeled). -/
theorem th31 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ordinalAdd A FUNCT_3.one = ORDINAL1.succ A := by
  exact (congrArg (ordinalAdd A) lm1).trans
    ((th28 hA ORDINAL1.empty_isOrdinal).trans
      (congrArg ORDINAL1.succ (th27 hA)))

/-- `ORDINAL2:32` (`Th32`). -/
theorem th32 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hAB : A ∈ B) :
    ordinalAdd C A ∈ ordinalAdd C B := by
  let P := fun D : TarskiSet.{u} =>
    A ∈ D → ordinalAdd C A ∈ ordinalAdd C D
  have hind : ∀ D, ORDINAL1.isOrdinal D →
      (∀ E, E ∈ D → P E) → P D := by
    intro D hD ih hAD
    by_cases hsuc : ∃ E, ORDINAL1.isOrdinal E ∧ D = ORDINAL1.succ E
    · obtain ⟨E, hE, hDE⟩ := hsuc
      have hadd : ordinalAdd C D =
          ORDINAL1.succ (ordinalAdd C E) :=
        Eq.subst (motive := fun s => ordinalAdd C s =
          ORDINAL1.succ (ordinalAdd C E)) hDE.symm (th28 hC hE)
      rcases (ORDINAL1.th8 A E).mp
          (Eq.subst (motive := fun s => A ∈ s) hDE hAD) with hAE | heq
      · have hi := ih E
          (Eq.subst (motive := fun s => E ∈ s) hDE.symm (ORDINAL1.th6 E)) hAE
        have htop : ordinalAdd C E ∈ ORDINAL1.succ (ordinalAdd C E) :=
          ORDINAL1.th6 _
        exact Eq.subst (motive := fun s => ordinalAdd C A ∈ s)
          hadd.symm
          ((ORDINAL1.th17 (ordinalAdd_isOrdinal C E)).1
            (ordinalAdd C E) htop (ordinalAdd C A) hi)
      · exact Eq.subst (motive := fun s => ordinalAdd C A ∈ s)
          hadd.symm (by
            rw [heq]
            exact ORDINAL1.th6 _)
    · have hne : D ≠ (∅ : TarskiSet.{u}) := fun he =>
        (XBOOLE_0.empty_iff A).mp
          (Eq.subst (motive := fun s => A ∈ s) he hAD)
      have hlim : ORDINAL1.isLimitOrdinal D := by
        apply Classical.byContradiction
        intro hn
        exact hsuc ((ORDINAL1.th29 hD).mp hn)
      obtain ⟨fi, hfi, hd, hv⟩ :=
        sch_OSLambda hD (fun E => ordinalAdd C E)
          (fun E _ _ => ordinalAdd_isOrdinal C E)
      have hAd : A ∈ RELAT_1.dom fi :=
        Eq.subst (motive := fun s => A ∈ s) hd.symm hAD
      have hr : ordinalAdd C A ∈ RELAT_1.rng fi :=
        (FUNCT_1.def3 hfi.1.1.2).mpr
          ⟨A, hAd, (hv A hA hAD).symm⟩
      have hmem : ordinalAdd C A ∈ sup (RELAT_1.rng fi) :=
        th19 (ordinalAdd_isOrdinal C A) hr
      exact Eq.subst (motive := fun s => ordinalAdd C A ∈ s)
        ((th29 hC hD hne hlim hfi hd hv).trans rfl).symm hmem
  exact ORDINAL1.sch_TransfiniteInd P hind B hB hAB

/-- `ORDINAL2:33` (`Th33`). -/
theorem th33 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hAB : A ⊆ B) :
    ordinalAdd C A ⊆ ordinalAdd C B := by
  by_cases heq : A = B
  · rw [heq]
  · have hmem : A ∈ B :=
      ORDINAL1.th11 hA.1 hB ⟨hAB, heq⟩
    exact (ordinalAdd_isOrdinal C B).1 _ (th32 hA hB hC hmem)

/-- `ORDINAL2:34` (`Th34`). -/
theorem th34 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hAB : A ⊆ B) :
    ordinalAdd A C ⊆ ordinalAdd B C := by
  let P := fun D : TarskiSet.{u} =>
    ordinalAdd A D ⊆ ordinalAdd B D
  have h0 : P (∅ : TarskiSet.{u}) := by
    change ordinalAdd A (∅ : TarskiSet.{u}) ⊆
      ordinalAdd B (∅ : TarskiSet.{u})
    rw [th27 hA, th27 hB]
    exact hAB
  have hs : ∀ D, ORDINAL1.isOrdinal D → P D → P (ORDINAL1.succ D) := by
    intro D hD ih
    change ordinalAdd A (ORDINAL1.succ D) ⊆
      ordinalAdd B (ORDINAL1.succ D)
    change ordinalAdd A D ⊆ ordinalAdd B D at ih
    rw [th28 hA hD, th28 hB hD]
    exact (th1 (ordinalAdd_isOrdinal A D)
      (ordinalAdd_isOrdinal B D)).mp ih
  have hl : ∀ D, ORDINAL1.isOrdinal D → D ≠ (∅ : TarskiSet.{u}) →
      ORDINAL1.isLimitOrdinal D → (∀ E, E ∈ D → P E) → P D := by
    intro D hD hne hlim ih
    obtain ⟨fi, hfi, hd, hv⟩ :=
      sch_OSLambda hD (fun E => ordinalAdd A E)
        (fun E _ _ => ordinalAdd_isOrdinal A E)
    have hrng : ∀ x, x ∈ RELAT_1.rng fi → x ∈ ordinalAdd B D := by
      intro x hx
      obtain ⟨E, hEd, heq⟩ := (FUNCT_1.def3 hfi.1.1.2).mp hx
      have hED : E ∈ D := Eq.subst (motive := fun s => E ∈ s) hd hEd
      have hE := ORDINAL1.th13 hD hED
      have hvE := hv E hE hED
      have hleft : ordinalAdd A E ⊆ ordinalAdd B E := ih E hED
      have hright : ordinalAdd B E ∈ ordinalAdd B D :=
        th32 hE hD hB hED
      have hm : ordinalAdd A E ∈ ordinalAdd B D :=
        ORDINAL1.th12 (ordinalAdd_isOrdinal A E).1
          (ordinalAdd_isOrdinal B E) (ordinalAdd_isOrdinal B D)
          hleft hright
      exact Eq.subst (motive := fun s => s ∈ ordinalAdd B D)
        (hvE.symm.trans heq.symm) hm
    have hsup : sup (RELAT_1.rng fi) ⊆ ordinalAdd B D :=
      th20 (ordinalAdd_isOrdinal B D)
        (fun x hxord hx => hrng x hx)
    exact Eq.subst (motive := fun s => s ⊆ ordinalAdd B D)
      (th29 hA hD hne hlim hfi hd hv).symm hsup
  exact sch_OrdinalInd P h0 hs hl C hC

/-! ## Ordinal multiplication -/

private theorem mul_exists (A B : TarskiSet.{u})
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B) :
    ∃ x, ORDINAL1.isOrdinal x ∧
      OSRecWitness A x (∅ : TarskiSet.{u})
        (fun _ y => ordinalAdd y B)
        (fun _ L => TARSKI.union (sequenceSup L)) :=
  (sch_OSDef hA ORDINAL1.empty_isOrdinal
    (fun _ y => ordinalAdd y B)
    (fun _ L => TARSKI.union (sequenceSup L))
    (fun _ y _ _ => ordinalAdd_isOrdinal y B)
    (fun _ L _ _ => ORDINAL1.th18 (sequenceSup_isOrdinal L))).1

/-- `ORDINAL2:def 15` — ordinal multiplication `A *^ B`. -/
noncomputable def ordinalMul (A B : TarskiSet.{u}) : TarskiSet.{u} := by
  classical
  exact if h : ORDINAL1.isOrdinal A ∧ ORDINAL1.isOrdinal B
    then Classical.choose (mul_exists A B h.1 h.2)
    else (∅ : TarskiSet.{u})

theorem ordinalMul_isOrdinal (A B : TarskiSet.{u}) :
    ORDINAL1.isOrdinal (ordinalMul A B) := by
  classical
  unfold ordinalMul
  split
  · rename_i h
    exact (Classical.choose_spec (mul_exists A B h.1 h.2)).1
  · exact ORDINAL1.empty_isOrdinal

theorem def15 {A B : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B) :
    OSRecWitness A (ordinalMul A B) (∅ : TarskiSet.{u})
      (fun _ y => ordinalAdd y B)
      (fun _ L => TARSKI.union (sequenceSup L)) := by
  classical
  have hp := And.intro hA hB
  unfold ordinalMul
  rw [dif_pos hp]
  exact (Classical.choose_spec (mul_exists A B hp.1 hp.2)).2

/-- `ORDINAL2:35` (`Th35`). -/
theorem th35 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ordinalMul (∅ : TarskiSet.{u}) A = (∅ : TarskiSet.{u}) := by
  obtain ⟨fi, hfi, hx, hd, h0, _hs, _hl⟩ :=
    def15 ORDINAL1.empty_isOrdinal hA
  exact hx.trans ((th6 hfi.1 ORDINAL1.empty_isOrdinal hd).trans h0)

/-- `ORDINAL2:36` (`Th36`). -/
theorem th36 {A B : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B) :
    ordinalMul (ORDINAL1.succ B) A =
      ordinalAdd (ordinalMul B A) A := by
  obtain ⟨fi, hfi, hx, hd, h0, hs, hl⟩ :=
    def15 (ORDINAL1.th17 hB) hA
  have htop : ORDINAL1.succ B ∈ ORDINAL1.succ (ORDINAL1.succ B) :=
    ORDINAL1.th6 _
  have hBin : B ∈ RELAT_1.dom fi :=
    Eq.subst (motive := fun s => B ∈ s) hd.symm
      ((ORDINAL1.th17 (ORDINAL1.th17 hB)).1
        (ORDINAL1.succ B) htop B (ORDINAL1.th6 B))
  have hpref : OSRecWitness B (FUNCT_1.apply fi B)
      (∅ : TarskiSet.{u}) (fun _ y => ordinalAdd y A)
      (fun _ L => TARSKI.union (sequenceSup L)) :=
    prefix_OSRecWitness hfi hB hBin (fun _ => h0)
      (fun _ y => ordinalAdd y A)
      (fun _ L => TARSKI.union (sequenceSup L))
      (fun E hE hEin => hs E hE
        (Eq.subst (motive := fun s => ORDINAL1.succ E ∈ s) hd hEin))
      (fun E hE hEin hn hlm => hl E hE
        (Eq.subst (motive := fun s => E ∈ s) hd hEin) hn hlm)
  have hprev : FUNCT_1.apply fi B = ordinalMul B A :=
    (sch_OSDef hB ORDINAL1.empty_isOrdinal
      (fun _ y => ordinalAdd y A)
      (fun _ L => TARSKI.union (sequenceSup L))
      (fun _ y _ _ => ordinalAdd_isOrdinal y A)
      (fun _ L _ _ => ORDINAL1.th18 (sequenceSup_isOrdinal L))).2
      _ _ (apply_ordinal_sequence hfi hB) (ordinalMul_isOrdinal B A)
      hpref (def15 hB hA)
  exact hx.trans ((th6 hfi.1 (ORDINAL1.th17 hB) hd).trans
    ((hs B hB htop).trans (congrArg (fun y => ordinalAdd y A) hprev)))

/-- `ORDINAL2:37` (`Th37`). -/
theorem th37 {A B fi : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hne : B ≠ (∅ : TarskiSet.{u})) (hlim : ORDINAL1.isLimitOrdinal B)
    (hfi : isOrdinalSequence fi) (hdom : RELAT_1.dom fi = B)
    (hv : ∀ E, ORDINAL1.isOrdinal E → E ∈ B →
      FUNCT_1.apply fi E = ordinalMul E A) :
    ordinalMul B A = TARSKI.union (sequenceSup fi) := by
  obtain ⟨W, hW, hx, hdW, h0W, hsW, hlW⟩ := def15 hB hA
  have hBin := ORDINAL1.th6 B
  have hrestDom : RELAT_1.dom (RELAT_1.restrict W B) = B :=
    RELAT_1.th62 (R := W) (X := B)
      (Eq.subst (motive := fun s => B ⊆ s) hdW.symm
        ((ORDINAL1.th17 hB).1 B hBin))
  have hrestOS := restrict_ordinal_sequence hW hB
  have hEq : RELAT_1.restrict W B = fi := by
    apply FUNCT_1.th2 hrestOS.1.1 hfi.1.1
      (hrestDom.trans hdom.symm)
    intro E hEd
    have hEB : E ∈ B :=
      Eq.subst (motive := fun s => E ∈ s) hrestDom hEd
    have hE := ORDINAL1.th13 hB hEB
    have hEW : E ∈ RELAT_1.dom W :=
      Eq.subst (motive := fun s => E ∈ s) hdW.symm
        ((ORDINAL1.th17 hB).1 B hBin E hEB)
    have hpref := prefix_OSRecWitness hW hE hEW (fun _ => h0W)
      (fun _ y => ordinalAdd y A)
      (fun _ L => TARSKI.union (sequenceSup L))
      (fun C hC hCin => hsW C hC
        (Eq.subst (motive := fun s => ORDINAL1.succ C ∈ s) hdW hCin))
      (fun C hC hCin hn hlm => hlW C hC
        (Eq.subst (motive := fun s => C ∈ s) hdW hCin) hn hlm)
    have happ : FUNCT_1.apply W E = ordinalMul E A :=
      (sch_OSDef hE ORDINAL1.empty_isOrdinal
        (fun _ y => ordinalAdd y A)
        (fun _ L => TARSKI.union (sequenceSup L))
        (fun _ y _ _ => ordinalAdd_isOrdinal y A)
        (fun _ L _ _ => ORDINAL1.th18 (sequenceSup_isOrdinal L))).2
        _ _ (apply_ordinal_sequence hW hE) (ordinalMul_isOrdinal E A)
        hpref (def15 hE hA)
    exact (FUNCT_1.th47 hW.1.1.2 hEd).trans
      (happ.trans (hv E hE hEB).symm)
  exact hx.trans ((th6 hW.1 hB hdW).trans
    ((hlW B hB hBin hne hlim).trans
      (congrArg (fun L => TARSKI.union (sequenceSup L)) hEq)))

/-- `ORDINAL2:38` (`Th38`). -/
theorem th38 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ordinalMul A (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) := by
  let P := fun B : TarskiSet.{u} =>
    ordinalMul B (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u})
  have h0 : P (∅ : TarskiSet.{u}) :=
    th35 ORDINAL1.empty_isOrdinal
  have hs : ∀ B, ORDINAL1.isOrdinal B → P B → P (ORDINAL1.succ B) := by
    intro B hB ih
    change ordinalMul (ORDINAL1.succ B) (∅ : TarskiSet.{u}) =
      (∅ : TarskiSet.{u})
    rw [th36 ORDINAL1.empty_isOrdinal hB, th27 (ordinalMul_isOrdinal B _), ih]
  have hl : ∀ B, ORDINAL1.isOrdinal B → B ≠ (∅ : TarskiSet.{u}) →
      ORDINAL1.isLimitOrdinal B → (∀ E, E ∈ B → P E) → P B := by
    intro B hB hne hlim ih
    obtain ⟨fi, hfi, hd, hv⟩ :=
      sch_OSLambda hB (fun E => ordinalMul E (∅ : TarskiSet.{u}))
        (fun E _ _ => ordinalMul_isOrdinal E (∅ : TarskiSet.{u}))
    have hrng : RELAT_1.rng fi = ORDINAL1.succ (∅ : TarskiSet.{u}) := by
      apply eq_of_mem
      intro x
      constructor
      · intro hx
        obtain ⟨E, hEd, heq⟩ := (FUNCT_1.def3 hfi.1.1.2).mp hx
        have hEB : E ∈ B := Eq.subst (motive := fun s => E ∈ s) hd hEd
        have hE := ORDINAL1.th13 hB hEB
        have hz : FUNCT_1.apply fi E = (∅ : TarskiSet.{u}) :=
          (hv E hE hEB).trans (ih E hEB)
        rw [ORDINAL1.th8]
        exact Or.inr (heq.trans hz)
      · intro hx
        have hx0 : x = (∅ : TarskiSet.{u}) := by
          rcases (ORDINAL1.th8 x (∅ : TarskiSet.{u})).mp hx with he | he
          · exact ((XBOOLE_0.empty_iff x).mp he).elim
          · exact he
        obtain ⟨E, hEB⟩ := XBOOLE_0.th7 hne
        have hE := ORDINAL1.th13 hB hEB
        have hEd : E ∈ RELAT_1.dom fi :=
          Eq.subst (motive := fun s => E ∈ s) hd.symm hEB
        have hz : FUNCT_1.apply fi E = (∅ : TarskiSet.{u}) :=
          (hv E hE hEB).trans (ih E hEB)
        exact (FUNCT_1.def3 hfi.1.1.2).mpr
          ⟨E, hEd, hx0.trans hz.symm⟩
    have hsup : sequenceSup fi = ORDINAL1.succ (∅ : TarskiSet.{u}) :=
      (congrArg sup hrng).trans (th18
        (ORDINAL1.th17 ORDINAL1.empty_isOrdinal))
    exact (th37 ORDINAL1.empty_isOrdinal hB hne hlim hfi hd hv).trans
      ((congrArg TARSKI.union hsup).trans (th2 ORDINAL1.empty_isOrdinal))
  exact sch_OrdinalInd P h0 hs hl A hA

/-- `ORDINAL2:39` (`Th39`). -/
theorem th39 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ordinalMul FUNCT_3.one A = A ∧ ordinalMul A FUNCT_3.one = A := by
  have hOne : ORDINAL1.isOrdinal (FUNCT_3.one : TarskiSet.{u}) :=
    Eq.subst (motive := ORDINAL1.isOrdinal) lm1.symm
      (ORDINAL1.th17 ORDINAL1.empty_isOrdinal)
  have hleft : ordinalMul FUNCT_3.one A = A := by
    rw [lm1, th36 hA ORDINAL1.empty_isOrdinal,
      th35 hA, th30 hA]
  let P := fun B : TarskiSet.{u} => ordinalMul B FUNCT_3.one = B
  have h0 : P (∅ : TarskiSet.{u}) := th35 hOne
  have hs : ∀ B, ORDINAL1.isOrdinal B → P B → P (ORDINAL1.succ B) := by
    intro B hB ih
    change ordinalMul (ORDINAL1.succ B) FUNCT_3.one = ORDINAL1.succ B
    rw [th36 hOne hB, th31 (ordinalMul_isOrdinal B FUNCT_3.one), ih]
  have hl : ∀ B, ORDINAL1.isOrdinal B → B ≠ (∅ : TarskiSet.{u}) →
      ORDINAL1.isLimitOrdinal B → (∀ E, E ∈ B → P E) → P B := by
    intro B hB hne hlim ih
    obtain ⟨fi, hfi, hd, hv⟩ :=
      sch_OSLambda hB (fun E => ordinalMul E FUNCT_3.one)
        (fun E _ _ => ordinalMul_isOrdinal E FUNCT_3.one)
    have hrng : RELAT_1.rng fi = B := by
      apply eq_of_mem
      intro x
      constructor
      · intro hx
        obtain ⟨E, hEd, heq⟩ := (FUNCT_1.def3 hfi.1.1.2).mp hx
        have hEB : E ∈ B := Eq.subst (motive := fun s => E ∈ s) hd hEd
        have hE := ORDINAL1.th13 hB hEB
        have hxe : x = E := heq.trans ((hv E hE hEB).trans (ih E hEB))
        exact Eq.subst (motive := fun s => s ∈ B) hxe.symm hEB
      · intro hx
        have hxo := ORDINAL1.th13 hB hx
        have hxd : x ∈ RELAT_1.dom fi :=
          Eq.subst (motive := fun s => x ∈ s) hd.symm hx
        have happ : FUNCT_1.apply fi x = x :=
          (hv x hxo hx).trans (ih x hx)
        exact (FUNCT_1.def3 hfi.1.1.2).mpr ⟨x, hxd, happ.symm⟩
    exact (th37 hOne hB hne hlim hfi hd hv).trans
      ((congrArg TARSKI.union
        ((congrArg sup hrng).trans (th18 hB))).trans hlim.symm)
  exact ⟨hleft, sch_OrdinalInd P h0 hs hl A hA⟩

private theorem mul_step_mem {A C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hC : ORDINAL1.isOrdinal C)
    (hne : C ≠ (∅ : TarskiSet.{u})) :
    ordinalMul A C ∈ ordinalMul (ORDINAL1.succ A) C := by
  have h0C : (∅ : TarskiSet.{u}) ∈ C := by
    exact ORDINAL1.th11 ORDINAL1.empty_isOrdinal.1 hC
      ⟨XBOOLE_1.th2, hne.symm⟩
  have hadd : ordinalAdd (ordinalMul A C) (∅ : TarskiSet.{u}) ∈
      ordinalAdd (ordinalMul A C) C :=
    th32 ORDINAL1.empty_isOrdinal hC (ordinalMul_isOrdinal A C) h0C
  exact Eq.subst (motive := fun s => ordinalMul A C ∈ s)
    (th36 hC hA).symm
    (Eq.subst (motive := fun s => s ∈ ordinalAdd (ordinalMul A C) C)
      (th27 (ordinalMul_isOrdinal A C)) hadd)

/-- `ORDINAL2:40` (`Th40`). -/
theorem th40 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hne : C ≠ (∅ : TarskiSet.{u}))
    (hAB : A ∈ B) :
    ordinalMul A C ∈ ordinalMul B C := by
  let P := fun D : TarskiSet.{u} =>
    A ∈ D → ordinalMul A C ∈ ordinalMul D C
  have hind : ∀ D, ORDINAL1.isOrdinal D →
      (∀ E, E ∈ D → P E) → P D := by
    intro D hD ih hAD
    by_cases hsuc : ∃ E, ORDINAL1.isOrdinal E ∧ D = ORDINAL1.succ E
    · obtain ⟨E, hE, hDE⟩ := hsuc
      rcases (ORDINAL1.th8 A E).mp
          (Eq.subst (motive := fun s => A ∈ s) hDE hAD) with hAE | heq
      · have hi := ih E
          (Eq.subst (motive := fun s => E ∈ s) hDE.symm
            (ORDINAL1.th6 E)) hAE
        have hs := mul_step_mem hE hC hne
        have ht : ordinalMul A C ∈ ordinalMul (ORDINAL1.succ E) C :=
          (ordinalMul_isOrdinal (ORDINAL1.succ E) C).1
            (ordinalMul E C) hs (ordinalMul A C) hi
        exact Eq.subst (motive := fun s => ordinalMul A C ∈ ordinalMul s C)
          hDE.symm ht
      · exact Eq.subst (motive := fun s => ordinalMul A C ∈ ordinalMul s C)
          hDE.symm (by rw [heq]; exact mul_step_mem hE hC hne)
    · have hneD : D ≠ (∅ : TarskiSet.{u}) := fun he =>
        (XBOOLE_0.empty_iff A).mp
          (Eq.subst (motive := fun s => A ∈ s) he hAD)
      have hlim : ORDINAL1.isLimitOrdinal D := by
        apply Classical.byContradiction
        intro hn
        exact hsuc ((ORDINAL1.th29 hD).mp hn)
      have hsA : ORDINAL1.succ A ∈ D :=
        ((ORDINAL1.th28 hD).mp hlim) A hAD
      obtain ⟨fi, hfi, hd, hv⟩ :=
        sch_OSLambda hD (fun E => ordinalMul E C)
          (fun E _ _ => ordinalMul_isOrdinal E C)
      have hsAd : ORDINAL1.succ A ∈ RELAT_1.dom fi :=
        Eq.subst (motive := fun s => ORDINAL1.succ A ∈ s) hd.symm hsA
      have hyrng : ordinalMul (ORDINAL1.succ A) C ∈ RELAT_1.rng fi :=
        (FUNCT_1.def3 hfi.1.1.2).mpr
          ⟨ORDINAL1.succ A, hsAd,
            (hv (ORDINAL1.succ A) (ORDINAL1.th17 hA) hsA).symm⟩
      have hysup : ordinalMul (ORDINAL1.succ A) C ∈
          sup (RELAT_1.rng fi) :=
        th19 (ordinalMul_isOrdinal (ORDINAL1.succ A) C) hyrng
      have hsub : ordinalMul (ORDINAL1.succ A) C ⊆
          TARSKI.union (sup (RELAT_1.rng fi)) :=
        ZFMISC_1.th74 hysup
      have hm := hsub (ordinalMul A C) (mul_step_mem hA hC hne)
      exact Eq.subst (motive := fun s => ordinalMul A C ∈ s)
        (th37 hC hD hneD hlim hfi hd hv).symm hm
  exact ORDINAL1.sch_TransfiniteInd P hind B hB hAB

/-- `ORDINAL2:41` (unlabeled). -/
theorem th41 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hAB : A ⊆ B) :
    ordinalMul A C ⊆ ordinalMul B C := by
  by_cases hC0 : C = (∅ : TarskiSet.{u})
  · rw [hC0, th38 hA, th38 hB]
  · by_cases hEq : A = B
    · rw [hEq]
    · exact (ordinalMul_isOrdinal B C).1 _
        (th40 hA hB hC hC0
          (ORDINAL1.th11 hA.1 hB ⟨hAB, hEq⟩))

/-- `ORDINAL2:42` (unlabeled). -/
theorem th42 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hAB : A ⊆ B) :
    ordinalMul C A ⊆ ordinalMul C B := by
  by_cases hB0 : B = (∅ : TarskiSet.{u})
  · have hA0 : A = (∅ : TarskiSet.{u}) :=
      (XBOOLE_0.def10).mpr
        ⟨Eq.subst (motive := fun s => A ⊆ s) hB0 hAB, XBOOLE_1.th2⟩
    rw [hA0, hB0]
  · let P := fun D : TarskiSet.{u} =>
      ordinalMul D A ⊆ ordinalMul D B
    have h0 : P (∅ : TarskiSet.{u}) := by
      change ordinalMul (∅ : TarskiSet.{u}) A ⊆
        ordinalMul (∅ : TarskiSet.{u}) B
      rw [th35 hA, th35 hB]
    have hs : ∀ D, ORDINAL1.isOrdinal D → P D →
        P (ORDINAL1.succ D) := by
      intro D hD ih
      change ordinalMul (ORDINAL1.succ D) A ⊆
        ordinalMul (ORDINAL1.succ D) B
      change ordinalMul D A ⊆ ordinalMul D B at ih
      rw [th36 hA hD, th36 hB hD]
      exact XBOOLE_1.th1
        (th34 (ordinalMul_isOrdinal D A) (ordinalMul_isOrdinal D B) hA ih)
        (th33 hA hB (ordinalMul_isOrdinal D B) hAB)
    have hl : ∀ D, ORDINAL1.isOrdinal D → D ≠ (∅ : TarskiSet.{u}) →
        ORDINAL1.isLimitOrdinal D → (∀ E, E ∈ D → P E) → P D := by
      intro D hD hne hlim ih
      obtain ⟨fi, hfi, hd, hv⟩ :=
        sch_OSLambda hD (fun E => ordinalMul E A)
          (fun E _ _ => ordinalMul_isOrdinal E A)
      have hrng : ∀ x, x ∈ RELAT_1.rng fi → x ∈ ordinalMul D B := by
        intro x hx
        obtain ⟨E, hEd, heq⟩ := (FUNCT_1.def3 hfi.1.1.2).mp hx
        have hED : E ∈ D := Eq.subst (motive := fun s => E ∈ s) hd hEd
        have hE := ORDINAL1.th13 hD hED
        have hsub := ih E hED
        have hmem := th40 hE hD hB hB0 hED
        have hm : ordinalMul E A ∈ ordinalMul D B :=
          ORDINAL1.th12 (ordinalMul_isOrdinal E A).1
            (ordinalMul_isOrdinal E B) (ordinalMul_isOrdinal D B)
            hsub hmem
        exact Eq.subst (motive := fun s => s ∈ ordinalMul D B)
          ((hv E hE hED).symm.trans heq.symm) hm
      have hsup : sup (RELAT_1.rng fi) ⊆ ordinalMul D B :=
        th20 (ordinalMul_isOrdinal D B) (fun x _ hx => hrng x hx)
      have hun : TARSKI.union (sup (RELAT_1.rng fi)) ⊆ ordinalMul D B :=
        XBOOLE_1.th1 (th5 (sup_isOrdinal _)) hsup
      exact Eq.subst (motive := fun s => s ⊆ ordinalMul D B)
        (th37 hA hD hne hlim hfi hd hv).symm hun
    exact sch_OrdinalInd P h0 hs hl C hC

/-! ## Ordinal exponentiation -/

private theorem exp_exists (A B : TarskiSet.{u})
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B) :
    ∃ x, ORDINAL1.isOrdinal x ∧
      OSRecWitness B x FUNCT_3.one
        (fun _ y => ordinalMul A y)
        (fun _ L => lim L) :=
  (sch_OSDef hB
    (Eq.subst (motive := ORDINAL1.isOrdinal) lm1.symm
      (ORDINAL1.th17 ORDINAL1.empty_isOrdinal))
    (fun _ y => ordinalMul A y) (fun _ L => lim L)
    (fun _ y _ _ => ordinalMul_isOrdinal A y)
    (fun _ L _ _ => lim_isOrdinal L)).1

/-- `ORDINAL2:def 16` — `exp(A,B)`. -/
noncomputable def ordinalExp (A B : TarskiSet.{u}) : TarskiSet.{u} := by
  classical
  exact if h : ORDINAL1.isOrdinal A ∧ ORDINAL1.isOrdinal B
    then Classical.choose (exp_exists A B h.1 h.2)
    else (∅ : TarskiSet.{u})

theorem ordinalExp_isOrdinal (A B : TarskiSet.{u}) :
    ORDINAL1.isOrdinal (ordinalExp A B) := by
  classical
  unfold ordinalExp
  split
  · rename_i h
    exact (Classical.choose_spec (exp_exists A B h.1 h.2)).1
  · exact ORDINAL1.empty_isOrdinal

theorem def16 {A B : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B) :
    OSRecWitness B (ordinalExp A B) FUNCT_3.one
      (fun _ y => ordinalMul A y) (fun _ L => lim L) := by
  classical
  have hp := And.intro hA hB
  unfold ordinalExp
  rw [dif_pos hp]
  exact (Classical.choose_spec (exp_exists A B hp.1 hp.2)).2

/-- `ORDINAL2:43` (`Th43`). -/
theorem th43 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ordinalExp A (∅ : TarskiSet.{u}) = FUNCT_3.one := by
  obtain ⟨fi, hfi, hx, hd, h0, _hs, _hl⟩ :=
    def16 hA ORDINAL1.empty_isOrdinal
  exact hx.trans ((th6 hfi.1 ORDINAL1.empty_isOrdinal hd).trans h0)

/-- `ORDINAL2:44` (`Th44`). -/
theorem th44 {A B : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B) :
    ordinalExp A (ORDINAL1.succ B) =
      ordinalMul A (ordinalExp A B) := by
  obtain ⟨fi, hfi, hx, hd, h0, hs, hl⟩ :=
    def16 hA (ORDINAL1.th17 hB)
  have htop := ORDINAL1.th6 (ORDINAL1.succ B)
  have hBin : B ∈ RELAT_1.dom fi :=
    Eq.subst (motive := fun s => B ∈ s) hd.symm
      ((ORDINAL1.th17 (ORDINAL1.th17 hB)).1
        (ORDINAL1.succ B) htop B (ORDINAL1.th6 B))
  have hpref := prefix_OSRecWitness hfi hB hBin (fun _ => h0)
    (fun _ y => ordinalMul A y) (fun _ L => lim L)
    (fun E hE hEin => hs E hE
      (Eq.subst (motive := fun s => ORDINAL1.succ E ∈ s) hd hEin))
    (fun E hE hEin hn hlm => hl E hE
      (Eq.subst (motive := fun s => E ∈ s) hd hEin) hn hlm)
  have hprev : FUNCT_1.apply fi B = ordinalExp A B :=
    (sch_OSDef hB
      (Eq.subst (motive := ORDINAL1.isOrdinal) lm1.symm
        (ORDINAL1.th17 ORDINAL1.empty_isOrdinal))
      (fun _ y => ordinalMul A y) (fun _ L => lim L)
      (fun _ y _ _ => ordinalMul_isOrdinal A y)
      (fun _ L _ _ => lim_isOrdinal L)).2
      _ _ (apply_ordinal_sequence hfi hB) (ordinalExp_isOrdinal A B)
      hpref (def16 hA hB)
  exact hx.trans ((th6 hfi.1 (ORDINAL1.th17 hB) hd).trans
    ((hs B hB htop).trans (congrArg (ordinalMul A) hprev)))

/-- `ORDINAL2:45` (`Th45`). -/
theorem th45 {A B fi : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hne : B ≠ (∅ : TarskiSet.{u})) (hlim : ORDINAL1.isLimitOrdinal B)
    (hfi : isOrdinalSequence fi) (hdom : RELAT_1.dom fi = B)
    (hv : ∀ E, ORDINAL1.isOrdinal E → E ∈ B →
      FUNCT_1.apply fi E = ordinalExp A E) :
    ordinalExp A B = lim fi := by
  obtain ⟨W, hW, hx, hdW, h0W, hsW, hlW⟩ := def16 hA hB
  have hBin := ORDINAL1.th6 B
  have hrestDom : RELAT_1.dom (RELAT_1.restrict W B) = B :=
    RELAT_1.th62 (R := W) (X := B)
      (Eq.subst (motive := fun s => B ⊆ s) hdW.symm
        ((ORDINAL1.th17 hB).1 B hBin))
  have hrestOS := restrict_ordinal_sequence hW hB
  have hEq : RELAT_1.restrict W B = fi := by
    apply FUNCT_1.th2 hrestOS.1.1 hfi.1.1
      (hrestDom.trans hdom.symm)
    intro E hEd
    have hEB : E ∈ B :=
      Eq.subst (motive := fun s => E ∈ s) hrestDom hEd
    have hE := ORDINAL1.th13 hB hEB
    have hEW : E ∈ RELAT_1.dom W :=
      Eq.subst (motive := fun s => E ∈ s) hdW.symm
        ((ORDINAL1.th17 hB).1 B hBin E hEB)
    have hpref := prefix_OSRecWitness hW hE hEW (fun _ => h0W)
      (fun _ y => ordinalMul A y) (fun _ L => lim L)
      (fun C hC hCin => hsW C hC
        (Eq.subst (motive := fun s => ORDINAL1.succ C ∈ s) hdW hCin))
      (fun C hC hCin hn hlm => hlW C hC
        (Eq.subst (motive := fun s => C ∈ s) hdW hCin) hn hlm)
    have happ : FUNCT_1.apply W E = ordinalExp A E :=
      (sch_OSDef hE
        (Eq.subst (motive := ORDINAL1.isOrdinal) lm1.symm
          (ORDINAL1.th17 ORDINAL1.empty_isOrdinal))
        (fun _ y => ordinalMul A y) (fun _ L => lim L)
        (fun _ y _ _ => ordinalMul_isOrdinal A y)
        (fun _ L _ _ => lim_isOrdinal L)).2
        _ _ (apply_ordinal_sequence hW hE) (ordinalExp_isOrdinal A E)
        hpref (def16 hA hE)
    exact (FUNCT_1.th47 hW.1.1.2 hEd).trans
      (happ.trans (hv E hE hEB).symm)
  exact hx.trans ((th6 hW.1 hB hdW).trans
    ((hlW B hB hBin hne hlim).trans (congrArg lim hEq)))

/-- `ORDINAL2:46` (unlabeled). -/
theorem th46 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ordinalExp A FUNCT_3.one = A ∧
      ordinalExp FUNCT_3.one A = FUNCT_3.one := by
  have hOne : ORDINAL1.isOrdinal (FUNCT_3.one : TarskiSet.{u}) :=
    Eq.subst (motive := ORDINAL1.isOrdinal) lm1.symm
      (ORDINAL1.th17 ORDINAL1.empty_isOrdinal)
  have hfirst : ordinalExp A FUNCT_3.one = A := by
    rw [lm1, th44 hA ORDINAL1.empty_isOrdinal,
      th43 hA, (th39 hA).2]
  let P := fun B : TarskiSet.{u} =>
    ordinalExp FUNCT_3.one B = FUNCT_3.one
  have h0 : P (∅ : TarskiSet.{u}) := th43 hOne
  have hs : ∀ B, ORDINAL1.isOrdinal B → P B →
      P (ORDINAL1.succ B) := by
    intro B hB ih
    change ordinalExp FUNCT_3.one (ORDINAL1.succ B) = FUNCT_3.one
    rw [th44 hOne hB, ih, (th39 hOne).1]
  have hl : ∀ B, ORDINAL1.isOrdinal B → B ≠ (∅ : TarskiSet.{u}) →
      ORDINAL1.isLimitOrdinal B → (∀ E, E ∈ B → P E) → P B := by
    intro B hB hne hlim ih
    obtain ⟨fi, hfi, hd, hv⟩ :=
      sch_OSLambda hB (fun E => ordinalExp FUNCT_3.one E)
        (fun E _ _ => ordinalExp_isOrdinal FUNCT_3.one E)
    have honeLim : isLimesOf FUNCT_3.one fi := by
      refine ⟨fun he => (FUNCT_3.one_ne_empty he).elim, ?_⟩
      intro _ X Y hX hY hXone honeY
      have hXsucc : X ∈ ORDINAL1.succ (∅ : TarskiSet.{u}) :=
        Eq.subst (motive := fun s => X ∈ s) lm1 hXone
      have hX0 : X = (∅ : TarskiSet.{u}) := by
        rcases (ORDINAL1.th8 X (∅ : TarskiSet.{u})).mp hXsucc with he | he
        · exact ((XBOOLE_0.empty_iff X).mp he).elim
        · exact he
      obtain ⟨D, hDB⟩ := XBOOLE_0.th7 hne
      have hD := ORDINAL1.th13 hB hDB
      refine ⟨D, hD, Eq.subst (motive := fun s => D ∈ s) hd.symm hDB, ?_⟩
      intro E hE _ hEd
      have hEB : E ∈ B := Eq.subst (motive := fun s => E ∈ s) hd hEd
      have happ : FUNCT_1.apply fi E = FUNCT_3.one :=
        (hv E hE hEB).trans (ih E hEB)
      refine ⟨?_, Eq.subst (motive := fun s => s ∈ Y) happ.symm honeY⟩
      exact Eq.subst (motive := fun s => s ∈ FUNCT_1.apply fi E)
        hX0.symm (Eq.subst (motive := fun s =>
          (∅ : TarskiSet.{u}) ∈ s) happ.symm
          (Eq.subst (motive := fun s =>
            (∅ : TarskiSet.{u}) ∈ s) lm1.symm (ORDINAL1.th6 _)))
    have hlimEq : lim fi = FUNCT_3.one :=
      ((def10 hfi ⟨FUNCT_3.one, hOne, honeLim⟩).2
        FUNCT_3.one hOne honeLim).symm
    exact (th45 hOne hB hne hlim hfi hd hv).trans hlimEq
  exact ⟨hfirst, sch_OrdinalInd P h0 hs hl A hA⟩

/-- Registration after `Th13`: a limit ordinal exists. -/
theorem exists_limitOrdinal :
    ∃ A : TarskiSet.{u}, ORDINAL1.isOrdinal A ∧
      ORDINAL1.isLimitOrdinal A :=
  ⟨(∅ : TarskiSet.{u}), ORDINAL1.empty_isOrdinal, th4⟩

/-- Registration after `Def15`: every element of an ordinal is ordinal. -/
theorem element_isOrdinal {O x : TarskiSet.{u}}
    (hO : ORDINAL1.isOrdinal O) (hx : x ∈ O) :
    ORDINAL1.isOrdinal x :=
  ORDINAL1.th13 hO hx

/-- `ORDINAL2:47` (unlabeled): every ordinal is a limit plus a natural. -/
theorem th47 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ∃ B C, ORDINAL1.isOrdinal B ∧ ORDINAL1.isOrdinal C ∧
      ORDINAL1.isLimitOrdinal B ∧ ORDINAL1.isNatural C ∧
      A = ordinalAdd B C := by
  let P := fun D : TarskiSet.{u} =>
    ∃ B C, ORDINAL1.isOrdinal B ∧ ORDINAL1.isOrdinal C ∧
      ORDINAL1.isLimitOrdinal B ∧ ORDINAL1.isNatural C ∧
      D = ordinalAdd B C
  have hind : ∀ D, ORDINAL1.isOrdinal D →
      (∀ E, E ∈ D → P E) → P D := by
    intro D hD ih
    by_cases hs : ∃ E, ORDINAL1.isOrdinal E ∧ D = ORDINAL1.succ E
    · obtain ⟨E, hE, hDE⟩ := hs
      obtain ⟨B, C, hB, hC, hBl, hCn, heq⟩ :=
        ih E (Eq.subst (motive := fun s => E ∈ s) hDE.symm
          (ORDINAL1.th6 E))
      refine ⟨B, ORDINAL1.succ C, hB, ORDINAL1.th17 hC, hBl,
        ORDINAL1.succ_isNatural hCn, ?_⟩
      exact hDE.trans ((congrArg ORDINAL1.succ heq).trans
        (th28 hB hC).symm)
    · have hlim : ORDINAL1.isLimitOrdinal D := by
        apply Classical.byContradiction
        intro hn
        exact hs ((ORDINAL1.th29 hD).mp hn)
      exact ⟨D, (∅ : TarskiSet.{u}), hD, ORDINAL1.empty_isOrdinal,
        hlim, ORDINAL1.empty_isNatural, (th27 hD).symm⟩
  exact ORDINAL1.sch_TransfiniteInd P hind A hA

/-- Registration: `X --> o` is ordinal-yielding. -/
theorem mapsTo_ordinal_yielding (X o : TarskiSet.{u})
    (ho : ORDINAL1.isOrdinal o) :
    isOrdinalYielding (FUNCOP_1.mapsTo X o) :=
  ⟨ORDINAL1.succ o, ORDINAL1.th17 ho,
    XBOOLE_1.th1 (FUNCOP_1.th13 X o).2
      (fun x hx => (ORDINAL1.th8 x o).mpr
        (Or.inr ((singleton_iff o x).mp hx)))⟩

/-- Registration: `O --> x` is T-sequence-like. -/
theorem mapsTo_isTSequence (O x : TarskiSet.{u})
    (hO : ORDINAL1.isOrdinal O) :
    ORDINAL1.isTSequence (FUNCOP_1.mapsTo O x) :=
  ⟨FUNCOP_1.mapsTo_isFunction O x,
    Eq.subst (motive := ORDINAL1.isOrdinal)
      (FUNCOP_1.mapsTo_dom O x).symm hO⟩

/-- `ORDINAL2:def 17` — cofinality. -/
def isCofinalWith (A B : TarskiSet.{u}) : Prop :=
  ∃ xi, isOrdinalSequence xi ∧ RELAT_1.dom xi = B ∧
    RELAT_1.rng xi ⊆ A ∧ isIncreasing xi ∧ A = sequenceSup xi

theorem def17 (A B : TarskiSet.{u}) :
    isCofinalWith A B ↔
      ∃ xi, isOrdinalSequence xi ∧ RELAT_1.dom xi = B ∧
        RELAT_1.rng xi ⊆ A ∧ isIncreasing xi ∧ A = sequenceSup xi :=
  Iff.rfl

theorem isCofinalWith_refl {A : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) : isCofinalWith A A := by
  let xi := RELAT_1.id A
  have hTS : ORDINAL1.isTSequence xi :=
    ⟨FUNCT_1.id_isFunction A,
      Eq.subst (motive := ORDINAL1.isOrdinal)
        (RELAT_1.id_dom A).symm hA⟩
  have hOS : isOrdinalSequence xi :=
    ⟨hTS, ⟨A, hA, Eq.subst (motive := fun s => s ⊆ A)
      (RELAT_1.id_rng A).symm (subset_refl A)⟩⟩
  refine ⟨xi, hOS, RELAT_1.id_dom A, ?_, ?_, ?_⟩
  · exact Eq.subst (motive := fun s => s ⊆ A)
      (RELAT_1.id_rng A).symm (subset_refl A)
  · intro B C hB hC hBC hCd
    have hBA : B ∈ A :=
      hA.1 C (Eq.subst (motive := fun s => C ∈ s)
        (RELAT_1.id_dom A) hCd) B hBC
    rw [FUNCT_1.th18 hBA,
      FUNCT_1.th18 (Eq.subst (motive := fun s => C ∈ s)
        (RELAT_1.id_dom A) hCd)]
    exact hBC
  · exact (th18 hA).symm.trans
      (congrArg sup (RELAT_1.id_rng A).symm)

/-- `ORDINAL2:48` (`Th48`). -/
theorem th48 {psi e : TarskiSet.{u}} (hpsi : isOrdinalSequence psi)
    (he : e ∈ RELAT_1.rng psi) : ORDINAL1.isOrdinal e := by
  obtain ⟨u, hu, heq⟩ := (FUNCT_1.def3 hpsi.1.1.2).mp he
  exact Eq.subst (motive := ORDINAL1.isOrdinal) heq.symm (th25 hpsi hu)

/-- `ORDINAL2:49` (unlabeled). -/
theorem th49 {psi : TarskiSet.{u}} (hpsi : isOrdinalSequence psi) :
    RELAT_1.rng psi ⊆ sequenceSup psi := by
  intro e he
  exact th19 (th48 hpsi he) he

/-- `ORDINAL2:50` (unlabeled). -/
theorem th50 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (h : isCofinalWith A (∅ : TarskiSet.{u})) :
    A = (∅ : TarskiSet.{u}) := by
  obtain ⟨psi, hpsi, hd, _hr, _hi, hsup⟩ := h
  have hrng : RELAT_1.rng psi = (∅ : TarskiSet.{u}) :=
    (RELAT_1.th42 hpsi.1.1.1).mp hd
  exact hsup.trans ((congrArg sup hrng).trans
    (th18 ORDINAL1.empty_isOrdinal))

/-! ## Natural-number registrations and recursion schemes -/

/-- `ORDINAL2:sch 17` (`OmegaInd`). -/
theorem sch_OmegaInd {a : TarskiSet.{u}} (ha : ORDINAL1.isNatural a)
    (P : TarskiSet.{u} → Prop)
    (h0 : P (∅ : TarskiSet.{u}))
    (hs : ∀ n, ORDINAL1.isNatural n → P n → P (ORDINAL1.succ n)) :
    P a := by
  let Q := fun A : TarskiSet.{u} => ORDINAL1.isNatural A → P A
  have q0 : Q (∅ : TarskiSet.{u}) := fun _ => h0
  have qs : ∀ A, ORDINAL1.isOrdinal A → Q A → Q (ORDINAL1.succ A) := by
    intro A _ ih hsn
    have hn : ORDINAL1.isNatural A :=
      ORDINAL1.def11.1.1 (ORDINAL1.succ A) hsn A (ORDINAL1.th6 A)
    exact hs A hn (ih hn)
  have ql : ∀ A, ORDINAL1.isOrdinal A → A ≠ (∅ : TarskiSet.{u}) →
      ORDINAL1.isLimitOrdinal A → (∀ B, B ∈ A → Q B) → Q A := by
    intro A hA hne hlim _ hnat
    have h0A : (∅ : TarskiSet.{u}) ∈ A :=
      ORDINAL1.th11 ORDINAL1.empty_isOrdinal.1 hA
        ⟨XBOOLE_1.th2, hne.symm⟩
    have hwA : ORDINAL1.omega ⊆ A :=
      ORDINAL1.def11.2.2.2 A hA h0A hlim
    exact (ORDINAL1.th5 hnat hwA).elim
  exact sch_OrdinalInd Q q0 qs ql a (ORDINAL1.natural_isOrdinal ha) ha

/-- Registration: ordinal addition preserves naturals. -/
theorem add_natural {a b : TarskiSet.{u}}
    (ha : ORDINAL1.isNatural a) (hb : ORDINAL1.isNatural b) :
    ORDINAL1.isNatural (ordinalAdd a b) := by
  let P := fun n : TarskiSet.{u} => ORDINAL1.isNatural (ordinalAdd a n)
  have h0 : P (∅ : TarskiSet.{u}) := by
    change ORDINAL1.isNatural (ordinalAdd a (∅ : TarskiSet.{u}))
    rw [th27 (ORDINAL1.natural_isOrdinal ha)]
    exact ha
  have hs : ∀ n, ORDINAL1.isNatural n → P n →
      P (ORDINAL1.succ n) := by
    intro n hn ih
    change ORDINAL1.isNatural (ordinalAdd a (ORDINAL1.succ n))
    rw [th28 (ORDINAL1.natural_isOrdinal ha)
      (ORDINAL1.natural_isOrdinal hn)]
    exact ORDINAL1.succ_isNatural ih
  exact sch_OmegaInd hb P h0 hs

/-- Registration: `IFEQ(x,y,a,b)` is natural for natural branches. -/
theorem IFEQ_natural {x y a b : TarskiSet.{u}}
    (ha : ORDINAL1.isNatural a) (hb : ORDINAL1.isNatural b) :
    ORDINAL1.isNatural (FUNCOP_1.IFEQ x y a b) := by
  by_cases h : x = y
  · exact Eq.subst (motive := ORDINAL1.isNatural)
      ((FUNCOP_1.def8 x y a b).1 h).symm ha
  · exact Eq.subst (motive := ORDINAL1.isNatural)
      ((FUNCOP_1.def8 x y a b).2 h).symm hb

/-- `ORDINAL2:sch 18` (`LambdaRecEx`). -/
theorem sch_LambdaRecEx (A : TarskiSet.{u})
    (G : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u}) :
    ∃ f, FUNCT_1.isFunction f ∧ RELAT_1.dom f = ORDINAL1.omega ∧
      FUNCT_1.apply f (∅ : TarskiSet.{u}) = A ∧
      ∀ n, ORDINAL1.isNatural n →
        FUNCT_1.apply f (ORDINAL1.succ n) =
          G n (FUNCT_1.apply f n) := by
  obtain ⟨L, hL, hd, h0, hs, _hl⟩ :=
    sch_TSExist1 (A := ORDINAL1.omega) (B0 := A)
      ORDINAL1.def11.1 G (fun _ _ => (∅ : TarskiSet.{u}))
  refine ⟨L, hL.1, hd, h0 ORDINAL1.def11.2.1, ?_⟩
  intro n hn
  exact hs n (ORDINAL1.natural_isOrdinal hn)
    (ORDINAL1.succ_isNatural hn)

/-- `ORDINAL2:sch 19` (`RecUn`). -/
theorem sch_RecUn {A F G : TarskiSet.{u}}
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hF : FUNCT_1.isFunction F) (hdF : RELAT_1.dom F = ORDINAL1.omega)
    (hF0 : FUNCT_1.apply F (∅ : TarskiSet.{u}) = A)
    (hFs : ∀ n, ORDINAL1.isNatural n →
      P n (FUNCT_1.apply F n) (FUNCT_1.apply F (ORDINAL1.succ n)))
    (hG : FUNCT_1.isFunction G) (hdG : RELAT_1.dom G = ORDINAL1.omega)
    (hG0 : FUNCT_1.apply G (∅ : TarskiSet.{u}) = A)
    (hGs : ∀ n, ORDINAL1.isNatural n →
      P n (FUNCT_1.apply G n) (FUNCT_1.apply G (ORDINAL1.succ n)))
    (huniq : ∀ n x y1 y2, ORDINAL1.isNatural n →
      P n x y1 → P n x y2 → y1 = y2) :
    F = G := by
  have hv : ∀ n, ORDINAL1.isNatural n →
      FUNCT_1.apply F n = FUNCT_1.apply G n := by
    intro n hn
    let Q := fun k : TarskiSet.{u} =>
      FUNCT_1.apply F k = FUNCT_1.apply G k
    have q0 : Q (∅ : TarskiSet.{u}) := hF0.trans hG0.symm
    have qs : ∀ k, ORDINAL1.isNatural k → Q k →
        Q (ORDINAL1.succ k) := by
      intro k hk ih
      exact huniq k (FUNCT_1.apply F k)
        (FUNCT_1.apply F (ORDINAL1.succ k))
        (FUNCT_1.apply G (ORDINAL1.succ k)) hk
        (hFs k hk)
        (Eq.subst (motive := fun s =>
          P k s (FUNCT_1.apply G (ORDINAL1.succ k))) ih.symm (hGs k hk))
    exact sch_OmegaInd hn Q q0 qs
  apply FUNCT_1.th2 hF hG (hdF.trans hdG.symm)
  intro x hx
  have hxw : x ∈ ORDINAL1.omega :=
    Eq.subst (motive := fun s => x ∈ s) hdF hx
  exact hv x hxw

/-- `ORDINAL2:sch 20` (`LambdaRecUn`). -/
theorem sch_LambdaRecUn {A F G : TarskiSet.{u}}
    (H : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hF : FUNCT_1.isFunction F) (hdF : RELAT_1.dom F = ORDINAL1.omega)
    (hF0 : FUNCT_1.apply F (∅ : TarskiSet.{u}) = A)
    (hFs : ∀ n, ORDINAL1.isNatural n →
      FUNCT_1.apply F (ORDINAL1.succ n) = H n (FUNCT_1.apply F n))
    (hG : FUNCT_1.isFunction G) (hdG : RELAT_1.dom G = ORDINAL1.omega)
    (hG0 : FUNCT_1.apply G (∅ : TarskiSet.{u}) = A)
    (hGs : ∀ n, ORDINAL1.isNatural n →
      FUNCT_1.apply G (ORDINAL1.succ n) = H n (FUNCT_1.apply G n)) :
    F = G :=
  sch_RecUn (fun n x y => y = H n x)
    hF hdF hF0 (fun n hn => hFs n hn)
    hG hdG hG0 (fun n hn => hGs n hn)
    (fun _ _ y1 y2 _ h1 h2 => h1.trans h2.symm)

end ORDINAL2
