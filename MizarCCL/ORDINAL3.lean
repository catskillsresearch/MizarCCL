import MizarCCL.ORDINAL2

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/ordinal3.miz`.
Authors: Grzegorz Bancerek (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Ordinal Arithmetics

Faithful 1–1 Lean rendering of Mizar article `ORDINAL3`.
All 75 absolute theorem slots, definitions 1–7, `Lm1`, the two
commutativity redefinitions, and all four registration claims are represented.
The article has no schemes and no canceled items.

Mizar's ordinal and natural modes are predicates on the common `TarskiSet`
carrier, so their typing assumptions are explicit hypotheses.
-/

universe u

open TarskiSet TARSKI XBOOLE_0

namespace ORDINAL3

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

private theorem subset_refl (X : TarskiSet.{u}) : X ⊆ X :=
  fun _ hx => hx

private theorem ordinal_eq {A B : TarskiSet.{u}} (hAB : A ⊆ B)
    (hBA : B ⊆ A) : A = B :=
  XBOOLE_0.def10.mpr ⟨hAB, hBA⟩

private theorem mem_of_mem_of_subset {x A B : TarskiSet.{u}}
    (hx : x ∈ A) (hAB : A ⊆ B) : x ∈ B :=
  hAB x hx

local infixl:65 " +ᵒ " => ORDINAL2.ordinalAdd
local infixl:70 " *ᵒ " => ORDINAL2.ordinalMul

/-! ## Early set and ordinal facts -/

/-- `ORDINAL3:1` (unlabeled). -/
theorem th1 (X : TarskiSet.{u}) : X ⊆ ORDINAL1.succ X :=
  XBOOLE_1.th7

/-- `ORDINAL3:2` (unlabeled). -/
theorem th2 {X Y : TarskiSet.{u}} (h : ORDINAL1.succ X ⊆ Y) : X ⊆ Y :=
  XBOOLE_1.th1 (th1 X) h

/-- `ORDINAL3:3` (unlabeled). -/
theorem th3 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) :
    A ∈ B ↔ ORDINAL1.succ A ∈ ORDINAL1.succ B := by
  constructor
  · intro hAB
    exact (ORDINAL1.th22 (ORDINAL1.th17 hA) hB).mpr
      ((ORDINAL1.th21 hA hB).mp hAB)
  · intro hs
    have hsub := (ORDINAL1.th22 (ORDINAL1.th17 hA) hB).mp hs
    exact (ORDINAL1.th21 hA hB).mpr hsub

/-- `ORDINAL3:4` (unlabeled). -/
theorem th4 {X A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hXA : X ⊆ A) : ORDINAL1.isOrdinal (TARSKI.union X) :=
  ORDINAL1.th23 (fun x hx => ORDINAL1.th13 hA (hXA x hx))

/-- `ORDINAL3:5` (`Th5`). -/
theorem th5 (X : TarskiSet.{u}) :
    ORDINAL1.isOrdinal (TARSKI.union (ORDINAL1.On X)) :=
  ORDINAL1.th23 (fun x hx => (ORDINAL1.def9 X x).mp hx |>.2)

/-- `ORDINAL3:6` (`Th6`). -/
theorem th6 {X A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hXA : X ⊆ A) : ORDINAL1.On X = X := by
  apply eq_of_mem
  intro x
  constructor
  · exact fun hx => ((ORDINAL1.def9 X x).mp hx).1
  · intro hx
    exact (ORDINAL1.def9 X x).mpr ⟨hx, ORDINAL1.th13 hA (hXA x hx)⟩

/-- `ORDINAL3:7` (`Th7`). -/
theorem th7 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ORDINAL1.On (TARSKI.singleton A) = TARSKI.singleton A :=
  th6 (ORDINAL1.th17 hA)
    (fun x hx => (ORDINAL1.th8 x A).mpr
      (Or.inr ((singleton_iff A x).mp hx)))

/-- `ORDINAL3:8` (`Th8`). -/
theorem th8 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hne : A ≠ (∅ : TarskiSet.{u})) : (∅ : TarskiSet.{u}) ∈ A :=
  ORDINAL1.th11 ORDINAL1.empty_isOrdinal.1 hA
    ⟨XBOOLE_1.th2, hne.symm⟩

/-- `ORDINAL3:9` (unlabeled). -/
theorem th9 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ORDINAL2.inf A = (∅ : TarskiSet.{u}) := by
  rw [ORDINAL2.def2, ORDINAL2.th8 hA]
  by_cases hne : A = (∅ : TarskiSet.{u})
  · rw [hne, SETFAM_1.def1_empty]
  · exact SETFAM_1.th4 (th8 hA hne)

/-- `ORDINAL3:10` (unlabeled). -/
theorem th10 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ORDINAL2.inf (TARSKI.singleton A) = A := by
  rw [ORDINAL2.def2, th7 hA, SETFAM_1.th10]

/-- `ORDINAL3:11` (unlabeled). -/
theorem th11 {X A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hXA : X ⊆ A) : ORDINAL1.isOrdinal (SETFAM_1.meet X) := by
  have hOn := th6 hA hXA
  exact Eq.subst (motive := fun s => ORDINAL1.isOrdinal (SETFAM_1.meet s))
    hOn (ORDINAL2.inf_isOrdinal X)

/-- First registration: union of two ordinals is ordinal. -/
theorem union_isOrdinal {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) : ORDINAL1.isOrdinal (A ∪ B) := by
  rcases ORDINAL1.th15 hA hB with h | h
  · rw [XBOOLE_1.th12 h]; exact hB
  · rw [union_comm, XBOOLE_1.th12 h]; exact hA

/-- Second registration: intersection of two ordinals is ordinal. -/
theorem inter_isOrdinal {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) : ORDINAL1.isOrdinal (A ∩ B) := by
  rcases ORDINAL1.th15 hA hB with h | h
  · have heq : A ∩ B = A := XBOOLE_1.th28 h
    rw [heq]; exact hA
  · have heq : A ∩ B = B := by
      rw [inter_comm]
      exact XBOOLE_1.th28 h
    rw [heq]; exact hB

/-- `ORDINAL3:12` (unlabeled). -/
theorem th12 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) : A ∪ B = A ∨ A ∪ B = B := by
  rcases ORDINAL1.th15 hA hB with h | h
  · exact Or.inr (XBOOLE_1.th12 h)
  · exact Or.inl (by rw [union_comm, XBOOLE_1.th12 h])

/-- `ORDINAL3:13` (unlabeled). -/
theorem th13 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) : A ∩ B = A ∨ A ∩ B = B := by
  rcases ORDINAL1.th15 hA hB with h | h
  · exact Or.inl (XBOOLE_1.th28 h)
  · exact Or.inr (by rw [inter_comm]; exact XBOOLE_1.th28 h)

/-- `ORDINAL3:Lm1`. -/
theorem lm1 : (FUNCT_3.one : TarskiSet.{u}) =
    ORDINAL1.succ (∅ : TarskiSet.{u}) :=
  ORDINAL2.lm1

private theorem one_isOrdinal :
    ORDINAL1.isOrdinal (FUNCT_3.one : TarskiSet.{u}) :=
  Eq.subst (motive := ORDINAL1.isOrdinal) lm1.symm
    (ORDINAL1.th17 ORDINAL1.empty_isOrdinal)

/-- `ORDINAL3:14` (`Th14`). -/
theorem th14 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (h : A ∈ (FUNCT_3.one : TarskiSet.{u})) :
    A = (∅ : TarskiSet.{u}) := by
  have hs : A ∈ ORDINAL1.succ (∅ : TarskiSet.{u}) :=
    Eq.subst (motive := fun s => A ∈ s) lm1 h
  rcases (ORDINAL1.th8 A (∅ : TarskiSet.{u})).mp hs with he | he
  · exact XBOOLE_1.th3 (ORDINAL1.empty_isOrdinal.1 A he)
  · exact he

/-- `ORDINAL3:15` (unlabeled). -/
theorem th15 : (FUNCT_3.one : TarskiSet.{u}) =
    TARSKI.singleton (∅ : TarskiSet.{u}) := by
  rw [lm1, ORDINAL1.succ_def, XBOOLE_1.th12 XBOOLE_1.th2]

/-- `ORDINAL3:16` (`Th16`). -/
theorem th16 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (h : A ⊆ (FUNCT_3.one : TarskiSet.{u})) :
    A = (∅ : TarskiSet.{u}) ∨ A = FUNCT_3.one := by
  by_cases he : A = (∅ : TarskiSet.{u})
  · exact Or.inl he
  · right
    apply ordinal_eq h
    intro x hx
    have hx0 : x = (∅ : TarskiSet.{u}) := th14 (ORDINAL1.th13 one_isOrdinal hx) hx
    rw [hx0]
    exact th8 hA he

/-! ## Monotonicity and cancellation -/

/-- `ORDINAL3:17` (unlabeled). -/
theorem th17 {A B C D : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hD : ORDINAL1.isOrdinal D)
    (hAB : A ⊆ B ∨ A ∈ B) (hCD : C ∈ D) :
    A +ᵒ C ∈ B +ᵒ D := by
  have hAB' : A ⊆ B := hAB.elim id (fun h => hB.1 A h)
  exact ORDINAL1.th12 (ORDINAL2.ordinalAdd_isOrdinal A C).1
    (ORDINAL2.ordinalAdd_isOrdinal B C)
    (ORDINAL2.ordinalAdd_isOrdinal B D)
    (ORDINAL2.th34 hA hB hC hAB')
    (ORDINAL2.th32 hC hD hB hCD)

/-- `ORDINAL3:18` (unlabeled). -/
theorem th18 {A B C D : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hD : ORDINAL1.isOrdinal D)
    (hAB : A ⊆ B) (hCD : C ⊆ D) :
    A +ᵒ C ⊆ B +ᵒ D :=
  XBOOLE_1.th1 (ORDINAL2.th34 hA hB hC hAB)
    (ORDINAL2.th33 hC hD hB hCD)

/-- `ORDINAL3:19` (`Th19`). -/
theorem th19 {A B C D : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hD : ORDINAL1.isOrdinal D)
    (hAB : A ∈ B) (hCD : C ⊆ D ∧ D ≠ (∅ : TarskiSet.{u}) ∨ C ∈ D) :
    A *ᵒ C ∈ B *ᵒ D := by
  have hsub : C ⊆ D := hCD.elim And.left (fun h => hD.1 C h)
  have hne : D ≠ (∅ : TarskiSet.{u}) := hCD.elim And.right
    (fun h he => (XBOOLE_0.empty_iff C).mp (Eq.subst (motive := fun s => C ∈ s) he h))
  exact ORDINAL1.th12 (ORDINAL2.ordinalMul_isOrdinal A C).1
    (ORDINAL2.ordinalMul_isOrdinal A D)
    (ORDINAL2.ordinalMul_isOrdinal B D)
    (ORDINAL2.th42 hC hD hA hsub)
    (ORDINAL2.th40 hA hB hD hne hAB)

/-- `ORDINAL3:20` (unlabeled). -/
theorem th20 {A B C D : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hD : ORDINAL1.isOrdinal D)
    (hAB : A ⊆ B) (hCD : C ⊆ D) :
    A *ᵒ C ⊆ B *ᵒ D :=
  XBOOLE_1.th1 (ORDINAL2.th41 hA hB hC hAB)
    (ORDINAL2.th42 hC hD hB hCD)

/-- `ORDINAL3:21` (`Th21`). -/
theorem th21 {B C D : TarskiSet.{u}}
    (hB : ORDINAL1.isOrdinal B) (hC : ORDINAL1.isOrdinal C)
    (hD : ORDINAL1.isOrdinal D) (h : B +ᵒ C = B +ᵒ D) : C = D := by
  rcases ORDINAL1.th14 hC hD with hCD | heq | hDC
  · exact (ORDINAL1.not_mem_self (B +ᵒ C)
      (Eq.subst (motive := fun s => B +ᵒ C ∈ s) h.symm
        (ORDINAL2.th32 hC hD hB hCD))).elim
  · exact heq
  · exact (ORDINAL1.not_mem_self (B +ᵒ D)
      (Eq.subst (motive := fun s => B +ᵒ D ∈ s) h
        (ORDINAL2.th32 hD hC hB hDC))).elim

/-- `ORDINAL3:22` (`Th22`). -/
theorem th22 {B C D : TarskiSet.{u}}
    (hB : ORDINAL1.isOrdinal B) (hC : ORDINAL1.isOrdinal C)
    (hD : ORDINAL1.isOrdinal D) (h : B +ᵒ C ∈ B +ᵒ D) : C ∈ D := by
  rcases ORDINAL1.th16 hC hD with hCD | hDC
  · by_cases heq : C = D
    · rw [heq] at h; exact (ORDINAL1.not_mem_self _ h).elim
    · exact ORDINAL1.th11 hC.1 hD ⟨hCD, heq⟩
  · have hs := ORDINAL2.th33 hD hC hB (hC.1 D hDC)
    exact (ORDINAL1.th5 h hs).elim

/-- `ORDINAL3:23` (`Th23`). -/
theorem th23 {B C D : TarskiSet.{u}}
    (hB : ORDINAL1.isOrdinal B) (hC : ORDINAL1.isOrdinal C)
    (hD : ORDINAL1.isOrdinal D) (h : B +ᵒ C ⊆ B +ᵒ D) : C ⊆ D := by
  rcases ORDINAL1.th16 hC hD with hCD | hDC
  · exact hCD
  · exact (ORDINAL1.th5
      (ORDINAL2.th32 hD hC hB hDC) h).elim

/-- `ORDINAL3:24` (`Th24`). -/
theorem th24 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) :
    A ⊆ A +ᵒ B ∧ B ⊆ A +ᵒ B := by
  constructor
  · have h := ORDINAL2.th33 ORDINAL1.empty_isOrdinal hB hA XBOOLE_1.th2
    rw [ORDINAL2.th27 hA] at h
    exact h
  · have h := ORDINAL2.th34 ORDINAL1.empty_isOrdinal hA hB XBOOLE_1.th2
    rw [ORDINAL2.th30 hB] at h
    exact h

/-- `ORDINAL3:25` (unlabeled). -/
theorem th25 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (h : A ∈ B) :
    A ∈ B +ᵒ C ∧ A ∈ C +ᵒ B :=
  ⟨(th24 hB hC).1 A h, (th24 hC hB).2 A h⟩

/-- `ORDINAL3:26` (`Th26`). -/
theorem th26 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (h : A +ᵒ B = (∅ : TarskiSet.{u})) :
    A = (∅ : TarskiSet.{u}) ∧ B = (∅ : TarskiSet.{u}) :=
  ⟨XBOOLE_1.th3 (Eq.subst (motive := fun s => A ⊆ s) h (th24 hA hB).1),
    XBOOLE_1.th3 (Eq.subst (motive := fun s => B ⊆ s) h (th24 hA hB).2)⟩

/-! ## Right subtraction existence and addition -/

/-- `ORDINAL3:27` (`Th27`). -/
theorem th27 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (hAB : A ⊆ B) :
    ∃ C, ORDINAL1.isOrdinal C ∧ B = A +ᵒ C := by
  let P := fun C : TarskiSet.{u} => B ⊆ A +ᵒ C
  have hex : ∃ C, ORDINAL1.isOrdinal C ∧ P C :=
    ⟨B, hB, (th24 hA hB).2⟩
  obtain ⟨C, hC, hBC, hleast⟩ := ORDINAL1.sch_OrdinalMin P hex
  have hCB : A +ᵒ C ⊆ B := by
    by_cases hC0 : C = (∅ : TarskiSet.{u})
    · rw [hC0, ORDINAL2.th27 hA]
      exact hAB
    · by_cases hlim : ORDINAL1.isLimitOrdinal C
      · obtain ⟨fi, hfi, hd, hv⟩ :=
          ORDINAL2.sch_OSLambda hC (fun D => A +ᵒ D)
            (fun D _ _ => ORDINAL2.ordinalAdd_isOrdinal A D)
        have heq := ORDINAL2.th29 hA hC hC0 hlim hfi hd hv
        rw [heq]
        apply ORDINAL2.th20 hB
        intro x hxord hx
        obtain ⟨E, hEd, hxE⟩ := (FUNCT_1.def3 hfi.1.1.2).mp hx
        have hEC : E ∈ C := Eq.subst (motive := fun s => E ∈ s) hd hEd
        have hE := ORDINAL1.th13 hC hEC
        have hvE := hv E hE hEC
        have hn : ¬ B ⊆ A +ᵒ E := fun hs =>
          ORDINAL1.th5 hEC (hleast E hE hs)
        have hmem : A +ᵒ E ∈ B := by
          rcases ORDINAL1.th14 (ORDINAL2.ordinalAdd_isOrdinal A E) hB with hm | he | hm
          · exact hm
          · exact (hn (he ▸ subset_refl B)).elim
          · exact (hn ((ORDINAL2.ordinalAdd_isOrdinal A E).1 B hm)).elim
        exact Eq.subst (motive := fun s => s ∈ B) (hxE.trans hvE).symm hmem
      · obtain ⟨D, hD, hCD⟩ := (ORDINAL1.th29 hC).mp hlim
        have hDinC : D ∈ C :=
          Eq.subst (motive := fun s => D ∈ s) hCD.symm (ORDINAL1.th6 D)
        have hn : ¬ B ⊆ A +ᵒ D := fun hs =>
          ORDINAL1.th5 hDinC (hleast D hD hs)
        have hmem : A +ᵒ D ∈ B := by
          rcases ORDINAL1.th14 (ORDINAL2.ordinalAdd_isOrdinal A D) hB with hm | he | hm
          · exact hm
          · exact (hn (he ▸ subset_refl B)).elim
          · exact (hn ((ORDINAL2.ordinalAdd_isOrdinal A D).1 B hm)).elim
        have hs : ORDINAL1.succ (A +ᵒ D) ⊆ B :=
          (ORDINAL1.th21 (ORDINAL2.ordinalAdd_isOrdinal A D) hB).mp hmem
        rw [hCD, ORDINAL2.th28 hA hD]
        exact hs
  exact ⟨C, hC, ordinal_eq hBC hCB⟩

/-- `ORDINAL3:28` (`Th28`). -/
theorem th28 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (hAB : A ∈ B) :
    ∃ C, ORDINAL1.isOrdinal C ∧ B = A +ᵒ C ∧ C ≠ (∅ : TarskiSet.{u}) := by
  obtain ⟨C, hC, heq⟩ := th27 hA hB (hB.1 A hAB)
  refine ⟨C, hC, heq, ?_⟩
  intro h0
  rw [h0, ORDINAL2.th27 hA] at heq
  exact ORDINAL1.not_mem_self A (heq ▸ hAB)

private theorem add_mem_cases {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (h : A ∈ B +ᵒ C) :
    A ∈ B ∨ ∃ D, ORDINAL1.isOrdinal D ∧ D ∈ C ∧ A = B +ᵒ D := by
  by_cases hAB : A ∈ B
  · exact Or.inl hAB
  · have hBA : B ⊆ A := by
      rcases ORDINAL1.th14 hB hA with h | h | h
      · exact hA.1 B h
      · exact h ▸ subset_refl A
      · exact (hAB h).elim
    obtain ⟨D, hD, heq⟩ := th27 hB hA hBA
    have hDC : D ∈ C := by
      rcases ORDINAL1.th14 hD hC with hDC | heqDC | hCD
      · exact hDC
      · have h' : A ∈ B +ᵒ D := by rw [heqDC]; exact h
        exact (ORDINAL1.not_mem_self A (heq ▸ h')).elim
      · have hs := ORDINAL2.th33 hC hD hB (hD.1 C hCD)
        exact (ORDINAL1.th5 h
          (Eq.subst (motive := fun s => B +ᵒ C ⊆ s) heq.symm hs)).elim
    exact Or.inr ⟨D, hD, hDC, heq⟩

/-- `ORDINAL3:29` (`Th29`). -/
theorem th29 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (hne : A ≠ (∅ : TarskiSet.{u}))
    (hlim : ORDINAL1.isLimitOrdinal A) :
    ORDINAL1.isLimitOrdinal (B +ᵒ A) := by
  apply (ORDINAL1.th28 (ORDINAL2.ordinalAdd_isOrdinal B A)).mpr
  intro C hC
  have hCOrd := ORDINAL1.th13 (ORDINAL2.ordinalAdd_isOrdinal B A) hC
  rcases add_mem_cases hCOrd hB hA hC with hCB | ⟨D, hD, hDA, heq⟩
  · have hsCB : ORDINAL1.succ C ⊆ B :=
      (ORDINAL1.th21 hCOrd hB).mp hCB
    have hBmem : B ∈ B +ᵒ A :=
      Eq.subst (motive := fun s => s ∈ B +ᵒ A) (ORDINAL2.th27 hB)
        (ORDINAL2.th32 ORDINAL1.empty_isOrdinal hA hB (th8 hA hne))
    exact ORDINAL1.th12 (ORDINAL1.th17 hCOrd).1 hB
      (ORDINAL2.ordinalAdd_isOrdinal B A) hsCB hBmem
  · have hsD := ((ORDINAL1.th28 hA).mp hlim) D hDA
    have hm := ORDINAL2.th32 (ORDINAL1.th17 hD) hA hB hsD
    rw [ORDINAL2.th28 hB hD] at hm
    exact Eq.subst (motive := fun s => ORDINAL1.succ s ∈ B +ᵒ A) heq.symm hm

private theorem add_sequence_sup {C fi psi : TarskiSet.{u}}
    (hC : ORDINAL1.isOrdinal C)
    (hfi : ORDINAL2.isOrdinalSequence fi)
    (hpsi : ORDINAL2.isOrdinalSequence psi)
    (hne : (∅ : TarskiSet.{u}) ≠ RELAT_1.dom fi)
    (hdom : RELAT_1.dom fi = RELAT_1.dom psi)
    (hv : ∀ A, A ∈ RELAT_1.dom fi →
      FUNCT_1.apply psi A = C +ᵒ FUNCT_1.apply fi A) :
    ORDINAL2.sequenceSup psi = C +ᵒ ORDINAL2.sequenceSup fi := by
  rw [ORDINAL2.def5, ORDINAL2.def5]
  apply ordinal_eq
  · apply ORDINAL2.th20 (ORDINAL2.ordinalAdd_isOrdinal C (ORDINAL2.sup _))
    intro x hxord hx
    obtain ⟨a, had, hxa⟩ := (FUNCT_1.def3 hpsi.1.1.2).mp hx
    have haf : a ∈ RELAT_1.dom fi :=
      Eq.subst (motive := fun s => a ∈ s) hdom.symm had
    have hval := hv a haf
    have hfrng : FUNCT_1.apply fi a ∈ RELAT_1.rng fi :=
      (FUNCT_1.def3 hfi.1.1.2).mpr ⟨a, haf, rfl⟩
    have hfsup : FUNCT_1.apply fi a ∈ ORDINAL2.sup (RELAT_1.rng fi) :=
      ORDINAL2.th19 (ORDINAL2.th25 hfi haf) hfrng
    have hadd : C +ᵒ FUNCT_1.apply fi a ∈
        C +ᵒ ORDINAL2.sup (RELAT_1.rng fi) :=
      ORDINAL2.th32 (ORDINAL2.th25 hfi haf) (ORDINAL2.sup_isOrdinal _) hC hfsup
    exact Eq.subst (motive := fun s => s ∈ C +ᵒ ORDINAL2.sup (RELAT_1.rng fi))
      (hxa.trans hval).symm hadd
  · intro x hx
    have hxord := ORDINAL1.th13
      (ORDINAL2.ordinalAdd_isOrdinal C (ORDINAL2.sup _)) hx
    rcases add_mem_cases hxord hC (ORDINAL2.sup_isOrdinal _) hx with hxC | ⟨B, hB, hBsup, heq⟩
    · obtain ⟨a, had⟩ := XBOOLE_0.th7 (fun hd0 => hne hd0.symm)
      have hpdom : a ∈ RELAT_1.dom psi :=
        Eq.subst (motive := fun s => a ∈ s) hdom had
      have hpval := hv a had
      have hprng : FUNCT_1.apply psi a ∈ RELAT_1.rng psi :=
        (FUNCT_1.def3 hpsi.1.1.2).mpr ⟨a, hpdom, rfl⟩
      have hpsup := ORDINAL2.th19 (ORDINAL2.th25 hpsi hpdom) hprng
      have hCsub := (th24 hC (ORDINAL2.th25 hfi had)).1
      exact (ORDINAL2.sup_isOrdinal _).1 (FUNCT_1.apply psi a) hpsup x
        (Eq.subst (motive := fun s => x ∈ s) hpval.symm (hCsub x hxC))
    · obtain ⟨D, hDord, hDrng, hBD⟩ := ORDINAL2.th21 hB hBsup
      obtain ⟨a, had, hDa⟩ := (FUNCT_1.def3 hfi.1.1.2).mp hDrng
      have hpdom : a ∈ RELAT_1.dom psi :=
        Eq.subst (motive := fun s => a ∈ s) hdom had
      have hpval := hv a had
      have hprng : FUNCT_1.apply psi a ∈ RELAT_1.rng psi :=
        (FUNCT_1.def3 hpsi.1.1.2).mpr ⟨a, hpdom, rfl⟩
      have hpsup := ORDINAL2.th19 (ORDINAL2.th25 hpsi hpdom) hprng
      have hsub : C +ᵒ B ⊆ C +ᵒ FUNCT_1.apply fi a :=
        ORDINAL2.th33 hB (ORDINAL2.th25 hfi had) hC
          (Eq.subst (motive := fun s => B ⊆ s) hDa hBD)
      have hxsub : x ⊆ FUNCT_1.apply psi a :=
        Eq.subst (motive := fun s => s ⊆ FUNCT_1.apply psi a) heq.symm
          (Eq.subst (motive := fun s => C +ᵒ B ⊆ s) hpval.symm hsub)
      exact ORDINAL1.th12 hxord.1 (ORDINAL2.th25 hpsi hpdom)
        (ORDINAL2.sup_isOrdinal _) hxsub hpsup

/-- `ORDINAL3:30` (`Th30`): associativity of ordinal addition. -/
theorem th30 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) :
    (A +ᵒ B) +ᵒ C = A +ᵒ (B +ᵒ C) := by
  let P := fun D : TarskiSet.{u} => (A +ᵒ B) +ᵒ D = A +ᵒ (B +ᵒ D)
  have h0 : P (∅ : TarskiSet.{u}) := by
    simp only [P]
    rw [ORDINAL2.th27 (ORDINAL2.ordinalAdd_isOrdinal A B),
      ORDINAL2.th27 hB]
  have hs : ∀ D, ORDINAL1.isOrdinal D → P D → P (ORDINAL1.succ D) := by
    intro D hD ih
    simp only [P] at ih ⊢
    rw [ORDINAL2.th28 (ORDINAL2.ordinalAdd_isOrdinal A B) hD,
      ORDINAL2.th28 hB hD,
      ORDINAL2.th28 hA (ORDINAL2.ordinalAdd_isOrdinal B D), ih]
  have hl : ∀ D, ORDINAL1.isOrdinal D → D ≠ (∅ : TarskiSet.{u}) →
      ORDINAL1.isLimitOrdinal D → (∀ E, E ∈ D → P E) → P D := by
    intro D hD hne hlim ih
    obtain ⟨fi, hfi, hd, hv⟩ :=
      ORDINAL2.sch_OSLambda hD (fun E => B +ᵒ E)
        (fun E _ _ => ORDINAL2.ordinalAdd_isOrdinal B E)
    obtain ⟨psi, hpsi, hdp, hvp⟩ :=
      ORDINAL2.sch_OSLambda hD (fun E => (A +ᵒ B) +ᵒ E)
        (fun E _ _ => ORDINAL2.ordinalAdd_isOrdinal (A +ᵒ B) E)
    have hBlim := ORDINAL2.th29 hB hD hne hlim hfi hd hv
    have hABlim := ORDINAL2.th29 (ORDINAL2.ordinalAdd_isOrdinal A B)
      hD hne hlim hpsi hdp hvp
    obtain ⟨chi, hchi, hdc, hvc⟩ :=
      ORDINAL2.sch_OSLambda hD (fun E => A +ᵒ (B +ᵒ E))
        (fun E _ _ => ORDINAL2.ordinalAdd_isOrdinal A (B +ᵒ E))
    have heq : psi = chi := by
      apply FUNCT_1.th2 hpsi.1.1 hchi.1.1 (hdp.trans hdc.symm)
      intro E hEd
      have hED : E ∈ D := Eq.subst (motive := fun s => E ∈ s) hdp hEd
      have hE := ORDINAL1.th13 hD hED
      exact (hvp E hE hED).trans ((ih E hED).trans (hvc E hE hED).symm)
    calc
      (A +ᵒ B) +ᵒ D = ORDINAL2.sequenceSup psi := hABlim
      _ = ORDINAL2.sequenceSup chi := congrArg ORDINAL2.sequenceSup heq
      _ = A +ᵒ ORDINAL2.sequenceSup fi := by
        have hdom : (∅ : TarskiSet.{u}) ≠ RELAT_1.dom fi := hd ▸ hne.symm
        exact (add_sequence_sup hA hfi hchi hdom (hd.trans hdc.symm)
          (fun E hEd => (hvc E (ORDINAL1.th13 hD
            (Eq.subst (motive := fun s => E ∈ s) hd hEd))
            (Eq.subst (motive := fun s => E ∈ s) hd hEd)).trans
              (congrArg (ORDINAL2.ordinalAdd A)
                (hv E (ORDINAL1.th13 hD
                  (Eq.subst (motive := fun s => E ∈ s) hd hEd))
                  (Eq.subst (motive := fun s => E ∈ s) hd hEd)).symm)))
      _ = A +ᵒ (B +ᵒ D) := congrArg (ORDINAL2.ordinalAdd A) hBlim.symm
  exact ORDINAL2.sch_OrdinalInd P h0 hs hl C hC

/-! ## Elementary multiplication facts -/

/-- `ORDINAL3:31` (unlabeled). -/
theorem th31 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (h : A *ᵒ B = (∅ : TarskiSet.{u})) :
    A = (∅ : TarskiSet.{u}) ∨ B = (∅ : TarskiSet.{u}) := by
  by_cases hA0 : A = (∅ : TarskiSet.{u})
  · exact Or.inl hA0
  · right
    apply Classical.byContradiction
    intro hB0
    have h0A := th8 hA hA0
    have hm := ORDINAL2.th40 ORDINAL1.empty_isOrdinal hA hB hB0 h0A
    rw [ORDINAL2.th35 hB, h] at hm
    exact ORDINAL1.not_mem_self (∅ : TarskiSet.{u}) hm

/-- `ORDINAL3:32` (unlabeled). -/
theorem th32 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hAB : A ∈ B) (hne : C ≠ (∅ : TarskiSet.{u})) :
    A ∈ B *ᵒ C ∧ A ∈ C *ᵒ B := by
  have h0C := th8 hC hne
  have hOneC : FUNCT_3.one ⊆ C := by
    rw [lm1]
    exact (ORDINAL1.th21 ORDINAL1.empty_isOrdinal hC).mp h0C
  have h1 := ORDINAL2.th42 one_isOrdinal hC hB hOneC
  have h2 := ORDINAL2.th41 one_isOrdinal hC hB hOneC
  rw [(ORDINAL2.th39 hB).2] at h1
  rw [(ORDINAL2.th39 hB).1] at h2
  exact ⟨h1 A hAB, h2 A hAB⟩

/-- `ORDINAL3:33` (`Th33`). -/
theorem th33 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hne : A ≠ (∅ : TarskiSet.{u}))
    (h : B *ᵒ A = C *ᵒ A) : B = C := by
  rcases ORDINAL1.th14 hB hC with hBC | heq | hCB
  · have hm := ORDINAL2.th40 hB hC hA hne hBC
    exact (ORDINAL1.not_mem_self (B *ᵒ A) (h ▸ hm)).elim
  · exact heq
  · have hm := ORDINAL2.th40 hC hB hA hne hCB
    exact (ORDINAL1.not_mem_self (C *ᵒ A) (h ▸ hm)).elim

/-- `ORDINAL3:34` (`Th34`). -/
theorem th34 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (h : B *ᵒ A ∈ C *ᵒ A) : B ∈ C := by
  rcases ORDINAL1.th16 hB hC with hBC | hCB
  · by_cases he : B = C
    · rw [he] at h; exact (ORDINAL1.not_mem_self _ h).elim
    · exact ORDINAL1.th11 hB.1 hC ⟨hBC, he⟩
  · exact (ORDINAL1.th5 h (ORDINAL2.th41 hC hB hA (hB.1 C hCB))).elim

/-- `ORDINAL3:35` (`Th35`). -/
theorem th35 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hne : A ≠ (∅ : TarskiSet.{u}))
    (h : B *ᵒ A ⊆ C *ᵒ A) : B ⊆ C := by
  rcases ORDINAL1.th16 hB hC with hBC | hCB
  · exact hBC
  · exact (ORDINAL1.th5 (ORDINAL2.th40 hC hB hA hne hCB) h).elim

/-- `ORDINAL3:36` (`Th36`). -/
theorem th36 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (hne : B ≠ (∅ : TarskiSet.{u})) :
    A ⊆ A *ᵒ B ∧ A ⊆ B *ᵒ A := by
  have h0B := th8 hB hne
  have hOneB : FUNCT_3.one ⊆ B := by
    rw [lm1]
    exact (ORDINAL1.th21 ORDINAL1.empty_isOrdinal hB).mp h0B
  have h1 := ORDINAL2.th42 one_isOrdinal hB hA hOneB
  have h2 := ORDINAL2.th41 one_isOrdinal hB hA hOneB
  rw [(ORDINAL2.th39 hA).2] at h1
  rw [(ORDINAL2.th39 hA).1] at h2
  exact ⟨h1, h2⟩

/-- `ORDINAL3:37` (unlabeled). -/
theorem th37 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (h : A *ᵒ B = FUNCT_3.one) :
    A = FUNCT_3.one ∧ B = FUNCT_3.one := by
  have hB0 : B ≠ (∅ : TarskiSet.{u}) := by
    intro hb
    rw [hb, ORDINAL2.th38 hA] at h
    exact FUNCT_3.one_ne_empty h.symm
  have hA0 : A ≠ (∅ : TarskiSet.{u}) := by
    intro ha
    rw [ha, ORDINAL2.th35 hB] at h
    exact FUNCT_3.one_ne_empty h.symm
  have hAsub : A ⊆ FUNCT_3.one := Eq.subst
    (motive := fun s => A ⊆ s) h (th36 hA hB hB0).1
  have hBsub : B ⊆ FUNCT_3.one := Eq.subst
    (motive := fun s => B ⊆ s) h (th36 hB hA hA0).2
  rcases th16 hA hAsub with ha | ha
  · exact (hA0 ha).elim
  · rcases th16 hB hBsub with hb | hb
    · exact (hB0 hb).elim
    · exact ⟨ha, hb⟩

/-- `ORDINAL3:38` (`Th38`). -/
theorem th38 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (h : A ∈ B +ᵒ C) :
    A ∈ B ∨ ∃ D, ORDINAL1.isOrdinal D ∧ D ∈ C ∧ A = B +ᵒ D :=
  add_mem_cases hA hB hC h

/-! ## Pointwise ordinal-sequence operations (`ORDINAL3:def 1`–`def 4`) -/

private noncomputable def seqMap
    (F : TarskiSet.{u} → TarskiSet.{u}) (fi : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (FUNCT_1.sch_Lambda (RELAT_1.dom fi) F)

private theorem seqMap_spec
    (F : TarskiSet.{u} → TarskiSet.{u}) (fi : TarskiSet.{u}) :
    FUNCT_1.isFunction (seqMap F fi) ∧
      RELAT_1.dom (seqMap F fi) = RELAT_1.dom fi ∧
      ∀ A, A ∈ RELAT_1.dom fi → FUNCT_1.apply (seqMap F fi) A = F A :=
  Classical.choose_spec (FUNCT_1.sch_Lambda (RELAT_1.dom fi) F)

noncomputable def addLeftSequence (C fi : TarskiSet.{u}) : TarskiSet.{u} :=
  seqMap (fun A => C +ᵒ FUNCT_1.apply fi A) fi

noncomputable def addRightSequence (fi C : TarskiSet.{u}) : TarskiSet.{u} :=
  seqMap (fun A => FUNCT_1.apply fi A +ᵒ C) fi

noncomputable def mulLeftSequence (C fi : TarskiSet.{u}) : TarskiSet.{u} :=
  seqMap (fun A => C *ᵒ FUNCT_1.apply fi A) fi

noncomputable def mulRightSequence (fi C : TarskiSet.{u}) : TarskiSet.{u} :=
  seqMap (fun A => FUNCT_1.apply fi A *ᵒ C) fi

theorem def1 (C fi : TarskiSet.{u}) :
    RELAT_1.dom (addLeftSequence C fi) = RELAT_1.dom fi ∧
      ∀ A, A ∈ RELAT_1.dom fi →
        FUNCT_1.apply (addLeftSequence C fi) A = C +ᵒ FUNCT_1.apply fi A :=
  (seqMap_spec (fun A => C +ᵒ FUNCT_1.apply fi A) fi).2

theorem def2 (fi C : TarskiSet.{u}) :
    RELAT_1.dom (addRightSequence fi C) = RELAT_1.dom fi ∧
      ∀ A, A ∈ RELAT_1.dom fi →
        FUNCT_1.apply (addRightSequence fi C) A = FUNCT_1.apply fi A +ᵒ C :=
  (seqMap_spec (fun A => FUNCT_1.apply fi A +ᵒ C) fi).2

theorem def3 (C fi : TarskiSet.{u}) :
    RELAT_1.dom (mulLeftSequence C fi) = RELAT_1.dom fi ∧
      ∀ A, A ∈ RELAT_1.dom fi →
        FUNCT_1.apply (mulLeftSequence C fi) A = C *ᵒ FUNCT_1.apply fi A :=
  (seqMap_spec (fun A => C *ᵒ FUNCT_1.apply fi A) fi).2

theorem def4 (fi C : TarskiSet.{u}) :
    RELAT_1.dom (mulRightSequence fi C) = RELAT_1.dom fi ∧
      ∀ A, A ∈ RELAT_1.dom fi →
        FUNCT_1.apply (mulRightSequence fi C) A = FUNCT_1.apply fi A *ᵒ C :=
  (seqMap_spec (fun A => FUNCT_1.apply fi A *ᵒ C) fi).2

private theorem seqMap_isOrdinalSequence
    {F : TarskiSet.{u} → TarskiSet.{u}} {fi : TarskiSet.{u}}
    (hfi : ORDINAL2.isOrdinalSequence fi)
    (hF : ∀ A, A ∈ RELAT_1.dom fi → ORDINAL1.isOrdinal (F A)) :
    ORDINAL2.isOrdinalSequence (seqMap F fi) := by
  have hs := seqMap_spec F fi
  refine ⟨⟨hs.1, Eq.subst (motive := ORDINAL1.isOrdinal)
    hs.2.1.symm hfi.1.2⟩, ?_⟩
  refine ⟨ORDINAL2.sup (RELAT_1.rng (seqMap F fi)),
    ORDINAL2.sup_isOrdinal _, ?_⟩
  intro x hx
  obtain ⟨a, had, hxa⟩ := (FUNCT_1.def3 hs.1.2).mp hx
  have haf : a ∈ RELAT_1.dom fi :=
    Eq.subst (motive := fun s => a ∈ s) hs.2.1 had
  have hxord : ORDINAL1.isOrdinal x :=
    Eq.subst (motive := ORDINAL1.isOrdinal)
      (hxa.trans (hs.2.2 a haf)).symm (hF a haf)
  exact (ORDINAL2.def3 _).1 x
    ((ORDINAL1.def9 _ x).mpr ⟨hx, hxord⟩)

/-- `ORDINAL3:39` (`Th39`). -/
theorem th39 {C fi psi : TarskiSet.{u}}
    (hC : ORDINAL1.isOrdinal C)
    (hfi : ORDINAL2.isOrdinalSequence fi)
    (hpsi : ORDINAL2.isOrdinalSequence psi)
    (hne : (∅ : TarskiSet.{u}) ≠ RELAT_1.dom fi)
    (hdom : RELAT_1.dom fi = RELAT_1.dom psi)
    (hv : ∀ A, A ∈ RELAT_1.dom fi →
      FUNCT_1.apply psi A = C +ᵒ FUNCT_1.apply fi A) :
    ORDINAL2.sequenceSup psi = C +ᵒ ORDINAL2.sequenceSup fi :=
  add_sequence_sup hC hfi hpsi hne hdom hv

/-! ## Limits and distributivity -/

private theorem mul_limit_member {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hlim : ORDINAL1.isLimitOrdinal B)
    (h : A ∈ B *ᵒ C) :
    ∃ D, ORDINAL1.isOrdinal D ∧ D ∈ B ∧ A ∈ D *ᵒ C := by
  have hB0 : B ≠ (∅ : TarskiSet.{u}) := by
    intro hb
    rw [hb, ORDINAL2.th35 hC] at h
    exact ((XBOOLE_0.empty_iff A).mp h).elim
  obtain ⟨fi, hfi, hd, hv⟩ :=
    ORDINAL2.sch_OSLambda hB (fun D => D *ᵒ C)
      (fun D _ _ => ORDINAL2.ordinalMul_isOrdinal D C)
  have heq := ORDINAL2.th37 hC hB hB0 hlim hfi hd hv
  obtain ⟨X, hAX, hX⟩ := (TARSKI.def4 (ORDINAL2.sequenceSup fi) A).mp
    (Eq.subst (motive := fun s => A ∈ s) heq h)
  have hXord := ORDINAL1.th13 (ORDINAL2.sequenceSup_isOrdinal fi) hX
  obtain ⟨D, hDord, hDrng, hXD⟩ := ORDINAL2.th21 hXord hX
  obtain ⟨d, hdd, hDd⟩ := (FUNCT_1.def3 hfi.1.1.2).mp hDrng
  have hdB : d ∈ B := Eq.subst (motive := fun s => d ∈ s) hd hdd
  have hordd := ORDINAL1.th13 hB hdB
  let E := ORDINAL1.succ d
  have hEB : E ∈ B := ((ORDINAL1.th28 hB).mp hlim) d hdB
  refine ⟨E, ORDINAL1.th17 hordd, hEB, ?_⟩
  have hC0 : C ≠ (∅ : TarskiSet.{u}) := by
    intro hc
    rw [hc, ORDINAL2.th38 hB] at h
    exact ((XBOOLE_0.empty_iff A).mp h).elim
  have h0C := th8 hC hC0
  have hbase : D ∈ D +ᵒ C := by
    have hm := ORDINAL2.th32 ORDINAL1.empty_isOrdinal hC hDord h0C
    exact Eq.subst (motive := fun s => s ∈ D +ᵒ C)
      (ORDINAL2.th27 hDord) hm
  have hDin : D ∈ E *ᵒ C := by
    rw [show E = ORDINAL1.succ d from rfl, ORDINAL2.th36 hC hordd]
    exact Eq.subst (motive := fun s => D ∈ s +ᵒ C)
      (hDd.trans (hv d hordd hdB)) hbase
  exact (ORDINAL2.ordinalMul_isOrdinal E C).1 D hDin A
    (hXD A hAX)

/-- `ORDINAL3:40` (`Th40`). -/
theorem th40 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (hlim : ORDINAL1.isLimitOrdinal A) :
    ORDINAL1.isLimitOrdinal (A *ᵒ B) := by
  by_cases hA0 : A = (∅ : TarskiSet.{u})
  · rw [hA0, ORDINAL2.th35 hB]
    exact ORDINAL2.th4
  · apply (ORDINAL1.th28 (ORDINAL2.ordinalMul_isOrdinal A B)).mpr
    intro C hC
    have hCord := ORDINAL1.th13 (ORDINAL2.ordinalMul_isOrdinal A B) hC
    obtain ⟨D, hD, hDA, hCD⟩ :=
      mul_limit_member hCord hA hB hlim hC
    have hsDA := ((ORDINAL1.th28 hA).mp hlim) D hDA
    have hB0 : B ≠ (∅ : TarskiSet.{u}) := by
      intro hb
      rw [hb, ORDINAL2.th38 hA] at hC
      exact ((XBOOLE_0.empty_iff C).mp hC).elim
    have hstep : D *ᵒ B ∈ ORDINAL1.succ D *ᵒ B := by
      rw [ORDINAL2.th36 hB hD]
      have h0B := th8 hB hB0
      have hm := ORDINAL2.th32 ORDINAL1.empty_isOrdinal hB
        (ORDINAL2.ordinalMul_isOrdinal D B) h0B
      exact Eq.subst (motive := fun s => s ∈ D *ᵒ B +ᵒ B)
        (ORDINAL2.th27 (ORDINAL2.ordinalMul_isOrdinal D B)) hm
    have hsCsub : ORDINAL1.succ C ⊆ D *ᵒ B :=
      (ORDINAL1.th21 hCord (ORDINAL2.ordinalMul_isOrdinal D B)).mp hCD
    have hsCin : ORDINAL1.succ C ∈ ORDINAL1.succ D *ᵒ B :=
      ORDINAL1.th12 (ORDINAL1.th17 hCord).1
        (ORDINAL2.ordinalMul_isOrdinal D B)
        (ORDINAL2.ordinalMul_isOrdinal (ORDINAL1.succ D) B)
        hsCsub hstep
    exact (ORDINAL2.ordinalMul_isOrdinal A B).1
      (ORDINAL1.succ D *ᵒ B)
      (ORDINAL2.th40 (ORDINAL1.th17 hD) hA hB hB0 hsDA)
      _ hsCin

/-- `ORDINAL3:41` (`Th41`). -/
theorem th41 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hlim : ORDINAL1.isLimitOrdinal B)
    (h : A ∈ B *ᵒ C) :
    ∃ D, ORDINAL1.isOrdinal D ∧ D ∈ B ∧ A ∈ D *ᵒ C :=
  mul_limit_member hA hB hC hlim h

/-- `ORDINAL3:42` (`Th42`). -/
theorem th42 {fi psi C : TarskiSet.{u}}
    (hfi : ORDINAL2.isOrdinalSequence fi)
    (hpsi : ORDINAL2.isOrdinalSequence psi)
    (hC : ORDINAL1.isOrdinal C) (hne : C ≠ (∅ : TarskiSet.{u}))
    (hlim : ORDINAL1.isLimitOrdinal (ORDINAL2.sequenceSup fi))
    (hdom : RELAT_1.dom fi = RELAT_1.dom psi)
    (hv : ∀ A, A ∈ RELAT_1.dom fi →
      FUNCT_1.apply psi A = FUNCT_1.apply fi A *ᵒ C) :
    ORDINAL2.sequenceSup psi = ORDINAL2.sequenceSup fi *ᵒ C := by
  rw [ORDINAL2.def5, ORDINAL2.def5]
  apply ordinal_eq
  · apply ORDINAL2.th20 (ORDINAL2.ordinalMul_isOrdinal (ORDINAL2.sup _) C)
    intro x hxord hx
    obtain ⟨a, had, hxa⟩ := (FUNCT_1.def3 hpsi.1.1.2).mp hx
    have haf : a ∈ RELAT_1.dom fi :=
      Eq.subst (motive := fun s => a ∈ s) hdom.symm had
    have hfr := (FUNCT_1.def3 hfi.1.1.2).mpr ⟨a, haf, rfl⟩
    have hfs := ORDINAL2.th19 (ORDINAL2.th25 hfi haf) hfr
    have hm := ORDINAL2.th40 (ORDINAL2.th25 hfi haf)
      (ORDINAL2.sup_isOrdinal _) hC hne hfs
    exact Eq.subst (motive := fun s => s ∈ ORDINAL2.sup (RELAT_1.rng fi) *ᵒ C)
      (hxa.trans (hv a haf)).symm hm
  · intro x hx
    have hxord := ORDINAL1.th13
      (ORDINAL2.ordinalMul_isOrdinal (ORDINAL2.sup _) C) hx
    obtain ⟨B, hB, hBsup, hxB⟩ :=
      th41 hxord (ORDINAL2.sup_isOrdinal _) hC hlim hx
    obtain ⟨D, hD, hDrng, hBD⟩ := ORDINAL2.th21 hB hBsup
    obtain ⟨a, had, hDa⟩ := (FUNCT_1.def3 hfi.1.1.2).mp hDrng
    have hpdom : a ∈ RELAT_1.dom psi :=
      Eq.subst (motive := fun s => a ∈ s) hdom had
    have hsub : B *ᵒ C ⊆ FUNCT_1.apply fi a *ᵒ C :=
      ORDINAL2.th41 hB (ORDINAL2.th25 hfi had) hC
        (Eq.subst (motive := fun s => B ⊆ s) hDa hBD)
    have hxin : x ∈ FUNCT_1.apply psi a :=
      Eq.subst (motive := fun s => x ∈ s) (hv a had).symm (hsub x hxB)
    have hr := (FUNCT_1.def3 hpsi.1.1.2).mpr ⟨a, hpdom, rfl⟩
    exact (ORDINAL2.sup_isOrdinal _).1 (FUNCT_1.apply psi a)
      (ORDINAL2.th19 (ORDINAL2.th25 hpsi hpdom) hr) x hxin

/-- `ORDINAL3:43` (`Th43`). -/
theorem th43 {C fi : TarskiSet.{u}} (hC : ORDINAL1.isOrdinal C)
    (hfi : ORDINAL2.isOrdinalSequence fi)
    (hne : (∅ : TarskiSet.{u}) ≠ RELAT_1.dom fi) :
    ORDINAL2.sequenceSup (addLeftSequence C fi) =
      C +ᵒ ORDINAL2.sequenceSup fi := by
  have hs := seqMap_isOrdinalSequence hfi
    (fun A _ => ORDINAL2.ordinalAdd_isOrdinal C (FUNCT_1.apply fi A))
  exact th39 hC hfi hs hne (def1 C fi).1.symm
    (fun A hA => (def1 C fi).2 A hA)

/-- `ORDINAL3:44` (`Th44`). -/
theorem th44 {fi C : TarskiSet.{u}}
    (hfi : ORDINAL2.isOrdinalSequence fi) (hC : ORDINAL1.isOrdinal C)
    (hdom0 : (∅ : TarskiSet.{u}) ≠ RELAT_1.dom fi)
    (hne : C ≠ (∅ : TarskiSet.{u}))
    (hlim : ORDINAL1.isLimitOrdinal (ORDINAL2.sequenceSup fi)) :
    ORDINAL2.sequenceSup (mulRightSequence fi C) =
      ORDINAL2.sequenceSup fi *ᵒ C := by
  have hs := seqMap_isOrdinalSequence hfi
    (fun A _ => ORDINAL2.ordinalMul_isOrdinal (FUNCT_1.apply fi A) C)
  exact th42 hfi hs hC hne hlim (def4 fi C).1.symm
    (fun A hA => (def4 fi C).2 A hA)

/-- `ORDINAL3:45` (`Th45`). -/
theorem th45 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (hne : B ≠ (∅ : TarskiSet.{u})) :
    TARSKI.union (A +ᵒ B) = A +ᵒ TARSKI.union B := by
  by_cases hlim : ORDINAL1.isLimitOrdinal B
  · have hlimAB := th29 hB hA hne hlim
    rw [← hlimAB, ← hlim]
  · obtain ⟨C, hC, heq⟩ := (ORDINAL1.th29 hB).mp hlim
    rw [heq, ORDINAL2.th28 hA hC, ORDINAL2.th2
      (ORDINAL2.ordinalAdd_isOrdinal A C), ORDINAL2.th2 hC]

/-- `ORDINAL3:46` (`Th46`): right distributivity. -/
theorem th46 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) :
    (A +ᵒ B) *ᵒ C = A *ᵒ C +ᵒ B *ᵒ C := by
  let P := fun D : TarskiSet.{u} =>
    (A +ᵒ D) *ᵒ C = A *ᵒ C +ᵒ D *ᵒ C
  have h0 : P (∅ : TarskiSet.{u}) := by
    simp only [P]
    rw [ORDINAL2.th27 hA, ORDINAL2.th35 hC,
      ORDINAL2.th27 (ORDINAL2.ordinalMul_isOrdinal A C)]
  have hs : ∀ D, ORDINAL1.isOrdinal D → P D → P (ORDINAL1.succ D) := by
    intro D hD ih
    simp only [P] at ih ⊢
    rw [ORDINAL2.th28 hA hD, ORDINAL2.th36 hC
      (ORDINAL2.ordinalAdd_isOrdinal A D), ih,
      th30 (ORDINAL2.ordinalMul_isOrdinal A C)
        (ORDINAL2.ordinalMul_isOrdinal D C) hC,
      ORDINAL2.th36 hC hD]
  have hl : ∀ D, ORDINAL1.isOrdinal D → D ≠ (∅ : TarskiSet.{u}) →
      ORDINAL1.isLimitOrdinal D → (∀ E, E ∈ D → P E) → P D := by
    intro D hD hD0 hlim ih
    by_cases hC0 : C = (∅ : TarskiSet.{u})
    · simp only [P]
      rw [hC0, ORDINAL2.th38 (ORDINAL2.ordinalAdd_isOrdinal A D),
        ORDINAL2.th38 hA, ORDINAL2.th38 hD,
        ORDINAL2.th27 ORDINAL1.empty_isOrdinal]
    · apply ordinal_eq
      · intro x hx
        have hxord := ORDINAL1.th13
          (ORDINAL2.ordinalMul_isOrdinal (A +ᵒ D) C) hx
        have hADlim := th29 hD hA hD0 hlim
        obtain ⟨E, hE, hEAD, hxE⟩ :=
          th41 hxord (ORDINAL2.ordinalAdd_isOrdinal A D) hC hADlim hx
        rcases th38 hE hA hD hEAD with hEA | ⟨F, hF, hFD, heq⟩
        · have hsEA := ORDINAL2.th41 hE hA hC (hA.1 E hEA)
          exact (th24 (ORDINAL2.ordinalMul_isOrdinal A C)
            (ORDINAL2.ordinalMul_isOrdinal D C)).1 x (hsEA x hxE)
        · have hFC : F *ᵒ C ∈ D *ᵒ C :=
            ORDINAL2.th40 hF hD hC hC0 hFD
          have hval : E *ᵒ C = A *ᵒ C +ᵒ F *ᵒ C :=
            Eq.subst (motive := fun s => s *ᵒ C = A *ᵒ C +ᵒ F *ᵒ C)
              heq.symm (ih F hFD)
          have hm := ORDINAL2.th32
            (ORDINAL2.ordinalMul_isOrdinal F C)
            (ORDINAL2.ordinalMul_isOrdinal D C)
            (ORDINAL2.ordinalMul_isOrdinal A C) hFC
          exact (ORDINAL2.ordinalAdd_isOrdinal (A *ᵒ C) (D *ᵒ C)).1
            (E *ᵒ C) (Eq.subst (motive := fun s => s ∈ A *ᵒ C +ᵒ D *ᵒ C)
              hval.symm hm) x hxE
      · intro x hx
        have hxord := ORDINAL1.th13
          (ORDINAL2.ordinalAdd_isOrdinal (A *ᵒ C) (D *ᵒ C)) hx
        rcases th38 hxord (ORDINAL2.ordinalMul_isOrdinal A C)
            (ORDINAL2.ordinalMul_isOrdinal D C) hx with hxA | ⟨E, hE, hEDC, heq⟩
        · exact (ORDINAL2.th41 hA (ORDINAL2.ordinalAdd_isOrdinal A D) hC
            (th24 hA hD).1) x hxA
        · obtain ⟨F, hF, hFD, hEF⟩ :=
            th41 hE hD hC hlim hEDC
          have hAF : A +ᵒ F ∈ A +ᵒ D :=
            ORDINAL2.th32 hF hD hA hFD
          have hval := ih F hFD
          have hm := ORDINAL2.th32 hE
            (ORDINAL2.ordinalMul_isOrdinal F C)
            (ORDINAL2.ordinalMul_isOrdinal A C) hEF
          have hxin : x ∈ (A +ᵒ F) *ᵒ C :=
            Eq.subst (motive := fun s => x ∈ s) hval.symm
              (Eq.subst (motive := fun s => s ∈
                A *ᵒ C +ᵒ F *ᵒ C) heq.symm hm)
          exact (ORDINAL2.th41 (ORDINAL2.ordinalAdd_isOrdinal A F)
            (ORDINAL2.ordinalAdd_isOrdinal A D) hC
            ((ORDINAL2.ordinalAdd_isOrdinal A D).1 _ hAF)) x hxin
  exact ORDINAL2.sch_OrdinalInd P h0 hs hl B hB

/-! ## Division algorithm and multiplication associativity -/

/-- `ORDINAL3:47` (`Th47`). -/
theorem th47 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (hne : A ≠ (∅ : TarskiSet.{u})) :
    ∃ C D, ORDINAL1.isOrdinal C ∧ ORDINAL1.isOrdinal D ∧
      B = C *ᵒ A +ᵒ D ∧ D ∈ A := by
  let P := fun C : TarskiSet.{u} => B ∈ C *ᵒ A
  have hex : ∃ C, ORDINAL1.isOrdinal C ∧ P C := by
    refine ⟨ORDINAL1.succ B, ORDINAL1.th17 hB, ?_⟩
    exact (th36 (ORDINAL1.th17 hB) hA hne).1 B (ORDINAL1.th6 B)
  obtain ⟨C, hC, hPC, hleast⟩ := ORDINAL1.sch_OrdinalMin P hex
  have hC0 : C ≠ (∅ : TarskiSet.{u}) := by
    intro hc
    change B ∈ C *ᵒ A at hPC
    rw [hc, ORDINAL2.th35 hA] at hPC
    exact ((XBOOLE_0.empty_iff B).mp hPC).elim
  have hnlim : ¬ ORDINAL1.isLimitOrdinal C := by
    intro hlim
    obtain ⟨D, hD, hDC, hBD⟩ :=
      th41 hB hC hA hlim hPC
    exact ORDINAL1.th5 hDC (hleast D hD hBD)
  obtain ⟨Q, hQ, hCQ⟩ := (ORDINAL1.th29 hC).mp hnlim
  have hnot : B ∉ Q *ᵒ A := fun h =>
    ORDINAL1.th5
      (Eq.subst (motive := fun s => Q ∈ s) hCQ.symm (ORDINAL1.th6 Q))
      (hleast Q hQ h)
  have hsub : Q *ᵒ A ⊆ B := by
    rcases ORDINAL1.th16 (ORDINAL2.ordinalMul_isOrdinal Q A) hB with hs | hm
    · exact hs
    · exact (hnot hm).elim
  obtain ⟨D, hD, hEq⟩ :=
    th27 (ORDINAL2.ordinalMul_isOrdinal Q A) hB hsub
  have hDA : D ∈ A := by
    have hPin : B ∈ Q *ᵒ A +ᵒ A := by
      rw [← ORDINAL2.th36 hA hQ, ← hCQ]
      exact hPC
    have hEqMem : Q *ᵒ A +ᵒ D ∈ Q *ᵒ A +ᵒ A :=
      Eq.subst (motive := fun s => s ∈ Q *ᵒ A +ᵒ A) hEq hPin
    exact th22 (ORDINAL2.ordinalMul_isOrdinal Q A) hD hA hEqMem
  exact ⟨Q, D, hQ, hD, hEq, hDA⟩

/-- `ORDINAL3:48` (`Th48`). -/
theorem th48 {A C1 D1 C2 D2 : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A)
    (hC1 : ORDINAL1.isOrdinal C1) (hD1 : ORDINAL1.isOrdinal D1)
    (hC2 : ORDINAL1.isOrdinal C2) (hD2 : ORDINAL1.isOrdinal D2)
    (heq : C1 *ᵒ A +ᵒ D1 = C2 *ᵒ A +ᵒ D2)
    (hD1A : D1 ∈ A) (hD2A : D2 ∈ A) :
    C1 = C2 ∧ D1 = D2 := by
  have hn21 : C2 ∉ C1 := by
    intro h21
    obtain ⟨C, hC, hEqC, hC0⟩ := th28 hC2 hC1 h21
    have hmul := th46 hC2 hC hA
    have hcancel : D2 = C *ᵒ A +ᵒ D1 := by
      apply th21 (ORDINAL2.ordinalMul_isOrdinal C2 A) hD2
        (ORDINAL2.ordinalAdd_isOrdinal (C *ᵒ A) D1)
      calc
        C2 *ᵒ A +ᵒ D2 = C1 *ᵒ A +ᵒ D1 := heq.symm
        _ = (C2 +ᵒ C) *ᵒ A +ᵒ D1 := by rw [← hEqC]
        _ = (C2 *ᵒ A +ᵒ C *ᵒ A) +ᵒ D1 := by rw [hmul]
        _ = C2 *ᵒ A +ᵒ (C *ᵒ A +ᵒ D1) :=
          th30 (ORDINAL2.ordinalMul_isOrdinal C2 A)
            (ORDINAL2.ordinalMul_isOrdinal C A) hD1
    have hAsub : A ⊆ C *ᵒ A := (th36 hA hC hC0).2
    have hCsub := (th24 (ORDINAL2.ordinalMul_isOrdinal C A) hD1).1
    exact ORDINAL1.th5 hD2A
      (Eq.subst (motive := fun s => A ⊆ s) hcancel.symm
        (XBOOLE_1.th1 hAsub hCsub))
  have hn12 : C1 ∉ C2 := by
    intro h12
    obtain ⟨C, hC, hEqC, hC0⟩ := th28 hC1 hC2 h12
    have hmul := th46 hC1 hC hA
    have hcancel : D1 = C *ᵒ A +ᵒ D2 := by
      apply th21 (ORDINAL2.ordinalMul_isOrdinal C1 A) hD1
        (ORDINAL2.ordinalAdd_isOrdinal (C *ᵒ A) D2)
      calc
        C1 *ᵒ A +ᵒ D1 = C2 *ᵒ A +ᵒ D2 := heq
        _ = (C1 +ᵒ C) *ᵒ A +ᵒ D2 := by rw [← hEqC]
        _ = (C1 *ᵒ A +ᵒ C *ᵒ A) +ᵒ D2 := by rw [hmul]
        _ = C1 *ᵒ A +ᵒ (C *ᵒ A +ᵒ D2) :=
          th30 (ORDINAL2.ordinalMul_isOrdinal C1 A)
            (ORDINAL2.ordinalMul_isOrdinal C A) hD2
    have hAsub : A ⊆ C *ᵒ A := (th36 hA hC hC0).2
    have hCsub := (th24 (ORDINAL2.ordinalMul_isOrdinal C A) hD2).1
    exact ORDINAL1.th5 hD1A
      (Eq.subst (motive := fun s => A ⊆ s) hcancel.symm
        (XBOOLE_1.th1 hAsub hCsub))
  have hCeq : C1 = C2 := by
    rcases ORDINAL1.th14 hC1 hC2 with h | h | h
    · exact (hn12 h).elim
    · exact h
    · exact (hn21 h).elim
  refine ⟨hCeq, ?_⟩
  subst C2
  exact th21 (ORDINAL2.ordinalMul_isOrdinal C1 A) hD1 hD2 heq

/-- `ORDINAL3:49` (`Th49`). -/
theorem th49 {A B fi : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hfi : ORDINAL2.isOrdinalSequence fi)
    (hOneB : FUNCT_3.one ∈ B)
    (hne : A ≠ (∅ : TarskiSet.{u}))
    (hlim : ORDINAL1.isLimitOrdinal A)
    (hdom : RELAT_1.dom fi = A)
    (hv : ∀ C, C ∈ A → FUNCT_1.apply fi C = C *ᵒ B) :
    A *ᵒ B = ORDINAL2.sequenceSup fi := by
  have hsupLim : ORDINAL1.isLimitOrdinal (ORDINAL2.sequenceSup fi) := by
    apply Classical.byContradiction
    intro hn
    obtain ⟨C, hC, hEq⟩ :=
      (ORDINAL1.th29 (ORDINAL2.sequenceSup_isOrdinal fi)).mp hn
    have hCin : C ∈ ORDINAL2.sequenceSup fi :=
      Eq.subst (motive := fun s => C ∈ s) hEq.symm (ORDINAL1.th6 C)
    rw [ORDINAL2.def5] at hCin
    obtain ⟨D, hD, hDrng, hCD⟩ :=
      ORDINAL2.th21 hC hCin
    have hDsup := ORDINAL2.th19 hD hDrng
    have hDsubC : D ⊆ C :=
      (ORDINAL1.th22 hD hC).mp
        (Eq.subst (motive := fun s => D ∈ s) hEq hDsup)
    have hCDsub : C ⊆ D := hCD
    have hCD_eq : C = D := ordinal_eq hCDsub hDsubC
    obtain ⟨x, hxd, hDx⟩ := (FUNCT_1.def3 hfi.1.1.2).mp hDrng
    have hxA : x ∈ A := Eq.subst (motive := fun s => x ∈ s) hdom hxd
    have hx := ORDINAL1.th13 hA hxA
    have hsxA := ((ORDINAL1.th28 hA).mp hlim) x hxA
    have hsxd : ORDINAL1.succ x ∈ RELAT_1.dom fi :=
      Eq.subst (motive := fun s => ORDINAL1.succ x ∈ s) hdom.symm hsxA
    have hnextRng : FUNCT_1.apply fi (ORDINAL1.succ x) ∈ RELAT_1.rng fi :=
      (FUNCT_1.def3 hfi.1.1.2).mpr ⟨ORDINAL1.succ x, hsxd, rfl⟩
    have hvalx : C = x *ᵒ B :=
      hCD_eq.trans (hDx.trans (hv x hxA))
    have hvalnext : FUNCT_1.apply fi (ORDINAL1.succ x) = C +ᵒ B := by
      rw [hv (ORDINAL1.succ x) hsxA, ORDINAL2.th36 hB hx, ← hvalx]
    have hC1 : C +ᵒ FUNCT_3.one ∈ C +ᵒ B :=
      ORDINAL2.th32 one_isOrdinal hB hC hOneB
    rw [ORDINAL2.th31 hC] at hC1
    have hnextSup := ORDINAL2.th19
      (ORDINAL2.th25 hfi hsxd) hnextRng
    have hCBsup : C +ᵒ B ∈ ORDINAL2.sequenceSup fi :=
      Eq.subst (motive := fun s => s ∈ ORDINAL2.sequenceSup fi)
        hvalnext hnextSup
    have hs : ORDINAL1.succ C ∈ ORDINAL2.sequenceSup fi :=
      (ORDINAL2.sequenceSup_isOrdinal fi).1
        (C +ᵒ B) hCBsup (ORDINAL1.succ C) hC1
    exact ORDINAL1.not_mem_self (ORDINAL1.succ C)
      (Eq.subst (motive := fun s => ORDINAL1.succ C ∈ s) hEq hs)
  have hrec := ORDINAL2.th37 hB hA hne hlim hfi hdom
    (fun C _ hCA => hv C hCA)
  exact hrec.trans hsupLim.symm

/-- `ORDINAL3:50` (unlabeled): associativity of ordinal multiplication. -/
theorem th50 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) :
    (A *ᵒ B) *ᵒ C = A *ᵒ (B *ᵒ C) := by
  let P := fun D : TarskiSet.{u} => (D *ᵒ B) *ᵒ C = D *ᵒ (B *ᵒ C)
  have h0 : P (∅ : TarskiSet.{u}) := by
    simp only [P]
    rw [ORDINAL2.th35 hB, ORDINAL2.th35 hC,
      ORDINAL2.th35 (ORDINAL2.ordinalMul_isOrdinal B C)]
  have hs : ∀ D, ORDINAL1.isOrdinal D → P D → P (ORDINAL1.succ D) := by
    intro D hD ih
    simp only [P] at ih ⊢
    rw [ORDINAL2.th36 hB hD,
      th46 (ORDINAL2.ordinalMul_isOrdinal D B) hB hC, ih,
      ORDINAL2.th36 (ORDINAL2.ordinalMul_isOrdinal B C) hD]
  have hl : ∀ D, ORDINAL1.isOrdinal D → D ≠ (∅ : TarskiSet.{u}) →
      ORDINAL1.isLimitOrdinal D → (∀ E, E ∈ D → P E) → P D := by
    intro D hD hD0 hlim ih
    by_cases hOneB : FUNCT_3.one ∈ B
    · by_cases hOneC : FUNCT_3.one ∈ C
      · obtain ⟨fi, hfi, hd, hv⟩ :=
          ORDINAL2.sch_OSLambda hD (fun E => E *ᵒ B)
            (fun E _ _ => ORDINAL2.ordinalMul_isOrdinal E B)
        have hDB := th49 hD hB hfi hOneB hD0 hlim hd
          (fun E hED => hv E (ORDINAL1.th13 hD hED) hED)
        have hBCone : FUNCT_3.one ∈ B *ᵒ C := by
          have hm := th19 one_isOrdinal hB one_isOrdinal hC
            hOneB (Or.inr hOneC)
          rw [(ORDINAL2.th39 one_isOrdinal).1] at hm
          exact hm
        have hmap : ORDINAL2.isOrdinalSequence (mulRightSequence fi C) :=
          seqMap_isOrdinalSequence hfi
            (fun E _ => ORDINAL2.ordinalMul_isOrdinal
              (FUNCT_1.apply fi E) C)
        have hEqSeq : mulRightSequence fi C =
            (seqMap (fun E => E *ᵒ (B *ᵒ C)) fi) := by
          apply FUNCT_1.th2
            (seqMap_spec (fun E => FUNCT_1.apply fi E *ᵒ C) fi).1
            (seqMap_spec (fun E => E *ᵒ (B *ᵒ C)) fi).1
            ((def4 fi C).1.trans
              (seqMap_spec (fun E => E *ᵒ (B *ᵒ C)) fi).2.1.symm)
          intro E hEd
          have hEfi : E ∈ RELAT_1.dom fi :=
            Eq.subst (motive := fun s => E ∈ s) (def4 fi C).1 hEd
          have hED : E ∈ D := Eq.subst (motive := fun s => E ∈ s) hd hEfi
          rw [(seqMap_spec (fun E => FUNCT_1.apply fi E *ᵒ C) fi).2.2 E hEfi,
            (seqMap_spec (fun E => E *ᵒ (B *ᵒ C)) fi).2.2 E hEfi,
            hv E (ORDINAL1.th13 hD hED) hED, ih E hED]
        have hright := th49 hD (ORDINAL2.ordinalMul_isOrdinal B C)
          (seqMap_isOrdinalSequence hfi
            (fun E _ => ORDINAL2.ordinalMul_isOrdinal E (B *ᵒ C)))
          hBCone hD0 hlim
          ((seqMap_spec (fun E => E *ᵒ (B *ᵒ C)) fi).2.1.trans hd)
          (fun E hED => (seqMap_spec
            (fun E => E *ᵒ (B *ᵒ C)) fi).2.2 E
              (Eq.subst (motive := fun s => E ∈ s) hd.symm hED))
        calc
          (D *ᵒ B) *ᵒ C =
              ORDINAL2.sequenceSup (mulRightSequence fi C) := by
                rw [hDB]
                exact (th44 hfi hC (hd ▸ hD0.symm) (fun hc =>
                  (XBOOLE_0.empty_iff FUNCT_3.one).mp (hc ▸ hOneC))
                  (Eq.subst (motive := ORDINAL1.isLimitOrdinal)
                    hDB (th40 hD hB hlim))).symm
          _ = ORDINAL2.sequenceSup
              (seqMap (fun E => E *ᵒ (B *ᵒ C)) fi) :=
                congrArg ORDINAL2.sequenceSup hEqSeq
          _ = D *ᵒ (B *ᵒ C) := hright.symm
      · have hCsmall : C = (∅ : TarskiSet.{u}) ∨ C = FUNCT_3.one := by
          have hCsub : C ⊆ FUNCT_3.one :=
            (ORDINAL1.th16 hC one_isOrdinal).resolve_right hOneC
          exact th16 hC hCsub
        rcases hCsmall with hc | hc
        · simp only [P]; rw [hc, ORDINAL2.th38
            (ORDINAL2.ordinalMul_isOrdinal D B),
            ORDINAL2.th38 hB, ORDINAL2.th38 hD]
        · simp only [P]; rw [hc, (ORDINAL2.th39
            (ORDINAL2.ordinalMul_isOrdinal D B)).2,
            (ORDINAL2.th39 hB).2]
    · have hBsmall : B = (∅ : TarskiSet.{u}) ∨ B = FUNCT_3.one := by
        have hBsub : B ⊆ FUNCT_3.one :=
          (ORDINAL1.th16 hB one_isOrdinal).resolve_right hOneB
        exact th16 hB hBsub
      rcases hBsmall with hb | hb
      · simp only [P]; rw [hb, ORDINAL2.th38 hD,
          ORDINAL2.th35 hC, ORDINAL2.th38 hD]
      · simp only [P]; rw [hb, (ORDINAL2.th39 hD).2,
          (ORDINAL2.th39 hC).1]
  exact ORDINAL2.sch_OrdinalInd P h0 hs hl A hA

/-! ## Ordinal subtraction, quotient, and remainder -/

private theorem sub_exists {A B : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hBA : B ⊆ A) :
    ∃ C, ORDINAL1.isOrdinal C ∧ A = B +ᵒ C :=
  th27 hB hA hBA

/-- `ORDINAL3:def 5` — right ordinal subtraction `A -^ B`. -/
noncomputable def ordinalSub (A B : TarskiSet.{u}) : TarskiSet.{u} := by
  classical
  exact if h : ORDINAL1.isOrdinal A ∧ ORDINAL1.isOrdinal B ∧ B ⊆ A
    then Classical.choose (sub_exists h.1 h.2.1 h.2.2)
    else (∅ : TarskiSet.{u})

theorem ordinalSub_isOrdinal (A B : TarskiSet.{u}) :
    ORDINAL1.isOrdinal (ordinalSub A B) := by
  classical
  unfold ordinalSub
  split
  · rename_i h
    exact (Classical.choose_spec (sub_exists h.1 h.2.1 h.2.2)).1
  · exact ORDINAL1.empty_isOrdinal

theorem def5 {A B : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B) :
    (B ⊆ A → A = B +ᵒ ordinalSub A B) ∧
      (¬ B ⊆ A → ordinalSub A B = (∅ : TarskiSet.{u})) := by
  classical
  constructor
  · intro hBA
    unfold ordinalSub
    rw [dif_pos ⟨hA, hB, hBA⟩]
    exact (Classical.choose_spec (sub_exists hA hB hBA)).2
  · intro hn
    unfold ordinalSub
    rw [dif_neg (fun h => hn h.2.2)]

private theorem div_exists {A B : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hne : B ≠ (∅ : TarskiSet.{u})) :
    ∃ Q, ORDINAL1.isOrdinal Q ∧
      ∃ R, ORDINAL1.isOrdinal R ∧ A = Q *ᵒ B +ᵒ R ∧ R ∈ B := by
  obtain ⟨Q, R, hQ, hR, heq, hRB⟩ := th47 hB hA hne
  exact ⟨Q, hQ, R, hR, heq, hRB⟩

/-- `ORDINAL3:def 6` — ordinal quotient `A div^ B`. -/
noncomputable def ordinalDiv (A B : TarskiSet.{u}) : TarskiSet.{u} := by
  classical
  exact if h : ORDINAL1.isOrdinal A ∧ ORDINAL1.isOrdinal B ∧
      B ≠ (∅ : TarskiSet.{u})
    then Classical.choose (div_exists h.1 h.2.1 h.2.2)
    else (∅ : TarskiSet.{u})

theorem ordinalDiv_isOrdinal (A B : TarskiSet.{u}) :
    ORDINAL1.isOrdinal (ordinalDiv A B) := by
  classical
  unfold ordinalDiv
  split
  · rename_i h
    exact (Classical.choose_spec (div_exists h.1 h.2.1 h.2.2)).1
  · exact ORDINAL1.empty_isOrdinal

theorem def6 {A B : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B) :
    (B ≠ (∅ : TarskiSet.{u}) →
      ∃ C, ORDINAL1.isOrdinal C ∧
        A = ordinalDiv A B *ᵒ B +ᵒ C ∧ C ∈ B) ∧
      (B = (∅ : TarskiSet.{u}) →
        ordinalDiv A B = (∅ : TarskiSet.{u})) := by
  classical
  constructor
  · intro hne
    unfold ordinalDiv
    rw [dif_pos ⟨hA, hB, hne⟩]
    exact (Classical.choose_spec (div_exists hA hB hne)).2
  · intro he
    unfold ordinalDiv
    rw [dif_neg (fun h => h.2.2 he)]

/-- `ORDINAL3:def 7` — ordinal remainder `A mod^ B`. -/
noncomputable def ordinalMod (A B : TarskiSet.{u}) : TarskiSet.{u} :=
  ordinalSub A (ordinalDiv A B *ᵒ B)

theorem def7 (A B : TarskiSet.{u}) :
    ordinalMod A B = ordinalSub A (ordinalDiv A B *ᵒ B) :=
  rfl

/-- `ORDINAL3:51` (unlabeled). -/
theorem th51 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (hAB : A ∈ B) :
    B = A +ᵒ ordinalSub B A :=
  (def5 hB hA).1 (hB.1 A hAB)

/-- `ORDINAL3:52` (`Th52`). -/
theorem th52 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) :
    ordinalSub (A +ᵒ B) A = B := by
  have hEq := (def5 (ORDINAL2.ordinalAdd_isOrdinal A B) hA).1
    (th24 hA hB).1
  exact th21 hA (ordinalSub_isOrdinal (A +ᵒ B) A) hB
    hEq.symm

/-- `ORDINAL3:53` (`Th53`). -/
theorem th53 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hAB : A ∈ B)
    (hCA : C ⊆ A ∨ C ∈ A) :
    ordinalSub A C ∈ ordinalSub B C := by
  have hCA' : C ⊆ A := hCA.elim id (fun h => hA.1 C h)
  have hCB : C ⊆ B := XBOOLE_1.th1 hCA' (hB.1 A hAB)
  have hEqA := (def5 hA hC).1 hCA'
  have hEqB := (def5 hB hC).1 hCB
  have hm : C +ᵒ ordinalSub A C ∈ C +ᵒ ordinalSub B C :=
    Eq.subst (motive := fun s => s ∈ C +ᵒ ordinalSub B C)
      hEqA (Eq.subst (motive := fun s => A ∈ s) hEqB hAB)
  exact th22 hC (ordinalSub_isOrdinal A C)
    (ordinalSub_isOrdinal B C) hm

/-- `ORDINAL3:54` (`Th54`). -/
theorem th54 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ordinalSub A A = (∅ : TarskiSet.{u}) := by
  have h := (def5 hA hA).1 (subset_refl A)
  have he : A = A +ᵒ (∅ : TarskiSet.{u}) := (ORDINAL2.th27 hA).symm
  exact th21 hA (ordinalSub_isOrdinal A A) ORDINAL1.empty_isOrdinal
    (h.symm.trans he)

/-- `ORDINAL3:55` (unlabeled). -/
theorem th55 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (hAB : A ∈ B) :
    ordinalSub B A ≠ (∅ : TarskiSet.{u}) ∧
      (∅ : TarskiSet.{u}) ∈ ordinalSub B A := by
  have hm := th53 hA hB hA hAB (Or.inl (subset_refl A))
  rw [th54 hA] at hm
  exact ⟨fun he => (XBOOLE_0.empty_iff (∅ : TarskiSet.{u})).mp (he ▸ hm),
    hm⟩

/-- `ORDINAL3:56` (`Th56`). -/
theorem th56 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ordinalSub A (∅ : TarskiSet.{u}) = A ∧
      ordinalSub (∅ : TarskiSet.{u}) A = (∅ : TarskiSet.{u}) := by
  constructor
  · have h := (def5 hA ORDINAL1.empty_isOrdinal).1 XBOOLE_1.th2
    rw [ORDINAL2.th30 (ordinalSub_isOrdinal A (∅ : TarskiSet.{u}))] at h
    exact h.symm
  · by_cases hsub : A ⊆ (∅ : TarskiSet.{u})
    · have hA0 := XBOOLE_1.th3 hsub
      rw [hA0, th54 ORDINAL1.empty_isOrdinal]
    · exact (def5 ORDINAL1.empty_isOrdinal hA).2 hsub

/-- `ORDINAL3:57` (unlabeled). -/
theorem th57 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) :
    ordinalSub A (B +ᵒ C) =
      ordinalSub (ordinalSub A B) C := by
  by_cases hBA : B ⊆ A
  · have hAB := (def5 hA hB).1 hBA
    by_cases hCsub : C ⊆ ordinalSub A B
    · have h1 := (def5 (ordinalSub_isOrdinal A B) hC).1 hCsub
      have hsum : B +ᵒ C ⊆ A := by
        exact Eq.subst (motive := fun s => B +ᵒ C ⊆ s) hAB.symm
          (ORDINAL2.th33 hC (ordinalSub_isOrdinal A B) hB hCsub)
      have h2 := (def5 hA (ORDINAL2.ordinalAdd_isOrdinal B C)).1 hsum
      apply th21 (ORDINAL2.ordinalAdd_isOrdinal B C)
        (ordinalSub_isOrdinal A (B +ᵒ C))
        (ordinalSub_isOrdinal (ordinalSub A B) C)
      calc
        (B +ᵒ C) +ᵒ ordinalSub A (B +ᵒ C) = A := h2.symm
        _ = B +ᵒ ordinalSub A B := hAB
        _ = B +ᵒ (C +ᵒ ordinalSub (ordinalSub A B) C) :=
          congrArg (ORDINAL2.ordinalAdd B) h1
        _ = (B +ᵒ C) +ᵒ ordinalSub (ordinalSub A B) C :=
          (th30 hB hC (ordinalSub_isOrdinal (ordinalSub A B) C)).symm
    · have hr := (def5 (ordinalSub_isOrdinal A B) hC).2 hCsub
      have hsumNot : ¬ B +ᵒ C ⊆ A := by
        intro hs
        have hs' : B +ᵒ C ⊆ B +ᵒ ordinalSub A B :=
          Eq.subst (motive := fun s => B +ᵒ C ⊆ s) hAB hs
        exact hCsub (th23 hB hC (ordinalSub_isOrdinal A B) hs')
      rw [(def5 hA (ORDINAL2.ordinalAdd_isOrdinal B C)).2 hsumNot, hr]
  · have hAB0 := (def5 hA hB).2 hBA
    have hsumNot : ¬ B +ᵒ C ⊆ A := fun hs =>
      hBA (XBOOLE_1.th1 (th24 hB hC).1 hs)
    rw [(def5 hA (ORDINAL2.ordinalAdd_isOrdinal B C)).2 hsumNot,
      hAB0, (th56 hC).2]

/-- `ORDINAL3:58` (unlabeled). -/
theorem th58 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hAB : A ⊆ B) :
    ordinalSub C B ⊆ ordinalSub C A := by
  by_cases hBC : B ⊆ C
  · have hAC := XBOOLE_1.th1 hAB hBC
    have hEqB := (def5 hC hB).1 hBC
    have hEqA := (def5 hC hA).1 hAC
    obtain ⟨D, hD, hBD⟩ := th27 hA hB hAB
    have hcan :
        A +ᵒ (D +ᵒ ordinalSub C B) =
          A +ᵒ ordinalSub C A := by
      calc
        A +ᵒ (D +ᵒ ordinalSub C B) =
            (A +ᵒ D) +ᵒ ordinalSub C B :=
          (th30 hA hD (ordinalSub_isOrdinal C B)).symm
        _ = B +ᵒ ordinalSub C B := by rw [← hBD]
        _ = C := hEqB.symm
        _ = A +ᵒ ordinalSub C A := hEqA
    have heq : D +ᵒ ordinalSub C B = ordinalSub C A :=
      th21 hA (ORDINAL2.ordinalAdd_isOrdinal D (ordinalSub C B))
        (ordinalSub_isOrdinal C A) hcan
    exact Eq.subst (motive := fun s => ordinalSub C B ⊆ s) heq
      (th24 hD (ordinalSub_isOrdinal C B)).2
  · rw [(def5 hC hB).2 hBC]
    exact XBOOLE_1.th2

/-- `ORDINAL3:59` (unlabeled). -/
theorem th59 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hAB : A ⊆ B) :
    ordinalSub A C ⊆ ordinalSub B C := by
  by_cases hCA : C ⊆ A
  · have hCB := XBOOLE_1.th1 hCA hAB
    have hEqA := (def5 hA hC).1 hCA
    have hEqB := (def5 hB hC).1 hCB
    apply th23 hC (ordinalSub_isOrdinal A C) (ordinalSub_isOrdinal B C)
    exact Eq.subst (motive := fun s => s ⊆ C +ᵒ ordinalSub B C)
      hEqA (Eq.subst (motive := fun s => A ⊆ s) hEqB hAB)
  · rw [(def5 hA hC).2 hCA]
    exact XBOOLE_1.th2

/-- `ORDINAL3:60` (unlabeled). -/
theorem th60 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hne : C ≠ (∅ : TarskiSet.{u}))
    (h : A ∈ B +ᵒ C) :
    ordinalSub A B ∈ C := by
  by_cases hBA : B ⊆ A
  · have hm := th53 hA (ORDINAL2.ordinalAdd_isOrdinal B C) hB h
      (Or.inl hBA)
    rw [th52 hB hC] at hm
    exact hm
  · rw [(def5 hA hB).2 hBA]
    exact th8 hC hne

/-- `ORDINAL3:61` (unlabeled). -/
theorem th61 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (h : A +ᵒ B ∈ C) :
    B ∈ ordinalSub C A := by
  have hsub : A ⊆ A +ᵒ B := (th24 hA hB).1
  have hm := th53 (ORDINAL2.ordinalAdd_isOrdinal A B) hC hA h
    (Or.inl hsub)
  rw [th52 hA hB] at hm
  exact hm

/-- `ORDINAL3:62` (unlabeled). -/
theorem th62 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) :
    A ⊆ B +ᵒ ordinalSub A B := by
  by_cases hBA : B ⊆ A
  · rw [← (def5 hA hB).1 hBA]
  · rw [(def5 hA hB).2 hBA, ORDINAL2.th27 hB]
    exact (ORDINAL1.th16 hA hB).resolve_right
      (fun hm => hBA (hA.1 B hm))

/-- `ORDINAL3:63` (unlabeled). -/
theorem th63 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) :
    ordinalSub (A *ᵒ C) (B *ᵒ C) =
      ordinalSub A B *ᵒ C := by
  by_cases hBA : B ⊆ A
  · have hEq := (def5 hA hB).1 hBA
    have hm := th46 hB (ordinalSub_isOrdinal A B) hC
    have hprod : B *ᵒ C ⊆ A *ᵒ C :=
      ORDINAL2.th41 hB hA hC hBA
    have hd := (def5 (ORDINAL2.ordinalMul_isOrdinal A C)
      (ORDINAL2.ordinalMul_isOrdinal B C)).1 hprod
    exact th21 (ORDINAL2.ordinalMul_isOrdinal B C)
      (ordinalSub_isOrdinal (A *ᵒ C) (B *ᵒ C))
      (ORDINAL2.ordinalMul_isOrdinal (ordinalSub A B) C)
      (hd.symm.trans (Eq.subst (motive := fun s =>
        s *ᵒ C = B *ᵒ C +ᵒ ordinalSub A B *ᵒ C) hEq.symm hm))
  · have hs0 := (def5 hA hB).2 hBA
    by_cases hC0 : C = (∅ : TarskiSet.{u})
    · rw [hC0, ORDINAL2.th38 hA, ORDINAL2.th38 hB,
        th54 ORDINAL1.empty_isOrdinal, ORDINAL2.th38
          (ordinalSub_isOrdinal A B)]
    · have hnprod : ¬ B *ᵒ C ⊆ A *ᵒ C :=
        fun hs => hBA (th35 hC hB hA hC0 hs)
      rw [(def5 (ORDINAL2.ordinalMul_isOrdinal A C)
        (ORDINAL2.ordinalMul_isOrdinal B C)).2 hnprod,
        hs0, ORDINAL2.th35 hC]

/-- `ORDINAL3:64` (`Th64`). -/
theorem th64 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) :
    ordinalDiv A B *ᵒ B ⊆ A := by
  by_cases hB0 : B = (∅ : TarskiSet.{u})
  · subst B
    rw [(def6 hA ORDINAL1.empty_isOrdinal).2 rfl,
      ORDINAL2.th35 ORDINAL1.empty_isOrdinal]
    exact XBOOLE_1.th2
  · obtain ⟨C, hC, heq, _⟩ := (def6 hA hB).1 hB0
    exact Eq.subst (motive := fun s => ordinalDiv A B *ᵒ B ⊆ s)
      heq.symm (th24 (ORDINAL2.ordinalMul_isOrdinal (ordinalDiv A B) B) hC).1

/-- `ORDINAL3:65` (`Th65`). -/
theorem th65 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) :
    A = ordinalDiv A B *ᵒ B +ᵒ ordinalMod A B := by
  exact (def5 hA (ORDINAL2.ordinalMul_isOrdinal (ordinalDiv A B) B)).1
    (th64 hA hB)

/-- `ORDINAL3:66` (unlabeled). -/
theorem th66 {A B C D : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (hD : ORDINAL1.isOrdinal D)
    (heq : A = B *ᵒ C +ᵒ D) (hDC : D ∈ C) :
    B = ordinalDiv A C ∧ D = ordinalMod A C := by
  have hC0 : C ≠ (∅ : TarskiSet.{u}) := fun hc =>
    (XBOOLE_0.empty_iff D).mp (hc ▸ hDC)
  obtain ⟨R, hR, hEqR, hRC⟩ := (def6 hA hC).1 hC0
  have hu := th48 hC hB hD (ordinalDiv_isOrdinal A C) hR
    (heq.symm.trans hEqR) hDC hRC
  refine ⟨hu.1, ?_⟩
  have hm : ordinalMod A C = D := by
    rw [def7, ← hu.1, heq,
      th52 (ORDINAL2.ordinalMul_isOrdinal B C) hD]
  exact hm.symm

/-- `ORDINAL3:67` (unlabeled). -/
theorem th67 {A B C : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hC : ORDINAL1.isOrdinal C) (h : A ∈ B *ᵒ C) :
    ordinalDiv A C ∈ B ∧ ordinalMod A C ∈ C := by
  have hC0 : C ≠ (∅ : TarskiSet.{u}) := by
    intro hc
    rw [hc, ORDINAL2.th38 hB] at h
    exact ((XBOOLE_0.empty_iff A).mp h).elim
  obtain ⟨R, hR, heq, hRC⟩ := (def6 hA hC).1 hC0
  have hsub := (th24 (ORDINAL2.ordinalMul_isOrdinal (ordinalDiv A C) C) hR).1
  have hqprod : ordinalDiv A C *ᵒ C ∈ B *ᵒ C :=
    ORDINAL1.th12 (ORDINAL2.ordinalMul_isOrdinal (ordinalDiv A C) C).1
      hA (ORDINAL2.ordinalMul_isOrdinal B C)
      (Eq.subst (motive := fun s => ordinalDiv A C *ᵒ C ⊆ s)
        heq.symm hsub) h
  have hq : ordinalDiv A C ∈ B :=
    th34 hC (ordinalDiv_isOrdinal A C) hB hqprod
  have hmod : ordinalMod A C = R := by
    calc
      ordinalMod A C =
          ordinalSub A (ordinalDiv A C *ᵒ C) := rfl
      _ = ordinalSub (ordinalDiv A C *ᵒ C +ᵒ R)
          (ordinalDiv A C *ᵒ C) :=
        congrArg (fun s => ordinalSub s (ordinalDiv A C *ᵒ C)) heq
      _ = R := th52
        (ORDINAL2.ordinalMul_isOrdinal (ordinalDiv A C) C) hR
  exact ⟨hq, hmod ▸ hRC⟩

/-- `ORDINAL3:68` (`Th68`). -/
theorem th68 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (hne : B ≠ (∅ : TarskiSet.{u})) :
    ordinalDiv (A *ᵒ B) B = A := by
  have h0B := th8 hB hne
  have heq : A *ᵒ B = A *ᵒ B +ᵒ (∅ : TarskiSet.{u}) :=
    (ORDINAL2.th27 (ORDINAL2.ordinalMul_isOrdinal A B)).symm
  exact (th66 (ORDINAL2.ordinalMul_isOrdinal A B) hA hB
    ORDINAL1.empty_isOrdinal heq h0B).1.symm

/-- `ORDINAL3:69` (unlabeled). -/
theorem th69 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) :
    ordinalMod (A *ᵒ B) B = (∅ : TarskiSet.{u}) := by
  by_cases hB0 : B = (∅ : TarskiSet.{u})
  · rw [hB0, ORDINAL2.th38 hA, def7,
      (def6 ORDINAL1.empty_isOrdinal ORDINAL1.empty_isOrdinal).2 rfl,
      ORDINAL2.th35 ORDINAL1.empty_isOrdinal,
      th54 ORDINAL1.empty_isOrdinal]
  · exact (th66 (ORDINAL2.ordinalMul_isOrdinal A B) hA hB
      ORDINAL1.empty_isOrdinal
      (ORDINAL2.th27 (ORDINAL2.ordinalMul_isOrdinal A B)).symm
      (th8 hB hB0)).2.symm

/-- `ORDINAL3:70` (unlabeled). -/
theorem th70 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ordinalDiv (∅ : TarskiSet.{u}) A = (∅ : TarskiSet.{u}) ∧
      ordinalMod (∅ : TarskiSet.{u}) A = (∅ : TarskiSet.{u}) ∧
      ordinalMod A (∅ : TarskiSet.{u}) = A := by
  have hdiv : ordinalDiv (∅ : TarskiSet.{u}) A =
      (∅ : TarskiSet.{u}) := by
    by_cases hA0 : A = (∅ : TarskiSet.{u})
    · exact (def6 ORDINAL1.empty_isOrdinal hA).2 hA0
    · have := th68 ORDINAL1.empty_isOrdinal hA hA0
      rw [ORDINAL2.th35 hA] at this
      exact this
  refine ⟨hdiv, ?_, ?_⟩
  · rw [def7, hdiv, ORDINAL2.th35 hA,
      (th56 ORDINAL1.empty_isOrdinal).2]
  · rw [def7, (def6 hA ORDINAL1.empty_isOrdinal).2 rfl,
      ORDINAL2.th35 ORDINAL1.empty_isOrdinal, (th56 hA).1]

/-- `ORDINAL3:71` (unlabeled). -/
theorem th71 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ordinalDiv A FUNCT_3.one = A ∧
      ordinalMod A FUNCT_3.one = (∅ : TarskiSet.{u}) := by
  have h0one : (∅ : TarskiSet.{u}) ∈ FUNCT_3.one := by
    rw [lm1]
    exact ORDINAL1.th6 _
  have heq : A = A *ᵒ FUNCT_3.one +ᵒ (∅ : TarskiSet.{u}) := by
    rw [(ORDINAL2.th39 hA).2, ORDINAL2.th27 hA]
  have hu := th66 hA hA one_isOrdinal ORDINAL1.empty_isOrdinal heq h0one
  exact ⟨hu.1.symm, hu.2.symm⟩

/-! ## Addenda and natural ordinals -/

/-- `ORDINAL3:72` (unlabeled addendum). -/
theorem th72 (X : TarskiSet.{u}) :
    ORDINAL2.sup X ⊆ ORDINAL1.succ (TARSKI.union (ORDINAL1.On X)) := by
  apply (ORDINAL2.def3 X).2
    (ORDINAL1.succ (TARSKI.union (ORDINAL1.On X)))
    (ORDINAL1.th17 (th5 X))
  intro A hA
  have hAord := (ORDINAL1.def9 X A).mp hA |>.2
  have hsub : A ⊆ TARSKI.union (ORDINAL1.On X) :=
    ZFMISC_1.th74 hA
  exact (ORDINAL1.th22 hAord (th5 X)).mpr hsub

/-- `ORDINAL3:73` (unlabeled addendum). -/
theorem th73 {A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A) :
    ORDINAL2.isCofinalWith (ORDINAL1.succ A) FUNCT_3.one := by
  let psi := FUNCOP_1.mapsTo FUNCT_3.one A
  have hTS := ORDINAL2.mapsTo_isTSequence FUNCT_3.one A one_isOrdinal
  have hOS : ORDINAL2.isOrdinalSequence psi :=
    ⟨hTS, ORDINAL2.mapsTo_ordinal_yielding FUNCT_3.one A hA⟩
  have hdom : RELAT_1.dom psi = FUNCT_3.one :=
    FUNCOP_1.mapsTo_dom FUNCT_3.one A
  have h0one : (∅ : TarskiSet.{u}) ∈ FUNCT_3.one := by
    rw [lm1]; exact ORDINAL1.th6 _
  have happ : FUNCT_1.apply psi (∅ : TarskiSet.{u}) = A :=
    FUNCOP_1.th7 h0one
  have hArng : A ∈ RELAT_1.rng psi :=
    (FUNCT_1.def3 hOS.1.1.2).mpr
      ⟨(∅ : TarskiSet.{u}),
        Eq.subst (motive := fun s => (∅ : TarskiSet.{u}) ∈ s)
          hdom.symm h0one, happ.symm⟩
  have hrng : RELAT_1.rng psi = TARSKI.singleton A :=
    ordinal_eq (FUNCOP_1.th13 FUNCT_3.one A).2
      (fun x hx => Eq.subst (motive := fun s => s ∈ RELAT_1.rng psi)
        ((singleton_iff A x).mp hx).symm hArng)
  refine ⟨psi, hOS, hdom, ?_, ?_, ?_⟩
  · intro x hx
    have hxA := (singleton_iff A x).mp
      (Eq.subst (motive := fun s => x ∈ s) hrng hx)
    exact Eq.subst (motive := fun s => s ∈ ORDINAL1.succ A)
      hxA.symm (ORDINAL1.th6 A)
  · intro B C hB hC hBC hCd
    have hCone : C ∈ FUNCT_3.one :=
      Eq.subst (motive := fun s => C ∈ s) hdom hCd
    have hC0 := th14 hC hCone
    rw [hC0] at hBC
    exact ((XBOOLE_0.empty_iff B).mp hBC).elim
  · rw [ORDINAL2.def5, hrng, ORDINAL2.th23 hA]

/-- `ORDINAL3:74` (`Th74`). -/
theorem th74 {a b : TarskiSet.{u}}
    (ha : ORDINAL1.isOrdinal a) (hb : ORDINAL1.isOrdinal b)
    (hsum : ORDINAL1.isNatural (a +ᵒ b)) :
    ORDINAL1.isNatural a ∧ ORDINAL1.isNatural b := by
  have hord := ORDINAL1.natural_isOrdinal hsum
  exact ⟨ORDINAL1.th12 ha.1 hord ORDINAL1.def11.1
      (th24 ha hb).1 hsum,
    ORDINAL1.th12 hb.1 hord ORDINAL1.def11.1
      (th24 ha hb).2 hsum⟩

/-- Third registration: subtraction preserves natural ordinals. -/
theorem sub_natural {a b : TarskiSet.{u}}
    (ha : ORDINAL1.isNatural a) (hb : ORDINAL1.isNatural b) :
    ORDINAL1.isNatural (ordinalSub a b) := by
  have hao := ORDINAL1.natural_isOrdinal ha
  have hbo := ORDINAL1.natural_isOrdinal hb
  by_cases hba : b ⊆ a
  · have heq := (def5 hao hbo).1 hba
    exact (th74 hbo (ordinalSub_isOrdinal a b)
      (Eq.subst (motive := ORDINAL1.isNatural) heq ha)).2
  · rw [(def5 hao hbo).2 hba]
    exact ORDINAL1.empty_isNatural

/-- Fourth registration: multiplication preserves natural ordinals. -/
theorem mul_natural {a b : TarskiSet.{u}}
    (ha : ORDINAL1.isNatural a) (hb : ORDINAL1.isNatural b) :
    ORDINAL1.isNatural (a *ᵒ b) := by
  let P := fun n : TarskiSet.{u} => ORDINAL1.isNatural (n *ᵒ b)
  have h0 : P (∅ : TarskiSet.{u}) := by
    simp only [P]
    rw [ORDINAL2.th35 (ORDINAL1.natural_isOrdinal hb)]
    exact ORDINAL1.empty_isNatural
  have hs : ∀ n, ORDINAL1.isNatural n → P n → P (ORDINAL1.succ n) := by
    intro n hn ih
    simp only [P] at ih ⊢
    rw [ORDINAL2.th36 (ORDINAL1.natural_isOrdinal hb)
      (ORDINAL1.natural_isOrdinal hn)]
    exact ORDINAL2.add_natural ih hb
  exact ORDINAL2.sch_OmegaInd ha P h0 hs

/-- `ORDINAL3:75` (unlabeled). -/
theorem th75 {a b : TarskiSet.{u}}
    (ha : ORDINAL1.isOrdinal a) (hb : ORDINAL1.isOrdinal b)
    (hprod : ORDINAL1.isNatural (a *ᵒ b))
    (hne : a *ᵒ b ≠ (∅ : TarskiSet.{u})) :
    ORDINAL1.isNatural a ∧ ORDINAL1.isNatural b := by
  have ha0 : a ≠ (∅ : TarskiSet.{u}) := by
    intro h; rw [h, ORDINAL2.th35 hb] at hne; exact hne rfl
  have hb0 : b ≠ (∅ : TarskiSet.{u}) := by
    intro h; rw [h, ORDINAL2.th38 ha] at hne; exact hne rfl
  have hpord := ORDINAL1.natural_isOrdinal hprod
  exact ⟨ORDINAL1.th12 ha.1 hpord ORDINAL1.def11.1
      (th36 ha hb hb0).1 hprod,
    ORDINAL1.th12 hb.1 hpord ORDINAL1.def11.1
      (th36 hb ha ha0).2 hprod⟩

/-- First natural-ordinal redefinition: addition is commutative. -/
theorem add_comm_natural {a b : TarskiSet.{u}}
    (ha : ORDINAL1.isNatural a) (hb : ORDINAL1.isNatural b) :
    a +ᵒ b = b +ᵒ a := by
  let R := fun n : TarskiSet.{u} => a +ᵒ n = n +ᵒ a
  have h0 : R (∅ : TarskiSet.{u}) := by
    simp only [R]
    rw [ORDINAL2.th27 (ORDINAL1.natural_isOrdinal ha),
      ORDINAL2.th30 (ORDINAL1.natural_isOrdinal ha)]
  have hs : ∀ n, ORDINAL1.isNatural n → R n → R (ORDINAL1.succ n) := by
    intro n hn ih
    simp only [R] at ih ⊢
    rw [ORDINAL2.th28 (ORDINAL1.natural_isOrdinal ha)
      (ORDINAL1.natural_isOrdinal hn), ih]
    let Q := fun m : TarskiSet.{u} =>
      ORDINAL1.succ n +ᵒ m = ORDINAL1.succ (n +ᵒ m)
    have q0 : Q (∅ : TarskiSet.{u}) := by
      simp only [Q]
      rw [ORDINAL2.th27 (ORDINAL1.th17
        (ORDINAL1.natural_isOrdinal hn)),
        ORDINAL2.th27 (ORDINAL1.natural_isOrdinal hn)]
    have qs : ∀ m, ORDINAL1.isNatural m → Q m →
        Q (ORDINAL1.succ m) := by
      intro m hm iq
      simp only [Q] at iq ⊢
      rw [ORDINAL2.th28 (ORDINAL1.th17
        (ORDINAL1.natural_isOrdinal hn))
        (ORDINAL1.natural_isOrdinal hm), iq,
        ORDINAL2.th28 (ORDINAL1.natural_isOrdinal hn)
          (ORDINAL1.natural_isOrdinal hm)]
    exact (ORDINAL2.sch_OmegaInd ha Q q0 qs).symm
  exact ORDINAL2.sch_OmegaInd hb R h0 hs

/-- Second natural-ordinal redefinition: multiplication is commutative. -/
theorem mul_comm_natural {a b : TarskiSet.{u}}
    (ha : ORDINAL1.isNatural a) (hb : ORDINAL1.isNatural b) :
    a *ᵒ b = b *ᵒ a := by
  let R := fun n : TarskiSet.{u} => a *ᵒ n = n *ᵒ a
  have h0 : R (∅ : TarskiSet.{u}) := by
    simp only [R]
    rw [ORDINAL2.th38 (ORDINAL1.natural_isOrdinal ha),
      ORDINAL2.th35 (ORDINAL1.natural_isOrdinal ha)]
  have hs : ∀ n, ORDINAL1.isNatural n → R n → R (ORDINAL1.succ n) := by
    intro n hn ih
    simp only [R] at ih ⊢
    let Q := fun m : TarskiSet.{u} =>
      m *ᵒ ORDINAL1.succ n = m *ᵒ n +ᵒ m
    have q0 : Q (∅ : TarskiSet.{u}) := by
      simp only [Q]
      rw [ORDINAL2.th35 (ORDINAL1.th17
        (ORDINAL1.natural_isOrdinal hn)),
        ORDINAL2.th35 (ORDINAL1.natural_isOrdinal hn),
        ORDINAL2.th27 ORDINAL1.empty_isOrdinal]
    have qs : ∀ m, ORDINAL1.isNatural m → Q m →
        Q (ORDINAL1.succ m) := by
      intro m hm iq
      simp only [Q] at iq ⊢
      calc
        ORDINAL1.succ m *ᵒ ORDINAL1.succ n =
            m *ᵒ ORDINAL1.succ n +ᵒ ORDINAL1.succ n :=
          ORDINAL2.th36 (ORDINAL1.th17
            (ORDINAL1.natural_isOrdinal hn))
            (ORDINAL1.natural_isOrdinal hm)
        _ = (m *ᵒ n +ᵒ m) +ᵒ ORDINAL1.succ n :=
          congrArg (fun s => s +ᵒ ORDINAL1.succ n) iq
        _ = m *ᵒ n +ᵒ (m +ᵒ ORDINAL1.succ n) :=
          th30 (ORDINAL2.ordinalMul_isOrdinal m n)
            (ORDINAL1.natural_isOrdinal hm)
            (ORDINAL1.th17 (ORDINAL1.natural_isOrdinal hn))
        _ = m *ᵒ n +ᵒ ORDINAL1.succ (m +ᵒ n) := by
          rw [ORDINAL2.th28 (ORDINAL1.natural_isOrdinal hm)
            (ORDINAL1.natural_isOrdinal hn)]
        _ = ORDINAL1.succ (m *ᵒ n +ᵒ (m +ᵒ n)) :=
          ORDINAL2.th28 (ORDINAL2.ordinalMul_isOrdinal m n)
            (ORDINAL1.natural_isOrdinal
              (ORDINAL2.add_natural hm hn))
        _ = ORDINAL1.succ ((m *ᵒ n +ᵒ n) +ᵒ m) := by
          congr 1
          rw [add_comm_natural hm hn,
            ← th30 (ORDINAL2.ordinalMul_isOrdinal m n)
              (ORDINAL1.natural_isOrdinal hn)
              (ORDINAL1.natural_isOrdinal hm)]
        _ = ORDINAL1.succ (ORDINAL1.succ m *ᵒ n +ᵒ m) := by
          rw [ORDINAL2.th36 (ORDINAL1.natural_isOrdinal hn)
            (ORDINAL1.natural_isOrdinal hm)]
        _ = ORDINAL1.succ m *ᵒ n +ᵒ ORDINAL1.succ m :=
          (ORDINAL2.th28
            (ORDINAL2.ordinalMul_isOrdinal (ORDINAL1.succ m) n)
            (ORDINAL1.natural_isOrdinal hm)).symm
    have hQa := ORDINAL2.sch_OmegaInd ha Q q0 qs
    rw [hQa, ih, ORDINAL2.th36 (ORDINAL1.natural_isOrdinal ha)
      (ORDINAL1.natural_isOrdinal hn)]
  exact ORDINAL2.sch_OmegaInd hb R h0 hs

end ORDINAL3
