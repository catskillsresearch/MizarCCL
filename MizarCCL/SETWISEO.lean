import MizarCCL.FINSUB_1
import MizarCCL.FUNCOP_1

/-
Copyright (c) 1990-2012 Association of Mizar Users.
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `vendor/mml/setwiseo.miz`.
Authors: Andrzej Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Semilattice Operations on Finite Subsets

Faithful 1–1 Lean rendering of Mizar article `SETWISEO` (queue index 34).
Absolute theorem slots 3--5 are canceled in the source; the declarations
below therefore preserve `th1`, `th2`, and `th6` through `th59`.
-/

universe u

open TarskiSet TARSKI XBOOLE_0

namespace SETWISEO

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  TARSKI.extensionality h

private theorem subset_refl (A : TarskiSet.{u}) : A ⊆ A := fun _ h => h

/-! ## Auxiliary theorems -/

/-- `SETWISEO:1` (`Th1`). -/
theorem th1 (x y z : TarskiSet.{u}) :
    TARSKI.singleton x ⊆ ENUMSET1.enumset3 x y z := by
  intro a ha
  exact (ENUMSET1.def1 x y z a).mpr (Or.inl ((singleton_iff x a).mp ha))

/-- `SETWISEO:2` (`Th2`). -/
theorem th2 (x y z : TarskiSet.{u}) :
    TARSKI.upair x y ⊆ ENUMSET1.enumset3 x y z := by
  intro a ha
  rcases (upair_iff x y a).mp ha with h | h
  · exact (ENUMSET1.def1 x y z a).mpr (Or.inl h)
  · exact (ENUMSET1.def1 x y z a).mpr (Or.inr (Or.inl h))

/- The source explicitly cancels absolute theorem slots 3, 4, and 5. -/

/-- `SETWISEO:6` (`Th6`). -/
theorem th6 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    RELAT_1.image f (Y \ RELAT_1.invimage f X) =
      RELAT_1.image f Y \ X := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    obtain ⟨z, hp, hz⟩ := (RELAT_1.def13 f _ a).mp ha
    have hzY := (XBOOLE_0.def5 Y (RELAT_1.invimage f X) z).mp hz
    apply (XBOOLE_0.def5 (RELAT_1.image f Y) X a).mpr
    refine ⟨(RELAT_1.def13 f Y a).mpr ⟨z, hp, hzY.1⟩, ?_⟩
    intro haX
    exact hzY.2 ((RELAT_1.def14 f X z).mpr ⟨a, hp, haX⟩)
  · intro ha
    have ha' := (XBOOLE_0.def5 (RELAT_1.image f Y) X a).mp ha
    obtain ⟨z, hp, hzY⟩ := (RELAT_1.def13 f Y a).mp ha'.1
    apply (RELAT_1.def13 f _ a).mpr
    refine ⟨z, hp, (XBOOLE_0.def5 Y (RELAT_1.invimage f X) z).mpr
      ⟨hzY, ?_⟩⟩
    intro hz
    obtain ⟨w, hpw, hwX⟩ := (RELAT_1.def14 f X z).mp hz
    exact ha'.2 (Eq.subst (motive := fun s => s ∈ X)
      (hf.2 z a w hp hpw).symm hwX)

/-- `SETWISEO:7` (`Th7`). -/
private theorem th7_aux {X Y f x : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f X Y) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ X) :
    x ∈ RELAT_1.invimage f (TARSKI.singleton (FUNCT_1.apply f x)) := by
  exact (FUNCT_2.th38 hf hY).mpr
    ⟨hx, (singleton_iff _ _).mpr rfl⟩

/-- `SETWISEO:8` (`Th8`). -/
private theorem th8_aux {X Y f x : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f X Y) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ X) :
    RELAT_1.Im f x = TARSKI.singleton (FUNCT_1.apply f x) :=
  FUNCT_1.th59 (FUNCT_2.functionOf_isFunction hf).2
    (FUNCT_2.functionOf_dom_eq hf hY ▸ hx)

/-- `SETWISEO:9` (`Th9`). -/
private theorem th9_aux {X B x : TarskiSet.{u}} (hB : B ∈ FINSUB_1.Fin X)
    (hx : x ∈ B) : x ∈ X :=
  (FINSUB_1.def5 X B).mp hB |>.1 x hx

/-- Absolute slot 10. -/
private theorem th10_aux {X Y A B f : TarskiSet.{u}}
    (_hA : A ∈ FINSUB_1.Fin X)
    (hf : FUNCT_2.isFunctionOf f X Y)
    (hmap : ∀ x, x ∈ A → FUNCT_1.apply f x ∈ B) :
    RELAT_1.image f A ⊆ B := by
  intro y hy
  obtain ⟨x, _, hxA, heq⟩ := FUNCT_2.th65 hf hy
  exact heq ▸ hmap x hxA

/-- `SETWISEO:11` (`Th11`). -/
theorem th11 {X A B : TarskiSet.{u}} (hB : B ∈ FINSUB_1.Fin X)
    (hAB : A ⊆ B) : A ∈ FINSUB_1.Fin X := by
  have hb := (FINSUB_1.def5 X B).mp hB
  exact (FINSUB_1.def5 X A).mpr
    ⟨XBOOLE_1.th1 hAB hb.1, FINSET_1.subset_isFinite hAB hb.2⟩

/-- `SETWISEO:Lm1`: finite images are finite subsets of the codomain. -/
private theorem lm1_aux {X Y A f : TarskiSet.{u}} (hA : A ∈ FINSUB_1.Fin X)
    (hf : FUNCT_2.isFunctionOf f X Y) :
    RELAT_1.image f A ∈ FINSUB_1.Fin Y := by
  apply (FINSUB_1.def5 Y _).mpr
  refine ⟨?_, FINSET_1.image_isFinite
    (FUNCT_2.functionOf_isFunction hf) ((FINSUB_1.def5 X A).mp hA).2⟩
  exact XBOOLE_1.th1 RELAT_1.th111 (FUNCT_2.functionOf_rng_sub hf)

/-- `SETWISEO:12` (`Th12`). -/
private theorem th12_aux {X B : TarskiSet.{u}} (hB : B ∈ FINSUB_1.Fin X)
    (hne : B ≠ (∅ : TarskiSet.{u})) :
    ∃ x, x ∈ X ∧ x ∈ B := by
  obtain ⟨x, hx⟩ := XBOOLE_0.th7 hne
  exact ⟨x, th9_aux hB hx, hx⟩

/-- `SETWISEO:13` (`Th13`). -/
private theorem th13_aux {X Y A f : TarskiSet.{u}}
    (hA : A ∈ FINSUB_1.Fin X) (hf : FUNCT_2.isFunctionOf f X Y)
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (he : RELAT_1.image f A = (∅ : TarskiSet.{u})) :
    A = (∅ : TarskiSet.{u}) := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨x, hx⟩ := XBOOLE_0.th7 hne
  have hfx : FUNCT_1.apply f x ∈ RELAT_1.image f A :=
    FUNCT_2.th35 hf hY ⟨x, th9_aux hA hx, hx, rfl⟩
  exact (XBOOLE_0.empty_iff _).mp (he ▸ hfx)

theorem th7 {X Y f x : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X Y) (hx : x ∈ X) :
    x ∈ RELAT_1.invimage f (TARSKI.singleton (FUNCT_1.apply f x)) :=
  th7_aux hf hY hx

theorem th8 {X Y f x : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X Y) (hx : x ∈ X) :
    RELAT_1.Im f x = TARSKI.singleton (FUNCT_1.apply f x) :=
  th8_aux hf hY hx

theorem th9 {X B x : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hx : x ∈ B) : x ∈ X :=
  th9_aux hB hx

theorem th10 {X Y A B f : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (_hY : Y ≠ (∅ : TarskiSet.{u}))
    (hA : A ∈ FINSUB_1.Fin X) (hf : FUNCT_2.isFunctionOf f X Y)
    (hmap : ∀ x, x ∈ A → FUNCT_1.apply f x ∈ B) :
    RELAT_1.image f A ⊆ B :=
  th10_aux hA hf hmap

theorem lm1 {X Y A f : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (_hY : Y ≠ (∅ : TarskiSet.{u}))
    (hA : A ∈ FINSUB_1.Fin X) (hf : FUNCT_2.isFunctionOf f X Y) :
    RELAT_1.image f A ∈ FINSUB_1.Fin Y :=
  lm1_aux hA hf

theorem th12 {X B : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hne : B ≠ (∅ : TarskiSet.{u})) :
    ∃ x, x ∈ X ∧ x ∈ B :=
  th12_aux hB hne

theorem th13 {X Y A f : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (_hY : Y ≠ (∅ : TarskiSet.{u}))
    (hA : A ∈ FINSUB_1.Fin X) (hf : FUNCT_2.isFunctionOf f X Y)
    (he : RELAT_1.image f A = (∅ : TarskiSet.{u})) :
    A = (∅ : TarskiSet.{u}) :=
  th13_aux hA hf _hY he

/-! ## Empty finite subset and finite-subset schemes -/

/-- Registration: the empty finite subset. -/
theorem empty_mem_Fin (X : TarskiSet.{u}) :
    (∅ : TarskiSet.{u}) ∈ FINSUB_1.Fin X :=
  (FINSUB_1.def5 X ∅).mpr
    ⟨XBOOLE_1.th2, FINSET_1.empty_isFinite⟩

/-- `SETWISEO:def 1`: `{}.X`. -/
noncomputable def emptyFin (_X : TarskiSet.{u}) : TarskiSet.{u} := ∅

theorem def1 (X : TarskiSet.{u}) : emptyFin X = (∅ : TarskiSet.{u}) := rfl

/-- `SETWISEO:sch FinSubFuncEx`. -/
theorem FinSubFuncEx {A B : TarskiSet.{u}} (_hA : A ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin A)
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop) :
    ∃ f, FUNCT_2.isFunctionOf f A (FINSUB_1.Fin A) ∧
      ∀ b a, b ∈ A → a ∈ A →
        (a ∈ FUNCT_1.apply f b ↔ a ∈ B ∧ P a b) := by
  have hFin : FINSUB_1.Fin A ≠ (∅ : TarskiSet.{u}) :=
    FINSUB_1.Fin_nonempty A
  let Q := fun b a : TarskiSet.{u} => a ∈ B ∧ P a b
  have hex : ∀ b, b ∈ A → ∃ y, y ∈ FINSUB_1.Fin A ∧
      ∀ a, a ∈ A → (a ∈ y ↔ Q b a) := by
    intro b hb
    obtain ⟨y, hy⟩ := XBOOLE_0.sch_separation B (fun a => P a b)
    refine ⟨y, (FINSUB_1.def5 A y).mpr ⟨?_,
      FINSET_1.subset_isFinite (fun a ha => (hy a).mp ha |>.1)
        ((FINSUB_1.def5 A B).mp hB).2⟩, ?_⟩
    · intro a ha
      exact (FINSUB_1.def5 A B).mp hB |>.1 a ((hy a).mp ha).1
    · intro a _
      exact hy a
  obtain ⟨f, hf, hv⟩ := FUNCT_2.sch_FuncEx1 A (FINSUB_1.Fin A)
    (fun b y => ∀ a, a ∈ A → (a ∈ y ↔ Q b a))
    (fun b hb => hex b hb)
  exact ⟨f, hf, fun b a hb ha => hv b hb a ha⟩

/-- `SETWISEO:def 2`: a binary operation has a unity. -/
def isHavingAUnity (F Y : TarskiSet.{u}) : Prop :=
  ∃ e, SUBSET_1.isElement e Y ∧ BINOP_1.is_a_unity_wrt e F Y

theorem def2 (F Y : TarskiSet.{u}) (_hY : Y ≠ (∅ : TarskiSet.{u}))
    (_hF : BINOP_1.isBinOp F Y) :
    isHavingAUnity F Y ↔
      ∃ e, SUBSET_1.isElement e Y ∧ BINOP_1.is_a_unity_wrt e F Y :=
  Iff.rfl

/-- Totalized Mizar `the_unity_wrt`; outside the defining guard it is empty. -/
noncomputable def unity (F Y : TarskiSet.{u}) : TarskiSet.{u} :=
  by
    classical
    exact if h : isHavingAUnity F Y then BINOP_1.the_unity_wrt h
      else SUBSET_1.choose Y

private theorem unity_isElement_total (F Y : TarskiSet.{u}) :
    SUBSET_1.isElement (unity F Y) Y := by
  classical
  by_cases h : isHavingAUnity F Y
  · rw [unity, dif_pos h]
    exact BINOP_1.the_unity_wrt_isElement h
  · rw [unity, dif_neg h]
    exact SUBSET_1.choose_isElement Y

theorem unity_isElement {F Y : TarskiSet.{u}} (h : isHavingAUnity F Y) :
    SUBSET_1.isElement (unity F Y) Y := by
  rw [unity, dif_pos h]
  exact BINOP_1.the_unity_wrt_isElement h

theorem unity_spec {F Y : TarskiSet.{u}} (h : isHavingAUnity F Y) :
    BINOP_1.is_a_unity_wrt (unity F Y) F Y := by
  rw [unity, dif_pos h]
  exact BINOP_1.def8 h

/-- `SETWISEO:14` (`Th14`). -/
private theorem havingUnity_iff {F Y : TarskiSet.{u}} :
    isHavingAUnity F Y ↔
      BINOP_1.is_a_unity_wrt (unity F Y) F Y ∧
        SUBSET_1.isElement (unity F Y) Y := by
  constructor
  · intro h; exact ⟨unity_spec h, unity_isElement h⟩
  · rintro ⟨hu, he⟩; exact ⟨unity F Y, he, hu⟩

/-- `SETWISEO:14` (`Th14`). -/
theorem th14 {F Y : TarskiSet.{u}} (_hY : Y ≠ (∅ : TarskiSet.{u}))
    (_hF : BINOP_1.isBinOp F Y) :
    isHavingAUnity F Y ↔
      BINOP_1.is_a_unity_wrt (unity F Y) F Y := by
  constructor
  · exact unity_spec
  · intro h
    exact ⟨unity F Y, unity_isElement_total F Y, h⟩

private theorem th15_aux {F Y : TarskiSet.{u}} (h : isHavingAUnity F Y) :
    ∀ x, SUBSET_1.isElement x Y →
      BINOP_1.apply2 F (unity F Y) x = x ∧
      BINOP_1.apply2 F x (unity F Y) = x :=
  BINOP_1.th3.mp (unity_spec h)

theorem th15 {F Y : TarskiSet.{u}} (_hY : Y ≠ (∅ : TarskiSet.{u}))
    (_hF : BINOP_1.isBinOp F Y) (h : isHavingAUnity F Y) :
    ∀ x, SUBSET_1.isElement x Y →
      BINOP_1.apply2 F (unity F Y) x = x ∧
      BINOP_1.apply2 F x (unity F Y) = x :=
  th15_aux h

/-- Singletons, unordered pairs, and triples are finite subsets. -/
private theorem singleton_mem_Fin_aux {X x : TarskiSet.{u}} (hx : x ∈ X) :
    TARSKI.singleton x ∈ FINSUB_1.Fin X :=
  (FINSUB_1.def5 X _).mpr
    ⟨(ZFMISC_1.th31).2 hx, FINSET_1.singleton_isFinite x⟩

private theorem upair_mem_Fin_aux {X x y : TarskiSet.{u}} (hx : x ∈ X) (hy : y ∈ X) :
    TARSKI.upair x y ∈ FINSUB_1.Fin X :=
  (FINSUB_1.def5 X _).mpr
    ⟨(ZFMISC_1.th32).2 ⟨hx, hy⟩, FINSET_1.upair_isFinite x y⟩

private theorem enumset3_mem_Fin_aux {X x y z : TarskiSet.{u}}
    (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X) :
    ENUMSET1.enumset3 x y z ∈ FINSUB_1.Fin X :=
  (FINSUB_1.def5 X _).mpr
    ⟨fun a ha => by
        rcases (ENUMSET1.def1 x y z a).mp ha with h | h | h
        · exact h ▸ hx
        · exact h ▸ hy
        · exact h ▸ hz,
      FINSET_1.enumset3_isFinite x y z⟩

theorem singleton_mem_Fin {X x : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hx : x ∈ X) :
    TARSKI.singleton x ∈ FINSUB_1.Fin X :=
  singleton_mem_Fin_aux hx

theorem upair_mem_Fin {X x y : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hx : x ∈ X) (hy : y ∈ X) :
    TARSKI.upair x y ∈ FINSUB_1.Fin X :=
  upair_mem_Fin_aux hx hy

theorem enumset3_mem_Fin {X x y z : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X) :
    ENUMSET1.enumset3 x y z ∈ FINSUB_1.Fin X :=
  enumset3_mem_Fin_aux hx hy hz

theorem union_mem_Fin {X A B : TarskiSet.{u}}
    (hA : A ∈ FINSUB_1.Fin X) (hB : B ∈ FINSUB_1.Fin X) :
    A ∪ B ∈ FINSUB_1.Fin X :=
  (FINSUB_1.def5 X _).mpr
    ⟨XBOOLE_1.th8 ((FINSUB_1.def5 X A).mp hA).1
      ((FINSUB_1.def5 X B).mp hB).1,
      FINSET_1.union_isFinite ((FINSUB_1.def5 X A).mp hA).2
        ((FINSUB_1.def5 X B).mp hB).2⟩

theorem diff_mem_Fin {X A B : TarskiSet.{u}}
    (hA : A ∈ FINSUB_1.Fin X) :
    A \ B ∈ FINSUB_1.Fin X :=
  (FINSUB_1.def5 X _).mpr
    ⟨fun x hx => (FINSUB_1.def5 X A).mp hA |>.1 x
      ((XBOOLE_0.def5 A B x).mp hx).1,
      FINSET_1.diff_isFinite ((FINSUB_1.def5 X A).mp hA).2⟩

/-- `SETWISEO:sch FinSubInd1`. -/
theorem FinSubInd1 {X : TarskiSet.{u}} (_hX : X ≠ (∅ : TarskiSet.{u}))
    (P : TarskiSet.{u} → Prop)
    (h0 : P (emptyFin X))
    (hs : ∀ B b, B ∈ FINSUB_1.Fin X → b ∈ X → P B → b ∉ B →
      P (B ∪ TARSKI.singleton b)) :
    ∀ B, B ∈ FINSUB_1.Fin X → P B := by
  intro B hB
  apply FINSET_1.sch_Finite (A := B) P ((FINSUB_1.def5 X B).mp hB).2
  · exact h0
  · intro x A hxB hAB ih
    have hxX := th9_aux hB hxB
    by_cases hxA : x ∈ A
    · have he : A ∪ TARSKI.singleton x = A :=
        XBOOLE_0.union_comm _ _ ▸ XBOOLE_1.th12 (ZFMISC_1.th31.mpr hxA)
      rw [he]
      exact ih
    · exact hs A x (th11 hB hAB) hxX ih hxA

/-- `SETWISEO:sch FinSubInd2`. -/
theorem FinSubInd2 {X : TarskiSet.{u}} (hX : X ≠ (∅ : TarskiSet.{u}))
    (P : TarskiSet.{u} → Prop)
    (h1 : ∀ x, x ∈ X → P (TARSKI.singleton x))
    (hu : ∀ B₁ B₂, B₁ ∈ FINSUB_1.Fin X → B₂ ∈ FINSUB_1.Fin X →
      B₁ ≠ (∅ : TarskiSet.{u}) → B₂ ≠ (∅ : TarskiSet.{u}) →
      P B₁ → P B₂ → P (B₁ ∪ B₂)) :
    ∀ B, B ∈ FINSUB_1.Fin X → B ≠ (∅ : TarskiSet.{u}) → P B := by
  intro B hB
  exact FinSubInd1 hX
    (fun C => C ≠ (∅ : TarskiSet.{u}) → P C)
    (fun h => (h rfl).elim)
    (by
      intro C x hC hx ih hxC hne
      by_cases hC0 : C = (∅ : TarskiSet.{u})
      · rw [hC0, XBOOLE_1.th12 (X := (∅ : TarskiSet.{u}))
          (Y := TARSKI.singleton x) XBOOLE_1.th2]
        exact h1 x hx
      · exact hu C (TARSKI.singleton x) hC (singleton_mem_Fin_aux hx)
          hC0 (fun he => (XBOOLE_0.empty_iff x).mp
            (he ▸ (singleton_iff x x).mpr rfl)) (ih hC0) (h1 x hx))
    B hB

/-- `SETWISEO:sch FinSubInd3`. -/
theorem FinSubInd3 {X : TarskiSet.{u}} (hX : X ≠ (∅ : TarskiSet.{u}))
    (P : TarskiSet.{u} → Prop)
    (h0 : P (emptyFin X))
    (hs : ∀ B b, B ∈ FINSUB_1.Fin X → b ∈ X → P B →
      P (B ∪ TARSKI.singleton b)) :
    ∀ B, B ∈ FINSUB_1.Fin X → P B :=
  FinSubInd1 hX P h0 (fun B b hB hb hP _ => hs B b hB hb hP)

/-! ## The finite setwise operation

The implementation below uses a duplicate-free list representing the finite
set.  Folding takes place in `Option {y // y ∈ Y}`; `none` is the formal
identity.  This is the usual free adjunction of a unity to a semigroup and
allows the Mizar operation to cover both the nonempty and unity cases.
-/

private theorem finite_has_nodup_list {B : TarskiSet.{u}}
    (hB : FINSET_1.isFinite B) :
    ∃ xs : List TarskiSet.{u}, xs.Nodup ∧
      ∀ x, x ∈ xs ↔ x ∈ B := by
  let P := fun C : TarskiSet.{u} =>
    ∃ xs : List TarskiSet.{u}, xs.Nodup ∧ ∀ x, x ∈ xs ↔ x ∈ C
  apply FINSET_1.sch_Finite (A := B) P hB
  · exact ⟨[], List.nodup_nil, fun x => by
      simp only [List.not_mem_nil, XBOOLE_0.empty_iff]⟩
  · intro x C _ _ ih
    obtain ⟨xs, hnd, hmem⟩ := ih
    by_cases hx : x ∈ C
    · refine ⟨xs, hnd, fun z => (hmem z).trans ?_⟩
      constructor
      · intro hz
        exact (XBOOLE_0.def3 C (TARSKI.singleton x) z).mpr (Or.inl hz)
      · intro hz
        rcases (XBOOLE_0.def3 C (TARSKI.singleton x) z).mp hz with h | h
        · exact h
        · exact (singleton_iff x z).mp h ▸ hx
    · refine ⟨x :: xs, List.nodup_cons.mpr
        ⟨fun h => hx ((hmem x).mp h), hnd⟩, ?_⟩
      intro z
      simp only [List.mem_cons, hmem, XBOOLE_0.def3, singleton_iff]
      exact or_comm

private noncomputable def elems (B : TarskiSet.{u})
    (hB : FINSET_1.isFinite B) : List TarskiSet.{u} :=
  Classical.choose (finite_has_nodup_list hB)

private theorem elems_nodup (B : TarskiSet.{u})
    (hB : FINSET_1.isFinite B) : (elems B hB).Nodup :=
  (Classical.choose_spec (finite_has_nodup_list hB)).1

private theorem mem_elems {B x : TarskiSet.{u}}
    (hB : FINSET_1.isFinite B) : x ∈ elems B hB ↔ x ∈ B :=
  (Classical.choose_spec (finite_has_nodup_list hB)).2 x

private theorem nodup_ext_perm {xs ys : List TarskiSet.{u}}
    (hx : xs.Nodup) (hy : ys.Nodup)
    (hm : ∀ z, z ∈ xs ↔ z ∈ ys) : xs.Perm ys := by
  classical
  apply List.perm_iff_count.mpr
  intro z
  rw [hx.count, hy.count]
  simp only [hm z]

private noncomputable def optMul (F Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F Y) :
    Option {y : TarskiSet.{u} // y ∈ Y} →
      Option {y : TarskiSet.{u} // y ∈ Y} →
      Option {y : TarskiSet.{u} // y ∈ Y}
  | none, b => b
  | a, none => a
  | some a, some b =>
      some ⟨BINOP_1.apply2 F a.1 b.1,
        SUBSET_1.isElement_mem
          (fun he => hY (XBOOLE_0.empty_eq he))
          (BINOP_1.apply2_binop_isElement hF
            (SUBSET_1.isElement_of a.2) (SUBSET_1.isElement_of b.2))⟩

private noncomputable def defaultElement (Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u})) : TarskiSet.{u} :=
  Classical.choose (XBOOLE_0.th7 hY)

private theorem defaultElement_mem (Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u})) : defaultElement Y hY ∈ Y :=
  Classical.choose_spec (XBOOLE_0.th7 hY)

private noncomputable def norm (Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u})) (x : TarskiSet.{u}) : TarskiSet.{u} :=
  by
    classical
    exact if x ∈ Y then x else defaultElement Y hY

private theorem norm_mem (Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u})) (x : TarskiSet.{u}) :
    norm Y hY x ∈ Y := by
  classical
  by_cases hx : x ∈ Y
  · rw [norm, if_pos hx]; exact hx
  · rw [norm, if_neg hx]; exact defaultElement_mem Y hY

private theorem norm_eq {Y x : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hx : x ∈ Y) :
    norm Y hY x = x := by
  classical
  rw [norm, if_pos hx]

private noncomputable def mul (F Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u})) (x y : TarskiSet.{u}) : TarskiSet.{u} :=
  BINOP_1.apply2 F (norm Y hY x) (norm Y hY y)

private theorem mul_mem {F Y : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F Y)
    (x y : TarskiSet.{u}) : mul F Y hY x y ∈ Y :=
  SUBSET_1.isElement_mem
    (fun he => hY (XBOOLE_0.empty_eq he))
    (BINOP_1.apply2_binop_isElement hF
      (SUBSET_1.isElement_of (norm_mem Y hY x))
      (SUBSET_1.isElement_of (norm_mem Y hY y)))

private theorem mul_eq {F Y x y : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hx : x ∈ Y) (hy : y ∈ Y) :
    mul F Y hY x y = BINOP_1.apply2 F x y := by
  simp only [mul, norm_eq hY hx, norm_eq hY hy]

private theorem mul_comm {F Y : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hc : BINOP_1.isCommutative F Y) (x y : TarskiSet.{u}) :
    mul F Y hY x y = mul F Y hY y x :=
  hc _ _ (SUBSET_1.isElement_of (norm_mem Y hY x))
    (SUBSET_1.isElement_of (norm_mem Y hY y))

private theorem mul_assoc {F Y : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F Y)
    (ha : BINOP_1.isAssociative F Y) (x y z : TarskiSet.{u}) :
    mul F Y hY x (mul F Y hY y z) =
      mul F Y hY (mul F Y hY x y) z := by
  change BINOP_1.apply2 F (norm Y hY x)
      (norm Y hY (mul F Y hY y z)) =
    BINOP_1.apply2 F (norm Y hY (mul F Y hY x y))
      (norm Y hY z)
  rw [norm_eq hY (mul_mem hY hF y z),
    norm_eq hY (mul_mem hY hF x y)]
  exact ha _ _ _
    (SUBSET_1.isElement_of (norm_mem Y hY x))
    (SUBSET_1.isElement_of (norm_mem Y hY y))
    (SUBSET_1.isElement_of (norm_mem Y hY z))

private noncomputable def optMulRaw (F Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u})) :
    Option TarskiSet.{u} → Option TarskiSet.{u} → Option TarskiSet.{u}
  | none, b => b
  | a, none => a
  | some a, some b => some (mul F Y hY a b)

private theorem optMulRaw_interchange {F Y : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F Y)
    (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y)
    (x y : TarskiSet.{u}) (z : Option TarskiSet.{u}) :
    optMulRaw F Y hY (some y)
        (optMulRaw F Y hY (some x) z) =
      optMulRaw F Y hY (some x)
        (optMulRaw F Y hY (some y) z) := by
  cases z with
  | none =>
      simp only [optMulRaw]
      exact congrArg some (mul_comm hY hc y x)
  | some z =>
      simp only [optMulRaw]
      apply congrArg some
      calc
        mul F Y hY y (mul F Y hY x z) =
            mul F Y hY (mul F Y hY y x) z :=
          mul_assoc hY hF ha y x z
        _ = mul F Y hY (mul F Y hY x y) z := by
          rw [mul_comm hY hc y x]
        _ = mul F Y hY x (mul F Y hY y z) :=
          (mul_assoc hY hF ha x y z).symm

private noncomputable def foldValues (F Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u})) (f : TarskiSet.{u})
    (xs : List TarskiSet.{u}) : Option TarskiSet.{u} :=
  (xs.map (fun x => some (FUNCT_1.apply f x))).foldr
    (optMulRaw F Y hY) none

private theorem foldValues_perm {F Y f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F Y)
    (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y)
    {xs ys : List TarskiSet.{u}} (hp : xs.Perm ys) :
    foldValues F Y hY f xs = foldValues F Y hY f ys := by
  unfold foldValues
  apply (hp.map (fun x => some (FUNCT_1.apply f x))).foldr_eq'
  intro x _ y _ z
  cases x with
  | none => rfl
  | some x =>
      cases y with
      | none => rfl
      | some y => exact optMulRaw_interchange hY hF hc ha x y z

private noncomputable def finishFold (F Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u})) : Option TarskiSet.{u} → TarskiSet.{u}
  | some y => y
  | none => by
      classical
      exact if h : isHavingAUnity F Y then unity F Y else defaultElement Y hY

private theorem finishFold_none_of_unity {F Y : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hu : isHavingAUnity F Y) :
    finishFold F Y hY none = unity F Y := by
  unfold finishFold
  exact dif_pos hu

/-- `SETWISEO:def 3`: `F $$ (B,f)`. -/
noncomputable def setwiseFold (F B f X Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) : TarskiSet.{u} :=
  finishFold F Y hY
    (foldValues F Y hY f
      (elems B ((FINSUB_1.def5 X B).mp hB).2))

private theorem setwiseFold_raw (F B f X Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) :
    setwiseFold F B f X Y hY hB =
      finishFold F Y hY
        (foldValues F Y hY f
          (elems B ((FINSUB_1.def5 X B).mp hB).2)) :=
  rfl

private theorem optMulRaw_comm {F Y : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hc : BINOP_1.isCommutative F Y)
    (a b : Option TarskiSet.{u}) :
    optMulRaw F Y hY a b = optMulRaw F Y hY b a := by
  cases a <;> cases b
  · rfl
  · rfl
  · rfl
  · simp only [optMulRaw]
    exact congrArg some (mul_comm hY hc _ _)

private theorem optMulRaw_assoc {F Y : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F Y)
    (ha : BINOP_1.isAssociative F Y)
    (a b c : Option TarskiSet.{u}) :
    optMulRaw F Y hY a (optMulRaw F Y hY b c) =
      optMulRaw F Y hY (optMulRaw F Y hY a b) c := by
  cases a <;> cases b <;> cases c <;> try rfl
  simp only [optMulRaw]
  exact congrArg some (mul_assoc hY hF ha _ _ _)

private theorem optMulRaw_idem {F Y x : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hi : BINOP_1.isIdempotent F Y) (hx : x ∈ Y) :
    optMulRaw F Y hY (some x) (some x) = some x := by
  simp only [optMulRaw]
  apply congrArg some
  rw [mul_eq hY hx hx]
  exact hi x (SUBSET_1.isElement_of hx)

private theorem foldValues_cons (F Y f x : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u})) (xs : List TarskiSet.{u}) :
    foldValues F Y hY f (x :: xs) =
      optMulRaw F Y hY (some (FUNCT_1.apply f x))
        (foldValues F Y hY f xs) :=
  rfl

private theorem foldValues_absorb {F X Y f x : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F Y)
    (hf : FUNCT_2.isFunctionOf f X Y)
    (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y)
    (hi : BINOP_1.isIdempotent F Y)
    {xs : List TarskiSet.{u}}
    (hxs : ∀ z, z ∈ xs → z ∈ X) (hx : x ∈ X) (hmem : x ∈ xs) :
    foldValues F Y hY f (x :: xs) = foldValues F Y hY f xs := by
  have hfx : FUNCT_1.apply f x ∈ Y :=
    FUNCT_2.th5 hf hY hx
  induction xs with
  | nil => exact (List.not_mem_nil hmem).elim
  | cons a xs ih =>
      rw [foldValues_cons, foldValues_cons]
      rcases List.mem_cons.mp hmem with hxa | hxt
      · subst a
        rw [optMulRaw_assoc hY hF ha]
        rw [optMulRaw_idem hY hi hfx]
      · have haX := hxs a List.mem_cons_self
        have htail : ∀ z, z ∈ xs → z ∈ X :=
          fun z hz => hxs z (List.mem_cons.mpr (Or.inr hz))
        have ih' := ih htail hxt
        calc
          optMulRaw F Y hY (some (FUNCT_1.apply f x))
              (optMulRaw F Y hY (some (FUNCT_1.apply f a))
                (foldValues F Y hY f xs)) =
            optMulRaw F Y hY (some (FUNCT_1.apply f a))
              (optMulRaw F Y hY (some (FUNCT_1.apply f x))
                (foldValues F Y hY f xs)) :=
              optMulRaw_interchange hY hF hc ha _ _ _
          _ = optMulRaw F Y hY (some (FUNCT_1.apply f a))
                (foldValues F Y hY f xs) :=
            congrArg (optMulRaw F Y hY (some (FUNCT_1.apply f a))) ih'

private noncomputable def support : List TarskiSet.{u} → List TarskiSet.{u}
  | [] => []
  | x :: xs => by
      classical
      exact if x ∈ xs then support xs else x :: support xs

private theorem support_mem (x : TarskiSet.{u}) :
    ∀ xs : List TarskiSet.{u}, x ∈ support xs ↔ x ∈ xs := by
  classical
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases ha : a ∈ xs
      · rw [support, if_pos ha, ih]
        constructor
        · exact fun h => List.mem_cons.mpr (Or.inr h)
        · intro h
          rcases List.mem_cons.mp h with h | h
          · exact h ▸ ha
          · exact h
      · rw [support, if_neg ha]
        simp only [List.mem_cons, ih]

private theorem support_nodup :
    ∀ xs : List TarskiSet.{u}, (support xs).Nodup := by
  classical
  intro xs
  induction xs with
  | nil => exact List.nodup_nil
  | cons a xs ih =>
      by_cases ha : a ∈ xs
      · rw [support, if_pos ha]; exact ih
      · rw [support, if_neg ha]
        exact List.nodup_cons.mpr
          ⟨fun h => ha ((support_mem a xs).mp h), ih⟩

private theorem foldValues_support {F X Y f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y)
    (hi : BINOP_1.isIdempotent F Y) :
    ∀ xs : List TarskiSet.{u}, (∀ z, z ∈ xs → z ∈ X) →
      foldValues F Y hY f (support xs) = foldValues F Y hY f xs := by
  classical
  intro xs hxs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hxX := hxs x List.mem_cons_self
      have ht : ∀ z, z ∈ xs → z ∈ X :=
        fun z hz => hxs z (List.mem_cons.mpr (Or.inr hz))
      by_cases hx : x ∈ xs
      · rw [support, if_pos hx, ih ht]
        exact (foldValues_absorb hY hF hf hc ha hi ht hxX hx).symm
      · rw [support, if_neg hx, foldValues_cons, ih ht, foldValues_cons]

private theorem foldValues_ext {F X Y f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y)
    (hi : BINOP_1.isIdempotent F Y)
    {xs ys : List TarskiSet.{u}}
    (hxs : ∀ z, z ∈ xs → z ∈ X)
    (hys : ∀ z, z ∈ ys → z ∈ X)
    (hm : ∀ z, z ∈ xs ↔ z ∈ ys) :
    foldValues F Y hY f xs = foldValues F Y hY f ys := by
  have hp : (support xs).Perm (support ys) :=
    nodup_ext_perm (support_nodup xs) (support_nodup ys)
      (fun z => (support_mem z xs).trans ((hm z).trans (support_mem z ys).symm))
  calc
    foldValues F Y hY f xs =
        foldValues F Y hY f (support xs) :=
      (foldValues_support hY hF hf hc ha hi xs hxs).symm
    _ = foldValues F Y hY f (support ys) :=
      foldValues_perm hY hF hc ha hp
    _ = foldValues F Y hY f ys :=
      foldValues_support hY hF hf hc ha hi ys hys

private theorem elems_subset {X B : TarskiSet.{u}}
    (hB : B ∈ FINSUB_1.Fin X) :
    ∀ z, z ∈ elems B ((FINSUB_1.def5 X B).mp hB).2 → z ∈ X :=
  fun z hz => (FINSUB_1.def5 X B).mp hB |>.1 z
    ((mem_elems ((FINSUB_1.def5 X B).mp hB).2).mp hz)

private theorem setwiseFold_list {F X Y B f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X)
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y)
    (hi : BINOP_1.isIdempotent F Y)
    {xs : List TarskiSet.{u}} (_hnd : xs.Nodup)
    (hm : ∀ z, z ∈ xs ↔ z ∈ B) :
    setwiseFold F B f X Y hY hB =
      finishFold F Y hY (foldValues F Y hY f xs) := by
  unfold setwiseFold
  apply congrArg (finishFold F Y hY)
  apply foldValues_ext hY hF hf hc ha hi
    (elems_subset hB)
    (fun z hz => (FINSUB_1.def5 X B).mp hB |>.1 z ((hm z).mp hz))
  intro z
  exact (mem_elems ((FINSUB_1.def5 X B).mp hB).2).trans (hm z).symm

private theorem foldValues_append {F Y f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F Y)
    (ha : BINOP_1.isAssociative F Y) :
    ∀ xs ys : List TarskiSet.{u},
      foldValues F Y hY f (xs ++ ys) =
        optMulRaw F Y hY (foldValues F Y hY f xs)
          (foldValues F Y hY f ys) := by
  intro xs ys
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.cons_append, foldValues_cons, foldValues_cons, ih]
      exact optMulRaw_assoc hY hF ha _ _ _

private theorem foldValues_typed {F X Y f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F Y)
    (hf : FUNCT_2.isFunctionOf f X Y) :
    ∀ xs : List TarskiSet.{u}, (∀ z, z ∈ xs → z ∈ X) →
      foldValues F Y hY f xs = none ∨
        ∃ y, y ∈ Y ∧ foldValues F Y hY f xs = some y := by
  intro xs hxs
  induction xs with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
      have hxX := hxs x List.mem_cons_self
      have ht : ∀ z, z ∈ xs → z ∈ X :=
        fun z hz => hxs z (List.mem_cons.mpr (Or.inr hz))
      rcases ih ht with hnone | ⟨y, hy, hsome⟩
      · exact Or.inr ⟨FUNCT_1.apply f x, FUNCT_2.th5 hf hY hxX, by
          rw [foldValues_cons, hnone]; rfl⟩
      · exact Or.inr ⟨mul F Y hY (FUNCT_1.apply f x) y,
          mul_mem hY hF _ _, by
            rw [foldValues_cons, hsome]; rfl⟩

private theorem foldValues_some_of_nonempty {F X Y f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F Y)
    (hf : FUNCT_2.isFunctionOf f X Y)
    {xs : List TarskiSet.{u}} (hxs : ∀ z, z ∈ xs → z ∈ X)
    (hne : xs ≠ []) :
    ∃ y, y ∈ Y ∧ foldValues F Y hY f xs = some y := by
  rcases foldValues_typed hY hF hf xs hxs with hnone | hsome
  · cases xs with
    | nil => exact (hne rfl).elim
    | cons x xs =>
        rw [foldValues_cons] at hnone
        cases h : foldValues F Y hY f xs <;> simp [h, optMulRaw] at hnone
  · exact hsome

/-- `SETWISEO:17` (`Th17`). -/
private theorem th17_aux {F X Y f b : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hb : b ∈ X)
    (hF : BINOP_1.isBinOp F Y) (_hf : FUNCT_2.isFunctionOf f X Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y) :
    setwiseFold F (TARSKI.singleton b) f X Y hY (singleton_mem_Fin_aux hb) =
      FUNCT_1.apply f b := by
  let hB := singleton_mem_Fin_aux hb
  unfold setwiseFold
  have hp : (elems (TARSKI.singleton b)
      ((FINSUB_1.def5 X (TARSKI.singleton b)).mp hB).2).Perm [b] :=
    nodup_ext_perm (elems_nodup _ _) (by simp)
      (fun z => by
        rw [mem_elems, singleton_iff]
        simp)
  rw [foldValues_perm hY hF hc ha hp]
  rfl

private theorem elems_ne_nil {X B : TarskiSet.{u}}
    (hB : B ∈ FINSUB_1.Fin X) (hne : B ≠ (∅ : TarskiSet.{u})) :
    elems B ((FINSUB_1.def5 X B).mp hB).2 ≠ [] := by
  intro he
  obtain ⟨x, hx⟩ := XBOOLE_0.th7 hne
  have hm := (mem_elems ((FINSUB_1.def5 X B).mp hB).2).mpr hx
  rw [he] at hm
  exact List.not_mem_nil hm

private theorem fold_eq_some_setwise {F X Y B f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hne : B ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y) :
    foldValues F Y hY f
      (elems B ((FINSUB_1.def5 X B).mp hB).2) =
        some (setwiseFold F B f X Y hY hB) := by
  obtain ⟨y, hy, heq⟩ := foldValues_some_of_nonempty hY hF hf
    (elems_subset hB) (elems_ne_nil hB hne)
  unfold setwiseFold
  rw [heq]
  rfl

private theorem singleton_ne_empty (x : TarskiSet.{u}) :
    TARSKI.singleton x ≠ (∅ : TarskiSet.{u}) := by
  intro h
  exact (XBOOLE_0.empty_iff x).mp
    (Eq.subst (motive := fun S => x ∈ S) h
      ((singleton_iff x x).mpr rfl))

/-- Registration: a nonempty `X` has a nonempty element of `Fin X`. -/
theorem Fin_has_nonempty_element {X : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) :
    ∃ B, B ∈ FINSUB_1.Fin X ∧ B ≠ (∅ : TarskiSet.{u}) := by
  obtain ⟨x, hx⟩ := XBOOLE_0.th7 hX
  exact ⟨TARSKI.singleton x, singleton_mem_Fin_aux hx, singleton_ne_empty x⟩

private theorem upair_ne_empty (x y : TarskiSet.{u}) :
    TARSKI.upair x y ≠ (∅ : TarskiSet.{u}) := by
  intro h
  exact (XBOOLE_0.empty_iff x).mp
    (Eq.subst (motive := fun S => x ∈ S) h
      ((upair_iff x y x).mpr (Or.inl rfl)))

private theorem setwiseFold_congr {F X Y B C f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hC : C ∈ FINSUB_1.Fin X) (h : B = C) :
    setwiseFold F B f X Y hY hB = setwiseFold F C f X Y hY hC := by
  subst C
  rfl

/-- `SETWISEO:21` (`Th21`): fold of a union of nonempty finite sets. -/
private theorem th21_aux {F X Y B₁ B₂ f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB₁ : B₁ ∈ FINSUB_1.Fin X) (hB₂ : B₂ ∈ FINSUB_1.Fin X)
    (hne₁ : B₁ ≠ (∅ : TarskiSet.{u}))
    (hne₂ : B₂ ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hi : BINOP_1.isIdempotent F Y)
    (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y) :
    setwiseFold F (B₁ ∪ B₂) f X Y hY (union_mem_Fin hB₁ hB₂) =
      BINOP_1.apply2 F (setwiseFold F B₁ f X Y hY hB₁)
        (setwiseFold F B₂ f X Y hY hB₂) := by
  let xs := elems B₁ ((FINSUB_1.def5 X B₁).mp hB₁).2
  let ys := elems B₂ ((FINSUB_1.def5 X B₂).mp hB₂).2
  let hU := union_mem_Fin hB₁ hB₂
  have hfold : foldValues F Y hY f
      (elems (B₁ ∪ B₂) ((FINSUB_1.def5 X (B₁ ∪ B₂)).mp hU).2) =
      foldValues F Y hY f (xs ++ ys) := by
    apply foldValues_ext hY hF hf hc ha hi
    · exact elems_subset hU
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact (FINSUB_1.def5 X B₁).mp hB₁ |>.1 z
          ((mem_elems _).mp hz)
      · exact (FINSUB_1.def5 X B₂).mp hB₂ |>.1 z
          ((mem_elems _).mp hz)
    · intro z
      rw [mem_elems, List.mem_append, mem_elems, mem_elems,
        XBOOLE_0.def3]
  have h1 := fold_eq_some_setwise hY hB₁ hne₁ hF hf
  have h2 := fold_eq_some_setwise hY hB₂ hne₂ hF hf
  have hs1 : setwiseFold F B₁ f X Y hY hB₁ ∈ Y := by
    obtain ⟨y, hy, hey⟩ := foldValues_some_of_nonempty hY hF hf
      (elems_subset hB₁) (elems_ne_nil hB₁ hne₁)
    have heq : setwiseFold F B₁ f X Y hY hB₁ = y :=
      Option.some.inj (h1.symm.trans hey)
    exact heq ▸ hy
  have hs2 : setwiseFold F B₂ f X Y hY hB₂ ∈ Y := by
    obtain ⟨y, hy, hey⟩ := foldValues_some_of_nonempty hY hF hf
      (elems_subset hB₂) (elems_ne_nil hB₂ hne₂)
    have heq : setwiseFold F B₂ f X Y hY hB₂ = y :=
      Option.some.inj (h2.symm.trans hey)
    exact heq ▸ hy
  unfold setwiseFold
  rw [hfold, foldValues_append hY hF ha, h1, h2]
  simp only [optMulRaw, finishFold]
  rw [mul_eq hY hs1 hs2]

/-- `SETWISEO:18` (`Th18`). -/
private theorem th18_aux {F X Y f a b : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (haX : a ∈ X) (hbX : b ∈ X)
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hi : BINOP_1.isIdempotent F Y)
    (hc : BINOP_1.isCommutative F Y)
    (hassoc : BINOP_1.isAssociative F Y) :
    setwiseFold F (TARSKI.upair a b) f X Y hY (upair_mem_Fin_aux haX hbX) =
      BINOP_1.apply2 F (FUNCT_1.apply f a) (FUNCT_1.apply f b) := by
  let hU := union_mem_Fin (singleton_mem_Fin_aux haX) (singleton_mem_Fin_aux hbX)
  calc
    setwiseFold F (TARSKI.upair a b) f X Y hY (upair_mem_Fin_aux haX hbX) =
        setwiseFold F (TARSKI.singleton a ∪ TARSKI.singleton b)
          f X Y hY hU :=
      setwiseFold_congr hY (upair_mem_Fin_aux haX hbX) hU ENUMSET1.th1
    _ = BINOP_1.apply2 F
          (setwiseFold F (TARSKI.singleton a) f X Y hY
            (singleton_mem_Fin_aux haX))
          (setwiseFold F (TARSKI.singleton b) f X Y hY
            (singleton_mem_Fin_aux hbX)) :=
      th21_aux hY (singleton_mem_Fin_aux haX) (singleton_mem_Fin_aux hbX)
        (singleton_ne_empty a) (singleton_ne_empty b) hF hf hi hc hassoc
    _ = _ := by
      rw [th17_aux hY haX hF hf hc hassoc, th17_aux hY hbX hF hf hc hassoc]

/-- `SETWISEO:19` (`Th19`). -/
private theorem th19_aux {F X Y f a b c : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (haX : a ∈ X) (hbX : b ∈ X)
    (hcX : c ∈ X) (hF : BINOP_1.isBinOp F Y)
    (hf : FUNCT_2.isFunctionOf f X Y) (hi : BINOP_1.isIdempotent F Y)
    (hcomm : BINOP_1.isCommutative F Y)
    (hassoc : BINOP_1.isAssociative F Y) :
    setwiseFold F (ENUMSET1.enumset3 a b c) f X Y hY
      (enumset3_mem_Fin_aux haX hbX hcX) =
      BINOP_1.apply2 F
        (BINOP_1.apply2 F (FUNCT_1.apply f a) (FUNCT_1.apply f b))
        (FUNCT_1.apply f c) := by
  let hU := union_mem_Fin (upair_mem_Fin_aux haX hbX) (singleton_mem_Fin_aux hcX)
  calc
    setwiseFold F (ENUMSET1.enumset3 a b c) f X Y hY
        (enumset3_mem_Fin_aux haX hbX hcX) =
      setwiseFold F (TARSKI.upair a b ∪ TARSKI.singleton c)
        f X Y hY hU :=
      setwiseFold_congr hY (enumset3_mem_Fin_aux haX hbX hcX) hU ENUMSET1.th3
    _ = BINOP_1.apply2 F
        (setwiseFold F (TARSKI.upair a b) f X Y hY
          (upair_mem_Fin_aux haX hbX))
        (setwiseFold F (TARSKI.singleton c) f X Y hY
          (singleton_mem_Fin_aux hcX)) :=
      th21_aux hY (upair_mem_Fin_aux haX hbX) (singleton_mem_Fin_aux hcX)
        (upair_ne_empty a b) (singleton_ne_empty c) hF hf hi hcomm hassoc
    _ = _ := by
      rw [th18_aux hY haX hbX hF hf hi hcomm hassoc,
        th17_aux hY hcX hF hf hcomm hassoc]

/-- `SETWISEO:20` (`Th20`). -/
private theorem th20_aux {F X Y B f x : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hne : B ≠ (∅ : TarskiSet.{u})) (hx : x ∈ X)
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hi : BINOP_1.isIdempotent F Y)
    (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y) :
    setwiseFold F (B ∪ TARSKI.singleton x) f X Y hY
      (union_mem_Fin hB (singleton_mem_Fin_aux hx)) =
      BINOP_1.apply2 F (setwiseFold F B f X Y hY hB)
        (FUNCT_1.apply f x) := by
  rw [th21_aux hY hB (singleton_mem_Fin_aux hx) hne
    (singleton_ne_empty x) hF hf hi hc ha,
    th17_aux hY hx hF hf hc ha]

/-- Absolute slot 22. -/
private theorem th22_aux {F X Y B f x : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hxB : x ∈ B) (hF : BINOP_1.isBinOp F Y)
    (hf : FUNCT_2.isFunctionOf f X Y) (hi : BINOP_1.isIdempotent F Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y) :
    BINOP_1.apply2 F (FUNCT_1.apply f x)
      (setwiseFold F B f X Y hY hB) =
      setwiseFold F B f X Y hY hB := by
  have hxX := th9_aux hB hxB
  have hSB := union_mem_Fin (singleton_mem_Fin_aux hxX) hB
  have hneB : B ≠ (∅ : TarskiSet.{u}) := by
    intro h
    exact (XBOOLE_0.empty_iff x).mp (h ▸ hxB)
  have he : TARSKI.singleton x ∪ B = B :=
    XBOOLE_1.th12 ((ZFMISC_1.th31).2 hxB)
  calc
    BINOP_1.apply2 F (FUNCT_1.apply f x)
        (setwiseFold F B f X Y hY hB) =
      setwiseFold F (TARSKI.singleton x ∪ B) f X Y hY hSB := by
        rw [th21_aux hY (singleton_mem_Fin_aux hxX) hB
          (singleton_ne_empty x) hneB hF hf hi hc ha,
          th17_aux hY hxX hF hf hc ha]
    _ = setwiseFold F B f X Y hY hB :=
      setwiseFold_congr hY hSB hB he

/-- Absolute slot 23. -/
private theorem th23_aux {F X Y B C f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hC : C ∈ FINSUB_1.Fin X) (hneB : B ≠ (∅ : TarskiSet.{u}))
    (hBC : B ⊆ C) (hF : BINOP_1.isBinOp F Y)
    (hf : FUNCT_2.isFunctionOf f X Y) (hi : BINOP_1.isIdempotent F Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y) :
    BINOP_1.apply2 F (setwiseFold F B f X Y hY hB)
      (setwiseFold F C f X Y hY hC) =
      setwiseFold F C f X Y hY hC := by
  have hneC : C ≠ (∅ : TarskiSet.{u}) := by
    intro h
    obtain ⟨b, hb⟩ := XBOOLE_0.th7 hneB
    exact (XBOOLE_0.empty_iff b).mp
      (Eq.subst (motive := fun S => b ∈ S) h (hBC b hb))
  have hU := union_mem_Fin hB hC
  calc
    BINOP_1.apply2 F (setwiseFold F B f X Y hY hB)
        (setwiseFold F C f X Y hY hC) =
      setwiseFold F (B ∪ C) f X Y hY hU :=
        (th21_aux hY hB hC hneB hneC hF hf hi hc ha).symm
    _ = setwiseFold F C f X Y hY hC :=
      setwiseFold_congr hY hU hC (XBOOLE_1.th12 hBC)

theorem th17 {F X Y f b : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hb : b ∈ X) (hF : BINOP_1.isBinOp F Y)
    (hf : FUNCT_2.isFunctionOf f X Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y) :
    setwiseFold F (TARSKI.singleton b) f X Y hY
      (singleton_mem_Fin_aux hb) = FUNCT_1.apply f b :=
  th17_aux hY hb hF hf hc ha

theorem th18 {F X Y f a b : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (haX : a ∈ X) (hbX : b ∈ X) (hF : BINOP_1.isBinOp F Y)
    (hf : FUNCT_2.isFunctionOf f X Y) (hi : BINOP_1.isIdempotent F Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y) :
    setwiseFold F (TARSKI.upair a b) f X Y hY
      (upair_mem_Fin_aux haX hbX) =
        BINOP_1.apply2 F (FUNCT_1.apply f a) (FUNCT_1.apply f b) :=
  th18_aux hY haX hbX hF hf hi hc ha

theorem th19 {F X Y f a b c : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (haX : a ∈ X) (hbX : b ∈ X) (hcX : c ∈ X)
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hi : BINOP_1.isIdempotent F Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y) :
    setwiseFold F (ENUMSET1.enumset3 a b c) f X Y hY
      (enumset3_mem_Fin_aux haX hbX hcX) =
        BINOP_1.apply2 F
          (BINOP_1.apply2 F (FUNCT_1.apply f a) (FUNCT_1.apply f b))
          (FUNCT_1.apply f c) :=
  th19_aux hY haX hbX hcX hF hf hi hc ha

theorem th20 {F X Y B f x : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) (hne : B ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ X) (hF : BINOP_1.isBinOp F Y)
    (hf : FUNCT_2.isFunctionOf f X Y) (hi : BINOP_1.isIdempotent F Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y) :
    setwiseFold F (B ∪ TARSKI.singleton x) f X Y hY
      (union_mem_Fin hB (singleton_mem_Fin_aux hx)) =
        BINOP_1.apply2 F (setwiseFold F B f X Y hY hB)
          (FUNCT_1.apply f x) :=
  th20_aux hY hB hne hx hF hf hi hc ha

theorem th21 {F X Y B₁ B₂ f : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB₁ : B₁ ∈ FINSUB_1.Fin X) (hB₂ : B₂ ∈ FINSUB_1.Fin X)
    (hne₁ : B₁ ≠ (∅ : TarskiSet.{u})) (hne₂ : B₂ ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hi : BINOP_1.isIdempotent F Y) (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y) :
    setwiseFold F (B₁ ∪ B₂) f X Y hY (union_mem_Fin hB₁ hB₂) =
      BINOP_1.apply2 F (setwiseFold F B₁ f X Y hY hB₁)
        (setwiseFold F B₂ f X Y hY hB₂) :=
  th21_aux hY hB₁ hB₂ hne₁ hne₂ hF hf hi hc ha

theorem th22 {F X Y B f x : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) (hxB : x ∈ B)
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hi : BINOP_1.isIdempotent F Y) (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y) :
    BINOP_1.apply2 F (FUNCT_1.apply f x)
      (setwiseFold F B f X Y hY hB) = setwiseFold F B f X Y hY hB :=
  th22_aux hY hB hxB hF hf hi hc ha

theorem th23 {F X Y B C f : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) (hC : C ∈ FINSUB_1.Fin X)
    (hneB : B ≠ (∅ : TarskiSet.{u})) (hBC : B ⊆ C)
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hi : BINOP_1.isIdempotent F Y) (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y) :
    BINOP_1.apply2 F (setwiseFold F B f X Y hY hB)
      (setwiseFold F C f X Y hY hC) = setwiseFold F C f X Y hY hC :=
  th23_aux hY hB hC hneB hBC hF hf hi hc ha

/-- `SETWISEO:24` (`Th24`): fold of a nonempty constant family. -/
theorem th24 {F X Y B f a : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) (hneB : B ≠ (∅ : TarskiSet.{u}))
    (haY : a ∈ Y) (hF : BINOP_1.isBinOp F Y)
    (hf : FUNCT_2.isFunctionOf f X Y) (hi : BINOP_1.isIdempotent F Y)
    (hc : BINOP_1.isCommutative F Y) (hassoc : BINOP_1.isAssociative F Y)
    (hconst : ∀ b, b ∈ B → FUNCT_1.apply f b = a) :
    setwiseFold F B f X Y hY hB = a := by
  apply FinSubInd2 hX
    (fun C => ∀ hC : C ∈ FINSUB_1.Fin X, C ⊆ B →
      setwiseFold F C f X Y hY hC = a)
    (fun x hxX _hC hxsub => by
      have hxin : x ∈ B := hxsub x ((singleton_iff x x).mpr rfl)
      rw [th17_aux hY hxX hF hf hc hassoc, hconst x hxin])
    (by
      intro C D hC hD hneC hneD ihC ihD hCD hsub
      have hCB : C ⊆ B := XBOOLE_1.th1 XBOOLE_1.th7 hsub
      have hDB : D ⊆ B := XBOOLE_1.th1
        (fun z hz => (XBOOLE_0.def3 C D z).mpr (Or.inr hz)) hsub
      rw [th21_aux hY hC hD hneC hneD hF hf hi hc hassoc,
        ihC hC hCB, ihD hD hDB]
      exact hi a (SUBSET_1.isElement_of haY))
    B hB hneB hB (subset_refl B)

/-- `SETWISEO:25` (`Th25`). -/
theorem th25 {F X Y B f a : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) (haY : a ∈ Y)
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hi : BINOP_1.isIdempotent F Y) (hc : BINOP_1.isCommutative F Y)
    (hassoc : BINOP_1.isAssociative F Y)
    (himg : RELAT_1.image f B = TARSKI.singleton a) :
    setwiseFold F B f X Y hY hB = a := by
  have hneB : B ≠ (∅ : TarskiSet.{u}) := by
    intro h
    have he : RELAT_1.image f B = (∅ : TarskiSet.{u}) := by
      rw [h]
      apply XBOOLE_0.empty_eq
      rintro ⟨z, hz⟩
      obtain ⟨x, _, hx⟩ := (RELAT_1.def13 f ∅ z).mp hz
      exact (XBOOLE_0.empty_iff x).mp hx
    exact singleton_ne_empty a (himg.symm.trans he)
  apply th24 hX hY hB hneB haY hF hf hi hc hassoc
  intro b hb
  have hfb : FUNCT_1.apply f b ∈ RELAT_1.image f B :=
    (RELAT_1.def13 f B _).mpr
      ⟨b, FUNCT_1.apply_spec
        (FUNCT_2.functionOf_dom_eq hf hY ▸ th9_aux hB hb), hb⟩
  exact (singleton_iff a _).mp (himg ▸ hfb)

/-- Membership of a nonempty finite fold in its codomain. -/
theorem setwiseFold_mem {F X Y B f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hneB : B ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y) :
    setwiseFold F B f X Y hY hB ∈ Y := by
  obtain ⟨y, hy, hey⟩ := foldValues_some_of_nonempty hY hF hf
    (elems_subset hB) (elems_ne_nil hB hneB)
  have hfold := fold_eq_some_setwise hY hB hneB hF hf
  exact Option.some.inj (hfold.symm.trans hey) ▸ hy

private theorem comp_functionOf {X Y A f g : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hA : A ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X Y) (hg : FUNCT_2.isFunctionOf g Y A) :
    FUNCT_2.isFunctionOf (RELAT_1.comp f g) X A := by
  exact FUNCT_2.def11 hY hf (FUNCT_2.functionOf_isFunction hg)
    (FUNCT_2.functionOf_rng_sub hg)
    (fun z hz => Eq.subst (motive := fun S => z ∈ S)
      (FUNCT_2.functionOf_dom_eq hg hA).symm
      (FUNCT_2.functionOf_rng_sub hf z hz))

private theorem fold_hom_aux {F G X Y Z B f g q : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hZ : Z ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) (hneB : B ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F Y) (hG : BINOP_1.isBinOp G Z)
    (hf : FUNCT_2.isFunctionOf f X Y) (_hg : FUNCT_2.isFunctionOf g Y Z)
    (hq : FUNCT_2.isFunctionOf q X Z)
    (hqv : ∀ x, x ∈ X →
      FUNCT_1.apply q x = FUNCT_1.apply g (FUNCT_1.apply f x))
    (hiF : BINOP_1.isIdempotent F Y) (hcF : BINOP_1.isCommutative F Y)
    (haF : BINOP_1.isAssociative F Y)
    (hiG : BINOP_1.isIdempotent G Z) (hcG : BINOP_1.isCommutative G Z)
    (haG : BINOP_1.isAssociative G Z)
    (hhom : ∀ x y, x ∈ Y → y ∈ Y →
      FUNCT_1.apply g (BINOP_1.apply2 F x y) =
        BINOP_1.apply2 G (FUNCT_1.apply g x) (FUNCT_1.apply g y)) :
    FUNCT_1.apply g (setwiseFold F B f X Y hY hB) =
      setwiseFold G B q X Z hZ hB := by
  apply FinSubInd2 hX
    (fun C => ∀ hC : C ∈ FINSUB_1.Fin X,
      FUNCT_1.apply g (setwiseFold F C f X Y hY hC) =
        setwiseFold G C q X Z hZ hC)
    (fun x hx _ => by
      rw [th17_aux hY hx hF hf hcF haF, th17_aux hZ hx hG hq hcG haG,
        hqv x hx])
    (by
      intro C D hC hD hneC hneD ihC ihD hCD
      rw [th21_aux hY hC hD hneC hneD hF hf hiF hcF haF,
        th21_aux hZ hC hD hneC hneD hG hq hiG hcG haG,
        hhom, ihC hC, ihD hD]
      · exact setwiseFold_mem hY hC hneC hF hf
      · exact setwiseFold_mem hY hD hneD hF hf)
    B hB hneB hB

/-- `SETWISEO:30` (`Th30`): a semilattice homomorphism preserves folds. -/
theorem th30 {F G X Y Z B f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hZ : Z ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) (hneB : B ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F Y) (hG : BINOP_1.isBinOp G Z)
    (hf : FUNCT_2.isFunctionOf f X Y) (hg : FUNCT_2.isFunctionOf g Y Z)
    (hiF : BINOP_1.isIdempotent F Y) (hcF : BINOP_1.isCommutative F Y)
    (haF : BINOP_1.isAssociative F Y)
    (hiG : BINOP_1.isIdempotent G Z) (hcG : BINOP_1.isCommutative G Z)
    (haG : BINOP_1.isAssociative G Z)
    (hhom : ∀ x y, x ∈ Y → y ∈ Y →
      FUNCT_1.apply g (BINOP_1.apply2 F x y) =
        BINOP_1.apply2 G (FUNCT_1.apply g x) (FUNCT_1.apply g y)) :
    FUNCT_1.apply g (setwiseFold F B f X Y hY hB) =
      setwiseFold G B (RELAT_1.comp f g) X Z hZ hB :=
  fold_hom_aux hX hY hZ hB hneB hF hG hf hg
    (comp_functionOf hY hZ hf hg)
    (fun x hx => FUNCT_2.th15 (x := x) hf
      (FUNCT_2.functionOf_isFunction hg) hY hx)
    hiF hcF haF hiG hcG haG hhom

/-- Absolute slot 27: left distributivity through a finite fold. -/
theorem th27 {F G X Y B f a : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) (hneB : B ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F Y) (hG : BINOP_1.isBinOp G Y)
    (hf : FUNCT_2.isFunctionOf f X Y) (haY : a ∈ Y)
    (hi : BINOP_1.isIdempotent F Y) (hc : BINOP_1.isCommutative F Y)
    (hassoc : BINOP_1.isAssociative F Y)
    (hdist : BINOP_1.is_distributive_wrt G F Y) :
    BINOP_1.apply2 G a (setwiseFold F B f X Y hY hB) =
      setwiseFold F B (FUNCOP_1.appliedLeft G a f) X Y hY hB := by
  let idY := RELAT_1.id Y
  have hid : FUNCT_2.isFunctionOf idY Y Y := (FUNCT_2.id_isPermutation Y).1
  let gL := FUNCOP_1.appliedLeft G a idY
  let q := FUNCOP_1.appliedLeft G a f
  have hgL : FUNCT_2.isFunctionOf gL Y Y :=
    FUNCOP_1.appliedLeft_isFunctionOf hY hG hid (SUBSET_1.isElement_of haY)
  have hq : FUNCT_2.isFunctionOf q X Y :=
    FUNCOP_1.appliedLeft_isFunctionOf hY hG hf (SUBSET_1.isElement_of haY)
  have hmain := fold_hom_aux hX hY hY hB hneB hF hF hf hgL hq
    (fun x hx => by
      rw [FUNCOP_1.th53 hY hX hG hf (SUBSET_1.isElement_of haY) hx,
        FUNCOP_1.th53 hY hY hG hid (SUBSET_1.isElement_of haY)
          (FUNCT_2.th5 hf hY hx),
        FUNCT_1.id_apply (FUNCT_2.th5 hf hY hx)])
    hi hc hassoc hi hc hassoc
    (fun x y hx hy => by
      have hxy : BINOP_1.apply2 F x y ∈ Y :=
        SUBSET_1.isElement_mem (fun he => hY (XBOOLE_0.empty_eq he))
          (BINOP_1.apply2_binop_isElement hF
            (SUBSET_1.isElement_of hx) (SUBSET_1.isElement_of hy))
      rw [FUNCOP_1.th53 hY hY hG hid (SUBSET_1.isElement_of haY) hxy,
        FUNCOP_1.th53 hY hY hG hid (SUBSET_1.isElement_of haY) hx,
        FUNCOP_1.th53 hY hY hG hid (SUBSET_1.isElement_of haY) hy,
        FUNCT_1.id_apply hxy, FUNCT_1.id_apply hx, FUNCT_1.id_apply hy]
      exact hdist.1 a x y (SUBSET_1.isElement_of haY)
        (SUBSET_1.isElement_of hx) (SUBSET_1.isElement_of hy))
  rw [FUNCOP_1.th53 hY hY hG hid (SUBSET_1.isElement_of haY)
    (setwiseFold_mem hY hB hneB hF hf)] at hmain
  rw [FUNCT_1.id_apply (setwiseFold_mem hY hB hneB hF hf)] at hmain
  simpa [q] using hmain

/-- Absolute slot 28: right distributivity through a finite fold. -/
theorem th28 {F G X Y B f a : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) (hneB : B ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F Y) (hG : BINOP_1.isBinOp G Y)
    (hf : FUNCT_2.isFunctionOf f X Y) (haY : a ∈ Y)
    (hi : BINOP_1.isIdempotent F Y) (hc : BINOP_1.isCommutative F Y)
    (hassoc : BINOP_1.isAssociative F Y)
    (hdist : BINOP_1.is_distributive_wrt G F Y) :
    BINOP_1.apply2 G (setwiseFold F B f X Y hY hB) a =
      setwiseFold F B (FUNCOP_1.appliedRight G f a) X Y hY hB := by
  let idY := RELAT_1.id Y
  have hid : FUNCT_2.isFunctionOf idY Y Y := (FUNCT_2.id_isPermutation Y).1
  let gR := FUNCOP_1.appliedRight G idY a
  let q := FUNCOP_1.appliedRight G f a
  have hgR : FUNCT_2.isFunctionOf gR Y Y :=
    FUNCOP_1.appliedRight_isFunctionOf hY hG hid (SUBSET_1.isElement_of haY)
  have hq : FUNCT_2.isFunctionOf q X Y :=
    FUNCOP_1.appliedRight_isFunctionOf hY hG hf (SUBSET_1.isElement_of haY)
  have hmain := fold_hom_aux hX hY hY hB hneB hF hF hf hgR hq
    (fun x hx => by
      rw [FUNCOP_1.th48 hY hX hG hf (SUBSET_1.isElement_of haY) hx,
        FUNCOP_1.th48 hY hY hG hid (SUBSET_1.isElement_of haY)
          (FUNCT_2.th5 hf hY hx),
        FUNCT_1.id_apply (FUNCT_2.th5 hf hY hx)])
    hi hc hassoc hi hc hassoc
    (fun x y hx hy => by
      have hxy : BINOP_1.apply2 F x y ∈ Y :=
        SUBSET_1.isElement_mem (fun he => hY (XBOOLE_0.empty_eq he))
          (BINOP_1.apply2_binop_isElement hF
            (SUBSET_1.isElement_of hx) (SUBSET_1.isElement_of hy))
      rw [FUNCOP_1.th48 hY hY hG hid (SUBSET_1.isElement_of haY) hxy,
        FUNCOP_1.th48 hY hY hG hid (SUBSET_1.isElement_of haY) hx,
        FUNCOP_1.th48 hY hY hG hid (SUBSET_1.isElement_of haY) hy,
        FUNCT_1.id_apply hxy, FUNCT_1.id_apply hx, FUNCT_1.id_apply hy]
      exact hdist.2 x y a (SUBSET_1.isElement_of hx)
        (SUBSET_1.isElement_of hy) (SUBSET_1.isElement_of haY))
  rw [FUNCOP_1.th48 hY hY hG hid (SUBSET_1.isElement_of haY)
    (setwiseFold_mem hY hB hneB hF hf)] at hmain
  rw [FUNCT_1.id_apply (setwiseFold_mem hY hB hneB hF hf)] at hmain
  simpa [q] using hmain

private theorem image_nonempty {X Y C f : TarskiSet.{u}}
    (hC : C ∈ FINSUB_1.Fin X) (hneC : C ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X Y) (hY : Y ≠ (∅ : TarskiSet.{u})) :
    RELAT_1.image f C ≠ (∅ : TarskiSet.{u}) := by
  intro h
  exact hneC (th13_aux hC hf hY h)

/-- `SETWISEO:29` (`Th29`). -/
theorem th29 {A X Y F B f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hneB : B ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F A)
    (hf : FUNCT_2.isFunctionOf f X Y) (hg : FUNCT_2.isFunctionOf g Y A)
    (hi : BINOP_1.isIdempotent F A) (hc : BINOP_1.isCommutative F A)
    (ha : BINOP_1.isAssociative F A) :
    setwiseFold F (RELAT_1.image f B) g Y A hA (lm1_aux hB hf) =
      setwiseFold F B (RELAT_1.comp f g) X A hA hB := by
  let hcomp := comp_functionOf hY hA hf hg
  apply FinSubInd2 hX
    (fun C => ∀ hC : C ∈ FINSUB_1.Fin X,
      setwiseFold F (RELAT_1.image f C) g Y A hA (lm1_aux hC hf) =
        setwiseFold F C (RELAT_1.comp f g) X A hA hC)
    (fun x hx hC => by
      have hfxY := FUNCT_2.th5 hf hY hx
      have himg := th8_aux hf hY hx
      calc
        setwiseFold F (RELAT_1.image f (TARSKI.singleton x)) g Y A hA
            (lm1_aux hC hf) =
          setwiseFold F (TARSKI.singleton (FUNCT_1.apply f x)) g Y A hA
            (singleton_mem_Fin_aux hfxY) :=
          setwiseFold_congr hA (lm1_aux hC hf) (singleton_mem_Fin_aux hfxY) himg
        _ = FUNCT_1.apply g (FUNCT_1.apply f x) :=
          th17_aux hA hfxY hF hg hc ha
        _ = FUNCT_1.apply (RELAT_1.comp f g) x :=
          (FUNCT_2.th15 hf (FUNCT_2.functionOf_isFunction hg) hY hx).symm
        _ = setwiseFold F (TARSKI.singleton x) (RELAT_1.comp f g) X A hA hC :=
          (th17_aux hA hx hF hcomp hc ha).symm)
    (by
      intro C D hC hD hneC hneD ihC ihD hCD
      have himgC := lm1_aux hC hf
      have himgD := lm1_aux hD hf
      have himgU := lm1_aux hCD hf
      have hEq := RELAT_1.th120
        (R := f) (X := C) (Y := D)
      calc
        setwiseFold F (RELAT_1.image f (C ∪ D)) g Y A hA himgU =
          setwiseFold F (RELAT_1.image f C ∪ RELAT_1.image f D)
            g Y A hA (union_mem_Fin himgC himgD) :=
          setwiseFold_congr hA himgU (union_mem_Fin himgC himgD) hEq
        _ = BINOP_1.apply2 F
            (setwiseFold F (RELAT_1.image f C) g Y A hA himgC)
            (setwiseFold F (RELAT_1.image f D) g Y A hA himgD) :=
          th21_aux hA himgC himgD (image_nonempty hC hneC hf hY)
            (image_nonempty hD hneD hf hY) hF hg hi hc ha
        _ = BINOP_1.apply2 F
            (setwiseFold F C (RELAT_1.comp f g) X A hA hC)
            (setwiseFold F D (RELAT_1.comp f g) X A hA hD) := by
          rw [ihC hC, ihD hD]
        _ = setwiseFold F (C ∪ D) (RELAT_1.comp f g) X A hA hCD :=
          (th21_aux hA hC hD hneC hneD hF hcomp hi hc ha).symm)
    B hB hneB hB

private theorem foldValues_fun_congr {F _X Y f g : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) :
    ∀ xs : List TarskiSet.{u},
      (∀ x, x ∈ xs → FUNCT_1.apply f x = FUNCT_1.apply g x) →
      foldValues F Y hY f xs = foldValues F Y hY g xs := by
  intro xs hv
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [foldValues_cons, foldValues_cons, hv x List.mem_cons_self,
        ih (fun z hz => hv z (List.mem_cons.mpr (Or.inr hz)))]

private theorem setwiseFold_fun_congr {F X Y B f g : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hv : ∀ x, x ∈ B → FUNCT_1.apply f x = FUNCT_1.apply g x) :
    setwiseFold F B f X Y hY hB = setwiseFold F B g X Y hY hB := by
  unfold setwiseFold
  apply congrArg (finishFold F Y hY)
  apply foldValues_fun_congr (_X := X) hY
  intro x hx
  exact hv x ((mem_elems ((FINSUB_1.def5 X B).mp hB).2).mp hx)

/-- `SETWISEO:26` (`Th26`). -/
theorem th26 {F X Y A B f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hA : A ∈ FINSUB_1.Fin X) (hB : B ∈ FINSUB_1.Fin X)
    (hneA : A ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X Y) (hg : FUNCT_2.isFunctionOf g X Y)
    (hF : BINOP_1.isBinOp F Y) (hi : BINOP_1.isIdempotent F Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y)
    (himg : RELAT_1.image f A = RELAT_1.image g B) :
    setwiseFold F A f X Y hY hA = setwiseFold F B g X Y hY hB := by
  let idY := RELAT_1.id Y
  have hid : FUNCT_2.isFunctionOf idY Y Y := (FUNCT_2.id_isPermutation Y).1
  have hneB : B ≠ (∅ : TarskiSet.{u}) := by
    intro h
    have he : RELAT_1.image g B = (∅ : TarskiSet.{u}) := by
      rw [h]
      apply XBOOLE_0.empty_eq
      rintro ⟨z, hz⟩
      obtain ⟨x, _, hx⟩ := (RELAT_1.def13 g ∅ z).mp hz
      exact (XBOOLE_0.empty_iff x).mp hx
    exact image_nonempty hA hneA hf hY (himg.trans he)
  have hfa := th29 hX hY hY hA hneA hF hf hid hi hc ha
  have hgb := th29 hX hY hY hB hneB hF hg hid hi hc ha
  have hcf : setwiseFold F A (RELAT_1.comp f idY) X Y hY hA =
      setwiseFold F A f X Y hY hA := by
    apply setwiseFold_fun_congr hY hA
    intro x hx
    rw [FUNCT_2.th15 hf (FUNCT_2.functionOf_isFunction hid) hY
      (th9_aux hA hx), FUNCT_1.id_apply (FUNCT_2.th5 hf hY (th9_aux hA hx))]
  have hcg : setwiseFold F B (RELAT_1.comp g idY) X Y hY hB =
      setwiseFold F B g X Y hY hB := by
    apply setwiseFold_fun_congr hY hB
    intro x hx
    rw [FUNCT_2.th15 hg (FUNCT_2.functionOf_isFunction hid) hY
      (th9_aux hB hx), FUNCT_1.id_apply (FUNCT_2.th5 hg hY (th9_aux hB hx))]
  calc
    setwiseFold F A f X Y hY hA =
        setwiseFold F (RELAT_1.image f A) idY Y Y hY (lm1_aux hA hf) :=
      hcf.symm.trans hfa.symm
    _ = setwiseFold F (RELAT_1.image g B) idY Y Y hY (lm1_aux hB hg) :=
      setwiseFold_congr hY (lm1_aux hA hf) (lm1_aux hB hg) himg
    _ = setwiseFold F B g X Y hY hB :=
      hgb.trans hcg

private theorem elems_empty_eq_nil (X : TarskiSet.{u}) :
    elems (∅ : TarskiSet.{u})
      ((FINSUB_1.def5 X (∅ : TarskiSet.{u})).mp (empty_mem_Fin X)).2 = [] := by
  cases h : elems (∅ : TarskiSet.{u})
      ((FINSUB_1.def5 X (∅ : TarskiSet.{u})).mp (empty_mem_Fin X)).2 with
  | nil => rfl
  | cons x xs =>
      have hx := (mem_elems
        ((FINSUB_1.def5 X (∅ : TarskiSet.{u})).mp (empty_mem_Fin X)).2).mp
        (Eq.subst (motive := fun l => x ∈ l) h.symm List.mem_cons_self)
      exact (XBOOLE_0.empty_iff x).mp hx |>.elim

/-- `SETWISEO:31` (`Th31`). -/
private theorem th31_aux {F X Y f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (_hc : BINOP_1.isCommutative F Y) (_ha : BINOP_1.isAssociative F Y)
    (hu : isHavingAUnity F Y) :
    setwiseFold F (emptyFin X) f X Y hY (empty_mem_Fin X) =
      unity F Y := by
  unfold emptyFin setwiseFold
  rw [elems_empty_eq_nil X]
  simp only [foldValues, List.map_nil, List.foldr]
  exact finishFold_none_of_unity hY hu

/-- `SETWISEO:32` (`Th32`). -/
private theorem th32_aux {F X Y B f x : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hx : x ∈ X) (hF : BINOP_1.isBinOp F Y)
    (hf : FUNCT_2.isFunctionOf f X Y) (hi : BINOP_1.isIdempotent F Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y)
    (hu : isHavingAUnity F Y) :
    setwiseFold F (B ∪ TARSKI.singleton x) f X Y hY
      (union_mem_Fin hB (singleton_mem_Fin_aux hx)) =
      BINOP_1.apply2 F (setwiseFold F B f X Y hY hB)
        (FUNCT_1.apply f x) := by
  by_cases hne : B = (∅ : TarskiSet.{u})
  · have hU := union_mem_Fin hB (singleton_mem_Fin_aux hx)
    have heU : B ∪ TARSKI.singleton x = TARSKI.singleton x := by
      rw [hne]
      exact XBOOLE_1.th12 XBOOLE_1.th2
    calc
      setwiseFold F (B ∪ TARSKI.singleton x) f X Y hY hU =
          setwiseFold F (TARSKI.singleton x) f X Y hY
            (singleton_mem_Fin_aux hx) :=
        setwiseFold_congr hY hU (singleton_mem_Fin_aux hx) heU
      _ = FUNCT_1.apply f x := th17_aux hY hx hF hf hc ha
      _ = BINOP_1.apply2 F (unity F Y) (FUNCT_1.apply f x) :=
        (th15_aux hu _ (SUBSET_1.isElement_of (FUNCT_2.th5 hf hY hx))).1.symm
      _ = BINOP_1.apply2 F (setwiseFold F B f X Y hY hB)
          (FUNCT_1.apply f x) := by
        have heB : setwiseFold F B f X Y hY hB = unity F Y := by
          have h0 := th31_aux (F := F) (X := X) (f := f) hY hc ha hu
          exact (setwiseFold_congr hY hB (empty_mem_Fin X) hne).trans h0
        rw [heB]
  · exact th20_aux hY hB hne hx hF hf hi hc ha

/-- Absolute slot 33: the unital union formula. -/
private theorem th33_aux {F X Y B₁ B₂ f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB₁ : B₁ ∈ FINSUB_1.Fin X) (hB₂ : B₂ ∈ FINSUB_1.Fin X)
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hi : BINOP_1.isIdempotent F Y) (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y) (hu : isHavingAUnity F Y) :
    setwiseFold F (B₁ ∪ B₂) f X Y hY (union_mem_Fin hB₁ hB₂) =
      BINOP_1.apply2 F (setwiseFold F B₁ f X Y hY hB₁)
        (setwiseFold F B₂ f X Y hY hB₂) := by
  by_cases h1 : B₁ = (∅ : TarskiSet.{u})
  · have hU : B₁ ∪ B₂ = B₂ := by rw [h1]; exact XBOOLE_1.th12 XBOOLE_1.th2
    have hf1 : setwiseFold F B₁ f X Y hY hB₁ = unity F Y :=
      (setwiseFold_congr hY hB₁ (empty_mem_Fin X) h1).trans
        (th31_aux hY hc ha hu)
    rw [hf1]
    exact (setwiseFold_congr hY (union_mem_Fin hB₁ hB₂) hB₂ hU).trans
      ((th15_aux hu _ (SUBSET_1.isElement_of
        (by
          by_cases h2 : B₂ = (∅ : TarskiSet.{u})
          · rw [(setwiseFold_congr hY hB₂ (empty_mem_Fin X) h2).trans
              (th31_aux hY hc ha hu)]
            exact SUBSET_1.isElement_mem
              (fun he => hY (XBOOLE_0.empty_eq he)) (unity_isElement hu)
          · exact setwiseFold_mem hY hB₂ h2 hF hf))).1).symm
  · by_cases h2 : B₂ = (∅ : TarskiSet.{u})
    · have hU : B₁ ∪ B₂ = B₁ := by
        rw [h2, XBOOLE_0.union_comm]
        exact XBOOLE_1.th12 XBOOLE_1.th2
      have hf2 : setwiseFold F B₂ f X Y hY hB₂ = unity F Y :=
        (setwiseFold_congr hY hB₂ (empty_mem_Fin X) h2).trans
          (th31_aux hY hc ha hu)
      rw [hf2]
      exact (setwiseFold_congr hY (union_mem_Fin hB₁ hB₂) hB₁ hU).trans
        ((th15_aux hu _ (SUBSET_1.isElement_of
          (setwiseFold_mem hY hB₁ h1 hF hf))).2).symm
    · exact th21_aux hY hB₁ hB₂ h1 h2 hF hf hi hc ha

theorem th31 {F X Y f : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (_hF : BINOP_1.isBinOp F Y) (_hf : FUNCT_2.isFunctionOf f X Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y)
    (hu : isHavingAUnity F Y) :
    setwiseFold F (emptyFin X) f X Y hY (empty_mem_Fin X) = unity F Y :=
  th31_aux hY hc ha hu

theorem th32 {F X Y B f x : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) (hx : x ∈ X)
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hi : BINOP_1.isIdempotent F Y) (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y) (hu : isHavingAUnity F Y) :
    setwiseFold F (B ∪ TARSKI.singleton x) f X Y hY
      (union_mem_Fin hB (singleton_mem_Fin_aux hx)) =
        BINOP_1.apply2 F (setwiseFold F B f X Y hY hB)
          (FUNCT_1.apply f x) :=
  th32_aux hY hB hx hF hf hi hc ha hu

theorem th33 {F X Y B₁ B₂ f : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB₁ : B₁ ∈ FINSUB_1.Fin X) (hB₂ : B₂ ∈ FINSUB_1.Fin X)
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hi : BINOP_1.isIdempotent F Y) (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y) (hu : isHavingAUnity F Y) :
    setwiseFold F (B₁ ∪ B₂) f X Y hY (union_mem_Fin hB₁ hB₂) =
      BINOP_1.apply2 F (setwiseFold F B₁ f X Y hY hB₁)
        (setwiseFold F B₂ f X Y hY hB₂) :=
  th33_aux hY hB₁ hB₂ hF hf hi hc ha hu

/-- Absolute slot 34: the unital image-invariance formula. -/
theorem th34 {F X Y A B f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hA : A ∈ FINSUB_1.Fin X) (hB : B ∈ FINSUB_1.Fin X)
    (hf : FUNCT_2.isFunctionOf f X Y) (hg : FUNCT_2.isFunctionOf g X Y)
    (hF : BINOP_1.isBinOp F Y) (hi : BINOP_1.isIdempotent F Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y)
    (hu : isHavingAUnity F Y)
    (himg : RELAT_1.image f A = RELAT_1.image g B) :
    setwiseFold F A f X Y hY hA = setwiseFold F B g X Y hY hB := by
  by_cases hneA : A = (∅ : TarskiSet.{u})
  · have heA : RELAT_1.image f A = (∅ : TarskiSet.{u}) := by
      rw [hneA]
      apply XBOOLE_0.empty_eq
      rintro ⟨z, hz⟩
      obtain ⟨x, _, hx⟩ := (RELAT_1.def13 f ∅ z).mp hz
      exact (XBOOLE_0.empty_iff x).mp hx
    have hneB : B = (∅ : TarskiSet.{u}) :=
      th13_aux hB hg hY (himg ▸ heA)
    calc
      setwiseFold F A f X Y hY hA = unity F Y :=
        (setwiseFold_congr hY hA (empty_mem_Fin X) hneA).trans
          (th31_aux hY hc ha hu)
      _ = setwiseFold F B g X Y hY hB :=
        ((setwiseFold_congr hY hB (empty_mem_Fin X) hneB).trans
          (th31_aux hY hc ha hu)).symm
  · exact th26 hX hY hA hB hneA hf hg hF hi hc ha himg

/-- `SETWISEO:35` (`Th35`). -/
theorem th35 {A X Y F B f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hF : BINOP_1.isBinOp F A) (hf : FUNCT_2.isFunctionOf f X Y)
    (hg : FUNCT_2.isFunctionOf g Y A) (hi : BINOP_1.isIdempotent F A)
    (hc : BINOP_1.isCommutative F A) (ha : BINOP_1.isAssociative F A)
    (hu : isHavingAUnity F A) :
    setwiseFold F (RELAT_1.image f B) g Y A hA (lm1_aux hB hf) =
      setwiseFold F B (RELAT_1.comp f g) X A hA hB := by
  by_cases hneB : B = (∅ : TarskiSet.{u})
  · have himg : RELAT_1.image f B = (∅ : TarskiSet.{u}) := by
      rw [hneB]
      apply XBOOLE_0.empty_eq
      rintro ⟨z, hz⟩
      obtain ⟨x, _, hx⟩ := (RELAT_1.def13 f ∅ z).mp hz
      exact (XBOOLE_0.empty_iff x).mp hx
    calc
      setwiseFold F (RELAT_1.image f B) g Y A hA (lm1_aux hB hf) =
          unity F A :=
        (setwiseFold_congr hA (lm1_aux hB hf) (empty_mem_Fin Y) himg).trans
          (th31_aux hA hc ha hu)
      _ = setwiseFold F B (RELAT_1.comp f g) X A hA hB :=
        ((setwiseFold_congr hA hB (empty_mem_Fin X) hneB).trans
          (th31_aux hA hc ha hu)).symm
  · exact th29 hX hY hA hB hneB hF hf hg hi hc ha

/-- Absolute slot 36: unital homomorphisms preserve all finite folds. -/
theorem th36 {F G X Y Z B f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hZ : Z ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hF : BINOP_1.isBinOp F Y) (hG : BINOP_1.isBinOp G Z)
    (hf : FUNCT_2.isFunctionOf f X Y) (hg : FUNCT_2.isFunctionOf g Y Z)
    (hiF : BINOP_1.isIdempotent F Y) (hcF : BINOP_1.isCommutative F Y)
    (haF : BINOP_1.isAssociative F Y) (huF : isHavingAUnity F Y)
    (hiG : BINOP_1.isIdempotent G Z) (hcG : BINOP_1.isCommutative G Z)
    (haG : BINOP_1.isAssociative G Z) (huG : isHavingAUnity G Z)
    (hunit : FUNCT_1.apply g (unity F Y) = unity G Z)
    (hhom : ∀ x y, x ∈ Y → y ∈ Y →
      FUNCT_1.apply g (BINOP_1.apply2 F x y) =
        BINOP_1.apply2 G (FUNCT_1.apply g x) (FUNCT_1.apply g y)) :
    FUNCT_1.apply g (setwiseFold F B f X Y hY hB) =
      setwiseFold G B (RELAT_1.comp f g) X Z hZ hB := by
  let hcomp := comp_functionOf hY hZ hf hg
  by_cases hneB : B = (∅ : TarskiSet.{u})
  · have hf0 : setwiseFold F B f X Y hY hB = unity F Y :=
      (setwiseFold_congr hY hB (empty_mem_Fin X) hneB).trans
        (th31_aux hY hcF haF huF)
    have hg0 : setwiseFold G B (RELAT_1.comp f g) X Z hZ hB = unity G Z :=
      (setwiseFold_congr hZ hB (empty_mem_Fin X) hneB).trans
        (th31_aux hZ hcG haG huG)
    rw [hf0, hg0, hunit]
  · exact th30 hX hY hZ hB hneB hF hG hf hg
      hiF hcF haF hiG hcG haG hhom

private theorem setwiseFold_insert_fresh {F X Y C f x : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hC : C ∈ FINSUB_1.Fin X)
    (hx : x ∈ X) (hxC : x ∉ C) (hneC : C ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y) :
    setwiseFold F (C ∪ TARSKI.singleton x) f X Y hY
      (union_mem_Fin hC (singleton_mem_Fin_aux hx)) =
      BINOP_1.apply2 F (setwiseFold F C f X Y hY hC)
        (FUNCT_1.apply f x) := by
  let hU := union_mem_Fin hC (singleton_mem_Fin_aux hx)
  let xs := elems C ((FINSUB_1.def5 X C).mp hC).2
  let ys := elems (C ∪ TARSKI.singleton x)
    ((FINSUB_1.def5 X (C ∪ TARSKI.singleton x)).mp hU).2
  have hnd : (x :: xs).Nodup := List.nodup_cons.mpr
    ⟨fun hm => hxC ((mem_elems ((FINSUB_1.def5 X C).mp hC).2).mp hm),
      elems_nodup _ _⟩
  have hp : ys.Perm (x :: xs) :=
    nodup_ext_perm (elems_nodup _ _) hnd (fun z => by
      rw [mem_elems, List.mem_cons, mem_elems, XBOOLE_0.def3, singleton_iff]
      exact or_comm)
  unfold setwiseFold
  rw [foldValues_perm hY hF hc ha hp, foldValues_cons,
    fold_eq_some_setwise hY hC hneC hF hf]
  simp only [optMulRaw, finishFold]
  rw [mul_eq hY (FUNCT_2.th5 hf hY hx)
    (setwiseFold_mem hY hC hneC hF hf)]
  exact hc _ _ (SUBSET_1.isElement_of (FUNCT_2.th5 hf hY hx))
    (SUBSET_1.isElement_of (setwiseFold_mem hY hC hneC hF hf))

private theorem finishFold_none_of_no_unity {F Y : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hu : ¬ isHavingAUnity F Y) :
    finishFold F Y hY none = defaultElement Y hY := by
  unfold finishFold
  exact dif_neg hu

private theorem setwiseFold_mem_all {F X Y C f : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hC : C ∈ FINSUB_1.Fin X)
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y) :
    setwiseFold F C f X Y hY hC ∈ Y := by
  by_cases hne : C = (∅ : TarskiSet.{u})
  · by_cases hu : isHavingAUnity F Y
    · rw [(setwiseFold_congr hY hC (empty_mem_Fin X) hne).trans
          (th31_aux hY hc ha hu)]
      exact SUBSET_1.isElement_mem (fun he => hY (XBOOLE_0.empty_eq he))
        (unity_isElement hu)
    · have he : setwiseFold F C f X Y hY hC = defaultElement Y hY := by
        calc
          setwiseFold F C f X Y hY hC =
              setwiseFold F (∅ : TarskiSet.{u}) f X Y hY
                (empty_mem_Fin X) :=
            setwiseFold_congr hY hC (empty_mem_Fin X) hne
          _ = defaultElement Y hY := by
            unfold setwiseFold
            rw [elems_empty_eq_nil X]
            simp only [foldValues, List.map_nil, List.foldr]
            exact finishFold_none_of_no_unity hY hu
      rw [he]
      exact defaultElement_mem Y hY
  · exact setwiseFold_mem hY hC hne hF hf

private noncomputable def foldFamily
    (F f X Y : TarskiSet.{u}) (hY : Y ≠ (∅ : TarskiSet.{u})) :
    TarskiSet.{u} :=
  by
    classical
    exact Classical.choose (FUNCT_1.sch_Lambda (FINSUB_1.Fin X)
      (fun C => if hC : C ∈ FINSUB_1.Fin X
        then setwiseFold F C f X Y hY hC else defaultElement Y hY))

private theorem foldFamily_isFunction (F f X Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.isFunction (foldFamily F f X Y hY) :=
  by
    classical
    exact (Classical.choose_spec (FUNCT_1.sch_Lambda (FINSUB_1.Fin X)
      (fun C => if hC : C ∈ FINSUB_1.Fin X
        then setwiseFold F C f X Y hY hC else defaultElement Y hY))).1

private theorem foldFamily_dom (F f X Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u})) :
    RELAT_1.dom (foldFamily F f X Y hY) = FINSUB_1.Fin X :=
  by
    classical
    exact (Classical.choose_spec (FUNCT_1.sch_Lambda (FINSUB_1.Fin X)
      (fun C => if hC : C ∈ FINSUB_1.Fin X
        then setwiseFold F C f X Y hY hC else defaultElement Y hY))).2.1

private theorem foldFamily_apply {F f X Y C : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hC : C ∈ FINSUB_1.Fin X) :
    FUNCT_1.apply (foldFamily F f X Y hY) C =
      setwiseFold F C f X Y hY hC := by
  classical
  unfold foldFamily
  rw [(Classical.choose_spec (FUNCT_1.sch_Lambda (FINSUB_1.Fin X)
    (fun C => if hC : C ∈ FINSUB_1.Fin X
      then setwiseFold F C f X Y hY hC else defaultElement Y hY))).2.2 C hC,
    dif_pos hC]

private theorem foldFamily_isFunctionOf {F f X Y : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F Y)
    (hf : FUNCT_2.isFunctionOf f X Y) (hc : BINOP_1.isCommutative F Y)
    (ha : BINOP_1.isAssociative F Y) :
    FUNCT_2.isFunctionOf (foldFamily F f X Y hY) (FINSUB_1.Fin X) Y :=
  FUNCT_2.functionOf_of (foldFamily_isFunction F f X Y hY)
    (foldFamily_dom F f X Y hY)
    (fun y hy => by
      obtain ⟨C, hC, hey⟩ :=
        (FUNCT_1.def3 (foldFamily_isFunction F f X Y hY).2).mp hy
      rw [hey, foldFamily_apply hY (foldFamily_dom F f X Y hY ▸ hC)]
      exact setwiseFold_mem_all hY
        (foldFamily_dom F f X Y hY ▸ hC) hF hf hc ha)

/-- The exact witness package occurring in Mizar `Def3`. -/
def FoldWitness (F B f X Y IT G : TarskiSet.{u}) : Prop :=
  FUNCT_2.isFunctionOf G (FINSUB_1.Fin X) Y ∧
  IT = FUNCT_1.apply G B ∧
  (∀ e, e ∈ Y → BINOP_1.is_a_unity_wrt e F Y →
    FUNCT_1.apply G (∅ : TarskiSet.{u}) = e) ∧
  (∀ x, x ∈ X →
    FUNCT_1.apply G (TARSKI.singleton x) = FUNCT_1.apply f x) ∧
  ∀ C, C ∈ FINSUB_1.Fin X → C ⊆ B → C ≠ (∅ : TarskiSet.{u}) →
    ∀ x, x ∈ X → x ∈ B \ C →
      FUNCT_1.apply G (C ∪ TARSKI.singleton x) =
        BINOP_1.apply2 F (FUNCT_1.apply G C) (FUNCT_1.apply f x)

/-- `SETWISEO:def 3`: the finite setwise fold is exactly the unique value
realizing Mizar's auxiliary function on `Fin X`. -/
theorem def3 {F B f X Y IT : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (_hIT : IT ∈ Y)
    (hB : B ∈ FINSUB_1.Fin X)
    (hcond : B ≠ (∅ : TarskiSet.{u}) ∨ isHavingAUnity F Y)
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y) :
    IT = setwiseFold F B f X Y hY hB ↔
      ∃ G, FoldWitness F B f X Y IT G := by
  let H := foldFamily F f X Y hY
  have hHF : FUNCT_2.isFunctionOf H (FINSUB_1.Fin X) Y :=
    foldFamily_isFunctionOf hY hF hf hc ha
  constructor
  · intro hIT
    refine ⟨H, hHF, hIT.trans (foldFamily_apply hY hB).symm, ?_, ?_, ?_⟩
    · intro e heY he
      let hu : isHavingAUnity F Y :=
        ⟨e, SUBSET_1.isElement_of heY, he⟩
      calc
        FUNCT_1.apply H (∅ : TarskiSet.{u}) =
            setwiseFold F (∅ : TarskiSet.{u}) f X Y hY
              (empty_mem_Fin X) := foldFamily_apply hY (empty_mem_Fin X)
        _ = unity F Y := th31_aux (F := F) (X := X) (f := f) hY hc ha hu
        _ = e := BINOP_1.th10 (unity_isElement hu)
          (SUBSET_1.isElement_of heY) (unity_spec hu) he
    · intro x hx
      rw [foldFamily_apply hY (singleton_mem_Fin_aux hx),
        th17_aux hY hx hF hf hc ha]
    · intro C hC hCB hneC x hx hxBC
      have hxC : x ∉ C := fun h => (XBOOLE_0.def5 B C x).mp hxBC |>.2 h
      rw [foldFamily_apply hY (union_mem_Fin hC (singleton_mem_Fin_aux hx)),
        foldFamily_apply hY hC]
      exact setwiseFold_insert_fresh hY hC hx hxC hneC hF hf hc ha
  · rintro ⟨G, hGF, hIT, hzero, hsingle, hstep⟩
    have hEq : ∀ C, C ∈ FINSUB_1.Fin X →
        C = (∅ : TarskiSet.{u}) ∨
          (C ⊆ B → FUNCT_1.apply G C = FUNCT_1.apply H C) := by
      apply FinSubInd1 hX
        (fun C => C = (∅ : TarskiSet.{u}) ∨
          (C ⊆ B → FUNCT_1.apply G C = FUNCT_1.apply H C))
      · exact Or.inl rfl
      · intro C x hC hx ih hxC
        right
        intro hUB
        have hCB : C ⊆ B :=
          XBOOLE_1.th1
            (XBOOLE_1.th7 (X := C) (Y := TARSKI.singleton x)) hUB
        have hxB : x ∈ B := hUB x
          ((XBOOLE_0.def3 C (TARSKI.singleton x) x).mpr
            (Or.inr ((singleton_iff x x).mpr rfl)))
        by_cases hneC : C = (∅ : TarskiSet.{u})
        · have hUeq : C ∪ TARSKI.singleton x = TARSKI.singleton x := by
            rw [hneC]
            exact XBOOLE_1.th12 XBOOLE_1.th2
          rw [hUeq, hsingle x hx,
            foldFamily_apply hY (singleton_mem_Fin_aux hx),
            th17_aux hY hx hF hf hc ha]
        · have ihEq : FUNCT_1.apply G C = FUNCT_1.apply H C :=
            ih.resolve_left hneC hCB
          have hxBC : x ∈ B \ C :=
            (XBOOLE_0.def5 B C x).mpr ⟨hxB, hxC⟩
          rw [hstep C hC hCB hneC x hx hxBC, ihEq,
            foldFamily_apply hY hC,
            foldFamily_apply hY (union_mem_Fin hC (singleton_mem_Fin_aux hx))]
          exact (setwiseFold_insert_fresh hY hC hx hxC hneC
            hF hf hc ha).symm
    rcases hEq B hB with hB0 | heq
    · have hu : isHavingAUnity F Y :=
        hcond.resolve_left (fun hne => hne hB0)
      have hGY := hzero (unity F Y)
        (SUBSET_1.isElement_mem (fun he => hY (XBOOLE_0.empty_eq he))
          (unity_isElement hu)) (unity_spec hu)
      calc
        IT = FUNCT_1.apply G B := hIT
        _ = unity F Y := by rw [hB0]; exact hGY
        _ = setwiseFold F B f X Y hY hB := by
          rw [(setwiseFold_congr hY hB (empty_mem_Fin X) hB0).trans
            (th31_aux hY hc ha hu)]
    · calc
        IT = FUNCT_1.apply G B := hIT
        _ = FUNCT_1.apply H B := heq (subset_refl B)
        _ = setwiseFold F B f X Y hY hB := foldFamily_apply hY hB

/-- `SETWISEO:16` (`Th16`): idempotence strengthens `Def3` by allowing
the inserted point to be any point of `B`, including one already present. -/
theorem th16 {F X Y B f IT : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hITY : IT ∈ Y)
    (hB : B ∈ FINSUB_1.Fin X)
    (hcond : B ≠ (∅ : TarskiSet.{u}) ∨ isHavingAUnity F Y)
    (hF : BINOP_1.isBinOp F Y) (hf : FUNCT_2.isFunctionOf f X Y)
    (hi : BINOP_1.isIdempotent F Y)
    (hc : BINOP_1.isCommutative F Y) (ha : BINOP_1.isAssociative F Y) :
    IT = setwiseFold F B f X Y hY hB ↔
      ∃ G, FUNCT_2.isFunctionOf G (FINSUB_1.Fin X) Y ∧
        IT = FUNCT_1.apply G B ∧
        (∀ e, e ∈ Y → BINOP_1.is_a_unity_wrt e F Y →
          FUNCT_1.apply G (∅ : TarskiSet.{u}) = e) ∧
        (∀ x, x ∈ X →
          FUNCT_1.apply G (TARSKI.singleton x) = FUNCT_1.apply f x) ∧
        ∀ C, C ∈ FINSUB_1.Fin X → C ⊆ B → C ≠ (∅ : TarskiSet.{u}) →
          ∀ x, x ∈ X → x ∈ B →
            FUNCT_1.apply G (C ∪ TARSKI.singleton x) =
              BINOP_1.apply2 F (FUNCT_1.apply G C) (FUNCT_1.apply f x) := by
  constructor
  · intro hIT
    let H := foldFamily F f X Y hY
    refine ⟨H, foldFamily_isFunctionOf hY hF hf hc ha,
      hIT.trans (foldFamily_apply hY hB).symm, ?_, ?_, ?_⟩
    · intro e heY he
      let hu : isHavingAUnity F Y := ⟨e, SUBSET_1.isElement_of heY, he⟩
      calc
        FUNCT_1.apply H (∅ : TarskiSet.{u}) =
            setwiseFold F (∅ : TarskiSet.{u}) f X Y hY
              (empty_mem_Fin X) := foldFamily_apply hY (empty_mem_Fin X)
        _ = unity F Y := th31_aux (F := F) (X := X) (f := f) hY hc ha hu
        _ = e := BINOP_1.th10 (unity_isElement hu)
          (SUBSET_1.isElement_of heY) (unity_spec hu) he
    · intro x hx
      rw [foldFamily_apply hY (singleton_mem_Fin_aux hx),
        th17_aux hY hx hF hf hc ha]
    · intro C hC hCB hneC x hx hxB
      rw [foldFamily_apply hY (union_mem_Fin hC (singleton_mem_Fin_aux hx)),
        foldFamily_apply hY hC]
      exact th20_aux hY hC hneC hx hF hf hi hc ha
  · rintro ⟨G, hGF, hIT, hzero, hsingle, hstep⟩
    apply (def3 hX hY hITY hB hcond hF hf hc ha).2
    refine ⟨G, hGF, hIT, hzero, hsingle, ?_⟩
    intro C hC hCB hneC x hx hxBC
    exact hstep C hC hCB hneC x hx ((XBOOLE_0.def5 B C x).mp hxBC).1

/-! ## Finite union -/

/-- `SETWISEO:def 4`: union as a binary operation on `Fin A`. -/
noncomputable def FinUnionOp (A : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (BINOP_1.sch_Lambda2
    (FINSUB_1.Fin A) (FINSUB_1.Fin A) (FINSUB_1.Fin A)
    (fun x y => x ∪ y)
    (fun _ _ hx hy => union_mem_Fin hx hy))

theorem FinUnionOp_isBinOp (A : TarskiSet.{u}) :
    BINOP_1.isBinOp (FinUnionOp A) (FINSUB_1.Fin A) :=
  (Classical.choose_spec (BINOP_1.sch_Lambda2
    (FINSUB_1.Fin A) (FINSUB_1.Fin A) (FINSUB_1.Fin A)
    (fun x y => x ∪ y)
    (fun _ _ hx hy => union_mem_Fin hx hy))).1

theorem def4 {A x y : TarskiSet.{u}}
    (hx : x ∈ FINSUB_1.Fin A) (hy : y ∈ FINSUB_1.Fin A) :
    BINOP_1.apply2 (FinUnionOp A) x y = x ∪ y :=
  (Classical.choose_spec (BINOP_1.sch_Lambda2
    (FINSUB_1.Fin A) (FINSUB_1.Fin A) (FINSUB_1.Fin A)
    (fun x y => x ∪ y)
    (fun _ _ hx hy => union_mem_Fin hx hy))).2 x y hx hy

private theorem finElement_mem {A x : TarskiSet.{u}}
    (hx : SUBSET_1.isElement x (FINSUB_1.Fin A)) :
    x ∈ FINSUB_1.Fin A :=
  SUBSET_1.isElement_mem
    (fun he => FINSUB_1.Fin_nonempty A (XBOOLE_0.empty_eq he)) hx

/-- `SETWISEO:37` (`Th37`). -/
theorem th37 (A : TarskiSet.{u}) :
    BINOP_1.isIdempotent (FinUnionOp A) (FINSUB_1.Fin A) := by
  intro x hx
  have hx' := finElement_mem hx
  rw [def4 hx' hx']
  exact XBOOLE_0.union_idem x

/-- `SETWISEO:38` (`Th38`). -/
theorem th38 (A : TarskiSet.{u}) :
    BINOP_1.isCommutative (FinUnionOp A) (FINSUB_1.Fin A) := by
  intro x y hx hy
  have hx' := finElement_mem hx
  have hy' := finElement_mem hy
  rw [def4 hx' hy', def4 hy' hx']
  exact XBOOLE_0.union_comm x y

/-- `SETWISEO:39` (`Th39`). -/
theorem th39 (A : TarskiSet.{u}) :
    BINOP_1.isAssociative (FinUnionOp A) (FINSUB_1.Fin A) := by
  intro x y z hx hy hz
  have hx' := finElement_mem hx
  have hy' := finElement_mem hy
  have hz' := finElement_mem hz
  have hyz := union_mem_Fin hy' hz'
  have hxy := union_mem_Fin hx' hy'
  rw [def4 hy' hz', def4 hx' hyz, def4 hx' hy', def4 hxy hz']
  exact XBOOLE_1.th4.symm

/-- `SETWISEO:40` (`Th40`). -/
theorem th40 (A : TarskiSet.{u}) :
    BINOP_1.is_a_unity_wrt (emptyFin A) (FinUnionOp A)
      (FINSUB_1.Fin A) := by
  apply BINOP_1.th3.mpr
  intro x hx
  have hx' := finElement_mem hx
  constructor
  · unfold emptyFin
    rw [def4 (empty_mem_Fin A) hx']
    exact XBOOLE_1.th12 XBOOLE_1.th2
  · unfold emptyFin
    rw [def4 hx' (empty_mem_Fin A), XBOOLE_0.union_comm]
    exact XBOOLE_1.th12 XBOOLE_1.th2

/-- `SETWISEO:41` (`Th41`). -/
theorem th41 (A : TarskiSet.{u}) :
    isHavingAUnity (FinUnionOp A) (FINSUB_1.Fin A) :=
  ⟨emptyFin A, SUBSET_1.isElement_of (empty_mem_Fin A), th40 A⟩

/-- Absolute slot 42. -/
theorem th42 (A : TarskiSet.{u}) :
    BINOP_1.is_a_unity_wrt
      (unity (FinUnionOp A) (FINSUB_1.Fin A))
      (FinUnionOp A) (FINSUB_1.Fin A) :=
  unity_spec (th41 A)

/-- `SETWISEO:43` (`Th43`). -/
theorem th43 (A : TarskiSet.{u}) :
    unity (FinUnionOp A) (FINSUB_1.Fin A) = (∅ : TarskiSet.{u}) :=
  BINOP_1.th10 (unity_isElement (th41 A))
    (SUBSET_1.isElement_of (empty_mem_Fin A))
    (unity_spec (th41 A)) (th40 A)

/-- `SETWISEO:def 5`: finite union is definitionally the specialization of
the setwise fold to `FinUnionOp`. -/
noncomputable def FinUnion {X A B f : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (_hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin A)) : TarskiSet.{u} :=
  setwiseFold (FinUnionOp A) B f X (FINSUB_1.Fin A)
    (FINSUB_1.Fin_nonempty A) hB

theorem def5 {X A B f : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin A)) :
    FinUnion hX hB hf =
      setwiseFold (FinUnionOp A) B f X (FINSUB_1.Fin A)
        (FINSUB_1.Fin_nonempty A) hB := rfl

/-- `SETWISEO:44`. -/
theorem th44 {X A f i : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin A)) (hi : i ∈ X) :
    FinUnion hX (singleton_mem_Fin hX hi) hf = FUNCT_1.apply f i := by
  rw [def5, th17_aux (F := FinUnionOp A) (hY := FINSUB_1.Fin_nonempty A)
    hi (FinUnionOp_isBinOp A) hf (th38 A) (th39 A)]

/-- `SETWISEO:45`. -/
theorem th45 {X A f i j : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin A))
    (hi : i ∈ X) (hj : j ∈ X) :
    FinUnion hX (upair_mem_Fin hX hi hj) hf =
      FUNCT_1.apply f i ∪ FUNCT_1.apply f j := by
  rw [def5, th18_aux (F := FinUnionOp A) (hY := FINSUB_1.Fin_nonempty A)
    hi hj (FinUnionOp_isBinOp A) hf (th37 A) (th38 A) (th39 A),
    def4 (FUNCT_2.th5 hf (FINSUB_1.Fin_nonempty A) hi)
      (FUNCT_2.th5 hf (FINSUB_1.Fin_nonempty A) hj)]

/-- `SETWISEO:46`. -/
theorem th46 {X A f i j k : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin A))
    (hi : i ∈ X) (hj : j ∈ X) (hk : k ∈ X) :
    FinUnion hX (enumset3_mem_Fin hX hi hj hk) hf =
      FUNCT_1.apply f i ∪ FUNCT_1.apply f j ∪ FUNCT_1.apply f k := by
  rw [def5, th19_aux (F := FinUnionOp A) (hY := FINSUB_1.Fin_nonempty A)
    hi hj hk (FinUnionOp_isBinOp A) hf (th37 A) (th38 A) (th39 A),
    def4 (FUNCT_2.th5 hf (FINSUB_1.Fin_nonempty A) hi)
      (FUNCT_2.th5 hf (FINSUB_1.Fin_nonempty A) hj),
    def4 (union_mem_Fin
      (FUNCT_2.th5 hf (FINSUB_1.Fin_nonempty A) hi)
      (FUNCT_2.th5 hf (FINSUB_1.Fin_nonempty A) hj))
      (FUNCT_2.th5 hf (FINSUB_1.Fin_nonempty A) hk)]

/-- `SETWISEO:47` (`Th47`). -/
theorem th47 {X A f : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin A)) :
    FinUnion hX (empty_mem_Fin X) hf = (∅ : TarskiSet.{u}) := by
  calc
    FinUnion hX (empty_mem_Fin X) hf =
        setwiseFold (FinUnionOp A) (∅ : TarskiSet.{u}) f X
          (FINSUB_1.Fin A) (FINSUB_1.Fin_nonempty A)
          (empty_mem_Fin X) := rfl
    _ = unity (FinUnionOp A) (FINSUB_1.Fin A) :=
      th31_aux (F := FinUnionOp A) (X := X) (f := f)
        (FINSUB_1.Fin_nonempty A) (th38 A) (th39 A) (th41 A)
    _ = (∅ : TarskiSet.{u}) := th43 A

/-- `SETWISEO:48` (`Th48`). -/
theorem th48 {X A B f i : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin A)) (hi : i ∈ X) :
    FinUnion hX (union_mem_Fin hB (singleton_mem_Fin hX hi)) hf =
      FinUnion hX hB hf ∪ FUNCT_1.apply f i := by
  rw [def5, th32_aux (F := FinUnionOp A) (hY := FINSUB_1.Fin_nonempty A)
    hB hi (FinUnionOp_isBinOp A) hf (th37 A) (th38 A) (th39 A) (th41 A),
    def4
      (setwiseFold_mem_all (FINSUB_1.Fin_nonempty A) hB
        (FinUnionOp_isBinOp A) hf (th38 A) (th39 A))
      (FUNCT_2.th5 hf (FINSUB_1.Fin_nonempty A) hi),
    ← def5 hX hB hf]

/-- `SETWISEO:49` (`Th49`). -/
theorem th49 {X A B f : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin A)) :
    FinUnion hX hB hf = TARSKI.union (RELAT_1.image f B) := by
  apply FinSubInd3 hX
    (fun C => ∀ hC : C ∈ FINSUB_1.Fin X,
      FinUnion hX hC hf = TARSKI.union (RELAT_1.image f C))
    (by
      intro h0
      unfold emptyFin at h0 ⊢
      rw [th47 hX hf]
      have he : RELAT_1.image f (∅ : TarskiSet.{u}) =
          (∅ : TarskiSet.{u}) := by
        apply XBOOLE_0.empty_eq
        rintro ⟨z, hz⟩
        obtain ⟨x, _, hx⟩ := (RELAT_1.def13 f ∅ z).mp hz
        exact (XBOOLE_0.empty_iff x).mp hx
      rw [he, ZFMISC_1.th2])
    (by
      intro C i hC hi ih hU
      rw [th48 hX hC hf hi, ih hC, RELAT_1.th120, ZFMISC_1.th78]
      change TARSKI.union (RELAT_1.image f C) ∪ FUNCT_1.apply f i =
        TARSKI.union (RELAT_1.image f C) ∪ TARSKI.union (RELAT_1.Im f i)
      rw [FUNCT_1.th59 (FUNCT_2.functionOf_isFunction hf).2
        (FUNCT_2.functionOf_dom_eq hf (FINSUB_1.Fin_nonempty A) ▸ hi),
        ZFMISC_1.th25])
    B hB hB

/-- `SETWISEO:50`. -/
theorem th50 {X A B₁ B₂ f : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u}))
    (hB₁ : B₁ ∈ FINSUB_1.Fin X) (hB₂ : B₂ ∈ FINSUB_1.Fin X)
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin A)) :
    FinUnion hX (union_mem_Fin hB₁ hB₂) hf =
      FinUnion hX hB₁ hf ∪ FinUnion hX hB₂ hf := by
  rw [th49 hX (union_mem_Fin hB₁ hB₂) hf, th49 hX hB₁ hf,
    th49 hX hB₂ hf, RELAT_1.th120, ZFMISC_1.th78]

/-- `SETWISEO:51`. -/
theorem th51 {X Y A B f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) (hf : FUNCT_2.isFunctionOf f X Y)
    (hg : FUNCT_2.isFunctionOf g Y (FINSUB_1.Fin A)) :
    FinUnion hY (lm1_aux hB hf) hg =
      FinUnion hX hB (comp_functionOf hY (FINSUB_1.Fin_nonempty A) hf hg) := by
  rw [th49 hY (lm1_aux hB hf) hg,
    th49 hX hB (comp_functionOf hY (FINSUB_1.Fin_nonempty A) hf hg),
    RELAT_1.th126]

/-- `SETWISEO:52` (`Th52`). -/
theorem th52 {A X Y G B f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hA : A ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) (hneB : B ≠ (∅ : TarskiSet.{u}))
    (hG : BINOP_1.isBinOp G A)
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin Y))
    (hg : FUNCT_2.isFunctionOf g (FINSUB_1.Fin Y) A)
    (hcG : BINOP_1.isCommutative G A)
    (haG : BINOP_1.isAssociative G A)
    (hiG : BINOP_1.isIdempotent G A)
    (hhom : ∀ x y, x ∈ FINSUB_1.Fin Y → y ∈ FINSUB_1.Fin Y →
      FUNCT_1.apply g (x ∪ y) =
        BINOP_1.apply2 G (FUNCT_1.apply g x) (FUNCT_1.apply g y)) :
    FUNCT_1.apply g (FinUnion hX hB hf) =
      setwiseFold G B (RELAT_1.comp f g) X A hA hB := by
  rw [def5 hX hB hf]
  exact th30 hX (FINSUB_1.Fin_nonempty Y) hA hB hneB
    (FinUnionOp_isBinOp Y) hG hf hg
    (th37 Y) (th38 Y) (th39 Y) hiG hcG haG
    (fun x y hx hy => by rw [def4 hx hy]; exact hhom x y hx hy)

/-- `SETWISEO:53` (`Th53`). -/
theorem th53 {X Y Z G B f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hZ : Z ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) (hG : BINOP_1.isBinOp G Z)
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin Y))
    (hg : FUNCT_2.isFunctionOf g (FINSUB_1.Fin Y) Z)
    (hcG : BINOP_1.isCommutative G Z)
    (haG : BINOP_1.isAssociative G Z)
    (hiG : BINOP_1.isIdempotent G Z) (huG : isHavingAUnity G Z)
    (h0 : FUNCT_1.apply g (∅ : TarskiSet.{u}) = unity G Z)
    (hhom : ∀ x y, x ∈ FINSUB_1.Fin Y → y ∈ FINSUB_1.Fin Y →
      FUNCT_1.apply g (x ∪ y) =
        BINOP_1.apply2 G (FUNCT_1.apply g x) (FUNCT_1.apply g y)) :
    FUNCT_1.apply g (FinUnion hX hB hf) =
      setwiseFold G B (RELAT_1.comp f g) X Z hZ hB := by
  rw [def5 hX hB hf]
  exact th36 hX (FINSUB_1.Fin_nonempty Y) hZ hB
    (FinUnionOp_isBinOp Y) hG hf hg
    (th37 Y) (th38 Y) (th39 Y) (th41 Y)
    hiG hcG haG huG
    (by rw [th43 Y]; exact h0)
    (fun x y hx hy => by rw [def4 hx hy]; exact hhom x y hx hy)

/-- `SETWISEO:def 6`: singleton map. -/
noncomputable def singletonMap (A : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (FUNCT_1.sch_Lambda A TARSKI.singleton)

theorem singletonMap_isFunction (A : TarskiSet.{u}) :
    FUNCT_1.isFunction (singletonMap A) :=
  (Classical.choose_spec (FUNCT_1.sch_Lambda A TARSKI.singleton)).1

theorem singletonMap_dom (A : TarskiSet.{u}) :
    RELAT_1.dom (singletonMap A) = A :=
  (Classical.choose_spec (FUNCT_1.sch_Lambda A TARSKI.singleton)).2.1

theorem def6 {A x : TarskiSet.{u}} (hx : x ∈ A) :
    FUNCT_1.apply (singletonMap A) x = TARSKI.singleton x :=
  (Classical.choose_spec (FUNCT_1.sch_Lambda A TARSKI.singleton)).2.2 x hx

theorem singletonMap_isFunctionOf (A : TarskiSet.{u}) :
    FUNCT_2.isFunctionOf (singletonMap A) A (FINSUB_1.Fin A) :=
  FUNCT_2.functionOf_of (singletonMap_isFunction A) (singletonMap_dom A)
    (fun y hy => by
      obtain ⟨x, hx, heq⟩ :=
        (FUNCT_1.def3 (singletonMap_isFunction A).2).mp hy
      rw [heq, def6 (singletonMap_dom A ▸ hx)]
      exact singleton_mem_Fin_aux (singletonMap_dom A ▸ hx))

/-- `SETWISEO:54` (`Th54`). -/
theorem th54 {A f : TarskiSet.{u}} (_hA : A ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f A (FINSUB_1.Fin A)) :
    f = singletonMap A ↔
      ∀ x, x ∈ A → FUNCT_1.apply f x = TARSKI.singleton x := by
  have hfun := FUNCT_2.functionOf_isFunction hf
  have hd := FUNCT_2.functionOf_dom_eq hf (FINSUB_1.Fin_nonempty A)
  constructor
  · intro h x hx
    rw [h]
    exact def6 hx
  · intro h
    apply FUNCT_1.th2 hfun (singletonMap_isFunction A)
      (hd.trans (singletonMap_dom A).symm)
    intro x hx
    rw [h x (hd ▸ hx)]
    exact (def6 (hd ▸ hx)).symm

/-- `SETWISEO:55` (`Th55`). -/
theorem th55 {A x y : TarskiSet.{u}} (_hA : A ≠ (∅ : TarskiSet.{u}))
    (hy : y ∈ A) :
    x ∈ FUNCT_1.apply (singletonMap A) y ↔ x = y := by
  rw [def6 hy, singleton_iff]

/-- Absolute slot 56. -/
theorem th56 {A x y z : TarskiSet.{u}} (hA : A ≠ (∅ : TarskiSet.{u}))
    (hz : z ∈ A)
    (hx : x ∈ FUNCT_1.apply (singletonMap A) z)
    (hy : y ∈ FUNCT_1.apply (singletonMap A) z) : x = y :=
  (th55 hA hz).mp hx |>.trans ((th55 hA hz).mp hy).symm

/-- `SETWISEO:Lm2`. -/
theorem lm2 {D X P f : TarskiSet.{u}}
    (_hD : D ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X D) :
    RELAT_1.image f P ⊆ D :=
  XBOOLE_1.th1 RELAT_1.th111 (FUNCT_2.functionOf_rng_sub hf)

/-- `SETWISEO:57` (`Th57`). -/
theorem th57 {X A B f x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin A)) :
    x ∈ FinUnion hX hB hf ↔
      ∃ i, i ∈ X ∧ i ∈ B ∧ x ∈ FUNCT_1.apply f i := by
  rw [th49 hX hB hf]
  have hBX := (FINSUB_1.def5 X B).mp hB |>.1
  constructor
  · intro hx
    obtain ⟨Z, hxZ, hZ⟩ := (union_iff _ _).mp hx
    obtain ⟨i, hp, hi⟩ := (RELAT_1.def13 f B Z).mp hZ
    exact ⟨i, hBX i hi, hi, Eq.subst (motive := fun s => x ∈ s)
      (FUNCT_1.apply_of_mem (FUNCT_2.functionOf_isFunction hf).2 hp).symm hxZ⟩
  · rintro ⟨i, hiX, hi, hx⟩
    apply (union_iff _ _).mpr
    exact ⟨FUNCT_1.apply f i, hx,
      (RELAT_1.def13 f B _).mpr
        ⟨i, FUNCT_1.apply_spec
          (FUNCT_2.functionOf_dom_eq hf (FINSUB_1.Fin_nonempty A) ▸
            hiX), hi⟩⟩

/-- Absolute slot 58. -/
theorem th58 {X B : TarskiSet.{u}} (hX : X ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X) :
    FinUnion hX hB (singletonMap_isFunctionOf X) = B := by
  let hf := singletonMap_isFunctionOf X
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    obtain ⟨i, _, hi, hxi⟩ := (th57 hX hB hf).mp hx
    exact (th55 hX (th9_aux hB hi)).mp hxi ▸ hi
  · intro hx
    exact (th57 hX hB hf).mpr
      ⟨x, th9_aux hB hx, hx, (th55 hX (th9_aux hB hx)).mpr rfl⟩

/-- Absolute slot 59: finite-union homomorphisms commute with `FinUnion`. -/
theorem th59 {X Y Z B f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hB : B ∈ FINSUB_1.Fin X)
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin Y))
    (hg : FUNCT_2.isFunctionOf g (FINSUB_1.Fin Y) (FINSUB_1.Fin Z))
    (h0 : FUNCT_1.apply g (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}))
    (hhom : ∀ x y, x ∈ FINSUB_1.Fin Y → y ∈ FINSUB_1.Fin Y →
      FUNCT_1.apply g (x ∪ y) =
        FUNCT_1.apply g x ∪ FUNCT_1.apply g y) :
    FUNCT_1.apply g (FinUnion hX hB hf) =
      FinUnion hX hB
        (comp_functionOf (FINSUB_1.Fin_nonempty Y)
          (FINSUB_1.Fin_nonempty Z) hf hg) := by
  calc
    FUNCT_1.apply g (FinUnion hX hB hf) =
        setwiseFold (FinUnionOp Z) B (RELAT_1.comp f g) X
          (FINSUB_1.Fin Z) (FINSUB_1.Fin_nonempty Z) hB :=
      th53 hX (FINSUB_1.Fin_nonempty Z) hB (FinUnionOp_isBinOp Z)
        hf hg (th38 Z) (th39 Z) (th37 Z) (th41 Z)
        (by rw [th43 Z]; exact h0)
        (fun x y hx hy => by
          rw [def4 (A := Z)
            (FUNCT_2.th5 hg (FINSUB_1.Fin_nonempty Z) hx)
            (FUNCT_2.th5 hg (FINSUB_1.Fin_nonempty Z) hy)]
          exact hhom x y hx hy)
    _ = FinUnion hX hB
          (comp_functionOf (FINSUB_1.Fin_nonempty Y)
            (FINSUB_1.Fin_nonempty Z) hf hg) :=
      (def5 hX hB
        (comp_functionOf (FINSUB_1.Fin_nonempty Y)
          (FINSUB_1.Fin_nonempty Z) hf hg)).symm






