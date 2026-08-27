import MizarCCL.MCART_1
import MizarCCL.ORDINAL1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/domain_1.miz`.
Authors: Andrzej Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Domains and Their Cartesian Products

1–1 Lean rendering of Mizar article `DOMAIN_1`
(`vendor/mml/domain_1.miz`). Import is `MCART_1` and `ORDINAL1`
(last queue deps; `ORDINAL1` for the `c=-linear` registration).
-/

universe u

open TarskiSet TARSKI

namespace DOMAIN_1

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

private theorem ne_imp_not_empty {X : TarskiSet.{u}}
    (h : X ≠ (∅ : TarskiSet.{u})) : ¬ XBOOLE_0.isEmpty X :=
  fun he => h (XBOOLE_0.empty_eq he)

private theorem nonempty_of_mem {X x : TarskiSet.{u}} (hx : x ∈ X) :
    X ≠ (∅ : TarskiSet.{u}) :=
  fun hempty => (XBOOLE_0.empty_iff x).mp
    (Eq.subst (motive := fun s => x ∈ s) hempty hx)

private theorem symmdiff_mem_xor (X Y x : TarskiSet.{u}) :
    x ∈ X ∆ Y ↔ (x ∈ X ∧ x ∉ Y) ∨ (x ∉ X ∧ x ∈ Y) := by
  have hU : x ∈ X ∆ Y ↔ x ∈ (X \ Y) ∪ (Y \ X) := by
    have heq : X ∆ Y = (X \ Y) ∪ (Y \ X) := XBOOLE_0.def6 X Y
    exact Iff.of_eq (congrArg (fun s => x ∈ s) heq)
  constructor
  · intro hx
    cases (XBOOLE_0.def3 (X \ Y) (Y \ X) x).mp (hU.mp hx) with
    | inl h =>
      have ⟨hX, hY⟩ := (XBOOLE_0.def5 X Y x).mp h
      exact Or.inl ⟨hX, hY⟩
    | inr h =>
      have ⟨hY, hX⟩ := (XBOOLE_0.def5 Y X x).mp h
      exact Or.inr ⟨hX, hY⟩
  · intro hx
    apply hU.mpr
    apply (XBOOLE_0.def3 (X \ Y) (Y \ X) x).mpr
    cases hx with
    | inl h =>
      exact Or.inl ((XBOOLE_0.def5 X Y x).mpr h)
    | inr h =>
      exact Or.inr ((XBOOLE_0.def5 Y X x).mpr ⟨h.2, h.1⟩)

/-! ## Separation / Fraenkel helpers -/

/-- Separation `{ x ∈ A : P x }`. -/
noncomputable def sep (A : TarskiSet.{u}) (P : TarskiSet.{u} → Prop) :
    TarskiSet.{u} :=
  Classical.choose (XBOOLE_0.sch_separation A P)

theorem sep_iff (A : TarskiSet.{u}) (P : TarskiSet.{u} → Prop)
    (x : TarskiSet.{u}) :
    x ∈ sep A P ↔ x ∈ A ∧ P x :=
  Classical.choose_spec (XBOOLE_0.sch_separation A P) x

/-- `{ x1 : P[x1] }` with `x1` ranging over `Element of X1`. -/
noncomputable def fraenkel1 (X1 : TarskiSet.{u}) (P : TarskiSet.{u} → Prop) :
    TarskiSet.{u} :=
  sep X1 P

theorem fraenkel1_iff (X1 : TarskiSet.{u}) (P : TarskiSet.{u} → Prop)
    (a : TarskiSet.{u}) :
    a ∈ fraenkel1 X1 P ↔ a ∈ X1 ∧ P a :=
  sep_iff X1 P a

/-- `{ [x1,x2] : P[x1,x2] }`. -/
noncomputable def fraenkel2 (X1 X2 : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop) : TarskiSet.{u} :=
  sep (ZFMISC_1.product X1 X2)
    (fun a => ∃ x1 x2, a = TARSKI.pair x1 x2 ∧ x1 ∈ X1 ∧ x2 ∈ X2 ∧ P x1 x2)

theorem fraenkel2_iff (X1 X2 : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop) (a : TarskiSet.{u}) :
    a ∈ fraenkel2 X1 X2 P ↔
      ∃ x1 x2, a = TARSKI.pair x1 x2 ∧ x1 ∈ X1 ∧ x2 ∈ X2 ∧ P x1 x2 := by
  constructor
  · intro ha
    exact And.right ((sep_iff _ _ a).mp ha)
  · intro ⟨x1, x2, heq, hx1, hx2, hP⟩
    exact (sep_iff _ _ a).mpr
      ⟨(ZFMISC_1.def2 X1 X2 a).mpr ⟨x1, x2, hx1, hx2, heq⟩,
        ⟨x1, x2, heq, hx1, hx2, hP⟩⟩

/-- `{ [x1,x2,x3] : P[x1,x2,x3] }`. -/
noncomputable def fraenkel3 (X1 X2 X3 : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop) :
    TarskiSet.{u} :=
  sep (ZFMISC_1.product3 X1 X2 X3)
    (fun a => ∃ x1 x2 x3, a = XTUPLE_0.triple x1 x2 x3 ∧
      x1 ∈ X1 ∧ x2 ∈ X2 ∧ x3 ∈ X3 ∧ P x1 x2 x3)

theorem fraenkel3_iff (X1 X2 X3 : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop)
    (a : TarskiSet.{u}) :
    a ∈ fraenkel3 X1 X2 X3 P ↔
      ∃ x1 x2 x3, a = XTUPLE_0.triple x1 x2 x3 ∧
        x1 ∈ X1 ∧ x2 ∈ X2 ∧ x3 ∈ X3 ∧ P x1 x2 x3 := by
  constructor
  · intro ha
    exact And.right ((sep_iff _ _ a).mp ha)
  · intro ⟨x1, x2, x3, heq, hx1, hx2, hx3, hP⟩
    have hin : XTUPLE_0.triple x1 x2 x3 ∈ ZFMISC_1.product3 X1 X2 X3 :=
      (MCART_1.th69 x1 x2 x3 X1 X2 X3).mpr ⟨hx1, hx2, hx3⟩
    exact (sep_iff _ _ a).mpr
      ⟨Eq.subst (motive := fun s => s ∈ ZFMISC_1.product3 X1 X2 X3)
          heq.symm hin,
        ⟨x1, x2, x3, heq, hx1, hx2, hx3, hP⟩⟩

/-- `{ [x1,x2,x3,x4] : P[...] }`. -/
noncomputable def fraenkel4 (X1 X2 X3 X4 : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop) :
    TarskiSet.{u} :=
  sep (ZFMISC_1.product4 X1 X2 X3 X4)
    (fun a => ∃ x1 x2 x3 x4, a = XTUPLE_0.quadruple x1 x2 x3 x4 ∧
      x1 ∈ X1 ∧ x2 ∈ X2 ∧ x3 ∈ X3 ∧ x4 ∈ X4 ∧ P x1 x2 x3 x4)

theorem fraenkel4_iff (X1 X2 X3 X4 : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop)
    (a : TarskiSet.{u}) :
    a ∈ fraenkel4 X1 X2 X3 X4 P ↔
      ∃ x1 x2 x3 x4, a = XTUPLE_0.quadruple x1 x2 x3 x4 ∧
        x1 ∈ X1 ∧ x2 ∈ X2 ∧ x3 ∈ X3 ∧ x4 ∈ X4 ∧ P x1 x2 x3 x4 := by
  constructor
  · intro ha
    exact And.right ((sep_iff _ _ a).mp ha)
  · intro ⟨x1, x2, x3, x4, heq, hx1, hx2, hx3, hx4, hP⟩
    have hin : XTUPLE_0.quadruple x1 x2 x3 x4 ∈
        ZFMISC_1.product4 X1 X2 X3 X4 :=
      (MCART_1.th80 x1 x2 x3 x4 X1 X2 X3 X4).mpr ⟨hx1, hx2, hx3, hx4⟩
    exact (sep_iff _ _ a).mpr
      ⟨Eq.subst (motive := fun s => s ∈ ZFMISC_1.product4 X1 X2 X3 X4)
          heq.symm hin,
        ⟨x1, x2, x3, x4, heq, hx1, hx2, hx3, hx4, hP⟩⟩

/-- `{ F(x) where x is Element of A : P[x] }`. -/
noncomputable def imageSep (A : TarskiSet.{u}) (F : TarskiSet.{u} → TarskiSet.{u})
    (P : TarskiSet.{u} → Prop) : TarskiSet.{u} :=
  Classical.choose
    (TARSKI.fraenkel A (fun y x => P y ∧ x = F y)
      (fun _y _x1 _x2 h1 h2 => h1.2.trans h2.2.symm))

theorem imageSep_iff (A : TarskiSet.{u}) (F : TarskiSet.{u} → TarskiSet.{u})
    (P : TarskiSet.{u} → Prop) (w : TarskiSet.{u}) :
    w ∈ imageSep A F P ↔ ∃ y, y ∈ A ∧ P y ∧ w = F y :=
  Classical.choose_spec
    (TARSKI.fraenkel A (fun y x => P y ∧ x = F y)
      (fun _y _x1 _x2 h1 h2 => h1.2.trans h2.2.symm)) w

private theorem imageSep2_functional {A B : TarskiSet.{u}}
    (F : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (p w1 w2 : TarskiSet.{u})
    (h1 : ∃ x y, p = TARSKI.pair x y ∧ x ∈ A ∧ y ∈ B ∧ P x y ∧ w1 = F x y)
    (h2 : ∃ x y, p = TARSKI.pair x y ∧ x ∈ A ∧ y ∈ B ∧ P x y ∧ w2 = F x y) :
    w1 = w2 := by
  obtain ⟨x1, y1, heq1, _, _, _, hw1⟩ := h1
  obtain ⟨x2, y2, heq2, _, _, _, hw2⟩ := h2
  have ⟨hx, hy⟩ := XTUPLE_0.th1 (heq1.symm.trans heq2)
  have hF : F x1 y1 = F x2 y2 :=
    Eq.subst (motive := fun s => F x1 y1 = F s y2) hx
      (Eq.subst (motive := fun s => F x1 y1 = F x1 s) hy rfl)
  exact hw1.trans (hF.trans hw2.symm)

/-- `{ F(x,y) where x ∈ A, y ∈ B : P[x,y] }`. -/
noncomputable def imageSep2 (A B : TarskiSet.{u})
    (F : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop) : TarskiSet.{u} :=
  Classical.choose
    (TARSKI.fraenkel (ZFMISC_1.product A B)
      (fun p w => ∃ x y, p = TARSKI.pair x y ∧ x ∈ A ∧ y ∈ B ∧ P x y ∧ w = F x y)
      (fun p w1 w2 h1 h2 => imageSep2_functional F P p w1 w2 h1 h2))

theorem imageSep2_iff (A B : TarskiSet.{u})
    (F : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop) (w : TarskiSet.{u}) :
    w ∈ imageSep2 A B F P ↔
      ∃ x y, x ∈ A ∧ y ∈ B ∧ P x y ∧ w = F x y := by
  have hspec := Classical.choose_spec
    (TARSKI.fraenkel (ZFMISC_1.product A B)
      (fun p w => ∃ x y, p = TARSKI.pair x y ∧ x ∈ A ∧ y ∈ B ∧ P x y ∧ w = F x y)
      (fun p w1 w2 h1 h2 => imageSep2_functional F P p w1 w2 h1 h2)) w
  constructor
  · intro hw
    obtain ⟨p, hp, hex⟩ := (hspec.mp hw)
    obtain ⟨x, y, _, hx, hy, hP, hwF⟩ := hex
    exact ⟨x, y, hx, hy, hP, hwF⟩
  · intro ⟨x, y, hx, hy, hP, hwF⟩
    have hp : TARSKI.pair x y ∈ ZFMISC_1.product A B :=
      (ZFMISC_1.th87 (x := x) (y := y) (X := A) (Y := B)).mpr ⟨hx, hy⟩
    exact hspec.mpr ⟨TARSKI.pair x y, hp, ⟨x, y, rfl, hx, hy, hP, hwF⟩⟩

/-! ## Domains and their elements -/

/-- Unlabeled `DOMAIN_1` (`Th1`). -/
theorem th1 {a X1 X2 : TarskiSet.{u}}
    (_h1 : X1 ≠ (∅ : TarskiSet.{u})) (_h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (ha : a ∈ ZFMISC_1.product X1 X2) :
    ∃ x1 x2, SUBSET_1.isElement x1 X1 ∧ SUBSET_1.isElement x2 X2 ∧
      a = TARSKI.pair x1 x2 := by
  obtain ⟨x1, x2, hx1, hx2, heq⟩ := (ZFMISC_1.def2 X1 X2 a).mp ha
  exact ⟨x1, x2, SUBSET_1.isElement_of hx1, SUBSET_1.isElement_of hx2, heq⟩

/-- Unlabeled `DOMAIN_1` (`Th2`). -/
theorem th2 {X1 X2 x y : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x (ZFMISC_1.product X1 X2))
    (hy : SUBSET_1.isElement y (ZFMISC_1.product X1 X2))
    (hfst : XTUPLE_0.fst x = XTUPLE_0.fst y)
    (hsnd : XTUPLE_0.snd x = XTUPLE_0.snd y) :
    x = y := by
  have hPne : ZFMISC_1.product X1 X2 ≠ (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := X1) (Y := X2)).mp hempty)
        (fun h => h1 h) (fun h => h2 h)
  have hx' : x ∈ ZFMISC_1.product X1 X2 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  have hy' : y ∈ ZFMISC_1.product X1 X2 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hy
  have hxeq : x = TARSKI.pair (XTUPLE_0.fst x) (XTUPLE_0.snd x) :=
    MCART_1.th22 h1 h2 hx'
  have hyeq : y = TARSKI.pair (XTUPLE_0.fst y) (XTUPLE_0.snd y) :=
    MCART_1.th22 h1 h2 hy'
  have hpair :
      TARSKI.pair (XTUPLE_0.fst x) (XTUPLE_0.snd x) =
        TARSKI.pair (XTUPLE_0.fst y) (XTUPLE_0.snd y) :=
    Eq.subst (motive := fun s =>
        TARSKI.pair (XTUPLE_0.fst x) (XTUPLE_0.snd x) =
          TARSKI.pair s (XTUPLE_0.snd y)) hfst
      (Eq.subst (motive := fun s =>
          TARSKI.pair (XTUPLE_0.fst x) (XTUPLE_0.snd x) =
            TARSKI.pair (XTUPLE_0.fst x) s) hsnd rfl)
  exact hxeq.trans (hpair.trans hyeq.symm)

/-- Coherence: `[x1,x2]` is `Element of [:X1,X2:]`. -/
theorem pair_isElement {X1 X2 x1 x2 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (hx1 : SUBSET_1.isElement x1 X1) (hx2 : SUBSET_1.isElement x2 X2) :
    SUBSET_1.isElement (TARSKI.pair x1 x2) (ZFMISC_1.product X1 X2) :=
  SUBSET_1.isElement_of
    ((ZFMISC_1.th87 (x := x1) (y := x2) (X := X1) (Y := X2)).mpr
      ⟨SUBSET_1.isElement_mem (ne_imp_not_empty h1) hx1,
        SUBSET_1.isElement_mem (ne_imp_not_empty h2) hx2⟩)

/-- Coherence: `x`1` is `Element of X1`. -/
theorem fst_isElement {X1 X2 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x (ZFMISC_1.product X1 X2)) :
    SUBSET_1.isElement (XTUPLE_0.fst x) X1 := by
  have hPne : ZFMISC_1.product X1 X2 ≠ (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := X1) (Y := X2)).mp hempty)
        (fun h => h1 h) (fun h => h2 h)
  exact SUBSET_1.isElement_of
    (MCART_1.th10
      (SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx)).1

/-- Coherence: `x`2` is `Element of X2`. -/
theorem snd_isElement {X1 X2 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x (ZFMISC_1.product X1 X2)) :
    SUBSET_1.isElement (XTUPLE_0.snd x) X2 := by
  have hPne : ZFMISC_1.product X1 X2 ≠ (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := X1) (Y := X2)).mp hempty)
        (fun h => h1 h) (fun h => h2 h)
  exact SUBSET_1.isElement_of
    (MCART_1.th10
      (SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx)).2

/-! ## Cartesian products of three sets -/

/-- `DOMAIN_1:3` (`Th3`) -/
theorem th3 {a X1 X2 X3 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) :
    a ∈ ZFMISC_1.product3 X1 X2 X3 ↔
      ∃ x1 x2 x3, SUBSET_1.isElement x1 X1 ∧ SUBSET_1.isElement x2 X2 ∧
        SUBSET_1.isElement x3 X3 ∧ a = XTUPLE_0.triple x1 x2 x3 := by
  constructor
  · intro ha
    obtain ⟨x1, x2, x3, hx1, hx2, hx3, heq⟩ := MCART_1.th68 ha
    exact ⟨x1, x2, x3, SUBSET_1.isElement_of hx1, SUBSET_1.isElement_of hx2,
      SUBSET_1.isElement_of hx3, heq⟩
  · intro ⟨x1, x2, x3, hx1, hx2, hx3, heq⟩
    have hin : XTUPLE_0.triple x1 x2 x3 ∈ ZFMISC_1.product3 X1 X2 X3 :=
      (MCART_1.th69 x1 x2 x3 X1 X2 X3).mpr
        ⟨SUBSET_1.isElement_mem (ne_imp_not_empty h1) hx1,
          SUBSET_1.isElement_mem (ne_imp_not_empty h2) hx2,
          SUBSET_1.isElement_mem (ne_imp_not_empty h3) hx3⟩
    exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product3 X1 X2 X3)
      heq.symm hin

/-- `DOMAIN_1:4` (`Th4`) -/
theorem th4 {D X1 X2 X3 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (_hD : D ≠ (∅ : TarskiSet.{u}))
    (h : ∀ a, a ∈ D ↔
      ∃ x1 x2 x3, SUBSET_1.isElement x1 X1 ∧ SUBSET_1.isElement x2 X2 ∧
        SUBSET_1.isElement x3 X3 ∧ a = XTUPLE_0.triple x1 x2 x3) :
    D = ZFMISC_1.product3 X1 X2 X3 := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    obtain ⟨x1, x2, x3, hx1, hx2, hx3, heq⟩ := (h a).mp ha
    exact (th3 h1 h2 h3).mpr ⟨x1, x2, x3, hx1, hx2, hx3, heq⟩
  · intro ha
    obtain ⟨x1, x2, x3, hx1, hx2, hx3, heq⟩ := (th3 h1 h2 h3).mp ha
    exact (h a).mpr ⟨x1, x2, x3, hx1, hx2, hx3, heq⟩

/-- Unlabeled `DOMAIN_1` after `Th4`. -/
theorem th5 {D X1 X2 X3 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hD : D ≠ (∅ : TarskiSet.{u})) :
    D = ZFMISC_1.product3 X1 X2 X3 ↔
      ∀ a, a ∈ D ↔
        ∃ x1 x2 x3, SUBSET_1.isElement x1 X1 ∧ SUBSET_1.isElement x2 X2 ∧
          SUBSET_1.isElement x3 X3 ∧ a = XTUPLE_0.triple x1 x2 x3 := by
  constructor
  · intro heq a
    constructor
    · intro ha
      exact (th3 h1 h2 h3).mp
        (Eq.subst (motive := fun s => a ∈ s) heq ha)
    · intro hex
      exact Eq.subst (motive := fun s => a ∈ s) heq.symm
        ((th3 h1 h2 h3).mpr hex)
  · intro h
    exact th4 h1 h2 h3 hD h

/-- Coherence: `[x1,x2,x3]` is `Element of [:X1,X2,X3:]`. -/
theorem triple_isElement {X1 X2 X3 x1 x2 x3 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hx1 : SUBSET_1.isElement x1 X1) (hx2 : SUBSET_1.isElement x2 X2)
    (hx3 : SUBSET_1.isElement x3 X3) :
    SUBSET_1.isElement (XTUPLE_0.triple x1 x2 x3)
      (ZFMISC_1.product3 X1 X2 X3) :=
  SUBSET_1.isElement_of
    ((MCART_1.th69 x1 x2 x3 X1 X2 X3).mpr
      ⟨SUBSET_1.isElement_mem (ne_imp_not_empty h1) hx1,
        SUBSET_1.isElement_mem (ne_imp_not_empty h2) hx2,
        SUBSET_1.isElement_mem (ne_imp_not_empty h3) hx3⟩)

/-- Unlabeled `DOMAIN_1` (`L155`). -/
theorem th6 {a X1 X2 X3 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x (ZFMISC_1.product3 X1 X2 X3)) :
    a = XTUPLE_0.fst3 x ↔
      ∀ x1 x2 x3, SUBSET_1.isElement x1 X1 → SUBSET_1.isElement x2 X2 →
        SUBSET_1.isElement x3 X3 → x = XTUPLE_0.triple x1 x2 x3 → a = x1 := by
  have hPne : ZFMISC_1.product3 X1 X2 X3 ≠ (∅ : TarskiSet.{u}) :=
    (MCART_1.th31 X1 X2 X3).mp ⟨h1, h2, h3⟩
  have hx' : x ∈ ZFMISC_1.product3 X1 X2 X3 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  constructor
  · intro ha x1 x2 x3 hx1 hx2 hx3 heq
    have heta : x = XTUPLE_0.triple (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x)
        (XTUPLE_0.thd3 x) :=
      MCART_1.th43 h1 h2 h3 hx'
    have ⟨e1, e2, e3⟩ := XTUPLE_0.th3 (heta.symm.trans heq)
    exact ha.trans e1
  · intro hy
    exact MCART_1.th65 h1 h2 h3 hx' fun xx1 xx2 xx3 hx1 hx2 hx3 heq =>
      hy xx1 xx2 xx3 (SUBSET_1.isElement_of hx1) (SUBSET_1.isElement_of hx2)
        (SUBSET_1.isElement_of hx3) heq

/-- Unlabeled `DOMAIN_1` (`L169`). -/
theorem th7 {b X1 X2 X3 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x (ZFMISC_1.product3 X1 X2 X3)) :
    b = XTUPLE_0.snd3 x ↔
      ∀ x1 x2 x3, SUBSET_1.isElement x1 X1 → SUBSET_1.isElement x2 X2 →
        SUBSET_1.isElement x3 X3 → x = XTUPLE_0.triple x1 x2 x3 → b = x2 := by
  have hPne : ZFMISC_1.product3 X1 X2 X3 ≠ (∅ : TarskiSet.{u}) :=
    (MCART_1.th31 X1 X2 X3).mp ⟨h1, h2, h3⟩
  have hx' : x ∈ ZFMISC_1.product3 X1 X2 X3 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  constructor
  · intro hb x1 x2 x3 hx1 hx2 hx3 heq
    have heta : x = XTUPLE_0.triple (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x)
        (XTUPLE_0.thd3 x) :=
      MCART_1.th43 h1 h2 h3 hx'
    have ⟨e1, e2, e3⟩ := XTUPLE_0.th3 (heta.symm.trans heq)
    exact hb.trans e2
  · intro hy
    exact MCART_1.th66 h1 h2 h3 hx' fun xx1 xx2 xx3 hx1 hx2 hx3 heq =>
      hy xx1 xx2 xx3 (SUBSET_1.isElement_of hx1) (SUBSET_1.isElement_of hx2)
        (SUBSET_1.isElement_of hx3) heq

/-- Unlabeled `DOMAIN_1` (`L184`). -/
theorem th8 {c X1 X2 X3 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x (ZFMISC_1.product3 X1 X2 X3)) :
    c = XTUPLE_0.thd3 x ↔
      ∀ x1 x2 x3, SUBSET_1.isElement x1 X1 → SUBSET_1.isElement x2 X2 →
        SUBSET_1.isElement x3 X3 → x = XTUPLE_0.triple x1 x2 x3 → c = x3 := by
  have hPne : ZFMISC_1.product3 X1 X2 X3 ≠ (∅ : TarskiSet.{u}) :=
    (MCART_1.th31 X1 X2 X3).mp ⟨h1, h2, h3⟩
  have hx' : x ∈ ZFMISC_1.product3 X1 X2 X3 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  constructor
  · intro hc x1 x2 x3 hx1 hx2 hx3 heq
    have heta : x = XTUPLE_0.triple (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x)
        (XTUPLE_0.thd3 x) :=
      MCART_1.th43 h1 h2 h3 hx'
    have ⟨e1, e2, e3⟩ := XTUPLE_0.th3 (heta.symm.trans heq)
    exact hc.trans e3
  · intro hy
    exact MCART_1.th67 h1 h2 h3 hx' fun xx1 xx2 xx3 hx1 hx2 hx3 heq =>
      hy xx1 xx2 xx3 (SUBSET_1.isElement_of hx1) (SUBSET_1.isElement_of hx2)
        (SUBSET_1.isElement_of hx3) heq

/-- Unlabeled `DOMAIN_1` (`L199`). -/
theorem th9 {X1 X2 X3 x y : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x (ZFMISC_1.product3 X1 X2 X3))
    (hy : SUBSET_1.isElement y (ZFMISC_1.product3 X1 X2 X3))
    (h1eq : XTUPLE_0.fst3 x = XTUPLE_0.fst3 y)
    (h2eq : XTUPLE_0.snd3 x = XTUPLE_0.snd3 y)
    (h3eq : XTUPLE_0.thd3 x = XTUPLE_0.thd3 y) :
    x = y := by
  have hPne : ZFMISC_1.product3 X1 X2 X3 ≠ (∅ : TarskiSet.{u}) :=
    (MCART_1.th31 X1 X2 X3).mp ⟨h1, h2, h3⟩
  have hx' : x ∈ ZFMISC_1.product3 X1 X2 X3 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  have hy' : y ∈ ZFMISC_1.product3 X1 X2 X3 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hy
  have hxeq := MCART_1.th43 h1 h2 h3 hx'
  have hyeq := MCART_1.th43 h1 h2 h3 hy'
  have htrip :
      XTUPLE_0.triple (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x) (XTUPLE_0.thd3 x) =
        XTUPLE_0.triple (XTUPLE_0.fst3 y) (XTUPLE_0.snd3 y) (XTUPLE_0.thd3 y) :=
    Eq.subst (motive := fun s =>
        XTUPLE_0.triple (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x) (XTUPLE_0.thd3 x) =
          XTUPLE_0.triple s (XTUPLE_0.snd3 y) (XTUPLE_0.thd3 y)) h1eq
      (Eq.subst (motive := fun s =>
          XTUPLE_0.triple (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x)
            (XTUPLE_0.thd3 x) =
            XTUPLE_0.triple (XTUPLE_0.fst3 x) s (XTUPLE_0.thd3 y)) h2eq
        (Eq.subst (motive := fun s =>
            XTUPLE_0.triple (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x)
              (XTUPLE_0.thd3 x) =
              XTUPLE_0.triple (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x) s)
          h3eq rfl))
  exact hxeq.trans (htrip.trans hyeq.symm)

/-- `DOMAIN_1:10` (`Th10`) -/
theorem th10 {a X1 X2 X3 X4 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u})) :
    a ∈ ZFMISC_1.product4 X1 X2 X3 X4 ↔
      ∃ x1 x2 x3 x4, SUBSET_1.isElement x1 X1 ∧ SUBSET_1.isElement x2 X2 ∧
        SUBSET_1.isElement x3 X3 ∧ SUBSET_1.isElement x4 X4 ∧
        a = XTUPLE_0.quadruple x1 x2 x3 x4 := by
  constructor
  · intro ha
    obtain ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, heq⟩ := MCART_1.th79 ha
    exact ⟨x1, x2, x3, x4, SUBSET_1.isElement_of hx1, SUBSET_1.isElement_of hx2,
      SUBSET_1.isElement_of hx3, SUBSET_1.isElement_of hx4, heq⟩
  · intro ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, heq⟩
    have hin : XTUPLE_0.quadruple x1 x2 x3 x4 ∈
        ZFMISC_1.product4 X1 X2 X3 X4 :=
      (MCART_1.th80 x1 x2 x3 x4 X1 X2 X3 X4).mpr
        ⟨SUBSET_1.isElement_mem (ne_imp_not_empty h1) hx1,
          SUBSET_1.isElement_mem (ne_imp_not_empty h2) hx2,
          SUBSET_1.isElement_mem (ne_imp_not_empty h3) hx3,
          SUBSET_1.isElement_mem (ne_imp_not_empty h4) hx4⟩
    exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product4 X1 X2 X3 X4)
      heq.symm hin

/-- `DOMAIN_1:11` (`Th11`) -/
theorem th11 {D X1 X2 X3 X4 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (_hD : D ≠ (∅ : TarskiSet.{u}))
    (h : ∀ a, a ∈ D ↔
      ∃ x1 x2 x3 x4, SUBSET_1.isElement x1 X1 ∧ SUBSET_1.isElement x2 X2 ∧
        SUBSET_1.isElement x3 X3 ∧ SUBSET_1.isElement x4 X4 ∧
        a = XTUPLE_0.quadruple x1 x2 x3 x4) :
    D = ZFMISC_1.product4 X1 X2 X3 X4 := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    obtain ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, heq⟩ := (h a).mp ha
    exact (th10 h1 h2 h3 h4).mpr ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, heq⟩
  · intro ha
    obtain ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, heq⟩ :=
      (th10 h1 h2 h3 h4).mp ha
    exact (h a).mpr ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, heq⟩

/-- Unlabeled `DOMAIN_1` after `Th11`. -/
theorem th12 {D X1 X2 X3 X4 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hD : D ≠ (∅ : TarskiSet.{u})) :
    D = ZFMISC_1.product4 X1 X2 X3 X4 ↔
      ∀ a, a ∈ D ↔
        ∃ x1 x2 x3 x4, SUBSET_1.isElement x1 X1 ∧ SUBSET_1.isElement x2 X2 ∧
          SUBSET_1.isElement x3 X3 ∧ SUBSET_1.isElement x4 X4 ∧
          a = XTUPLE_0.quadruple x1 x2 x3 x4 := by
  constructor
  · intro heq a
    constructor
    · intro ha
      exact (th10 h1 h2 h3 h4).mp
        (Eq.subst (motive := fun s => a ∈ s) heq ha)
    · intro hex
      exact Eq.subst (motive := fun s => a ∈ s) heq.symm
        ((th10 h1 h2 h3 h4).mpr hex)
  · intro h
    exact th11 h1 h2 h3 h4 hD h

/-- Coherence: `[x1,x2,x3,x4]` is `Element of [:X1,X2,X3,X4:]`. -/
theorem quadruple_isElement {X1 X2 X3 X4 x1 x2 x3 x4 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx1 : SUBSET_1.isElement x1 X1) (hx2 : SUBSET_1.isElement x2 X2)
    (hx3 : SUBSET_1.isElement x3 X3) (hx4 : SUBSET_1.isElement x4 X4) :
    SUBSET_1.isElement (XTUPLE_0.quadruple x1 x2 x3 x4)
      (ZFMISC_1.product4 X1 X2 X3 X4) :=
  SUBSET_1.isElement_of
    ((MCART_1.th80 x1 x2 x3 x4 X1 X2 X3 X4).mpr
      ⟨SUBSET_1.isElement_mem (ne_imp_not_empty h1) hx1,
        SUBSET_1.isElement_mem (ne_imp_not_empty h2) hx2,
        SUBSET_1.isElement_mem (ne_imp_not_empty h3) hx3,
        SUBSET_1.isElement_mem (ne_imp_not_empty h4) hx4⟩)

/-- Unlabeled `DOMAIN_1` (`L274`). -/
theorem th13 {a X1 X2 X3 X4 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x (ZFMISC_1.product4 X1 X2 X3 X4)) :
    a = XTUPLE_0.fst4 x ↔
      ∀ x1 x2 x3 x4, SUBSET_1.isElement x1 X1 → SUBSET_1.isElement x2 X2 →
        SUBSET_1.isElement x3 X3 → SUBSET_1.isElement x4 X4 →
        x = XTUPLE_0.quadruple x1 x2 x3 x4 → a = x1 := by
  have hPne : ZFMISC_1.product4 X1 X2 X3 X4 ≠ (∅ : TarskiSet.{u}) :=
    (MCART_1.th51 X1 X2 X3 X4).mp ⟨h1, h2, h3, h4⟩
  have hx' : x ∈ ZFMISC_1.product4 X1 X2 X3 X4 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  constructor
  · intro ha x1 x2 x3 x4 hx1 hx2 hx3 hx4 heq
    have heta := MCART_1.th55 h1 h2 h3 h4 hx'
    have ⟨e1, e2, e3, e4⟩ := XTUPLE_0.th5 (heta.symm.trans heq)
    exact ha.trans e1
  · intro hy
    exact MCART_1.th75 h1 h2 h3 h4 hx' fun xx1 xx2 xx3 xx4 hx1 hx2 hx3 hx4 heq =>
      hy xx1 xx2 xx3 xx4 (SUBSET_1.isElement_of hx1) (SUBSET_1.isElement_of hx2)
        (SUBSET_1.isElement_of hx3) (SUBSET_1.isElement_of hx4) heq

/-- Unlabeled `DOMAIN_1` (`L289`). -/
theorem th14 {b X1 X2 X3 X4 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x (ZFMISC_1.product4 X1 X2 X3 X4)) :
    b = XTUPLE_0.snd4 x ↔
      ∀ x1 x2 x3 x4, SUBSET_1.isElement x1 X1 → SUBSET_1.isElement x2 X2 →
        SUBSET_1.isElement x3 X3 → SUBSET_1.isElement x4 X4 →
        x = XTUPLE_0.quadruple x1 x2 x3 x4 → b = x2 := by
  have hPne : ZFMISC_1.product4 X1 X2 X3 X4 ≠ (∅ : TarskiSet.{u}) :=
    (MCART_1.th51 X1 X2 X3 X4).mp ⟨h1, h2, h3, h4⟩
  have hx' : x ∈ ZFMISC_1.product4 X1 X2 X3 X4 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  constructor
  · intro hb x1 x2 x3 x4 hx1 hx2 hx3 hx4 heq
    have heta := MCART_1.th55 h1 h2 h3 h4 hx'
    have ⟨e1, e2, e3, e4⟩ := XTUPLE_0.th5 (heta.symm.trans heq)
    exact hb.trans e2
  · intro hy
    exact MCART_1.th76 h1 h2 h3 h4 hx' fun xx1 xx2 xx3 xx4 hx1 hx2 hx3 hx4 heq =>
      hy xx1 xx2 xx3 xx4 (SUBSET_1.isElement_of hx1) (SUBSET_1.isElement_of hx2)
        (SUBSET_1.isElement_of hx3) (SUBSET_1.isElement_of hx4) heq

/-- Unlabeled `DOMAIN_1` (`L304`). -/
theorem th15 {c X1 X2 X3 X4 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x (ZFMISC_1.product4 X1 X2 X3 X4)) :
    c = XTUPLE_0.thd4 x ↔
      ∀ x1 x2 x3 x4, SUBSET_1.isElement x1 X1 → SUBSET_1.isElement x2 X2 →
        SUBSET_1.isElement x3 X3 → SUBSET_1.isElement x4 X4 →
        x = XTUPLE_0.quadruple x1 x2 x3 x4 → c = x3 := by
  have hPne : ZFMISC_1.product4 X1 X2 X3 X4 ≠ (∅ : TarskiSet.{u}) :=
    (MCART_1.th51 X1 X2 X3 X4).mp ⟨h1, h2, h3, h4⟩
  have hx' : x ∈ ZFMISC_1.product4 X1 X2 X3 X4 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  constructor
  · intro hc x1 x2 x3 x4 hx1 hx2 hx3 hx4 heq
    have heta := MCART_1.th55 h1 h2 h3 h4 hx'
    have ⟨e1, e2, e3, e4⟩ := XTUPLE_0.th5 (heta.symm.trans heq)
    exact hc.trans e3
  · intro hy
    exact MCART_1.th77 h1 h2 h3 h4 hx' fun xx1 xx2 xx3 xx4 hx1 hx2 hx3 hx4 heq =>
      hy xx1 xx2 xx3 xx4 (SUBSET_1.isElement_of hx1) (SUBSET_1.isElement_of hx2)
        (SUBSET_1.isElement_of hx3) (SUBSET_1.isElement_of hx4) heq

/-- Unlabeled `DOMAIN_1` (`L319`). -/
theorem th16 {d X1 X2 X3 X4 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x (ZFMISC_1.product4 X1 X2 X3 X4)) :
    d = XTUPLE_0.fth4 x ↔
      ∀ x1 x2 x3 x4, SUBSET_1.isElement x1 X1 → SUBSET_1.isElement x2 X2 →
        SUBSET_1.isElement x3 X3 → SUBSET_1.isElement x4 X4 →
        x = XTUPLE_0.quadruple x1 x2 x3 x4 → d = x4 := by
  have hPne : ZFMISC_1.product4 X1 X2 X3 X4 ≠ (∅ : TarskiSet.{u}) :=
    (MCART_1.th51 X1 X2 X3 X4).mp ⟨h1, h2, h3, h4⟩
  have hx' : x ∈ ZFMISC_1.product4 X1 X2 X3 X4 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  constructor
  · intro hd x1 x2 x3 x4 hx1 hx2 hx3 hx4 heq
    have heta := MCART_1.th55 h1 h2 h3 h4 hx'
    have ⟨e1, e2, e3, e4⟩ := XTUPLE_0.th5 (heta.symm.trans heq)
    exact hd.trans e4
  · intro hy
    exact MCART_1.th78 h1 h2 h3 h4 hx' fun xx1 xx2 xx3 xx4 hx1 hx2 hx3 hx4 heq =>
      hy xx1 xx2 xx3 xx4 (SUBSET_1.isElement_of hx1) (SUBSET_1.isElement_of hx2)
        (SUBSET_1.isElement_of hx3) (SUBSET_1.isElement_of hx4) heq

/-- Unlabeled `DOMAIN_1` (`L334`). -/
theorem th17 {X1 X2 X3 X4 x y : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x (ZFMISC_1.product4 X1 X2 X3 X4))
    (hy : SUBSET_1.isElement y (ZFMISC_1.product4 X1 X2 X3 X4))
    (h1eq : XTUPLE_0.fst4 x = XTUPLE_0.fst4 y)
    (h2eq : XTUPLE_0.snd4 x = XTUPLE_0.snd4 y)
    (h3eq : XTUPLE_0.thd4 x = XTUPLE_0.thd4 y)
    (h4eq : XTUPLE_0.fth4 x = XTUPLE_0.fth4 y) :
    x = y := by
  have hPne : ZFMISC_1.product4 X1 X2 X3 X4 ≠ (∅ : TarskiSet.{u}) :=
    (MCART_1.th51 X1 X2 X3 X4).mp ⟨h1, h2, h3, h4⟩
  have hx' : x ∈ ZFMISC_1.product4 X1 X2 X3 X4 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  have hy' : y ∈ ZFMISC_1.product4 X1 X2 X3 X4 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hy
  have hxeq := MCART_1.th55 h1 h2 h3 h4 hx'
  have hyeq := MCART_1.th55 h1 h2 h3 h4 hy'
  have hquad :
      XTUPLE_0.quadruple (XTUPLE_0.fst4 x) (XTUPLE_0.snd4 x)
          (XTUPLE_0.thd4 x) (XTUPLE_0.fth4 x) =
        XTUPLE_0.quadruple (XTUPLE_0.fst4 y) (XTUPLE_0.snd4 y)
          (XTUPLE_0.thd4 y) (XTUPLE_0.fth4 y) :=
    Eq.subst (motive := fun s =>
        XTUPLE_0.quadruple (XTUPLE_0.fst4 x) (XTUPLE_0.snd4 x)
          (XTUPLE_0.thd4 x) (XTUPLE_0.fth4 x) =
          XTUPLE_0.quadruple s (XTUPLE_0.snd4 y) (XTUPLE_0.thd4 y)
            (XTUPLE_0.fth4 y)) h1eq
      (Eq.subst (motive := fun s =>
          XTUPLE_0.quadruple (XTUPLE_0.fst4 x) (XTUPLE_0.snd4 x)
            (XTUPLE_0.thd4 x) (XTUPLE_0.fth4 x) =
            XTUPLE_0.quadruple (XTUPLE_0.fst4 x) s (XTUPLE_0.thd4 y)
              (XTUPLE_0.fth4 y)) h2eq
        (Eq.subst (motive := fun s =>
            XTUPLE_0.quadruple (XTUPLE_0.fst4 x) (XTUPLE_0.snd4 x)
              (XTUPLE_0.thd4 x) (XTUPLE_0.fth4 x) =
              XTUPLE_0.quadruple (XTUPLE_0.fst4 x) (XTUPLE_0.snd4 x) s
                (XTUPLE_0.fth4 y)) h3eq
          (Eq.subst (motive := fun s =>
              XTUPLE_0.quadruple (XTUPLE_0.fst4 x) (XTUPLE_0.snd4 x)
                (XTUPLE_0.thd4 x) (XTUPLE_0.fth4 x) =
                XTUPLE_0.quadruple (XTUPLE_0.fst4 x) (XTUPLE_0.snd4 x)
                  (XTUPLE_0.thd4 x) s) h4eq rfl)))
  exact hxeq.trans (hquad.trans hyeq.symm)

/-! ## Schemes -/

/-- `DOMAIN_1:sch Fraenkel1` -/
theorem sch_Fraenkel1 (P : TarskiSet.{u} → Prop) (X1 : TarskiSet.{u}) :
    SUBSET_1.isSubset (fraenkel1 X1 P) X1 :=
  fun a ha => And.left ((fraenkel1_iff X1 P a).mp ha)

/-- `DOMAIN_1:sch Fraenkel2` -/
theorem sch_Fraenkel2 (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (X1 X2 : TarskiSet.{u}) :
    SUBSET_1.isSubset (fraenkel2 X1 X2 P) (ZFMISC_1.product X1 X2) :=
  fun a ha => And.left ((sep_iff _ _ a).mp ha)

/-- `DOMAIN_1:sch Fraenkel3` -/
theorem sch_Fraenkel3
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop)
    (X1 X2 X3 : TarskiSet.{u}) :
    SUBSET_1.isSubset (fraenkel3 X1 X2 X3 P)
      (ZFMISC_1.product3 X1 X2 X3) :=
  fun a ha => And.left ((sep_iff _ _ a).mp ha)

/-- `DOMAIN_1:sch Fraenkel4` -/
theorem sch_Fraenkel4
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop)
    (X1 X2 X3 X4 : TarskiSet.{u}) :
    SUBSET_1.isSubset (fraenkel4 X1 X2 X3 X4 P)
      (ZFMISC_1.product4 X1 X2 X3 X4) :=
  fun a ha => And.left ((sep_iff _ _ a).mp ha)

/-- `DOMAIN_1:sch Fraenkel5` -/
theorem sch_Fraenkel5 (P Q : TarskiSet.{u} → Prop) {X1 : TarskiSet.{u}}
    (h : ∀ x1, SUBSET_1.isElement x1 X1 → P x1 → Q x1) :
    fraenkel1 X1 P ⊆ fraenkel1 X1 Q := by
  intro a ha
  have ⟨haX, hP⟩ := (fraenkel1_iff X1 P a).mp ha
  exact (fraenkel1_iff X1 Q a).mpr
    ⟨haX, h a (SUBSET_1.isElement_of haX) hP⟩

/-- `DOMAIN_1:sch Fraenkel6` -/
theorem sch_Fraenkel6 (P Q : TarskiSet.{u} → Prop) {X1 : TarskiSet.{u}}
    (h : ∀ x1, SUBSET_1.isElement x1 X1 → (P x1 ↔ Q x1)) :
    fraenkel1 X1 P = fraenkel1 X1 Q :=
  XBOOLE_0.eq_iff_subset.mpr
    ⟨sch_Fraenkel5 P Q fun x1 hx hP => (h x1 hx).mp hP,
      sch_Fraenkel5 Q P fun x1 hx hQ => (h x1 hx).mpr hQ⟩

/-- `DOMAIN_1:sch SubsetD` -/
theorem sch_SubsetD (D : TarskiSet.{u}) (P : TarskiSet.{u} → Prop)
    (_hD : D ≠ (∅ : TarskiSet.{u})) :
    SUBSET_1.isSubset (fraenkel1 D P) D :=
  sch_Fraenkel1 P D

/-! ## Fraenkel equalities -/

/-- Unlabeled `DOMAIN_1` (`L439`). -/
theorem th18 {X1 : TarskiSet.{u}} (h1 : X1 ≠ (∅ : TarskiSet.{u})) :
    X1 = fraenkel1 X1 (fun _ => True) := by
  have hsub : SUBSET_1.isSubset (fraenkel1 X1 (fun _ => True)) X1 :=
    sch_SubsetD X1 (fun _ => True) h1
  refine SUBSET_1.th28 hsub ?_
  intro x hx
  have hx' : x ∈ X1 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty h1) hx
  exact (fraenkel1_iff X1 (fun _ => True) x).mpr ⟨hx', trivial⟩

/-- Unlabeled `DOMAIN_1` (`L448`). -/
theorem th19 {X1 X2 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u})) :
    ZFMISC_1.product X1 X2 =
      fraenkel2 X1 X2 (fun _ _ => True) := by
  have hsub : SUBSET_1.isSubset (fraenkel2 X1 X2 (fun _ _ => True))
      (ZFMISC_1.product X1 X2) :=
    sch_Fraenkel2 (fun _ _ => True) X1 X2
  have hPne : ZFMISC_1.product X1 X2 ≠ (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := X1) (Y := X2)).mp hempty)
        (fun h => h1 h) (fun h => h2 h)
  refine SUBSET_1.th28 hsub ?_
  intro x hx
  have hx' : x ∈ ZFMISC_1.product X1 X2 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  have heq : x = TARSKI.pair (XTUPLE_0.fst x) (XTUPLE_0.snd x) :=
    MCART_1.th22 h1 h2 hx'
  have ⟨hf, hs⟩ := MCART_1.th10 hx'
  exact (fraenkel2_iff X1 X2 (fun _ _ => True) x).mpr
    ⟨XTUPLE_0.fst x, XTUPLE_0.snd x, heq, hf, hs, trivial⟩

/-- Unlabeled `DOMAIN_1` (`L464`). -/
theorem th20 {X1 X2 X3 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) :
    ZFMISC_1.product3 X1 X2 X3 =
      fraenkel3 X1 X2 X3 (fun _ _ _ => True) := by
  have hsub : SUBSET_1.isSubset (fraenkel3 X1 X2 X3 (fun _ _ _ => True))
      (ZFMISC_1.product3 X1 X2 X3) :=
    sch_Fraenkel3 (fun _ _ _ => True) X1 X2 X3
  have hPne : ZFMISC_1.product3 X1 X2 X3 ≠ (∅ : TarskiSet.{u}) :=
    (MCART_1.th31 X1 X2 X3).mp ⟨h1, h2, h3⟩
  refine SUBSET_1.th28 hsub ?_
  intro x hx
  have hx' : x ∈ ZFMISC_1.product3 X1 X2 X3 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  obtain ⟨x1, x2, x3, hx1, hx2, hx3, heq'⟩ := MCART_1.lm2 h1 h2 h3 hx'
  exact (fraenkel3_iff X1 X2 X3 (fun _ _ _ => True) x).mpr
    ⟨x1, x2, x3, heq', hx1, hx2, hx3, trivial⟩

/-- Unlabeled `DOMAIN_1` (`L481`). -/
theorem th21 {X1 X2 X3 X4 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u})) :
    ZFMISC_1.product4 X1 X2 X3 X4 =
      fraenkel4 X1 X2 X3 X4 (fun _ _ _ _ => True) := by
  have hsub : SUBSET_1.isSubset
      (fraenkel4 X1 X2 X3 X4 (fun _ _ _ _ => True))
      (ZFMISC_1.product4 X1 X2 X3 X4) :=
    sch_Fraenkel4 (fun _ _ _ _ => True) X1 X2 X3 X4
  have hPne : ZFMISC_1.product4 X1 X2 X3 X4 ≠ (∅ : TarskiSet.{u}) :=
    (MCART_1.th51 X1 X2 X3 X4).mp ⟨h1, h2, h3, h4⟩
  refine SUBSET_1.th28 hsub ?_
  intro x hx
  have hx' : x ∈ ZFMISC_1.product4 X1 X2 X3 X4 :=
    SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  obtain ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, heq⟩ :=
    MCART_1.lm3 h1 h2 h3 h4 hx'
  exact (fraenkel4_iff X1 X2 X3 X4 (fun _ _ _ _ => True) x).mpr
    ⟨x1, x2, x3, x4, heq, hx1, hx2, hx3, hx4, trivial⟩

/-- Unlabeled `DOMAIN_1` (`L498`). -/
theorem th22 {X1 A1 : TarskiSet.{u}} (_h1 : X1 ≠ (∅ : TarskiSet.{u}))
    (hA : SUBSET_1.isSubset A1 X1) :
    A1 = fraenkel1 X1 (fun x1 => x1 ∈ A1) := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    exact (fraenkel1_iff X1 (fun x1 => x1 ∈ A1) a).mpr ⟨hA a ha, ha⟩
  · intro ha
    exact And.right ((fraenkel1_iff X1 (fun x1 => x1 ∈ A1) a).mp ha)

/-- Unlabeled `DOMAIN_1` (`L513`). -/
theorem th23 {X1 X2 A1 A2 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (hA1 : SUBSET_1.isSubset A1 X1) (hA2 : SUBSET_1.isSubset A2 X2) :
    ZFMISC_1.product A1 A2 =
      fraenkel2 X1 X2 (fun x1 x2 => x1 ∈ A1 ∧ x2 ∈ A2) := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    have ha' : a ∈ ZFMISC_1.product X1 X2 :=
      MCART_1.product_subset hA1 hA2 a ha
    have heq : a = TARSKI.pair (XTUPLE_0.fst a) (XTUPLE_0.snd a) :=
      MCART_1.th22 h1 h2 ha'
    have ⟨hf, hs⟩ := MCART_1.th10 ha
    exact (fraenkel2_iff X1 X2 (fun x1 x2 => x1 ∈ A1 ∧ x2 ∈ A2) a).mpr
      ⟨XTUPLE_0.fst a, XTUPLE_0.snd a, heq, hA1 _ hf, hA2 _ hs, ⟨hf, hs⟩⟩
  · intro ha
    obtain ⟨x1, x2, heq, hx1, hx2, ⟨hA1', hA2'⟩⟩ :=
      (fraenkel2_iff X1 X2 (fun x1 x2 => x1 ∈ A1 ∧ x2 ∈ A2) a).mp ha
    exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product A1 A2) heq.symm
      ((ZFMISC_1.th87 (x := x1) (y := x2) (X := A1) (Y := A2)).mpr
        ⟨hA1', hA2'⟩)

/-- Unlabeled `DOMAIN_1` (`L532`). -/
theorem th24 {X1 X2 X3 A1 A2 A3 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hA1 : SUBSET_1.isSubset A1 X1) (hA2 : SUBSET_1.isSubset A2 X2)
    (hA3 : SUBSET_1.isSubset A3 X3) :
    ZFMISC_1.product3 A1 A2 A3 =
      fraenkel3 X1 X2 X3 (fun x1 x2 x3 => x1 ∈ A1 ∧ x2 ∈ A2 ∧ x3 ∈ A3) := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    have hAne : A1 ≠ (∅ : TarskiSet.{u}) ∧ A2 ≠ (∅ : TarskiSet.{u}) ∧
        A3 ≠ (∅ : TarskiSet.{u}) :=
      (MCART_1.th31 A1 A2 A3).mpr (nonempty_of_mem ha)
    have ha' : a ∈ ZFMISC_1.product3 X1 X2 X3 :=
      MCART_1.th73 hA1 hA2 hA3 a ha
    have ⟨hf, hs, ht⟩ :=
      MCART_1.th72 h1 h2 h3 hAne.1 hAne.2.1 hAne.2.2 hA1 hA2 hA3 ha' ha
    have heq := MCART_1.th43 h1 h2 h3 ha'
    exact (fraenkel3_iff X1 X2 X3
        (fun x1 x2 x3 => x1 ∈ A1 ∧ x2 ∈ A2 ∧ x3 ∈ A3) a).mpr
      ⟨XTUPLE_0.fst3 a, XTUPLE_0.snd3 a, XTUPLE_0.thd3 a, heq,
        hA1 _ hf, hA2 _ hs, hA3 _ ht, ⟨hf, hs, ht⟩⟩
  · intro ha
    obtain ⟨x1, x2, x3, heq, hx1, hx2, hx3, ⟨hA1', hA2', hA3'⟩⟩ :=
      (fraenkel3_iff X1 X2 X3
        (fun x1 x2 x3 => x1 ∈ A1 ∧ x2 ∈ A2 ∧ x3 ∈ A3) a).mp ha
    exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product3 A1 A2 A3)
      heq.symm ((MCART_1.th69 x1 x2 x3 A1 A2 A3).mpr ⟨hA1', hA2', hA3'⟩)

/-- Unlabeled `DOMAIN_1` (`L556`). -/
theorem th25 {X1 X2 X3 X4 A1 A2 A3 A4 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hA1 : SUBSET_1.isSubset A1 X1) (hA2 : SUBSET_1.isSubset A2 X2)
    (hA3 : SUBSET_1.isSubset A3 X3) (hA4 : SUBSET_1.isSubset A4 X4) :
    ZFMISC_1.product4 A1 A2 A3 A4 =
      fraenkel4 X1 X2 X3 X4
        (fun x1 x2 x3 x4 => x1 ∈ A1 ∧ x2 ∈ A2 ∧ x3 ∈ A3 ∧ x4 ∈ A4) := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    have hAne : A1 ≠ (∅ : TarskiSet.{u}) ∧ A2 ≠ (∅ : TarskiSet.{u}) ∧
        A3 ≠ (∅ : TarskiSet.{u}) ∧ A4 ≠ (∅ : TarskiSet.{u}) :=
      (MCART_1.th51 A1 A2 A3 A4).mpr (nonempty_of_mem ha)
    have ha' : a ∈ ZFMISC_1.product4 X1 X2 X3 X4 :=
      MCART_1.th84 hA1 hA2 hA3 hA4 a ha
    have ⟨hf, hs, ht, hft⟩ :=
      MCART_1.th83 h1 h2 h3 h4 hAne.1 hAne.2.1 hAne.2.2.1 hAne.2.2.2
        ha' ha
    have heq := MCART_1.th55 h1 h2 h3 h4 ha'
    exact (fraenkel4_iff X1 X2 X3 X4
        (fun x1 x2 x3 x4 => x1 ∈ A1 ∧ x2 ∈ A2 ∧ x3 ∈ A3 ∧ x4 ∈ A4) a).mpr
      ⟨XTUPLE_0.fst4 a, XTUPLE_0.snd4 a, XTUPLE_0.thd4 a, XTUPLE_0.fth4 a, heq,
        hA1 _ hf, hA2 _ hs, hA3 _ ht, hA4 _ hft, ⟨hf, hs, ht, hft⟩⟩
  · intro ha
    obtain ⟨x1, x2, x3, x4, heq, hx1, hx2, hx3, hx4,
        ⟨hA1', hA2', hA3', hA4'⟩⟩ :=
      (fraenkel4_iff X1 X2 X3 X4
        (fun x1 x2 x3 x4 => x1 ∈ A1 ∧ x2 ∈ A2 ∧ x3 ∈ A3 ∧ x4 ∈ A4) a).mp ha
    exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product4 A1 A2 A3 A4)
      heq.symm
      ((MCART_1.th80 x1 x2 x3 x4 A1 A2 A3 A4).mpr ⟨hA1', hA2', hA3', hA4'⟩)

/-- Unlabeled `DOMAIN_1` (`L584`). -/
theorem th26 {X1 : TarskiSet.{u}} (_h1 : X1 ≠ (∅ : TarskiSet.{u})) :
    SUBSET_1.emptyOf X1 = fraenkel1 X1 (fun _ => False) := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    exact ((XBOOLE_0.empty_iff a).mp
      (Eq.subst (motive := fun s => a ∈ s)
        (show SUBSET_1.emptyOf X1 = (∅ : TarskiSet.{u}) from rfl) ha)).elim
  · intro ha
    exact (And.right ((fraenkel1_iff X1 (fun _ => False) a).mp ha)).elim

/-- Unlabeled `DOMAIN_1` (`L598`). -/
theorem th27 {X1 A1 : TarskiSet.{u}} (h1 : X1 ≠ (∅ : TarskiSet.{u}))
    (_hA : SUBSET_1.isSubset A1 X1) :
    SUBSET_1.compl X1 A1 = fraenkel1 X1 (fun x1 => x1 ∉ A1) := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    have ⟨haX, hnot⟩ := (XBOOLE_0.def5 X1 A1 a).mp ha
    exact (fraenkel1_iff X1 (fun x1 => x1 ∉ A1) a).mpr ⟨haX, hnot⟩
  · intro ha
    have ⟨haX, hnot⟩ := (fraenkel1_iff X1 (fun x1 => x1 ∉ A1) a).mp ha
    exact SUBSET_1.th29 h1 (SUBSET_1.isElement_of haX) hnot

/-- Unlabeled `DOMAIN_1` (`L615`). -/
theorem th28 {X1 A1 B1 : TarskiSet.{u}} (_h1 : X1 ≠ (∅ : TarskiSet.{u}))
    (hA : SUBSET_1.isSubset A1 X1) (_hB : SUBSET_1.isSubset B1 X1) :
    A1 ∩ B1 = fraenkel1 X1 (fun x1 => x1 ∈ A1 ∧ x1 ∈ B1) := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    have ⟨haA, haB⟩ := (XBOOLE_0.def4 A1 B1 a).mp ha
    exact (fraenkel1_iff X1 (fun x1 => x1 ∈ A1 ∧ x1 ∈ B1) a).mpr
      ⟨hA a haA, ⟨haA, haB⟩⟩
  · intro ha
    have ⟨_, ⟨haA, haB⟩⟩ :=
      (fraenkel1_iff X1 (fun x1 => x1 ∈ A1 ∧ x1 ∈ B1) a).mp ha
    exact (XBOOLE_0.def4 A1 B1 a).mpr ⟨haA, haB⟩

/-- Unlabeled `DOMAIN_1` (`L633`). -/
theorem th29 {X1 A1 B1 : TarskiSet.{u}} (_h1 : X1 ≠ (∅ : TarskiSet.{u}))
    (hA : SUBSET_1.isSubset A1 X1) (hB : SUBSET_1.isSubset B1 X1) :
    A1 ∪ B1 = fraenkel1 X1 (fun x1 => x1 ∈ A1 ∨ x1 ∈ B1) := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    have haX : a ∈ X1 :=
      Or.elim ((XBOOLE_0.def3 A1 B1 a).mp ha)
        (fun h => hA a h) (fun h => hB a h)
    exact (fraenkel1_iff X1 (fun x1 => x1 ∈ A1 ∨ x1 ∈ B1) a).mpr
      ⟨haX, (XBOOLE_0.def3 A1 B1 a).mp ha⟩
  · intro ha
    have ⟨_, hor⟩ :=
      (fraenkel1_iff X1 (fun x1 => x1 ∈ A1 ∨ x1 ∈ B1) a).mp ha
    exact (XBOOLE_0.def3 A1 B1 a).mpr hor

/-- Unlabeled `DOMAIN_1` (`L651`). -/
theorem th30 {X1 A1 B1 : TarskiSet.{u}} (_h1 : X1 ≠ (∅ : TarskiSet.{u}))
    (hA : SUBSET_1.isSubset A1 X1) (_hB : SUBSET_1.isSubset B1 X1) :
    A1 \ B1 = fraenkel1 X1 (fun x1 => x1 ∈ A1 ∧ x1 ∉ B1) := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    have ⟨haA, hnot⟩ := (XBOOLE_0.def5 A1 B1 a).mp ha
    exact (fraenkel1_iff X1 (fun x1 => x1 ∈ A1 ∧ x1 ∉ B1) a).mpr
      ⟨hA a haA, ⟨haA, hnot⟩⟩
  · intro ha
    have ⟨_, ⟨haA, hnot⟩⟩ :=
      (fraenkel1_iff X1 (fun x1 => x1 ∈ A1 ∧ x1 ∉ B1) a).mp ha
    exact (XBOOLE_0.def5 A1 B1 a).mpr ⟨haA, hnot⟩

/-- `DOMAIN_1:31` (`Th31`) -/
theorem th31 {X1 A1 B1 : TarskiSet.{u}} (_h1 : X1 ≠ (∅ : TarskiSet.{u}))
    (hA : SUBSET_1.isSubset A1 X1) (hB : SUBSET_1.isSubset B1 X1) :
    A1 ∆ B1 =
      fraenkel1 X1
        (fun x1 => x1 ∈ A1 ∧ x1 ∉ B1 ∨ x1 ∉ A1 ∧ x1 ∈ B1) := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    have haX : a ∈ X1 :=
      Or.elim ((symmdiff_mem_xor A1 B1 a).mp ha)
        (fun ⟨hA', _⟩ => hA a hA') (fun ⟨_, hB'⟩ => hB a hB')
    exact (fraenkel1_iff X1
        (fun x1 => x1 ∈ A1 ∧ x1 ∉ B1 ∨ x1 ∉ A1 ∧ x1 ∈ B1) a).mpr
      ⟨haX, (symmdiff_mem_xor A1 B1 a).mp ha⟩
  · intro ha
    have ⟨_, hor⟩ :=
      (fraenkel1_iff X1
        (fun x1 => x1 ∈ A1 ∧ x1 ∉ B1 ∨ x1 ∉ A1 ∧ x1 ∈ B1) a).mp ha
    exact (symmdiff_mem_xor A1 B1 a).mpr hor

/-- `DOMAIN_1:32` (`Th32`) -/
theorem th32 {X1 A1 B1 : TarskiSet.{u}} (h1 : X1 ≠ (∅ : TarskiSet.{u}))
    (hA : SUBSET_1.isSubset A1 X1) (hB : SUBSET_1.isSubset B1 X1) :
    A1 ∆ B1 = fraenkel1 X1 (fun x1 => x1 ∉ A1 ↔ x1 ∈ B1) := by
  have hchar : ∀ x1, SUBSET_1.isElement x1 X1 →
      ((x1 ∈ A1 ∧ x1 ∉ B1 ∨ x1 ∉ A1 ∧ x1 ∈ B1) ↔ (x1 ∉ A1 ↔ x1 ∈ B1)) := by
    intro x1 _
    constructor
    · intro h
      constructor
      · intro hnotA
        exact Or.elim h (fun ⟨hA', _⟩ => (hnotA hA').elim) And.right
      · intro hB'
        exact Or.elim h (fun ⟨_, hnotB⟩ => (hnotB hB').elim)
          (fun ⟨hnotA, _⟩ => hnotA)
    · intro hiff
      by_cases hA' : x1 ∈ A1
      · exact Or.inl ⟨hA', fun hB' => hiff.mpr hB' hA'⟩
      · exact Or.inr ⟨hA', hiff.mp hA'⟩
  exact (th31 h1 hA hB).trans
    (sch_Fraenkel6
      (fun x1 => x1 ∈ A1 ∧ x1 ∉ B1 ∨ x1 ∉ A1 ∧ x1 ∈ B1)
      (fun x1 => x1 ∉ A1 ↔ x1 ∈ B1) hchar)

/-- Unlabeled `DOMAIN_1` (`L701`). -/
theorem th33 {X1 A1 B1 : TarskiSet.{u}} (h1 : X1 ≠ (∅ : TarskiSet.{u}))
    (hA : SUBSET_1.isSubset A1 X1) (hB : SUBSET_1.isSubset B1 X1) :
    A1 ∆ B1 = fraenkel1 X1 (fun x1 => x1 ∈ A1 ↔ x1 ∉ B1) := by
  have hchar : ∀ x1, SUBSET_1.isElement x1 X1 →
      ((x1 ∉ A1 ↔ x1 ∈ B1) ↔ (x1 ∈ A1 ↔ x1 ∉ B1)) := by
    intro x1 _
    constructor
    · intro h
      exact ⟨fun hA' hB' => h.mpr hB' hA',
        fun hnotB => Classical.byContradiction fun hnotA =>
          hnotB (h.mp hnotA)⟩
    · intro h
      exact ⟨fun hnotA => Classical.byContradiction fun hnotB =>
          hnotA (h.mpr hnotB),
        fun hB' hA' => h.mp hA' hB'⟩
  exact (th32 h1 hA hB).trans
    (sch_Fraenkel6 (fun x1 => x1 ∉ A1 ↔ x1 ∈ B1)
      (fun x1 => x1 ∈ A1 ↔ x1 ∉ B1) hchar)

/-- Unlabeled `DOMAIN_1` (`L713`). -/
theorem th34 {X1 A1 B1 : TarskiSet.{u}} (h1 : X1 ≠ (∅ : TarskiSet.{u}))
    (hA : SUBSET_1.isSubset A1 X1) (hB : SUBSET_1.isSubset B1 X1) :
    A1 ∆ B1 = fraenkel1 X1 (fun x1 => ¬ (x1 ∈ A1 ↔ x1 ∈ B1)) := by
  have hchar : ∀ x1, SUBSET_1.isElement x1 X1 →
      ((x1 ∉ A1 ↔ x1 ∈ B1) ↔ ¬ (x1 ∈ A1 ↔ x1 ∈ B1)) := by
    intro x1 _
    constructor
    · intro h hiff
      by_cases hxA : x1 ∈ A1
      · exact h.mpr (hiff.mp hxA) hxA
      · exact hxA (hiff.mpr (h.mp hxA))
    · intro h
      constructor
      · intro hnotA
        exact Classical.byContradiction fun hnotB =>
          h ⟨fun hA' => (hnotA hA').elim, fun hB' => (hnotB hB').elim⟩
      · intro hB' hA'
        exact h ⟨fun _ => hB', fun _ => hA'⟩
  exact (th32 h1 hA hB).trans
    (sch_Fraenkel6 (fun x1 => x1 ∉ A1 ↔ x1 ∈ B1)
      (fun x1 => ¬ (x1 ∈ A1 ↔ x1 ∈ B1)) hchar)

/-! ## Singleton / enumset redefines as Subset of D -/

/-- Coherence: `{x1}` is `Subset of D`. -/
theorem singleton_isSubset {D x1 : TarskiSet.{u}}
    (hD : D ≠ (∅ : TarskiSet.{u})) (hx1 : SUBSET_1.isElement x1 D) :
    SUBSET_1.isSubset (TARSKI.singleton x1) D :=
  SUBSET_1.th33 hD hx1

theorem upair_isSubset {D x1 x2 : TarskiSet.{u}}
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hx1 : SUBSET_1.isElement x1 D) (hx2 : SUBSET_1.isElement x2 D) :
    SUBSET_1.isSubset (TARSKI.upair x1 x2) D :=
  SUBSET_1.th34 hD hx1 hx2

theorem enumset3_isSubset {D x1 x2 x3 : TarskiSet.{u}}
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hx1 : SUBSET_1.isElement x1 D) (hx2 : SUBSET_1.isElement x2 D)
    (hx3 : SUBSET_1.isElement x3 D) :
    SUBSET_1.isSubset (ENUMSET1.enumset3 x1 x2 x3) D :=
  SUBSET_1.th35 hD hx1 hx2 hx3

theorem enumset4_isSubset {D x1 x2 x3 x4 : TarskiSet.{u}}
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hx1 : SUBSET_1.isElement x1 D) (hx2 : SUBSET_1.isElement x2 D)
    (hx3 : SUBSET_1.isElement x3 D) (hx4 : SUBSET_1.isElement x4 D) :
    SUBSET_1.isSubset (ENUMSET1.enumset4 x1 x2 x3 x4) D :=
  SUBSET_1.th36 hD hx1 hx2 hx3 hx4

theorem enumset5_isSubset {D x1 x2 x3 x4 x5 : TarskiSet.{u}}
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hx1 : SUBSET_1.isElement x1 D) (hx2 : SUBSET_1.isElement x2 D)
    (hx3 : SUBSET_1.isElement x3 D) (hx4 : SUBSET_1.isElement x4 D)
    (hx5 : SUBSET_1.isElement x5 D) :
    SUBSET_1.isSubset (ENUMSET1.enumset5 x1 x2 x3 x4 x5) D :=
  SUBSET_1.th37 hD hx1 hx2 hx3 hx4 hx5

theorem enumset6_isSubset {D x1 x2 x3 x4 x5 x6 : TarskiSet.{u}}
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hx1 : SUBSET_1.isElement x1 D) (hx2 : SUBSET_1.isElement x2 D)
    (hx3 : SUBSET_1.isElement x3 D) (hx4 : SUBSET_1.isElement x4 D)
    (hx5 : SUBSET_1.isElement x5 D) (hx6 : SUBSET_1.isElement x6 D) :
    SUBSET_1.isSubset (ENUMSET1.enumset6 x1 x2 x3 x4 x5 x6) D :=
  SUBSET_1.th38 hD hx1 hx2 hx3 hx4 hx5 hx6

theorem enumset7_isSubset {D x1 x2 x3 x4 x5 x6 x7 : TarskiSet.{u}}
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hx1 : SUBSET_1.isElement x1 D) (hx2 : SUBSET_1.isElement x2 D)
    (hx3 : SUBSET_1.isElement x3 D) (hx4 : SUBSET_1.isElement x4 D)
    (hx5 : SUBSET_1.isElement x5 D) (hx6 : SUBSET_1.isElement x6 D)
    (hx7 : SUBSET_1.isElement x7 D) :
    SUBSET_1.isSubset (ENUMSET1.enumset7 x1 x2 x3 x4 x5 x6 x7) D :=
  SUBSET_1.th39 hD hx1 hx2 hx3 hx4 hx5 hx6 hx7

theorem enumset8_isSubset {D x1 x2 x3 x4 x5 x6 x7 x8 : TarskiSet.{u}}
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hx1 : SUBSET_1.isElement x1 D) (hx2 : SUBSET_1.isElement x2 D)
    (hx3 : SUBSET_1.isElement x3 D) (hx4 : SUBSET_1.isElement x4 D)
    (hx5 : SUBSET_1.isElement x5 D) (hx6 : SUBSET_1.isElement x6 D)
    (hx7 : SUBSET_1.isElement x7 D) (hx8 : SUBSET_1.isElement x8 D) :
    SUBSET_1.isSubset (ENUMSET1.enumset8 x1 x2 x3 x4 x5 x6 x7 x8) D :=
  SUBSET_1.th40 hD hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8

/-! ## Addenda -/

/-- `DOMAIN_1:sch SubsetFD` -/
theorem sch_SubsetFD (A D : TarskiSet.{u})
    (F : TarskiSet.{u} → TarskiSet.{u}) (P : TarskiSet.{u} → Prop)
    (_hA : A ≠ (∅ : TarskiSet.{u})) (hD : D ≠ (∅ : TarskiSet.{u}))
    (hF : ∀ x, SUBSET_1.isElement x A → SUBSET_1.isElement (F x) D) :
    SUBSET_1.isSubset (imageSep A F P) D := by
  intro y hy
  obtain ⟨z, hzA, _, hyF⟩ := (imageSep_iff A F P y).mp hy
  have hFz : SUBSET_1.isElement (F z) D :=
    hF z (SUBSET_1.isElement_of hzA)
  exact Eq.subst (motive := fun s => s ∈ D) hyF.symm
    (SUBSET_1.isElement_mem (ne_imp_not_empty hD) hFz)

/-- `DOMAIN_1:sch SubsetFD2` -/
theorem sch_SubsetFD2 (A B D : TarskiSet.{u})
    (F : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (_hA : A ≠ (∅ : TarskiSet.{u})) (_hB : B ≠ (∅ : TarskiSet.{u}))
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hF : ∀ x y, SUBSET_1.isElement x A → SUBSET_1.isElement y B →
      SUBSET_1.isElement (F x y) D) :
    SUBSET_1.isSubset (imageSep2 A B F P) D := by
  intro w hw
  obtain ⟨x, y, hx, hy, _, hwF⟩ := (imageSep2_iff A B F P w).mp hw
  have hFxy : SUBSET_1.isElement (F x y) D :=
    hF x y (SUBSET_1.isElement_of hx) (SUBSET_1.isElement_of hy)
  exact Eq.subst (motive := fun s => s ∈ D) hwF.symm
    (SUBSET_1.isElement_mem (ne_imp_not_empty hD) hFxy)

/-- Coherence: `x`11` is `Element of D1`. -/
theorem fst11_isElement {D1 D2 D3 x : TarskiSet.{u}}
    (h1 : D1 ≠ (∅ : TarskiSet.{u})) (h2 : D2 ≠ (∅ : TarskiSet.{u}))
    (h3 : D3 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x
      (ZFMISC_1.product (ZFMISC_1.product D1 D2) D3)) :
    SUBSET_1.isElement (MCART_1.fst11 x) D1 := by
  have h12 : ZFMISC_1.product D1 D2 ≠ (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := D1) (Y := D2)).mp hempty)
        (fun h => h1 h) (fun h => h2 h)
  have hPne : ZFMISC_1.product (ZFMISC_1.product D1 D2) D3 ≠
      (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := ZFMISC_1.product D1 D2) (Y := D3)).mp hempty)
        (fun h => h12 h) (fun h => h3 h)
  have hx' := SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  have hf := (MCART_1.th10 hx').1
  exact SUBSET_1.isElement_of (MCART_1.th10 hf).1

/-- Coherence: `x`12` is `Element of D2`. -/
theorem fst12_isElement {D1 D2 D3 x : TarskiSet.{u}}
    (h1 : D1 ≠ (∅ : TarskiSet.{u})) (h2 : D2 ≠ (∅ : TarskiSet.{u}))
    (h3 : D3 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x
      (ZFMISC_1.product (ZFMISC_1.product D1 D2) D3)) :
    SUBSET_1.isElement (MCART_1.fst12 x) D2 := by
  have h12 : ZFMISC_1.product D1 D2 ≠ (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := D1) (Y := D2)).mp hempty)
        (fun h => h1 h) (fun h => h2 h)
  have hPne : ZFMISC_1.product (ZFMISC_1.product D1 D2) D3 ≠
      (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := ZFMISC_1.product D1 D2) (Y := D3)).mp hempty)
        (fun h => h12 h) (fun h => h3 h)
  have hx' := SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  have hf := (MCART_1.th10 hx').1
  exact SUBSET_1.isElement_of (MCART_1.th10 hf).2

/-- Coherence: `x`21` is `Element of D2`. -/
theorem snd21_isElement {D1 D2 D3 x : TarskiSet.{u}}
    (h1 : D1 ≠ (∅ : TarskiSet.{u})) (h2 : D2 ≠ (∅ : TarskiSet.{u}))
    (h3 : D3 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x
      (ZFMISC_1.product D1 (ZFMISC_1.product D2 D3))) :
    SUBSET_1.isElement (MCART_1.snd21 x) D2 := by
  have h23 : ZFMISC_1.product D2 D3 ≠ (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := D2) (Y := D3)).mp hempty)
        (fun h => h2 h) (fun h => h3 h)
  have hPne : ZFMISC_1.product D1 (ZFMISC_1.product D2 D3) ≠
      (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := D1) (Y := ZFMISC_1.product D2 D3)).mp hempty)
        (fun h => h1 h) (fun h => h23 h)
  have hx' := SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  have hs := (MCART_1.th10 hx').2
  exact SUBSET_1.isElement_of (MCART_1.th10 hs).1

/-- Coherence: `x`22` is `Element of D3`. -/
theorem snd22_isElement {D1 D2 D3 x : TarskiSet.{u}}
    (h1 : D1 ≠ (∅ : TarskiSet.{u})) (h2 : D2 ≠ (∅ : TarskiSet.{u}))
    (h3 : D3 ≠ (∅ : TarskiSet.{u}))
    (hx : SUBSET_1.isElement x
      (ZFMISC_1.product D1 (ZFMISC_1.product D2 D3))) :
    SUBSET_1.isElement (MCART_1.snd22 x) D3 := by
  have h23 : ZFMISC_1.product D2 D3 ≠ (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := D2) (Y := D3)).mp hempty)
        (fun h => h2 h) (fun h => h3 h)
  have hPne : ZFMISC_1.product D1 (ZFMISC_1.product D2 D3) ≠
      (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := D1) (Y := ZFMISC_1.product D2 D3)).mp hempty)
        (fun h => h1 h) (fun h => h23 h)
  have hx' := SUBSET_1.isElement_mem (ne_imp_not_empty hPne) hx
  have hs := (MCART_1.th10 hx').2
  exact SUBSET_1.isElement_of (MCART_1.th10 hs).2

/-- `DOMAIN_1:sch AndScheme` -/
theorem sch_AndScheme (A : TarskiSet.{u}) (P Q : TarskiSet.{u} → Prop)
    (_hA : A ≠ (∅ : TarskiSet.{u})) :
    fraenkel1 A (fun a => P a ∧ Q a) =
      fraenkel1 A P ∩ fraenkel1 A Q := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    have ⟨hxA, ⟨hP, hQ⟩⟩ :=
      (fraenkel1_iff A (fun a => P a ∧ Q a) x).mp hx
    exact (XBOOLE_0.def4 (fraenkel1 A P) (fraenkel1 A Q) x).mpr
      ⟨(fraenkel1_iff A P x).mpr ⟨hxA, hP⟩,
        (fraenkel1_iff A Q x).mpr ⟨hxA, hQ⟩⟩
  · intro hx
    have ⟨hxP, hxQ⟩ :=
      (XBOOLE_0.def4 (fraenkel1 A P) (fraenkel1 A Q) x).mp hx
    have ⟨hxA, hP⟩ := (fraenkel1_iff A P x).mp hxP
    have ⟨_, hQ⟩ := (fraenkel1_iff A Q x).mp hxQ
    exact (fraenkel1_iff A (fun a => P a ∧ Q a) x).mpr ⟨hxA, ⟨hP, hQ⟩⟩

/-- Registration: `c=-linear non empty for Subset of A`. -/
theorem exists_cLinear_nonempty_subset {A : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u})) :
    ∃ B, SUBSET_1.isSubset B A ∧ B ≠ (∅ : TarskiSet.{u}) ∧
      ORDINAL1.isCLinear B := by
  let a := SUBSET_1.choose A
  have ha : SUBSET_1.isElement a A := SUBSET_1.choose_isElement A
  refine ⟨TARSKI.singleton a, SUBSET_1.th33 hA ha, ?_, ?_⟩
  · exact fun hempty =>
      (XBOOLE_0.empty_iff a).mp
        (Eq.subst (motive := fun s => a ∈ s) hempty
          ((TARSKI.singleton_iff a a).mpr rfl))
  · intro x y hx hy
    have hxeq : x = a := (TARSKI.singleton_iff a x).mp hx
    have hyeq : y = a := (TARSKI.singleton_iff a y).mp hy
    exact Or.inl
      (Eq.subst (motive := fun s => s ⊆ y) hxeq.symm
        (Eq.subst (motive := fun s => a ⊆ s) hyeq.symm
          (fun z hz => hz)))

end DOMAIN_1
