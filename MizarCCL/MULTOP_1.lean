import MizarCCL.FUNCT_2

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/multop_1.miz`.
Authors: Michal Muzalewski, Wojciech Skaba (Mizar),
  Lars Warren Ericson (Lean 4).
-/

/-!
# Three-Argument Operations and Four-Argument Operations

1–1 Lean rendering of Mizar article `MULTOP_1`
(`vendor/mml/multop_1.miz`). Import is `FUNCT_2` only
(`DOMAIN_1` is in the Mizar environ but unused by proofs;
`MCART_1` / `XTUPLE_0` arrive via `FUNCT_2`).
-/

universe u

open TarskiSet TARSKI

namespace MULTOP_1

/-! ## `f.(a,b,c)` (`MULTOP_1:def 1`) -/

/-- `MULTOP_1:def 1` — ternary application `f.(a,b,c) = f.[a,b,c]`. -/
noncomputable def apply3 (f a b c : TarskiSet.{u}) : TarskiSet.{u} :=
  FUNCT_1.apply f (XTUPLE_0.triple a b c)

theorem def1 (f a b c : TarskiSet.{u}) :
    apply3 f a b c = FUNCT_1.apply f (XTUPLE_0.triple a b c) :=
  rfl

private theorem apply3_of_empty_fun {f a b c : TarskiSet.{u}}
    (hf : f = (∅ : TarskiSet.{u})) : apply3 f a b c = (∅ : TarskiSet.{u}) := by
  have hdom : XTUPLE_0.triple a b c ∉ RELAT_1.dom f := by
    intro hx
    have hx' : XTUPLE_0.triple a b c ∈ RELAT_1.dom (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => XTUPLE_0.triple a b c ∈ RELAT_1.dom s) hf hx
    have hx'' : XTUPLE_0.triple a b c ∈ (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => XTUPLE_0.triple a b c ∈ s) RELAT_1.th38.1 hx'
    exact (XBOOLE_0.empty_iff _).mp hx''
  exact FUNCT_1.apply_of_not_mem hdom

private theorem ne_imp_not_empty {A : TarskiSet.{u}}
    (h : A ≠ (∅ : TarskiSet.{u})) : ¬ XBOOLE_0.isEmpty A :=
  fun he => h (XBOOLE_0.empty_eq he)

/-- Coherence: `Function of [:A,B,C:],D` with nonempty `A`,`B`,`C` yields
`Element of D`. -/
theorem apply3_isElement {A B C D f a b c : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hC : C ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f (ZFMISC_1.product3 A B C) D)
    (ha : SUBSET_1.isElement a A) (hb : SUBSET_1.isElement b B)
    (hc : SUBSET_1.isElement c C) :
    SUBSET_1.isElement (apply3 f a b c) D := by
  have ha' : a ∈ A := SUBSET_1.isElement_mem (ne_imp_not_empty hA) ha
  have hb' : b ∈ B := SUBSET_1.isElement_mem (ne_imp_not_empty hB) hb
  have hc' : c ∈ C := SUBSET_1.isElement_mem (ne_imp_not_empty hC) hc
  have habc : XTUPLE_0.triple a b c ∈ ZFMISC_1.product3 A B C :=
    (MCART_1.th69 a b c A B C).mpr ⟨ha', hb', hc'⟩
  have := Classical.propDecidable (D = (∅ : TarskiSet.{u}))
  by_cases hD : D = (∅ : TarskiSet.{u})
  · have hempty : f = (∅ : TarskiSet.{u}) := FUNCT_2.functionOf_empty_cod hf hD
    exact Eq.subst (motive := fun s => SUBSET_1.isElement s D)
      (apply3_of_empty_fun hempty).symm
      ((SUBSET_1.isElement_iff_empty (x := ∅) (X := D)
        (hD ▸ XBOOLE_0.emptySet_isEmpty)).mpr XBOOLE_0.emptySet_isEmpty)
  · exact SUBSET_1.isElement_of (FUNCT_2.th5 hf hD habc)

/-! ## Equality of ternary functions -/

/-- `MULTOP_1:1` (`Th1`) -/
theorem th1 {X Y Z D f1 f2 : TarskiSet.{u}}
    (h1 : FUNCT_2.isFunctionOf f1 (ZFMISC_1.product3 X Y Z) D)
    (h2 : FUNCT_2.isFunctionOf f2 (ZFMISC_1.product3 X Y Z) D)
    (hv : ∀ x y z, x ∈ X → y ∈ Y → z ∈ Z →
      FUNCT_1.apply f1 (XTUPLE_0.triple x y z) =
        FUNCT_1.apply f2 (XTUPLE_0.triple x y z)) :
    f1 = f2 := by
  refine FUNCT_2.th12 h1 h2 ?_
  intro t ht
  obtain ⟨x, y, z, hx, hy, hz, heq⟩ := MCART_1.th68 ht
  exact Eq.subst (motive := fun s =>
      FUNCT_1.apply f1 s = FUNCT_1.apply f2 s) heq.symm (hv x y z hx hy hz)

/-- `MULTOP_1:2` (`Th2`) -/
theorem th2 {A B C D f1 f2 : TarskiSet.{u}}
    (_hA : A ≠ (∅ : TarskiSet.{u})) (_hB : B ≠ (∅ : TarskiSet.{u}))
    (_hC : C ≠ (∅ : TarskiSet.{u})) (_hD : D ≠ (∅ : TarskiSet.{u}))
    (h1 : FUNCT_2.isFunctionOf f1 (ZFMISC_1.product3 A B C) D)
    (h2 : FUNCT_2.isFunctionOf f2 (ZFMISC_1.product3 A B C) D)
    (hv : ∀ a b c, SUBSET_1.isElement a A → SUBSET_1.isElement b B →
      SUBSET_1.isElement c C →
      FUNCT_1.apply f1 (XTUPLE_0.triple a b c) =
        FUNCT_1.apply f2 (XTUPLE_0.triple a b c)) :
    f1 = f2 :=
  th1 h1 h2 fun x y z hx hy hz =>
    hv x y z (SUBSET_1.isElement_of hx) (SUBSET_1.isElement_of hy)
      (SUBSET_1.isElement_of hz)

/-- Unlabeled `MULTOP_1` after `Th2` -/
theorem th3 {A B C D f1 f2 : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hC : C ≠ (∅ : TarskiSet.{u})) (hD : D ≠ (∅ : TarskiSet.{u}))
    (h1 : FUNCT_2.isFunctionOf f1 (ZFMISC_1.product3 A B C) D)
    (h2 : FUNCT_2.isFunctionOf f2 (ZFMISC_1.product3 A B C) D)
    (hv : ∀ a b c, SUBSET_1.isElement a A → SUBSET_1.isElement b B →
      SUBSET_1.isElement c C → apply3 f1 a b c = apply3 f2 a b c) :
    f1 = f2 :=
  th2 hA hB hC hD h1 h2 fun a b c ha hb hc =>
    (def1 f1 a b c).symm.trans
      ((hv a b c ha hb hc).trans (def1 f2 a b c))

/-! ## Mode `TriOp of A` -/

/-- Mode `TriOp of A` — `Function of [:A,A,A:],A`. -/
def isTriOp (f A : TarskiSet.{u}) : Prop :=
  FUNCT_2.isFunctionOf f (ZFMISC_1.product3 A A A) A

/-- Coherence: `TriOp of A` yields `Element of A` under `f.(a,b,c)`. -/
theorem apply3_triOp_isElement {A f a b c : TarskiSet.{u}}
    (hf : isTriOp f A)
    (ha : SUBSET_1.isElement a A) (hb : SUBSET_1.isElement b A)
    (hc : SUBSET_1.isElement c A) :
    SUBSET_1.isElement (apply3 f a b c) A := by
  have := Classical.propDecidable (A = (∅ : TarskiSet.{u}))
  by_cases hA : A = (∅ : TarskiSet.{u})
  · have hempty : f = (∅ : TarskiSet.{u}) :=
      FUNCT_2.functionOf_empty_cod hf hA
    exact Eq.subst (motive := fun s => SUBSET_1.isElement s A)
      (apply3_of_empty_fun hempty).symm
      ((SUBSET_1.isElement_iff_empty (x := ∅) (X := A)
        (hA ▸ XBOOLE_0.emptySet_isEmpty)).mpr XBOOLE_0.emptySet_isEmpty)
  · exact apply3_isElement hA hA hA hf ha hb hc

/-! ## Schemes `FuncEx3D`, `TriOpEx`, `Lambda3D`, `TriOpLambda` -/

/-- `MULTOP_1:sch FuncEx3D` -/
theorem sch_FuncEx3D (X Y Z T : TarskiSet.{u})
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hZ : Z ≠ (∅ : TarskiSet.{u})) (hT : T ≠ (∅ : TarskiSet.{u}))
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hP : ∀ x y z, SUBSET_1.isElement x X → SUBSET_1.isElement y Y →
      SUBSET_1.isElement z Z →
      ∃ t, SUBSET_1.isElement t T ∧ P x y z t) :
    ∃ f, FUNCT_2.isFunctionOf f (ZFMISC_1.product3 X Y Z) T ∧
      ∀ x y z, SUBSET_1.isElement x X → SUBSET_1.isElement y Y →
        SUBSET_1.isElement z Z →
        P x y z (FUNCT_1.apply f (XTUPLE_0.triple x y z)) := by
  let Q : TarskiSet.{u} → TarskiSet.{u} → Prop :=
    fun p w => ∀ x y z, SUBSET_1.isElement x X → SUBSET_1.isElement y Y →
      SUBSET_1.isElement z Z → p = XTUPLE_0.triple x y z → P x y z w
  have hXne := ne_imp_not_empty hX
  have hYne := ne_imp_not_empty hY
  have hZne := ne_imp_not_empty hZ
  have hTne := ne_imp_not_empty hT
  have hDomNe : ZFMISC_1.product3 X Y Z ≠ (∅ : TarskiSet.{u}) :=
    fun he =>
      (SUBSET_1.product3_nonempty hXne hYne hZne)
        (Eq.subst (motive := XBOOLE_0.isEmpty) he.symm XBOOLE_0.emptySet_isEmpty)
  have hQ : ∀ p, p ∈ ZFMISC_1.product3 X Y Z →
      ∃ t, t ∈ T ∧ Q p t := by
    intro p hp
    obtain ⟨x1, y1, z1, hx1, hy1, hz1, heq⟩ := MCART_1.th68 hp
    obtain ⟨t, ht, hPt⟩ :=
      hP x1 y1 z1 (SUBSET_1.isElement_of hx1) (SUBSET_1.isElement_of hy1)
        (SUBSET_1.isElement_of hz1)
    refine ⟨t, SUBSET_1.isElement_mem hTne ht, ?_⟩
    intro x y z hx hy hz heq2
    have ⟨hxeq, hyeq, hzeq⟩ := XTUPLE_0.th3 (heq.symm.trans heq2)
    exact Eq.subst (motive := fun s => P s y z t) hxeq
      (Eq.subst (motive := fun s => P x1 s z t) hyeq
        (Eq.subst (motive := fun s => P x1 y1 s t) hzeq hPt))
  obtain ⟨f, hf, hv⟩ :=
    FUNCT_2.sch_FuncExD (ZFMISC_1.product3 X Y Z) T hDomNe hT Q hQ
  refine ⟨f, hf, ?_⟩
  intro x y z hx hy hz
  have hp : XTUPLE_0.triple x y z ∈ ZFMISC_1.product3 X Y Z :=
    (MCART_1.th69 x y z X Y Z).mpr
      ⟨SUBSET_1.isElement_mem hXne hx, SUBSET_1.isElement_mem hYne hy,
        SUBSET_1.isElement_mem hZne hz⟩
  exact hv (XTUPLE_0.triple x y z) hp x y z hx hy hz rfl

/-- `MULTOP_1:sch TriOpEx` -/
theorem sch_TriOpEx (A : TarskiSet.{u}) (hA : A ≠ (∅ : TarskiSet.{u}))
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hP : ∀ x y z, SUBSET_1.isElement x A → SUBSET_1.isElement y A →
      SUBSET_1.isElement z A →
      ∃ t, SUBSET_1.isElement t A ∧ P x y z t) :
    ∃ o, isTriOp o A ∧
      ∀ a b c, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
        SUBSET_1.isElement c A → P a b c (apply3 o a b c) := by
  obtain ⟨f, hf, hv⟩ := sch_FuncEx3D A A A A hA hA hA hA P hP
  refine ⟨f, hf, ?_⟩
  intro a b c ha hb hc
  exact Eq.subst (motive := fun s => P a b c s) (def1 f a b c).symm
    (hv a b c ha hb hc)

/-- `MULTOP_1:sch Lambda3D` -/
theorem sch_Lambda3D (X Y Z T : TarskiSet.{u})
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hZ : Z ≠ (∅ : TarskiSet.{u})) (hT : T ≠ (∅ : TarskiSet.{u}))
    (F : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ x y z, SUBSET_1.isElement x X → SUBSET_1.isElement y Y →
      SUBSET_1.isElement z Z → SUBSET_1.isElement (F x y z) T) :
    ∃ f, FUNCT_2.isFunctionOf f (ZFMISC_1.product3 X Y Z) T ∧
      ∀ x y z, SUBSET_1.isElement x X → SUBSET_1.isElement y Y →
        SUBSET_1.isElement z Z →
        FUNCT_1.apply f (XTUPLE_0.triple x y z) = F x y z :=
  sch_FuncEx3D X Y Z T hX hY hZ hT (fun x y z t => t = F x y z)
    (fun x y z hx hy hz => ⟨F x y z, hF x y z hx hy hz, rfl⟩)

/-- `MULTOP_1:sch TriOpLambda` -/
theorem sch_TriOpLambda (A B C D : TarskiSet.{u})
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hC : C ≠ (∅ : TarskiSet.{u})) (hD : D ≠ (∅ : TarskiSet.{u}))
    (O : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hO : ∀ a b c, SUBSET_1.isElement a A → SUBSET_1.isElement b B →
      SUBSET_1.isElement c C → SUBSET_1.isElement (O a b c) D) :
    ∃ o, FUNCT_2.isFunctionOf o (ZFMISC_1.product3 A B C) D ∧
      ∀ a b c, SUBSET_1.isElement a A → SUBSET_1.isElement b B →
        SUBSET_1.isElement c C → apply3 o a b c = O a b c := by
  obtain ⟨f, hf, hv⟩ := sch_Lambda3D A B C D hA hB hC hD O hO
  refine ⟨f, hf, ?_⟩
  intro a b c ha hb hc
  exact (def1 f a b c).trans (hv a b c ha hb hc)

/-! ## `f.(a,b,c,d)` (`MULTOP_1:def 2`) -/

/-- `MULTOP_1:def 2` — quaternary application `f.(a,b,c,d) = f.[a,b,c,d]`. -/
noncomputable def apply4 (f a b c d : TarskiSet.{u}) : TarskiSet.{u} :=
  FUNCT_1.apply f (XTUPLE_0.quadruple a b c d)

theorem def2 (f a b c d : TarskiSet.{u}) :
    apply4 f a b c d = FUNCT_1.apply f (XTUPLE_0.quadruple a b c d) :=
  rfl

private theorem apply4_of_empty_fun {f a b c d : TarskiSet.{u}}
    (hf : f = (∅ : TarskiSet.{u})) : apply4 f a b c d = (∅ : TarskiSet.{u}) := by
  have hdom : XTUPLE_0.quadruple a b c d ∉ RELAT_1.dom f := by
    intro hx
    have hx' : XTUPLE_0.quadruple a b c d ∈ RELAT_1.dom (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s =>
        XTUPLE_0.quadruple a b c d ∈ RELAT_1.dom s) hf hx
    have hx'' : XTUPLE_0.quadruple a b c d ∈ (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => XTUPLE_0.quadruple a b c d ∈ s)
        RELAT_1.th38.1 hx'
    exact (XBOOLE_0.empty_iff _).mp hx''
  exact FUNCT_1.apply_of_not_mem hdom

/-- Coherence: `Function of [:A,B,C,D:],E` with nonempty domains yields
`Element of E`. -/
theorem apply4_isElement {A B C D E f a b c d : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hC : C ≠ (∅ : TarskiSet.{u})) (hD : D ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f (ZFMISC_1.product4 A B C D) E)
    (ha : SUBSET_1.isElement a A) (hb : SUBSET_1.isElement b B)
    (hc : SUBSET_1.isElement c C) (hd : SUBSET_1.isElement d D) :
    SUBSET_1.isElement (apply4 f a b c d) E := by
  have ha' : a ∈ A := SUBSET_1.isElement_mem (ne_imp_not_empty hA) ha
  have hb' : b ∈ B := SUBSET_1.isElement_mem (ne_imp_not_empty hB) hb
  have hc' : c ∈ C := SUBSET_1.isElement_mem (ne_imp_not_empty hC) hc
  have hd' : d ∈ D := SUBSET_1.isElement_mem (ne_imp_not_empty hD) hd
  have habcd : XTUPLE_0.quadruple a b c d ∈ ZFMISC_1.product4 A B C D :=
    (MCART_1.th80 a b c d A B C D).mpr ⟨ha', hb', hc', hd'⟩
  have := Classical.propDecidable (E = (∅ : TarskiSet.{u}))
  by_cases hE : E = (∅ : TarskiSet.{u})
  · have hempty : f = (∅ : TarskiSet.{u}) := FUNCT_2.functionOf_empty_cod hf hE
    exact Eq.subst (motive := fun s => SUBSET_1.isElement s E)
      (apply4_of_empty_fun hempty).symm
      ((SUBSET_1.isElement_iff_empty (x := ∅) (X := E)
        (hE ▸ XBOOLE_0.emptySet_isEmpty)).mpr XBOOLE_0.emptySet_isEmpty)
  · exact SUBSET_1.isElement_of (FUNCT_2.th5 hf hE habcd)

/-! ## Equality of quaternary functions -/

/-- `MULTOP_1:4` (`Th4`) -/
theorem th4 {X Y Z S D f1 f2 : TarskiSet.{u}}
    (h1 : FUNCT_2.isFunctionOf f1 (ZFMISC_1.product4 X Y Z S) D)
    (h2 : FUNCT_2.isFunctionOf f2 (ZFMISC_1.product4 X Y Z S) D)
    (hv : ∀ x y z s, x ∈ X → y ∈ Y → z ∈ Z → s ∈ S →
      FUNCT_1.apply f1 (XTUPLE_0.quadruple x y z s) =
        FUNCT_1.apply f2 (XTUPLE_0.quadruple x y z s)) :
    f1 = f2 := by
  refine FUNCT_2.th12 h1 h2 ?_
  intro t ht
  obtain ⟨x, y, z, s, hx, hy, hz, hs, heq⟩ := MCART_1.th79 ht
  exact Eq.subst (motive := fun u =>
      FUNCT_1.apply f1 u = FUNCT_1.apply f2 u) heq.symm
    (hv x y z s hx hy hz hs)

/-- `MULTOP_1:5` (`Th5`) -/
theorem th5 {A B C D E f1 f2 : TarskiSet.{u}}
    (_hA : A ≠ (∅ : TarskiSet.{u})) (_hB : B ≠ (∅ : TarskiSet.{u}))
    (_hC : C ≠ (∅ : TarskiSet.{u})) (_hD : D ≠ (∅ : TarskiSet.{u}))
    (_hE : E ≠ (∅ : TarskiSet.{u}))
    (h1 : FUNCT_2.isFunctionOf f1 (ZFMISC_1.product4 A B C D) E)
    (h2 : FUNCT_2.isFunctionOf f2 (ZFMISC_1.product4 A B C D) E)
    (hv : ∀ a b c d, SUBSET_1.isElement a A → SUBSET_1.isElement b B →
      SUBSET_1.isElement c C → SUBSET_1.isElement d D →
      FUNCT_1.apply f1 (XTUPLE_0.quadruple a b c d) =
        FUNCT_1.apply f2 (XTUPLE_0.quadruple a b c d)) :
    f1 = f2 :=
  th4 h1 h2 fun x y z s hx hy hz hs =>
    hv x y z s (SUBSET_1.isElement_of hx) (SUBSET_1.isElement_of hy)
      (SUBSET_1.isElement_of hz) (SUBSET_1.isElement_of hs)

/-- Unlabeled `MULTOP_1` after `Th5` -/
theorem th6 {A B C D E f1 f2 : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hC : C ≠ (∅ : TarskiSet.{u})) (hD : D ≠ (∅ : TarskiSet.{u}))
    (hE : E ≠ (∅ : TarskiSet.{u}))
    (h1 : FUNCT_2.isFunctionOf f1 (ZFMISC_1.product4 A B C D) E)
    (h2 : FUNCT_2.isFunctionOf f2 (ZFMISC_1.product4 A B C D) E)
    (hv : ∀ a b c d, SUBSET_1.isElement a A → SUBSET_1.isElement b B →
      SUBSET_1.isElement c C → SUBSET_1.isElement d D →
      apply4 f1 a b c d = apply4 f2 a b c d) :
    f1 = f2 :=
  th5 hA hB hC hD hE h1 h2 fun a b c d ha hb hc hd =>
    (def2 f1 a b c d).symm.trans
      ((hv a b c d ha hb hc hd).trans (def2 f2 a b c d))

/-! ## Mode `QuaOp of A` -/

/-- Mode `QuaOp of A` — `Function of [:A,A,A,A:],A`. -/
def isQuaOp (f A : TarskiSet.{u}) : Prop :=
  FUNCT_2.isFunctionOf f (ZFMISC_1.product4 A A A A) A

/-- Coherence: `QuaOp of A` yields `Element of A` under `f.(a,b,c,d)`. -/
theorem apply4_quaOp_isElement {A f a b c d : TarskiSet.{u}}
    (hf : isQuaOp f A)
    (ha : SUBSET_1.isElement a A) (hb : SUBSET_1.isElement b A)
    (hc : SUBSET_1.isElement c A) (hd : SUBSET_1.isElement d A) :
    SUBSET_1.isElement (apply4 f a b c d) A := by
  have := Classical.propDecidable (A = (∅ : TarskiSet.{u}))
  by_cases hA : A = (∅ : TarskiSet.{u})
  · have hempty : f = (∅ : TarskiSet.{u}) :=
      FUNCT_2.functionOf_empty_cod hf hA
    exact Eq.subst (motive := fun s => SUBSET_1.isElement s A)
      (apply4_of_empty_fun hempty).symm
      ((SUBSET_1.isElement_iff_empty (x := ∅) (X := A)
        (hA ▸ XBOOLE_0.emptySet_isEmpty)).mpr XBOOLE_0.emptySet_isEmpty)
  · exact apply4_isElement hA hA hA hA hf ha hb hc hd

/-! ## Schemes `FuncEx4D`, `QuaOpEx`, `Lambda4D`, `QuaOpLambda` -/

/-- `MULTOP_1:sch FuncEx4D` -/
theorem sch_FuncEx4D (X Y Z S T : TarskiSet.{u})
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hZ : Z ≠ (∅ : TarskiSet.{u})) (hS : S ≠ (∅ : TarskiSet.{u}))
    (hT : T ≠ (∅ : TarskiSet.{u}))
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} →
      TarskiSet.{u} → Prop)
    (hP : ∀ x y z s, SUBSET_1.isElement x X → SUBSET_1.isElement y Y →
      SUBSET_1.isElement z Z → SUBSET_1.isElement s S →
      ∃ t, SUBSET_1.isElement t T ∧ P x y z s t) :
    ∃ f, FUNCT_2.isFunctionOf f (ZFMISC_1.product4 X Y Z S) T ∧
      ∀ x y z s, SUBSET_1.isElement x X → SUBSET_1.isElement y Y →
        SUBSET_1.isElement z Z → SUBSET_1.isElement s S →
        P x y z s (FUNCT_1.apply f (XTUPLE_0.quadruple x y z s)) := by
  let Q : TarskiSet.{u} → TarskiSet.{u} → Prop :=
    fun p w => ∀ x y z s, SUBSET_1.isElement x X → SUBSET_1.isElement y Y →
      SUBSET_1.isElement z Z → SUBSET_1.isElement s S →
      p = XTUPLE_0.quadruple x y z s → P x y z s w
  have hXne := ne_imp_not_empty hX
  have hYne := ne_imp_not_empty hY
  have hZne := ne_imp_not_empty hZ
  have hSne := ne_imp_not_empty hS
  have hTne := ne_imp_not_empty hT
  have hDomNe : ZFMISC_1.product4 X Y Z S ≠ (∅ : TarskiSet.{u}) :=
    fun he =>
      (SUBSET_1.product4_nonempty hXne hYne hZne hSne)
        (Eq.subst (motive := XBOOLE_0.isEmpty) he.symm XBOOLE_0.emptySet_isEmpty)
  have hQ : ∀ p, p ∈ ZFMISC_1.product4 X Y Z S →
      ∃ t, t ∈ T ∧ Q p t := by
    intro p hp
    obtain ⟨x1, y1, z1, s1, hx1, hy1, hz1, hs1, heq⟩ := MCART_1.th79 hp
    obtain ⟨t, ht, hPt⟩ :=
      hP x1 y1 z1 s1 (SUBSET_1.isElement_of hx1) (SUBSET_1.isElement_of hy1)
        (SUBSET_1.isElement_of hz1) (SUBSET_1.isElement_of hs1)
    refine ⟨t, SUBSET_1.isElement_mem hTne ht, ?_⟩
    intro x y z s hx hy hz hs heq2
    have ⟨hxeq, hyeq, hzeq, hseq⟩ := XTUPLE_0.th5 (heq.symm.trans heq2)
    exact Eq.subst (motive := fun u => P u y z s t) hxeq
      (Eq.subst (motive := fun u => P x1 u z s t) hyeq
        (Eq.subst (motive := fun u => P x1 y1 u s t) hzeq
          (Eq.subst (motive := fun u => P x1 y1 z1 u t) hseq hPt)))
  obtain ⟨f, hf, hv⟩ :=
    FUNCT_2.sch_FuncExD (ZFMISC_1.product4 X Y Z S) T hDomNe hT Q hQ
  refine ⟨f, hf, ?_⟩
  intro x y z s hx hy hz hs
  have hp : XTUPLE_0.quadruple x y z s ∈ ZFMISC_1.product4 X Y Z S :=
    (MCART_1.th80 x y z s X Y Z S).mpr
      ⟨SUBSET_1.isElement_mem hXne hx, SUBSET_1.isElement_mem hYne hy,
        SUBSET_1.isElement_mem hZne hz, SUBSET_1.isElement_mem hSne hs⟩
  exact hv (XTUPLE_0.quadruple x y z s) hp x y z s hx hy hz hs rfl

/-- `MULTOP_1:sch QuaOpEx` -/
theorem sch_QuaOpEx (A : TarskiSet.{u}) (hA : A ≠ (∅ : TarskiSet.{u}))
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} →
      TarskiSet.{u} → Prop)
    (hP : ∀ x y z s, SUBSET_1.isElement x A → SUBSET_1.isElement y A →
      SUBSET_1.isElement z A → SUBSET_1.isElement s A →
      ∃ t, SUBSET_1.isElement t A ∧ P x y z s t) :
    ∃ o, isQuaOp o A ∧
      ∀ a b c d, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
        SUBSET_1.isElement c A → SUBSET_1.isElement d A →
        P a b c d (apply4 o a b c d) := by
  obtain ⟨f, hf, hv⟩ := sch_FuncEx4D A A A A A hA hA hA hA hA P hP
  refine ⟨f, hf, ?_⟩
  intro a b c d ha hb hc hd
  exact Eq.subst (motive := fun u => P a b c d u) (def2 f a b c d).symm
    (hv a b c d ha hb hc hd)

/-- `MULTOP_1:sch Lambda4D` -/
theorem sch_Lambda4D (X Y Z S T : TarskiSet.{u})
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hZ : Z ≠ (∅ : TarskiSet.{u})) (hS : S ≠ (∅ : TarskiSet.{u}))
    (hT : T ≠ (∅ : TarskiSet.{u}))
    (F : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} →
      TarskiSet.{u})
    (hF : ∀ x y z s, SUBSET_1.isElement x X → SUBSET_1.isElement y Y →
      SUBSET_1.isElement z Z → SUBSET_1.isElement s S →
      SUBSET_1.isElement (F x y z s) T) :
    ∃ f, FUNCT_2.isFunctionOf f (ZFMISC_1.product4 X Y Z S) T ∧
      ∀ x y z s, SUBSET_1.isElement x X → SUBSET_1.isElement y Y →
        SUBSET_1.isElement z Z → SUBSET_1.isElement s S →
        FUNCT_1.apply f (XTUPLE_0.quadruple x y z s) = F x y z s :=
  sch_FuncEx4D X Y Z S T hX hY hZ hS hT
    (fun x y z s t => t = F x y z s)
    (fun x y z s hx hy hz hs => ⟨F x y z s, hF x y z s hx hy hz hs, rfl⟩)

/-- `MULTOP_1:sch QuaOpLambda` -/
theorem sch_QuaOpLambda (A : TarskiSet.{u}) (hA : A ≠ (∅ : TarskiSet.{u}))
    (O : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} →
      TarskiSet.{u})
    (hO : ∀ a b c d, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
      SUBSET_1.isElement c A → SUBSET_1.isElement d A →
      SUBSET_1.isElement (O a b c d) A) :
    ∃ o, isQuaOp o A ∧
      ∀ a b c d, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
        SUBSET_1.isElement c A → SUBSET_1.isElement d A →
        apply4 o a b c d = O a b c d := by
  obtain ⟨f, hf, hv⟩ := sch_Lambda4D A A A A A hA hA hA hA hA O hO
  refine ⟨f, hf, ?_⟩
  intro a b c d ha hb hc hd
  exact (def2 f a b c d).trans (hv a b c d ha hb hc hd)

end MULTOP_1
