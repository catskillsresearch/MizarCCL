import MizarCCL.GRFUNC_1
import MizarCCL.RELAT_2
import MizarCCL.RELSET_1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/partfun1.miz`.
Authors: Czesław Byliński (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Partial Functions

1–1 Lean rendering of Mizar article `PARTFUN1`
(`vendor/mml/partfun1.miz`). Import is `GRFUNC_1`, `RELAT_2`, and
`RELSET_1`.
-/

universe u

open TarskiSet TARSKI

namespace PARTFUN1

/-- `PARTFUN1:1` (`Th1`) -/
theorem th1 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (h : ∀ x, x ∈ RELAT_1.dom f ∩ RELAT_1.dom g →
      FUNCT_1.apply f x = FUNCT_1.apply g x) :
    ∃ h, FUNCT_1.isFunction h ∧ f ∪ g = h := by
  have huniq : ∀ x y1 y2,
      TARSKI.pair x y1 ∈ f ∪ g → TARSKI.pair x y2 ∈ f ∪ g → y1 = y2 := by
    intro x y1 y2 hp1 hp2
    have o1 := (XBOOLE_0.def3 f g (TARSKI.pair x y1)).mp hp1
    have o2 := (XBOOLE_0.def3 f g (TARSKI.pair x y2)).mp hp2
    have hf1 : TARSKI.pair x y1 ∈ f →
        x ∈ RELAT_1.dom f ∧ y1 = FUNCT_1.apply f x :=
      (FUNCT_1.th1 hf.2 (x := x) (y := y1)).mp
    have hg1 : TARSKI.pair x y1 ∈ g →
        x ∈ RELAT_1.dom g ∧ y1 = FUNCT_1.apply g x :=
      (FUNCT_1.th1 hg.2 (x := x) (y := y1)).mp
    have hf2 : TARSKI.pair x y2 ∈ f →
        x ∈ RELAT_1.dom f ∧ y2 = FUNCT_1.apply f x :=
      (FUNCT_1.th1 hf.2 (x := x) (y := y2)).mp
    have hg2 : TARSKI.pair x y2 ∈ g →
        x ∈ RELAT_1.dom g ∧ y2 = FUNCT_1.apply g x :=
      (FUNCT_1.th1 hg.2 (x := x) (y := y2)).mp
    exact Or.elim o1
      (fun h1f => Or.elim o2
        (fun h2f => (hf1 h1f).2.trans (hf2 h2f).2.symm)
        (fun h2g =>
          let ⟨hd1, he1⟩ := hf1 h1f
          let ⟨hd2, he2⟩ := hg2 h2g
          he1.trans
            ((h x ((XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom g) x).mpr
              ⟨hd1, hd2⟩)).trans he2.symm)))
      (fun h1g => Or.elim o2
        (fun h2f =>
          let ⟨hd1, he1⟩ := hg1 h1g
          let ⟨hd2, he2⟩ := hf2 h2f
          he1.trans
            ((h x ((XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom g) x).mpr
              ⟨hd2, hd1⟩)).symm.trans he2.symm))
        (fun h2g => (hg1 h1g).2.trans (hg2 h2g).2.symm))
  obtain ⟨H, hHfun, hchar⟩ :=
    FUNCT_1.sch_GraphFunc (RELAT_1.dom f ∪ RELAT_1.dom g)
      (fun x y => TARSKI.pair x y ∈ f ∪ g) huniq
  have heq : f ∪ g = H :=
    RELAT_1.rel_eq (RELAT_1.union_isRelation hf.1 hg.1) hHfun.1
      fun x y => by
        constructor
        · intro hp
          have hx : x ∈ RELAT_1.dom f ∪ RELAT_1.dom g :=
            (XBOOLE_0.def3 (RELAT_1.dom f) (RELAT_1.dom g) x).mpr
              (Or.elim ((XBOOLE_0.def3 f g (TARSKI.pair x y)).mp hp)
                (fun hf => Or.inl (RELAT_1.pair_mem_dom hf))
                (fun hg => Or.inr (RELAT_1.pair_mem_dom hg)))
          exact (hchar x y).mpr ⟨hx, hp⟩
        · intro hp
          exact ((hchar x y).mp hp).2
  exact ⟨H, hHfun, heq⟩

/-- `PARTFUN1:2` (`Th2`) -/
theorem th2 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (_hh : FUNCT_1.isFunction h)
    (heq : f ∪ g = h) {x : TarskiSet.{u}}
    (hx : x ∈ RELAT_1.dom f ∩ RELAT_1.dom g) :
    FUNCT_1.apply f x = FUNCT_1.apply g x := by
  have hdf : x ∈ RELAT_1.dom f :=
    ((XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom g) x).mp hx).1
  have hdg : x ∈ RELAT_1.dom g :=
    ((XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom g) x).mp hx).2
  have heqh : h = f ∪ g := heq.symm
  have hhg := GRFUNC_1.th15 (f := f) (g := g) (h := h) _hh.2 hg.2 hdg heqh
  have heqh2 : h = g ∪ f := heq.symm.trans (XBOOLE_0.union_comm f g)
  have hhf := GRFUNC_1.th15 (f := g) (g := f) (h := h) _hh.2 hf.2 hdf heqh2
  exact hhf.symm.trans hhg

/-- `PARTFUN1:sch LambdaC` -/
theorem sch_LambdaC (A : TarskiSet.{u})
    (C : TarskiSet.{u} → Prop)
    (F G : TarskiSet.{u} → TarskiSet.{u}) :
    ∃ f, FUNCT_1.isFunction f ∧ RELAT_1.dom f = A ∧
      ∀ x, x ∈ A →
        (C x → FUNCT_1.apply f x = F x) ∧
          (¬ C x → FUNCT_1.apply f x = G x) := by
  have hex : ∀ x, x ∈ A → ∃ y,
      (C x → y = F x) ∧ (¬ C x → y = G x) := by
    intro x _
    exact Or.elim (Classical.em (C x))
      (fun hC => ⟨F x, fun _ => rfl, fun hn => (hn hC).elim⟩)
      (fun hnC => ⟨G x, fun hC => (hnC hC).elim, fun _ => rfl⟩)
  have hfun : ∀ x y1 y2, x ∈ A →
      ((C x → y1 = F x) ∧ (¬ C x → y1 = G x)) →
      ((C x → y2 = F x) ∧ (¬ C x → y2 = G x)) → y1 = y2 := by
    intro x y1 y2 _ hp1 hp2
    exact Or.elim (Classical.em (C x))
      (fun hC => (hp1.1 hC).trans (hp2.1 hC).symm)
      (fun hn => (hp1.2 hn).trans (hp2.2 hn).symm)
  obtain ⟨f, hf, hd, hv⟩ := FUNCT_1.sch_FuncEx A
    (fun x y => (C x → y = F x) ∧ (¬ C x → y = G x)) hfun hex
  exact ⟨f, hf, hd, hv⟩

/-- `PARTFUN1:lm 1` -/
theorem lm1 (X Y : TarskiSet.{u}) :
    ∃ E, FUNCT_1.isFunction E ∧ RELAT_1.dom E ⊆ X ∧ RELAT_1.rng E ⊆ Y :=
  ⟨∅, FUNCT_1.empty_isFunction,
    Eq.subst (motive := fun s => s ⊆ X) RELAT_1.th38.1.symm
      (XBOOLE_1.th2 (X := X)),
    Eq.subst (motive := fun s => s ⊆ Y) RELAT_1.th38.2.symm
      (XBOOLE_1.th2 (X := Y))⟩

/-- Mizar mode `PartFunc of X,Y`. -/
def isPartFunc (f X Y : TarskiSet.{u}) : Prop :=
  FUNCT_1.isFunction f ∧ RELSET_1.isRelationOf f X Y

theorem empty_isPartFunc (X Y : TarskiSet.{u}) :
    isPartFunc (∅ : TarskiSet.{u}) X Y :=
  ⟨FUNCT_1.empty_isFunction, RELSET_1.th12 X Y⟩

theorem partFunc_of {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hd : RELAT_1.dom f ⊆ X) (hr : RELAT_1.rng f ⊆ Y) :
    isPartFunc f X Y :=
  ⟨hf, RELSET_1.th4 hf.1 hd hr⟩

/-- Unlabeled `PARTFUN1` (`L147`). -/
theorem th3 {f X Y y : TarskiSet.{u}} (hf : isPartFunc f X Y)
    (hy : y ∈ RELAT_1.rng f) :
    ∃ x, x ∈ X ∧ x ∈ RELAT_1.dom f ∧ y = FUNCT_1.apply f x := by
  obtain ⟨x, hx, heq⟩ := (FUNCT_1.def3 hf.1.2).mp hy
  exact ⟨x, RELSET_1.relationOf_defined hf.2 x hx, hx, heq⟩

/-- `PARTFUN1:4` (`Th4`) -/
theorem th4 {f Y x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hv : RELAT_1.isXvalued f Y) (hx : x ∈ RELAT_1.dom f) :
    FUNCT_1.apply f x ∈ Y :=
  hv _ (FUNCT_1.th3 hf.2 hx)

/-- Unlabeled `PARTFUN1` (`L168`). -/
theorem th5 {f1 f2 X Y : TarskiSet.{u}} (h1 : isPartFunc f1 X Y)
    (h2 : isPartFunc f2 X Y) (hd : RELAT_1.dom f1 = RELAT_1.dom f2)
    (hv : ∀ x, x ∈ X → x ∈ RELAT_1.dom f1 →
      FUNCT_1.apply f1 x = FUNCT_1.apply f2 x) :
    f1 = f2 :=
  FUNCT_1.th2 h1.1 h2.1 hd fun x hx =>
    hv x (RELSET_1.relationOf_defined h1.2 x hx) hx

/-- `PARTFUN1:sch PartFuncEx` -/
theorem sch_PartFuncEx (X Y : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hY : ∀ x y, x ∈ X → P x y → y ∈ Y)
    (hfun : ∀ x y1 y2, x ∈ X → P x y1 → P x y2 → y1 = y2) :
    ∃ f, isPartFunc f X Y ∧
      (∀ x, x ∈ RELAT_1.dom f ↔ x ∈ X ∧ ∃ y, P x y) ∧
      ∀ x, x ∈ RELAT_1.dom f → P x (FUNCT_1.apply f x) := by
  refine Or.elim (Classical.em (Y = (∅ : TarskiSet.{u}))) (fun hYe => ?_)
    (fun _ => ?_)
  · refine ⟨∅, empty_isPartFunc X Y, ?_, ?_⟩
    · intro x
      constructor
      · intro hx
        exact ((XBOOLE_0.empty_iff x).mp
          (Eq.subst (motive := fun s => x ∈ s) RELAT_1.th38.1 hx)).elim
      · intro ⟨hxX, ⟨y, hP⟩⟩
        exact (hY x y hxX hP
          |> (fun hy => (XBOOLE_0.empty_iff y).mp
            (Eq.subst (motive := fun s => y ∈ s) hYe hy))).elim
    · intro x hx
      exact ((XBOOLE_0.empty_iff x).mp
        (Eq.subst (motive := fun s => x ∈ s) RELAT_1.th38.1 hx)).elim
  · have hex : ∀ x, x ∈ X → ∃ z,
        ((∃ y, P x y) → P x z) ∧ ((∀ y, ¬ P x y) → z = (∅ : TarskiSet.{u})) := by
      intro x _
      exact Or.elim (Classical.em (∃ y, P x y))
        (fun ⟨y, hP⟩ => ⟨y, fun _ => hP, fun hn => (hn y hP).elim⟩)
        (fun hn => ⟨∅, fun hex => (hn hex).elim, fun _ => rfl⟩)
    have hq : ∀ x z1 z2, x ∈ X →
        (((∃ y, P x y) → P x z1) ∧ ((∀ y, ¬ P x y) → z1 = (∅ : TarskiSet.{u}))) →
        (((∃ y, P x y) → P x z2) ∧ ((∀ y, ¬ P x y) → z2 = (∅ : TarskiSet.{u}))) →
        z1 = z2 := by
      intro x z1 z2 hx hp1 hp2
      exact Or.elim (Classical.em (∃ y, P x y))
        (fun hex => hfun x z1 z2 hx (hp1.1 hex) (hp2.1 hex))
        (fun hn =>
          (hp1.2 (fun y hP => hn ⟨y, hP⟩)).trans
            (hp2.2 (fun y hP => hn ⟨y, hP⟩)).symm)
    obtain ⟨g, hg, hdg, hgv⟩ := FUNCT_1.sch_FuncEx X
      (fun x z => ((∃ y, P x y) → P x z) ∧
        ((∀ y, ¬ P x y) → z = (∅ : TarskiSet.{u}))) hq hex
    obtain ⟨S, hS⟩ :=
      XBOOLE_0.sch_separation X (fun x => ∃ y, P x y)
    let f := RELAT_1.restrict g S
    have hfF : FUNCT_1.isFunction f := FUNCT_1.restrict_isFunction hg
    have hdomf : RELAT_1.dom f ⊆ S := RELAT_1.th58 (R := g) (X := S)
    have hdomX : RELAT_1.dom f ⊆ X :=
      fun z hz => ((hS z).mp (hdomf z hz)).1
    have hrng : RELAT_1.rng f ⊆ Y := by
      intro y hy
      obtain ⟨x, hxD, heq⟩ := (FUNCT_1.def3 hfF.2).mp hy
      have hxS : x ∈ S := hdomf x hxD
      have ⟨hxX, hex⟩ := (hS x).mp hxS
      have hPg : P x (FUNCT_1.apply g x) := (hgv x hxX).1 hex
      have hyeq : y = FUNCT_1.apply g x :=
        heq.trans (FUNCT_1.th47 hg.2 hxD)
      exact hY x y hxX
        (Eq.subst (motive := fun s => P x s) hyeq.symm hPg)
    refine ⟨f, partFunc_of hfF hdomX hrng, ?_, ?_⟩
    · intro x
      constructor
      · intro hx
        exact (hS x).mp (hdomf x hx)
      · intro ⟨hxX, hex⟩
        have hxS : x ∈ S := (hS x).mpr ⟨hxX, hex⟩
        have hxg : x ∈ RELAT_1.dom g :=
          Eq.subst (motive := fun s => x ∈ s) hdg.symm hxX
        exact (RELAT_1.th57 (R := g) (X := S) (x := x)).mpr ⟨hxS, hxg⟩
    · intro x hx
      have hxS : x ∈ S := hdomf x hx
      have ⟨hxX, hex⟩ := (hS x).mp hxS
      have hPg : P x (FUNCT_1.apply g x) := (hgv x hxX).1 hex
      exact Eq.subst (motive := fun s => P x s)
        (FUNCT_1.th47 hg.2 hx).symm hPg

/-- `PARTFUN1:sch LambdaR` -/
theorem sch_LambdaR (X Y : TarskiSet.{u})
    (F : TarskiSet.{u} → TarskiSet.{u}) (P : TarskiSet.{u} → Prop)
    (hF : ∀ x, P x → F x ∈ Y) :
    ∃ f, isPartFunc f X Y ∧
      (∀ x, x ∈ RELAT_1.dom f ↔ x ∈ X ∧ P x) ∧
      ∀ x, x ∈ RELAT_1.dom f → FUNCT_1.apply f x = F x := by
  obtain ⟨f, hf, hdom, happ⟩ :=
    sch_PartFuncEx X Y (fun x y => P x ∧ y = F x)
      (fun x y _ hp =>
        Eq.subst (motive := fun s => s ∈ Y) hp.2.symm (hF x hp.1))
      (fun x y1 y2 _ hp1 hp2 => hp1.2.trans hp2.2.symm)
  refine ⟨f, hf, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have ⟨hxX, ⟨y, hP, _⟩⟩ := (hdom x).mp hx
      exact ⟨hxX, hP⟩
    · intro ⟨hxX, hP⟩
      exact (hdom x).mpr ⟨hxX, ⟨F x, hP, rfl⟩⟩
  · intro x hx
    exact (happ x hx).2

/-- Unlabeled `PARTFUN1` (`L305`). -/
theorem th6 {f X Y : TarskiSet.{u}} (hf : RELSET_1.isRelationOf f X Y) :
    RELAT_1.comp (RELAT_1.id X) f = f :=
  RELAT_1.th51 (RELSET_1.relationOf_isRelation hf)
    (RELSET_1.relationOf_defined hf)

/-- Unlabeled `PARTFUN1` (`L313`). -/
theorem th7 {f X Y : TarskiSet.{u}} (hf : RELSET_1.isRelationOf f X Y) :
    RELAT_1.comp f (RELAT_1.id Y) = f :=
  RELAT_1.th53 (RELSET_1.relationOf_isRelation hf)
    (RELSET_1.relationOf_valued hf)

/-- Unlabeled `PARTFUN1` (`L321`). -/
theorem th8 {f X Y : TarskiSet.{u}} (hf : isPartFunc f X Y)
    (h : ∀ x1 x2, x1 ∈ X → x2 ∈ X →
      x1 ∈ RELAT_1.dom f → x2 ∈ RELAT_1.dom f →
        FUNCT_1.apply f x1 = FUNCT_1.apply f x2 → x1 = x2) :
    FUNCT_1.isOneToOne f :=
  fun x1 x2 hx1 hx2 heq =>
    h x1 x2 (RELSET_1.relationOf_defined hf.2 x1 hx1)
      (RELSET_1.relationOf_defined hf.2 x2 hx2) hx1 hx2 heq

/-- Unlabeled `PARTFUN1` (`L332`). -/
theorem th9 {f X Y : TarskiSet.{u}} (hf : isPartFunc f X Y)
    (h1 : FUNCT_1.isOneToOne f) :
    isPartFunc (FUNCT_1.inv f) Y X :=
  partFunc_of (FUNCT_1.inv_isFunction hf.1 h1)
    (Eq.subst (motive := fun s => s ⊆ Y) (FUNCT_1.th33 h1).1
      (RELSET_1.relationOf_valued hf.2))
    (Eq.subst (motive := fun s => s ⊆ X) (FUNCT_1.th33 h1).2
      (RELSET_1.relationOf_defined hf.2))

/-- Unlabeled `PARTFUN1` (`L345`). -/
theorem th10 {f X Y Z : TarskiSet.{u}} (hf : isPartFunc f X Y) :
    isPartFunc (RELAT_1.restrict f Z) Z Y :=
  partFunc_of (FUNCT_1.restrict_isFunction hf.1)
    (RELAT_1.th58 (R := f) (X := Z))
    (XBOOLE_1.th1 (X := RELAT_1.rng (RELAT_1.restrict f Z))
      (Y := RELAT_1.rng f) (Z := Y)
      (RELAT_1.th11 (RELAT_1.th59 (R := f) (X := Z))).2
      (RELSET_1.relationOf_valued hf.2))

/-- `PARTFUN1:11` (`Th11`) -/
theorem th11 {f X Y Z : TarskiSet.{u}} (hf : isPartFunc f X Y) :
    isPartFunc (RELAT_1.restrict f Z) X Y :=
  partFunc_of (FUNCT_1.restrict_isFunction hf.1)
    (XBOOLE_1.th1 (X := RELAT_1.dom (RELAT_1.restrict f Z))
      (Y := RELAT_1.dom f) (Z := X)
      (RELAT_1.th60 (R := f) (X := Z))
      (RELSET_1.relationOf_defined hf.2))
    (XBOOLE_1.th1 (X := RELAT_1.rng (RELAT_1.restrict f Z))
      (Y := RELAT_1.rng f) (Z := Y)
      (RELAT_1.th11 (RELAT_1.th59 (R := f) (X := Z))).2
      (RELSET_1.relationOf_valued hf.2))

/-- Unlabeled `PARTFUN1` (`L364`). -/
theorem th12 {f X Y Z : TarskiSet.{u}} (hf : isPartFunc f X Y) :
    isPartFunc (RELAT_1.restrictRng Z f) X Z :=
  partFunc_of (FUNCT_1.restrictRng_isFunction hf.1)
    (XBOOLE_1.th1 (X := RELAT_1.dom (RELAT_1.restrictRng Z f))
      (Y := RELAT_1.dom f) (Z := X)
      (FUNCT_1.th56 hf.1 (Y := Z))
      (RELSET_1.relationOf_defined hf.2))
    (RELAT_1.th85 (Y := Z) (R := f))

/-- Unlabeled `PARTFUN1` (`L372`). -/
theorem th13 {f X Y Z : TarskiSet.{u}} (hf : isPartFunc f X Y) :
    isPartFunc (RELAT_1.restrictRng Z f) X Y :=
  partFunc_of (FUNCT_1.restrictRng_isFunction hf.1)
    (XBOOLE_1.th1 (X := RELAT_1.dom (RELAT_1.restrictRng Z f))
      (Y := RELAT_1.dom f) (Z := X)
      (FUNCT_1.th56 hf.1 (Y := Z))
      (RELSET_1.relationOf_defined hf.2))
    (XBOOLE_1.th1 (X := RELAT_1.rng (RELAT_1.restrictRng Z f))
      (Y := RELAT_1.rng f) (Z := Y)
      (RELAT_1.th11 (RELAT_1.th86 (Y := Z) (R := f))).2
      (RELSET_1.relationOf_valued hf.2))

/-- `PARTFUN1:14` (`Th14`) -/
theorem th14 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    isPartFunc (RELAT_1.restrict (RELAT_1.restrictRng Y f) X) X Y :=
  let r := RELAT_1.restrict (RELAT_1.restrictRng Y f) X
  have heq : r = RELAT_1.restrictRng Y (RELAT_1.restrict f X) :=
    RELAT_1.th109 (R := f) (Y := Y) (X := X)
  have hf2 : FUNCT_1.isFunction (RELAT_1.restrict f X) :=
    FUNCT_1.restrict_isFunction hf
  partFunc_of
    (Eq.subst (motive := FUNCT_1.isFunction) heq.symm
      (FUNCT_1.restrictRng_isFunction hf2))
    (Eq.subst (motive := fun s => RELAT_1.dom s ⊆ X) heq.symm
      (XBOOLE_1.th1 (X := RELAT_1.dom (RELAT_1.restrictRng Y
          (RELAT_1.restrict f X)))
        (Y := RELAT_1.dom (RELAT_1.restrict f X)) (Z := X)
        (FUNCT_1.th56 hf2 (Y := Y))
        (RELAT_1.th58 (R := f) (X := X))))
    (Eq.subst (motive := fun s => RELAT_1.rng s ⊆ Y) heq.symm
      (RELAT_1.th85 (Y := Y) (R := RELAT_1.restrict f X)))

/-- `<:f,X,Y:> = Y|`f|X`. -/
noncomputable def clip (f X Y : TarskiSet.{u}) : TarskiSet.{u} :=
  RELAT_1.restrict (RELAT_1.restrictRng Y f) X

theorem clip_isPartFunc {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    isPartFunc (clip f X Y) X Y :=
  th14 hf

/-- Unlabeled `PARTFUN1` (`L384`). -/
theorem th15 {f X Y y : TarskiSet.{u}} (hf : isPartFunc f X Y)
    (hy : y ∈ RELAT_1.image f X) :
    ∃ x, x ∈ X ∧ x ∈ RELAT_1.dom f ∧ y = FUNCT_1.apply f x := by
  obtain ⟨x, hxD, hxX, heq⟩ := (FUNCT_1.def6 hf.1.2).mp hy
  exact ⟨x, hxX, hxD, heq⟩

/-- `PARTFUN1:16` (`Th16`) -/
theorem th16 {f x Y : TarskiSet.{u}} (hf : isPartFunc f (TARSKI.singleton x) Y) :
    RELAT_1.rng f ⊆ TARSKI.singleton (FUNCT_1.apply f x) := by
  have hd := (ZFMISC_1.th33 (Y := RELAT_1.dom f) (x := x)).mp
    (RELSET_1.relationOf_defined hf.2)
  exact Or.elim hd
    (fun hempty =>
      fun y hy =>
        ((XBOOLE_0.empty_iff y).mp
          (Eq.subst (motive := fun s => y ∈ s)
            ((RELAT_1.th42 hf.1.1).mp hempty) hy)).elim)
    (fun hsing =>
      Eq.subst (motive := fun s => s ⊆ TARSKI.singleton (FUNCT_1.apply f x))
        (FUNCT_1.th4 hf.1.2 hsing).symm
        (fun _ hz => hz))

/-- Unlabeled `PARTFUN1` (`L405`). -/
theorem th17 {f x Y : TarskiSet.{u}}
    (hf : isPartFunc f (TARSKI.singleton x) Y) :
    FUNCT_1.isOneToOne f :=
  fun x1 x2 hx1 hx2 _ =>
    let h1 := (singleton_iff x x1).mp (RELSET_1.relationOf_defined hf.2 x1 hx1)
    let h2 := (singleton_iff x x2).mp (RELSET_1.relationOf_defined hf.2 x2 hx2)
    h1.trans h2.symm

/-- Unlabeled `PARTFUN1` (`L417`). -/
theorem th18 {f x Y P : TarskiSet.{u}}
    (hf : isPartFunc f (TARSKI.singleton x) Y) :
    RELAT_1.image f P ⊆ TARSKI.singleton (FUNCT_1.apply f x) :=
  XBOOLE_1.th1 (X := RELAT_1.image f P) (Y := RELAT_1.rng f)
    (Z := TARSKI.singleton (FUNCT_1.apply f x))
    (RELAT_1.th111 (R := f) (X := P)) (th16 hf)

/-- Unlabeled `PARTFUN1` (`L425`). -/
theorem th19 {f x X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hd : RELAT_1.dom f = TARSKI.singleton x) (hx : x ∈ X)
    (hy : FUNCT_1.apply f x ∈ Y) : isPartFunc f X Y :=
  partFunc_of hf
    (Eq.subst (motive := fun s => s ⊆ X) hd.symm
      ((ZFMISC_1.th31 (x := x) (X := X)).mpr hx))
    (Eq.subst (motive := fun s => s ⊆ Y) (FUNCT_1.th4 hf.2 hd).symm
      ((ZFMISC_1.th31 (x := FUNCT_1.apply f x) (X := Y)).mpr hy))

/-- `PARTFUN1:20` (`Th20`) -/
theorem th20 {f X y x : TarskiSet.{u}}
    (hf : isPartFunc f X (TARSKI.singleton y)) (hx : x ∈ RELAT_1.dom f) :
    FUNCT_1.apply f x = y :=
  (singleton_iff y (FUNCT_1.apply f x)).mp
    (th4 hf.1 (RELSET_1.relationOf_valued hf.2) hx)

/-- Unlabeled `PARTFUN1` (`L450`). -/
theorem th21 {f1 f2 X y : TarskiSet.{u}}
    (h1 : isPartFunc f1 X (TARSKI.singleton y))
    (h2 : isPartFunc f2 X (TARSKI.singleton y))
    (hd : RELAT_1.dom f1 = RELAT_1.dom f2) : f1 = f2 :=
  FUNCT_1.th2 h1.1 h2.1 hd fun x hx =>
    (th20 h1 hx).trans
      (th20 h2 (Eq.subst (motive := fun s => x ∈ s) hd hx)).symm

/-- `PARTFUN1:22` (`Th22`) -/
theorem th22 {f X Y : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f) :
    clip f X Y ⊆ f :=
  XBOOLE_1.th1 (X := clip f X Y) (Y := RELAT_1.restrictRng Y f) (Z := f)
    (RELAT_1.th59 (R := RELAT_1.restrictRng Y f) (X := X))
    (RELAT_1.th86 (Y := Y) (R := f))

/-- `PARTFUN1:23` (`Th23`) -/
theorem th23 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    RELAT_1.dom (clip f X Y) ⊆ RELAT_1.dom f ∧
      RELAT_1.rng (clip f X Y) ⊆ RELAT_1.rng f :=
  RELAT_1.th11 (th22 hf)

/-- `PARTFUN1:24` (`Th24`) -/
theorem th24 {f X Y x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    x ∈ RELAT_1.dom (clip f X Y) ↔
      x ∈ RELAT_1.dom f ∧ x ∈ X ∧ FUNCT_1.apply f x ∈ Y := by
  constructor
  · intro hx
    have hxI : x ∈ RELAT_1.dom (RELAT_1.restrictRng Y f) ∩ X :=
      Eq.subst (motive := fun s => x ∈ s)
        (RELAT_1.th61 (R := RELAT_1.restrictRng Y f) (X := X)) hx
    have ⟨hxY, hxX⟩ :=
      (XBOOLE_0.def4 (RELAT_1.dom (RELAT_1.restrictRng Y f)) X x).mp hxI
    have ⟨hdf, hval⟩ := (FUNCT_1.th54 hf (Y := Y) (x := x)).mp hxY
    exact ⟨hdf, hxX, hval⟩
  · intro ⟨hdf, hxX, hval⟩
    have hxY : x ∈ RELAT_1.dom (RELAT_1.restrictRng Y f) :=
      (FUNCT_1.th54 hf (Y := Y) (x := x)).mpr ⟨hdf, hval⟩
    exact Eq.subst (motive := fun s => x ∈ s)
      (RELAT_1.th61 (R := RELAT_1.restrictRng Y f) (X := X)).symm
      ((XBOOLE_0.def4 (RELAT_1.dom (RELAT_1.restrictRng Y f)) X x).mpr
        ⟨hxY, hxX⟩)

/-- `PARTFUN1:25` (`Th25`) -/
theorem th25 {f X Y x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hdf : x ∈ RELAT_1.dom f) (hx : x ∈ X) (hy : FUNCT_1.apply f x ∈ Y) :
    FUNCT_1.apply (clip f X Y) x = FUNCT_1.apply f x := by
  have hxY : x ∈ RELAT_1.dom (RELAT_1.restrictRng Y f) :=
    (FUNCT_1.th54 hf (Y := Y) (x := x)).mpr ⟨hdf, hy⟩
  have h1 : FUNCT_1.apply (RELAT_1.restrictRng Y f) x = FUNCT_1.apply f x :=
    FUNCT_1.th55 hf hxY
  have h2 : FUNCT_1.apply (clip f X Y) x =
      FUNCT_1.apply (RELAT_1.restrictRng Y f) x :=
    FUNCT_1.th49 (FUNCT_1.restrictRng_isFunction hf).2 hx
  exact h2.trans h1

/-- `PARTFUN1:26` (`Th26`) -/
theorem th26 {f X Y x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hx : x ∈ RELAT_1.dom (clip f X Y)) :
    FUNCT_1.apply (clip f X Y) x = FUNCT_1.apply f x :=
  let ⟨hdf, hxX, hy⟩ := (th24 hf).mp hx
  th25 hf hdf hxX hy

/-- Unlabeled `PARTFUN1` (`L539`). -/
theorem th27 {f g X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hsub : f ⊆ g) :
    clip f X Y ⊆ clip g X Y := by
  have hd : RELAT_1.dom (clip f X Y) ⊆ RELAT_1.dom (clip g X Y) := by
    intro x hx
    have ⟨hdf, hxX, hy⟩ := (th24 hf).mp hx
    have hdg : x ∈ RELAT_1.dom g := (RELAT_1.th11 hsub).1 x hdf
    have heq : FUNCT_1.apply f x = FUNCT_1.apply g x :=
      ((GRFUNC_1.th2 hf hg).mp hsub).2 x hdf
    exact (th24 hg).mpr
      ⟨hdg, hxX, Eq.subst (motive := fun s => s ∈ Y) heq hy⟩
  exact (GRFUNC_1.th2 (clip_isPartFunc hf).1 (clip_isPartFunc hg).1).mpr
    ⟨hd, fun x hx =>
      (th26 hf hx).trans
                ((((GRFUNC_1.th2 hf hg).mp hsub).2 x ((th23 hf).1 x hx)).trans
                  (th26 hg (hd x hx)).symm)⟩

/-- `PARTFUN1:28` (`Th28`) -/
theorem th28 {f X Y Z : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hZ : Z ⊆ X) : clip f Z Y ⊆ clip f X Y := by
  have hd : RELAT_1.dom (clip f Z Y) ⊆ RELAT_1.dom (clip f X Y) := by
    intro x hx
    have ⟨hdf, hxZ, hy⟩ := (th24 hf (X := Z) (Y := Y)).mp hx
    exact (th24 hf (X := X) (Y := Y)).mpr ⟨hdf, hZ x hxZ, hy⟩
  exact (GRFUNC_1.th2 (clip_isPartFunc hf).1 (clip_isPartFunc hf).1).mpr
    ⟨hd, fun x hx =>
      (th26 hf hx).trans (th26 hf (hd x hx)).symm⟩

/-- `PARTFUN1:29` (`Th29`) -/
theorem th29 {f X Y Z : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hZ : Z ⊆ Y) : clip f X Z ⊆ clip f X Y := by
  have hd : RELAT_1.dom (clip f X Z) ⊆ RELAT_1.dom (clip f X Y) := by
    intro x hx
    have ⟨hdf, hxX, hy⟩ := (th24 hf (X := X) (Y := Z)).mp hx
    exact (th24 hf (X := X) (Y := Y)).mpr ⟨hdf, hxX, hZ _ hy⟩
  exact (GRFUNC_1.th2 (clip_isPartFunc hf).1 (clip_isPartFunc hf).1).mpr
    ⟨hd, fun x hx =>
      (th26 hf hx).trans (th26 hf (hd x hx)).symm⟩

/-- Unlabeled `PARTFUN1` (`L617`). -/
theorem th30 {f X1 X2 Y1 Y2 : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hX : X1 ⊆ X2) (hY : Y1 ⊆ Y2) :
    clip f X1 Y1 ⊆ clip f X2 Y2 :=
  XBOOLE_1.th1 (th28 hf hX) (th29 hf hY)

/-- `PARTFUN1:31` (`Th31`) -/
theorem th31 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hd : RELAT_1.dom f ⊆ X) (hr : RELAT_1.rng f ⊆ Y) :
    f = clip f X Y := by
  have hsub : RELAT_1.dom f ⊆ RELAT_1.dom (clip f X Y) := by
    intro x hx
    exact (th24 hf).mpr ⟨hx, hd x hx, hr _ (FUNCT_1.th3 hf.2 hx)⟩
  have hdom : RELAT_1.dom f = RELAT_1.dom (clip f X Y) :=
    (XBOOLE_0.def10 (X := RELAT_1.dom f)
      (Y := RELAT_1.dom (clip f X Y))).mpr ⟨hsub, (th23 hf).1⟩
  exact FUNCT_1.th2 hf (clip_isPartFunc hf).1 hdom fun x hx =>
    (th26 hf (Eq.subst (motive := fun s => x ∈ s) hdom hx)).symm

/-- Unlabeled `PARTFUN1` (`L646`). -/
theorem th32 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    f = clip f (RELAT_1.dom f) (RELAT_1.rng f) :=
  th31 hf (fun _ hx => hx) (fun _ hx => hx)

/-- Unlabeled `PARTFUN1` (`L649`). -/
theorem th33 {f X Y : TarskiSet.{u}} (hf : isPartFunc f X Y) :
    clip f X Y = f :=
  (th31 hf.1 (RELSET_1.relationOf_defined hf.2)
    (RELSET_1.relationOf_valued hf.2)).symm

/-- `PARTFUN1:34` (`Th34`) -/
theorem th34 (X Y : TarskiSet.{u}) :
    clip (∅ : TarskiSet.{u}) X Y = (∅ : TarskiSet.{u}) :=
  (th31 FUNCT_1.empty_isFunction
    (Eq.subst (motive := fun s => s ⊆ X) RELAT_1.th38.1.symm
      (XBOOLE_1.th2 (X := X)))
    (Eq.subst (motive := fun s => s ⊆ Y) RELAT_1.th38.2.symm
      (XBOOLE_1.th2 (X := Y)))).symm

/-- `PARTFUN1:35` (`Th35`) -/
theorem th35 {f g X Y Z : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    RELAT_1.comp (clip f X Y) (clip g Y Z) ⊆ clip (RELAT_1.comp f g) X Z := by
  have hfC := clip_isPartFunc hf (X := X) (Y := Y)
  have hgC := clip_isPartFunc hg (X := Y) (Y := Z)
  have hcomp : FUNCT_1.isFunction (RELAT_1.comp (clip f X Y) (clip g Y Z)) :=
    FUNCT_1.comp_isFunction hfC.1 hgC.1
  have hd : RELAT_1.dom (RELAT_1.comp (clip f X Y) (clip g Y Z)) ⊆
      RELAT_1.dom (clip (RELAT_1.comp f g) X Z) := by
    intro x hx
    have ⟨hxF, hfx⟩ := (FUNCT_1.th11 hfC.1.2 (f := clip f X Y)
      (g := clip g Y Z) (x := x)).mp hx
    have ⟨hdf, hxX, _⟩ := (th24 hf).mp hxF
    have hfeq := th26 hf hxF
    have hfx2 : FUNCT_1.apply f x ∈ RELAT_1.dom (clip g Y Z) :=
      Eq.subst (motive := fun s => s ∈ RELAT_1.dom (clip g Y Z)) hfeq hfx
    have ⟨hdg, _, hgz⟩ := (th24 hg).mp hfx2
    have hgf : FUNCT_1.apply (RELAT_1.comp f g) x ∈ Z :=
      Eq.subst (motive := fun s => s ∈ Z)
        (FUNCT_1.th13 hf.2 hg.2 hdf).symm hgz
    have hxfg : x ∈ RELAT_1.dom (RELAT_1.comp f g) :=
      (FUNCT_1.th11 hf.2 (f := f) (g := g) (x := x)).mpr ⟨hdf, hdg⟩
    exact (th24 (FUNCT_1.comp_isFunction hf hg)).mpr ⟨hxfg, hxX, hgf⟩
  exact (GRFUNC_1.th2 hcomp
      (clip_isPartFunc (FUNCT_1.comp_isFunction hf hg)).1).mpr
    ⟨hd, fun x hx => by
      have ⟨hxF, hfx⟩ := (FUNCT_1.th11 hfC.1.2 (f := clip f X Y)
        (g := clip g Y Z) (x := x)).mp hx
      have hfeq := th26 hf hxF
      have hfx2 : FUNCT_1.apply f x ∈ RELAT_1.dom (clip g Y Z) :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.dom (clip g Y Z)) hfeq hfx
      have hdf := ((th24 hf).mp hxF).1
      have h1 := FUNCT_1.th12 hfC.1.2 hgC.1.2 hx
      have hmid : FUNCT_1.apply (clip g Y Z)
          (FUNCT_1.apply (clip f X Y) x) =
          FUNCT_1.apply g (FUNCT_1.apply f x) :=
        Eq.subst (motive := fun s =>
            FUNCT_1.apply (clip g Y Z) s =
              FUNCT_1.apply g (FUNCT_1.apply f x)) hfeq.symm
          (th26 hg hfx2)
      have h4 := (FUNCT_1.th13 hf.2 hg.2 hdf).symm
      have h5 := (th26 (FUNCT_1.comp_isFunction hf hg) (hd x hx)).symm
      exact (h1.trans hmid).trans (h4.trans h5)⟩

/-- `PARTFUN1:def 2` -/
def isTotal (f X : TarskiSet.{u}) : Prop := RELAT_1.dom f = X

theorem def2 (f X : TarskiSet.{u}) : isTotal f X ↔ RELAT_1.dom f = X :=
  Iff.rfl

/-- `PARTFUN1:40` (`Th40`) -/
theorem th40 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (h : isTotal (clip f X Y) X) : X ⊆ RELAT_1.dom f :=
  fun x hx => (th23 hf).1 x
    (Eq.subst (motive := fun s => x ∈ s) h.symm hx)

/-- Unlabeled `PARTFUN1` (`L715`). -/
theorem th36 {f g X Y Z : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (hY : RELAT_1.rng f ∩ RELAT_1.dom g ⊆ Y) :
    RELAT_1.comp (clip f X Y) (clip g Y Z) =
      clip (RELAT_1.comp f g) X Z := by
  have hfC := clip_isPartFunc hf (X := X) (Y := Y)
  have hgC := clip_isPartFunc hg (X := Y) (Y := Z)
  have hfg := FUNCT_1.comp_isFunction hf hg
  have hsub := th35 hf hg (X := X) (Y := Y) (Z := Z)
  have hd : RELAT_1.dom (clip (RELAT_1.comp f g) X Z) ⊆
      RELAT_1.dom (RELAT_1.comp (clip f X Y) (clip g Y Z)) := by
    intro x hx
    have ⟨hxfg, hxX, hval⟩ := (th24 hfg).mp hx
    have ⟨hdf, hdg⟩ :=
      (FUNCT_1.th11 hf.2 (f := f) (g := g) (x := x)).mp hxfg
    have hfr : FUNCT_1.apply f x ∈ RELAT_1.rng f := FUNCT_1.th3 hf.2 hdf
    have hin : FUNCT_1.apply f x ∈ RELAT_1.rng f ∩ RELAT_1.dom g :=
      (XBOOLE_0.def4 (RELAT_1.rng f) (RELAT_1.dom g)
        (FUNCT_1.apply f x)).mpr ⟨hfr, hdg⟩
    have hyY : FUNCT_1.apply f x ∈ Y := hY _ hin
    have hxF : x ∈ RELAT_1.dom (clip f X Y) :=
      (th24 hf).mpr ⟨hdf, hxX, hyY⟩
    have hgeq : FUNCT_1.apply (RELAT_1.comp f g) x =
        FUNCT_1.apply g (FUNCT_1.apply f x) :=
      FUNCT_1.th12 hf.2 hg.2 hxfg
    have hgz : FUNCT_1.apply g (FUNCT_1.apply f x) ∈ Z :=
      Eq.subst (motive := fun s => s ∈ Z) hgeq hval
    have hfxG : FUNCT_1.apply f x ∈ RELAT_1.dom (clip g Y Z) :=
      (th24 hg).mpr ⟨hdg, hyY, hgz⟩
    have hfeq := th25 hf hdf hxX hyY
    exact (FUNCT_1.th11 hfC.1.2 (f := clip f X Y) (g := clip g Y Z)
      (x := x)).mpr
      ⟨hxF, Eq.subst (motive := fun s => s ∈ RELAT_1.dom (clip g Y Z))
        hfeq.symm hfxG⟩
  have hv : ∀ x, x ∈ RELAT_1.dom (clip (RELAT_1.comp f g) X Z) →
      FUNCT_1.apply (clip (RELAT_1.comp f g) X Z) x =
        FUNCT_1.apply (RELAT_1.comp (clip f X Y) (clip g Y Z)) x := by
    intro x hx
    have h1 := th26 hfg hx
    have ⟨hxfg, _, _⟩ := (th24 hfg).mp hx
    have h2 := FUNCT_1.th12 hf.2 hg.2 hxfg
    have hxC := hd x hx
    have h3 := FUNCT_1.th12 hfC.1.2 hgC.1.2 hxC
    have ⟨hxF, _⟩ := (FUNCT_1.th11 hfC.1.2 (f := clip f X Y)
      (g := clip g Y Z) (x := x)).mp hxC
    have hfeq := th26 hf hxF
    have hfx2 : FUNCT_1.apply f x ∈ RELAT_1.dom (clip g Y Z) :=
      Eq.subst (motive := fun s => s ∈ RELAT_1.dom (clip g Y Z))
        hfeq ((FUNCT_1.th11 hfC.1.2 (f := clip f X Y)
          (g := clip g Y Z) (x := x)).mp hxC).2
    have h4 := th26 hg hfx2
    have hmid : FUNCT_1.apply (clip g Y Z)
        (FUNCT_1.apply (clip f X Y) x) =
        FUNCT_1.apply g (FUNCT_1.apply f x) :=
      Eq.subst (motive := fun s =>
          FUNCT_1.apply (clip g Y Z) s =
            FUNCT_1.apply g (FUNCT_1.apply f x)) hfeq.symm h4
    exact h1.trans (h2.trans (hmid.symm.trans h3.symm))
  have hrev : clip (RELAT_1.comp f g) X Z ⊆
      RELAT_1.comp (clip f X Y) (clip g Y Z) :=
    (GRFUNC_1.th2 (clip_isPartFunc hfg).1
      (FUNCT_1.comp_isFunction hfC.1 hgC.1)).mpr ⟨hd, hv⟩
  exact (XBOOLE_0.def10
      (X := RELAT_1.comp (clip f X Y) (clip g Y Z))
      (Y := clip (RELAT_1.comp f g) X Z)).mpr ⟨hsub, hrev⟩

/-- `PARTFUN1:37` (`Th37`) -/
theorem th37 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (h1 : FUNCT_1.isOneToOne f) : FUNCT_1.isOneToOne (clip f X Y) :=
  FUNCT_1.th52 (FUNCT_1.restrictRng_isFunction hf).2
    (FUNCT_1.th58 hf h1)


/-- Unlabeled `PARTFUN1` (`L782`). -/
theorem th38 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (h1 : FUNCT_1.isOneToOne f) :
    FUNCT_1.inv (clip f X Y) = clip (FUNCT_1.inv f) Y X := by
  have hfC : isPartFunc (clip f X Y) X Y := clip_isPartFunc hf
  have h1C : FUNCT_1.isOneToOne (clip f X Y) := th37 hf h1
  have hfinv : FUNCT_1.isFunction (FUNCT_1.inv f) := FUNCT_1.inv_isFunction hf h1
  have hCinv : FUNCT_1.isFunction (FUNCT_1.inv (clip f X Y)) :=
    FUNCT_1.inv_isFunction hfC.1 h1C
  have hdom : RELAT_1.dom (FUNCT_1.inv (clip f X Y)) =
      RELAT_1.dom (clip (FUNCT_1.inv f) Y X) := by
    apply TARSKI.extensionality
    intro y
    constructor
    · intro hy
      have hyR : y ∈ RELAT_1.rng (clip f X Y) :=
        Eq.subst (motive := fun s => y ∈ s) (FUNCT_1.th33 h1C).1.symm hy
      obtain ⟨x, hxD, hyeq⟩ := (FUNCT_1.def3 hfC.1.2).mp hyR
      have hfy : FUNCT_1.apply f x = y :=
        (th26 hf hxD).symm.trans hyeq.symm
      have ⟨hdf, hxX, hyY0⟩ := (th24 hf).mp hxD
      have hyY : y ∈ Y :=
        Eq.subst (motive := fun s => s ∈ Y) hfy hyY0
      have hyRf : y ∈ RELAT_1.rng f := (th23 hf).2 y hyR
      have hyDinv : y ∈ RELAT_1.dom (FUNCT_1.inv f) :=
        Eq.subst (motive := fun s => y ∈ s) (FUNCT_1.th33 h1).1 hyRf
      have hinvy : FUNCT_1.apply (FUNCT_1.inv f) y = x :=
        Eq.subst (motive := fun s => FUNCT_1.apply (FUNCT_1.inv f) s = x)
          hfy (FUNCT_1.th34 hf h1 hdf).1
      exact (th24 hfinv (X := Y) (Y := X)).mpr
        ⟨hyDinv, hyY,
          Eq.subst (motive := fun s => s ∈ X) hinvy.symm hxX⟩
    · intro hy
      have ⟨hyDinv, hyY, hxX0⟩ :=
        (th24 hfinv (X := Y) (Y := X)).mp hy
      have hyRf : y ∈ RELAT_1.rng f :=
        Eq.subst (motive := fun s => y ∈ s)
          (FUNCT_1.th33 h1).1.symm hyDinv
      obtain ⟨x, hdf, hyeq⟩ := (FUNCT_1.def3 hf.2).mp hyRf
      have hinvy : FUNCT_1.apply (FUNCT_1.inv f) y = x :=
        Eq.subst (motive := fun s => FUNCT_1.apply (FUNCT_1.inv f) s = x)
          hyeq.symm (FUNCT_1.th34 hf h1 hdf).1
      have hxX : x ∈ X :=
        Eq.subst (motive := fun s => s ∈ X) hinvy hxX0
      have hxC : x ∈ RELAT_1.dom (clip f X Y) :=
        (th24 hf).mpr
          ⟨hdf, hxX, Eq.subst (motive := fun s => s ∈ Y) hyeq hyY⟩
      have hval : FUNCT_1.apply (clip f X Y) x = y :=
        (th26 hf hxC).trans hyeq.symm
      have hyRC : y ∈ RELAT_1.rng (clip f X Y) :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.rng (clip f X Y))
          hval (FUNCT_1.th3 hfC.1.2 hxC)
      exact Eq.subst (motive := fun s => y ∈ s) (FUNCT_1.th33 h1C).1 hyRC
  refine FUNCT_1.th2 hCinv (clip_isPartFunc hfinv).1 hdom fun y hy => ?_
  have hy2 : y ∈ RELAT_1.dom (clip (FUNCT_1.inv f) Y X) :=
    Eq.subst (motive := fun s => y ∈ s) hdom hy
  have ⟨hyDinv, hyY, hxX0⟩ := (th24 hfinv (X := Y) (Y := X)).mp hy2
  have hyRf : y ∈ RELAT_1.rng f :=
    Eq.subst (motive := fun s => y ∈ s) (FUNCT_1.th33 h1).1.symm hyDinv
  obtain ⟨x, hdf, hyeq⟩ := (FUNCT_1.def3 hf.2).mp hyRf
  have hinvy : FUNCT_1.apply (FUNCT_1.inv f) y = x :=
    Eq.subst (motive := fun s => FUNCT_1.apply (FUNCT_1.inv f) s = x)
      hyeq.symm (FUNCT_1.th34 hf h1 hdf).1
  have hxX : x ∈ X :=
    Eq.subst (motive := fun s => s ∈ X) hinvy hxX0
  have hxC : x ∈ RELAT_1.dom (clip f X Y) :=
    (th24 hf).mpr
      ⟨hdf, hxX, Eq.subst (motive := fun s => s ∈ Y) hyeq hyY⟩
  have hleft : FUNCT_1.apply (clip (FUNCT_1.inv f) Y X) y =
      FUNCT_1.apply (FUNCT_1.inv f) y :=
    th26 hfinv hy2
  have hclipx : FUNCT_1.apply (clip f X Y) x = y :=
    (th26 hf hxC).trans hyeq.symm
  have hright : FUNCT_1.apply (FUNCT_1.inv (clip f X Y)) y = x :=
    Eq.subst (motive := fun s =>
        FUNCT_1.apply (FUNCT_1.inv (clip f X Y)) s = x)
      hclipx (FUNCT_1.th34 hfC.1 h1C hxC).1
  exact hright.trans ((hleft.trans hinvy).symm)

/-- Unlabeled `PARTFUN1` (`L848`). -/
theorem th39 {f X Y Z : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f) :
    RELAT_1.restrictRng Z (clip f X Y) = clip f X (Z ∩ Y) := by
  have h1 : clip f X Y =
      RELAT_1.restrictRng Y (RELAT_1.restrict f X) :=
    RELAT_1.th109 (R := f) (Y := Y) (X := X)
  have h2 : RELAT_1.restrictRng Z (clip f X Y) =
      RELAT_1.restrictRng Z (RELAT_1.restrictRng Y (RELAT_1.restrict f X)) :=
    congrArg (RELAT_1.restrictRng Z) h1
  have h3 : RELAT_1.restrictRng Z
      (RELAT_1.restrictRng Y (RELAT_1.restrict f X)) =
      RELAT_1.restrictRng (Z ∩ Y) (RELAT_1.restrict f X) :=
    RELAT_1.th96 (Y := Z) (X := Y) (R := RELAT_1.restrict f X)
  have h4 : clip f X (Z ∩ Y) =
      RELAT_1.restrictRng (Z ∩ Y) (RELAT_1.restrict f X) :=
    RELAT_1.th109 (R := f) (Y := Z ∩ Y) (X := X)
  exact h2.trans (h3.trans h4.symm)

/-- Unlabeled `PARTFUN1` (`L900`). -/
theorem th41 {X Y : TarskiSet.{u}}
    (h : isTotal (clip (∅ : TarskiSet.{u}) X Y) X) :
    X = (∅ : TarskiSet.{u}) := by
  have hdom : RELAT_1.dom (∅ : TarskiSet.{u}) = X :=
    Eq.subst (motive := fun s => RELAT_1.dom s = X) (th34 X Y) h
  exact hdom.symm.trans RELAT_1.th38.1

/-- Unlabeled `PARTFUN1` (`L907`). -/
theorem th42 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hX : X ⊆ RELAT_1.dom f) (hY : RELAT_1.rng f ⊆ Y) :
    isTotal (clip f X Y) X :=
  (XBOOLE_0.def10 (X := RELAT_1.dom (clip f X Y)) (Y := X)).mpr
    ⟨fun x hx => ((th24 hf).mp hx).2.1, fun x hx =>
      (th24 hf).mpr ⟨hX x hx, hx, hY _ (FUNCT_1.th3 hf.2 (hX x hx))⟩⟩

/-- Unlabeled `PARTFUN1` (`L924`). -/
theorem th43 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (h : isTotal (clip f X Y) X) :
    RELAT_1.image f X ⊆ Y := by
  intro y hy
  obtain ⟨x, hxD, hxX, heq⟩ := (FUNCT_1.def6 hf.2).mp hy
  have hxC : x ∈ RELAT_1.dom (clip f X Y) :=
    Eq.subst (motive := fun s => x ∈ s) h.symm hxX
  have hy2 : FUNCT_1.apply (clip f X Y) x ∈ RELAT_1.rng (clip f X Y) :=
    FUNCT_1.th3 (clip_isPartFunc hf).1.2 hxC
  have hr : RELAT_1.rng (clip f X Y) ⊆ Y :=
    RELSET_1.relationOf_valued (clip_isPartFunc hf).2
  exact Eq.subst (motive := fun s => s ∈ Y)
    ((th26 hf hxC).trans heq.symm) (hr _ hy2)

/-- Unlabeled `PARTFUN1` (`L939`). -/
theorem th44 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hX : X ⊆ RELAT_1.dom f) (hY : RELAT_1.image f X ⊆ Y) :
    isTotal (clip f X Y) X :=
  (XBOOLE_0.def10 (X := RELAT_1.dom (clip f X Y)) (Y := X)).mpr
    ⟨fun x hx => ((th24 hf).mp hx).2.1, fun x hx =>
      (th24 hf).mpr ⟨hX x hx, hx,
        hY _ ((FUNCT_1.def6 hf.2).mpr ⟨x, hX x hx, hx, rfl⟩)⟩⟩

/-- `PARTFUN1:def 3` — `PFuncs(X,Y)`. -/
noncomputable def PFuncs (X Y : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (XBOOLE_0.sch_separation (ZFMISC_1.bool (ZFMISC_1.product X Y))
      (fun z => FUNCT_1.isFunction z ∧ RELAT_1.dom z ⊆ X ∧
        RELAT_1.rng z ⊆ Y))

theorem def3 (X Y x : TarskiSet.{u}) :
    x ∈ PFuncs X Y ↔
      ∃ f, FUNCT_1.isFunction f ∧ x = f ∧ RELAT_1.dom f ⊆ X ∧
        RELAT_1.rng f ⊆ Y := by
  have h := Classical.choose_spec
    (XBOOLE_0.sch_separation (ZFMISC_1.bool (ZFMISC_1.product X Y))
      (fun z => FUNCT_1.isFunction z ∧ RELAT_1.dom z ⊆ X ∧
        RELAT_1.rng z ⊆ Y))
  constructor
  · intro hx
    have ⟨_, hf, hd, hr⟩ := (h x).mp hx
    exact ⟨x, hf, rfl, hd, hr⟩
  · intro ⟨f, hf, heq, hd, hr⟩
    have hf' : FUNCT_1.isFunction x :=
      Eq.subst (motive := FUNCT_1.isFunction) heq.symm hf
    have hd' : RELAT_1.dom x ⊆ X :=
      Eq.subst (motive := fun s => RELAT_1.dom s ⊆ X) heq.symm hd
    have hr' : RELAT_1.rng x ⊆ Y :=
      Eq.subst (motive := fun s => RELAT_1.rng s ⊆ Y) heq.symm hr
    have hsub : x ⊆ ZFMISC_1.product X Y :=
      RELSET_1.th4 hf'.1 hd' hr'
    have hbool : x ∈ ZFMISC_1.bool (ZFMISC_1.product X Y) :=
      (ZFMISC_1.def1 (ZFMISC_1.product X Y) x).mpr hsub
    exact (h x).mpr ⟨hbool, hf', hd', hr'⟩

/-- `PARTFUN1:45` (`Th45`) -/
theorem th45 {f X Y : TarskiSet.{u}} (hf : isPartFunc f X Y) :
    f ∈ PFuncs X Y :=
  (def3 X Y f).mpr
    ⟨f, hf.1, rfl, RELSET_1.relationOf_defined hf.2,
      RELSET_1.relationOf_valued hf.2⟩

/-- `PARTFUN1:46` (`Th46`) -/
theorem th46 {f X Y : TarskiSet.{u}} (hf : f ∈ PFuncs X Y) :
    isPartFunc f X Y := by
  obtain ⟨F, hF, heq, hd, hr⟩ := (def3 X Y f).mp hf
  exact Eq.subst (motive := fun s => isPartFunc s X Y) heq.symm
    (partFunc_of hF hd hr)

/-- Unlabeled `PARTFUN1` (`L1029`). -/
theorem th47 {f X Y : TarskiSet.{u}} (hf : f ∈ PFuncs X Y) :
    isPartFunc f X Y :=
  th46 hf

/-- Unlabeled `PARTFUN1` (`L1032`). -/
theorem th48 (Y : TarskiSet.{u}) :
    PFuncs (∅ : TarskiSet.{u}) Y =
      TARSKI.singleton (∅ : TarskiSet.{u}) := by
  apply TARSKI.extensionality
  intro x
  constructor
  · intro hx
    have hf := th46 hx
    have hdom : RELAT_1.dom x = (∅ : TarskiSet.{u}) :=
      (XBOOLE_0.def10 (X := RELAT_1.dom x)
        (Y := (∅ : TarskiSet.{u}))).mpr
        ⟨RELSET_1.relationOf_defined hf.2, XBOOLE_1.th2⟩
    have hempty : x = (∅ : TarskiSet.{u}) :=
      RELAT_1.th41 hf.1.1 (Or.inl hdom)
    exact (singleton_iff (∅ : TarskiSet.{u}) x).mpr hempty
  · intro hx
    have heq : x = (∅ : TarskiSet.{u}) :=
      (singleton_iff (∅ : TarskiSet.{u}) x).mp hx
    exact Eq.subst (motive := fun s => s ∈ PFuncs (∅ : TarskiSet.{u}) Y)
      heq.symm (th45 (empty_isPartFunc ∅ Y))

/-- Unlabeled `PARTFUN1` (`L1049`). -/
theorem th49 (X : TarskiSet.{u}) :
    PFuncs X (∅ : TarskiSet.{u}) =
      TARSKI.singleton (∅ : TarskiSet.{u}) := by
  apply TARSKI.extensionality
  intro x
  constructor
  · intro hx
    have hf := th46 hx
    have hrng : RELAT_1.rng x = (∅ : TarskiSet.{u}) :=
      (XBOOLE_0.def10 (X := RELAT_1.rng x)
        (Y := (∅ : TarskiSet.{u}))).mpr
        ⟨RELSET_1.relationOf_valued hf.2, XBOOLE_1.th2⟩
    have hempty : x = (∅ : TarskiSet.{u}) :=
      RELAT_1.th41 hf.1.1 (Or.inr hrng)
    exact (singleton_iff (∅ : TarskiSet.{u}) x).mpr hempty
  · intro hx
    have heq : x = (∅ : TarskiSet.{u}) :=
      (singleton_iff (∅ : TarskiSet.{u}) x).mp hx
    exact Eq.subst (motive := fun s => s ∈ PFuncs X (∅ : TarskiSet.{u}))
      heq.symm (th45 (empty_isPartFunc X ∅))

/-- Unlabeled `PARTFUN1` (`L1066`). -/
theorem th50 {X1 X2 Y1 Y2 : TarskiSet.{u}} (hX : X1 ⊆ X2) (hY : Y1 ⊆ Y2) :
    PFuncs X1 Y1 ⊆ PFuncs X2 Y2 := by
  intro f hf
  have hp := th46 hf
  exact th45 (partFunc_of hp.1
    (XBOOLE_1.th1 (RELSET_1.relationOf_defined hp.2) hX)
    (XBOOLE_1.th1 (RELSET_1.relationOf_valued hp.2) hY))

/-- `PARTFUN1:def 4` -/
def tolerates (f g : TarskiSet.{u}) : Prop :=
  ∀ x, x ∈ RELAT_1.dom f ∩ RELAT_1.dom g →
    FUNCT_1.apply f x = FUNCT_1.apply g x

theorem def4 (f g : TarskiSet.{u}) :
    tolerates f g ↔
      ∀ x, x ∈ RELAT_1.dom f ∩ RELAT_1.dom g →
        FUNCT_1.apply f x = FUNCT_1.apply g x :=
  Iff.rfl

theorem tolerates_refl (f : TarskiSet.{u}) : tolerates f f :=
  fun _ _ => rfl

theorem tolerates_symm {f g : TarskiSet.{u}} (h : tolerates f g) :
    tolerates g f :=
  fun x hx =>
    (h x (Eq.subst (motive := fun s => x ∈ s)
      (XBOOLE_0.inter_comm (RELAT_1.dom g) (RELAT_1.dom f)) hx)).symm

/-- `PARTFUN1:51` (`Th51`) -/
theorem th51 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    tolerates f g ↔ ∃ h, FUNCT_1.isFunction h ∧ f ∪ g = h :=
  ⟨fun ht => th1 hf hg ht, fun ⟨h, hh, heq⟩ => fun x hx => th2 hf hg hh heq hx⟩

/-- `PARTFUN1:52` (`Th52`) -/
theorem th52 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    tolerates f g ↔
      ∃ h, FUNCT_1.isFunction h ∧ f ⊆ h ∧ g ⊆ h := by
  constructor
  · intro ht
    obtain ⟨h, hh, heq⟩ := (th51 hf hg).mp ht
    exact ⟨h, hh,
      Eq.subst (motive := fun s => f ⊆ s) heq (XBOOLE_1.th7 (X := f) (Y := g)),
      Eq.subst (motive := fun s => g ⊆ s) heq
        (Eq.subst (motive := fun s => g ⊆ s) (XBOOLE_0.union_comm f g).symm
          (XBOOLE_1.th7 (X := g) (Y := f)))⟩
  · intro ⟨h, hh, hfsub, hgsub⟩
    have hun : FUNCT_1.isFunction (f ∪ g) :=
      GRFUNC_1.th1 hh (XBOOLE_1.th8 hfsub hgsub)
    exact (th51 hf hg).mpr ⟨f ∪ g, hun, rfl⟩

/-- `PARTFUN1:53` (`Th53`) -/
theorem th53 {f g : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g) (hd : RELAT_1.dom f ⊆ RELAT_1.dom g) :
    tolerates f g ↔
      ∀ x, x ∈ RELAT_1.dom f → FUNCT_1.apply f x = FUNCT_1.apply g x := by
  have hinter : RELAT_1.dom f ∩ RELAT_1.dom g = RELAT_1.dom f :=
    XBOOLE_1.th28 (X := RELAT_1.dom f) (Y := RELAT_1.dom g) hd
  constructor
  · intro ht x hx
    exact ht x (Eq.subst (motive := fun s => x ∈ s) hinter.symm hx)
  · intro hv x hx
    exact hv x (Eq.subst (motive := fun s => x ∈ s) hinter hx)

/-- Unlabeled `PARTFUN1` (`L1131`). -/
theorem th54 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (h : f ⊆ g) : tolerates f g :=
  (th52 hf hg).mpr ⟨g, hg, h, fun _ hx => hx⟩

/-- `PARTFUN1:55` (`Th55`) -/
theorem th55 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hd : RELAT_1.dom f = RELAT_1.dom g)
    (ht : tolerates f g) : f = g :=
  FUNCT_1.th2 hf hg hd fun x hx =>
    ((th53 hf hg (fun y hy =>
      Eq.subst (motive := fun s => y ∈ s) hd hy)).mp ht) x hx

/-- Unlabeled `PARTFUN1` (`L1145`). -/
theorem th56 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f) (RELAT_1.dom g)) :
    tolerates f g :=
  (th51 hf hg).mpr ⟨f ∪ g, GRFUNC_1.th13 hf hg hmiss, rfl⟩

/-- Unlabeled `PARTFUN1` (`L1154`). -/
theorem th57 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (hfsub : f ⊆ h) (hgsub : g ⊆ h) : tolerates f g :=
  (th52 hf hg).mpr ⟨h, hh, hfsub, hgsub⟩

/-- Unlabeled `PARTFUN1` (`L1157`). -/
theorem th58 {f g h X Y : TarskiSet.{u}} (_hf : isPartFunc f X Y)
    (hg : isPartFunc g X Y) (hh : FUNCT_1.isFunction h)
    (ht : tolerates f h) (hsub : g ⊆ f) : tolerates g h := by
  intro x hx
  have ⟨hxg, hxh⟩ :=
    (XBOOLE_0.def4 (RELAT_1.dom g) (RELAT_1.dom h) x).mp hx
  have heq : FUNCT_1.apply g x = FUNCT_1.apply f x :=
    ((GRFUNC_1.th2 hg.1 _hf.1).mp hsub).2 x hxg
  have hxf : x ∈ RELAT_1.dom f := (RELAT_1.th11 hsub).1 x hxg
  have hxI : x ∈ RELAT_1.dom f ∩ RELAT_1.dom h :=
    (XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom h) x).mpr ⟨hxf, hxh⟩
  exact heq.trans (ht x hxI)

/-- `PARTFUN1:59` (`Th59`) -/
theorem th59 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    tolerates (∅ : TarskiSet.{u}) f :=
  (th51 FUNCT_1.empty_isFunction hf).mpr
    ⟨f, hf, XBOOLE_1.th12 (X := (∅ : TarskiSet.{u})) (Y := f)
      (XBOOLE_1.th2 (X := f))⟩

/-- Unlabeled `PARTFUN1` (`L1185`). -/
theorem th60 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    tolerates (clip (∅ : TarskiSet.{u}) X Y) f :=
  Eq.subst (motive := fun s => tolerates s f) (th34 X Y).symm (th59 hf)

/-- Unlabeled `PARTFUN1` (`L1193`). -/
theorem th61 {f g X y : TarskiSet.{u}}
    (hf : isPartFunc f X (TARSKI.singleton y))
    (hg : isPartFunc g X (TARSKI.singleton y)) : tolerates f g :=
  fun x hx =>
    let ⟨hxf, hxg⟩ :=
      (XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom g) x).mp hx
    (th20 hf hxf).trans (th20 hg hxg).symm

/-- Unlabeled `PARTFUN1` (`L1207`). -/
theorem th62 {f X : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    tolerates (RELAT_1.restrict f X) f :=
  th54 (FUNCT_1.restrict_isFunction hf) hf (RELAT_1.th59 (R := f) (X := X))

/-- Unlabeled `PARTFUN1` (`L1215`). -/
theorem th63 {f Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    tolerates (RELAT_1.restrictRng Y f) f :=
  th54 (FUNCT_1.restrictRng_isFunction hf) hf (RELAT_1.th86 (Y := Y) (R := f))

/-- `PARTFUN1:64` (`Th64`) -/
theorem th64 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    tolerates (RELAT_1.restrict (RELAT_1.restrictRng Y f) X) f :=
  th54 (th14 hf).1 hf (th22 hf)

/-- Unlabeled `PARTFUN1` (`L1232`). -/
theorem th65 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    tolerates (clip f X Y) f :=
  th64 hf

/-- `PARTFUN1:66` (`Th66`) -/
theorem th66 {f g X Y : TarskiSet.{u}} (hf : isPartFunc f X Y)
    (hg : isPartFunc g X Y) (htf : isTotal f X) (htg : isTotal g X)
    (ht : tolerates f g) : f = g :=
  th55 hf.1 hg.1 (htf.trans htg.symm) ht

/-- `PARTFUN1:67` (`Th67`) -/
theorem th67 {f g h X Y : TarskiSet.{u}} (hf : isPartFunc f X Y)
    (hg : isPartFunc g X Y) (_hh : isPartFunc h X Y)
    (hfh : tolerates f h) (hgh : tolerates g h) (hth : isTotal h X) :
    tolerates f g := by
  intro x hx
  have ⟨hxf, hxg⟩ :=
    (XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom g) x).mp hx
  have hxh : x ∈ RELAT_1.dom h :=
    Eq.subst (motive := fun s => x ∈ s) hth.symm
      (RELSET_1.relationOf_defined hf.2 x hxf)
  have hxI1 : x ∈ RELAT_1.dom f ∩ RELAT_1.dom h :=
    (XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom h) x).mpr ⟨hxf, hxh⟩
  have hxI2 : x ∈ RELAT_1.dom g ∩ RELAT_1.dom h :=
    (XBOOLE_0.def4 (RELAT_1.dom g) (RELAT_1.dom h) x).mpr ⟨hxg, hxh⟩
  exact (hfh x hxI1).trans (hgh x hxI2).symm

/-- `PARTFUN1:68` (`Th68`) -/
theorem th68 {f g X Y : TarskiSet.{u}} (hf : isPartFunc f X Y)
    (hg : isPartFunc g X Y)
    (hYX : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (ht : tolerates f g) :
    ∃ h, isPartFunc h X Y ∧ isTotal h X ∧ tolerates f h ∧ tolerates g h := by
  refine Or.elim (Classical.em (Y = (∅ : TarskiSet.{u})))
    (fun hYe => ?_) (fun hne => ?_)
  · have hXe : X = (∅ : TarskiSet.{u}) := hYX hYe
    refine ⟨∅, empty_isPartFunc X Y, ?_,
      tolerates_symm (th59 hf.1), tolerates_symm (th59 hg.1)⟩
    exact Eq.subst (motive := fun s => RELAT_1.dom (∅ : TarskiSet.{u}) = s)
      hXe.symm RELAT_1.th38.1
  · obtain ⟨y0, hy0⟩ := XBOOLE_0.th7 hne
    have hex : ∀ x, x ∈ X → ∃ z,
        (x ∈ RELAT_1.dom f → z = FUNCT_1.apply f x) ∧
          (x ∈ RELAT_1.dom g → z = FUNCT_1.apply g x) ∧
            (x ∉ RELAT_1.dom f ∧ x ∉ RELAT_1.dom g → z = y0) := by
      intro x _
      refine Or.elim (Classical.em (x ∈ RELAT_1.dom f)) (fun hxf => ?_)
        (fun hnf => ?_)
      · refine Or.elim (Classical.em (x ∈ RELAT_1.dom g)) (fun hxg => ?_)
          (fun hng => ?_)
        · refine ⟨FUNCT_1.apply f x, fun _ => rfl, ?_, fun ⟨hnf, _⟩ => (hnf hxf).elim⟩
          intro _
          have hxI : x ∈ RELAT_1.dom f ∩ RELAT_1.dom g :=
            (XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom g) x).mpr ⟨hxf, hxg⟩
          exact ht x hxI
        · exact ⟨FUNCT_1.apply f x, fun _ => rfl,
            fun hxg => (hng hxg).elim, fun ⟨hnf, _⟩ => (hnf hxf).elim⟩
      · refine Or.elim (Classical.em (x ∈ RELAT_1.dom g)) (fun hxg => ?_)
          (fun hng => ?_)
        · exact ⟨FUNCT_1.apply g x, fun hxf => (hnf hxf).elim,
            fun _ => rfl, fun ⟨_, hng'⟩ => (hng' hxg).elim⟩
        · exact ⟨y0, fun hxf => (hnf hxf).elim, fun hxg => (hng hxg).elim,
            fun _ => rfl⟩
    have hfun : ∀ x z1 z2, x ∈ X →
        ((x ∈ RELAT_1.dom f → z1 = FUNCT_1.apply f x) ∧
          (x ∈ RELAT_1.dom g → z1 = FUNCT_1.apply g x) ∧
            (x ∉ RELAT_1.dom f ∧ x ∉ RELAT_1.dom g → z1 = y0)) →
        ((x ∈ RELAT_1.dom f → z2 = FUNCT_1.apply f x) ∧
          (x ∈ RELAT_1.dom g → z2 = FUNCT_1.apply g x) ∧
            (x ∉ RELAT_1.dom f ∧ x ∉ RELAT_1.dom g → z2 = y0)) →
        z1 = z2 := by
      intro x z1 z2 _ hp1 hp2
      refine Or.elim (Classical.em (x ∈ RELAT_1.dom f))
        (fun hxf => (hp1.1 hxf).trans (hp2.1 hxf).symm)
        (fun hnf => Or.elim (Classical.em (x ∈ RELAT_1.dom g))
          (fun hxg => (hp1.2.1 hxg).trans (hp2.2.1 hxg).symm)
          (fun hng => (hp1.2.2 ⟨hnf, hng⟩).trans (hp2.2.2 ⟨hnf, hng⟩).symm))
    obtain ⟨h, hh, hdh, hv⟩ := FUNCT_1.sch_FuncEx X
      (fun x z => (x ∈ RELAT_1.dom f → z = FUNCT_1.apply f x) ∧
        (x ∈ RELAT_1.dom g → z = FUNCT_1.apply g x) ∧
          (x ∉ RELAT_1.dom f ∧ x ∉ RELAT_1.dom g → z = y0)) hfun hex
    have hrng : RELAT_1.rng h ⊆ Y := by
      intro z hz
      obtain ⟨x, hxD, heq⟩ := (FUNCT_1.def3 hh.2).mp hz
      have hxX : x ∈ X := Eq.subst (motive := fun s => x ∈ s) hdh hxD
      have hp := hv x hxX
      refine Or.elim (Classical.em (x ∈ RELAT_1.dom f)) (fun hxf => ?_)
        (fun hnf => ?_)
      · have hzf : z = FUNCT_1.apply f x := heq.trans (hp.1 hxf)
        exact Eq.subst (motive := fun s => s ∈ Y) hzf.symm
          (th4 hf.1 (RELSET_1.relationOf_valued hf.2) hxf)
      · refine Or.elim (Classical.em (x ∈ RELAT_1.dom g)) (fun hxg => ?_)
          (fun hng => ?_)
        · have hzg : z = FUNCT_1.apply g x := heq.trans (hp.2.1 hxg)
          exact Eq.subst (motive := fun s => s ∈ Y) hzg.symm
            (th4 hg.1 (RELSET_1.relationOf_valued hg.2) hxg)
        · have hzy : z = y0 := heq.trans (hp.2.2 ⟨hnf, hng⟩)
          exact Eq.subst (motive := fun s => s ∈ Y) hzy.symm hy0
    have hP : isPartFunc h X Y := partFunc_of hh
      (Eq.subst (motive := fun s => s ⊆ X) hdh.symm (fun _ hx => hx)) hrng
    have htf : isTotal h X := hdh
    have hfh : tolerates f h := by
      intro x hx
      have hxf := ((XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom h) x).mp hx).1
      have hxX : x ∈ X := RELSET_1.relationOf_defined hf.2 x hxf
      exact ((hv x hxX).1 hxf).symm
    have hgh : tolerates g h := by
      intro x hx
      have hxg := ((XBOOLE_0.def4 (RELAT_1.dom g) (RELAT_1.dom h) x).mp hx).1
      have hxX : x ∈ X := RELSET_1.relationOf_defined hg.2 x hxg
      exact ((hv x hxX).2.1 hxg).symm
    exact ⟨h, hP, htf, hfh, hgh⟩

/-- `PARTFUN1:def 5` — `TotFuncs f`. -/
noncomputable def TotFuncs {X Y f : TarskiSet.{u}}
    (_hf : isPartFunc f X Y) : TarskiSet.{u} :=
  Classical.choose
    (XBOOLE_0.sch_separation (PFuncs X Y)
      (fun x => isPartFunc x X Y ∧ isTotal x X ∧ tolerates f x))

theorem def5 {X Y f : TarskiSet.{u}} (hf : isPartFunc f X Y)
    (x : TarskiSet.{u}) :
    x ∈ TotFuncs hf ↔
      ∃ g, isPartFunc g X Y ∧ g = x ∧ isTotal g X ∧ tolerates f g := by
  have h := Classical.choose_spec
    (XBOOLE_0.sch_separation (PFuncs X Y)
      (fun z => isPartFunc z X Y ∧ isTotal z X ∧ tolerates f z))
  constructor
  · intro hx
    have ⟨_, hp, ht, htol⟩ := (h x).mp hx
    exact ⟨x, hp, rfl, ht, htol⟩
  · intro ⟨g, hp, heq, ht, htol⟩
    have hxP : x ∈ PFuncs X Y :=
      Eq.subst (motive := fun s => s ∈ PFuncs X Y) heq (th45 hp)
    have hp' : isPartFunc x X Y :=
      Eq.subst (motive := fun s => isPartFunc s X Y) heq hp
    have ht' : isTotal x X :=
      Eq.subst (motive := fun s => isTotal s X) heq ht
    have htol' : tolerates f x :=
      Eq.subst (motive := fun s => tolerates f s) heq htol
    exact (h x).mpr ⟨hxP, hp', ht', htol'⟩

/-- `PARTFUN1:69` (`Th69`) -/
theorem th69 {X Y f g : TarskiSet.{u}} (hf : isPartFunc f X Y)
    (hg : g ∈ TotFuncs hf) : isPartFunc g X Y := by
  obtain ⟨g9, hp, heq, _, _⟩ := (def5 hf g).mp hg
  exact Eq.subst (motive := fun s => isPartFunc s X Y) heq hp

/-- `PARTFUN1:70` (`Th70`) -/
theorem th70 {X Y f g : TarskiSet.{u}} (hf : isPartFunc f X Y)
    (_hg : isPartFunc g X Y) (hin : g ∈ TotFuncs hf) : isTotal g X := by
  obtain ⟨g9, _, heq, ht, _⟩ := (def5 hf g).mp hin
  exact Eq.subst (motive := fun s => isTotal s X) heq ht

/-- `PARTFUN1:71` (`Th71`) -/
theorem th71 {X Y f g : TarskiSet.{u}} (hf : isPartFunc f X Y)
    (_hg : FUNCT_1.isFunction g) (hin : g ∈ TotFuncs hf) :
    tolerates f g := by
  obtain ⟨g9, _, heq, _, htol⟩ := (def5 hf g).mp hin
  exact Eq.subst (motive := fun s => tolerates f s) heq htol

/-- `PARTFUN1:72` (`Th72`) -/
theorem th72 {X Y f : TarskiSet.{u}} (hf : isPartFunc f X Y) :
    isTotal f X ↔ TotFuncs hf = TARSKI.singleton f := by
  constructor
  · intro ht
    apply TARSKI.extensionality
    intro g
    constructor
    · intro hg
      obtain ⟨g9, hp, heq, ht9, htol⟩ := (def5 hf g).mp hg
      have heq2 : f = g9 := th66 hf hp ht ht9 htol
      exact (singleton_iff f g).mpr (heq2.trans heq).symm
    · intro hg
      have heq : g = f := (singleton_iff f g).mp hg
      exact (def5 hf g).mpr ⟨f, hf, heq.symm, ht, tolerates_refl f⟩
  · intro heq
    have hin : f ∈ TotFuncs hf :=
      Eq.subst (motive := fun s => f ∈ s) heq.symm
        ((singleton_iff f f).mpr rfl)
    exact th70 hf hf hin


/-- Unlabeled `PARTFUN1` (`L1485`). -/
theorem th73 {f Y : TarskiSet.{u}} (hf : isPartFunc f (∅ : TarskiSet.{u}) Y) :
    TotFuncs hf = TARSKI.singleton f :=
  (th72 hf).mp
    (XBOOLE_1.th3 (X := RELAT_1.dom f) (RELSET_1.relationOf_defined hf.2))

/-- Unlabeled `PARTFUN1` (`L1488`). -/
theorem th74 {f Y : TarskiSet.{u}} (hf : isPartFunc f (∅ : TarskiSet.{u}) Y) :
    TotFuncs hf = TARSKI.singleton (∅ : TarskiSet.{u}) := by
  have heq : f = (∅ : TarskiSet.{u}) :=
    RELAT_1.th41 hf.1.1
      (Or.inl (XBOOLE_1.th3 (X := RELAT_1.dom f)
        (RELSET_1.relationOf_defined hf.2)))
  exact Eq.subst (motive := fun s => TotFuncs hf = TARSKI.singleton s)
    heq (th73 hf)

/-- Unlabeled `PARTFUN1` (`L1491`). -/
theorem th75 {f g X Y : TarskiSet.{u}} (hf : isPartFunc f X Y)
    (hg : isPartFunc g X Y)
    (hmeet : XBOOLE_0.meets (TotFuncs hf) (TotFuncs hg)) :
    tolerates f g := by
  obtain ⟨h, hhI⟩ := XBOOLE_0.th7 hmeet
  have ⟨hhf, hhg⟩ :=
    (XBOOLE_0.def4 (TotFuncs hf) (TotFuncs hg) h).mp hhI
  have hp : isPartFunc h X Y := th69 hf hhf
  exact th67 hf hg hp (th71 hf hp.1 hhf) (th71 hg hp.1 hhg)
    (th70 hf hp hhf)

/-- Unlabeled `PARTFUN1` (`L1508`). -/
theorem th76 {f g X Y : TarskiSet.{u}} (hf : isPartFunc f X Y)
    (hg : isPartFunc g X Y)
    (hYX : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (ht : tolerates f g) :
    XBOOLE_0.meets (TotFuncs hf) (TotFuncs hg) := by
  obtain ⟨h, hp, htt, hfh, hgh⟩ := th68 hf hg hYX ht
  have hin1 : h ∈ TotFuncs hf :=
    (def5 hf h).mpr ⟨h, hp, rfl, htt, hfh⟩
  have hin2 : h ∈ TotFuncs hg :=
    (def5 hg h).mpr ⟨h, hp, rfl, htt, hgh⟩
  have hin : h ∈ TotFuncs hf ∩ TotFuncs hg :=
    (XBOOLE_0.def4 (TotFuncs hf) (TotFuncs hg) h).mpr ⟨hin1, hin2⟩
  intro heq
  exact (XBOOLE_0.empty_iff h).mp
    (Eq.subst (motive := fun s => h ∈ s) heq hin)

/-- `PARTFUN1:lm 2` -/
theorem lm2 {X R : TarskiSet.{u}} (heq : R = RELAT_1.id X) :
    isTotal R X :=
  Eq.subst (motive := fun s => RELAT_1.dom s = X) heq.symm
    (RELAT_1.th45 (X := X)).1

/-- `PARTFUN1:lm 3` -/
theorem lm3 {X R : TarskiSet.{u}} (heq : R = RELAT_1.id X) :
    RELAT_2.isReflexive R ∧ RELAT_2.isSymmetric R ∧
      RELAT_2.isAntisymmetric R ∧ RELAT_2.isTransitive R := by
  have hrefl : RELAT_2.isReflexive (RELAT_1.id X) := by
    intro x hx
    have o :=
      (XBOOLE_0.def3 (RELAT_1.dom (RELAT_1.id X))
        (RELAT_1.rng (RELAT_1.id X)) x).mp hx
    have hxX : x ∈ X :=
      Or.elim o
        (fun hd =>
          Eq.subst (motive := fun s => x ∈ s)
            (RELAT_1.th45 (X := X)).1 hd)
        (fun hr =>
          Eq.subst (motive := fun s => x ∈ s)
            (RELAT_1.th45 (X := X)).2 hr)
    exact (RELAT_1.def10 X x x).mpr ⟨hxX, rfl⟩
  exact ⟨
    Eq.subst (motive := RELAT_2.isReflexive) heq.symm hrefl,
    Eq.subst (motive := RELAT_2.isSymmetric) heq.symm
      (RELAT_2.id_isSymmetric X),
    Eq.subst (motive := RELAT_2.isAntisymmetric) heq.symm
      (RELAT_2.id_isAntisymmetric X),
    Eq.subst (motive := RELAT_2.isTransitive) heq.symm
      (RELAT_2.id_isTransitive X)⟩

/-- `PARTFUN1:lm 4` -/
theorem lm4 (X : TarskiSet.{u}) :
    RELSET_1.isRelationOf (RELAT_1.id X) X X :=
  RELSET_1.th4 (RELAT_1.id_isRelation X)
    (Eq.subst (motive := fun s => s ⊆ X)
      (RELAT_1.th45 (X := X)).1.symm (fun _ hx => hx))
    (Eq.subst (motive := fun s => s ⊆ X)
      (RELAT_1.th45 (X := X)).2.symm (fun _ hx => hx))

theorem id_isTotalRelation (X : TarskiSet.{u}) :
    isTotal (RELAT_1.id X) X ∧ RELSET_1.isRelationOf (RELAT_1.id X) X X :=
  ⟨lm2 rfl, lm4 X⟩

/-- `PARTFUN1:sch LambdaC9` -/
theorem sch_LambdaC9 (A : TarskiSet.{u}) (_hA : A ≠ (∅ : TarskiSet.{u}))
    (C : TarskiSet.{u} → Prop)
    (F G : TarskiSet.{u} → TarskiSet.{u}) :
    ∃ f, FUNCT_1.isFunction f ∧ RELAT_1.dom f = A ∧
      ∀ x, x ∈ A →
        (C x → FUNCT_1.apply f x = F x) ∧
          (¬ C x → FUNCT_1.apply f x = G x) :=
  sch_LambdaC A C F G

/-- `PARTFUN1:77` (`Th77`) -/
theorem th77 {f g x y z : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (ht : tolerates f g)
    (hpf : TARSKI.pair x y ∈ f) (hpg : TARSKI.pair x z ∈ g) : y = z := by
  obtain ⟨h, hh, heq⟩ := (th51 hf hg).mp ht
  have hp1 : TARSKI.pair x y ∈ h :=
    Eq.subst (motive := fun s => TARSKI.pair x y ∈ s) heq
      ((XBOOLE_0.def3 f g (TARSKI.pair x y)).mpr (Or.inl hpf))
  have hp2 : TARSKI.pair x z ∈ h :=
    Eq.subst (motive := fun s => TARSKI.pair x z ∈ s) heq
      ((XBOOLE_0.def3 f g (TARSKI.pair x z)).mpr (Or.inr hpg))
  exact hh.2 x y z hp1 hp2

/-- Unlabeled `PARTFUN1` (`L1643`). -/
theorem th78 {A : TarskiSet.{u}} (hfun : FUNCT_1.isFunctional A)
    (ht : ∀ f g, FUNCT_1.isFunction f → FUNCT_1.isFunction g →
      f ∈ A → g ∈ A → tolerates f g) :
    FUNCT_1.isFunction (TARSKI.union A) := by
  constructor
  · intro z hz
    obtain ⟨p, hzp, hpA⟩ := (TARSKI.def4 A z).mp hz
    exact (hfun p hpA).1 z hzp
  · intro x y z hp1 hp2
    obtain ⟨p, hpy, hpA⟩ := (TARSKI.def4 A (TARSKI.pair x y)).mp hp1
    obtain ⟨q, hqz, hqA⟩ := (TARSKI.def4 A (TARSKI.pair x z)).mp hp2
    have hf : FUNCT_1.isFunction p := hfun p hpA
    have hg : FUNCT_1.isFunction q := hfun q hqA
    exact th77 hf hg (ht p q hf hg hpA hqA) hpy hqz

/-- Mizar `p/.i`. -/
noncomputable def apply_at (p i : TarskiSet.{u}) : TarskiSet.{u} :=
  FUNCT_1.apply p i

/-- `PARTFUN1:def 6` -/
theorem def6 {D p i : TarskiSet.{u}} (_hp : FUNCT_1.isFunction p)
    (_hv : RELAT_1.isXvalued p D) (_hi : i ∈ RELAT_1.dom p) :
    apply_at p i = FUNCT_1.apply p i :=
  rfl

theorem nonempty_partFunc {X Y : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u})) :
    ∃ f, isPartFunc f X Y ∧ f ≠ (∅ : TarskiSet.{u}) := by
  obtain ⟨x, hx⟩ := XBOOLE_0.th7 hX
  obtain ⟨y, hy⟩ := XBOOLE_0.th7 hY
  refine ⟨TARSKI.singleton (TARSKI.pair x y),
    ⟨FUNCT_1.singleton_pair_isFunction x y, RELSET_1.th3 hx hy⟩, ?_⟩
  intro he
  exact (XBOOLE_0.empty_iff (TARSKI.pair x y)).mp
    (Eq.subst (motive := fun s => TARSKI.pair x y ∈ s) he
      ((singleton_iff (TARSKI.pair x y) (TARSKI.pair x y)).mpr rfl))

theorem PFuncs_isFunctional (X Y : TarskiSet.{u}) :
    FUNCT_1.isFunctional (PFuncs X Y) :=
  fun x hx =>
    let ⟨f, hf, heq, _, _⟩ := (def3 X Y x).mp hx
    Eq.subst (motive := FUNCT_1.isFunction) heq.symm hf

/-- Unlabeled `PARTFUN1` (`L1718`). -/
theorem th79 {f1 f2 g : TarskiSet.{u}} (h1 : FUNCT_1.isFunction f1)
    (h2 : FUNCT_1.isFunction f2) (hg : FUNCT_1.isFunction g)
    (hr1 : RELAT_1.rng g ⊆ RELAT_1.dom f1)
    (hr2 : RELAT_1.rng g ⊆ RELAT_1.dom f2) (ht : tolerates f1 f2) :
    RELAT_1.comp g f1 = RELAT_1.comp g f2 := by
  have hd1 : RELAT_1.dom (RELAT_1.comp g f1) = RELAT_1.dom g :=
    RELAT_1.th27 (R := g) (P := f1) hr1
  have hd2 : RELAT_1.dom (RELAT_1.comp g f2) = RELAT_1.dom g :=
    RELAT_1.th27 (R := g) (P := f2) hr2
  have hd : RELAT_1.dom (RELAT_1.comp g f1) =
      RELAT_1.dom (RELAT_1.comp g f2) :=
    hd1.trans hd2.symm
  refine FUNCT_1.th2 (FUNCT_1.comp_isFunction hg h1)
    (FUNCT_1.comp_isFunction hg h2) hd fun x hx => ?_
  have hxg : x ∈ RELAT_1.dom g :=
    Eq.subst (motive := fun s => x ∈ s) hd1 hx
  have hval1 : FUNCT_1.apply (RELAT_1.comp g f1) x =
      FUNCT_1.apply f1 (FUNCT_1.apply g x) :=
    FUNCT_1.th12 hg.2 h1.2 hx
  have hx2 : x ∈ RELAT_1.dom (RELAT_1.comp g f2) :=
    Eq.subst (motive := fun s => x ∈ s) hd2.symm hxg
  have hval2 : FUNCT_1.apply (RELAT_1.comp g f2) x =
      FUNCT_1.apply f2 (FUNCT_1.apply g x) :=
    FUNCT_1.th12 hg.2 h2.2 hx2
  have hgxR : FUNCT_1.apply g x ∈ RELAT_1.rng g :=
    FUNCT_1.th3 hg.2 hxg
  have hxI : FUNCT_1.apply g x ∈ RELAT_1.dom f1 ∩ RELAT_1.dom f2 :=
    (XBOOLE_0.def4 (RELAT_1.dom f1) (RELAT_1.dom f2)
      (FUNCT_1.apply g x)).mpr ⟨hr1 _ hgxR, hr2 _ hgxR⟩
  exact hval1.trans ((ht (FUNCT_1.apply g x) hxI).trans hval2.symm)

/-- Unlabeled `PARTFUN1` (`L1746`). -/
theorem th80 {f X Y x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (_hv : RELAT_1.isXvalued f Y)
    (hx : x ∈ RELAT_1.dom (RELAT_1.restrict f X)) :
    apply_at (RELAT_1.restrict f X) x = apply_at f x :=
  FUNCT_1.th47 hf.2 hx

end PARTFUN1
