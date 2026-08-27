import MizarCCL.PARTFUN1
import MizarCCL.MCART_1
import MizarCCL.SETFAM_1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/funct_2.miz`.
Authors: Czesław Byliński (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Functions from a Set to a Set

1–1 Lean rendering of Mizar article `FUNCT_2`
(`vendor/mml/funct_2.miz`). Import is `PARTFUN1`, `MCART_1`, and
`SETFAM_1`. `Th37` is canceled; Def7/Def8 are absent in the source.
-/

universe u

open TarskiSet TARSKI

namespace FUNCT_2

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

/-! ## Quasi-total (`FUNCT_2:def 1`) -/

/-- `FUNCT_2:def 1` — `R is quasi_total` (as Relation of `X`,`Y`). -/
def isQuasiTotal (R X Y : TarskiSet.{u}) : Prop :=
  (Y ≠ (∅ : TarskiSet.{u}) → RELAT_1.dom R = X) ∧
  (Y = (∅ : TarskiSet.{u}) → R = (∅ : TarskiSet.{u}))

theorem def1 (R X Y : TarskiSet.{u}) :
    isQuasiTotal R X Y ↔
      (Y ≠ (∅ : TarskiSet.{u}) → RELAT_1.dom R = X) ∧
      (Y = (∅ : TarskiSet.{u}) → R = (∅ : TarskiSet.{u})) :=
  Iff.rfl

/-- Mode `Function of X,Y`: quasi-total PartFunc of `X`,`Y`. -/
def isFunctionOf (f X Y : TarskiSet.{u}) : Prop :=
  PARTFUN1.isPartFunc f X Y ∧ isQuasiTotal f X Y

theorem functionOf_isFunction {f X Y : TarskiSet.{u}}
    (hf : isFunctionOf f X Y) : FUNCT_1.isFunction f :=
  hf.1.1

theorem functionOf_isRelationOf {f X Y : TarskiSet.{u}}
    (hf : isFunctionOf f X Y) : RELSET_1.isRelationOf f X Y :=
  hf.1.2

theorem functionOf_rng_sub {f X Y : TarskiSet.{u}}
    (hf : isFunctionOf f X Y) : RELAT_1.rng f ⊆ Y :=
  RELSET_1.relationOf_valued hf.1.2

theorem functionOf_dom_sub {f X Y : TarskiSet.{u}}
    (hf : isFunctionOf f X Y) : RELAT_1.dom f ⊆ X :=
  RELSET_1.relationOf_defined hf.1.2

theorem functionOf_dom_eq {f X Y : TarskiSet.{u}}
    (hf : isFunctionOf f X Y) (hY : Y ≠ (∅ : TarskiSet.{u})) :
    RELAT_1.dom f = X :=
  hf.2.1 hY

theorem functionOf_empty_cod {f X Y : TarskiSet.{u}}
    (hf : isFunctionOf f X Y) (hY : Y = (∅ : TarskiSet.{u})) :
    f = (∅ : TarskiSet.{u}) :=
  hf.2.2 hY

theorem relationOf_empty_cod {f X Y : TarskiSet.{u}}
    (hf : RELSET_1.isRelationOf f X Y) (hY : Y = (∅ : TarskiSet.{u})) :
    f = (∅ : TarskiSet.{u}) := by
  have hprod : ZFMISC_1.product X Y = (∅ : TarskiSet.{u}) :=
    (ZFMISC_1.th90 (X := X) (Y := Y)).mpr (Or.inr hY)
  exact (XBOOLE_0.def10 (X := f) (Y := (∅ : TarskiSet.{u}))).mpr
    ⟨Eq.subst (motive := fun s => f ⊆ s) hprod hf, XBOOLE_1.th2⟩

theorem empty_isQuasiTotal (X Y : TarskiSet.{u})
    (hY : Y = (∅ : TarskiSet.{u})) :
    isQuasiTotal (∅ : TarskiSet.{u}) X Y :=
  ⟨fun hne => (hne hY).elim, fun _ => rfl⟩

theorem empty_isFunctionOf (X : TarskiSet.{u}) :
    isFunctionOf (∅ : TarskiSet.{u}) X (∅ : TarskiSet.{u}) :=
  ⟨PARTFUN1.empty_isPartFunc X ∅, empty_isQuasiTotal X ∅ rfl⟩

/-- Build `Function of X,Y` from a function with `dom = X` and `rng ⊆ Y`. -/
theorem functionOf_of {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hd : RELAT_1.dom f = X) (hr : RELAT_1.rng f ⊆ Y) :
    isFunctionOf f X Y := by
  refine ⟨PARTFUN1.partFunc_of hf (hd ▸ fun _ h => h) hr, ?_⟩
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · have hrng : RELAT_1.rng f = (∅ : TarskiSet.{u}) :=
      (XBOOLE_0.def10 (X := RELAT_1.rng f) (Y := (∅ : TarskiSet.{u}))).mpr
        ⟨Eq.subst (motive := fun s => RELAT_1.rng f ⊆ s) hY hr,
          XBOOLE_1.th2⟩
    have hempty : f = (∅ : TarskiSet.{u}) :=
      RELAT_1.th41 hf.1 (Or.inr hrng)
    exact ⟨fun hne => (hne hY).elim, fun _ => hempty⟩
  · exact ⟨fun _ => hd, fun hempty => (hY hempty).elim⟩

/-- Registration: existence of a quasi-total PartFunc of `X`,`Y`. -/
theorem exists_quasiTotal_partFunc (X Y : TarskiSet.{u}) :
    ∃ R, PARTFUN1.isPartFunc R X Y ∧ isQuasiTotal R X Y := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact ⟨∅, PARTFUN1.empty_isPartFunc X Y, empty_isQuasiTotal X Y hY⟩
  · obtain ⟨f, hf, hdom, hr⟩ := FUNCT_1.th8 (Or.inl hY) (X := X) (Y := Y)
    exact ⟨f, (functionOf_of hf hdom.symm hr).1, (functionOf_of hf hdom.symm hr).2⟩

/-- Registration: total → quasi_total for Relation of `X`,`Y`. -/
theorem total_isQuasiTotal {f X Y : TarskiSet.{u}}
    (hf : RELSET_1.isRelationOf f X Y) (hd : RELAT_1.dom f = X) :
    isQuasiTotal f X Y := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact ⟨fun hne => (hne hY).elim, fun _ => relationOf_empty_cod hf hY⟩
  · exact ⟨fun _ => hd, fun hempty => (hY hempty).elim⟩

/-- Registration: empty domain → total for quasi_total Relation of `X`,`Y`. -/
theorem quasiTotal_total_of_empty_dom {f X Y : TarskiSet.{u}}
    (hX : X = (∅ : TarskiSet.{u})) (hf : isQuasiTotal f X Y) :
    RELAT_1.dom f = X := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · have hempty : f = (∅ : TarskiSet.{u}) := hf.2 hY
    exact Eq.subst (motive := fun s => RELAT_1.dom s = X) hempty.symm
      (RELAT_1.th38.1.trans hX.symm)
  · exact hf.1 hY

/-- Registration: non-empty codomain → total for quasi_total. -/
theorem quasiTotal_total_of_ne_cod {f X Y : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hf : isQuasiTotal f X Y) :
    RELAT_1.dom f = X :=
  hf.1 hY

/-- Registration: quasi_total → total for Relation of `X`,`X`. -/
theorem quasiTotal_total_diag {f X : TarskiSet.{u}}
    (hf : isQuasiTotal f X X) : RELAT_1.dom f = X := by
  have := Classical.propDecidable (X = (∅ : TarskiSet.{u}))
  by_cases hX : X = (∅ : TarskiSet.{u})
  · exact quasiTotal_total_of_empty_dom hX hf
  · exact hf.1 hX

/-- When `Y = {} → X = {}`, a Function of `X`,`Y` has `dom = X`. -/
theorem functionOf_dom_eq' {f X Y : TarskiSet.{u}}
    (hf : isFunctionOf f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    RELAT_1.dom f = X := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · have hempty : f = (∅ : TarskiSet.{u}) := functionOf_empty_cod hf hY
    exact Eq.subst (motive := fun s => RELAT_1.dom s = X) hempty.symm
      (RELAT_1.th38.1.trans (h hY).symm)
  · exact functionOf_dom_eq hf hY

/-! ## Early theorems -/

/-- Unlabeled `FUNCT_2` (`L119`) — `f` is Function of `dom f`, `rng f`. -/
theorem th1 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    isFunctionOf f (RELAT_1.dom f) (RELAT_1.rng f) :=
  functionOf_of hf rfl (fun _ h => h)

/-- `FUNCT_2:2` (`Th2`) -/
theorem th2 {f Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hr : RELAT_1.rng f ⊆ Y) :
    isFunctionOf f (RELAT_1.dom f) Y :=
  functionOf_of hf rfl hr

/-- Unlabeled `FUNCT_2` (`L139`) -/
theorem th3 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hd : RELAT_1.dom f = X)
    (hv : ∀ x, x ∈ X → FUNCT_1.apply f x ∈ Y) :
    isFunctionOf f X Y := by
  have hr : RELAT_1.rng f ⊆ Y := by
    intro y hy
    obtain ⟨x, hx, heq⟩ := (FUNCT_1.def3 hf.2).mp hy
    exact Eq.subst (motive := fun s => s ∈ Y) heq.symm
      (hv x (Eq.subst (motive := fun s => x ∈ s) hd hx))
  exact functionOf_of hf hd hr

/-- `FUNCT_2:4` (`Th4`) -/
theorem th4 {f X Y x : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hx : x ∈ X) :
    FUNCT_1.apply f x ∈ RELAT_1.rng f :=
  FUNCT_1.th3 (functionOf_isFunction hf).2
    (Eq.subst (motive := fun s => x ∈ s) (functionOf_dom_eq hf hY).symm hx)

/-- `FUNCT_2:5` (`Th5`) -/
theorem th5 {f X Y x : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hx : x ∈ X) :
    FUNCT_1.apply f x ∈ Y :=
  functionOf_rng_sub hf _ (th4 hf hY hx)

/-- Unlabeled `FUNCT_2` (`L177`) -/
theorem th6 {f X Y Z : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (hr : RELAT_1.rng f ⊆ Z) :
    isFunctionOf f X Z := by
  have hd : RELAT_1.dom f = X := functionOf_dom_eq' hf h
  have hZempty : Z = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}) := by
    intro hZ
    have hrng : RELAT_1.rng f = (∅ : TarskiSet.{u}) :=
      (XBOOLE_0.def10 (X := RELAT_1.rng f) (Y := (∅ : TarskiSet.{u}))).mpr
        ⟨Eq.subst (motive := fun s => RELAT_1.rng f ⊆ s) hZ hr, XBOOLE_1.th2⟩
    have : RELAT_1.dom f = (∅ : TarskiSet.{u}) :=
      (RELAT_1.th42 (functionOf_isFunction hf).1).mpr hrng
    exact hd.symm.trans this
  exact functionOf_of (functionOf_isFunction hf) hd hr

/-- Unlabeled `FUNCT_2` (`L195`) -/
theorem th7 {f X Y Z : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (hYZ : Y ⊆ Z) :
    isFunctionOf f X Z :=
  th6 hf h (XBOOLE_1.th1 (functionOf_rng_sub hf) hYZ)

/-! ## Schemes `FuncEx1`, `Lambda1` -/

/-- `FUNCT_2:sch FuncEx1` — uses `FUNCT_1:sch NonUniqBoundFuncEx`. -/
theorem sch_FuncEx1 (X Y : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hP : ∀ x, x ∈ X → ∃ y, y ∈ Y ∧ P x y) :
    ∃ f, isFunctionOf f X Y ∧ ∀ x, x ∈ X → P x (FUNCT_1.apply f x) := by
  obtain ⟨f, hf, hd, hr, hv⟩ := FUNCT_1.sch_NonUniqBoundFuncEx X Y P hP
  exact ⟨f, functionOf_of hf hd hr, hv⟩

/-- `FUNCT_2:sch Lambda1` -/
theorem sch_Lambda1 (X Y : TarskiSet.{u})
    (F : TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ x, x ∈ X → F x ∈ Y) :
    ∃ f, isFunctionOf f X Y ∧
      ∀ x, x ∈ X → FUNCT_1.apply f x = F x :=
  sch_FuncEx1 X Y (fun x y => y = F x)
    (fun x hx => ⟨F x, hF x hx, rfl⟩)

/-! ## `Funcs(X,Y)` (`FUNCT_2:def 2`) -/

/-- `FUNCT_2:def 2` — set of functions from `X` into `Y`. -/
noncomputable def Funcs (X Y : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (XBOOLE_0.sch_separation (ZFMISC_1.bool (ZFMISC_1.product X Y))
      (fun z => FUNCT_1.isFunction z ∧ RELAT_1.dom z = X ∧
        RELAT_1.rng z ⊆ Y))

theorem def2 (X Y z : TarskiSet.{u}) :
    z ∈ Funcs X Y ↔
      ∃ f, FUNCT_1.isFunction f ∧ z = f ∧ RELAT_1.dom f = X ∧
        RELAT_1.rng f ⊆ Y := by
  have h := Classical.choose_spec
    (XBOOLE_0.sch_separation (ZFMISC_1.bool (ZFMISC_1.product X Y))
      (fun z => FUNCT_1.isFunction z ∧ RELAT_1.dom z = X ∧
        RELAT_1.rng z ⊆ Y))
  constructor
  · intro hz
    have ⟨_, hf, hd, hr⟩ := (h z).mp hz
    exact ⟨z, hf, rfl, hd, hr⟩
  · intro ⟨f, hf, heq, hd, hr⟩
    have hf' : FUNCT_1.isFunction z :=
      Eq.subst (motive := FUNCT_1.isFunction) heq.symm hf
    have hd' : RELAT_1.dom z = X :=
      Eq.subst (motive := fun s => RELAT_1.dom s = X) heq.symm hd
    have hr' : RELAT_1.rng z ⊆ Y :=
      Eq.subst (motive := fun s => RELAT_1.rng s ⊆ Y) heq.symm hr
    have hsub : z ⊆ ZFMISC_1.product X Y :=
      RELSET_1.th4 hf'.1 (hd' ▸ fun _ hx => hx) hr'
    have hbool : z ∈ ZFMISC_1.bool (ZFMISC_1.product X Y) :=
      (ZFMISC_1.def1 (ZFMISC_1.product X Y) z).mpr hsub
    exact (h z).mpr ⟨hbool, hf', hd', hr'⟩

/-- `FUNCT_2:8` (`Th8`) -/
theorem th8 {f X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    f ∈ Funcs X Y :=
  (def2 X Y f).mpr
    ⟨f, functionOf_isFunction hf, rfl, functionOf_dom_eq' hf h,
      functionOf_rng_sub hf⟩

/-- Unlabeled `FUNCT_2` (`L282`) -/
theorem th9 {f X : TarskiSet.{u}} (hf : isFunctionOf f X X) :
    f ∈ Funcs X X :=
  th8 hf (fun h => h)

/-- Registration: `Funcs(X,Y)` non-empty when `Y` non-empty. -/
theorem Funcs_nonempty_of_ne_cod (X Y : TarskiSet.{u})
    (hY : Y ≠ (∅ : TarskiSet.{u})) :
    Funcs X Y ≠ (∅ : TarskiSet.{u}) := by
  obtain ⟨f, hf, hdom, hr⟩ := FUNCT_1.th8 (Or.inl hY) (X := X) (Y := Y)
  have hf' := functionOf_of hf hdom.symm hr
  exact fun hempty =>
    (XBOOLE_0.empty_iff f).mp (hempty ▸ th8 hf' (fun h => (hY h).elim))

/-- Registration: `Funcs(X,X)` non-empty. -/
theorem Funcs_diag_nonempty (X : TarskiSet.{u}) :
    Funcs X X ≠ (∅ : TarskiSet.{u}) := by
  have := Classical.propDecidable (X = (∅ : TarskiSet.{u}))
  by_cases hX : X = (∅ : TarskiSet.{u})
  · have hf : isFunctionOf (∅ : TarskiSet.{u}) X X :=
      Eq.subst (motive := fun s => isFunctionOf (∅ : TarskiSet.{u}) s s)
        hX.symm (empty_isFunctionOf (∅ : TarskiSet.{u}))
    have hmem : (∅ : TarskiSet.{u}) ∈ Funcs X X := th9 hf
    exact fun hempty =>
      (XBOOLE_0.empty_iff (∅ : TarskiSet.{u})).mp
        (Eq.subst (motive := fun s => (∅ : TarskiSet.{u}) ∈ s) hempty hmem)
  · exact Funcs_nonempty_of_ne_cod X X hX

/-- Registration: `Funcs(X,∅)` empty when `X` non-empty. -/
theorem Funcs_empty_cod_empty (X Y : TarskiSet.{u})
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y = (∅ : TarskiSet.{u})) :
    Funcs X Y = (∅ : TarskiSet.{u}) := by
  apply (XBOOLE_0.def10 (X := Funcs X Y) (Y := (∅ : TarskiSet.{u}))).mpr
  constructor
  · intro f hf
    obtain ⟨F, hF, heq, hd, hr⟩ := (def2 X Y f).mp hf
    have hrng : RELAT_1.rng F = (∅ : TarskiSet.{u}) :=
      (XBOOLE_0.def10 (X := RELAT_1.rng F) (Y := (∅ : TarskiSet.{u}))).mpr
        ⟨Eq.subst (motive := fun s => RELAT_1.rng F ⊆ s) hY hr, XBOOLE_1.th2⟩
    have hdomEmpty : RELAT_1.dom F = (∅ : TarskiSet.{u}) :=
      (RELAT_1.th42 hF.1).mpr hrng
    exact (hX (hd.symm.trans hdomEmpty)).elim
  · exact XBOOLE_1.th2

/-- Unlabeled `FUNCT_2` (`L312`) — surjectivity criterion. -/
theorem th10 {f X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (h : ∀ y, y ∈ Y → ∃ x, x ∈ X ∧ y = FUNCT_1.apply f x) :
    RELAT_1.rng f = Y := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact Eq.trans
      ((XBOOLE_0.def10 (X := RELAT_1.rng f) (Y := (∅ : TarskiSet.{u}))).mpr
        ⟨Eq.subst (motive := fun s => RELAT_1.rng f ⊆ s) hY
          (functionOf_rng_sub hf), XBOOLE_1.th2⟩)
      hY.symm
  · have hd : RELAT_1.dom f = X := functionOf_dom_eq hf hY
    apply eq_of_mem
    intro y
    constructor
    · intro hy
      exact functionOf_rng_sub hf y hy
    · intro hy
      obtain ⟨x, hx, heq⟩ := h y hy
      exact (FUNCT_1.def3 (functionOf_isFunction hf).2).mpr
        ⟨x, Eq.subst (motive := fun s => x ∈ s) hd.symm hx, heq⟩

/-- `FUNCT_2:11` (`Th11`) -/
theorem th11 {f X Y y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hy : y ∈ RELAT_1.rng f) :
    ∃ x, x ∈ X ∧ FUNCT_1.apply f x = y := by
  have hYne : Y ≠ (∅ : TarskiSet.{u}) := by
    intro hY
    have hempty : f = (∅ : TarskiSet.{u}) := functionOf_empty_cod hf hY
    have hrng : RELAT_1.rng f = (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => RELAT_1.rng s = (∅ : TarskiSet.{u}))
        hempty.symm RELAT_1.th38.2
    exact (XBOOLE_0.empty_iff y).mp (hrng ▸ hy)
  have hd : RELAT_1.dom f = X := functionOf_dom_eq hf hYne
  obtain ⟨x, hx, heq⟩ := (FUNCT_1.def3 (functionOf_isFunction hf).2).mp hy
  exact ⟨x, Eq.subst (motive := fun s => x ∈ s) hd hx, heq.symm⟩

/-- `FUNCT_2:12` (`Th12`) — uniqueness of Function of `X`,`Y` by values. -/
theorem th12 {f1 f2 X Y : TarskiSet.{u}} (h1 : isFunctionOf f1 X Y)
    (h2 : isFunctionOf f2 X Y)
    (hv : ∀ x, x ∈ X → FUNCT_1.apply f1 x = FUNCT_1.apply f2 x) :
    f1 = f2 := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact (functionOf_empty_cod h1 hY).trans
      (functionOf_empty_cod h2 hY).symm
  · have hd1 : RELAT_1.dom f1 = X := functionOf_dom_eq h1 hY
    have hd2 : RELAT_1.dom f2 = X := functionOf_dom_eq h2 hY
    exact FUNCT_1.th2 (functionOf_isFunction h1) (functionOf_isFunction h2)
      (hd1.trans hd2.symm) fun x hx =>
        hv x (Eq.subst (motive := fun s => x ∈ s) hd1 hx)

/-- `FUNCT_2:13` (`Th13`) — composition of quasi-total relations.
Mizar `f*g` is `RELAT_1.comp f g`. -/
theorem th13 {f g X Y Z : TarskiSet.{u}}
    (hf : RELSET_1.isRelationOf f X Y) (hqf : isQuasiTotal f X Y)
    (hg : RELSET_1.isRelationOf g Y Z) (hqg : isQuasiTotal g Y Z)
    (h : Y = (∅ : TarskiSet.{u}) →
      Z = (∅ : TarskiSet.{u}) ∨ X = (∅ : TarskiSet.{u})) :
    isQuasiTotal (RELAT_1.comp f g) X Z := by
  have := Classical.propDecidable (Z = (∅ : TarskiSet.{u}))
  by_cases hZ : Z = (∅ : TarskiSet.{u})
  · exact ⟨fun hne => (hne hZ).elim,
      fun _ => relationOf_empty_cod
        (RELSET_1.comp_isRelationOf hf hg) hZ⟩
  · have hdG : RELAT_1.dom g = Y := hqg.1 hZ
    have hdF : RELAT_1.dom f = X := by
      have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
      by_cases hY : Y = (∅ : TarskiSet.{u})
      · have hX : X = (∅ : TarskiSet.{u}) :=
          (h hY).elim (fun hZe => (hZ hZe).elim) (fun hX => hX)
        have hempty : f = (∅ : TarskiSet.{u}) := hqf.2 hY
        exact Eq.subst (motive := fun s => RELAT_1.dom s = X) hempty.symm
          (RELAT_1.th38.1.trans hX.symm)
      · exact hqf.1 hY
    have hrF : RELAT_1.rng f ⊆ Y := RELSET_1.relationOf_valued hf
    have hsub : RELAT_1.rng f ⊆ RELAT_1.dom g :=
      Eq.subst (motive := fun s => RELAT_1.rng f ⊆ s) hdG.symm hrF
    exact ⟨fun _ => (RELAT_1.th27 hsub).trans hdF,
      fun hempty => (hZ hempty).elim⟩

/-- Unlabeled `FUNCT_2` (`L378`) — Mizar `rng(g*f)`. -/
theorem th14 {f g X Y Z : TarskiSet.{u}} (_hf : isFunctionOf f X Y)
    (hg : isFunctionOf g Y Z) (hZ : Z ≠ (∅ : TarskiSet.{u}))
    (hrf : RELAT_1.rng f = Y) (hrg : RELAT_1.rng g = Z) :
    RELAT_1.rng (RELAT_1.comp f g) = Z := by
  have hdG : RELAT_1.dom g = Y := functionOf_dom_eq hg hZ
  have hsub : RELAT_1.dom g ⊆ RELAT_1.rng f :=
    Eq.subst (motive := fun s => RELAT_1.dom g ⊆ s) hrf.symm
      (Eq.subst (motive := fun s => s ⊆ Y) hdG.symm (fun _ h => h))
  exact (RELAT_1.th28 hsub).trans hrg

/-- `FUNCT_2:15` (`Th15`) — Mizar `(g*f).x = g.(f.x)`. -/
theorem th15 {f g X Y x : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hg : FUNCT_1.isFunction g) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ X) :
    FUNCT_1.apply (RELAT_1.comp f g) x =
      FUNCT_1.apply g (FUNCT_1.apply f x) :=
  FUNCT_1.th13 (functionOf_isFunction hf).2 hg.2
    (Eq.subst (motive := fun s => x ∈ s) (functionOf_dom_eq hf hY).symm hx)

/-- Unlabeled `FUNCT_2` (`L399`) — cancellation characterization of onto. -/
theorem th16 {f X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hY : Y ≠ (∅ : TarskiSet.{u})) :
    RELAT_1.rng f = Y ↔
      ∀ Z, Z ≠ (∅ : TarskiSet.{u}) →
        ∀ g h, isFunctionOf g Y Z → isFunctionOf h Y Z →
          RELAT_1.comp f g = RELAT_1.comp f h → g = h := by
  constructor
  · intro hrng Z hZ g h hg hh hcomp
    exact FUNCT_1.th86 (functionOf_isFunction hf) (functionOf_isFunction hg)
      (functionOf_isFunction hh) hrng.symm (functionOf_dom_eq hg hZ)
      (functionOf_dom_eq hh hZ) hcomp
  · intro hcan
    have hcan' : ∀ g h, FUNCT_1.isFunction g → FUNCT_1.isFunction h →
        RELAT_1.dom g = Y → RELAT_1.dom h = Y →
        RELAT_1.comp f g = RELAT_1.comp f h → g = h := by
      intro g h hg hh hdg hdh hcomp
      have hrgNe : RELAT_1.rng g ≠ (∅ : TarskiSet.{u}) := by
        intro hempty
        have : RELAT_1.dom g = (∅ : TarskiSet.{u}) :=
          (RELAT_1.th42 hg.1).mpr hempty
        exact hY (hdg.symm.trans this)
      have hsubG : RELAT_1.rng g ⊆ RELAT_1.rng g ∪ RELAT_1.rng h :=
        XBOOLE_1.th7
      have hsubH : RELAT_1.rng h ⊆ RELAT_1.rng g ∪ RELAT_1.rng h :=
        Eq.subst (motive := fun s => RELAT_1.rng h ⊆ s)
          (XBOOLE_0.union_comm (RELAT_1.rng h) (RELAT_1.rng g))
          (XBOOLE_1.th7 (X := RELAT_1.rng h) (Y := RELAT_1.rng g))
      have hg'' : isFunctionOf g Y (RELAT_1.rng g ∪ RELAT_1.rng h) :=
        functionOf_of hg hdg hsubG
      have hh'' : isFunctionOf h Y (RELAT_1.rng g ∪ RELAT_1.rng h) :=
        functionOf_of hh hdh hsubH
      have hUnionNe : RELAT_1.rng g ∪ RELAT_1.rng h ≠ (∅ : TarskiSet.{u}) :=
        fun hempty => hrgNe
          ((XBOOLE_0.def10 (X := RELAT_1.rng g)
            (Y := (∅ : TarskiSet.{u}))).mpr
            ⟨fun z hz =>
              Eq.subst (motive := fun s => z ∈ s) hempty
                ((XBOOLE_0.def3 (RELAT_1.rng g) (RELAT_1.rng h) z).mpr
                  (Or.inl hz)),
              XBOOLE_1.th2⟩)
      exact hcan (RELAT_1.rng g ∪ RELAT_1.rng h) hUnionNe g h hg'' hh'' hcomp
    exact (FUNCT_1.th16 (functionOf_isFunction hf)
      (functionOf_rng_sub hf) hcan').symm

/-- Unlabeled `FUNCT_2` (`L433`) — left/right identity. -/
theorem th17 {f X Y : TarskiSet.{u}} (hf : RELSET_1.isRelationOf f X Y) :
    RELAT_1.comp (RELAT_1.id X) f = f ∧
      RELAT_1.comp f (RELAT_1.id Y) = f :=
  ⟨RELAT_1.th51 (RELSET_1.relationOf_isRelation hf)
      (RELSET_1.relationOf_defined hf),
    RELAT_1.th53 (RELSET_1.relationOf_isRelation hf)
      (RELSET_1.relationOf_valued hf)⟩

/-- Unlabeled `FUNCT_2` (`L443`) — left inverse implies onto.
Mizar `f*g` (FUNCT) is `RELAT_1.comp g f`. -/
theorem th18 {f g X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (_hg : isFunctionOf g Y X)
    (h : RELAT_1.comp g f = RELAT_1.id Y) :
    RELAT_1.rng f = Y := by
  have hrng : RELAT_1.rng (RELAT_1.comp g f) = Y :=
    Eq.subst (motive := fun s => RELAT_1.rng s = Y) h.symm RELAT_1.th45.2
  have hsub : Y ⊆ RELAT_1.rng f :=
    Eq.subst (motive := fun s => s ⊆ RELAT_1.rng f) hrng
      (RELAT_1.th26 (P := g) (R := f))
  exact (XBOOLE_0.def10 (X := RELAT_1.rng f) (Y := Y)).mpr
    ⟨functionOf_rng_sub hf, hsub⟩

/-- Unlabeled `FUNCT_2` (`L454`) — one-to-one via values on `X`. -/
theorem th19 {f X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    FUNCT_1.isOneToOne f ↔
      ∀ x1 x2, x1 ∈ X → x2 ∈ X →
        FUNCT_1.apply f x1 = FUNCT_1.apply f x2 → x1 = x2 := by
  have hd : RELAT_1.dom f = X := functionOf_dom_eq' hf h
  constructor
  · intro h1 x1 x2 hx1 hx2 heq
    exact h1 x1 x2 (Eq.subst (motive := fun s => x1 ∈ s) hd.symm hx1)
      (Eq.subst (motive := fun s => x2 ∈ s) hd.symm hx2) heq
  · intro hvals x1 x2 hx1 hx2 heq
    exact hvals x1 x2 (Eq.subst (motive := fun s => x1 ∈ s) hd hx1)
      (Eq.subst (motive := fun s => x2 ∈ s) hd hx2) heq

/-- Unlabeled `FUNCT_2` (`L464`) — injectivity of first factor.
Mizar `g*f` is `RELAT_1.comp f g`. -/
theorem th20 {f g X Y Z : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hg : isFunctionOf g Y Z)
    (h : Z = (∅ : TarskiSet.{u}) → Y = (∅ : TarskiSet.{u}))
    (h1 : FUNCT_1.isOneToOne (RELAT_1.comp f g)) :
    FUNCT_1.isOneToOne f := by
  have hdG : RELAT_1.dom g = Y := functionOf_dom_eq' hg h
  have hr : RELAT_1.rng f ⊆ RELAT_1.dom g :=
    Eq.subst (motive := fun s => RELAT_1.rng f ⊆ s) hdG.symm
      (functionOf_rng_sub hf)
  exact FUNCT_1.th25 (functionOf_isFunction hf).2
    (functionOf_isFunction hg).2 h1 hr

/-- Unlabeled `FUNCT_2` (`L477`) — one-to-one via right cancellation.
Mizar `f*g` is `RELAT_1.comp g f`. -/
theorem th21 {f X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.isOneToOne f ↔
      ∀ Z g h, isFunctionOf g Z X → isFunctionOf h Z X →
        RELAT_1.comp g f = RELAT_1.comp h f → g = h := by
  have hd : RELAT_1.dom f = X := functionOf_dom_eq hf hY
  constructor
  · intro h1 Z g h hg hh hcomp
    have hdg : RELAT_1.dom g = Z := functionOf_dom_eq hg hX
    have hdh : RELAT_1.dom h = Z := functionOf_dom_eq hh hX
    exact ((FUNCT_1.th27 (functionOf_isFunction hf)).mp h1)
      g h (functionOf_isFunction hg) (functionOf_isFunction hh)
      (Eq.subst (motive := fun s => RELAT_1.rng g ⊆ s) hd.symm
        (functionOf_rng_sub hg))
      (Eq.subst (motive := fun s => RELAT_1.rng h ⊆ s) hd.symm
        (functionOf_rng_sub hh))
      (hdg.trans hdh.symm) hcomp
  · intro hcan
    exact (FUNCT_1.th27 (functionOf_isFunction hf)).mpr fun g h hg hh hrg hrh hdom
        hcomp => by
      have hg' : isFunctionOf g (RELAT_1.dom g) X :=
        th2 hg (Eq.subst (motive := fun s => RELAT_1.rng g ⊆ s) hd hrg)
      have hh' : isFunctionOf h (RELAT_1.dom g) X :=
        Eq.subst (motive := fun s => isFunctionOf h s X) hdom.symm
          (th2 hh (Eq.subst (motive := fun s => RELAT_1.rng h ⊆ s) hd hrh))
      exact hcan (RELAT_1.dom g) g h hg' hh' hcomp

/-- Unlabeled `FUNCT_2` (`L508`) — Mizar `rng(g*f)`. -/
theorem th22 {f g X Y Z : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hg : isFunctionOf g Y Z) (hZ : Z ≠ (∅ : TarskiSet.{u}))
    (hrng : RELAT_1.rng (RELAT_1.comp f g) = Z)
    (h1 : FUNCT_1.isOneToOne g) :
    RELAT_1.rng f = Y := by
  have hdG : RELAT_1.dom g = Y := functionOf_dom_eq hg hZ
  have hsub : RELAT_1.rng (RELAT_1.comp f g) ⊆ RELAT_1.rng g :=
    RELAT_1.th26 (P := f) (R := g)
  have hrG : RELAT_1.rng g = Z :=
    (XBOOLE_0.def10 (X := RELAT_1.rng g) (Y := Z)).mpr
      ⟨functionOf_rng_sub hg,
        Eq.subst (motive := fun s => s ⊆ RELAT_1.rng g) hrng hsub⟩
  have hrG' : RELAT_1.rng (RELAT_1.comp f g) = RELAT_1.rng g :=
    hrng.trans hrG.symm
  have hYsub : Y ⊆ RELAT_1.rng f :=
    Eq.subst (motive := fun s => s ⊆ RELAT_1.rng f) hdG
      (FUNCT_1.th29 (functionOf_isFunction hf).2
        (functionOf_isFunction hg).2 hrG' h1)
  exact (XBOOLE_0.def10 (X := RELAT_1.rng f) (Y := Y)).mpr
    ⟨functionOf_rng_sub hf, hYsub⟩

/-! ## Onto / bijective (`FUNCT_2:def 3`) -/

/-- `FUNCT_2:def 3` -/
def isOnto (f Y : TarskiSet.{u}) : Prop := RELAT_1.rng f = Y

theorem def3 (f Y : TarskiSet.{u}) : isOnto f Y ↔ RELAT_1.rng f = Y :=
  Iff.rfl

/-- `FUNCT_2:def 4` precursor — bijective as one-to-one and onto. -/
def isBijective (f Y : TarskiSet.{u}) : Prop :=
  FUNCT_1.isOneToOne f ∧ isOnto f Y

/-- Unlabeled `FUNCT_2` (`L533`) — right inverse ⇒ injective + onto.
Mizar `g*f` is `RELAT_1.comp f g`. -/
theorem th23 {f g X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hg : isFunctionOf g Y X)
    (h : RELAT_1.comp f g = RELAT_1.id X) :
    FUNCT_1.isOneToOne f ∧ isOnto g X := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  refine ⟨?inj, ?onto⟩
  · by_cases hY : Y = (∅ : TarskiSet.{u})
    · have hempty : f = (∅ : TarskiSet.{u}) := functionOf_empty_cod hf hY
      intro x1 x2 hx1 _ _
      have hx1' : x1 ∈ RELAT_1.dom (∅ : TarskiSet.{u}) :=
        Eq.subst (motive := fun s => x1 ∈ RELAT_1.dom s) hempty hx1
      exact ((XBOOLE_0.empty_iff x1).mp
        (Eq.subst (motive := fun s => x1 ∈ s) RELAT_1.th38.1 hx1')).elim
    · have hd : RELAT_1.dom f = X := functionOf_dom_eq hf hY
      have h' : RELAT_1.comp f g = RELAT_1.id (RELAT_1.dom f) :=
        Eq.subst (motive := fun s => RELAT_1.comp f g = RELAT_1.id s)
          hd.symm h
      exact FUNCT_1.th31 (functionOf_isFunction hf).2
        (functionOf_isFunction hg).2 h'
  · have hrng : RELAT_1.rng (RELAT_1.comp f g) = X :=
      Eq.subst (motive := fun s => RELAT_1.rng s = X) h.symm RELAT_1.th45.2
    exact (XBOOLE_0.def10 (X := RELAT_1.rng g) (Y := X)).mpr
      ⟨functionOf_rng_sub hg,
        Eq.subst (motive := fun s => s ⊆ RELAT_1.rng g) hrng
          (RELAT_1.th26 (P := f) (R := g))⟩

/-- Unlabeled `FUNCT_2` (`L557`) — Mizar `g*f` is `RELAT_1.comp f g`. -/
theorem th24 {f g X Y Z : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hg : isFunctionOf g Y Z)
    (h : Z = (∅ : TarskiSet.{u}) → Y = (∅ : TarskiSet.{u}))
    (h1 : FUNCT_1.isOneToOne (RELAT_1.comp f g))
    (hr : RELAT_1.rng f = Y) :
    FUNCT_1.isOneToOne f ∧ FUNCT_1.isOneToOne g := by
  have hdG : RELAT_1.dom g = Y := functionOf_dom_eq' hg h
  exact FUNCT_1.th26 (functionOf_isFunction hf).2
    (functionOf_isFunction hg).2 h1 (hr.trans hdG.symm)

/-- `FUNCT_2:25` (`Th25`) — inverse is Function of `Y`,`X`. -/
theorem th25 {f X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (h1 : FUNCT_1.isOneToOne f) (hr : RELAT_1.rng f = Y) :
    isFunctionOf (FUNCT_1.inv f) Y X := by
  have hinv := FUNCT_1.inv_isFunction (functionOf_isFunction hf) h1
  have hdom : RELAT_1.dom (FUNCT_1.inv f) = Y :=
    Eq.subst (motive := fun s => RELAT_1.dom (FUNCT_1.inv f) = s)
      hr (FUNCT_1.th33 h1).1.symm
  have hrng : RELAT_1.rng (FUNCT_1.inv f) ⊆ X := by
    intro x hx
    have hxdom : x ∈ RELAT_1.dom f :=
      Eq.subst (motive := fun s => x ∈ s) (FUNCT_1.th33 h1).2.symm hx
    exact functionOf_dom_sub hf x hxdom
  exact functionOf_of hinv hdom hrng

/-- Unlabeled `FUNCT_2` (`L601`) -/
theorem th26 {f X Y x : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hY : Y ≠ (∅ : TarskiSet.{u})) (h1 : FUNCT_1.isOneToOne f)
    (hx : x ∈ X) :
    FUNCT_1.apply (FUNCT_1.inv f) (FUNCT_1.apply f x) = x :=
  (FUNCT_1.th34 (functionOf_isFunction hf) h1
    (Eq.subst (motive := fun s => x ∈ s) (functionOf_dom_eq hf hY).symm hx)).1

/-- Unlabeled `FUNCT_2` (`L611`) — composition of onto maps. -/
theorem th27 {f g X Y Z : TarskiSet.{u}} (_hf : isFunctionOf f X Y)
    (hg : isFunctionOf g Y Z) (_hY : Y ≠ (∅ : TarskiSet.{u}))
    (hZ : Z ≠ (∅ : TarskiSet.{u}))
    (hontof : isOnto f Y) (hontog : isOnto g Z) :
    isOnto (RELAT_1.comp f g) Z := by
  have hrngf : RELAT_1.rng f = Y := hontof
  have hdG : RELAT_1.dom g = Y := functionOf_dom_eq hg hZ
  have hsub : RELAT_1.dom g ⊆ RELAT_1.rng f :=
    Eq.subst (motive := fun s => RELAT_1.dom g ⊆ s) hrngf.symm
      (Eq.subst (motive := fun s => s ⊆ Y) hdG.symm (fun _ h => h))
  exact (RELAT_1.th28 hsub).trans hontog

/-- Unlabeled `FUNCT_2` (`L628`) -/
theorem th28 {f g X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hg : isFunctionOf g Y X) (hX : X ≠ (∅ : TarskiSet.{u}))
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hr : RELAT_1.rng f = Y)
    (h1 : FUNCT_1.isOneToOne f)
    (hchar : ∀ y x, (y ∈ Y ∧ x = FUNCT_1.apply g y) ↔
      (x ∈ X ∧ y = FUNCT_1.apply f x)) :
    g = FUNCT_1.inv f :=
  ((FUNCT_1.th32 (functionOf_isFunction hf) (functionOf_isFunction hg) h1).mpr
    ⟨Eq.trans (functionOf_dom_eq hg hX) hr.symm, fun y x => by
      constructor
      · intro ⟨hyR, hxeq⟩
        have hyY : y ∈ Y :=
          Eq.subst (motive := fun s => y ∈ s) hr hyR
        have ⟨hx, hyeq⟩ := (hchar y x).mp ⟨hyY, hxeq⟩
        exact ⟨Eq.subst (motive := fun s => x ∈ s)
          (functionOf_dom_eq hf hY).symm hx, hyeq⟩
      · intro ⟨hx, hyeq⟩
        have ⟨hyY, hxeq⟩ := (hchar y x).mpr
          ⟨Eq.subst (motive := fun s => x ∈ s)
            (functionOf_dom_eq hf hY) hx, hyeq⟩
        exact ⟨Eq.subst (motive := fun s => y ∈ s) hr.symm hyY, hxeq⟩⟩)

/-- Unlabeled `FUNCT_2` (`L640`) -/
theorem th29 {f X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hr : RELAT_1.rng f = Y)
    (h1 : FUNCT_1.isOneToOne f) :
    RELAT_1.comp f (FUNCT_1.inv f) = RELAT_1.id X ∧
      RELAT_1.comp (FUNCT_1.inv f) f = RELAT_1.id Y := by
  have hd : RELAT_1.dom f = X := functionOf_dom_eq hf hY
  have hpair := FUNCT_1.th39 (functionOf_isFunction hf) h1
  exact ⟨Eq.subst (motive := fun s => RELAT_1.comp f (FUNCT_1.inv f) = RELAT_1.id s)
      hd hpair.1,
    Eq.subst (motive := fun s => RELAT_1.comp (FUNCT_1.inv f) f = RELAT_1.id s)
      hr hpair.2⟩

/-- Unlabeled `FUNCT_2` (`L650`) -/
theorem th30 {f g X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hg : isFunctionOf g Y X) (hX : X ≠ (∅ : TarskiSet.{u}))
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hr : RELAT_1.rng f = Y)
    (hcomp : RELAT_1.comp f g = RELAT_1.id X) (h1 : FUNCT_1.isOneToOne f) :
    g = FUNCT_1.inv f := by
  have hd : RELAT_1.dom f = X := functionOf_dom_eq hf hY
  have hdG : RELAT_1.dom g = Y := functionOf_dom_eq hg hX
  exact FUNCT_1.th41 (functionOf_isFunction hf) (functionOf_isFunction hg) h1
    (hr.trans hdG.symm)
    (Eq.subst (motive := fun s => RELAT_1.comp f g = RELAT_1.id s) hd.symm hcomp)

/-- Unlabeled `FUNCT_2` (`L661`) -/
theorem th31 {f X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hex : ∃ g, isFunctionOf g Y X ∧ RELAT_1.comp f g = RELAT_1.id X) :
    FUNCT_1.isOneToOne f := by
  obtain ⟨g, hg, hcomp⟩ := hex
  have hd : RELAT_1.dom f = X := functionOf_dom_eq hf hY
  exact FUNCT_1.th31 (functionOf_isFunction hf).2 (functionOf_isFunction hg).2
    (Eq.subst (motive := fun s => RELAT_1.comp f g = RELAT_1.id s) hd.symm hcomp)

/-- `FUNCT_2:32` (`Th32`) — restriction of a Function of. -/
theorem th32 {f X Y Z : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (hZ : Z ⊆ X) :
    isFunctionOf (RELAT_1.restrict f Z) Z Y := by
  have hd : RELAT_1.dom f = X := functionOf_dom_eq' hf h
  have hdomR : RELAT_1.dom (RELAT_1.restrict f Z) = Z :=
    RELAT_1.th62 (Eq.subst (motive := fun s => Z ⊆ s) hd.symm hZ)
  have hrng : RELAT_1.rng (RELAT_1.restrict f Z) ⊆ Y :=
    XBOOLE_1.th1 (RELAT_1.th70 (R := f) (X := Z)) (functionOf_rng_sub hf)
  exact functionOf_of
    (FUNCT_1.restrict_isFunction (functionOf_isFunction hf)) hdomR hrng

/-- Unlabeled `FUNCT_2` (`L700`) -/
theorem th33 {f X Y Z : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hX : X ⊆ Z) : RELAT_1.restrict f Z = f :=
  RELSET_1.th19 (functionOf_isRelationOf hf) hX

/-- Unlabeled `FUNCT_2` (`L703`) — Mizar restrictRng. -/
theorem th34 {f X Y Z x : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hx : x ∈ X)
    (hfx : FUNCT_1.apply f x ∈ Z) :
    FUNCT_1.apply (RELAT_1.restrictRng Z f) x = FUNCT_1.apply f x := by
  have hd : x ∈ RELAT_1.dom f :=
    Eq.subst (motive := fun s => x ∈ s) (functionOf_dom_eq hf hY).symm hx
  have hxR : x ∈ RELAT_1.dom (RELAT_1.restrictRng Z f) :=
    (FUNCT_1.th54 (functionOf_isFunction hf)).mpr ⟨hd, hfx⟩
  exact FUNCT_1.th55 (functionOf_isFunction hf) hxR

/-- Unlabeled `FUNCT_2` (`L716`) -/
theorem th35 {f X Y P y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hex : ∃ x, x ∈ X ∧ x ∈ P ∧ y = FUNCT_1.apply f x) :
    y ∈ RELAT_1.image f P := by
  obtain ⟨x, hxX, hxP, heq⟩ := hex
  have hd : RELAT_1.dom f = X := functionOf_dom_eq hf hY
  exact (FUNCT_1.def6 (functionOf_isFunction hf).2).mpr
    ⟨x, Eq.subst (motive := fun s => x ∈ s) hd.symm hxX, hxP, heq⟩

/-- Unlabeled `FUNCT_2` (`L730`) — image ⊆ codomain. -/
theorem th36 {f X Y P : TarskiSet.{u}} (hf : isFunctionOf f X Y) :
    RELAT_1.image f P ⊆ Y :=
  XBOOLE_1.th1 (RELAT_1.th111 (R := f) (X := P)) (functionOf_rng_sub hf)

-- FUNCT_2 Th37 canceled; skipped.

/-- Unlabeled `FUNCT_2` (`L735`) — membership in preimage. -/
theorem th38 {f X Y Q x : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hY : Y ≠ (∅ : TarskiSet.{u})) :
    x ∈ RELAT_1.invimage f Q ↔
      x ∈ X ∧ FUNCT_1.apply f x ∈ Q := by
  have hd : RELAT_1.dom f = X := functionOf_dom_eq hf hY
  constructor
  · intro hx
    have ⟨hdom, hQ⟩ := (FUNCT_1.def7 (functionOf_isFunction hf).2).mp hx
    exact ⟨Eq.subst (motive := fun s => x ∈ s) hd hdom, hQ⟩
  · intro ⟨hxX, hQ⟩
    exact (FUNCT_1.def7 (functionOf_isFunction hf).2).mpr
      ⟨Eq.subst (motive := fun s => x ∈ s) hd.symm hxX, hQ⟩

/-- Unlabeled `FUNCT_2` (`L745`) -/
theorem th39 {f X Y Q : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y) :
    RELAT_1.invimage f Q ⊆ X :=
  fun x hx => RELSET_1.relationOf_defined hf.2 x
    ((FUNCT_1.def7 hf.1.2).mp hx).1

/-- `FUNCT_2:40` (`Th40`) -/
theorem th40 {f X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    RELAT_1.invimage f Y = X := by
  have hinter : RELAT_1.rng f ∩ Y = RELAT_1.rng f :=
    XBOOLE_1.th28 (functionOf_rng_sub hf)
  have h1 : RELAT_1.invimage f Y =
      RELAT_1.invimage f (RELAT_1.rng f) :=
    Eq.trans (RELAT_1.th133 (R := f) (Y := Y))
      (congrArg (RELAT_1.invimage f) hinter)
  have hd : RELAT_1.dom f = X := functionOf_dom_eq' hf h
  exact h1.trans ((RELAT_1.th134 (R := f)).trans hd)

/-- Unlabeled `FUNCT_2` (`L760`) -/
theorem th41 {f X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y) :
    (∀ y, y ∈ Y → RELAT_1.invimage f (TARSKI.singleton y) ≠
      (∅ : TarskiSet.{u})) ↔
      RELAT_1.rng f = Y := by
  constructor
  · intro h
    have hsub : Y ⊆ RELAT_1.rng f :=
      FUNCT_1.th73 (R := f) (Y := Y) fun y hy => h y hy
    exact (XBOOLE_0.def10 (X := RELAT_1.rng f) (Y := Y)).mpr
      ⟨functionOf_rng_sub hf, hsub⟩
  · intro hrng y hy
    exact (FUNCT_1.th72 (R := f) (y := y)).mp
      (Eq.subst (motive := fun s => y ∈ s) hrng.symm hy)

/-- `FUNCT_2:42` (`Th42`) -/
theorem th42 {f X Y P : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (hP : P ⊆ X) :
    P ⊆ RELAT_1.invimage f (RELAT_1.image f P) := by
  have hd : RELAT_1.dom f = X := functionOf_dom_eq' hf h
  exact FUNCT_1.th76 (R := f) (X := P)
    (Eq.subst (motive := fun s => P ⊆ s) hd.symm hP)

/-- Unlabeled `FUNCT_2` (`L784`) -/
theorem th43 {f X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    RELAT_1.invimage f (RELAT_1.image f X) = X := by
  have hd : RELAT_1.dom f = X := functionOf_dom_eq' hf h
  have himg : RELAT_1.image f X = RELAT_1.rng f :=
    Eq.trans (congrArg (RELAT_1.image f) hd.symm) (RELAT_1.th113 (R := f))
  exact Eq.subst (motive := fun s => RELAT_1.invimage f s = X) himg.symm
    ((RELAT_1.th134 (R := f)).trans hd)

/-- Unlabeled `FUNCT_2` (`L795`) — Mizar `g*f`. -/
theorem th44 {f g X Y Z Q : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hg : isFunctionOf g Y Z)
    (h : Z = (∅ : TarskiSet.{u}) → Y = (∅ : TarskiSet.{u})) :
    RELAT_1.invimage f Q ⊆
      RELAT_1.invimage (RELAT_1.comp f g) (RELAT_1.image g Q) := by
  have hdG : RELAT_1.dom g = Y := functionOf_dom_eq' hg h
  have hr : RELAT_1.rng f ⊆ RELAT_1.dom g :=
    Eq.subst (motive := fun s => RELAT_1.rng f ⊆ s) hdG.symm
      (functionOf_rng_sub hf)
  exact FUNCT_1.th90 (R := f) (S := g) (X := Q) hr

/-- Unlabeled `FUNCT_2` (`L808`) -/
theorem th45 {f Y P : TarskiSet.{u}}
    (hf : isFunctionOf f (∅ : TarskiSet.{u}) Y) :
    RELAT_1.image f P = (∅ : TarskiSet.{u}) := by
  have hdomE : RELAT_1.dom f = (∅ : TarskiSet.{u}) :=
    (XBOOLE_0.def10 (X := RELAT_1.dom f) (Y := (∅ : TarskiSet.{u}))).mpr
      ⟨functionOf_dom_sub hf, XBOOLE_1.th2⟩
  apply (XBOOLE_0.def10 (X := RELAT_1.image f P)
    (Y := (∅ : TarskiSet.{u}))).mpr
  constructor
  · intro y hy
    obtain ⟨x, hx, _, _⟩ := (FUNCT_1.def6 (functionOf_isFunction hf).2).mp hy
    exact ((XBOOLE_0.empty_iff x).mp (hdomE ▸ hx)).elim
  · exact XBOOLE_1.th2

/-- Unlabeled `FUNCT_2` (`L811`) -/
theorem th46 {f Y Q : TarskiSet.{u}}
    (hf : isFunctionOf f (∅ : TarskiSet.{u}) Y) :
    RELAT_1.invimage f Q = (∅ : TarskiSet.{u}) := by
  have hdom : RELAT_1.dom f = (∅ : TarskiSet.{u}) :=
    (XBOOLE_0.def10 (X := RELAT_1.dom f) (Y := (∅ : TarskiSet.{u}))).mpr
      ⟨functionOf_dom_sub hf, XBOOLE_1.th2⟩
  apply (XBOOLE_0.def10 (X := RELAT_1.invimage f Q)
    (Y := (∅ : TarskiSet.{u}))).mpr
  constructor
  · intro x hx
    have ⟨hd, _⟩ := (FUNCT_1.def7 (functionOf_isFunction hf).2).mp hx
    exact ((XBOOLE_0.empty_iff x).mp (hdom ▸ hd)).elim
  · exact XBOOLE_1.th2

/-- Unlabeled `FUNCT_2` (`L814`) -/
theorem th47 {f x Y : TarskiSet.{u}}
    (hf : isFunctionOf f (TARSKI.singleton x) Y)
    (hY : Y ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.apply f x ∈ Y := by
  have hd : RELAT_1.dom f = TARSKI.singleton x :=
    functionOf_dom_eq hf hY
  have hx : x ∈ RELAT_1.dom f :=
    Eq.subst (motive := fun s => x ∈ s) hd.symm
      ((singleton_iff x x).mpr rfl)
  exact functionOf_rng_sub hf _
    (FUNCT_1.th3 (functionOf_isFunction hf).2 hx)

/-- `FUNCT_2:48` (`Th48`) -/
theorem th48 {f x Y : TarskiSet.{u}}
    (hf : isFunctionOf f (TARSKI.singleton x) Y)
    (hY : Y ≠ (∅ : TarskiSet.{u})) :
    RELAT_1.rng f = TARSKI.singleton (FUNCT_1.apply f x) :=
  FUNCT_1.th4 (functionOf_isFunction hf).2 (functionOf_dom_eq hf hY)

/-- Unlabeled `FUNCT_2` (`L835`) -/
theorem th49 {f x Y P : TarskiSet.{u}}
    (hf : isFunctionOf f (TARSKI.singleton x) Y)
    (hY : Y ≠ (∅ : TarskiSet.{u})) :
    RELAT_1.image f P ⊆ TARSKI.singleton (FUNCT_1.apply f x) :=
  XBOOLE_1.th1 (RELAT_1.th111 (R := f) (X := P))
    (Eq.subst (motive := fun s => RELAT_1.rng f ⊆ s) (th48 hf hY)
      (fun _ h => h))

/-- `FUNCT_2:50` (`Th50`) -/
theorem th50 {f X y x : TarskiSet.{u}}
    (hf : isFunctionOf f X (TARSKI.singleton y))
    (hx : x ∈ X) :
    FUNCT_1.apply f x = y := by
  have := Classical.propDecidable
    (TARSKI.singleton y = (∅ : TarskiSet.{u}))
  by_cases hY : TARSKI.singleton y = (∅ : TarskiSet.{u})
  · exact ((XBOOLE_0.empty_iff y).mp
      (hY ▸ (singleton_iff y y).mpr rfl)).elim
  · exact (singleton_iff y (FUNCT_1.apply f x)).mp (th5 hf hY hx)

/-- `FUNCT_2:51` (`Th51`) -/
theorem th51 {f1 f2 X y : TarskiSet.{u}}
    (h1 : isFunctionOf f1 X (TARSKI.singleton y))
    (h2 : isFunctionOf f2 X (TARSKI.singleton y)) :
    f1 = f2 :=
  th12 h1 h2 fun _x hx => (th50 h1 hx).trans (th50 h2 hx).symm

/-- `FUNCT_2:52` (`Th52`) — Function of `X`,`X` is total. -/
theorem th52 {f X : TarskiSet.{u}} (hf : isFunctionOf f X X) :
    RELAT_1.dom f = X :=
  functionOf_dom_eq' hf (fun h => h)

/-- Registration: composition quasi_total (right factor on diagonal).
Mizar `f*g` with f:X→Y, g:X→X is Lean `comp g f`. -/
theorem comp_quasiTotal_diag_right {f g X Y : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f X Y) (hqf : isQuasiTotal f X Y)
    (hg : PARTFUN1.isPartFunc g X X) (hqg : isQuasiTotal g X X) :
    isQuasiTotal (RELAT_1.comp g f) X Y := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact ⟨fun hne => (hne hY).elim,
      fun _ => relationOf_empty_cod
        (RELSET_1.comp_isRelationOf hg.2 hf.2) hY⟩
  · have hdf : RELAT_1.dom f = X := hqf.1 hY
    have hdg : RELAT_1.dom g = X := th52 ⟨hg, hqg⟩
    have hsub : RELAT_1.rng g ⊆ RELAT_1.dom f :=
      Eq.subst (motive := fun s => RELAT_1.rng g ⊆ s) hdf.symm
        (RELSET_1.relationOf_valued hg.2)
    exact ⟨fun _ => (RELAT_1.th27 hsub).trans hdg,
      fun hempty => (hY hempty).elim⟩

/-- Registration: composition quasi_total (left factor on diagonal).
Mizar `f*g` with f:Y→Y, g:X→Y is Lean `comp g f`. -/
theorem comp_quasiTotal_diag_left {f g X Y : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f Y Y) (hqf : isQuasiTotal f Y Y)
    (hg : PARTFUN1.isPartFunc g X Y) (hqg : isQuasiTotal g X Y) :
    isQuasiTotal (RELAT_1.comp g f) X Y := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact ⟨fun hne => (hne hY).elim,
      fun _ => relationOf_empty_cod
        (RELSET_1.comp_isRelationOf hg.2 hf.2) hY⟩
  · have hdf : RELAT_1.dom f = Y := th52 ⟨hf, hqf⟩
    have hdg : RELAT_1.dom g = X := hqg.1 hY
    have hsub : RELAT_1.rng g ⊆ RELAT_1.dom f :=
      Eq.subst (motive := fun s => RELAT_1.rng g ⊆ s) hdf.symm
        (RELSET_1.relationOf_valued hg.2)
    exact ⟨fun _ => (RELAT_1.th27 hsub).trans hdg,
      fun hempty => (hY hempty).elim⟩

/-- `FUNCT_2:53` (`Th53`) — Mizar `rng(g*f)`. -/
theorem th53 {f g X : TarskiSet.{u}}
    (_hf : RELSET_1.isRelationOf f X X)
    (hg : RELSET_1.isRelationOf g X X)
    (hrf : RELAT_1.rng f = X) (hrg : RELAT_1.rng g = X) :
    RELAT_1.rng (RELAT_1.comp f g) = X := by
  have h1 : RELAT_1.rng (RELAT_1.comp f g) =
      RELAT_1.image g (RELAT_1.rng f) :=
    RELAT_1.th127 (P := f) (R := g)
  exact Eq.trans h1
    (Eq.trans (congrArg (RELAT_1.image g) hrf)
      (Eq.trans (RELSET_1.th22 hg).1 hrg))

/-- Unlabeled `FUNCT_2` (`L929`) — Mizar `g*f = f`. -/
theorem th54 {f g X : TarskiSet.{u}} (hf : isFunctionOf f X X)
    (hg : isFunctionOf g X X)
    (hcomp : RELAT_1.comp f g = f) (hr : RELAT_1.rng f = X) :
    g = RELAT_1.id X := by
  have h' := FUNCT_1.th23 (functionOf_isFunction hf)
    (functionOf_isFunction hg) (hr.trans (th52 hg).symm) hcomp
  exact Eq.subst (motive := fun s => g = RELAT_1.id s) (th52 hg) h'

/-- Unlabeled `FUNCT_2` (`L937`) — Mizar `f*g = f`. -/
theorem th55 {f g X : TarskiSet.{u}} (hf : isFunctionOf f X X)
    (hg : isFunctionOf g X X)
    (hcomp : RELAT_1.comp g f = f) (h1 : FUNCT_1.isOneToOne f) :
    g = RELAT_1.id X :=
  FUNCT_1.th28 (functionOf_isFunction hf) (functionOf_isFunction hg)
    (th52 hf) (th52 hg) (functionOf_rng_sub hg) h1 hcomp

/-- `FUNCT_2:56` (`Th56`) -/
theorem th56 {f X : TarskiSet.{u}} (hf : isFunctionOf f X X) :
    FUNCT_1.isOneToOne f ↔
      ∀ x1 x2, x1 ∈ X → x2 ∈ X →
        FUNCT_1.apply f x1 = FUNCT_1.apply f x2 → x1 = x2 :=
  th19 hf (fun h => h)

/-- `FUNCT_2:def 4` — permutation of `X`. -/
def isPermutation (f X : TarskiSet.{u}) : Prop :=
  isFunctionOf f X X ∧ isBijective f X

theorem def4 (f X : TarskiSet.{u}) :
    isPermutation f X ↔
      isFunctionOf f X X ∧ FUNCT_1.isOneToOne f ∧ isOnto f X :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, ⟨h.2.1, h.2.2⟩⟩⟩

/-- `FUNCT_2:57` (`Th57`) -/
theorem th57 {f X : TarskiSet.{u}} (hf : isFunctionOf f X X)
    (h1 : FUNCT_1.isOneToOne f) (hr : RELAT_1.rng f = X) :
    isPermutation f X :=
  ⟨hf, ⟨h1, hr⟩⟩

/-- Unlabeled `FUNCT_2` (`L998`) -/
theorem th58 {f X : TarskiSet.{u}} (hf : isFunctionOf f X X)
    (h1 : FUNCT_1.isOneToOne f) :
    ∀ x1 x2, x1 ∈ X → x2 ∈ X →
      FUNCT_1.apply f x1 = FUNCT_1.apply f x2 → x1 = x2 :=
  (th56 hf).mp h1

/-- Registration: composition of onto PartFuncs on `X` is onto.
Mizar `f*g` is Lean `comp f g`. -/
theorem comp_onto_diag {f g X : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f X X) (hontof : isOnto f X)
    (hg : PARTFUN1.isPartFunc g X X) (hontog : isOnto g X) :
    isOnto (RELAT_1.comp f g) X :=
  th53 hf.2 hg.2 hontof hontog

/-- Registration: composition of bijective Functions of `X`,`X` is bijective.
Mizar `g*f` is Lean `comp f g`. -/
theorem comp_bijective_diag {f g X : TarskiSet.{u}}
    (hf : isFunctionOf f X X) (hbf : isBijective f X)
    (hg : isFunctionOf g X X) (hbg : isBijective g X) :
    isBijective (RELAT_1.comp f g) X :=
  ⟨FUNCT_1.th24 (functionOf_isFunction hf).2 (functionOf_isFunction hg).2
      hbf.1 hbg.1,
    th53 (functionOf_isRelationOf hf) (functionOf_isRelationOf hg)
      hbf.2 hbg.2⟩

/-- Inverse of a permutation is a permutation. -/
theorem inv_isPermutation {f X : TarskiSet.{u}}
    (hf : isPermutation f X) :
    isPermutation (FUNCT_1.inv f) X := by
  have ⟨hfun, ⟨h1, honto⟩⟩ := hf
  have hinv := th25 hfun h1 honto
  have hrng : RELAT_1.rng (FUNCT_1.inv f) = X :=
    Eq.subst (motive := fun s => RELAT_1.rng (FUNCT_1.inv f) = s)
      (th52 hfun) (FUNCT_1.th33 h1).2.symm
  exact th57 hinv (FUNCT_1.th40 (functionOf_isFunction hfun) h1) hrng

/-- Unlabeled `FUNCT_2` (`L1069`) — Mizar `g*f = g` is Lean `comp f g = g`. -/
theorem th59 {f g X : TarskiSet.{u}} (hf : isPermutation f X)
    (hg : isPermutation g X)
    (hcomp : RELAT_1.comp f g = g) :
    f = RELAT_1.id X :=
  FUNCT_1.th28 (functionOf_isFunction hg.1) (functionOf_isFunction hf.1)
    (th52 hg.1) (th52 hf.1) (functionOf_rng_sub hf.1) hg.2.1 hcomp

/-- Unlabeled `FUNCT_2` (`L1078`) — Mizar `g*f = id`. -/
theorem th60 {f g X : TarskiSet.{u}} (hf : isPermutation f X)
    (hg : isPermutation g X)
    (hcomp : RELAT_1.comp f g = RELAT_1.id X) :
    g = FUNCT_1.inv f :=
  FUNCT_1.th41 (functionOf_isFunction hf.1) (functionOf_isFunction hg.1)
    hf.2.1 (hf.2.2.trans (th52 hg.1).symm)
    (Eq.subst (motive := fun s => RELAT_1.comp f g = RELAT_1.id s)
      (th52 hf.1).symm hcomp)

/-- Unlabeled `FUNCT_2` (`L1087`) -/
theorem th61 {f X : TarskiSet.{u}} (hf : isPermutation f X) :
    RELAT_1.comp f (FUNCT_1.inv f) = RELAT_1.id X ∧
      RELAT_1.comp (FUNCT_1.inv f) f = RELAT_1.id X := by
  have hpair := FUNCT_1.th39 (functionOf_isFunction hf.1) hf.2.1
  exact ⟨Eq.subst (motive := fun s =>
        RELAT_1.comp f (FUNCT_1.inv f) = RELAT_1.id s)
      (th52 hf.1) hpair.1,
    Eq.subst (motive := fun s =>
        RELAT_1.comp (FUNCT_1.inv f) f = RELAT_1.id s)
      hf.2.2 hpair.2⟩

/-- `FUNCT_2:62` (`Th62`) -/
theorem th62 {f X P : TarskiSet.{u}} (hf : isPermutation f X) (hP : P ⊆ X) :
    RELAT_1.image f (RELAT_1.invimage f P) = P ∧
      RELAT_1.invimage f (RELAT_1.image f P) = P := by
  have hd : RELAT_1.dom f = X := th52 hf.1
  have h1 : P ⊆ RELAT_1.invimage f (RELAT_1.image f P) :=
    FUNCT_1.th76 (R := f) (X := P)
      (Eq.subst (motive := fun s => P ⊆ s) hd.symm hP)
  have h2 : RELAT_1.invimage f (RELAT_1.image f P) ⊆ P :=
    FUNCT_1.th82 (functionOf_isFunction hf.1).2 hf.2.1 (X := P)
  have himg : RELAT_1.image f (RELAT_1.invimage f P) = P :=
    FUNCT_1.th77 (functionOf_isFunction hf.1).2
      (Eq.subst (motive := fun s => P ⊆ s) hf.2.2.symm hP)
  exact ⟨himg, (XBOOLE_0.def10 (X := RELAT_1.invimage f (RELAT_1.image f P))
    (Y := P)).mpr ⟨h2, h1⟩⟩

/-- Registration: composition of Function of `X`,`D` and `D`,`Z` is quasi_total
when `D` nonempty. Mizar `g*f` is Lean `comp f g`. -/
theorem comp_quasiTotal_ne_mid {f g X D Z : TarskiSet.{u}}
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f X D) (hg : isFunctionOf g D Z) :
    isQuasiTotal (RELAT_1.comp f g) X Z :=
  th13 (functionOf_isRelationOf hf) hf.2 (functionOf_isRelationOf hg) hg.2
    (fun hD' => (hD hD').elim)

/-- `FUNCT_2:sch FuncExD` -/
theorem sch_FuncExD (C D : TarskiSet.{u})
    (_hC : C ≠ (∅ : TarskiSet.{u})) (_hD : D ≠ (∅ : TarskiSet.{u}))
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hP : ∀ x, x ∈ C → ∃ y, y ∈ D ∧ P x y) :
    ∃ f, isFunctionOf f C D ∧ ∀ x, x ∈ C → P x (FUNCT_1.apply f x) :=
  sch_FuncEx1 C D P hP

/-- `FUNCT_2:sch LambdaD` -/
theorem sch_LambdaD (C D : TarskiSet.{u})
    (hC : C ≠ (∅ : TarskiSet.{u})) (hD : D ≠ (∅ : TarskiSet.{u}))
    (F : TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ x, x ∈ C → F x ∈ D) :
    ∃ f, isFunctionOf f C D ∧
      ∀ x, x ∈ C → FUNCT_1.apply f x = F x :=
  sch_Lambda1 C D F hF

/-- `FUNCT_2:63` (`Th63`) -/
theorem th63 {f1 f2 X Y : TarskiSet.{u}} (h1 : isFunctionOf f1 X Y)
    (h2 : isFunctionOf f2 X Y)
    (hv : ∀ x, x ∈ X → FUNCT_1.apply f1 x = FUNCT_1.apply f2 x) :
    f1 = f2 :=
  th12 h1 h2 hv

/-- `FUNCT_2:64` (`Th64`) -/
theorem th64 {f X Y P y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hy : y ∈ RELAT_1.image f P) :
    ∃ x, x ∈ X ∧ x ∈ P ∧ y = FUNCT_1.apply f x := by
  obtain ⟨x, hxD, hxP, heq⟩ :=
    (FUNCT_1.def6 (functionOf_isFunction hf).2).mp hy
  exact ⟨x, functionOf_dom_sub hf x hxD, hxP, heq⟩

/-- Unlabeled `FUNCT_2` (`L1186`) -/
theorem th65 {f X Y P y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hy : y ∈ RELAT_1.image f P) :
    ∃ c, c ∈ X ∧ c ∈ P ∧ y = FUNCT_1.apply f c :=
  th64 hf hy

/-- `FUNCT_2:66` (`Th66`) -/
theorem th66 {f X Y : TarskiSet.{u}} (hf : f ∈ Funcs X Y) :
    isFunctionOf f X Y := by
  obtain ⟨F, hF, heq, hd, hr⟩ := (def2 X Y f).mp hf
  have hf' : FUNCT_1.isFunction f :=
    Eq.subst (motive := FUNCT_1.isFunction) heq.symm hF
  have hd' : RELAT_1.dom f = X :=
    Eq.subst (motive := fun s => RELAT_1.dom s = X) heq.symm hd
  have hr' : RELAT_1.rng f ⊆ Y :=
    Eq.subst (motive := fun s => RELAT_1.rng s ⊆ Y) heq.symm hr
  exact functionOf_of hf' hd' hr'

/-- `FUNCT_2:sch Lambda1C` — via `PARTFUN1.sch_LambdaC`. -/
theorem sch_Lambda1C (A B : TarskiSet.{u})
    (C : TarskiSet.{u} → Prop)
    (F G : TarskiSet.{u} → TarskiSet.{u})
    (hFG : ∀ x, x ∈ A → (C x → F x ∈ B) ∧ (¬ C x → G x ∈ B)) :
    ∃ f, isFunctionOf f A B ∧
      ∀ x, x ∈ A →
        (C x → FUNCT_1.apply f x = F x) ∧
          (¬ C x → FUNCT_1.apply f x = G x) := by
  have hBne : B = (∅ : TarskiSet.{u}) → A = (∅ : TarskiSet.{u}) := by
    intro hB
    refine Classical.byContradiction fun hA => ?_
    obtain ⟨x, hx⟩ := XBOOLE_0.th7 hA
    exact Or.elim (Classical.em (C x))
      (fun hC => (XBOOLE_0.empty_iff (F x)).mp (hB ▸ (hFG x hx).1 hC))
      (fun hn => (XBOOLE_0.empty_iff (G x)).mp (hB ▸ (hFG x hx).2 hn))
  obtain ⟨f, hf, hd, hv⟩ := PARTFUN1.sch_LambdaC A C F G
  have hr : RELAT_1.rng f ⊆ B := by
    intro y hy
    obtain ⟨x, hx, heq⟩ := (FUNCT_1.def3 hf.2).mp hy
    have hxA : x ∈ A := Eq.subst (motive := fun s => x ∈ s) hd hx
    have hvx := hv x hxA
    exact Or.elim (Classical.em (C x))
      (fun hC =>
        have hyF : y = F x := heq.trans (hvx.1 hC)
        Eq.subst (motive := fun s => s ∈ B) hyF.symm ((hFG x hxA).1 hC))
      (fun hn =>
        have hyG : y = G x := heq.trans (hvx.2 hn)
        Eq.subst (motive := fun s => s ∈ B) hyG.symm ((hFG x hxA).2 hn))
  exact ⟨f, functionOf_of hf hd hr, hv⟩

/-- Unlabeled `FUNCT_2` (`L1250`) -/
theorem th67 {f X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (hd : RELAT_1.dom f = X) :
    isFunctionOf f X Y :=
  functionOf_of hf.1 hd (RELSET_1.relationOf_valued hf.2)

/-- Unlabeled `FUNCT_2` (`L1258`) -/
theorem th68 {f X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (ht : PARTFUN1.isTotal f X) :
    isFunctionOf f X Y :=
  th67 hf ht

/-- Unlabeled `FUNCT_2` (`L1261`) -/
theorem th69 {f X Y : TarskiSet.{u}} (_hf : PARTFUN1.isPartFunc f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (hfun : isFunctionOf f X Y) :
    PARTFUN1.isTotal f X :=
  functionOf_dom_eq' hfun h

/-- Unlabeled `FUNCT_2` (`L1265`) — clip of Function of is total. -/
theorem th70 {f X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    PARTFUN1.isTotal (PARTFUN1.clip f X Y) X := by
  have hd : RELAT_1.dom f = X := functionOf_dom_eq' hf h
  have hclip : PARTFUN1.clip f X Y = f :=
    (PARTFUN1.th31 (functionOf_isFunction hf)
      (functionOf_dom_sub hf) (functionOf_rng_sub hf)).symm
  exact Eq.subst (motive := fun s => PARTFUN1.isTotal s X) hclip.symm hd

/-- Registration: clip of Function of `X`,`X` is total. -/
theorem clip_diag_total {f X : TarskiSet.{u}} (hf : isFunctionOf f X X) :
    PARTFUN1.isTotal (PARTFUN1.clip f X X) X :=
  th70 hf (fun h => h)

/-- `FUNCT_2:71` (`Th71`) -/
theorem th71 {f X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    ∃ g, isFunctionOf g X Y ∧
      ∀ x, x ∈ RELAT_1.dom f → FUNCT_1.apply g x = FUNCT_1.apply f x := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · have hX : X = (∅ : TarskiSet.{u}) := h hY
    have hempty : f = (∅ : TarskiSet.{u}) :=
      relationOf_empty_cod hf.2 hY
    have hf' : isFunctionOf f X Y :=
      Eq.subst (motive := fun s => isFunctionOf s X Y) hempty.symm
        (Eq.subst (motive := fun s => isFunctionOf (∅ : TarskiSet.{u}) s Y)
          hX.symm
          (Eq.subst (motive := fun s =>
              isFunctionOf (∅ : TarskiSet.{u}) (∅ : TarskiSet.{u}) s)
            hY.symm (empty_isFunctionOf (∅ : TarskiSet.{u}))))
    exact ⟨f, hf', fun _ _ => rfl⟩
  · obtain ⟨y, hy⟩ := XBOOLE_0.th7 hY
    obtain ⟨g, hg, hv⟩ := sch_Lambda1C X Y
      (fun x => x ∈ RELAT_1.dom f)
      (fun x => FUNCT_1.apply f x)
      (fun _ => y)
      (fun x hx => ⟨fun hxd => PARTFUN1.th4 hf.1
          (RELSET_1.relationOf_valued hf.2) hxd,
        fun _ => hy⟩)
    exact ⟨g, hg, fun x hx =>
      (hv x (RELSET_1.relationOf_defined hf.2 x hx)).1 hx⟩

/-- Unlabeled `FUNCT_2` (`L1303`) -/
theorem th72 {X Y : TarskiSet.{u}} :
    Funcs X Y ⊆ PARTFUN1.PFuncs X Y := by
  intro x hx
  obtain ⟨f, hf, heq, hd, hr⟩ := (def2 X Y x).mp hx
  exact (PARTFUN1.def3 X Y x).mpr
    ⟨f, hf, heq, hd ▸ fun _ h => h, hr⟩

/-- Unlabeled `FUNCT_2` (`L1312`) -/
theorem th73 {f g X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (hg : isFunctionOf g X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (ht : PARTFUN1.tolerates f g) :
    f = g :=
  PARTFUN1.th66 hf.1 hg.1 (functionOf_dom_eq' hf h)
    (functionOf_dom_eq' hg h) ht

/-- Unlabeled `FUNCT_2` (`L1316`) -/
theorem th74 {f g X : TarskiSet.{u}} (hf : isFunctionOf f X X)
    (hg : isFunctionOf g X X) (ht : PARTFUN1.tolerates f g) :
    f = g :=
  th73 hf hg (fun h => h) ht

/-- `FUNCT_2:75` (`Th75`) -/
theorem th75 {f g X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (hg : isFunctionOf g X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    PARTFUN1.tolerates f g ↔
      ∀ x, x ∈ RELAT_1.dom f → FUNCT_1.apply f x = FUNCT_1.apply g x :=
  PARTFUN1.th53 hf.1 (functionOf_isFunction hg)
    (Eq.subst (motive := fun s => RELAT_1.dom f ⊆ s)
      (functionOf_dom_eq' hg h).symm (RELSET_1.relationOf_defined hf.2))

/-- Unlabeled `FUNCT_2` (`L1330`) -/
theorem th76 {f g X : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X X)
    (hg : isFunctionOf g X X) :
    PARTFUN1.tolerates f g ↔
      ∀ x, x ∈ RELAT_1.dom f → FUNCT_1.apply f x = FUNCT_1.apply g x :=
  th75 hf hg (fun h => h)

/-- `FUNCT_2:77` (`Th77`) -/
theorem th77 {f X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    ∃ g, isFunctionOf g X Y ∧ PARTFUN1.tolerates f g := by
  obtain ⟨g, hg, hv⟩ := th71 hf h
  exact ⟨g, hg, (th75 hf hg h).mpr fun x hx => (hv x hx).symm⟩

/-- Unlabeled `FUNCT_2` (`L1353`) -/
theorem th78 {f g h X : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X X)
    (hg : PARTFUN1.isPartFunc g X X) (hh : isFunctionOf h X X)
    (hfh : PARTFUN1.tolerates f h) (hgh : PARTFUN1.tolerates g h) :
    PARTFUN1.tolerates f g :=
  PARTFUN1.th67 hf hg hh.1 hfh hgh (th52 hh)

/-- Unlabeled `FUNCT_2` (`L1357`) -/
theorem th79 {f g X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (hg : PARTFUN1.isPartFunc g X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (ht : PARTFUN1.tolerates f g) :
    ∃ k, isFunctionOf k X Y ∧ PARTFUN1.tolerates f k ∧
      PARTFUN1.tolerates g k := by
  obtain ⟨k, hp, htt, hfk, hgk⟩ := PARTFUN1.th68 hf hg h ht
  exact ⟨k, th68 hp htt, hfk, hgk⟩

/-- Unlabeled `FUNCT_2` (`L1369`) -/
theorem th80 {f g X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (hg : isFunctionOf g X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (ht : PARTFUN1.tolerates f g) :
    g ∈ PARTFUN1.TotFuncs hf :=
  (PARTFUN1.def5 hf g).mpr
    ⟨g, hg.1, rfl, functionOf_dom_eq' hg h, ht⟩

/-- Unlabeled `FUNCT_2` (`L1373`) -/
theorem th81 {f g X : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X X)
    (hg : isFunctionOf g X X) (ht : PARTFUN1.tolerates f g) :
    g ∈ PARTFUN1.TotFuncs hf :=
  th80 hf hg (fun h => h) ht

/-- `FUNCT_2:82` (`Th82`) -/
theorem th82 {f g X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (hg : g ∈ PARTFUN1.TotFuncs hf) :
    isFunctionOf g X Y := by
  obtain ⟨g9, hp, heq, ht, _⟩ := (PARTFUN1.def5 hf g).mp hg
  exact Eq.subst (motive := fun s => isFunctionOf s X Y) heq (th68 hp ht)

/-- Unlabeled `FUNCT_2` (`L1390`) -/
theorem th83 {f X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y) :
    PARTFUN1.TotFuncs hf ⊆ Funcs X Y := by
  intro g hg
  have hg' := th82 hf hg
  have htot : PARTFUN1.isTotal g X := PARTFUN1.th70 hf hg'.1 hg
  have hOK : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}) := by
    intro hY
    have hempty : g = (∅ : TarskiSet.{u}) := functionOf_empty_cod hg' hY
    have hdomE : RELAT_1.dom g = (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u}))
        hempty.symm RELAT_1.th38.1
    exact htot.symm.trans hdomE
  exact th8 hg' hOK

/-- Unlabeled `FUNCT_2` (`L1407`) -/
theorem th84 (X Y : TarskiSet.{u}) :
    PARTFUN1.TotFuncs (PARTFUN1.empty_isPartFunc X Y) = Funcs X Y := by
  have hf0 := PARTFUN1.empty_isPartFunc X Y
  apply eq_of_mem
  intro g
  constructor
  · intro hg
    exact th83 hf0 g hg
  · intro hg
    have hg' := th66 hg
    have hOK : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}) := by
      intro hY
      obtain ⟨F, hF, heq, hd, hr⟩ := (def2 X Y g).mp hg
      have hrng : RELAT_1.rng F = (∅ : TarskiSet.{u}) :=
        (XBOOLE_0.def10 (X := RELAT_1.rng F) (Y := (∅ : TarskiSet.{u}))).mpr
          ⟨Eq.subst (motive := fun s => RELAT_1.rng F ⊆ s) hY hr, XBOOLE_1.th2⟩
      exact hd.symm.trans ((RELAT_1.th42 hF.1).mpr hrng)
    have htol : PARTFUN1.tolerates (∅ : TarskiSet.{u}) g :=
      PARTFUN1.th59 (functionOf_isFunction hg')
    exact th80 hf0 hg' hOK htol

/-- Unlabeled `FUNCT_2` (`L1438`) -/
theorem th85 {f X Y : TarskiSet.{u}} (hf : isFunctionOf f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    PARTFUN1.TotFuncs hf.1 = TARSKI.singleton f :=
  (PARTFUN1.th72 hf.1).mp (functionOf_dom_eq' hf h)

/-- Unlabeled `FUNCT_2` (`L1442`) -/
theorem th86 {f X : TarskiSet.{u}} (hf : isFunctionOf f X X) :
    PARTFUN1.TotFuncs hf.1 = TARSKI.singleton f :=
  th85 hf (fun h => h)

/-- Unlabeled `FUNCT_2` (`L1445`) -/
theorem th87 {f g X y : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f X (TARSKI.singleton y))
    (hg : isFunctionOf g X (TARSKI.singleton y)) :
    PARTFUN1.TotFuncs hf = TARSKI.singleton g := by
  apply TARSKI.extensionality
  intro h
  constructor
  · intro hh
    have hh' := th82 hf hh
    have heq : h = g := th51 hh' hg
    exact (singleton_iff g h).mpr heq
  · intro hh
    have heq : h = g := (singleton_iff g h).mp hh
    have htol : PARTFUN1.tolerates f g := PARTFUN1.th61 hf hg.1
    exact Eq.subst (motive := fun s => s ∈ PARTFUN1.TotFuncs hf) heq.symm
      (th80 hf hg (fun hY =>
        ((XBOOLE_0.empty_iff y).mp
          (hY ▸ (singleton_iff y y).mpr rfl)).elim) htol)

/-- Unlabeled `FUNCT_2` (`L1466`) -/
theorem th88 {f g X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (hg : PARTFUN1.isPartFunc g X Y) (hsub : g ⊆ f) :
    PARTFUN1.TotFuncs hf ⊆ PARTFUN1.TotFuncs hg := by
  intro h hh
  have hp := PARTFUN1.th69 hf hh
  have htt := PARTFUN1.th70 hf hp hh
  have htol_fh := PARTFUN1.th71 hf hp.1 hh
  have htol_gh : PARTFUN1.tolerates g h :=
    PARTFUN1.th58 hf hg hp.1 htol_fh hsub
  exact (PARTFUN1.def5 hg h).mpr ⟨h, hp, rfl, htt, htol_gh⟩

/-- `FUNCT_2:89` (`Th89`) -/
theorem th89 {f g X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (hg : PARTFUN1.isPartFunc g X Y)
    (hd : RELAT_1.dom g ⊆ RELAT_1.dom f)
    (hTot : PARTFUN1.TotFuncs hf ⊆ PARTFUN1.TotFuncs hg) :
    g ⊆ f := by
  have := Classical.propDecidable
    (Y = (∅ : TarskiSet.{u}) ∧ X ≠ (∅ : TarskiSet.{u}))
  by_cases hbad : Y = (∅ : TarskiSet.{u}) ∧ X ≠ (∅ : TarskiSet.{u})
  · exact Eq.subst (motive := fun s => s ⊆ f)
      (relationOf_empty_cod hg.2 hbad.1).symm (XBOOLE_1.th2)
  · have hOK : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}) := by
      intro hY; refine Classical.byContradiction fun hX => hbad ⟨hY, hX⟩
    have hv : ∀ x, x ∈ RELAT_1.dom g →
        FUNCT_1.apply g x = FUNCT_1.apply f x := by
      intro x hx
      obtain ⟨h, hhfun, htol_f⟩ := th77 hf hOK
      have hin : h ∈ PARTFUN1.TotFuncs hf := th80 hf hhfun hOK htol_f
      have htol_g : PARTFUN1.tolerates g h :=
        PARTFUN1.th71 hg (th82 hf hin).1.1 (hTot _ hin)
      have hxH : x ∈ RELAT_1.dom h :=
        Eq.subst (motive := fun s => x ∈ s)
          (functionOf_dom_eq' hhfun hOK).symm
          (RELSET_1.relationOf_defined hg.2 x hx)
      have hxI : x ∈ RELAT_1.dom g ∩ RELAT_1.dom h :=
        (XBOOLE_0.def4 (RELAT_1.dom g) (RELAT_1.dom h) x).mpr ⟨hx, hxH⟩
      have hxIf : x ∈ RELAT_1.dom f ∩ RELAT_1.dom h :=
        (XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom h) x).mpr
          ⟨hd x hx, hxH⟩
      exact (htol_g x hxI).trans (htol_f x hxIf).symm
    exact (GRFUNC_1.th2 hg.1 hf.1).mpr ⟨hd, hv⟩

/-- Helper: TotFuncs inclusion implies domain inclusion when Y is not a singleton. -/
theorem totFuncs_dom_sub {f g X Y : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f X Y) (hg : PARTFUN1.isPartFunc g X Y)
    (hTot : PARTFUN1.TotFuncs hf ⊆ PARTFUN1.TotFuncs hg)
    (hYne : Y ≠ (∅ : TarskiSet.{u}))
    (hY : ∀ y, Y ≠ TARSKI.singleton y) :
    RELAT_1.dom g ⊆ RELAT_1.dom f := by
  intro x hx
  refine Classical.byContradiction fun hxnF => ?_
  have hxX : x ∈ X := RELSET_1.relationOf_defined hg.2 x hx
  obtain ⟨y, hyY, hyne⟩ :=
    ZFMISC_1.th35 (hY (FUNCT_1.apply g x)) hYne
  obtain ⟨h, hh, hv⟩ := sch_Lambda1C X Y
    (fun z => z ∈ RELAT_1.dom f)
    (fun z => FUNCT_1.apply f z)
    (fun _ => y)
    (fun z _ => ⟨fun hzd => PARTFUN1.th4 hf.1
        (RELSET_1.relationOf_valued hf.2) hzd,
      fun _ => hyY⟩)
  have hOK : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}) :=
    fun hY' => (hYne hY').elim
  have htol_f : PARTFUN1.tolerates f h :=
    (th75 hf hh hOK).mpr fun z hz =>
      ((hv z (RELSET_1.relationOf_defined hf.2 z hz)).1 hz).symm
  have hin : h ∈ PARTFUN1.TotFuncs hf := th80 hf hh hOK htol_f
  have htol_g : PARTFUN1.tolerates g h :=
    PARTFUN1.th71 hg (functionOf_isFunction hh) (hTot _ hin)
  have hxH : x ∈ RELAT_1.dom h :=
    Eq.subst (motive := fun s => x ∈ s)
      (functionOf_dom_eq hh hYne).symm hxX
  have hxI : x ∈ RELAT_1.dom g ∩ RELAT_1.dom h :=
    (XBOOLE_0.def4 (RELAT_1.dom g) (RELAT_1.dom h) x).mpr ⟨hx, hxH⟩
  have hval : FUNCT_1.apply h x = y := (hv x hxX).2 hxnF
  exact hyne ((htol_g x hxI).trans hval).symm

/-- `FUNCT_2:90` (`Th90`) -/
theorem th90 {f g X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (hg : PARTFUN1.isPartFunc g X Y)
    (hTot : PARTFUN1.TotFuncs hf ⊆ PARTFUN1.TotFuncs hg)
    (hY : ∀ y, Y ≠ TARSKI.singleton y) :
    g ⊆ f := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hYe : Y = (∅ : TarskiSet.{u})
  · exact Eq.subst (motive := fun s => s ⊆ f)
      (relationOf_empty_cod hg.2 hYe).symm (XBOOLE_1.th2)
  · exact th89 hf hg (totFuncs_dom_sub hf hg hTot hYe hY) hTot

/-- Unlabeled `FUNCT_2` (`L1569`) -/
theorem th91 {f g X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (hg : PARTFUN1.isPartFunc g X Y)
    (hY : ∀ y, Y ≠ TARSKI.singleton y)
    (hTot : PARTFUN1.TotFuncs hf = PARTFUN1.TotFuncs hg) :
    f = g :=
  (XBOOLE_0.def10 (X := f) (Y := g)).mpr
    ⟨th90 hg hf (fun z hz =>
        Eq.subst (motive := fun s => z ∈ s) hTot.symm hz) hY,
      th90 hf hg (fun z hz =>
        Eq.subst (motive := fun s => z ∈ s) hTot hz) hY⟩

/-- Registration: Function of nonempty to nonempty is nonempty as a set. -/
theorem functionOf_ne_as_set {f A B : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f A B) :
    f ≠ (∅ : TarskiSet.{u}) := by
  have hd : RELAT_1.dom f = A := functionOf_dom_eq hf hB
  intro hempty
  have hdomE : RELAT_1.dom f = (∅ : TarskiSet.{u}) :=
    Eq.subst (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u}))
      hempty.symm RELAT_1.th38.1
  exact hA (hd.symm.trans hdomE)

/-- `FUNCT_2:sch LambdaSep1` -/
theorem sch_LambdaSep1 (D R : TarskiSet.{u})
    (hD : D ≠ (∅ : TarskiSet.{u})) (hR : R ≠ (∅ : TarskiSet.{u}))
    (A B : TarskiSet.{u}) (hA : A ∈ D) (hB : B ∈ R)
    (F : TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ x, x ∈ D → x ≠ A → F x ∈ R) :
    ∃ f, isFunctionOf f D R ∧ FUNCT_1.apply f A = B ∧
      ∀ x, x ∈ D → x ≠ A → FUNCT_1.apply f x = F x := by
  obtain ⟨f, hf, hv⟩ := sch_FuncExD D R hD hR
    (fun x y => (x = A → y = B) ∧ (x ≠ A → y = F x))
    (fun x hx => by
      have := Classical.propDecidable (x = A)
      by_cases hxA : x = A
      · exact ⟨B, hB, fun _ => rfl, fun hne => (hne hxA).elim⟩
      · exact ⟨F x, hF x hx hxA, fun heq => (hxA heq).elim, fun _ => rfl⟩)
  exact ⟨f, hf, (hv A hA).1 rfl, fun x hx hxA => (hv x hx).2 hxA⟩

/-- `FUNCT_2:sch LambdaSep2` -/
theorem sch_LambdaSep2 (D R : TarskiSet.{u})
    (hD : D ≠ (∅ : TarskiSet.{u})) (hR : R ≠ (∅ : TarskiSet.{u}))
    (A1 A2 B1 B2 : TarskiSet.{u})
    (hA1 : A1 ∈ D) (hA2 : A2 ∈ D) (hB1 : B1 ∈ R) (hB2 : B2 ∈ R)
    (hne : A1 ≠ A2)
    (F : TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ x, x ∈ D → x ≠ A1 → x ≠ A2 → F x ∈ R) :
    ∃ f, isFunctionOf f D R ∧
      FUNCT_1.apply f A1 = B1 ∧ FUNCT_1.apply f A2 = B2 ∧
      ∀ x, x ∈ D → x ≠ A1 → x ≠ A2 → FUNCT_1.apply f x = F x := by
  obtain ⟨f, hf, hv⟩ := sch_FuncExD D R hD hR
    (fun x y => (x = A1 → y = B1) ∧ (x = A2 → y = B2) ∧
      (x ≠ A1 → x ≠ A2 → y = F x))
    (fun x hx => by
      have := Classical.propDecidable (x = A1)
      have := Classical.propDecidable (x = A2)
      by_cases hx1 : x = A1
      · exact ⟨B1, hB1, fun _ => rfl,
          fun hx2 => (hne (hx1.symm.trans hx2)).elim,
          fun hne1 _ => (hne1 hx1).elim⟩
      · by_cases hx2 : x = A2
        · exact ⟨B2, hB2, fun heq => (hx1 heq).elim, fun _ => rfl,
            fun _ hne2 => (hne2 hx2).elim⟩
        · exact ⟨F x, hF x hx hx1 hx2,
            fun heq => (hx1 heq).elim, fun heq => (hx2 heq).elim,
            fun _ _ => rfl⟩)
  exact ⟨f, hf, (hv A1 hA1).1 rfl, (hv A2 hA2).2.1 rfl,
    fun x hx hx1 hx2 => (hv x hx).2.2 hx1 hx2⟩

/-- Unlabeled `FUNCT_2` (`L1635`) — membership in `Funcs`. -/
theorem th92 {A B f : TarskiSet.{u}} (hf : f ∈ Funcs A B) :
    FUNCT_1.isFunction f ∧ RELAT_1.dom f = A ∧ RELAT_1.rng f ⊆ B := by
  obtain ⟨g, hg, heq, hd, hr⟩ := (def2 A B f).mp hf
  exact ⟨Eq.subst (motive := FUNCT_1.isFunction) heq.symm hg,
    Eq.subst (motive := fun s => RELAT_1.dom s = A) heq.symm hd,
    Eq.subst (motive := fun s => RELAT_1.rng s ⊆ B) heq.symm hr⟩

/-- `FUNCT_2:sch FunctRealEx` -/
theorem sch_FunctRealEx (X Y : TarskiSet.{u})
    (hX : X ≠ (∅ : TarskiSet.{u})) (_hY : Y ≠ (∅ : TarskiSet.{u}))
    (F : TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ x, x ∈ X → F x ∈ Y) :
    ∃ f, isFunctionOf f X Y ∧
      ∀ x, x ∈ X → FUNCT_1.apply f x = F x :=
  sch_Lambda1 X Y F hF

/-- `FUNCT_2:sch KappaMD` -/
theorem sch_KappaMD (X Y : TarskiSet.{u})
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (F : TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ x, x ∈ X → F x ∈ Y) :
    ∃ f, isFunctionOf f X Y ∧
      ∀ x, x ∈ X → FUNCT_1.apply f x = F x :=
  sch_FunctRealEx X Y hX hY F hF

/-- `FUNCT_2:def 5` — `pr1` of a product-valued Function of. -/
theorem def5 {A B C f : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hC : C ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f A (ZFMISC_1.product B C)) :
    isFunctionOf (MCART_1.pr1 f) A B ∧
      ∀ x, x ∈ A →
        FUNCT_1.apply (MCART_1.pr1 f) x =
          XTUPLE_0.fst (FUNCT_1.apply f x) := by
  have hprodNe : ZFMISC_1.product B C ≠ (∅ : TarskiSet.{u}) := by
    intro hempty
    exact ((ZFMISC_1.th90 (X := B) (Y := C)).mp hempty).elim hB hC
  have hdF : RELAT_1.dom f = A := functionOf_dom_eq hf hprodNe
  have hpr := MCART_1.pr1_spec f
  have hd : RELAT_1.dom (MCART_1.pr1 f) = A := hpr.2.1.trans hdF
  have hr : RELAT_1.rng (MCART_1.pr1 f) ⊆ B := by
    intro z hz
    obtain ⟨y, hy, heq⟩ := (FUNCT_1.def3 hpr.1.2).mp hz
    have hyA : y ∈ A := Eq.subst (motive := fun s => y ∈ s) hd hy
    have hval : FUNCT_1.apply (MCART_1.pr1 f) y =
        XTUPLE_0.fst (FUNCT_1.apply f y) :=
      hpr.2.2 y (Eq.subst (motive := fun s => y ∈ s) hdF.symm hyA)
    have hfy : FUNCT_1.apply f y ∈ ZFMISC_1.product B C :=
      th5 hf hprodNe hyA
    have hfst : XTUPLE_0.fst (FUNCT_1.apply f y) ∈ B :=
      (MCART_1.th10 hfy).1
    exact Eq.subst (motive := fun s => s ∈ B) (heq.trans hval).symm hfst
  exact ⟨functionOf_of hpr.1 hd hr,
    fun x hx => hpr.2.2 x (Eq.subst (motive := fun s => x ∈ s) hdF.symm hx)⟩

/-- `FUNCT_2:def 6` — `pr2` of a product-valued Function of. -/
theorem def6 {A B C f : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hC : C ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f A (ZFMISC_1.product B C)) :
    isFunctionOf (MCART_1.pr2 f) A C ∧
      ∀ x, x ∈ A →
        FUNCT_1.apply (MCART_1.pr2 f) x =
          XTUPLE_0.snd (FUNCT_1.apply f x) := by
  have hprodNe : ZFMISC_1.product B C ≠ (∅ : TarskiSet.{u}) := by
    intro hempty
    exact ((ZFMISC_1.th90 (X := B) (Y := C)).mp hempty).elim hB hC
  have hdF : RELAT_1.dom f = A := functionOf_dom_eq hf hprodNe
  have hpr := MCART_1.pr2_spec f
  have hd : RELAT_1.dom (MCART_1.pr2 f) = A := hpr.2.1.trans hdF
  have hr : RELAT_1.rng (MCART_1.pr2 f) ⊆ C := by
    intro z hz
    obtain ⟨y, hy, heq⟩ := (FUNCT_1.def3 hpr.1.2).mp hz
    have hyA : y ∈ A := Eq.subst (motive := fun s => y ∈ s) hd hy
    have hval : FUNCT_1.apply (MCART_1.pr2 f) y =
        XTUPLE_0.snd (FUNCT_1.apply f y) :=
      hpr.2.2 y (Eq.subst (motive := fun s => y ∈ s) hdF.symm hyA)
    have hfy : FUNCT_1.apply f y ∈ ZFMISC_1.product B C :=
      th5 hf hprodNe hyA
    have hsnd : XTUPLE_0.snd (FUNCT_1.apply f y) ∈ C :=
      (MCART_1.th10 hfy).2
    exact Eq.subst (motive := fun s => s ∈ C) (heq.trans hval).symm hsnd
  exact ⟨functionOf_of hpr.1 hd hr,
    fun x hx => hpr.2.2 x (Eq.subst (motive := fun s => x ∈ s) hdF.symm hx)⟩

/-- Equality of Functions of nonempty codomains by shared domain and values. -/
theorem functionOf_eq_of_dom_vals {A1 A2 B1 B2 f1 f2 : TarskiSet.{u}}
    (hB1 : B1 ≠ (∅ : TarskiSet.{u})) (hB2 : B2 ≠ (∅ : TarskiSet.{u}))
    (hf1 : isFunctionOf f1 A1 B1) (hf2 : isFunctionOf f2 A2 B2)
    (hA : A1 = A2)
    (hv : ∀ a, a ∈ A1 → FUNCT_1.apply f1 a = FUNCT_1.apply f2 a) :
    f1 = f2 := by
  have hd1 : RELAT_1.dom f1 = A1 := functionOf_dom_eq hf1 hB1
  have hd2 : RELAT_1.dom f2 = A2 := functionOf_dom_eq hf2 hB2
  exact FUNCT_1.th2 (functionOf_isFunction hf1) (functionOf_isFunction hf2)
    (hd1.trans (hA.trans hd2.symm)) fun a ha =>
      hv a (Eq.subst (motive := fun s => a ∈ s) hd1 ha)

/-- Unlabeled `FUNCT_2` (`L1781`) — relation with prescribed images. -/
theorem th93 {N f : TarskiSet.{u}}
    (hf : isFunctionOf f N (ZFMISC_1.bool N)) :
    ∃ R, RELSET_1.isRelationOf R N N ∧
      ∀ i, i ∈ N → RELAT_1.Im R i = FUNCT_1.apply f i := by
  have hboolNe : ZFMISC_1.bool N ≠ (∅ : TarskiSet.{u}) :=
    fun hempty =>
      (XBOOLE_0.empty_iff (∅ : TarskiSet.{u})).mp
        (Eq.subst (motive := fun s => (∅ : TarskiSet.{u}) ∈ s) hempty
          ((ZFMISC_1.def1 N (∅ : TarskiSet.{u})).mpr XBOOLE_1.th2))
  have hF : ∀ i, i ∈ N → i ∈ N → FUNCT_1.apply f i ⊆ N := by
    intro i hi _
    have hfi : FUNCT_1.apply f i ∈ ZFMISC_1.bool N := th5 hf hboolNe hi
    exact (ZFMISC_1.def1 N (FUNCT_1.apply f i)).mp hfi
  obtain ⟨R, hR, hIm⟩ := RELSET_1.sch_ImEx N N (fun _ h => h)
    (fun i => FUNCT_1.apply f i) hF
  exact ⟨R, hR, fun i hi => hIm i hi hi⟩

/-- `id X` is a permutation of `X`. -/
theorem id_isPermutation (X : TarskiSet.{u}) :
    isPermutation (RELAT_1.id X) X := by
  have hf : isFunctionOf (RELAT_1.id X) X X :=
    functionOf_of (FUNCT_1.id_isFunction X) (RELAT_1.id_dom X)
      (Eq.subst (motive := fun s => s ⊆ X) (RELAT_1.id_rng X).symm
        (fun _ h => h))
  have h1 : FUNCT_1.isOneToOne (RELAT_1.id X) :=
    FUNCT_1.id_isOneToOne X
  have hr : RELAT_1.rng (RELAT_1.id X) = X := RELAT_1.id_rng X
  exact th57 hf h1 hr

/-- `FUNCT_2:94` (`Th94`) -/
theorem th94 {X A : TarskiSet.{u}} (hA : A ⊆ X) :
    RELAT_1.invimage (RELAT_1.id X) A = A := by
  have hperm := id_isPermutation X
  have himg : RELAT_1.image (RELAT_1.id X) A = A := FUNCT_1.th92 hA
  have h := (th62 hperm hA).2
  exact Eq.subst (motive := fun s => RELAT_1.invimage (RELAT_1.id X) s = A)
    himg h

/-- Unlabeled `FUNCT_2` (`L1816`) — image/preimage Galois. -/
theorem th95 {A B f A0 B0 : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f A B) (hA0 : A0 ⊆ A) (_hB0 : B0 ⊆ B) :
    RELAT_1.image f A0 ⊆ B0 ↔ A0 ⊆ RELAT_1.invimage f B0 := by
  constructor
  · intro himg
    exact XBOOLE_1.th1 (th42 hf (fun h => (hB h).elim) hA0)
      (RELAT_1.th143 himg)
  · intro hpre
    exact XBOOLE_1.th1 (RELAT_1.th123 hpre)
      (FUNCT_1.th75 (functionOf_isFunction hf).2 (Y := B0))

/-- Unlabeled `FUNCT_2` (`L1839`) — restriction equals agreeing Function of. -/
theorem th96 {A B A0 f f0 : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hA0 : A0 ≠ (∅ : TarskiSet.{u})) (hA0sub : A0 ⊆ A)
    (hf : isFunctionOf f A B) (hf0 : isFunctionOf f0 A0 B)
    (hv : ∀ c, c ∈ A → c ∈ A0 → FUNCT_1.apply f c = FUNCT_1.apply f0 c) :
    RELAT_1.restrict f A0 = f0 := by
  have hg : isFunctionOf (RELAT_1.restrict f A0) A0 B :=
    th32 hf (fun h => (hB h).elim) hA0sub
  exact th63 hg hf0 fun c hc => by
    have hcA : c ∈ A := hA0sub c hc
    have hval : FUNCT_1.apply (RELAT_1.restrict f A0) c = FUNCT_1.apply f c :=
      FUNCT_1.th49 (functionOf_isFunction hf).2 hc
    exact hval.trans (hv c hcA hc)

/-- Unlabeled `FUNCT_2` (`L1857`) -/
theorem th97 {f A0 C : TarskiSet.{u}} (hC : C ⊆ A0) :
    RELAT_1.image f C = RELAT_1.image (RELAT_1.restrict f A0) C := by
  have h1 : RELAT_1.image (RELAT_1.restrict f A0) C =
      RELAT_1.image (RELAT_1.comp (RELAT_1.id A0) f) C :=
    congrArg (fun s => RELAT_1.image s C) (RELAT_1.th65 (R := f) (X := A0))
  have h2 : RELAT_1.image (RELAT_1.comp (RELAT_1.id A0) f) C =
      RELAT_1.image f (RELAT_1.image (RELAT_1.id A0) C) :=
    RELAT_1.th126 (P := RELAT_1.id A0) (R := f) (X := C)
  have h3 : RELAT_1.image (RELAT_1.id A0) C = C := FUNCT_1.th92 hC
  exact Eq.symm ((h1.trans h2).trans (congrArg (RELAT_1.image f) h3))

/-- Unlabeled `FUNCT_2` (`L1868`) -/
theorem th98 {f A0 D : TarskiSet.{u}}
    (h : RELAT_1.invimage f D ⊆ A0) :
    RELAT_1.invimage f D = RELAT_1.invimage (RELAT_1.restrict f A0) D := by
  have h1 : RELAT_1.invimage (RELAT_1.restrict f A0) D =
      RELAT_1.invimage (RELAT_1.comp (RELAT_1.id A0) f) D :=
    congrArg (fun s => RELAT_1.invimage s D) (RELAT_1.th65 (R := f) (X := A0))
  have h2 : RELAT_1.invimage (RELAT_1.comp (RELAT_1.id A0) f) D =
      RELAT_1.invimage (RELAT_1.id A0) (RELAT_1.invimage f D) :=
    RELAT_1.th146 (P := RELAT_1.id A0) (R := f) (Y := D)
  have h3 : RELAT_1.invimage (RELAT_1.id A0) (RELAT_1.invimage f D) =
      RELAT_1.invimage f D :=
    th94 h
  exact Eq.symm ((h1.trans h2).trans h3)

/-- `FUNCT_2:sch MChoice` -/
theorem sch_MChoice (A B : TarskiSet.{u})
    (_hA : A ≠ (∅ : TarskiSet.{u})) (_hB : B ≠ (∅ : TarskiSet.{u}))
    (F : TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ a, a ∈ A → XBOOLE_0.meets B (F a)) :
    ∃ t, isFunctionOf t A B ∧
      ∀ a, a ∈ A → FUNCT_1.apply t a ∈ F a := by
  obtain ⟨t, ht, hd, hr, hv⟩ := FUNCT_1.sch_NonUniqBoundFuncEx A B
    (fun e u => u ∈ F e)
    (fun e he => by
      obtain ⟨u, huB, huF⟩ := (XBOOLE_0.th3 B (F e)).mp (hF e he)
      exact ⟨u, huB, huF⟩)
  exact ⟨t, functionOf_of ht hd hr, hv⟩

/-- `FUNCT_2:99` (`Th99`) — `p/.i = p.i` for Function of. -/
theorem th99 {X D p i : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hD : D ≠ (∅ : TarskiSet.{u}))
    (hp : isFunctionOf p X D) (hi : i ∈ X) :
    PARTFUN1.apply_at p i = FUNCT_1.apply p i :=
  PARTFUN1.def6 (functionOf_isFunction hp)
    (RELSET_1.relationOf_valued hp.1.2)
    (Eq.subst (motive := fun s => i ∈ s) (functionOf_dom_eq hp hD).symm hi)

/-- Unlabeled `FUNCT_2` (`L1917`) — preimage of complement. -/
theorem th100 {S X f A : TarskiSet.{u}}
    (hf : isFunctionOf f S X) (hA : A ⊆ X)
    (hSX : X = (∅ : TarskiSet.{u}) → S = (∅ : TarskiSet.{u})) :
    SUBSET_1.compl S (RELAT_1.invimage f A) =
      RELAT_1.invimage f (SUBSET_1.compl X A) := by
  have hfLike := (functionOf_isFunction hf).2
  have hinter : A ∩ SUBSET_1.compl X A = (∅ : TarskiSet.{u}) := by
    apply (XBOOLE_0.def10 (X := A ∩ SUBSET_1.compl X A)
      (Y := (∅ : TarskiSet.{u}))).mpr
    constructor
    · intro z hz
      have ⟨hzA, hzC⟩ := (XBOOLE_0.def4 A (SUBSET_1.compl X A) z).mp hz
      exact (((XBOOLE_0.def5 X A z).mp hzC).2 hzA).elim
    · exact XBOOLE_1.th2
  have hmiss : XBOOLE_0.misses (RELAT_1.invimage f A)
      (RELAT_1.invimage f (SUBSET_1.compl X A)) := by
    have heq : RELAT_1.invimage f A ∩
        RELAT_1.invimage f (SUBSET_1.compl X A) =
          RELAT_1.invimage f (A ∩ SUBSET_1.compl X A) :=
      (FUNCT_1.th68 hfLike (Y1 := A) (Y2 := SUBSET_1.compl X A)).symm
    have hempty : RELAT_1.invimage f (A ∩ SUBSET_1.compl X A) =
        RELAT_1.invimage f (∅ : TarskiSet.{u}) :=
      congrArg (RELAT_1.invimage f) hinter
    have hemptyInv : RELAT_1.invimage f (∅ : TarskiSet.{u}) =
        (∅ : TarskiSet.{u}) := by
      apply (XBOOLE_0.def10).mpr
      constructor
      · intro x hx
        exact ((XBOOLE_0.empty_iff _).mp
          ((FUNCT_1.def7 hfLike).mp hx).2).elim
      · exact XBOOLE_1.th2
    exact (XBOOLE_0.def7 _ _).mpr (heq.trans (hempty.trans hemptyInv))
  have hAU : A ∪ SUBSET_1.compl X A = X :=
    SUBSET_1.th10 hA
  have hInvUnion : RELAT_1.invimage f A ∪
      RELAT_1.invimage f (SUBSET_1.compl X A) = S := by
    have h1 : RELAT_1.invimage f A ∪
        RELAT_1.invimage f (SUBSET_1.compl X A) =
          RELAT_1.invimage f (A ∪ SUBSET_1.compl X A) :=
      (RELAT_1.th140 (R := f) (X := A) (Y := SUBSET_1.compl X A)).symm
    exact (h1.trans (congrArg (RELAT_1.invimage f) hAU)).trans (th40 hf hSX)
  have hAsub : RELAT_1.invimage f A ⊆ S := th39 hf.1
  have hBsub : RELAT_1.invimage f (SUBSET_1.compl X A) ⊆ S := th39 hf.1
  have hmiss' : XBOOLE_0.misses
      (SUBSET_1.compl S (RELAT_1.invimage f A))
      (SUBSET_1.compl S (RELAT_1.invimage f (SUBSET_1.compl X A))) := by
    have hcap : SUBSET_1.compl S (RELAT_1.invimage f A) ∩
        SUBSET_1.compl S (RELAT_1.invimage f (SUBSET_1.compl X A)) =
          SUBSET_1.compl S
            (RELAT_1.invimage f A ∪
              RELAT_1.invimage f (SUBSET_1.compl X A)) :=
      (XBOOLE_1.th53 (X := S) (Y := RELAT_1.invimage f A)
        (Z := RELAT_1.invimage f (SUBSET_1.compl X A))).symm
    have hempty : SUBSET_1.compl S
        (RELAT_1.invimage f A ∪
          RELAT_1.invimage f (SUBSET_1.compl X A)) =
        (∅ : TarskiSet.{u}) := by
      have hU : RELAT_1.invimage f A ∪
          RELAT_1.invimage f (SUBSET_1.compl X A) = S := hInvUnion
      apply (XBOOLE_0.def10).mpr
      constructor
      · intro z hz
        have ⟨hzS, hzn⟩ := (XBOOLE_0.def5 S _ z).mp hz
        exact (hzn (Eq.subst (motive := fun s => z ∈ s) hU.symm hzS)).elim
      · exact XBOOLE_1.th2
    exact (XBOOLE_0.def7 _ _).mpr (hcap.trans hempty)
  have heq : RELAT_1.invimage f A =
      SUBSET_1.compl S (RELAT_1.invimage f (SUBSET_1.compl X A)) :=
    SUBSET_1.th25 hAsub hBsub hmiss hmiss'
  have hinvol : SUBSET_1.compl S
      (SUBSET_1.compl S (RELAT_1.invimage f (SUBSET_1.compl X A))) =
      RELAT_1.invimage f (SUBSET_1.compl X A) :=
    SUBSET_1.compl_involutive hBsub
  exact Eq.subst (motive := fun s => SUBSET_1.compl S s =
      RELAT_1.invimage f (SUBSET_1.compl X A)) heq.symm hinvol

/-- Unlabeled `FUNCT_2` (`L1940`) — restriction with image in `Z`. -/
theorem th101 {X Y Z D f : TarskiSet.{u}}
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f X D) (hY : Y ⊆ X)
    (himg : RELAT_1.image f Y ⊆ Z) :
    isFunctionOf (RELAT_1.restrict f Y) Y Z := by
  have hdF : RELAT_1.dom f = X := functionOf_dom_eq hf hD
  have hd : RELAT_1.dom (RELAT_1.restrict f Y) = Y :=
    RELAT_1.th62 (Eq.subst (motive := fun s => Y ⊆ s) hdF.symm hY)
  have hrng : RELAT_1.rng (RELAT_1.restrict f Y) ⊆ Z :=
    Eq.subst (motive := fun s => s ⊆ Z) (RELAT_1.th115 (R := f) (X := Y)).symm
      himg
  exact functionOf_of
    (FUNCT_1.restrict_isFunction (functionOf_isFunction hf)) hd hrng

/-! ## Subset-family image/preimage (`FUNCT_2:def 9`, `def 10`) -/

/-- `FUNCT_2:def 9` — `f"G` for a Subset-Family. -/
noncomputable def invimageFamily (T f G : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (XBOOLE_0.sch_separation (ZFMISC_1.bool T)
      (fun A => ∃ B, B ∈ G ∧ A = RELAT_1.invimage f B))

theorem def9 (T f G A : TarskiSet.{u}) :
    A ∈ invimageFamily T f G ↔
      A ∈ ZFMISC_1.bool T ∧
        ∃ B, B ∈ G ∧ A = RELAT_1.invimage f B :=
  Classical.choose_spec
    (XBOOLE_0.sch_separation (ZFMISC_1.bool T)
      (fun A => ∃ B, B ∈ G ∧ A = RELAT_1.invimage f B)) A

theorem invimageFamily_isSubsetFamily (T f G : TarskiSet.{u}) :
    SETFAM_1.isSubsetFamily (invimageFamily T f G) T :=
  fun A hA => ((def9 T f G A).mp hA).1

/-- Unlabeled `FUNCT_2` (`L2005`) -/
theorem th102 {T S f A B : TarskiSet.{u}}
    (_hT : T ≠ (∅ : TarskiSet.{u})) (_hS : S ≠ (∅ : TarskiSet.{u}))
    (_hf : isFunctionOf f T S) (hAB : A ⊆ B) :
    invimageFamily T f A ⊆ invimageFamily T f B := by
  intro x hx
  have ⟨hxBool, C, hC, heq⟩ := (def9 T f A x).mp hx
  exact (def9 T f B x).mpr ⟨hxBool, C, hAB C hC, heq⟩

/-- `FUNCT_2:def 10` — `f.:G` for a Subset-Family. -/
noncomputable def imageFamily (S f G : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (XBOOLE_0.sch_separation (ZFMISC_1.bool S)
      (fun A => ∃ B, B ∈ G ∧ A = RELAT_1.image f B))

theorem def10 (S f G A : TarskiSet.{u}) :
    A ∈ imageFamily S f G ↔
      A ∈ ZFMISC_1.bool S ∧
        ∃ B, B ∈ G ∧ A = RELAT_1.image f B :=
  Classical.choose_spec
    (XBOOLE_0.sch_separation (ZFMISC_1.bool S)
      (fun A => ∃ B, B ∈ G ∧ A = RELAT_1.image f B)) A

theorem imageFamily_isSubsetFamily (S f G : TarskiSet.{u}) :
    SETFAM_1.isSubsetFamily (imageFamily S f G) S :=
  fun A hA => ((def10 S f G A).mp hA).1

/-- Unlabeled `FUNCT_2` (`L2076`) -/
theorem th103 {T S f A B : TarskiSet.{u}}
    (_hT : T ≠ (∅ : TarskiSet.{u})) (_hS : S ≠ (∅ : TarskiSet.{u}))
    (_hf : isFunctionOf f T S) (hAB : A ⊆ B) :
    imageFamily S f A ⊆ imageFamily S f B := by
  intro x hx
  have ⟨hxBool, C, hC, heq⟩ := (def10 S f A x).mp hx
  exact (def10 S f B x).mpr ⟨hxBool, C, hAB C hC, heq⟩

/-- Unlabeled `FUNCT_2` (`L2099`) -/
theorem th104 {T S f B P : TarskiSet.{u}}
    (_hT : T ≠ (∅ : TarskiSet.{u})) (_hS : S ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f T S)
    (_hB : SETFAM_1.isSubsetFamily B S) (_hP : P ⊆ S)
    (hcov : SETFAM_1.isCover (imageFamily S f (invimageFamily T f B)) P) :
    SETFAM_1.isCover B P := by
  intro x hxP
  have ⟨Y, hxY, hY⟩ := (TARSKI.def4 _ x).mp (hcov x hxP)
  have ⟨_, Y1, hY1, heqY⟩ := (def10 S f (invimageFamily T f B) Y).mp hY
  have ⟨_, Y2, hY2, heqY1⟩ := (def9 T f B Y1).mp hY1
  have himg : RELAT_1.image f (RELAT_1.invimage f Y2) ⊆ Y2 :=
    FUNCT_1.th75 (functionOf_isFunction hf).2 (Y := Y2)
  have hxY2 : x ∈ Y2 :=
    himg x (Eq.subst (motive := fun s => x ∈ s)
      (heqY.trans (congrArg (RELAT_1.image f) heqY1)) hxY)
  exact (TARSKI.def4 B x).mpr ⟨Y2, hxY2, hY2⟩

/-- Unlabeled `FUNCT_2` (`L2136`) -/
theorem th105 {T S f B P : TarskiSet.{u}}
    (_hT : T ≠ (∅ : TarskiSet.{u})) (hS : S ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f T S)
    (hB : SETFAM_1.isSubsetFamily B T) (_hP : P ⊆ T)
    (hcov : SETFAM_1.isCover B P) :
    SETFAM_1.isCover (invimageFamily T f (imageFamily S f B)) P := by
  intro x hxP
  have ⟨Y, hxY, hY⟩ := (TARSKI.def4 B x).mp (hcov x hxP)
  have hYsub : Y ⊆ T := (ZFMISC_1.def1 T Y).mp (hB Y hY)
  have hd : RELAT_1.dom f = T := functionOf_dom_eq hf hS
  have hsub : Y ⊆ RELAT_1.invimage f (RELAT_1.image f Y) :=
    FUNCT_1.th76 (R := f) (X := Y)
      (Eq.subst (motive := fun s => Y ⊆ s) hd.symm hYsub)
  have himgSub : RELAT_1.image f Y ⊆ S :=
    XBOOLE_1.th1 (RELAT_1.th111 (R := f) (X := Y)) (functionOf_rng_sub hf)
  have hImgIn : RELAT_1.image f Y ∈ imageFamily S f B :=
    (def10 S f B (RELAT_1.image f Y)).mpr
      ⟨(ZFMISC_1.def1 S _).mpr himgSub, Y, hY, rfl⟩
  have hInvIn : RELAT_1.invimage f (RELAT_1.image f Y) ∈
      invimageFamily T f (imageFamily S f B) :=
    (def9 T f (imageFamily S f B) _).mpr
      ⟨(ZFMISC_1.def1 T _).mpr (th39 hf.1), RELAT_1.image f Y, hImgIn, rfl⟩
  exact (TARSKI.def4 _ x).mpr
    ⟨RELAT_1.invimage f (RELAT_1.image f Y), hsub x hxY, hInvIn⟩

/-- Unlabeled `FUNCT_2` (`L2171`) -/
theorem th106 {T S f Q : TarskiSet.{u}}
    (_hT : T ≠ (∅ : TarskiSet.{u})) (_hS : S ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f T S) (_hQ : SETFAM_1.isSubsetFamily Q S) :
    union (imageFamily S f (invimageFamily T f Q)) ⊆ union Q := by
  intro x hx
  obtain ⟨A, hxA, hA⟩ := (TARSKI.def4 _ x).mp hx
  have ⟨_, A1, hA1, heqA⟩ := (def10 S f (invimageFamily T f Q) A).mp hA
  have ⟨_, A2, hA2, heqA1⟩ := (def9 T f Q A1).mp hA1
  have himg : RELAT_1.image f (RELAT_1.invimage f A2) ⊆ A2 :=
    FUNCT_1.th75 (functionOf_isFunction hf).2 (Y := A2)
  exact (TARSKI.def4 Q x).mpr ⟨A2,
    himg x (Eq.subst (motive := fun s => x ∈ s)
      (heqA.trans (congrArg (RELAT_1.image f) heqA1)) hxA), hA2⟩

/-- Unlabeled `FUNCT_2` (`L2196`) -/
theorem th107 {T S f P : TarskiSet.{u}}
    (_hT : T ≠ (∅ : TarskiSet.{u})) (hS : S ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f T S) (hP : SETFAM_1.isSubsetFamily P T) :
    union P ⊆ union (invimageFamily T f (imageFamily S f P)) := by
  intro x hx
  obtain ⟨A, hxA, hA⟩ := (TARSKI.def4 P x).mp hx
  have hAsub : A ⊆ T := (ZFMISC_1.def1 T A).mp (hP A hA)
  have hd : RELAT_1.dom f = T := functionOf_dom_eq hf hS
  have hsub : A ⊆ RELAT_1.invimage f (RELAT_1.image f A) :=
    FUNCT_1.th76 (R := f) (X := A)
      (Eq.subst (motive := fun s => A ⊆ s) hd.symm hAsub)
  have himgSub : RELAT_1.image f A ⊆ S :=
    XBOOLE_1.th1 (RELAT_1.th111 (R := f) (X := A)) (functionOf_rng_sub hf)
  have hImgIn : RELAT_1.image f A ∈ imageFamily S f P :=
    (def10 S f P _).mpr
      ⟨(ZFMISC_1.def1 S _).mpr himgSub, A, hA, rfl⟩
  have hInvIn : RELAT_1.invimage f (RELAT_1.image f A) ∈
      invimageFamily T f (imageFamily S f P) :=
    (def9 T f (imageFamily S f P) _).mpr
      ⟨(ZFMISC_1.def1 T _).mpr (th39 hf.1), RELAT_1.image f A, hImgIn, rfl⟩
  exact (TARSKI.def4 _ x).mpr ⟨_, hsub x hxA, hInvIn⟩

/-! ## Composition along (`FUNCT_2:def 11`) -/

/-- `FUNCT_2:def 11` — Mizar `p/*f` is Lean `comp f p`. -/
noncomputable def composeAlong (p f : TarskiSet.{u}) : TarskiSet.{u} :=
  RELAT_1.comp f p

theorem def11 {X Y Z f p : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f X Y) (hp : FUNCT_1.isFunction p)
    (hv : RELAT_1.isXvalued p Z)
    (hr : RELAT_1.rng f ⊆ RELAT_1.dom p) :
    isFunctionOf (composeAlong p f) X Z := by
  have hdF : RELAT_1.dom f = X := functionOf_dom_eq hf hY
  have hd : RELAT_1.dom (RELAT_1.comp f p) = X :=
    (RELAT_1.th27 hr).trans hdF
  have hrng : RELAT_1.rng (RELAT_1.comp f p) ⊆ Z :=
    XBOOLE_1.th1 (RELAT_1.th26 (P := f) (R := p)) hv
  exact functionOf_of (FUNCT_1.comp_isFunction
      (functionOf_isFunction hf) hp) hd hrng

/-- `FUNCT_2:108` (`Th108`) -/
theorem th108 {X Y Z f p x : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f X Y) (hp : FUNCT_1.isFunction p)
    (_hv : RELAT_1.isXvalued p Z)
    (_hr : RELAT_1.rng f ⊆ RELAT_1.dom p) (hx : x ∈ X) :
    FUNCT_1.apply (composeAlong p f) x =
      FUNCT_1.apply p (FUNCT_1.apply f x) :=
  th15 hf hp hY hx

/-- `FUNCT_2:109` (`Th109`) -/
theorem th109 {X Y Z f p x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f X Y) (hp : FUNCT_1.isFunction p)
    (hv : RELAT_1.isXvalued p Z)
    (hr : RELAT_1.rng f ⊆ RELAT_1.dom p) (hx : x ∈ X) :
    FUNCT_1.apply (composeAlong p f) x =
      PARTFUN1.apply_at p (FUNCT_1.apply f x) := by
  have hfx : FUNCT_1.apply f x ∈ RELAT_1.rng f := th4 hf hY hx
  have hdom : FUNCT_1.apply f x ∈ RELAT_1.dom p := hr _ hfx
  exact (th108 hX hY hf hp hv hr hx).trans
    (PARTFUN1.def6 hp hv hdom).symm

/-- Unlabeled `FUNCT_2` (`L2271`) -/
theorem th110 {X Y Z f g p : TarskiSet.{u}}
    (_hY : Y ≠ (∅ : TarskiSet.{u}))
    (_hf : isFunctionOf f X Y) (_hg : isFunctionOf g X X)
    (_hp : FUNCT_1.isFunction p) (_hv : RELAT_1.isXvalued p Z)
    (hr : RELAT_1.rng f ⊆ RELAT_1.dom p) :
    RELAT_1.comp g (composeAlong p f) =
      composeAlong p (RELAT_1.comp g f) := by
  have _hrng : RELAT_1.rng (RELAT_1.comp g f) ⊆ RELAT_1.dom p :=
    XBOOLE_1.th1 (RELAT_1.th26 (P := g) (R := f)) hr
  exact (RELAT_1.th36 (P := g) (R := f) (Q := p)).symm

/-- Unlabeled `FUNCT_2` (`L2286`) -/
theorem th111 {X Y f : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f X Y) :
    FUNCT_1.isConstant f ↔
      ∃ y, y ∈ Y ∧ RELAT_1.rng f = TARSKI.singleton y := by
  constructor
  · intro hc
    obtain ⟨x, hx⟩ := XBOOLE_0.th7 hX
    have hd : RELAT_1.dom f = X := functionOf_dom_eq hf hY
    have hxD : x ∈ RELAT_1.dom f :=
      Eq.subst (motive := fun s => x ∈ s) hd.symm hx
    refine ⟨FUNCT_1.apply f x, th5 hf hY hx, ?_⟩
    apply eq_of_mem
    intro y9
    constructor
    · intro hy9
      obtain ⟨x9, hx9, heq⟩ := (FUNCT_1.def3 (functionOf_isFunction hf).2).mp hy9
      have heq' : y9 = FUNCT_1.apply f x :=
        heq.trans (hc x9 x hx9 hxD)
      exact (singleton_iff (FUNCT_1.apply f x) y9).mpr heq'
    · intro hy9
      have heq : y9 = FUNCT_1.apply f x :=
        (singleton_iff (FUNCT_1.apply f x) y9).mp hy9
      exact Eq.subst (motive := fun s => s ∈ RELAT_1.rng f) heq.symm
        (th4 hf hY hx)
  · intro ⟨y, _, hrng⟩
    intro x1 x2 hx1 hx2
    have h1 : FUNCT_1.apply f x1 ∈ RELAT_1.rng f :=
      FUNCT_1.th3 (functionOf_isFunction hf).2 hx1
    have h2 : FUNCT_1.apply f x2 ∈ RELAT_1.rng f :=
      FUNCT_1.th3 (functionOf_isFunction hf).2 hx2
    have e1 : FUNCT_1.apply f x1 = y :=
      (singleton_iff y (FUNCT_1.apply f x1)).mp (hrng ▸ h1)
    have e2 : FUNCT_1.apply f x2 = y :=
      (singleton_iff y (FUNCT_1.apply f x2)).mp (hrng ▸ h2)
    exact e1.trans e2.symm

/-- Unlabeled `FUNCT_2` (`L2328`) -/
theorem th112 {A B x f : TarskiSet.{u}}
    (_hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f A B) (hx : x ∈ A) :
    FUNCT_1.apply f x ∈ RELAT_1.rng f :=
  th4 hf hB hx

/-- `FUNCT_2:113` (`Th113`) -/
theorem th113 {A B f y : TarskiSet.{u}} (hf : isFunctionOf f A B)
    (hy : y ∈ RELAT_1.rng f) :
    ∃ x, x ∈ A ∧ y = FUNCT_1.apply f x := by
  obtain ⟨x, hx, heq⟩ := th11 hf hy
  exact ⟨x, hx, heq.symm⟩

/-- Unlabeled `FUNCT_2` (`L2355`) -/
theorem th114 {A B Z f : TarskiSet.{u}}
    (_hA : A ≠ (∅ : TarskiSet.{u})) (_hB : B ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f A B)
    (h : ∀ x, x ∈ A → FUNCT_1.apply f x ∈ Z) :
    RELAT_1.rng f ⊆ Z := by
  intro y hy
  obtain ⟨x, hx, heq⟩ := th113 hf hy
  exact Eq.subst (motive := fun s => s ∈ Z) heq.symm (h x hx)

/-- Unlabeled `FUNCT_2` (`L2373`) -/
theorem th115 {X Y Z f g x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f X Y) (hg : PARTFUN1.isPartFunc g Y Z)
    (ht : PARTFUN1.isTotal g Y) (hx : x ∈ X) :
    FUNCT_1.apply (composeAlong g f) x =
      FUNCT_1.apply g (FUNCT_1.apply f x) := by
  have hr : RELAT_1.rng f ⊆ RELAT_1.dom g :=
    Eq.subst (motive := fun s => RELAT_1.rng f ⊆ s) ht.symm
      (functionOf_rng_sub hf)
  exact th108 hX hY hf hg.1 (RELSET_1.relationOf_valued hg.2) hr hx

/-- Unlabeled `FUNCT_2` (`L2382`) -/
theorem th116 {X Y Z f g x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f X Y) (hg : PARTFUN1.isPartFunc g Y Z)
    (ht : PARTFUN1.isTotal g Y) (hx : x ∈ X) :
    FUNCT_1.apply (composeAlong g f) x =
      PARTFUN1.apply_at g (FUNCT_1.apply f x) := by
  have hr : RELAT_1.rng f ⊆ RELAT_1.dom g :=
    Eq.subst (motive := fun s => RELAT_1.rng f ⊆ s) ht.symm
      (functionOf_rng_sub hf)
  exact th109 hX hY hf hg.1 (RELSET_1.relationOf_valued hg.2) hr hx

/-- `FUNCT_2:117` (`Th117`) -/
theorem th117 {X Y Z S f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f X Y) (hg : PARTFUN1.isPartFunc g Y Z)
    (hr : RELAT_1.rng f ⊆ RELAT_1.dom (RELAT_1.restrict g S)) :
    composeAlong (RELAT_1.restrict g S) f = composeAlong g f := by
  have hdomSub : RELAT_1.dom (RELAT_1.restrict g S) ⊆ RELAT_1.dom g :=
    RELAT_1.th60 (R := g) (X := S)
  have hr' : RELAT_1.rng f ⊆ RELAT_1.dom g :=
    XBOOLE_1.th1 hr hdomSub
  have hvs : RELAT_1.isXvalued (RELAT_1.restrict g S) Z :=
    XBOOLE_1.th1 (RELAT_1.th70 (R := g) (X := S))
      (RELSET_1.relationOf_valued hg.2)
  apply th12 (def11 hY hf (FUNCT_1.restrict_isFunction hg.1) hvs hr)
    (def11 hY hf hg.1 (RELSET_1.relationOf_valued hg.2) hr')
  intro x hx
  have hfx : FUNCT_1.apply f x ∈ RELAT_1.rng f := th4 hf hY hx
  have hfxS : FUNCT_1.apply f x ∈ RELAT_1.dom (RELAT_1.restrict g S) :=
    hr _ hfx
  have h1 : FUNCT_1.apply (composeAlong (RELAT_1.restrict g S) f) x =
      FUNCT_1.apply (RELAT_1.restrict g S) (FUNCT_1.apply f x) :=
    th108 hX hY hf (FUNCT_1.restrict_isFunction hg.1) hvs hr hx
  have h2 : FUNCT_1.apply (RELAT_1.restrict g S) (FUNCT_1.apply f x) =
      FUNCT_1.apply g (FUNCT_1.apply f x) :=
    FUNCT_1.th47 hg.1.2 hfxS
  have h3 : FUNCT_1.apply (composeAlong g f) x =
      FUNCT_1.apply g (FUNCT_1.apply f x) :=
    th108 hX hY hf hg.1 (RELSET_1.relationOf_valued hg.2) hr' hx
  exact h1.trans (h2.trans h3.symm)

/-- Unlabeled `FUNCT_2` (`L2404`) -/
theorem th118 {X Y Z S T f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f X Y) (hg : PARTFUN1.isPartFunc g Y Z)
    (hr : RELAT_1.rng f ⊆ RELAT_1.dom (RELAT_1.restrict g S))
    (hST : S ⊆ T) :
    composeAlong (RELAT_1.restrict g S) f =
      composeAlong (RELAT_1.restrict g T) f := by
  have hsub : RELAT_1.restrict g S ⊆ RELAT_1.restrict g T :=
    RELAT_1.th75 (R := g) hST
  have hdom : RELAT_1.dom (RELAT_1.restrict g S) ⊆
      RELAT_1.dom (RELAT_1.restrict g T) :=
    (RELAT_1.th11 hsub).1
  have hrT : RELAT_1.rng f ⊆ RELAT_1.dom (RELAT_1.restrict g T) :=
    XBOOLE_1.th1 hr hdom
  exact (th117 hX hY hf hg hr).trans (th117 hX hY hf hg hrT).symm

/-- Unlabeled `FUNCT_2` (`L2419`) -/
theorem th119 {D A B H d : TarskiSet.{u}}
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hH : isFunctionOf H D (ZFMISC_1.product A B)) (hd : d ∈ D) :
    FUNCT_1.apply H d =
      TARSKI.pair (FUNCT_1.apply (MCART_1.pr1 H) d)
        (FUNCT_1.apply (MCART_1.pr2 H) d) := by
  have hprodNe : ZFMISC_1.product A B ≠ (∅ : TarskiSet.{u}) := by
    intro hempty
    exact ((ZFMISC_1.th90 (X := A) (Y := B)).mp hempty).elim hA hB
  have hHd : FUNCT_1.apply H d ∈ ZFMISC_1.product A B :=
    th5 hH hprodNe hd
  have hpair : FUNCT_1.apply H d =
      TARSKI.pair (XTUPLE_0.fst (FUNCT_1.apply H d))
        (XTUPLE_0.snd (FUNCT_1.apply H d)) :=
    MCART_1.th22 hA hB hHd
  have ⟨_, hpr1⟩ := def5 hD hA hB hH
  have ⟨_, hpr2⟩ := def6 hD hA hB hH
  have h1 : TARSKI.pair (XTUPLE_0.fst (FUNCT_1.apply H d))
      (XTUPLE_0.snd (FUNCT_1.apply H d)) =
      TARSKI.pair (FUNCT_1.apply (MCART_1.pr1 H) d)
        (XTUPLE_0.snd (FUNCT_1.apply H d)) :=
    congrArg (fun s => TARSKI.pair s (XTUPLE_0.snd (FUNCT_1.apply H d)))
      (hpr1 d hd).symm
  have h2 : TARSKI.pair (FUNCT_1.apply (MCART_1.pr1 H) d)
      (XTUPLE_0.snd (FUNCT_1.apply H d)) =
      TARSKI.pair (FUNCT_1.apply (MCART_1.pr1 H) d)
        (FUNCT_1.apply (MCART_1.pr2 H) d) :=
    congrArg (TARSKI.pair (FUNCT_1.apply (MCART_1.pr1 H) d))
      (hpr2 d hd).symm
  exact hpair.trans (h1.trans h2)

/-- Unlabeled `FUNCT_2` (`L2431`) -/
theorem th120 {A1 A2 B1 B2 f g : TarskiSet.{u}}
    (hf : isFunctionOf f A1 A2) (hg : isFunctionOf g B1 B2)
    (ht : PARTFUN1.tolerates f g) :
    isFunctionOf (f ∩ g) (A1 ∩ B1) (A2 ∩ B2) := by
  have hfun : FUNCT_1.isFunction (f ∩ g) :=
    GRFUNC_1.inter_isFunction (functionOf_isFunction hf) (X := g)
  have hrng : RELAT_1.rng (f ∩ g) ⊆ A2 ∩ B2 := by
    intro y hy
    have hyfg : y ∈ RELAT_1.rng f ∩ RELAT_1.rng g :=
      RELAT_1.th13 (P := f) (R := g) y hy
    have ⟨hyf, hyg⟩ := (XBOOLE_0.def4 (RELAT_1.rng f) (RELAT_1.rng g) y).mp hyfg
    exact (XBOOLE_0.def4 A2 B2 y).mpr
      ⟨functionOf_rng_sub hf y hyf, functionOf_rng_sub hg y hyg⟩
  have hdomSub : RELAT_1.dom (f ∩ g) ⊆ A1 ∩ B1 := by
    intro a ha
    have ha' : a ∈ RELAT_1.dom f ∩ RELAT_1.dom g :=
      RELAT_1.th2 (P := f) (R := g) a ha
    have ⟨haf, hag⟩ := (XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom g) a).mp ha'
    exact (XBOOLE_0.def4 A1 B1 a).mpr
      ⟨functionOf_dom_sub hf a haf, functionOf_dom_sub hg a hag⟩
  have := Classical.propDecidable (A2 ∩ B2 = (∅ : TarskiSet.{u}))
  by_cases hCod : A2 ∩ B2 = (∅ : TarskiSet.{u})
  · have hempty : f ∩ g = (∅ : TarskiSet.{u}) :=
      RELAT_1.th41 hfun.1 (Or.inr
        ((XBOOLE_0.def10).mpr
          ⟨Eq.subst (motive := fun s => RELAT_1.rng (f ∩ g) ⊆ s) hCod hrng,
            XBOOLE_1.th2⟩))
    have hrel : RELSET_1.isRelationOf (f ∩ g) (A1 ∩ B1) (A2 ∩ B2) :=
      Eq.subst (motive := fun s =>
          RELSET_1.isRelationOf s (A1 ∩ B1) (A2 ∩ B2))
        hempty.symm (RELSET_1.th12 (A1 ∩ B1) (A2 ∩ B2))
    have hqt : isQuasiTotal (f ∩ g) (A1 ∩ B1) (A2 ∩ B2) :=
      Eq.subst (motive := fun s => isQuasiTotal s (A1 ∩ B1) (A2 ∩ B2))
        hempty.symm (empty_isQuasiTotal (A1 ∩ B1) (A2 ∩ B2) hCod)
    exact ⟨⟨hfun, hrel⟩, hqt⟩
  · have hA2 : A2 ≠ (∅ : TarskiSet.{u}) := by
      intro hA
      exact hCod ((XBOOLE_0.def10).mpr ⟨fun z hz =>
        ((XBOOLE_0.empty_iff _).mp
          (Eq.subst (motive := fun s => z ∈ s) hA
            ((XBOOLE_0.def4 A2 B2 z).mp hz).1)).elim, XBOOLE_1.th2⟩)
    have hB2 : B2 ≠ (∅ : TarskiSet.{u}) := by
      intro hB
      exact hCod ((XBOOLE_0.def10).mpr ⟨fun z hz =>
        ((XBOOLE_0.empty_iff _).mp
          (Eq.subst (motive := fun s => z ∈ s) hB
            ((XBOOLE_0.def4 A2 B2 z).mp hz).2)).elim, XBOOLE_1.th2⟩)
    have hdF : RELAT_1.dom f = A1 := functionOf_dom_eq hf hA2
    have hdG : RELAT_1.dom g = B1 := functionOf_dom_eq hg hB2
    have hd : RELAT_1.dom (f ∩ g) = A1 ∩ B1 := by
      apply (XBOOLE_0.def10).mpr
      constructor
      · exact hdomSub
      · intro a ha
        have ⟨ha1, hb1⟩ := (XBOOLE_0.def4 A1 B1 a).mp ha
        have haf : a ∈ RELAT_1.dom f :=
          Eq.subst (motive := fun s => a ∈ s) hdF.symm ha1
        have hag : a ∈ RELAT_1.dom g :=
          Eq.subst (motive := fun s => a ∈ s) hdG.symm hb1
        have hval : FUNCT_1.apply f a = FUNCT_1.apply g a :=
          (PARTFUN1.def4 f g).mp ht a
            ((XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom g) a).mpr ⟨haf, hag⟩)
        have hpF : TARSKI.pair a (FUNCT_1.apply f a) ∈ f :=
          (FUNCT_1.def2 (f := f) (x := a)).1 haf
        have hpG : TARSKI.pair a (FUNCT_1.apply f a) ∈ g :=
          Eq.subst (motive := fun s => TARSKI.pair a s ∈ g) hval.symm
            ((FUNCT_1.def2 (f := g) (x := a)).1 hag)
        exact RELAT_1.pair_mem_dom
          ((XBOOLE_0.def4 f g _).mpr ⟨hpF, hpG⟩)
    exact functionOf_of hfun hd hrng

/-- Registration: `Funcs(A,B)` is functional. -/
theorem Funcs_isFunctional (A B : TarskiSet.{u}) :
    FUNCT_1.isFunctional (Funcs A B) :=
  fun x hx => (th92 hx).1

/-! ## Function domains (`FUNCT_2:def 12`) -/

/-- `FUNCT_2:def 12` — mode `FUNCTION_DOMAIN of A,B`. -/
def isFunctionDomain (F A B : TarskiSet.{u}) : Prop :=
  F ≠ (∅ : TarskiSet.{u}) ∧ ∀ x, x ∈ F → isFunctionOf x A B

theorem def12 (F A B : TarskiSet.{u}) :
    isFunctionDomain F A B ↔
      F ≠ (∅ : TarskiSet.{u}) ∧ ∀ x, x ∈ F → isFunctionOf x A B :=
  Iff.rfl

theorem functionDomain_isFunctional {F A B : TarskiSet.{u}}
    (hF : isFunctionDomain F A B) : FUNCT_1.isFunctional F :=
  fun x hx => functionOf_isFunction (hF.2 x hx)

/-- Unlabeled `FUNCT_2` (`L2532`) -/
theorem th121 {P Q f : TarskiSet.{u}} (hf : isFunctionOf f P Q) :
    isFunctionDomain (TARSKI.singleton f) P Q :=
  ⟨fun hempty =>
    (XBOOLE_0.empty_iff f).mp
      (Eq.subst (motive := fun s => f ∈ s) hempty
        ((singleton_iff f f).mpr rfl)),
    fun g hg =>
      Eq.subst (motive := fun s => isFunctionOf s P Q)
        ((singleton_iff f g).mp hg).symm hf⟩

/-- `FUNCT_2:122` (`Th122`) -/
theorem th122 (P B : TarskiSet.{u})
    (hne : Funcs P B ≠ (∅ : TarskiSet.{u})) :
    isFunctionDomain (Funcs P B) P B :=
  ⟨hne, fun f hf => th66 hf⟩

/-- Registration: `id I` is total as an `I`-defined Function. -/
theorem id_isTotal (I : TarskiSet.{u}) :
    PARTFUN1.isTotal (RELAT_1.id I) I :=
  RELAT_1.id_dom I

/-- Redefinition of `F/.x` for Function of nonempty codomain. -/
theorem apply_at_eq_apply {X A F x : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u}))
    (hF : isFunctionOf F X A) (hx : x ∈ X) :
    PARTFUN1.apply_at F x = FUNCT_1.apply F x :=
  PARTFUN1.def6 (functionOf_isFunction hF)
    (RELSET_1.relationOf_valued hF.1.2)
    (Eq.subst (motive := fun s => x ∈ s) (functionOf_dom_eq hF hA).symm hx)

/-- Unlabeled `FUNCT_2` (`L2580`) -/
theorem th123 {X f g : TarskiSet.{u}}
    (hf : isFunctionOf f X X) (hg : RELAT_1.isXvalued g X) :
    RELAT_1.dom (RELAT_1.comp g f) = RELAT_1.dom g := by
  have := Classical.propDecidable (X = (∅ : TarskiSet.{u}))
  by_cases hX : X = (∅ : TarskiSet.{u})
  · have hfE : f = (∅ : TarskiSet.{u}) := functionOf_empty_cod hf hX
    have hdF : RELAT_1.dom f = (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u}))
        hfE.symm RELAT_1.th38.1
    have hrngG : RELAT_1.rng g = (∅ : TarskiSet.{u}) :=
      (XBOOLE_0.def10).mpr
        ⟨Eq.subst (motive := fun s => RELAT_1.rng g ⊆ s) hX hg, XBOOLE_1.th2⟩
    have hr : RELAT_1.rng g ⊆ RELAT_1.dom f :=
      Eq.subst (motive := fun s => RELAT_1.rng g ⊆ s) hdF.symm
        (Eq.subst (motive := fun s => s ⊆ (∅ : TarskiSet.{u})) hrngG.symm
          (fun _ hz => hz))
    exact RELAT_1.th27 hr
  · have hd : RELAT_1.dom f = X := functionOf_dom_eq hf hX
    have hr : RELAT_1.rng g ⊆ RELAT_1.dom f :=
      Eq.subst (motive := fun s => RELAT_1.rng g ⊆ s) hd.symm hg
    exact RELAT_1.th27 hr

/-- Unlabeled `FUNCT_2` (`L2591`) -/
theorem th124 {X f : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u}))
    (hf : isFunctionOf f X X)
    (h : ∀ x, x ∈ X → FUNCT_1.apply f x = x) :
    f = RELAT_1.id X := by
  have hid : isFunctionOf (RELAT_1.id X) X X := (id_isPermutation X).1
  exact th63 hf hid fun x hx => (h x hx).trans (FUNCT_1.th18 hx).symm

/-- Mode `Action of O,E` is `Function of O, Funcs(E,E)`. -/
def isAction (a O E : TarskiSet.{u}) : Prop :=
  isFunctionOf a O (Funcs E E)

/-- Unlabeled `FUNCT_2` (`L2610`) -/
theorem th125 {x A f g : TarskiSet.{u}}
    (hf : isFunctionOf f (TARSKI.singleton x) A)
    (hg : isFunctionOf g (TARSKI.singleton x) A)
    (hv : FUNCT_1.apply f x = FUNCT_1.apply g x) :
    f = g := by
  apply th12 hf hg
  intro y hy
  have heq : y = x := (singleton_iff x y).mp hy
  exact Eq.subst (motive := fun s => FUNCT_1.apply f s = FUNCT_1.apply g s)
    heq.symm hv

end FUNCT_2
