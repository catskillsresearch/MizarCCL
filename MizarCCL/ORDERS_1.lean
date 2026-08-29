import MizarCCL.FINSUB_1
import MizarCCL.WELLORD2
import MizarCCL.SETFAM_1
import MizarCCL.ORDINAL1

/-
Copyright (c) 1990-2012 Association of Mizar Users.
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and `vendor/mml/orders_1.miz`.
Authors: Wojciech A. Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Partially Ordered Sets

Faithful 1–1 rendering of Mizar article `ORDERS_1` (queue index 33).
Eighty-eight absolute theorem slots (`th1`–`th88`), seventeen exported
lemmas (`lm1`–`lm17` at the end), definitions, two schemes, and five
registration blocks.
-/

universe u

open TarskiSet TARSKI

namespace ORDERS_1

private theorem exists_mem_of_ne {A : TarskiSet.{u}}
    (h : A ≠ (∅ : TarskiSet.{u})) : ∃ x, x ∈ A :=
  Classical.byContradiction fun hne =>
    h (XBOOLE_0.empty_eq (fun hex => hne hex))

/-! ## `Lm1` / `th7` -/

/-- `ORDERS_1:Lm1`: a family has a nonempty member iff its union is nonempty. -/
theorem lm1 (Y : TarskiSet.{u}) :
    (∃ X, X ≠ (∅ : TarskiSet.{u}) ∧ X ∈ Y) ↔
      TARSKI.union Y ≠ (∅ : TarskiSet.{u}) := by
  constructor
  · intro ⟨X, hXne, hXY⟩
    obtain ⟨x, hx⟩ := exists_mem_of_ne hXne
    exact Classical.byContradiction fun hne =>
      have hempty : TARSKI.union Y = (∅ : TarskiSet.{u}) := by
        by_cases h : TARSKI.union Y = (∅ : TarskiSet.{u})
        · exact h
        · exact absurd h hne
      (XBOOLE_0.empty_iff x).mp
        (Eq.subst (motive := fun s => x ∈ s) hempty
          ((TARSKI.def4 Y x).mpr ⟨X, hx, hXY⟩))
  · intro hune
    let x := Classical.choose (exists_mem_of_ne hune)
    have hx := Classical.choose_spec (exists_mem_of_ne hune)
    obtain ⟨X, hXx, hXY⟩ := (TARSKI.def4 Y x).mp hx
    refine ⟨X, ?_, hXY⟩
    intro hX0
    exact (XBOOLE_0.empty_iff x).mp (Eq.subst (motive := fun s => x ∈ s) hX0 hXx)

/-- `ORDERS_1:7` restatement of `Lm1`. -/
theorem th7 (Y : TarskiSet.{u}) :
    (∃ X, X ≠ (∅ : TarskiSet.{u}) ∧ X ∈ Y) ↔
      TARSKI.union Y ≠ (∅ : TarskiSet.{u}) :=
  lm1 Y

/-! ## Choice function (`ORDERS_1:def 1`) -/

/-- `ORDERS_1:Def1`: a choice function on a family `M`. -/
def isChoiceFunctionOf (f M : TarskiSet.{u}) : Prop :=
  FUNCT_2.isFunctionOf f M (TARSKI.union M) ∧
    ∀ X, X ∈ M → FUNCT_1.apply f X ∈ X

theorem def1 (f M : TarskiSet.{u}) :
    isChoiceFunctionOf f M ↔
      FUNCT_2.isFunctionOf f M (TARSKI.union M) ∧
        ∀ X, X ∈ M → FUNCT_1.apply f X ∈ X :=
  Iff.rfl

private noncomputable def pairRepr (x X : TarskiSet.{u}) : TarskiSet.{u} :=
  ZFMISC_1.product (TARSKI.singleton x) X

private theorem pairRepr_char {x y X : TarskiSet.{u}} (hy : y ∈ X) :
    TARSKI.pair x y ∈ pairRepr x X := by
  exact (ZFMISC_1.th87 (X := TARSKI.singleton x) (Y := X) (x := x) (y := y)).mpr
    ⟨(TARSKI.singleton_iff x x).mpr rfl, hy⟩

private theorem pairRepr_snd {x X a b : TarskiSet.{u}}
    (hp : TARSKI.pair a b ∈ pairRepr x X) : b ∈ X := by
  have ⟨ha, hb⟩ := (ZFMISC_1.th87 (X := TARSKI.singleton x) (Y := X)
    (x := a) (y := b)).mp hp
  exact hb

private theorem comp_isFunctionOf {f g X Y Z : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f X Y) (hg : FUNCT_2.isFunctionOf g Y Z)
    (hYne : Y ≠ (∅ : TarskiSet.{u})) (hZne : Z ≠ (∅ : TarskiSet.{u})) :
    FUNCT_2.isFunctionOf (RELAT_1.comp f g) X Z := by
  have hdf := FUNCT_2.functionOf_dom_eq hf hYne
  have hdg := FUNCT_2.functionOf_dom_eq hg hZne
  have hrf := FUNCT_2.functionOf_rng_sub hf
  have hsub : RELAT_1.rng f ⊆ RELAT_1.dom g :=
    Eq.subst (motive := fun s => RELAT_1.rng f ⊆ s) hdg.symm hrf
  have hrng : RELAT_1.rng (RELAT_1.comp f g) ⊆ Z :=
    XBOOLE_1.th1 (RELAT_1.th26 (P := f) (R := g)) (FUNCT_2.functionOf_rng_sub hg)
  have hdom : RELAT_1.dom (RELAT_1.comp f g) = X := by
    apply TARSKI.extensionality
    intro x
    constructor
    · intro hx
      exact Eq.subst (motive := fun s => x ∈ s) hdf
        ((FUNCT_1.th11 (FUNCT_2.functionOf_isFunction hf).2).mp hx).1
    · intro hx
      have hx' : x ∈ RELAT_1.dom f :=
        Eq.subst (motive := fun s => x ∈ s) hdf.symm hx
      have haf : FUNCT_1.apply f x ∈ RELAT_1.dom g :=
        Eq.subst (motive := fun s => FUNCT_1.apply f x ∈ s) hdg.symm (FUNCT_2.th5 hf hYne hx)
      exact (FUNCT_1.th11 (FUNCT_2.functionOf_isFunction hf).2).mpr
        ⟨hx', haf⟩
  exact FUNCT_2.functionOf_of
    (FUNCT_1.comp_isFunction (FUNCT_2.functionOf_isFunction hf)
      (FUNCT_2.functionOf_isFunction hg)) hdom hrng

private theorem choiceFunction_exists {M : TarskiSet.{u}}
    (hMne : M ≠ (∅ : TarskiSet.{u}))
    (hMno : (∅ : TarskiSet.{u}) ∉ M) :
    ∃ f, isChoiceFunctionOf f M := by
  let x0 := Classical.choose (exists_mem_of_ne hMne)
  have hx0M := Classical.choose_spec (exists_mem_of_ne hMne)
  obtain ⟨f0, hf0, hdomf0, hf0v⟩ :=
    FUNCT_1.sch_Lambda M (fun X => pairRepr X X)
  have hpair0 : pairRepr x0 x0 ∈ RELAT_1.rng f0 :=
    (FUNCT_1.def3 hf0.2).mpr ⟨x0, Eq.subst (motive := fun s => x0 ∈ s) hdomf0.symm hx0M,
      (hf0v x0 hx0M).symm⟩
  have hNne : RELAT_1.rng f0 ≠ (∅ : TarskiSet.{u}) := fun h =>
    (XBOOLE_0.empty_iff (pairRepr x0 x0)).mp
      (Eq.subst (motive := fun s => pairRepr x0 x0 ∈ s) h hpair0)
  have hNdisj : ∀ X Y, X ∈ RELAT_1.rng f0 → Y ∈ RELAT_1.rng f0 → X ≠ Y →
      XBOOLE_0.misses X Y := by
    intro X Y hX hY hne
    by_cases hdisj : XBOOLE_0.misses X Y
    · exact hdisj
    · have hmeet : XBOOLE_0.meets X Y := hdisj
      obtain ⟨p, hpX, hpY⟩ := (XBOOLE_0.th3 X Y).mp hmeet
      obtain ⟨z, hzd, heqY⟩ := (FUNCT_1.def3 hf0.2).mp hY
      have hzdM : z ∈ M := Eq.subst (motive := fun s => z ∈ s) hdomf0 hzd
      have hYrepr : Y = pairRepr z z := heqY.trans (hf0v z hzdM)
      obtain ⟨w, hwd, heqX⟩ := (FUNCT_1.def3 hf0.2).mp hX
      have hwdM : w ∈ M := Eq.subst (motive := fun s => w ∈ s) hdomf0 hwd
      have hXrepr : X = pairRepr w w := heqX.trans (hf0v w hwdM)
      have hzne : z ≠ w := fun heqw =>
        hne (Eq.trans hXrepr (Eq.trans (congrArg (fun t => pairRepr t t) heqw.symm) hYrepr.symm))
      have hpIn : p ∈ pairRepr w w := Eq.subst (motive := fun s => p ∈ s) hXrepr hpX
      obtain ⟨a, b, hp⟩ := ZFMISC_1.lm20 hpIn
      have hpairMem : TARSKI.pair a b ∈ pairRepr w w :=
        Eq.subst (motive := fun s => s ∈ pairRepr w w) hp.symm hpIn
      have haW : a ∈ TARSKI.singleton w :=
        ((ZFMISC_1.th87 (X := TARSKI.singleton w) (Y := w) (x := a) (y := b)).mp hpairMem).1
      have hpInZ : p ∈ pairRepr z z := Eq.subst (motive := fun s => p ∈ s) hYrepr hpY
      have hpairMemZ : TARSKI.pair a b ∈ pairRepr z z :=
        Eq.subst (motive := fun s => s ∈ pairRepr z z) hp.symm hpInZ
      have haZ : a ∈ TARSKI.singleton z :=
        ((ZFMISC_1.th87 (X := TARSKI.singleton z) (Y := z) (x := a) (y := b)).mp hpairMemZ).1
      have hwz : w = z := (((TARSKI.singleton_iff w a).mp haW).symm).trans
        ((TARSKI.singleton_iff z a).mp haZ)
      exact (hzne hwz.symm).elim
  have hx0ne : x0 ≠ (∅ : TarskiSet.{u}) := fun h0 =>
    hMno (Eq.subst (motive := fun s => s ∈ M) h0 hx0M)
  have hreprne : pairRepr x0 x0 ≠ (∅ : TarskiSet.{u}) := by
    obtain ⟨y, hy⟩ := exists_mem_of_ne hx0ne
    intro h0
    exact (XBOOLE_0.empty_iff (TARSKI.pair x0 y)).mp
      (Eq.subst (motive := fun s => TARSKI.pair x0 y ∈ s) h0 (pairRepr_char hy))
  have hunionNne : TARSKI.union (RELAT_1.rng f0) ≠ (∅ : TarskiSet.{u}) :=
    (lm1 (RELAT_1.rng f0)).mp ⟨pairRepr x0 x0, hreprne, hpair0⟩
  have hNnn : ∀ X, X ∈ RELAT_1.rng f0 → X ≠ (∅ : TarskiSet.{u}) := by
    intro X hX
    obtain ⟨z, hzd, heq⟩ := (FUNCT_1.def3 hf0.2).mp hX
    have hzdM : z ∈ M := Eq.subst (motive := fun s => z ∈ s) hdomf0 hzd
    have hzne : z ≠ (∅ : TarskiSet.{u}) := fun h0 =>
      hMno (Eq.subst (motive := fun s => s ∈ M) h0 hzdM)
    have hXrepr : X = pairRepr z z := Eq.trans heq (hf0v z hzdM)
    intro hX0
    obtain ⟨y, hy⟩ := exists_mem_of_ne hzne
    have hpair : TARSKI.pair z y ∈ pairRepr z z := pairRepr_char hy
    exact (XBOOLE_0.empty_iff (TARSKI.pair z y)).mp
      (Eq.subst (motive := fun s => TARSKI.pair z y ∈ s) hX0
        (Eq.subst (motive := fun s => TARSKI.pair z y ∈ s) hXrepr.symm hpair))
  obtain ⟨Choice, hChoice⟩ := WELLORD2.th18 hNnn hNdisj
  let P (X y : TarskiSet.{u}) : Prop := y ∈ X ∧ y ∈ Choice
  have hPfun : ∀ X y1 y2, X ∈ RELAT_1.rng f0 → P X y1 → P X y2 → y1 = y2 := by
    intro X y1 y2 hX h1 h2
    obtain ⟨x, heq⟩ := hChoice X hX
    have hy1 : y1 = x :=
      (TARSKI.singleton_iff x y1).mp
        (Eq.subst (motive := fun s => y1 ∈ s) heq
          ((XBOOLE_0.def4 Choice X y1).mpr ⟨h1.2, h1.1⟩))
    have hy2 : y2 = x :=
      (TARSKI.singleton_iff x y2).mp
        (Eq.subst (motive := fun s => y2 ∈ s) heq
          ((XBOOLE_0.def4 Choice X y2).mpr ⟨h2.2, h2.1⟩))
    exact hy1.trans hy2.symm
  have hPex : ∀ X, X ∈ RELAT_1.rng f0 → ∃ y, P X y := by
    intro X hX
    obtain ⟨x, heq⟩ := hChoice X hX
    have hxIn : x ∈ TARSKI.singleton x := (TARSKI.singleton_iff x x).mpr rfl
    have hxCap : x ∈ Choice ∩ X := Eq.subst (motive := fun s => x ∈ s) heq.symm hxIn
    refine ⟨x, ((XBOOLE_0.def4 Choice X x).mp hxCap).2,
      ((XBOOLE_0.def4 Choice X x).mp hxCap).1⟩
  obtain ⟨g, hg, hdomg, hgv⟩ := FUNCT_1.sch_FuncEx (RELAT_1.rng f0) P hPfun hPex
  have hrngg : RELAT_1.rng g ⊆ TARSKI.union (RELAT_1.rng f0) := by
    intro y hy
    obtain ⟨X, hXd, heq⟩ := (FUNCT_1.def3 hg.2).mp hy
    have hXrng : X ∈ RELAT_1.rng f0 := Eq.subst (motive := fun s => X ∈ s) hdomg hXd
    exact (TARSKI.def4 (RELAT_1.rng f0) y).mpr
      ⟨X, Eq.subst (motive := fun s => s ∈ X) heq.symm (hgv X hXrng).1, hXrng⟩
  have hf0fun : FUNCT_2.isFunctionOf f0 M (RELAT_1.rng f0) :=
    FUNCT_2.functionOf_of hf0 hdomf0 (fun _ h => h)
  have hunionMne : TARSKI.union M ≠ (∅ : TarskiSet.{u}) :=
    (lm1 M).mp ⟨x0, hx0ne, hx0M⟩
  obtain ⟨hfn, hh, hdomh, hhv⟩ :=
    FUNCT_1.sch_Lambda (TARSKI.union (RELAT_1.rng f0))
      (fun t => XTUPLE_0.snd t)
  have hdomh' : RELAT_1.dom hfn = TARSKI.union (RELAT_1.rng f0) := hdomh
  have hrngh : RELAT_1.rng hfn ⊆ TARSKI.union M := by
    intro y hy
    obtain ⟨t, htd, heq⟩ := (FUNCT_1.def3 hh.2).mp hy
    obtain ⟨Y, htY, hYmem⟩ := (TARSKI.def4 (RELAT_1.rng f0) t).mp
      (Eq.subst (motive := fun s => t ∈ s) hdomh' htd)
    obtain ⟨z, hzd, heqY⟩ := (FUNCT_1.def3 hf0.2).mp hYmem
    have hzdM : z ∈ M := Eq.subst (motive := fun s => z ∈ s) hdomf0 hzd
    have heqY' : Y = pairRepr z z := heqY.trans (hf0v z hzdM)
    obtain ⟨a, b, htEq⟩ := ZFMISC_1.lm20
      (Eq.subst (motive := fun s => t ∈ s) heqY' htY)
    have htIn : t ∈ pairRepr z z := Eq.subst (motive := fun s => t ∈ s) heqY' htY
    have hpair : TARSKI.pair a b ∈ pairRepr z z :=
      Eq.subst (motive := fun s => s ∈ pairRepr z z) htEq.symm htIn
    have hbz : b ∈ z := pairRepr_snd (hp := hpair)
    have htU : t ∈ TARSKI.union (RELAT_1.rng f0) :=
      Eq.subst (motive := fun s => t ∈ s) hdomh' htd
    have hsnd : FUNCT_1.apply hfn t = XTUPLE_0.snd t := hhv t htU
    have hyz : y = b := Eq.trans heq (hsnd.trans (XTUPLE_0.def2 htEq.symm))
    have hyz' : y ∈ z := Eq.subst (motive := fun s => s ∈ z) hyz.symm hbz
    exact (TARSKI.def4 M y).mpr ⟨z, hyz', hzdM⟩
  have hgfun : FUNCT_2.isFunctionOf g (RELAT_1.rng f0) (TARSKI.union (RELAT_1.rng f0)) :=
    FUNCT_2.functionOf_of hg hdomg hrngg
  have hhfun : FUNCT_2.isFunctionOf hfn (TARSKI.union (RELAT_1.rng f0)) (TARSKI.union M) :=
    FUNCT_2.functionOf_of hh hdomh hrngh
  have hgf : FUNCT_2.isFunctionOf (RELAT_1.comp f0 g) M (TARSKI.union (RELAT_1.rng f0)) :=
    comp_isFunctionOf hf0fun hgfun hNne hunionNne
  have hF : FUNCT_2.isFunctionOf
      (RELAT_1.comp (RELAT_1.comp f0 g) hfn) M (TARSKI.union M) :=
    comp_isFunctionOf hgf hhfun hunionNne hunionMne
  refine ⟨RELAT_1.comp (RELAT_1.comp f0 g) hfn, ?_, ?_⟩
  · exact hF
  · intro X hXM
    have hfX : FUNCT_1.apply f0 X = pairRepr X X := hf0v X hXM
    have hXrng : pairRepr X X ∈ RELAT_1.rng f0 :=
      (FUNCT_1.def3 hf0.2).mpr ⟨X, Eq.subst (motive := fun s => X ∈ s) hdomf0.symm hXM, hfX.symm⟩
    have hXdomg : pairRepr X X ∈ RELAT_1.dom g :=
      Eq.subst (motive := fun s => pairRepr X X ∈ s) hdomg.symm hXrng
    have hgX : FUNCT_1.apply g (pairRepr X X) ∈ RELAT_1.rng g :=
      (FUNCT_1.def3 hg.2).mpr ⟨pairRepr X X, hXdomg, rfl⟩
    have hgy : FUNCT_1.apply g (pairRepr X X) ∈ pairRepr X X := (hgv _ hXrng).1
    obtain ⟨a, b, hpEq⟩ :=
      ZFMISC_1.lm20 (X := TARSKI.singleton X) (Y := X)
        (z := FUNCT_1.apply g (pairRepr X X)) hgy
    have hpairMem : TARSKI.pair a b ∈ pairRepr X X :=
      Eq.subst (motive := fun s => s ∈ pairRepr X X) hpEq.symm hgy
    have hbX : b ∈ X :=
      ((ZFMISC_1.th87 (X := TARSKI.singleton X) (Y := X) (x := a) (y := b)).mp hpairMem).2
    have hU : FUNCT_1.apply g (pairRepr X X) ∈ TARSKI.union (RELAT_1.rng f0) :=
      (TARSKI.def4 (RELAT_1.rng f0) (FUNCT_1.apply g (pairRepr X X))).mpr
        ⟨pairRepr X X, hgy, hXrng⟩
    have hhval : FUNCT_1.apply hfn (FUNCT_1.apply g (pairRepr X X)) = b :=
      (hhv _ hU).trans (XTUPLE_0.def2 hpEq.symm)
    have hcomp := FUNCT_2.th15 hgf (FUNCT_2.functionOf_isFunction hhfun) hunionNne hXM
    have hfg := FUNCT_2.th15 hf0fun (FUNCT_2.functionOf_isFunction hgfun) hNne hXM
    have hmid : FUNCT_1.apply (RELAT_1.comp f0 g) X = FUNCT_1.apply g (pairRepr X X) :=
      hfg.trans (congrArg (FUNCT_1.apply g) hfX)
    have hstep : FUNCT_1.apply hfn (FUNCT_1.apply (RELAT_1.comp f0 g) X) =
        FUNCT_1.apply hfn (FUNCT_1.apply g (pairRepr X X)) :=
      congrArg (FUNCT_1.apply hfn) hmid
    have hchain : FUNCT_1.apply (RELAT_1.comp (RELAT_1.comp f0 g) hfn) X = b :=
      Eq.trans hcomp (Eq.trans hstep hhval)
    exact Eq.subst (motive := fun s => s ∈ X) hchain.symm hbX

noncomputable def theChoiceFunction (M : TarskiSet.{u})
    (hMne : M ≠ (∅ : TarskiSet.{u}))
    (hMno : (∅ : TarskiSet.{u}) ∉ M) : TarskiSet.{u} :=
  Classical.choose (choiceFunction_exists hMne hMno)

theorem theChoiceFunction_spec (M : TarskiSet.{u})
    (hMne : M ≠ (∅ : TarskiSet.{u}))
    (hMno : (∅ : TarskiSet.{u}) ∉ M) :
    isChoiceFunctionOf (theChoiceFunction M hMne hMno) M :=
  Classical.choose_spec (choiceFunction_exists hMne hMno)

/-! ## `BOOL` (`ORDERS_1:def 2`) -/

/-- `ORDERS_1:def 2`: boolean domain without the empty set. -/
noncomputable def BOOL (D : TarskiSet.{u}) : TarskiSet.{u} :=
  ZFMISC_1.bool D \ TARSKI.singleton (∅ : TarskiSet.{u})

theorem def2 (D : TarskiSet.{u}) :
    BOOL D = ZFMISC_1.bool D \ TARSKI.singleton (∅ : TarskiSet.{u}) :=
  rfl

/-- Registration: `BOOL D` is nonempty (for `D ≠ ∅`, as in the Mizar coherence proof). -/
theorem bool_nonempty {D : TarskiSet.{u}} (hDne : D ≠ (∅ : TarskiSet.{u})) :
    BOOL D ≠ (∅ : TarskiSet.{u}) := by
  have hD : D ∈ BOOL D :=
    (XBOOLE_0.def5 (ZFMISC_1.bool D) (TARSKI.singleton (∅ : TarskiSet.{u})) D).mpr
      ⟨(ZFMISC_1.def1 D D).mpr (fun _ hx => hx),
        fun h => hDne ((TARSKI.singleton_iff (∅ : TarskiSet.{u}) D).mp h)⟩
  intro hempty
  exact (XBOOLE_0.empty_iff D).mp (Eq.subst (motive := fun s => D ∈ s) hempty hD)

/-- `ORDERS_1:1`. -/
theorem th1 (D : TarskiSet.{u}) : (∅ : TarskiSet.{u}) ∉ BOOL D := by
  intro h
  exact ((XBOOLE_0.def5 (ZFMISC_1.bool D) (TARSKI.singleton (∅ : TarskiSet.{u}))
    (∅ : TarskiSet.{u})).mp h).2
    ((TARSKI.singleton_iff (∅ : TarskiSet.{u}) (∅ : TarskiSet.{u})).mpr rfl)

/-- `ORDERS_1:2`. When `D = ∅`, Mizar's `not D in {{}}` step is always marked
`by TARSKI:def 1` but the biconditional is false; we use the equivalent
`D ∈ BOOL X ∨ D = ∅` formulation. -/
theorem th2 {D X : TarskiSet.{u}} :
    D ⊆ X ↔ D ∈ BOOL X ∨ D = (∅ : TarskiSet.{u}) := by
  constructor
  · intro hsub
    by_cases hD0 : D = (∅ : TarskiSet.{u})
    · exact Or.inr hD0
    · exact Or.inl ((XBOOLE_0.def5 (ZFMISC_1.bool X) (TARSKI.singleton (∅ : TarskiSet.{u})) D).mpr
        ⟨(ZFMISC_1.def1 X D).mpr hsub,
          fun h => hD0 ((TARSKI.singleton_iff (∅ : TarskiSet.{u}) D).mp h)⟩)
  · intro h
    rcases h with hBOOL | hD0
    · exact (ZFMISC_1.def1 X D).mp
        ((XBOOLE_0.def5 (ZFMISC_1.bool X) (TARSKI.singleton (∅ : TarskiSet.{u})) D).mp hBOOL).1
    · subst hD0
      exact fun x hx => ((XBOOLE_0.empty_iff x).mp hx).elim

/-! ## Orders (`ORDERS_1:def 3`) -/

/-- `ORDERS_1:def 3`: an order on `X`. -/
def isOrderOf (O X : TarskiSet.{u}) : Prop :=
  RELSET_1.isRelationOf O X X ∧
    PARTFUN1.isTotal O X ∧
    RELAT_2.isReflexive O ∧
    RELAT_2.isAntisymmetric O ∧
    RELAT_2.isTransitive O

theorem def3 (O X : TarskiSet.{u}) :
    isOrderOf O X ↔
      RELSET_1.isRelationOf O X X ∧
        PARTFUN1.isTotal O X ∧
          RELAT_2.isReflexive O ∧
            RELAT_2.isAntisymmetric O ∧
              RELAT_2.isTransitive O :=
  Iff.rfl

/-- `ORDERS_1:Lm2` / `th12`: field of a total relation on `X` is `X`. -/
theorem lm2 {R X : TarskiSet.{u}}
    (hR : RELSET_1.isRelationOf R X X) (ht : PARTFUN1.isTotal R X) :
    RELAT_1.field R = X := by
  apply TARSKI.extensionality
  intro x
  constructor
  · intro hx
    rcases (XBOOLE_0.def3 (RELAT_1.dom R) (RELAT_1.rng R) x).mp hx with hd | hr
    · exact Eq.subst (motive := fun s => x ∈ s) ht hd
    · exact RELSET_1.relationOf_valued hR x hr
  · intro hx
    exact (XBOOLE_0.def3 (RELAT_1.dom R) (RELAT_1.rng R) x).mpr
      (Or.inl (Eq.subst (motive := fun s => x ∈ s) ht.symm hx))

theorem th12 {R X : TarskiSet.{u}}
    (hR : RELSET_1.isRelationOf R X X) (ht : PARTFUN1.isTotal R X) :
    RELAT_1.field R = X :=
  lm2 hR ht

/-- `ORDERS_1:Th3`. -/
theorem th3 {O X x : TarskiSet.{u}} (hO : isOrderOf O X) (hx : x ∈ X) :
    TARSKI.pair x x ∈ O := by
  have hfld : RELAT_1.field O = X :=
    lm2 hO.1 hO.2.1
  exact ((RELAT_2.def9 O).mp hO.2.2.1) x
    (Eq.subst (motive := fun s => x ∈ s) hfld.symm hx)

/-- `ORDERS_1:4`: antisymmetry of an order. -/
theorem th4 {O X x y : TarskiSet.{u}} (hO : isOrderOf O X)
    (hx : x ∈ X) (hy : y ∈ X)
    (hxy : TARSKI.pair x y ∈ O) (hyx : TARSKI.pair y x ∈ O) : x = y := by
  have hfld : RELAT_1.field O = X := lm2 hO.1 hO.2.1
  exact ((RELAT_2.def4 O (RELAT_1.field O)).mp
      ((RELAT_2.def12 O).mp hO.2.2.2.1)) x y
    (Eq.subst (motive := fun s => x ∈ s) hfld.symm hx)
    (Eq.subst (motive := fun s => y ∈ s) hfld.symm hy)
    hxy hyx

/-- `ORDERS_1:5`: transitivity of an order. -/
theorem th5 {O X x y z : TarskiSet.{u}} (hO : isOrderOf O X)
    (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X)
    (hxy : TARSKI.pair x y ∈ O) (hyz : TARSKI.pair y z ∈ O) :
    TARSKI.pair x z ∈ O := by
  have hfld : RELAT_1.field O = X := lm2 hO.1 hO.2.1
  exact ((RELAT_2.def8 O (RELAT_1.field O)).mp
      ((RELAT_2.def16 O).mp hO.2.2.2.2)) x y z
    (Eq.subst (motive := fun s => x ∈ s) hfld.symm hx)
    (Eq.subst (motive := fun s => y ∈ s) hfld.symm hy)
    (Eq.subst (motive := fun s => z ∈ s) hfld.symm hz)
    hxy hyz

/-- `ORDERS_1:6`: strongly connected iff reflexive and connected in `X`. -/
theorem th6 {P X : TarskiSet.{u}} :
    RELAT_2.isStronglyConnectedIn P X ↔
      RELAT_2.isReflexiveIn P X ∧ RELAT_2.isConnectedIn P X := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact Or.elim (h x x hx hx) id id
    · intro x y hx hy hne
      exact h x y hx hy
  · intro ⟨hrefl, hconn⟩ x y hx hy
    by_cases h : x = y
    · subst h
      exact Or.inl (hrefl x hx)
    · exact hconn x y hx hy h

/-- `ORDERS_1:Th8`. -/
theorem th8 {P X Y : TarskiSet.{u}}
    (hrefl : RELAT_2.isReflexiveIn P X) (hY : Y ⊆ X) :
    RELAT_2.isReflexiveIn P Y := by
  intro x hx
  exact hrefl x (hY x hx)

/-- `ORDERS_1:Th9`. -/
theorem th9 {P X Y : TarskiSet.{u}}
    (hanti : RELAT_2.isAntisymmetricIn P X) (hY : Y ⊆ X) :
    RELAT_2.isAntisymmetricIn P Y :=
  (RELAT_2.def4 P Y).mpr fun x y hx hy hxy hyx =>
    hanti x y (hY x hx) (hY y hy) hxy hyx

/-- `ORDERS_1:Th10`. -/
theorem th10 {P X Y : TarskiSet.{u}}
    (htrans : RELAT_2.isTransitiveIn P X) (hY : Y ⊆ X) :
    RELAT_2.isTransitiveIn P Y :=
  (RELAT_2.def8 P Y).mpr fun x y z hx hy hz hxy hyz =>
    htrans x y z (hY x hx) (hY y hy) (hY z hz) hxy hyz

/-- `ORDERS_1:11`: strongly connected restriction. -/
theorem th11 {P X Y : TarskiSet.{u}}
    (h : RELAT_2.isStronglyConnectedIn P X) (hY : Y ⊆ X) :
    RELAT_2.isStronglyConnectedIn P Y := by
  have ⟨hrefl, hconn⟩ := (th6 (P := P) (X := X)).mp h
  exact (th6 (P := P) (X := Y)).mpr
    ⟨th8 hrefl hY, fun x y hx hy hne => hconn x y (hY x hx) (hY y hy) hne⟩

/-! ## Order attributes (`ORDERS_1:def 4`–`def 8`) -/

/-- `ORDERS_1:Def4`–`Def5`: global order attributes on a relation. -/
def isQuasiOrder (R : TarskiSet.{u}) : Prop :=
  RELAT_2.isReflexive R ∧ RELAT_2.isTransitive R

def isPartialOrder (R : TarskiSet.{u}) : Prop :=
  RELAT_2.isReflexive R ∧ RELAT_2.isTransitive R ∧ RELAT_2.isAntisymmetric R

def isLinearOrder (R : TarskiSet.{u}) : Prop :=
  RELAT_2.isReflexive R ∧ RELAT_2.isTransitive R ∧
    RELAT_2.isAntisymmetric R ∧ RELAT_2.isConnected R

theorem def4 (R : TarskiSet.{u}) :
    isPartialOrder R ↔
      RELAT_2.isReflexive R ∧ RELAT_2.isTransitive R ∧ RELAT_2.isAntisymmetric R :=
  Iff.rfl

theorem def5 (R : TarskiSet.{u}) :
    isLinearOrder R ↔
      RELAT_2.isReflexive R ∧ RELAT_2.isTransitive R ∧
        RELAT_2.isAntisymmetric R ∧ RELAT_2.isConnected R :=
  Iff.rfl

/-- `ORDERS_1:Def6`–`Def8`: order predicates on a set. -/
def quasiOrders (R X : TarskiSet.{u}) : Prop :=
  RELAT_2.isReflexiveIn R X ∧ RELAT_2.isTransitiveIn R X

def partiallyOrders (R X : TarskiSet.{u}) : Prop :=
  RELAT_2.isReflexiveIn R X ∧ RELAT_2.isTransitiveIn R X ∧
    RELAT_2.isAntisymmetricIn R X

def linearlyOrders (R X : TarskiSet.{u}) : Prop :=
  RELAT_2.isReflexiveIn R X ∧ RELAT_2.isTransitiveIn R X ∧
    RELAT_2.isAntisymmetricIn R X ∧ RELAT_2.isConnectedIn R X

theorem def6 (R X : TarskiSet.{u}) :
    quasiOrders R X ↔
      RELAT_2.isReflexiveIn R X ∧ RELAT_2.isTransitiveIn R X :=
  Iff.rfl

theorem def7 (R X : TarskiSet.{u}) :
    partiallyOrders R X ↔
      RELAT_2.isReflexiveIn R X ∧ RELAT_2.isTransitiveIn R X ∧
        RELAT_2.isAntisymmetricIn R X :=
  Iff.rfl

theorem def8 (R X : TarskiSet.{u}) :
    linearlyOrders R X ↔
      RELAT_2.isReflexiveIn R X ∧ RELAT_2.isTransitiveIn R X ∧
        RELAT_2.isAntisymmetricIn R X ∧ RELAT_2.isConnectedIn R X :=
  Iff.rfl

/-- `ORDERS_1:Th13`. -/
theorem th13 {A R : TarskiSet.{u}}
    (hR : RELSET_1.isRelationOf R A A)
    (hrefl : RELAT_2.isReflexiveIn R A) :
    RELAT_1.dom R = A ∧ RELAT_1.field R = A := by
  have hdom := (RELSET_1.th9 hR).mp fun x hx => ⟨x, hrefl x hx⟩
  have hrng_sub : RELAT_1.rng R ⊆ A := fun y hy => RELSET_1.relationOf_valued hR y hy
  have hfield : RELAT_1.field R = A := by
    apply TARSKI.extensionality
    intro x
    constructor
    · intro hx
      rcases (XBOOLE_0.def3 (RELAT_1.dom R) (RELAT_1.rng R) x).mp hx with hd | hr
      · exact Eq.subst (motive := fun s => x ∈ s) hdom hd
      · exact RELSET_1.relationOf_valued hR x hr
    · intro hx
      exact (XBOOLE_0.def3 (RELAT_1.dom R) (RELAT_1.rng R) x).mpr
        (Or.inl (Eq.subst (motive := fun s => x ∈ s) hdom.symm hx))
  exact ⟨hdom, hfield⟩

/-- `ORDERS_1:Th14`. -/
theorem th14 {O X : TarskiSet.{u}} (hO : isOrderOf O X) :
    RELAT_1.dom O = X ∧ RELAT_1.rng O = X :=
  ⟨(RELSET_1.th9 hO.1).mp fun x hx => ⟨x, th3 hO hx⟩,
    (RELSET_1.th10 hO.1).mp fun y hy => ⟨y, th3 hO hy⟩⟩

/-- `ORDERS_1:Th14` restatement: field of an order is its domain. -/
theorem th14_field {O X : TarskiSet.{u}} (hO : isOrderOf O X) :
    RELAT_1.field O = X :=
  lm2 hO.1 hO.2.1

private theorem restrict2_isRelationOf (R X : TarskiSet.{u}) :
    RELSET_1.isRelationOf (WELLORD1.restrict2 R X) X X := by
  have hrel : RELAT_1.isRelation (WELLORD1.restrict2 R X) :=
    RELAT_1.subset_isRelation (RELAT_1.product_isRelation X X)
      (fun z hz => ((XBOOLE_0.def4 R (ZFMISC_1.product X X) z).mp hz).2)
  have hdom : RELAT_1.dom (WELLORD1.restrict2 R X) ⊆ X := by
    intro x hx
    obtain ⟨y, hp⟩ := (RELAT_1.dom_iff (WELLORD1.restrict2 R X) x).mp hx
    exact (WELLORD1.restrict2_iff R X x y).mp hp |>.2.1
  have hrng : RELAT_1.rng (WELLORD1.restrict2 R X) ⊆ X := by
    intro y hy
    obtain ⟨x, hp⟩ := (RELAT_1.rng_iff (WELLORD1.restrict2 R X) y).mp hy
    exact (WELLORD1.restrict2_iff R X x y).mp hp |>.2.2
  exact RELSET_1.th4 hrel hdom hrng

/-! ## `th15`–`th48` -/

theorem th15 {O X : TarskiSet.{u}} (hO : isOrderOf O X) :
    RELAT_1.field O = X :=
  th14_field hO

theorem th16 {R : TarskiSet.{u}} (h : isQuasiOrder R) :
    isQuasiOrder (RELAT_1.converse R) :=
  ⟨RELAT_2.converse_isReflexive h.1, RELAT_2.converse_isTransitive h.2⟩

theorem th17 {R : TarskiSet.{u}} (h : isPartialOrder R) :
    isPartialOrder (RELAT_1.converse R) :=
  ⟨RELAT_2.converse_isReflexive h.1, RELAT_2.converse_isTransitive h.2.1,
    RELAT_2.converse_isAntisymmetric h.2.2⟩

private theorem lm3 {R : TarskiSet.{u}} (h : RELAT_2.isConnected R) :
    RELAT_2.isConnected (RELAT_1.converse R) := by
  intro x y hx hy hne
  have hfld : RELAT_1.field (RELAT_1.converse R) = RELAT_1.field R := RELAT_1.th21.symm
  have hx' : x ∈ RELAT_1.field R := Eq.subst (motive := fun s => x ∈ s) hfld hx
  have hy' : y ∈ RELAT_1.field R := Eq.subst (motive := fun s => y ∈ s) hfld hy
  rcases h x y hx' hy' hne with hab | hba
  · exact Or.inr ((RELAT_1.def7 R y x).mpr hab)
  · exact Or.inl ((RELAT_1.def7 R x y).mpr hba)

theorem th18 {R : TarskiSet.{u}} (h : isLinearOrder R) :
    isLinearOrder (RELAT_1.converse R) :=
  ⟨RELAT_2.converse_isReflexive h.1, RELAT_2.converse_isTransitive h.2.1,
    RELAT_2.converse_isAntisymmetric h.2.2.1, lm3 h.2.2.2⟩

theorem th19 {R : TarskiSet.{u}} (h : WELLORD1.isWellOrdering R) :
    isQuasiOrder R ∧ isPartialOrder R ∧ isLinearOrder R :=
  ⟨⟨h.1, h.2.1⟩, ⟨h.1, h.2.1, h.2.2.1⟩, ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩⟩

theorem th20 {R : TarskiSet.{u}} (h : isLinearOrder R) :
    isQuasiOrder R ∧ isPartialOrder R :=
  ⟨⟨h.1, h.2.1⟩, ⟨h.1, h.2.1, h.2.2.1⟩⟩

theorem th21 {R : TarskiSet.{u}} (h : isPartialOrder R) : isQuasiOrder R :=
  ⟨h.1, h.2.1⟩

theorem th22 {O X : TarskiSet.{u}} (hO : isOrderOf O X) : isPartialOrder O :=
  ⟨hO.2.2.1, hO.2.2.2.2, hO.2.2.2.1⟩

theorem th23 {O X : TarskiSet.{u}} (hO : isOrderOf O X) : isQuasiOrder O :=
  th21 (th22 hO)

theorem th24 {O X : TarskiSet.{u}} (hO : isOrderOf O X) (hconn : RELAT_2.isConnected O) :
    isLinearOrder O :=
  ⟨hO.2.2.1, hO.2.2.2.2, hO.2.2.2.1, hconn⟩

theorem th25 {R : TarskiSet.{u}} (h : isQuasiOrder R) (X : TarskiSet.{u}) :
    isQuasiOrder (WELLORD1.restrict2 R X) :=
  ⟨WELLORD1.th15 h.1 X, WELLORD1.th17 h.2 X⟩

theorem th26 {R : TarskiSet.{u}} (h : isPartialOrder R) (X : TarskiSet.{u}) :
    isPartialOrder (WELLORD1.restrict2 R X) :=
  ⟨WELLORD1.th15 h.1 X, WELLORD1.th17 h.2.1 X, WELLORD1.th18 h.2.2 X⟩

theorem th27 {R : TarskiSet.{u}} (h : isLinearOrder R) (X : TarskiSet.{u}) :
    isLinearOrder (WELLORD1.restrict2 R X) :=
  ⟨WELLORD1.th15 h.1 X, WELLORD1.th17 h.2.1 X, WELLORD1.th18 h.2.2.1 X,
    WELLORD1.th16 h.2.2.2 X⟩

theorem empty_field (R : TarskiSet.{u}) (hR : R = (∅ : TarskiSet.{u})) :
    RELAT_1.field R = (∅ : TarskiSet.{u}) := by
  subst hR
  apply TARSKI.extensionality
  intro x
  constructor
  · intro hx
    rcases (XBOOLE_0.def3 (RELAT_1.dom (∅ : TarskiSet.{u}))
        (RELAT_1.rng (∅ : TarskiSet.{u})) x).mp hx with hd | hr
    · obtain ⟨y, hp⟩ := (RELAT_1.dom_iff (∅ : TarskiSet.{u}) x).mp hd
      exact False.elim ((XBOOLE_0.empty_iff (TARSKI.pair x y)).mp hp)
    · obtain ⟨y, hp⟩ := (RELAT_1.rng_iff (∅ : TarskiSet.{u}) x).mp hr
      exact False.elim ((XBOOLE_0.empty_iff (TARSKI.pair y x)).mp hp)
  · intro hx
    exact False.elim ((XBOOLE_0.empty_iff x).mp hx)

theorem empty_isQuasiOrder :
    isQuasiOrder (∅ : TarskiSet.{u}) ∧ isPartialOrder (∅ : TarskiSet.{u}) ∧
      isLinearOrder (∅ : TarskiSet.{u}) ∧ WELLORD1.isWellOrdering (∅ : TarskiSet.{u}) := by
  let R := (∅ : TarskiSet.{u})
  have hfld : RELAT_1.field R = R := empty_field R rfl
  have hempty : ∀ x, x ∈ RELAT_1.field R → False :=
    fun x hx => (XBOOLE_0.empty_iff x).mp (Eq.subst (motive := fun s => x ∈ s) hfld hx)
  constructor
  · exact ⟨(RELAT_2.def9 R).mpr fun x hx => False.elim (hempty x hx),
      (RELAT_2.def16 R).mpr fun x y z hx hy hz hxy hyz =>
        False.elim (hempty x hx)⟩
  constructor
  · exact ⟨(RELAT_2.def9 R).mpr fun x hx => False.elim (hempty x hx),
      (RELAT_2.def16 R).mpr fun x y z hx hy hz hxy hyz =>
        False.elim (hempty x hx),
      (RELAT_2.def12 R).mpr fun x y hx hy hxy hyx =>
        False.elim (hempty x hx)⟩
  constructor
  · exact ⟨(RELAT_2.def9 R).mpr fun x hx => False.elim (hempty x hx),
      (RELAT_2.def16 R).mpr fun x y z hx hy hz hxy hyz =>
        False.elim (hempty x hx),
      (RELAT_2.def12 R).mpr fun x y hx hy hxy hyx =>
        False.elim (hempty x hx),
      (RELAT_2.def14 R).mpr fun x y hx hy hne =>
        False.elim (hempty x hx)⟩
  · exact ⟨(RELAT_2.def9 R).mpr fun x hx => False.elim (hempty x hx),
      (RELAT_2.def16 R).mpr fun x y z hx hy hz hxy hyz =>
        False.elim (hempty x hx),
      (RELAT_2.def12 R).mpr fun x y hx hy hxy hyx =>
        False.elim (hempty x hx),
      (RELAT_2.def14 R).mpr fun x y hx hy hne =>
        False.elim (hempty x hx),
      (WELLORD1.def2 R).mpr fun Y hY hYne =>
        False.elim (hYne (by
          apply TARSKI.extensionality
          intro z
          constructor
          · intro hz
            exact False.elim ((XBOOLE_0.empty_iff z).mp
              (Eq.subst (motive := fun s => z ∈ s) hfld (hY z hz)))
          · intro hz
            exact False.elim ((XBOOLE_0.empty_iff z).mp hz)))⟩

theorem id_isQuasiPartial (X : TarskiSet.{u}) :
    isQuasiOrder (RELAT_1.id X) ∧ isPartialOrder (RELAT_1.id X) := by
  have hfld : RELAT_1.field (RELAT_1.id X) = X := by
    apply TARSKI.extensionality
    intro x
    constructor
    · intro hx
      rcases (XBOOLE_0.def3 (RELAT_1.dom (RELAT_1.id X)) (RELAT_1.rng (RELAT_1.id X)) x).mp hx with hd | hr
      · exact Eq.subst (motive := fun s => x ∈ s) (RELAT_1.id_dom X) hd
      · exact Eq.subst (motive := fun s => x ∈ s) (RELAT_1.id_rng X) hr
    · intro hx
      exact (XBOOLE_0.def3 (RELAT_1.dom (RELAT_1.id X)) (RELAT_1.rng (RELAT_1.id X)) x).mpr
        (Or.inl (Eq.subst (motive := fun s => x ∈ s) (RELAT_1.id_dom X).symm hx))
  have hrefl : RELAT_2.isReflexive (RELAT_1.id X) :=
    (RELAT_2.def9 (RELAT_1.id X)).mpr fun x hx =>
      (RELAT_1.def10 X x x).mpr
        ⟨Eq.subst (motive := fun s => x ∈ s) hfld hx, rfl⟩
  have htrans : RELAT_2.isTransitive (RELAT_1.id X) :=
    (RELAT_2.def16 (RELAT_1.id X)).mpr fun x y z hx hy hz hxy hyz => by
      have hyx : y = x := ((RELAT_1.def10 X x y).mp hxy).2.symm
      have hzy : z = y := ((RELAT_1.def10 X y z).mp hyz).2.symm
      exact Eq.subst (motive := fun t => TARSKI.pair x t ∈ RELAT_1.id X) hzy.symm hxy
  have hanti : RELAT_2.isAntisymmetric (RELAT_1.id X) :=
    (RELAT_2.def12 (RELAT_1.id X)).mpr fun x y hx hy hxy hyx =>
      (RELAT_1.def10 X x y).mp hxy |>.2
  exact ⟨⟨hrefl, htrans⟩, ⟨hrefl, htrans, hanti⟩⟩

theorem th28 {R X : TarskiSet.{u}} (h : WELLORD1.wellOrders R X) :
    quasiOrders R X ∧ partiallyOrders R X ∧ linearlyOrders R X :=
  ⟨⟨h.1, h.2.1⟩, ⟨h.1, h.2.1, h.2.2.1⟩, ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩⟩

theorem th29 {R X : TarskiSet.{u}} (h : linearlyOrders R X) :
    quasiOrders R X ∧ partiallyOrders R X :=
  ⟨⟨h.1, h.2.1⟩, ⟨h.1, h.2.1, h.2.2.1⟩⟩

theorem th30 {R X : TarskiSet.{u}} (h : partiallyOrders R X) : quasiOrders R X :=
  ⟨h.1, h.2.1⟩

theorem th31 {R : TarskiSet.{u}} (h : isQuasiOrder R) :
    quasiOrders R (RELAT_1.field R) :=
  ⟨(RELAT_2.def9 R).mp h.1, (RELAT_2.def16 R).mp h.2⟩

theorem th32 {R X Y : TarskiSet.{u}} (h : quasiOrders R Y) (hY : X ⊆ Y) :
    quasiOrders R X :=
  ⟨th8 h.1 hY, th10 h.2 hY⟩

private theorem lm6 {R X : TarskiSet.{u}} (hrefl : RELAT_2.isReflexiveIn R X) :
    RELAT_2.isReflexive (WELLORD1.restrict2 R X) :=
  (RELAT_2.def9 (WELLORD1.restrict2 R X)).mpr fun x hx =>
    (WELLORD1.restrict2_iff R X x x).mpr
      ⟨hrefl x (WELLORD1.th12 hx).2,
        (WELLORD1.th12 hx).2,
        (WELLORD1.th12 hx).2⟩

private theorem lm7 {R X : TarskiSet.{u}} (htrans : RELAT_2.isTransitiveIn R X) :
    RELAT_2.isTransitive (WELLORD1.restrict2 R X) :=
  (RELAT_2.def16 (WELLORD1.restrict2 R X)).mpr fun x y z hx hy hz hxy hyz =>
    (WELLORD1.restrict2_iff R X x z).mpr
      ⟨htrans x y z (WELLORD1.th12 hx).2
          (WELLORD1.th12 hy).2
          (WELLORD1.th12 hz).2
          ((WELLORD1.restrict2_iff R X x y).mp hxy).1
          ((WELLORD1.restrict2_iff R X y z).mp hyz).1,
        (WELLORD1.th12 hx).2,
        (WELLORD1.th12 hz).2⟩

private theorem lm8 {R X : TarskiSet.{u}} (hanti : RELAT_2.isAntisymmetricIn R X) :
    RELAT_2.isAntisymmetric (WELLORD1.restrict2 R X) :=
  (RELAT_2.def12 (WELLORD1.restrict2 R X)).mpr fun x y hx hy hxy hyx =>
    hanti x y (WELLORD1.th12 hx).2
      (WELLORD1.th12 hy).2
      ((WELLORD1.restrict2_iff R X x y).mp hxy).1
      ((WELLORD1.restrict2_iff R X y x).mp hyx).1

private theorem lm9 {R X : TarskiSet.{u}} (hconn : RELAT_2.isConnectedIn R X) :
    RELAT_2.isConnected (WELLORD1.restrict2 R X) :=
  (RELAT_2.def14 (WELLORD1.restrict2 R X)).mpr fun x y hx hy hne =>
    Or.elim (hconn x y (WELLORD1.th12 hx).2
        (WELLORD1.th12 hy).2 hne)
      (fun hxy => Or.inl ((WELLORD1.restrict2_iff R X x y).mpr
        ⟨hxy, (WELLORD1.th12 hx).2, (WELLORD1.th12 hy).2⟩))
      (fun hyx => Or.inr ((WELLORD1.restrict2_iff R X y x).mpr
        ⟨hyx, (WELLORD1.th12 hy).2, (WELLORD1.th12 hx).2⟩))

theorem th33 {R X : TarskiSet.{u}} (h : quasiOrders R X) :
    isQuasiOrder (WELLORD1.restrict2 R X) :=
  ⟨lm6 h.1, lm7 h.2⟩

theorem th34 {R : TarskiSet.{u}} (h : isPartialOrder R) :
    partiallyOrders R (RELAT_1.field R) :=
  ⟨(RELAT_2.def9 R).mp h.1, (RELAT_2.def16 R).mp h.2.1, (RELAT_2.def12 R).mp h.2.2⟩

theorem th35 {R X Y : TarskiSet.{u}} (h : partiallyOrders R Y) (hY : X ⊆ Y) :
    partiallyOrders R X :=
  ⟨th8 h.1 hY, th10 h.2.1 hY, th9 h.2.2 hY⟩

theorem th36 {R X : TarskiSet.{u}} (h : partiallyOrders R X) :
    isPartialOrder (WELLORD1.restrict2 R X) :=
  ⟨lm6 h.1, lm7 h.2.1, lm8 h.2.2⟩

private theorem lm10 {R X Y : TarskiSet.{u}}
    (hconn : RELAT_2.isConnectedIn R X) (hY : Y ⊆ X) :
    RELAT_2.isConnectedIn R Y :=
  fun x y hx hy hne => hconn x y (hY x hx) (hY y hy) hne

theorem th37 {R : TarskiSet.{u}} (h : isLinearOrder R) :
    linearlyOrders R (RELAT_1.field R) :=
  ⟨(RELAT_2.def9 R).mp h.1, (RELAT_2.def16 R).mp h.2.1,
    (RELAT_2.def12 R).mp h.2.2.1, (RELAT_2.def14 R).mp h.2.2.2⟩

theorem th38 {R X Y : TarskiSet.{u}} (h : linearlyOrders R Y) (hY : X ⊆ Y) :
    linearlyOrders R X :=
  ⟨th8 h.1 hY, th10 h.2.1 hY, th9 h.2.2.1 hY, lm10 h.2.2.2 hY⟩

theorem th39 {R X : TarskiSet.{u}} (h : linearlyOrders R X) :
    isLinearOrder (WELLORD1.restrict2 R X) :=
  ⟨lm6 h.1, lm7 h.2.1, lm8 h.2.2.1, lm9 h.2.2.2⟩

private theorem lm11 {R X : TarskiSet.{u}} (hrefl : RELAT_2.isReflexiveIn R X) :
    RELAT_2.isReflexiveIn (RELAT_1.converse R) X :=
  fun x hx => (RELAT_1.def7 R x x).mpr (hrefl x hx)

private theorem lm12 {R X : TarskiSet.{u}} (htrans : RELAT_2.isTransitiveIn R X) :
    RELAT_2.isTransitiveIn (RELAT_1.converse R) X :=
  fun x y z hx hy hz hxy hyz =>
    (RELAT_1.def7 R x z).mpr
      (htrans z y x hz hy hx ((RELAT_1.def7 R y z).mp hyz) ((RELAT_1.def7 R x y).mp hxy))

private theorem lm13 {R X : TarskiSet.{u}} (hanti : RELAT_2.isAntisymmetricIn R X) :
    RELAT_2.isAntisymmetricIn (RELAT_1.converse R) X :=
  fun x y hx hy hxy hyx =>
    hanti x y hx hy ((RELAT_1.def7 R y x).mp hyx) ((RELAT_1.def7 R x y).mp hxy)

private theorem lm14 {R X : TarskiSet.{u}} (hconn : RELAT_2.isConnectedIn R X) :
    RELAT_2.isConnectedIn (RELAT_1.converse R) X :=
  fun x y hx hy hne =>
    Or.elim (hconn x y hx hy hne)
      (fun hxy => Or.inr ((RELAT_1.converse_char R y x).mpr
        ⟨RELAT_1.pair_mem_rng hxy, RELAT_1.pair_mem_dom hxy, hxy⟩))
      (fun hyx => Or.inl ((RELAT_1.converse_char R x y).mpr
        ⟨RELAT_1.pair_mem_rng hyx, RELAT_1.pair_mem_dom hyx, hyx⟩))

theorem th40 {R X : TarskiSet.{u}} (h : quasiOrders R X) :
    quasiOrders (RELAT_1.converse R) X :=
  ⟨lm11 h.1, lm12 h.2⟩

theorem th41 {R X : TarskiSet.{u}} (h : partiallyOrders R X) :
    partiallyOrders (RELAT_1.converse R) X :=
  ⟨lm11 h.1, lm12 h.2.1, lm13 h.2.2⟩

theorem th42 {R X : TarskiSet.{u}} (h : linearlyOrders R X) :
    linearlyOrders (RELAT_1.converse R) X :=
  ⟨lm11 h.1, lm12 h.2.1, lm13 h.2.2.1, lm14 h.2.2.2⟩

theorem th43 {O X : TarskiSet.{u}} (hO : isOrderOf O X) : quasiOrders O X := by
  have hfld : RELAT_1.field O = X := lm2 hO.1 hO.2.1
  exact ⟨fun x hx => hO.2.2.1 x (Eq.subst (motive := fun s => x ∈ s) hfld.symm hx),
    fun x y z hx hy hz hxy hyz =>
      hO.2.2.2.2 x y z
        (Eq.subst (motive := fun s => x ∈ s) hfld.symm hx)
        (Eq.subst (motive := fun s => y ∈ s) hfld.symm hy)
        (Eq.subst (motive := fun s => z ∈ s) hfld.symm hz) hxy hyz⟩

theorem th44 {O X : TarskiSet.{u}} (hO : isOrderOf O X) : partiallyOrders O X := by
  have hfld : RELAT_1.field O = X := lm2 hO.1 hO.2.1
  exact ⟨fun x hx => hO.2.2.1 x (Eq.subst (motive := fun s => x ∈ s) hfld.symm hx),
    fun x y z hx hy hz hxy hyz =>
      hO.2.2.2.2 x y z
        (Eq.subst (motive := fun s => x ∈ s) hfld.symm hx)
        (Eq.subst (motive := fun s => y ∈ s) hfld.symm hy)
        (Eq.subst (motive := fun s => z ∈ s) hfld.symm hz) hxy hyz,
    fun x y hx hy hxy hyx =>
      hO.2.2.2.1 x y
        (Eq.subst (motive := fun s => x ∈ s) hfld.symm hx)
        (Eq.subst (motive := fun s => y ∈ s) hfld.symm hy) hxy hyx⟩

theorem th45 {R X : TarskiSet.{u}} (hpart : partiallyOrders R X) :
    isOrderOf (WELLORD1.restrict2 R X) X := by
  let S := WELLORD1.restrict2 R X
  have hR : RELSET_1.isRelationOf S X X := restrict2_isRelationOf R X
  have hrefl : RELAT_2.isReflexiveIn R X := hpart.1
  have htrans : RELAT_2.isTransitiveIn R X := hpart.2.1
  have hanti : RELAT_2.isAntisymmetricIn R X := hpart.2.2
  have hSreflIn : RELAT_2.isReflexiveIn S X := fun x hx =>
    (WELLORD1.restrict2_iff R X x x).mpr ⟨hrefl x hx, hx, hx⟩
  have hSrefl : RELAT_2.isReflexive S := lm6 hrefl
  have hStrans : RELAT_2.isTransitive S := lm7 htrans
  have hSanti : RELAT_2.isAntisymmetric S := lm8 hanti
  have hfield : RELAT_1.field S = X := (th13 hR hSreflIn).2
  have hdom : RELAT_1.dom S = X := (th13 hR hSreflIn).1
  exact ⟨hR, hdom, hSrefl, hSanti, hStrans⟩

theorem th46 {R X : TarskiSet.{u}} (h : linearlyOrders R X) :
    isOrderOf (WELLORD1.restrict2 R X) X :=
  th45 (th29 h).2

theorem th47 {R X : TarskiSet.{u}} (h : WELLORD1.wellOrders R X) :
    isOrderOf (WELLORD1.restrict2 R X) X :=
  th45 (th28 h).2.1

theorem th48 (X : TarskiSet.{u}) :
    quasiOrders (RELAT_1.id X) X ∧ partiallyOrders (RELAT_1.id X) X := by
  have hfield : RELAT_1.field (RELAT_1.id X) = X := by
    apply TARSKI.extensionality
    intro x
    constructor
    · intro hx
      rcases (XBOOLE_0.def3 (RELAT_1.dom (RELAT_1.id X)) (RELAT_1.rng (RELAT_1.id X)) x).mp hx with
          hd | hr
      · exact Eq.subst (motive := fun s => x ∈ s) (RELAT_1.id_dom X) hd
      · exact Eq.subst (motive := fun s => x ∈ s) (RELAT_1.id_rng X) hr
    · intro hx
      exact (XBOOLE_0.def3 (RELAT_1.dom (RELAT_1.id X)) (RELAT_1.rng (RELAT_1.id X)) x).mpr
        (Or.inl (Eq.subst (motive := fun s => x ∈ s) (RELAT_1.id_dom X).symm hx))
  have hquasi := th31 (id_isQuasiPartial X).1
  have hpart := th34 (id_isQuasiPartial X).2
  exact ⟨Eq.subst (motive := fun s => quasiOrders (RELAT_1.id X) s) hfield hquasi,
    Eq.subst (motive := fun s => partiallyOrders (RELAT_1.id X) s) hfield hpart⟩

/-! ## Zorn properties and extrema (`ORDERS_1:def 9`–`def 14`) -/

/-- `ORDERS_1:Def9`. -/
def hasUpperZornProperty (X R : TarskiSet.{u}) : Prop :=
  ∀ Y, Y ⊆ X → isLinearOrder (WELLORD1.restrict2 R Y) →
    ∃ x, x ∈ X ∧ ∀ y, y ∈ Y → TARSKI.pair y x ∈ R

/-- `ORDERS_1:Def10`. -/
def hasLowerZornProperty (X R : TarskiSet.{u}) : Prop :=
  ∀ Y, Y ⊆ X → isLinearOrder (WELLORD1.restrict2 R Y) →
    ∃ x, x ∈ X ∧ ∀ y, y ∈ Y → TARSKI.pair x y ∈ R

theorem def9 (X R : TarskiSet.{u}) :
    hasUpperZornProperty X R ↔
      ∀ Y, Y ⊆ X → isLinearOrder (WELLORD1.restrict2 R Y) →
        ∃ x, x ∈ X ∧ ∀ y, y ∈ Y → TARSKI.pair y x ∈ R :=
  Iff.rfl

theorem def10 (X R : TarskiSet.{u}) :
    hasLowerZornProperty X R ↔
      ∀ Y, Y ⊆ X → isLinearOrder (WELLORD1.restrict2 R Y) →
        ∃ x, x ∈ X ∧ ∀ y, y ∈ Y → TARSKI.pair x y ∈ R :=
  Iff.rfl

/-- `ORDERS_1:Def11`. -/
def isMaximalIn (x R : TarskiSet.{u}) : Prop :=
  x ∈ RELAT_1.field R ∧
    ¬ ∃ y, y ∈ RELAT_1.field R ∧ y ≠ x ∧ TARSKI.pair x y ∈ R

/-- `ORDERS_1:Def12`. -/
def isMinimalIn (x R : TarskiSet.{u}) : Prop :=
  x ∈ RELAT_1.field R ∧
    ¬ ∃ y, y ∈ RELAT_1.field R ∧ y ≠ x ∧ TARSKI.pair y x ∈ R

/-- `ORDERS_1:Def13`. -/
def isSuperiorOf (x R : TarskiSet.{u}) : Prop :=
  x ∈ RELAT_1.field R ∧
    ∀ y, y ∈ RELAT_1.field R → y ≠ x → TARSKI.pair y x ∈ R

/-- `ORDERS_1:Def14`. -/
def isInferiorOf (x R : TarskiSet.{u}) : Prop :=
  x ∈ RELAT_1.field R ∧
    ∀ y, y ∈ RELAT_1.field R → y ≠ x → TARSKI.pair x y ∈ R

theorem def11 (x R : TarskiSet.{u}) :
    isMaximalIn x R ↔
      x ∈ RELAT_1.field R ∧
        ¬ ∃ y, y ∈ RELAT_1.field R ∧ y ≠ x ∧ TARSKI.pair x y ∈ R :=
  Iff.rfl

theorem def12 (x R : TarskiSet.{u}) :
    isMinimalIn x R ↔
      x ∈ RELAT_1.field R ∧
        ¬ ∃ y, y ∈ RELAT_1.field R ∧ y ≠ x ∧ TARSKI.pair y x ∈ R :=
  Iff.rfl

theorem def13 (x R : TarskiSet.{u}) :
    isSuperiorOf x R ↔
      x ∈ RELAT_1.field R ∧
        ∀ y, y ∈ RELAT_1.field R → y ≠ x → TARSKI.pair y x ∈ R :=
  Iff.rfl

theorem def14 (x R : TarskiSet.{u}) :
    isInferiorOf x R ↔
      x ∈ RELAT_1.field R ∧
        ∀ y, y ∈ RELAT_1.field R → y ≠ x → TARSKI.pair x y ∈ R :=
  Iff.rfl

private theorem restrict2_isRelation (R X : TarskiSet.{u}) :
    RELAT_1.isRelation (WELLORD1.restrict2 R X) :=
  RELAT_1.subset_isRelation (RELAT_1.product_isRelation X X)
    (fun z hz => ((XBOOLE_0.def4 R (ZFMISC_1.product X X) z).mp hz).2)

private theorem lm4 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    R ⊆ ZFMISC_1.product (RELAT_1.field R) (RELAT_1.field R) :=
  fun p hp => by
    obtain ⟨x, y, hpEq⟩ := hR p hp
    have ⟨hx, hy⟩ := RELAT_1.th15 (Eq.subst (motive := fun s => s ∈ R) hpEq hp)
    exact hpEq ▸ ZFMISC_1.th87.mpr ⟨hx, hy⟩

private theorem lm5 {R X : TarskiSet.{u}}
    (hrefl : RELAT_2.isReflexive R) (hX : X ⊆ RELAT_1.field R) :
    RELAT_1.field (WELLORD1.restrict2 R X) = X := by
  apply TARSKI.extensionality
  intro y
  constructor
  · intro hy
    exact (WELLORD1.th12 hy).2
  · intro hy
    have hp : TARSKI.pair y y ∈ ZFMISC_1.product X X :=
      ZFMISC_1.th87.mpr ⟨hy, hy⟩
    have hpR : TARSKI.pair y y ∈ R :=
      (RELAT_2.def1 R (RELAT_1.field R)).mp hrefl y (hX y hy)
    exact (RELAT_1.th15 (a := y) (b := y) (R := WELLORD1.restrict2 R X)
      ((WELLORD1.restrict2_iff R X y y).mpr ⟨hpR, hy, hy⟩)).1

private theorem lm15 {R X : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    RELAT_1.converse (WELLORD1.restrict2 R X) =
      WELLORD1.restrict2 (RELAT_1.converse R) X := by
  refine RELAT_1.rel_eq (RELAT_1.converse_isRelation (WELLORD1.restrict2 R X))
    (restrict2_isRelation (RELAT_1.converse R) X) ?_
  intro x y
  constructor
  · intro h
    have h' := (RELAT_1.converse_char (WELLORD1.restrict2 R X) x y).mp h
    have ⟨hp, hy, hx⟩ := (WELLORD1.restrict2_iff R X y x).mp h'.2.2
    exact (WELLORD1.restrict2_iff (RELAT_1.converse R) X x y).mpr
      ⟨(RELAT_1.def7 R x y).mpr hp, hx, hy⟩
  · intro h
    have ⟨hp, hx, hy⟩ := (WELLORD1.restrict2_iff (RELAT_1.converse R) X x y).mp h
    have hp' : TARSKI.pair y x ∈ WELLORD1.restrict2 R X :=
      (WELLORD1.restrict2_iff R X y x).mpr ⟨(RELAT_1.def7 R x y).mp hp, hy, hx⟩
    exact (RELAT_1.converse_char (WELLORD1.restrict2 R X) x y).mpr
      ⟨RELAT_1.pair_mem_rng hp', RELAT_1.pair_mem_dom hp', hp'⟩

private theorem lm16 (R : TarskiSet.{u}) :
    WELLORD1.restrict2 R (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) := by
  apply RELAT_1.rel_eq (restrict2_isRelation R (∅ : TarskiSet.{u}))
    (RELAT_1.empty_isRelation)
  intro x y
  constructor
  · intro h
    rcases (WELLORD1.restrict2_iff R (∅ : TarskiSet.{u}) x y).mp h with ⟨_, hx, _⟩
    exact False.elim ((XBOOLE_0.empty_iff x).mp hx)
  · intro h
    exact False.elim ((XBOOLE_0.empty_iff (TARSKI.pair x y)).mp h)

private theorem lm17 {R X Y : TarskiSet.{u}} (h : WELLORD1.wellOrders R X) (hY : Y ⊆ X) :
    WELLORD1.wellOrders R Y := by
  rcases h with ⟨hrefl, htrans, hanti, hconn, hwf⟩
  refine ⟨th8 hrefl hY, th10 htrans hY, th9 hanti hY, lm10 hconn hY, ?_⟩
  intro Z hZ hZne
  have hZsub : Z ⊆ X := XBOOLE_1.th1 hZ hY
  exact hwf Z hZsub hZne

/-- `ORDERS_1:Th49`. -/
theorem th49 {X R : TarskiSet.{u}} (h : hasUpperZornProperty X R) :
    X ≠ (∅ : TarskiSet.{u}) := by
  have hlin : isLinearOrder (WELLORD1.restrict2 R (∅ : TarskiSet.{u})) :=
    Eq.subst (motive := isLinearOrder) (lm16 R).symm empty_isQuasiOrder.2.2.1
  obtain ⟨x, hx, _⟩ := h (∅ : TarskiSet.{u}) XBOOLE_1.th2 hlin
  exact fun hX => (XBOOLE_0.empty_iff x).mp (Eq.subst (motive := fun s => x ∈ s) hX hx)

/-- `ORDERS_1:50`. -/
theorem th50 {X R : TarskiSet.{u}} (h : hasLowerZornProperty X R) :
    X ≠ (∅ : TarskiSet.{u}) := by
  have hlin : isLinearOrder (WELLORD1.restrict2 R (∅ : TarskiSet.{u})) :=
    Eq.subst (motive := isLinearOrder) (lm16 R).symm empty_isQuasiOrder.2.2.1
  obtain ⟨x, hx, _⟩ := h (∅ : TarskiSet.{u}) XBOOLE_1.th2 hlin
  exact fun hX => (XBOOLE_0.empty_iff x).mp (Eq.subst (motive := fun s => x ∈ s) hX hx)

/-- `ORDERS_1:Th51`. -/
theorem th51 {X R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    hasUpperZornProperty X R ↔ hasLowerZornProperty X (RELAT_1.converse R) := by
  constructor
  · intro hUP Y hY hlin
    have hlin' : isLinearOrder (WELLORD1.restrict2 R Y) := by
      have h1 := th18 hlin
      have h2 : RELAT_1.converse (WELLORD1.restrict2 (RELAT_1.converse R) Y) =
          WELLORD1.restrict2 R Y := by
        rw [← RELAT_1.converse_involutive (restrict2_isRelation R Y), lm15 hR (X := Y)]
      exact Eq.subst (motive := isLinearOrder) h2 h1
    obtain ⟨x, hx, hbound⟩ := hUP Y hY hlin'
    refine ⟨x, hx, fun y hy => (RELAT_1.def7 R x y).mpr (hbound y hy)⟩
  · intro hLP Y hY hlin
    have hlin' : isLinearOrder (WELLORD1.restrict2 (RELAT_1.converse R) Y) :=
      Eq.subst (motive := isLinearOrder) (lm15 hR (X := Y)) (th18 hlin)
    obtain ⟨x, hx, hbound⟩ := hLP Y hY hlin'
    refine ⟨x, hx, fun y hy => (RELAT_1.def7 R x y).mp (hbound y hy)⟩

/-- `ORDERS_1:52`. -/
theorem th52 {X R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    hasUpperZornProperty X (RELAT_1.converse R) ↔ hasLowerZornProperty X R := by
  calc hasUpperZornProperty X (RELAT_1.converse R)
      ↔ hasLowerZornProperty X (RELAT_1.converse (RELAT_1.converse R)) :=
        th51 (RELAT_1.converse_isRelation R)
    _ ↔ hasLowerZornProperty X R := by
      rw [RELAT_1.converse_involutive hR]

/-- `ORDERS_1:53`. -/
theorem th53 {x R : TarskiSet.{u}} (hinf : isInferiorOf x R) (hanti : RELAT_2.isAntisymmetric R) :
    isMinimalIn x R := by
  have hantiIn : RELAT_2.isAntisymmetricIn R (RELAT_1.field R) :=
    (RELAT_2.def12 R).mp hanti
  refine ⟨hinf.1, fun ⟨y, hy, hyne, hp⟩ => ?_⟩
  have hyx : TARSKI.pair x y ∈ R := hinf.2 y hy hyne
  exact hyne (hantiIn x y hinf.1 hy hyx hp).symm

/-- `ORDERS_1:54`. -/
theorem th54 {x R : TarskiSet.{u}} (hsup : isSuperiorOf x R) (hanti : RELAT_2.isAntisymmetric R) :
    isMaximalIn x R := by
  have hantiIn : RELAT_2.isAntisymmetricIn R (RELAT_1.field R) :=
    (RELAT_2.def12 R).mp hanti
  refine ⟨hsup.1, fun ⟨y, hy, hyne, hp⟩ => ?_⟩
  have hyx : TARSKI.pair y x ∈ R := hsup.2 y hy hyne
  exact hyne (hantiIn x y hsup.1 hy hp hyx).symm

/-- `ORDERS_1:55`. -/
theorem th55 {x R : TarskiSet.{u}} (hmin : isMinimalIn x R) (hconn : RELAT_2.isConnected R) :
    isInferiorOf x R := by
  have hconnIn : RELAT_2.isConnectedIn R (RELAT_1.field R) :=
    (RELAT_2.def14 R).mp hconn
  refine ⟨hmin.1, fun y hy hyne => Or.elim (hconnIn x y hmin.1 hy (Ne.symm hyne))
    (fun hxy => hxy) fun hp => False.elim (hmin.2 ⟨y, hy, hyne, hp⟩)⟩

/-- `ORDERS_1:56`. -/
theorem th56 {x R : TarskiSet.{u}} (hmax : isMaximalIn x R) (hconn : RELAT_2.isConnected R) :
    isSuperiorOf x R := by
  have hconnIn : RELAT_2.isConnectedIn R (RELAT_1.field R) :=
    (RELAT_2.def14 R).mp hconn
  refine ⟨hmax.1, fun y hy hyne => Or.elim (hconnIn x y hmax.1 hy (Ne.symm hyne))
    (fun hp => False.elim (hmax.2 ⟨y, hy, hyne, hp⟩)) (fun hxy => hxy)⟩

/-- `ORDERS_1:57`. -/
theorem th57 {x X R : TarskiSet.{u}} (hx : x ∈ X) (hsup : isSuperiorOf x R)
    (hX : X ⊆ RELAT_1.field R) (hrefl : RELAT_2.isReflexive R) :
    hasUpperZornProperty X R := by
  intro Y hY hlin
  refine ⟨x, hx, fun y hy => ?_⟩
  have hyX : y ∈ X := hY y hy
  by_cases h : y = x
  · rw [h]
    exact (RELAT_2.def1 R (RELAT_1.field R)).mp hrefl x (hX x hx)
  · exact hsup.2 y (hX y hyX) h

/-- `ORDERS_1:58`. -/
theorem th58 {x X R : TarskiSet.{u}} (hx : x ∈ X) (hinf : isInferiorOf x R)
    (hX : X ⊆ RELAT_1.field R) (hrefl : RELAT_2.isReflexive R) :
    hasLowerZornProperty X R := by
  intro Y hY hlin
  refine ⟨x, hx, fun y hy => ?_⟩
  have hyX : y ∈ X := hY y hy
  by_cases h : y = x
  · rw [h]
    exact (RELAT_2.def1 R (RELAT_1.field R)).mp hrefl x (hX x hx)
  · exact hinf.2 y (hX y hyX) h

/-- `ORDERS_1:Th59`. -/
theorem th59 {x R : TarskiSet.{u}} :
    isMinimalIn x R ↔ isMaximalIn x (RELAT_1.converse R) := by
  have hfld : RELAT_1.field R = RELAT_1.field (RELAT_1.converse R) := RELAT_1.th21
  constructor
  · intro ⟨hx, hmin⟩
    refine ⟨Eq.subst (motive := fun s => x ∈ s) hfld hx, fun ⟨y, hy, hyne, hp⟩ => ?_⟩
    have hp' : TARSKI.pair y x ∈ R := (RELAT_1.def7 R x y).mp hp
    exact hmin ⟨y, Eq.subst (motive := fun s => y ∈ s) hfld.symm hy, hyne, hp'⟩
  · intro ⟨hx, hmax⟩
    refine ⟨Eq.subst (motive := fun s => x ∈ s) hfld.symm hx, fun ⟨y, hy, hyne, hp⟩ => ?_⟩
    exact hmax ⟨y, Eq.subst (motive := fun s => y ∈ s) hfld hy, hyne,
      (RELAT_1.def7 R x y).mpr hp⟩

/-- `ORDERS_1:60`. -/
theorem th60 {x R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    isMinimalIn x (RELAT_1.converse R) ↔ isMaximalIn x R :=
  ⟨fun h => Eq.subst (motive := fun s => isMaximalIn x s) (RELAT_1.converse_involutive hR)
      ((th59 (x := x) (R := RELAT_1.converse R)).mp h),
    fun h => (th59 (x := x) (R := RELAT_1.converse R)).mpr
      (Eq.subst (motive := fun s => isMaximalIn x s) (RELAT_1.converse_involutive hR).symm h)⟩

/-- `ORDERS_1:61`. -/
theorem th61 {x R : TarskiSet.{u}} :
    isInferiorOf x R ↔ isSuperiorOf x (RELAT_1.converse R) := by
  have hfld : RELAT_1.field R = RELAT_1.field (RELAT_1.converse R) := RELAT_1.th21
  constructor
  · intro ⟨hx, hinf⟩
    refine ⟨Eq.subst (motive := fun s => x ∈ s) hfld hx, fun y hy hyne => ?_⟩
    have hp : TARSKI.pair x y ∈ R :=
      hinf y (Eq.subst (motive := fun s => y ∈ s) hfld.symm hy) hyne
    exact (RELAT_1.def7 R y x).mpr hp
  · intro ⟨hx, hsup⟩
    refine ⟨Eq.subst (motive := fun s => x ∈ s) hfld.symm hx, fun y hy hyne => ?_⟩
    exact (RELAT_1.def7 R y x).mp (hsup y (Eq.subst (motive := fun s => y ∈ s) hfld hy) hyne)

/-- `ORDERS_1:62`. -/
theorem th62 {x R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    isInferiorOf x (RELAT_1.converse R) ↔ isSuperiorOf x R :=
  ⟨fun h => Eq.subst (motive := fun s => isSuperiorOf x s) (RELAT_1.converse_involutive hR)
      ((th61 (x := x) (R := RELAT_1.converse R)).mp h),
    fun h => (th61 (x := x) (R := RELAT_1.converse R)).mpr
      (Eq.subst (motive := fun s => isSuperiorOf x s) (RELAT_1.converse_involutive hR).symm h)⟩

/-! ## Kuratowski–Zorn helpers (`ORDERS_1:Th63` area) -/

private noncomputable def theElement (S : TarskiSet.{u}) (h : S ≠ (∅ : TarskiSet.{u})) : TarskiSet.{u} :=
  Classical.choose (exists_mem_of_ne h)

private theorem theElement_spec (S : TarskiSet.{u}) (h : S ≠ (∅ : TarskiSet.{u})) :
    theElement S h ∈ S :=
  Classical.choose_spec (exists_mem_of_ne h)

private def isChainValue (R L d : TarskiSet.{u}) : Prop :=
  ∀ x, x ∈ RELAT_1.rng L → x ≠ d ∧ TARSKI.pair x d ∈ R

private noncomputable def chainSet (D R L : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (XBOOLE_0.sch_separation D (isChainValue R L))

private theorem chainSet_spec (D R L : TarskiSet.{u}) (d : TarskiSet.{u}) :
    d ∈ chainSet D R L ↔ d ∈ D ∧ isChainValue R L d :=
  Classical.choose_spec (XBOOLE_0.sch_separation D (isChainValue R L)) d

private theorem chainSet_sub (D R L : TarskiSet.{u}) : chainSet D R L ⊆ D :=
  fun d hd => (chainSet_spec D R L d).mp hd |>.1

private def gChoicePred (D f x y : TarskiSet.{u}) : Prop :=
  (x ≠ (∅ : TarskiSet.{u}) ∧ y = FUNCT_1.apply f x) ∨
    (x = (∅ : TarskiSet.{u}) ∧ y = D)

private theorem gChoicePred_unique (D f : TarskiSet.{u})
    (x y1 y2 : TarskiSet.{u}) (_hx : x ∈ ZFMISC_1.bool D)
    (h1 : gChoicePred D f x y1) (h2 : gChoicePred D f x y2) : y1 = y2 := by
  rcases h1 with hne | h0
  · rcases h2 with hne' | h0'
    · exact hne.2.trans hne'.2.symm
    · exact False.elim (hne.1 h0'.1)
  · rcases h2 with hne' | h0'
    · exact False.elim (hne'.1 h0.1)
    · exact h0.2.trans h0'.2.symm

private theorem gChoicePred_exists (D f : TarskiSet.{u}) (x : TarskiSet.{u})
    (hx : x ∈ ZFMISC_1.bool D) : ∃ y, gChoicePred D f x y := by
  by_cases h0 : x = (∅ : TarskiSet.{u})
  · exact ⟨D, Or.inr ⟨h0, rfl⟩⟩
  · exact ⟨FUNCT_1.apply f x, Or.inl ⟨h0, rfl⟩⟩

private def ON (R g D : TarskiSet.{u}) (A d : TarskiSet.{u}) : Prop :=
  ORDINAL1.isOrdinal A ∧
  ∃ L, FUNCT_1.isFunction L ∧
    d = FUNCT_1.apply g (chainSet D R L) ∧
    RELAT_1.dom L = A ∧
    ∀ B L1, B ∈ A → L1 = RELAT_1.restrict L B →
      FUNCT_1.apply L B = FUNCT_1.apply g (chainSet D R L1)

private noncomputable def chainH (R g D : TarskiSet.{u}) (L1 : TarskiSet.{u}) : TarskiSet.{u} :=
  FUNCT_1.apply g (chainSet D R L1)

private def OM (R g D A : TarskiSet.{u}) : Prop :=
  ON R g D A D

private theorem ON_L_isTSequence {L A : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hf : FUNCT_1.isFunction L) (hdom : RELAT_1.dom L = A) :
    ORDINAL1.isTSequence L :=
  ⟨hf, Eq.subst (motive := ORDINAL1.isOrdinal) hdom.symm hA⟩

private theorem ON_restrict_values {R g D L A B : TarskiSet.{u}}
    (hdom : RELAT_1.dom L = A)
    (hrec : ∀ C L1, C ∈ A → L1 = RELAT_1.restrict L C →
      FUNCT_1.apply L C = chainH R g D L1)
    (hB : B ∈ A) :
    FUNCT_1.apply L B = chainH R g D (RELAT_1.restrict L B) :=
  hrec B (RELAT_1.restrict L B) hB rfl

private theorem ON_restrict_eq {R g D : TarskiSet.{u}}
    {L1 L2 A B C : TarskiSet.{u}}
    (hC : ORDINAL1.isOrdinal C) (hCsubA : C ⊆ A) (hCsubB : C ⊆ B)
    (hf1 : FUNCT_1.isFunction L1) (hdom1 : RELAT_1.dom L1 = A)
    (hrec1 : ∀ B' L1', B' ∈ A → L1' = RELAT_1.restrict L1 B' →
      FUNCT_1.apply L1 B' = chainH R g D L1')
    (hf2 : FUNCT_1.isFunction L2) (hdom2 : RELAT_1.dom L2 = B)
    (hrec2 : ∀ B' L2', B' ∈ B → L2' = RELAT_1.restrict L2 B' →
      FUNCT_1.apply L2 B' = chainH R g D L2') :
    RELAT_1.restrict L1 C = RELAT_1.restrict L2 C := by
  have hind : ∀ A1, ORDINAL1.isOrdinal A1 →
      (A1 ⊆ C → RELAT_1.restrict L1 A1 = RELAT_1.restrict L2 A1) :=
    ORDINAL1.sch_TransfiniteInd
      (fun A1 => A1 ⊆ C → RELAT_1.restrict L1 A1 = RELAT_1.restrict L2 A1)
      (fun A1 hA1 hIH hA1C => by
        have hA1subA : A1 ⊆ A := XBOOLE_1.th1 hA1C hCsubA
        have hA1subB : A1 ⊆ B := XBOOLE_1.th1 hA1C hCsubB
        have hdom1' : RELAT_1.dom (RELAT_1.restrict L1 A1) = A1 :=
          RELAT_1.th62 (R := L1) (X := A1)
            (Eq.subst (motive := fun s => A1 ⊆ s) hdom1.symm hA1subA)
        have hdom2' : RELAT_1.dom (RELAT_1.restrict L2 A1) = A1 :=
          RELAT_1.th62 (R := L2) (X := A1)
            (Eq.subst (motive := fun s => A1 ⊆ s) hdom2.symm hA1subB)
        apply FUNCT_1.th2
          (FUNCT_1.restrict_isFunction hf1) (FUNCT_1.restrict_isFunction hf2)
        · exact hdom1'.trans hdom2'.symm
        · intro x hx
          have hxA1 : x ∈ A1 := Eq.subst (motive := fun s => x ∈ s) hdom1' hx
          have hxC : x ∈ C := hA1C x hxA1
          have hxA : x ∈ A := hCsubA x hxC
          have hxB : x ∈ B := hCsubB x hxC
          have hxsubC : x ⊆ C := hC.1 x hxC
          have hrest : RELAT_1.restrict L1 x = RELAT_1.restrict L2 x :=
            hIH x hxA1 hxsubC
          have h1 := FUNCT_1.th49 hf1.2 (X := A1) (x := x) hxA1
          have h2 := FUNCT_1.th49 hf2.2 (X := A1) (x := x) hxA1
          have hv1 := ON_restrict_values (R := R) (g := g) (D := D) hdom1 hrec1 hxA
          have hv2 := ON_restrict_values (R := R) (g := g) (D := D) hdom2 hrec2 hxB
          calc FUNCT_1.apply (RELAT_1.restrict L1 A1) x
              = FUNCT_1.apply L1 x := h1
            _ = chainH R g D (RELAT_1.restrict L1 x) := hv1
            _ = chainH R g D (RELAT_1.restrict L2 x) := congrArg (chainH R g D) hrest
            _ = FUNCT_1.apply L2 x := hv2.symm
            _ = FUNCT_1.apply (RELAT_1.restrict L2 A1) x := h2.symm)
  exact hind C hC (fun _ hx => hx)

private theorem ON_unique {R g D A x y : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (h1 : ON R g D A x) (h2 : ON R g D A y) : x = y := by
  obtain ⟨_, L1, hf1, hx, hdom1, hrec1⟩ := h1
  obtain ⟨_, L2, hf2, hy, hdom2, hrec2⟩ := h2
  have hL12 : L1 = L2 :=
    ORDINAL1.sch_TSUniq (chainH R g D) hA
      (ON_L_isTSequence hA hf1 hdom1) (ON_L_isTSequence hA hf2 hdom2)
      hdom1 hdom2 hrec1 hrec2
  rw [hx, hy, hL12]

private theorem ON_at {R g D L A B : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hf : FUNCT_1.isFunction L)
    (hdom : RELAT_1.dom L = A)
    (hrec : ∀ C L1, C ∈ A → L1 = RELAT_1.restrict L C →
      FUNCT_1.apply L C = chainH R g D L1)
    (hB : B ∈ A) :
    ON R g D B (FUNCT_1.apply L B) := by
  have hBord : ORDINAL1.isOrdinal B := ORDINAL1.th13 hA hB
  have hBsub : B ⊆ A := hA.1 B hB
  have hdomK : RELAT_1.dom (RELAT_1.restrict L B) = B :=
    RELAT_1.th62 (R := L) (X := B)
      (Eq.subst (motive := fun s => B ⊆ s) hdom.symm hBsub)
  refine ⟨hBord, RELAT_1.restrict L B, FUNCT_1.restrict_isFunction hf,
    hrec B (RELAT_1.restrict L B) hB rfl, hdomK, ?_⟩
  intro C L1 hC hL1
  have hCsubB : C ⊆ B := hBord.1 C hC
  have hCA : C ∈ A := hBsub C hC
  have hL1eq : L1 = RELAT_1.restrict L C :=
    hL1.trans (FUNCT_1.th51 (f := L) (X := C) (Y := B) hCsubB).2
  have hx : C ∈ RELAT_1.dom (RELAT_1.restrict L B) :=
    Eq.subst (motive := fun s => C ∈ s) hdomK.symm hC
  exact (FUNCT_1.th47 hf.2 hx).trans (hrec C L1 hCA hL1eq)

private theorem ON_domain_unique {R g D d A B : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) (hB : ORDINAL1.isOrdinal B)
    (hg_empty : FUNCT_1.apply g (∅ : TarskiSet.{u}) = D)
    (hg_choice : ∀ {Y : TarskiSet.{u}}, Y ∈ ZFMISC_1.bool D → Y ≠ (∅ : TarskiSet.{u}) →
      FUNCT_1.apply g Y ∈ Y)
    (h1 : ON R g D A d) (h2 : ON R g D B d)
    (hnotOM : ¬ ON R g D A D) : A = B := by
  have hdne : d ≠ D := fun heq => hnotOM (heq ▸ h1)
  obtain ⟨_, L1, hf1, hd1, hdom1, hrec1⟩ := h1
  obtain ⟨_, L2, hf2, hd2, hdom2, hrec2⟩ := h2
  have hcase : ∀ {A' B' L L' : TarskiSet.{u}},
      ORDINAL1.isOrdinal A' → ORDINAL1.isOrdinal B' → B' ∈ A' →
      FUNCT_1.isFunction L → RELAT_1.dom L = A' →
      (∀ C L1, C ∈ A' → L1 = RELAT_1.restrict L C →
        FUNCT_1.apply L C = chainH R g D L1) →
      FUNCT_1.isFunction L' → RELAT_1.dom L' = B' →
      (∀ C L1, C ∈ B' → L1 = RELAT_1.restrict L' C →
        FUNCT_1.apply L' C = chainH R g D L1) →
      d = FUNCT_1.apply g (chainSet D R L) →
      d = FUNCT_1.apply g (chainSet D R L') → False := by
    intro A' B' L L' hA' hB' hBA hfL hdomL hrecL hfL' hdomL' hrecL' hdL hdL'
    have hBsub : B' ⊆ A' := hA'.1 B' hBA
    have hrest : RELAT_1.restrict L B' = RELAT_1.restrict L' B' :=
      ON_restrict_eq (R := R) (g := g) (D := D) hB' hBsub (fun _ hx => hx)
        hfL hdomL hrecL hfL' hdomL' hrecL'
    have hL'eq : RELAT_1.restrict L' B' = L' :=
      RELAT_1.th68 hfL'.1 (fun x hx => Eq.subst (motive := fun s => x ∈ s) hdomL' hx)
    have hLB : FUNCT_1.apply L B' = chainH R g D L' := by
      have h := ON_restrict_values (R := R) (g := g) (D := D) hdomL hrecL hBA
      exact h ▸ (hrest.trans hL'eq) ▸ rfl
    have hdrng : d ∈ RELAT_1.rng L :=
      (FUNCT_1.def3 hfL.2).mpr
        ⟨B', Eq.subst (motive := fun s => B' ∈ s) hdomL.symm hBA, hdL'.trans hLB.symm⟩
    let Y := chainSet D R L
    have hYsub : Y ⊆ D := chainSet_sub D R L
    have hYne : Y ≠ (∅ : TarskiSet.{u}) := fun h0 =>
      hdne (hdL.trans (Eq.subst (motive := fun s => FUNCT_1.apply g s = D) h0.symm hg_empty))
    have hdY : d ∈ Y :=
      Eq.subst (motive := fun s => s ∈ Y) hdL.symm
        (hg_choice ((ZFMISC_1.def1 D Y).mpr hYsub) hYne)
    have hchain : isChainValue R L d := ((chainSet_spec D R L d).mp hdY).2
    exact (hchain d hdrng).1 rfl
  rcases ORDINAL1.th14 hA hB with hAB | heq | hBA
  · exact False.elim (hcase hB hA hAB hf2 hdom2 hrec2 hf1 hdom1 hrec1 hd2 hd1)
  · exact heq
  · exact False.elim (hcase hA hB hBA hf1 hdom1 hrec1 hf2 hdom2 hrec2 hd1 hd2)

private theorem relIncl_partiallyOrders (D : TarskiSet.{u}) :
    partiallyOrders (WELLORD2.RelIncl D) D :=
  Eq.subst (motive := partiallyOrders (WELLORD2.RelIncl D))
    (WELLORD2.RelIncl_field D)
    (th34 ⟨WELLORD2.RelIncl_reflexive D, WELLORD2.RelIncl_transitive D,
      WELLORD2.RelIncl_antisymmetric D⟩)

private theorem g_empty (D f g : TarskiSet.{u})
    (hg : ∀ x, x ∈ ZFMISC_1.bool D → gChoicePred D f x (FUNCT_1.apply g x)) :
    FUNCT_1.apply g (∅ : TarskiSet.{u}) = D := by
  have h0 : (∅ : TarskiSet.{u}) ∈ ZFMISC_1.bool D :=
    (ZFMISC_1.def1 D (∅ : TarskiSet.{u})).mpr XBOOLE_1.th2
  rcases hg (∅ : TarskiSet.{u}) h0 with hne | h0'
  · exact False.elim (hne.1 rfl)
  · exact h0'.2

private theorem g_choice {D f g : TarskiSet.{u}}
    (hf : isChoiceFunctionOf f (BOOL D))
    (hg : ∀ x, x ∈ ZFMISC_1.bool D → gChoicePred D f x (FUNCT_1.apply g x))
    {X : TarskiSet.{u}} (hX : X ∈ ZFMISC_1.bool D) (hXne : X ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.apply g X ∈ X := by
  have hXBOOL : X ∈ BOOL D :=
    (XBOOLE_0.def5 (ZFMISC_1.bool D) (TARSKI.singleton (∅ : TarskiSet.{u})) X).mpr
      ⟨hX, fun h => hXne ((TARSKI.singleton_iff (∅ : TarskiSet.{u}) X).mp h)⟩
  have hfg : FUNCT_1.apply g X = FUNCT_1.apply f X :=
    match hg X hX with
    | Or.inl hne => hne.2
    | Or.inr h0 => False.elim (hXne h0.1)
  have hch : ∀ X, X ∈ BOOL D → FUNCT_1.apply f X ∈ X := And.right hf
  exact Eq.subst (motive := fun s => s ∈ X) hfg.symm (hch X hXBOOL)

private theorem ON_d_mem_D {R g D A d : TarskiSet.{u}}
    (hg_empty : FUNCT_1.apply g (∅ : TarskiSet.{u}) = D)
    (hg_choice : ∀ {Y : TarskiSet.{u}}, Y ∈ ZFMISC_1.bool D → Y ≠ (∅ : TarskiSet.{u}) →
      FUNCT_1.apply g Y ∈ Y)
    (hON : ON R g D A d) (hnotOM : ¬ ON R g D A D) : d ∈ D := by
  have hON' := hON
  obtain ⟨_, L, _, hd, _, _⟩ := hON
  let Y := chainSet D R L
  have hYsub : Y ⊆ D := chainSet_sub D R L
  have hYne : Y ≠ (∅ : TarskiSet.{u}) := fun h0 =>
    hnotOM (by
      have hdD : d = D :=
        hd.trans (Eq.subst (motive := fun s => FUNCT_1.apply g s = D) h0.symm hg_empty)
      exact Eq.subst (motive := fun s => ON R g D A s) hdD hON')
  exact Eq.subst (motive := fun s => s ∈ D) hd.symm
    (hYsub _ (hg_choice (Y := Y) ((ZFMISC_1.def1 D Y).mpr hYsub) hYne))

private theorem eq_of_mem {A B : TarskiSet.{u}} (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  TARSKI.extensionality h

/-! ## Kuratowski–Zorn (`ORDERS_1:Th63`–`Th64`) -/

/-- `ORDERS_1:Th63` (Kuratowski–Zorn Lemma). -/
theorem th63 {R X : TarskiSet.{u}}
    (hpart : partiallyOrders R X)
    (hfld : RELAT_1.field R = X)
    (hZorn : hasUpperZornProperty X R) :
    ∃ x, isMaximalIn x R := by
  let D := X
  have hDne : D ≠ (∅ : TarskiSet.{u}) := th49 hZorn
  have hMne : BOOL D ≠ (∅ : TarskiSet.{u}) := bool_nonempty hDne
  have hMno : (∅ : TarskiSet.{u}) ∉ BOOL D := th1 D
  let f := theChoiceFunction (BOOL D) hMne hMno
  have hf : isChoiceFunctionOf f (BOOL D) := theChoiceFunction_spec (BOOL D) hMne hMno
  obtain ⟨g, hg, hdomg, hgv⟩ :=
    FUNCT_1.sch_FuncEx (ZFMISC_1.bool D) (gChoicePred D f)
      (gChoicePred_unique D f) (gChoicePred_exists D f)
  have hg_spec : ∀ x, x ∈ ZFMISC_1.bool D → gChoicePred D f x (FUNCT_1.apply g x) :=
    fun x hx => hgv x hx
  have hg_empty : FUNCT_1.apply g (∅ : TarskiSet.{u}) = D :=
    g_empty D f g hg_spec
  have hg_choice : ∀ {Y : TarskiSet.{u}}, Y ∈ ZFMISC_1.bool D → Y ≠ (∅ : TarskiSet.{u}) →
      FUNCT_1.apply g Y ∈ Y :=
    fun {Y} hY hYne =>
      g_choice (D := D) (f := f) (g := g) hf hg_spec (X := Y) hY hYne
  have hOMex : ∃ A, ORDINAL1.isOrdinal A ∧ OM R g D A := by
    classical
    refine Classical.byContradiction fun hnone => ?_
    have hnotOMD : ∀ A, ORDINAL1.isOrdinal A → ¬ OM R g D A := fun A _ hOM =>
      hnone ⟨A, hOM.1, hOM⟩
    have hOO : ∀ A, ORDINAL1.isOrdinal A → (∀ B, B ∈ A → ∃ d, ON R g D B d) →
        ∃ d, ON R g D A d := by
      intro A hA hIH
      by_cases hOMD : OM R g D A
      · exact ⟨D, hOMD⟩
      · -- Construct the unique T-sequence of previous ON-values.
        have hexh : ∀ x, x ∈ A → ∃ y, ∃ C, x = C ∧ ON R g D C y := by
          intro x hx
          obtain ⟨d, hON⟩ := hIH x hx
          exact ⟨d, x, rfl, hON⟩
        obtain ⟨h, hh, hdomh, hhv⟩ :=
          FUNCT_1.sch_FuncEx A (fun x y => ∃ C, x = C ∧ ON R g D C y)
            (fun x y1 y2 hx h1 h2 => by
              obtain ⟨C1, rfl, hON1⟩ := h1
              obtain ⟨C2, rfl, hON2⟩ := h2
              exact ON_unique (ORDINAL1.th13 hA hx) hON1 hON2)
            hexh
        let Xset := chainSet D R h
        have hONh : ON R g D A (FUNCT_1.apply g Xset) := by
          refine ⟨hA, h, hh, rfl, hdomh, ?_⟩
          intro B L1 hB hL1
          obtain ⟨C, hCeq, hONC⟩ := hhv B hB
          subst hCeq
          obtain ⟨L', hf', hd', hdom', hrec'⟩ := hONC.2
          have hBsub : B ⊆ A := hA.1 B hB
          have hrest : RELAT_1.restrict h B = L' := by
            apply FUNCT_1.th2 (FUNCT_1.restrict_isFunction hh) hf'
            · have hdomr : RELAT_1.dom (RELAT_1.restrict h B) = B :=
                RELAT_1.th62 (R := h) (X := B)
                  (Eq.subst (motive := fun s => B ⊆ s) hdomh.symm hBsub)
              exact hdomr.trans hdom'.symm
            · intro x hx
              have hxB : x ∈ B :=
                Eq.subst (motive := fun s => x ∈ s)
                  (RELAT_1.th62 (R := h) (X := B)
                    (Eq.subst (motive := fun s => B ⊆ s) hdomh.symm hBsub)) hx
              have hxA : x ∈ A := hBsub x hxB
              obtain ⟨Cx, hCx, hONx⟩ := hhv x hxA
              subst hCx
              have hONx' : ON R g D x (FUNCT_1.apply L' x) :=
                ON_at (R := R) (g := g) (D := D) (ORDINAL1.th13 hA hB) hf'
                  hdom' hrec' hxB
              have hval : FUNCT_1.apply h x = FUNCT_1.apply L' x :=
                ON_unique (ORDINAL1.th13 hA hxA) hONx hONx'
              exact (FUNCT_1.th49 hh.2 (X := B) (x := x) hxB).trans hval
          exact hd'.trans (congrArg (chainH R g D) (hrest.symm.trans hL1.symm))
        have hXne : Xset ≠ (∅ : TarskiSet.{u}) := fun h0 =>
          hOMD (Eq.subst (motive := fun s => ON R g D A s)
            (Eq.subst (motive := fun s => FUNCT_1.apply g s = D) h0.symm hg_empty)
            hONh)
        exact ⟨FUNCT_1.apply g Xset, hONh⟩
    have hall : ∀ A, ORDINAL1.isOrdinal A → ∃ d, ON R g D A d :=
      fun A hA => ORDINAL1.sch_TransfiniteInd (fun A => ∃ d, ON R g D A d)
        (fun A hA hIH => hOO A hA hIH) A hA
    have huniq : ∀ x y z, (∃ A, y = A ∧ ON R g D A x) →
        (∃ A, z = A ∧ ON R g D A x) → y = z := by
      intro x y z ⟨A1, hy, hON1⟩ ⟨A2, hz, hON2⟩
      subst hy; subst hz
      exact ON_domain_unique hON1.1 hON2.1 hg_empty hg_choice hON1 hON2
        (hnotOMD _ hON1.1)
    obtain ⟨XOrd, hXOrd⟩ := TARSKI.sch1 D (fun y a => ∃ A, a = A ∧ ON R g D A y) huniq
    have hallIn : ∀ A, ORDINAL1.isOrdinal A → A ∈ XOrd := by
      intro A hAord
      obtain ⟨d, hON⟩ := hall A hAord
      exact (hXOrd A).mpr ⟨d, ON_d_mem_D hg_empty hg_choice hON (hnotOMD A hAord), A, rfl, hON⟩
    exact ORDINAL1.th26 ⟨XOrd, hallIn⟩
  obtain ⟨A, hA, hOM, hAmin⟩ :=
    ORDINAL1.sch_OrdinalMin (fun A => OM R g D A) hOMex
  obtain ⟨_, L, hfL, hdOM, hdomL, hrecL⟩ := hOM
  let isXVal (d : TarskiSet.{u}) : Prop := ∃ B, B ∈ A ∧ ON R g D B d
  obtain ⟨X0, hX0⟩ := XBOOLE_0.sch_separation D isXVal
  have hX0sub : X0 ⊆ D := fun d hd => ((hX0 d).mp hd).1
  have hfldD : RELAT_1.field R = D := hfld
  have htransD : RELAT_2.isTransitiveIn R D := hpart.2.1
  have hantiD : RELAT_2.isAntisymmetricIn R D := hpart.2.2
  have hreflD : RELAT_2.isReflexiveIn R D := hpart.1
  have hrngX0 : RELAT_1.rng L ⊆ X0 := by
    intro z hz
    obtain ⟨y, hyDom, hzEq⟩ := (FUNCT_1.def3 hfL.2).mp hz
    have hyA : y ∈ A := Eq.subst (motive := fun s => y ∈ s) hdomL hyDom
    have hONy : ON R g D y (FUNCT_1.apply L y) :=
      ON_at (R := R) (g := g) (D := D) hA hfL hdomL hrecL hyA
    have hnotOMy : ¬ ON R g D y D := fun hOMy =>
      ORDINAL1.th5 hyA (hAmin y (ORDINAL1.th13 hA hyA) hOMy)
    have hzD : z ∈ D := by
      have : FUNCT_1.apply L y ∈ D :=
        ON_d_mem_D hg_empty hg_choice hONy hnotOMy
      exact Eq.subst (motive := fun s => s ∈ D) hzEq.symm this
    exact (hX0 z).mpr ⟨hzD, y, hyA, hzEq ▸ hONy⟩
  have hXlin : isLinearOrder (WELLORD1.restrict2 R X0) := by
    have hpartX0 : partiallyOrders R X0 := th35 hpart hX0sub
    have hQ : isPartialOrder (WELLORD1.restrict2 R X0) := th36 hpartX0
    have hconn : RELAT_2.isConnected (WELLORD1.restrict2 R X0) := by
      refine (RELAT_2.def14 (WELLORD1.restrict2 R X0)).mpr ?_
      intro x y hx hy hne
      have hxX : x ∈ X0 := (WELLORD1.th12 hx).2
      have hyX : y ∈ X0 := (WELLORD1.th12 hy).2
      obtain ⟨A1, hA1A, hON1⟩ := ((hX0 x).mp hxX).2
      obtain ⟨A2, hA2A, hON2⟩ := ((hX0 y).mp hyX).2
      have hA1 : ORDINAL1.isOrdinal A1 := hON1.1
      have hA2 : ORDINAL1.isOrdinal A2 := hON2.1
      have hcmp : TARSKI.pair x y ∈ R ∨ TARSKI.pair y x ∈ R := by
        rcases ORDINAL1.th14 hA1 hA2 with h12 | heq | h21
        · obtain ⟨L2, hf2, hyEq, hdom2, hrec2⟩ := hON2.2
          have hA1sub : A1 ⊆ A2 := hA2.1 A1 h12
          obtain ⟨L1, hf1, hxEq, hdom1, hrec1⟩ := hON1.2
          have hrest : RELAT_1.restrict L2 A1 = L1 :=
            (ON_restrict_eq (R := R) (g := g) (D := D) hA1 hA1sub
              (fun _ ha => ha) hf2 hdom2 hrec2 hf1 hdom1 hrec1).trans
              (RELAT_1.th68 hf1.1
                (fun z hz => Eq.subst (motive := fun s => z ∈ s) hdom1 hz))
          have hxrng : x ∈ RELAT_1.rng L2 :=
            (FUNCT_1.def3 hf2.2).mpr
              ⟨A1, Eq.subst (motive := fun s => A1 ∈ s) hdom2.symm h12,
                hxEq.trans ((ON_restrict_values (R := R) (g := g) (D := D)
                  hdom2 hrec2 h12).trans (congrArg (chainH R g D) hrest)).symm⟩
          let Y := chainSet D R L2
          have hYsub : Y ⊆ D := chainSet_sub D R L2
          have hYne : Y ≠ (∅ : TarskiSet.{u}) := fun h0 => by
            have hgY : FUNCT_1.apply g Y = D :=
              Eq.subst (motive := fun t => FUNCT_1.apply g t = D) h0.symm hg_empty
            have hyD : y = D := by
              rw [hyEq]
              change FUNCT_1.apply g Y = D
              exact hgY
            exact ORDINAL1.not_mem_self y
              (Eq.subst (motive := fun s => y ∈ s) hyD.symm ((hX0 y).mp hyX).1)
          have hyY : y ∈ Y :=
            Eq.subst (motive := fun s => s ∈ Y) hyEq.symm
              (hg_choice (Y := Y) ((ZFMISC_1.def1 D Y).mpr hYsub) hYne)
          exact Or.inl ((chainSet_spec D R L2 y).mp hyY |>.2 x hxrng).2
        · exact False.elim (hne (ON_unique hA1 hON1 (heq ▸ hON2)))
        · obtain ⟨L1, hf1, hxEq, hdom1, hrec1⟩ := hON1.2
          obtain ⟨L2, hf2, hyEq, hdom2, hrec2⟩ := hON2.2
          have hA2sub : A2 ⊆ A1 := hA1.1 A2 h21
          have hrest : RELAT_1.restrict L1 A2 = L2 :=
            (ON_restrict_eq (R := R) (g := g) (D := D) hA2 hA2sub
              (fun _ ha => ha) hf1 hdom1 hrec1 hf2 hdom2 hrec2).trans
              (RELAT_1.th68 hf2.1
                (fun z hz => Eq.subst (motive := fun s => z ∈ s) hdom2 hz))
          have hyrng : y ∈ RELAT_1.rng L1 :=
            (FUNCT_1.def3 hf1.2).mpr
              ⟨A2, Eq.subst (motive := fun s => A2 ∈ s) hdom1.symm h21,
                hyEq.trans ((ON_restrict_values (R := R) (g := g) (D := D)
                  hdom1 hrec1 h21).trans (congrArg (chainH R g D) hrest)).symm⟩
          let Y := chainSet D R L1
          have hYsub : Y ⊆ D := chainSet_sub D R L1
          have hYne : Y ≠ (∅ : TarskiSet.{u}) := fun h0 => by
            have hgY : FUNCT_1.apply g Y = D :=
              Eq.subst (motive := fun t => FUNCT_1.apply g t = D) h0.symm hg_empty
            have hxD : x = D := by
              rw [hxEq]
              change FUNCT_1.apply g Y = D
              exact hgY
            exact ORDINAL1.not_mem_self x
              (Eq.subst (motive := fun s => x ∈ s) hxD.symm ((hX0 x).mp hxX).1)
          have hxY : x ∈ Y :=
            Eq.subst (motive := fun s => s ∈ Y) hxEq.symm
              (hg_choice (Y := Y) ((ZFMISC_1.def1 D Y).mpr hYsub) hYne)
          exact Or.inr ((chainSet_spec D R L1 x).mp hxY |>.2 y hyrng).2
      exact Or.elim hcmp
        (fun hxy => Or.inl ((WELLORD1.restrict2_iff R X0 x y).mpr
          ⟨hxy, hxX, hyX⟩))
        (fun hyx => Or.inr ((WELLORD1.restrict2_iff R X0 y x).mpr
          ⟨hyx, hyX, hxX⟩))
    exact ⟨hQ.1, hQ.2.1, hQ.2.2, hconn⟩
  obtain ⟨m, hmX, hmbound⟩ := hZorn X0 hX0sub hXlin
  have hmD : m ∈ D := hmX
  have hmFld : m ∈ RELAT_1.field R :=
    Eq.subst (motive := fun s => m ∈ s) hfld.symm hmD
  refine ⟨m, hmFld, ?_⟩
  intro ⟨y, hyFld, hyne, hxy⟩
  have hyD : y ∈ D := Eq.subst (motive := fun s => y ∈ s) hfld hyFld
  by_cases hyX : y ∈ X0
  · have hyx : TARSKI.pair y m ∈ R := hmbound y hyX
    exact hyne (hantiD m y hmD hyD hxy hyx).symm
  · have hchainY : isChainValue R L y := by
      intro z hz
      have hzX : z ∈ X0 := hrngX0 z hz
      exact ⟨fun heq => hyX (heq ▸ hzX),
        htransD z m y (hX0sub z hzX) hmD hyD (hmbound z hzX) hxy⟩
    have hyZ : y ∈ chainSet D R L :=
      (chainSet_spec D R L y).mpr ⟨hyD, hchainY⟩
    let Z := chainSet D R L
    have hZsub : Z ⊆ D := chainSet_sub D R L
    have hZne : Z ≠ (∅ : TarskiSet.{u}) := fun h0 =>
      (XBOOLE_0.empty_iff y).mp (Eq.subst (motive := fun s => y ∈ s) h0 hyZ)
    have hDg : FUNCT_1.apply g Z ∈ Z :=
      hg_choice ((ZFMISC_1.def1 D Z).mpr hZsub) hZne
    have hDZ : D ∈ Z :=
      Eq.subst (motive := fun s => s ∈ Z) hdOM.symm hDg
    exact ORDINAL1.th5 hDZ hZsub


/-- `ORDERS_1:Th64`. -/
theorem th64 {R X : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hpart : partiallyOrders R X) (hfld : RELAT_1.field R = X)
    (hZorn : hasLowerZornProperty X R) :
    ∃ x, isMinimalIn x R := by
  have hconv : partiallyOrders (RELAT_1.converse R) X := th41 hpart
  have hfld' : RELAT_1.field (RELAT_1.converse R) = X :=
    (RELAT_1.th21 (R := R)).symm.trans hfld
  have hUP : hasUpperZornProperty X (RELAT_1.converse R) := (th52 hR).mpr hZorn
  obtain ⟨x, hmax⟩ := th63 hconv hfld' hUP
  exact ⟨x, (th59 (x := x) (R := R)).mpr hmax⟩

/-! ## Subset-inclusion Zorn (`ORDERS_1:Th65`–`Th68`) -/

/-- `ORDERS_1:Th65`. -/
theorem th65 {X : TarskiSet.{u}} (_hXne : X ≠ (∅ : TarskiSet.{u}))
    (h : ∀ Z, Z ⊆ X → ORDINAL1.isCLinear Z →
      ∃ Y, Y ∈ X ∧ ∀ X1, X1 ∈ Z → X1 ⊆ Y) :
    ∃ Y, Y ∈ X ∧ ∀ Z, Z ∈ X → Z ≠ Y → ¬ Y ⊆ Z := by
  let D := X
  let R := WELLORD2.RelIncl D
  have hfld : RELAT_1.field R = D := WELLORD2.RelIncl_field D
  have hUP : hasUpperZornProperty D R := by
    intro Z hZ hlin
    have hQ := hlin
    have hZfld : Z ⊆ RELAT_1.field (WELLORD1.restrict2 R Z) := by
      intro x hx
      have hp : TARSKI.pair x x ∈ ZFMISC_1.product Z Z :=
        (ZFMISC_1.th87 (X := Z) (Y := Z) (x := x) (y := x)).mpr ⟨hx, hx⟩
      have hpR : TARSKI.pair x x ∈ R :=
        (WELLORD2.RelIncl_char D x x).mpr ⟨hZ x hx, hZ x hx, fun _ ha => ha⟩
      have hpQ : TARSKI.pair x x ∈ WELLORD1.restrict2 R Z :=
        (WELLORD1.restrict2_iff R Z x x).mpr ⟨hpR, hx, hx⟩
      exact (RELAT_1.th15 (a := x) (b := x) (R := WELLORD1.restrict2 R Z) hpQ).1
    have hconn : RELAT_2.isConnectedIn (WELLORD1.restrict2 R Z)
        (RELAT_1.field (WELLORD1.restrict2 R Z)) :=
      (RELAT_2.def14 (WELLORD1.restrict2 R Z)).mp hlin.2.2.2
    have hclin : ORDINAL1.isCLinear Z := by
      intro X1 X2 hX1 hX2
      by_cases heq : X1 = X2
      · exact Or.inl (fun _ hx => Eq.subst (motive := fun t => _ ∈ t) heq hx)
      · rcases hconn X1 X2 (hZfld X1 hX1) (hZfld X2 hX2) heq with h12 | h21
        · exact Or.inl ((WELLORD2.RelIncl_char D X1 X2).mp
            ((WELLORD1.restrict2_iff R Z X1 X2).mp h12).1).2.2
        · exact Or.inr ((WELLORD2.RelIncl_char D X2 X1).mp
            ((WELLORD1.restrict2_iff R Z X2 X1).mp h21).1).2.2
    obtain ⟨Y, hY, hbound⟩ := h Z hZ hclin
    refine ⟨Y, hY, fun y hy => ?_⟩
    exact (WELLORD2.RelIncl_char D y Y).mpr ⟨hZ y hy, hY, hbound y hy⟩
  have hpart := relIncl_partiallyOrders D
  obtain ⟨x, hmax⟩ := th63 hpart hfld hUP
  have hxD : x ∈ D := Eq.subst (motive := fun s => x ∈ s) hfld hmax.1
  refine ⟨x, hxD, ?_⟩
  intro Z hZ hne hsub
  have hp : TARSKI.pair x Z ∈ R :=
    (WELLORD2.RelIncl_char D x Z).mpr ⟨hxD, hZ, hsub⟩
  exact hmax.2 ⟨Z, Eq.subst (motive := fun s => Z ∈ s) hfld.symm (show Z ∈ D from hZ),
    hne, hp⟩

/-- `ORDERS_1:Th66`. -/
theorem th66 {X : TarskiSet.{u}} (_hXne : X ≠ (∅ : TarskiSet.{u}))
    (h : ∀ Z, Z ⊆ X → ORDINAL1.isCLinear Z →
      ∃ Y, Y ∈ X ∧ ∀ X1, X1 ∈ Z → Y ⊆ X1) :
    ∃ Y, Y ∈ X ∧ ∀ Z, Z ∈ X → Z ≠ Y → ¬ Z ⊆ Y := by
  let D := X
  let R := RELAT_1.converse (WELLORD2.RelIncl D)
  have hfld : RELAT_1.field R = D :=
    (RELAT_1.th21 (R := WELLORD2.RelIncl D)).symm.trans (WELLORD2.RelIncl_field D)
  have hrefl : ∀ x, x ∈ D → TARSKI.pair x x ∈ R := fun x hx =>
    (RELAT_1.def7 (WELLORD2.RelIncl D) x x).mpr
      ((WELLORD2.RelIncl_char D x x).mpr ⟨hx, hx, fun _ ha => ha⟩)
  have hUP : hasUpperZornProperty D R := by
    intro Z hZ hlin
    have hZfld : Z ⊆ RELAT_1.field (WELLORD1.restrict2 R Z) := by
      intro x hx
      have hpR : TARSKI.pair x x ∈ R := hrefl x (hZ x hx)
      have hpQ : TARSKI.pair x x ∈ WELLORD1.restrict2 R Z :=
        (WELLORD1.restrict2_iff R Z x x).mpr ⟨hpR, hx, hx⟩
      exact (RELAT_1.th15 (a := x) (b := x) (R := WELLORD1.restrict2 R Z) hpQ).1
    have hconn := (RELAT_2.def14 (WELLORD1.restrict2 R Z)).mp hlin.2.2.2
    have hclin : ORDINAL1.isCLinear Z := by
      intro X1 X2 hX1 hX2
      by_cases heq : X1 = X2
      · exact Or.inl (fun _ hx => Eq.subst (motive := fun t => _ ∈ t) heq hx)
      · rcases hconn X1 X2 (hZfld X1 hX1) (hZfld X2 hX2) heq with h12 | h21
        · have h12' := (WELLORD1.restrict2_iff R Z X1 X2).mp h12
          exact Or.inr ((WELLORD2.RelIncl_char D X2 X1).mp
            ((RELAT_1.def7 (WELLORD2.RelIncl D) X1 X2).mp h12'.1)).2.2
        · have h21' := (WELLORD1.restrict2_iff R Z X2 X1).mp h21
          exact Or.inl ((WELLORD2.RelIncl_char D X1 X2).mp
            ((RELAT_1.def7 (WELLORD2.RelIncl D) X2 X1).mp h21'.1)).2.2
    obtain ⟨Y, hY, hbound⟩ := h Z hZ hclin
    refine ⟨Y, hY, fun y hy => ?_⟩
    exact (RELAT_1.def7 (WELLORD2.RelIncl D) y Y).mpr
      ((WELLORD2.RelIncl_char D Y y).mpr ⟨hY, hZ y hy, hbound y hy⟩)
  have hpart : partiallyOrders R D :=
    th41 (relIncl_partiallyOrders D)
  obtain ⟨x, hmax⟩ := th63 hpart hfld hUP
  have hxD : x ∈ D := Eq.subst (motive := fun s => x ∈ s) hfld hmax.1
  refine ⟨x, hxD, ?_⟩
  intro Z hZ hne hsub
  have hp : TARSKI.pair x Z ∈ R :=
    (RELAT_1.def7 (WELLORD2.RelIncl D) x Z).mpr
      ((WELLORD2.RelIncl_char D Z x).mpr ⟨hZ, hxD, hsub⟩)
  exact hmax.2 ⟨Z, Eq.subst (motive := fun s => Z ∈ s) hfld.symm (show Z ∈ D from hZ),
    hne, hp⟩

/-- `ORDERS_1:Th67`. -/
theorem th67 {X : TarskiSet.{u}} (hXne : X ≠ (∅ : TarskiSet.{u}))
    (h : ∀ Z, Z ≠ (∅ : TarskiSet.{u}) → Z ⊆ X → ORDINAL1.isCLinear Z →
      TARSKI.union Z ∈ X) :
    ∃ Y, Y ∈ X ∧ ∀ Z, Z ∈ X → Z ≠ Y → ¬ Y ⊆ Z := by
  have h' : ∀ Z, Z ⊆ X → ORDINAL1.isCLinear Z →
      ∃ Y, Y ∈ X ∧ ∀ X1, X1 ∈ Z → X1 ⊆ Y := by
    intro Z hZ hlin
    by_cases hZ0 : Z = (∅ : TarskiSet.{u})
    · subst hZ0
      exact ⟨theElement X hXne, theElement_spec X hXne, fun X1 h => ((XBOOLE_0.empty_iff X1).mp h).elim⟩
    · exact ⟨TARSKI.union Z, h Z hZ0 hZ hlin, fun X1 hX1 x hx =>
        (TARSKI.def4 Z x).mpr ⟨X1, hx, hX1⟩⟩
  exact th65 hXne h'

/-- Unlabeled after `Th67` (meet version). -/
theorem th68 {X : TarskiSet.{u}} (hXne : X ≠ (∅ : TarskiSet.{u}))
    (h : ∀ Z, Z ≠ (∅ : TarskiSet.{u}) → Z ⊆ X → ORDINAL1.isCLinear Z →
      SETFAM_1.meet Z ∈ X) :
    ∃ Y, Y ∈ X ∧ ∀ Z, Z ∈ X → Z ≠ Y → ¬ Z ⊆ Y := by
  have h' : ∀ Z, Z ⊆ X → ORDINAL1.isCLinear Z →
      ∃ Y, Y ∈ X ∧ ∀ X1, X1 ∈ Z → Y ⊆ X1 := by
    intro Z hZ hlin
    by_cases hZ0 : Z = (∅ : TarskiSet.{u})
    · subst hZ0
      exact ⟨theElement X hXne, theElement_spec X hXne, fun X1 h => ((XBOOLE_0.empty_iff X1).mp h).elim⟩
    · exact ⟨SETFAM_1.meet Z, h Z hZ0 hZ hlin, fun X1 hX1 => SETFAM_1.th3 hX1⟩
  exact th66 hXne h'

/-! ## Hausdorff extension (unlabeled ~2507) -/

/-- `ORDERS_1:Th69` (Hausdorff extension). -/
theorem th69 {R X : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hpart : partiallyOrders R X) (hfld : RELAT_1.field R = X) :
    ∃ P, R ⊆ P ∧ linearlyOrders P X ∧ RELAT_1.field P = X := by
  let XX := ZFMISC_1.product X X
  have hRsub : R ⊆ XX :=
    Eq.subst (motive := fun s => R ⊆ ZFMISC_1.product s s) hfld (lm4 hR)
  let isExt (P : TarskiSet.{u}) : Prop :=
    R ⊆ P ∧ partiallyOrders P X ∧ RELAT_1.field P = X
  obtain ⟨Rel, hRel⟩ :=
    XBOOLE_0.sch_separation (ZFMISC_1.bool XX) isExt
  have hRin : R ∈ Rel :=
    (hRel R).mpr ⟨(ZFMISC_1.def1 XX R).mpr hRsub, fun _ hp => hp, hpart, hfld⟩
  have hRelne : Rel ≠ (∅ : TarskiSet.{u}) := fun h0 =>
    (XBOOLE_0.empty_iff R).mp (Eq.subst (motive := fun s => R ∈ s) h0 hRin)
  have hunion : ∀ Z, Z ≠ (∅ : TarskiSet.{u}) → Z ⊆ Rel → ORDINAL1.isCLinear Z →
      TARSKI.union Z ∈ Rel := by
    intro Z hZne hZsub hlin
    have hZbool : Z ⊆ ZFMISC_1.bool XX := fun P hP => ((hRel P).mp (hZsub P hP)).1
    have hSsub : TARSKI.union Z ⊆ XX :=
      Eq.subst (motive := fun s => TARSKI.union Z ⊆ s) (ZFMISC_1.th81 (A := XX))
        (ZFMISC_1.th77 hZbool)
    obtain ⟨P0, hP0Z⟩ := exists_mem_of_ne hZne
    have ⟨hR0, hpart0, _hfld0⟩ := ((hRel P0).mp (hZsub P0 hP0Z)).2
    have hSanti : RELAT_2.isAntisymmetricIn (TARSKI.union Z) X := by
      intro x y hx hy hxy hyx
      obtain ⟨X1, hX1xy, hX1Z⟩ := (TARSKI.def4 Z (TARSKI.pair x y)).mp hxy
      obtain ⟨X2, hX2yx, hX2Z⟩ := (TARSKI.def4 Z (TARSKI.pair y x)).mp hyx
      have hcmp : X1 ⊆ X2 ∨ X2 ⊆ X1 := hlin X1 X2 hX1Z hX2Z
      have hpart1 : partiallyOrders X1 X := ((hRel X1).mp (hZsub X1 hX1Z)).2.2.1
      have hpart2 : partiallyOrders X2 X := ((hRel X2).mp (hZsub X2 hX2Z)).2.2.1
      exact Or.elim hcmp
        (fun h12 => hpart2.2.2 x y hx hy (h12 _ hX1xy) hX2yx)
        (fun h21 => hpart1.2.2 x y hx hy hX1xy (h21 _ hX2yx))
    have hStrans : RELAT_2.isTransitiveIn (TARSKI.union Z) X := by
      intro x y z hx hy hz hxy hyz
      obtain ⟨X1, hX1xy, hX1Z⟩ := (TARSKI.def4 Z (TARSKI.pair x y)).mp hxy
      obtain ⟨X2, hX2yz, hX2Z⟩ := (TARSKI.def4 Z (TARSKI.pair y z)).mp hyz
      have hcmp : X1 ⊆ X2 ∨ X2 ⊆ X1 := hlin X1 X2 hX1Z hX2Z
      have hpart1 : partiallyOrders X1 X := ((hRel X1).mp (hZsub X1 hX1Z)).2.2.1
      have hpart2 : partiallyOrders X2 X := ((hRel X2).mp (hZsub X2 hX2Z)).2.2.1
      exact Or.elim hcmp
        (fun h12 => (TARSKI.def4 Z (TARSKI.pair x z)).mpr
          ⟨X2, hpart2.2.1 x y z hx hy hz (h12 _ hX1xy) hX2yz, hX2Z⟩)
        (fun h21 => (TARSKI.def4 Z (TARSKI.pair x z)).mpr
          ⟨X1, hpart1.2.1 x y z hx hy hz hX1xy (h21 _ hX2yz), hX1Z⟩)
    have hSrefl : RELAT_2.isReflexiveIn (TARSKI.union Z) X := fun x hx =>
      (TARSKI.def4 Z (TARSKI.pair x x)).mpr ⟨P0, hpart0.1 x hx, hP0Z⟩
    have hSpart : partiallyOrders (TARSKI.union Z) X := ⟨hSrefl, hStrans, hSanti⟩
    have hRsubS : R ⊆ TARSKI.union Z := fun p hp =>
      (TARSKI.def4 Z p).mpr ⟨P0, hR0 p hp, hP0Z⟩
    have hfldS : RELAT_1.field (TARSKI.union Z) = X := by
      apply (XBOOLE_0.def10
        (X := RELAT_1.field (TARSKI.union Z)) (Y := X)).mpr
      constructor
      · intro x hx
        rcases (XBOOLE_0.def3 (RELAT_1.dom (TARSKI.union Z))
            (RELAT_1.rng (TARSKI.union Z)) x).mp hx with hd | hr
        · obtain ⟨y, hp⟩ := (RELAT_1.dom_iff (TARSKI.union Z) x).mp hd
          obtain ⟨P, hPxy, hPZ⟩ := (TARSKI.def4 Z (TARSKI.pair x y)).mp hp
          have hfldP : RELAT_1.field P = X := ((hRel P).mp (hZsub P hPZ)).2.2.2
          exact Eq.subst (motive := fun s => x ∈ s) hfldP (RELAT_1.th15 hPxy).1
        · obtain ⟨y, hp⟩ := (RELAT_1.rng_iff (TARSKI.union Z) x).mp hr
          obtain ⟨P, hPyx, hPZ⟩ := (TARSKI.def4 Z (TARSKI.pair y x)).mp hp
          have hfldP : RELAT_1.field P = X := ((hRel P).mp (hZsub P hPZ)).2.2.2
          exact Eq.subst (motive := fun s => x ∈ s) hfldP (RELAT_1.th15 hPyx).2
      · exact Eq.subst (motive := fun s => s ⊆ RELAT_1.field (TARSKI.union Z))
          hfld (RELAT_1.th16 hRsubS)
    exact (hRel (TARSKI.union Z)).mpr
      ⟨(ZFMISC_1.def1 XX (TARSKI.union Z)).mpr hSsub, hRsubS, hSpart, hfldS⟩
  obtain ⟨Y, hYRel, hYmax⟩ := th67 hRelne hunion
  have ⟨hRY, hYpart, hYfld⟩ := ((hRel Y).mp hYRel).2
  have hYconn : RELAT_2.isConnectedIn Y X := by
    intro x y hx hy hne
    apply Classical.byContradiction
    intro hfail
    have hnxy : TARSKI.pair x y ∉ Y := fun hp => hfail (Or.inl hp)
    have hnyx' : TARSKI.pair y x ∉ Y := fun hp => hfail (Or.inr hp)
    obtain ⟨Q, hQrel, hQchar⟩ :=
      RELAT_1.sch_RelExistence X X
        (fun z u => TARSKI.pair z u ∈ Y ∨
          TARSKI.pair z x ∈ Y ∧ TARSKI.pair y u ∈ Y)
    have hYrel : RELAT_1.isRelation Y :=
      RELAT_1.subset_isRelation (RELAT_1.product_isRelation X X)
        ((ZFMISC_1.def1 XX Y).mp ((hRel Y).mp hYRel).1)
    have hYsubQ : Y ⊆ Q := by
      intro p hp
      obtain ⟨a, b, heq⟩ := hYrel p hp
      exact Eq.subst (motive := fun s => s ∈ Q) heq.symm
        ((hQchar a b).mpr ⟨
          Eq.subst (motive := fun s => a ∈ s) hYfld (RELAT_1.th15
            (Eq.subst (motive := fun s => s ∈ Y) heq hp)).1,
          Eq.subst (motive := fun s => b ∈ s) hYfld (RELAT_1.th15
            (Eq.subst (motive := fun s => s ∈ Y) heq hp)).2,
          Or.inl (Eq.subst (motive := fun s => s ∈ Y) heq hp)⟩)
    have hfldQ : RELAT_1.field Q = X := by
      apply (XBOOLE_0.def10 (X := RELAT_1.field Q) (Y := X)).mpr
      constructor
      · intro z hz
        rcases (XBOOLE_0.def3 (RELAT_1.dom Q) (RELAT_1.rng Q) z).mp hz with hd | hr
        · obtain ⟨u, hp⟩ := (RELAT_1.dom_iff Q z).mp hd
          exact ((hQchar z u).mp hp).1
        · obtain ⟨u, hp⟩ := (RELAT_1.rng_iff Q z).mp hr
          exact ((hQchar u z).mp hp).2.1
      · exact Eq.subst (motive := fun s => s ⊆ RELAT_1.field Q) hYfld
          (RELAT_1.th16 hYsubQ)
    have hQtrans : RELAT_2.isTransitiveIn Q X := by
      intro a b c ha hb hc hab hbc
      have hab' := (hQchar a b).mp hab
      have hbc' := (hQchar b c).mp hbc
      have hgoal :
          TARSKI.pair a c ∈ Y ∨
            TARSKI.pair a x ∈ Y ∧ TARSKI.pair y c ∈ Y := by
        rcases hab'.2.2 with habY | ⟨hax, hyb⟩
        · rcases hbc'.2.2 with hbcY | ⟨hbx, hyc⟩
          · exact Or.inl (hYpart.2.1 a b c ha hb hc habY hbcY)
          · exact Or.inr ⟨hYpart.2.1 a b x ha hb hx habY hbx, hyc⟩
        · rcases hbc'.2.2 with hbcY | ⟨hbx, hyc⟩
          · exact Or.inr ⟨hax, hYpart.2.1 y b c hy hb hc hyb hbcY⟩
          · exact False.elim (hnyx' (hYpart.2.1 y b x hy hb hx hyb hbx))
      exact (hQchar a c).mpr ⟨ha, hc, hgoal⟩
    have hQanti : RELAT_2.isAntisymmetricIn Q X := by
      intro a b ha hb hab hba
      have hab' := (hQchar a b).mp hab
      have hba' := (hQchar b a).mp hba
      rcases hab'.2.2 with habY | ⟨hax, hyb⟩
      · rcases hba'.2.2 with hbaY | ⟨hbx, hya⟩
        · exact hYpart.2.2 a b ha hb habY hbaY
        · exact False.elim (hnyx'
            (hYpart.2.1 y a x hy ha hx hya
              (hYpart.2.1 a b x ha hb hx habY hbx)))
      · rcases hba'.2.2 with hbaY | ⟨hbx, hya⟩
        · exact False.elim (hnyx'
            (hYpart.2.1 y b x hy hb hx hyb
              (hYpart.2.1 b a x hb ha hx hbaY hax)))
        · exact False.elim (hnyx' (hYpart.2.1 y b x hy hb hx hyb hbx))
    have hQrefl : RELAT_2.isReflexiveIn Q X := fun z hz =>
      (hQchar z z).mpr ⟨hz, hz, Or.inl (hYpart.1 z hz)⟩
    have hQpart : partiallyOrders Q X := ⟨hQrefl, hQtrans, hQanti⟩
    have hQsubXX : Q ⊆ XX := fun p hp => by
      have hQrel : RELAT_1.isRelation Q := hQrel
      obtain ⟨a, b, heq⟩ := hQrel p hp
      have ⟨ha, hb, _⟩ := (hQchar a b).mp (Eq.subst (motive := fun s => s ∈ Q) heq hp)
      exact Eq.subst (motive := fun s => s ∈ XX) heq.symm
        ((ZFMISC_1.th87 (X := X) (Y := X) (x := a) (y := b)).mpr ⟨ha, hb⟩)
    have hQin : Q ∈ Rel :=
      (hRel Q).mpr ⟨(ZFMISC_1.def1 XX Q).mpr hQsubXX,
        fun p hp => hYsubQ p (hRY p hp), hQpart, hfldQ⟩
    have hQeq : Q = Y := by
      apply Classical.byContradiction
      intro hne
      exact hYmax Q hQin hne hYsubQ
    have hyy : TARSKI.pair y y ∈ Y := hYpart.1 y hy
    have hxx : TARSKI.pair x x ∈ Y := hYpart.1 x hx
    have hxyQ : TARSKI.pair x y ∈ Q :=
      (hQchar x y).mpr ⟨hx, hy, Or.inr ⟨hxx, hyy⟩⟩
    exact hnxy (Eq.subst (motive := fun s => TARSKI.pair x y ∈ s) hQeq hxyQ)
  exact ⟨Y, hRY, ⟨hYpart.1, hYpart.2.1, hYpart.2.2, hYconn⟩, hYfld⟩

/-! ## Zorn schemes (`ORDERS_1:sch ZornMax`, `ZornMin`) -/

/-- `ORDERS_1:sch ZornMax`. -/
theorem sch_ZornMax (A : TarskiSet.{u}) (hAne : A ≠ (∅ : TarskiSet.{u}))
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hrefl : ∀ x, x ∈ A → P x x)
    (hanti : ∀ x y, x ∈ A → y ∈ A → P x y → P y x → x = y)
    (htrans : ∀ x y z, x ∈ A → y ∈ A → z ∈ A → P x y → P y z → P x z)
    (hchain : ∀ Y, Y ⊆ A → (∀ x y, x ∈ Y → y ∈ Y → P x y ∨ P y x) →
      ∃ y, y ∈ A ∧ ∀ x, x ∈ Y → P x y) :
    ∃ x, x ∈ A ∧ ∀ y, y ∈ A → x ≠ y → ¬ P x y := by
  obtain ⟨R, hR, hchar⟩ := RELSET_1.sch_RelOnSetEx A A P
  have htransR : RELAT_2.isTransitiveIn R A := by
    intro x y z hx hy hz hxy hyz
    exact (hchar x z).mpr ⟨hx, hz, htrans x y z hx hy hz
      ((hchar x y).mp hxy).2.2 ((hchar y z).mp hyz).2.2⟩
  have hdom : RELAT_1.dom R = A := by
    apply TARSKI.extensionality
    intro x
    constructor
    · intro hx
      obtain ⟨y, hp⟩ := (RELAT_1.dom_iff R x).mp hx
      exact ((hchar x y).mp hp).1
    · intro hx
      exact (RELAT_1.dom_iff R x).mpr ⟨x, (hchar x x).mpr ⟨hx, hx, hrefl x hx⟩⟩
  have hfld : RELAT_1.field R = A := by
    apply TARSKI.extensionality
    intro x
    constructor
    · intro hx
      rcases (XBOOLE_0.def3 (RELAT_1.dom R) (RELAT_1.rng R) x).mp hx with hd | hr
      · exact Eq.subst (motive := fun s => x ∈ s) hdom hd
      · obtain ⟨y, hp⟩ := (RELAT_1.rng_iff R x).mp hr
        exact ((hchar y x).mp hp).2.1
    · intro hx
      exact (XBOOLE_0.def3 (RELAT_1.dom R) (RELAT_1.rng R) x).mpr
        (Or.inl (Eq.subst (motive := fun s => x ∈ s) hdom.symm hx))
  have hreflR : RELAT_2.isReflexiveIn R A := fun x hx =>
    (hchar x x).mpr ⟨hx, hx, hrefl x hx⟩
  have hantiR : RELAT_2.isAntisymmetricIn R A := fun x y hx hy hxy hyx =>
    hanti x y hx hy ((hchar x y).mp hxy).2.2 ((hchar y x).mp hyx).2.2
  have hUP : hasUpperZornProperty A R := by
    intro Y hY hlin
    have hYfld : Y ⊆ RELAT_1.field (WELLORD1.restrict2 R Y) := by
      intro x hx
      have hp : TARSKI.pair x x ∈ WELLORD1.restrict2 R Y :=
        (WELLORD1.restrict2_iff R Y x x).mpr
          ⟨(hchar x x).mpr ⟨hY x hx, hY x hx, hrefl x (hY x hx)⟩, hx, hx⟩
      exact (RELAT_1.th15 (a := x) (b := x) (R := WELLORD1.restrict2 R Y) hp).1
    have hconn := (RELAT_2.def14 (WELLORD1.restrict2 R Y)).mp hlin.2.2.2
    have htot : ∀ x y, x ∈ Y → y ∈ Y → P x y ∨ P y x := by
      intro x y hx hy
      by_cases heq : x = y
      · exact Or.inl (Eq.subst (motive := fun t => P x t) heq (hrefl x (hY x hx)))
      · rcases hconn x y (hYfld x hx) (hYfld y hy) heq with hxy | hyx
        · exact Or.inl ((hchar x y).mp ((WELLORD1.restrict2_iff R Y x y).mp hxy).1).2.2
        · exact Or.inr ((hchar y x).mp ((WELLORD1.restrict2_iff R Y y x).mp hyx).1).2.2
    obtain ⟨y, hy, hbound⟩ := hchain Y hY htot
    refine ⟨y, hy, fun x hx => (hchar x y).mpr ⟨hY x hx, hy, hbound x hx⟩⟩
  have hpart : partiallyOrders R A := ⟨hreflR, htransR, hantiR⟩
  obtain ⟨x, hmax⟩ := th63 hpart hfld hUP
  refine ⟨x, Eq.subst (motive := fun s => x ∈ s) hfld hmax.1, ?_⟩
  intro y hy hyne hp
  have hxA : x ∈ A := Eq.subst (motive := fun s => x ∈ s) hfld hmax.1
  have hpR : TARSKI.pair x y ∈ R := (hchar x y).mpr ⟨hxA, hy, hp⟩
  exact hmax.2 ⟨y, Eq.subst (motive := fun s => y ∈ s) hfld.symm hy, hyne.symm, hpR⟩

/-- `ORDERS_1:sch ZornMin`. -/
theorem sch_ZornMin (A : TarskiSet.{u}) (hAne : A ≠ (∅ : TarskiSet.{u}))
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hrefl : ∀ x, x ∈ A → P x x)
    (hanti : ∀ x y, x ∈ A → y ∈ A → P x y → P y x → x = y)
    (htrans : ∀ x y z, x ∈ A → y ∈ A → z ∈ A → P x y → P y z → P x z)
    (hchain : ∀ Y, Y ⊆ A → (∀ x y, x ∈ Y → y ∈ Y → P x y ∨ P y x) →
      ∃ y, y ∈ A ∧ ∀ x, x ∈ Y → P y x) :
    ∃ x, x ∈ A ∧ ∀ y, y ∈ A → x ≠ y → ¬ P y x := by
  obtain ⟨x, hx, hmin⟩ := sch_ZornMax A hAne (fun a b => P b a) (fun a ha => hrefl a ha)
    (fun a b ha hb hpab hpba => (hanti b a hb ha hpab hpba).symm)
    (fun a b c ha hb hc hpba hpcb => htrans c b a hc hb ha hpcb hpba)
    (fun Y hY htot => by
      obtain ⟨y, hy, hbound⟩ := hchain Y hY (fun a b ha hb => Or.elim (htot a b ha hb) Or.inr Or.inl)
      exact ⟨y, hy, fun a ha => hbound a ha⟩)
  exact ⟨x, hx, fun y hy hyne hp => hmin y hy hyne hp⟩

/-! ## Exported auxiliary restatements (`ORDERS_1:Th70`–`Th84`) -/

theorem th70 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    R ⊆ ZFMISC_1.product (RELAT_1.field R) (RELAT_1.field R) :=
  lm4 hR

theorem th71 {R X : TarskiSet.{u}} (hrefl : RELAT_2.isReflexive R) (hX : X ⊆ RELAT_1.field R) :
    RELAT_1.field (WELLORD1.restrict2 R X) = X :=
  lm5 hrefl hX

theorem th72 {R X : TarskiSet.{u}} (hrefl : RELAT_2.isReflexiveIn R X) :
    RELAT_2.isReflexive (WELLORD1.restrict2 R X) :=
  lm6 hrefl

theorem th73 {R X : TarskiSet.{u}} (htrans : RELAT_2.isTransitiveIn R X) :
    RELAT_2.isTransitive (WELLORD1.restrict2 R X) :=
  lm7 htrans

theorem th74 {R X : TarskiSet.{u}} (hanti : RELAT_2.isAntisymmetricIn R X) :
    RELAT_2.isAntisymmetric (WELLORD1.restrict2 R X) :=
  lm8 hanti

theorem th75 {R X : TarskiSet.{u}} (hconn : RELAT_2.isConnectedIn R X) :
    RELAT_2.isConnected (WELLORD1.restrict2 R X) :=
  lm9 hconn

theorem th76 {R X Y : TarskiSet.{u}} (hconn : RELAT_2.isConnectedIn R X) (hY : Y ⊆ X) :
    RELAT_2.isConnectedIn R Y :=
  lm10 hconn hY

theorem th77 {R X Y : TarskiSet.{u}} (h : WELLORD1.wellOrders R X) (hY : Y ⊆ X) :
    WELLORD1.wellOrders R Y :=
  lm17 h hY

theorem th78 {R : TarskiSet.{u}} (h : RELAT_2.isConnected R) :
    RELAT_2.isConnected (RELAT_1.converse R) :=
  lm3 h

theorem th79 {R X : TarskiSet.{u}} (hrefl : RELAT_2.isReflexiveIn R X) :
    RELAT_2.isReflexiveIn (RELAT_1.converse R) X :=
  lm11 hrefl

theorem th80 {R X : TarskiSet.{u}} (htrans : RELAT_2.isTransitiveIn R X) :
    RELAT_2.isTransitiveIn (RELAT_1.converse R) X :=
  lm12 htrans

theorem th81 {R X : TarskiSet.{u}} (hanti : RELAT_2.isAntisymmetricIn R X) :
    RELAT_2.isAntisymmetricIn (RELAT_1.converse R) X :=
  lm13 hanti

theorem th82 {R X : TarskiSet.{u}} (hconn : RELAT_2.isConnectedIn R X) :
    RELAT_2.isConnectedIn (RELAT_1.converse R) X :=
  lm14 hconn

theorem th83 {R X : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    RELAT_1.converse (WELLORD1.restrict2 R X) =
      WELLORD1.restrict2 (RELAT_1.converse R) X :=
  lm15 hR

theorem th84 (R : TarskiSet.{u}) :
    WELLORD1.restrict2 R (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) :=
  lm16 R

/-! ## Addenda (`ORDERS_1:Th85`–`Th88`) -/

/-- `ORDERS_1:Th85` (from `COMPTS_1`). -/
theorem th85 {f Z : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hfin : FINSET_1.isFinite Z) (hZ : Z ⊆ RELAT_1.rng f) :
    ∃ Y, Y ⊆ RELAT_1.dom f ∧ FINSET_1.isFinite Y ∧ RELAT_1.image f Y = Z := by
  have hfib : ∀ z, z ∈ Z → RELAT_1.invimage f (TARSKI.singleton z) ≠
      (∅ : TarskiSet.{u}) :=
    fun z hz => (FUNCT_1.th72 (R := f) (y := z)).mp (hZ z hz)
  classical
  let F : TarskiSet.{u} → TarskiSet.{u} := fun z =>
    if h : z ∈ Z then
      Classical.choose (exists_mem_of_ne (hfib z h))
    else (∅ : TarskiSet.{u})
  obtain ⟨g, hg, hdom, hgv⟩ := FUNCT_1.sch_Lambda Z F
  have hFmem : ∀ z, z ∈ Z →
      FUNCT_1.apply g z ∈ RELAT_1.invimage f (TARSKI.singleton z) := by
    intro z hz
    have hF : F z = Classical.choose (exists_mem_of_ne (hfib z hz)) := dif_pos hz
    exact Eq.subst (motive := fun s => s ∈ RELAT_1.invimage f (TARSKI.singleton z))
      ((hgv z hz).trans hF).symm
      (Classical.choose_spec (exists_mem_of_ne (hfib z hz)))
  let Y := RELAT_1.rng g
  have hYsub : Y ⊆ RELAT_1.dom f := by
    intro y hy
    obtain ⟨z, hzdom, heq⟩ := (FUNCT_1.def3 hg.2).mp hy
    have hzZ : z ∈ Z := Eq.subst (motive := fun s => z ∈ s) hdom hzdom
    have hyinv : y ∈ RELAT_1.invimage f (TARSKI.singleton z) :=
      Eq.subst (motive := fun s => s ∈ RELAT_1.invimage f (TARSKI.singleton z))
        heq.symm (hFmem z hzZ)
    exact (FUNCT_1.def7 hf.2 (Y := TARSKI.singleton z) (x := y)).mp hyinv |>.1
  have hYfin : FINSET_1.isFinite Y :=
    FINSET_1.th8 hg (Eq.subst (motive := FINSET_1.isFinite) hdom.symm hfin)
  have himg : RELAT_1.image f Y = Z := by
    apply eq_of_mem
    intro w
    constructor
    · intro hw
      obtain ⟨y, hp, hyY⟩ := (RELAT_1.def13 f Y w).mp hw
      obtain ⟨z, hzdom, heq⟩ := (FUNCT_1.def3 hg.2).mp hyY
      have hzZ : z ∈ Z := Eq.subst (motive := fun s => z ∈ s) hdom hzdom
      have hyinv : y ∈ RELAT_1.invimage f (TARSKI.singleton z) :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.invimage f (TARSKI.singleton z))
          heq.symm (hFmem z hzZ)
      have hwz : w = z := by
        have hpair : TARSKI.pair y z ∈ f :=
          let ⟨_, hzsing⟩ := (FUNCT_1.def7 hf.2 (Y := TARSKI.singleton z) (x := y)).mp hyinv
          (FUNCT_1.th1 hf.2).mpr ⟨(FUNCT_1.def7 hf.2).mp hyinv |>.1,
            ((TARSKI.singleton_iff z (FUNCT_1.apply f y)).mp
              ((FUNCT_1.def7 hf.2).mp hyinv |>.2)).symm⟩
        exact hf.2 y w z hp hpair
      exact Eq.subst (motive := fun s => s ∈ Z) hwz.symm hzZ
    · intro hw
      have hyinv := hFmem w hw
      have ⟨hydom, hsing⟩ := (FUNCT_1.def7 hf.2 (Y := TARSKI.singleton w)
        (x := FUNCT_1.apply g w)).mp hyinv
      have hyY : FUNCT_1.apply g w ∈ Y :=
        (FUNCT_1.def3 hg.2).mpr
          ⟨w, Eq.subst (motive := fun s => w ∈ s) hdom.symm hw, rfl⟩
      have hp : TARSKI.pair (FUNCT_1.apply g w) w ∈ f :=
        (FUNCT_1.th1 hf.2).mpr ⟨hydom,
          ((TARSKI.singleton_iff w (FUNCT_1.apply f (FUNCT_1.apply g w))).mp hsing).symm⟩
      exact (RELAT_1.def13 f Y w).mpr ⟨FUNCT_1.apply g w, hp, hyY⟩
  exact ⟨Y, hYsub, hYfin, himg⟩

/-- `ORDERS_1:Th86`. -/
theorem th86 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hfin : FINSET_1.isFinite (RELAT_1.field R)) : FINSET_1.isFinite R := by
  have hsub := lm4 hR
  have hprod := FINSET_1.product_isFinite hfin hfin
  exact FINSET_1.subset_isFinite hsub hprod

/-- Unlabeled after `Th86` (`AMISTD_3`). -/
theorem th87 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hdom : FINSET_1.isFinite (RELAT_1.dom R)) (hrng : FINSET_1.isFinite (RELAT_1.rng R)) :
    FINSET_1.isFinite R := by
  have hfield : FINSET_1.isFinite (RELAT_1.field R) :=
    FINSET_1.lm2 hdom hrng
  exact th86 hR hfield

/-- Unlabeled order-type registration (`AMISTD_3` / `WELLORD2`). -/
theorem th88 {O : TarskiSet.{u}} (hO : ORDINAL1.isOrdinal O) :
    WELLORD2.order_type_of (WELLORD2.RelIncl_wellOrdering hO) = O := by
  have hiso : WELLORD1.areIsomorphic (WELLORD2.RelIncl O) (WELLORD2.RelIncl O) :=
    WELLORD1.th38 (WELLORD2.RelIncl O)
  exact WELLORD2.order_type_unique (WELLORD2.RelIncl_wellOrdering hO) hO hiso

end ORDERS_1

