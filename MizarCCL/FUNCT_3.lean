import MizarCCL.BINOP_1
import MizarCCL.DOMAIN_1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/funct_3.miz`.
Authors: Czesław Byliński (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Basic Functions and Operations on Functions

1–1 Lean rendering of Mizar article `FUNCT_3`
(`vendor/mml/funct_3.miz`). Import is `BINOP_1` and `DOMAIN_1`
(last queue deps; both used). Mizar `g*f` is Lean `RELAT_1.comp f g`.
Ordinal `1` is `TARSKI.singleton ∅`.
-/

universe u

open TarskiSet TARSKI

namespace FUNCT_3

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

private theorem ne_imp_not_empty {X : TarskiSet.{u}}
    (h : X ≠ (∅ : TarskiSet.{u})) : ¬ XBOOLE_0.isEmpty X :=
  fun he => h (XBOOLE_0.empty_eq he)

/-- Set-theoretic `1` = `{∅}`. -/
noncomputable def one : TarskiSet.{u} :=
  TARSKI.singleton (∅ : TarskiSet.{u})

theorem one_ne_empty : one ≠ (∅ : TarskiSet.{u}) :=
  fun h => XBOOLE_0.singleton_nonempty (∅ : TarskiSet.{u})
    (Eq.subst (motive := fun s => XBOOLE_0.isEmpty s) h.symm
      XBOOLE_0.emptySet_isEmpty)

/-! ## Additional propositions about functions -/

/-- `FUNCT_3:1` (`Th1`) -/
theorem th1 {A Y : TarskiSet.{u}} (h : A ⊆ Y) :
    RELAT_1.id A = RELAT_1.restrict (RELAT_1.id Y) A := by
  have hAY : A ∩ Y = A := XBOOLE_1.th28 h
  have hYA : Y ∩ A = A :=
    (XBOOLE_0.inter_comm Y A).trans hAY
  have h1 : RELAT_1.id A = RELAT_1.id (Y ∩ A) :=
    congrArg RELAT_1.id hYA.symm
  have h2 : RELAT_1.id (Y ∩ A) =
      RELAT_1.comp (RELAT_1.id A) (RELAT_1.id Y) :=
    (FUNCT_1.th22 (X := Y) (Y := A)).symm
  have h3 : RELAT_1.comp (RELAT_1.id A) (RELAT_1.id Y) =
      RELAT_1.restrict (RELAT_1.id Y) A :=
    (RELAT_1.th65 (R := RELAT_1.id Y) (X := A)).symm
  exact h1.trans (h2.trans h3)

/-- `FUNCT_3:2` (`Th2`) -/
theorem th2 {f g X : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g) (h : X ⊆ RELAT_1.dom (RELAT_1.comp f g)) :
    RELAT_1.image f X ⊆ RELAT_1.dom g := by
  intro y hy
  obtain ⟨x, hxD, hxX, heq⟩ := (FUNCT_1.def6 hf.2).mp hy
  have hxcomp : x ∈ RELAT_1.dom (RELAT_1.comp f g) := h x hxX
  have ⟨_, hfx⟩ := (FUNCT_1.th11 hf.2 (g := g) (x := x)).mp hxcomp
  exact Eq.subst (motive := fun s => s ∈ RELAT_1.dom g) heq.symm hfx

/-- `FUNCT_3:3` (`Th3`) -/
theorem th3 {f g X : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g) (h1 : X ⊆ RELAT_1.dom f)
    (h2 : RELAT_1.image f X ⊆ RELAT_1.dom g) :
    X ⊆ RELAT_1.dom (RELAT_1.comp f g) := by
  intro x hx
  have hfx : FUNCT_1.apply f x ∈ RELAT_1.image f X :=
    (FUNCT_1.def6 hf.2).mpr ⟨x, h1 x hx, hx, rfl⟩
  exact (FUNCT_1.th11 hf.2 (g := g) (x := x)).mpr ⟨h1 x hx, h2 _ hfx⟩

/-- `FUNCT_3:4` (`Th4`) -/
theorem th4 {f g Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (h1 : Y ⊆ RELAT_1.rng (RELAT_1.comp f g))
    (h2 : FUNCT_1.isOneToOne g) :
    RELAT_1.invimage g Y ⊆ RELAT_1.rng f := by
  intro y hy
  have hyD : y ∈ RELAT_1.dom g := ((FUNCT_1.def7 hg.2).mp hy).1
  have hgy : FUNCT_1.apply g y ∈ Y := ((FUNCT_1.def7 hg.2).mp hy).2
  obtain ⟨x, hxD, heq⟩ := (FUNCT_1.def3 (FUNCT_1.comp_isFunction hf hg).2).mp
    (h1 _ hgy)
  have hxDf : x ∈ RELAT_1.dom f := ((FUNCT_1.th11 hf.2).mp hxD).1
  have hfxDg : FUNCT_1.apply f x ∈ RELAT_1.dom g :=
    ((FUNCT_1.th11 hf.2).mp hxD).2
  have hcomp : FUNCT_1.apply g y = FUNCT_1.apply g (FUNCT_1.apply f x) :=
    heq.trans (FUNCT_1.th12 hf.2 hg.2 hxD)
  have hyeq : y = FUNCT_1.apply f x :=
    h2 y (FUNCT_1.apply f x) hyD hfxDg hcomp
  exact (FUNCT_1.def3 hf.2).mpr ⟨x, hxDf, hyeq⟩

/-- `FUNCT_3:5` (`Th5`) -/
theorem th5 {f g Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (h1 : Y ⊆ RELAT_1.rng g)
    (h2 : RELAT_1.invimage g Y ⊆ RELAT_1.rng f) :
    Y ⊆ RELAT_1.rng (RELAT_1.comp f g) := by
  intro y hy
  obtain ⟨z, hzD, heq⟩ := (FUNCT_1.def3 hg.2).mp (h1 y hy)
  have hzInv : z ∈ RELAT_1.invimage g Y :=
    (FUNCT_1.def7 hg.2).mpr ⟨hzD, Eq.subst (motive := fun s => s ∈ Y) heq hy⟩
  obtain ⟨x, hxD, hzfx⟩ := (FUNCT_1.def3 hf.2).mp (h2 z hzInv)
  have hxcomp : x ∈ RELAT_1.dom (RELAT_1.comp f g) :=
    (FUNCT_1.th11 hf.2).mpr ⟨hxD,
      Eq.subst (motive := fun s => s ∈ RELAT_1.dom g) hzfx hzD⟩
  have happ : FUNCT_1.apply (RELAT_1.comp f g) x = y :=
    (FUNCT_1.th13 hf.2 hg.2 hxD).trans
      (Eq.subst (motive := fun s => FUNCT_1.apply g s = y) hzfx heq.symm)
  exact (FUNCT_1.def3 (FUNCT_1.comp_isFunction hf hg).2).mpr
    ⟨x, hxcomp, happ.symm⟩

/-! ## Schemes FuncEx3 / Lambda3 -/

/-- `FUNCT_3:sch FuncEx3` -/
theorem sch_FuncEx3 (A B : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hfun : ∀ x y z1 z2, x ∈ A → y ∈ B → P x y z1 → P x y z2 → z1 = z2)
    (hex : ∀ x y, x ∈ A → y ∈ B → ∃ z, P x y z) :
    ∃ f, FUNCT_1.isFunction f ∧
      RELAT_1.dom f = ZFMISC_1.product A B ∧
      ∀ x y, x ∈ A → y ∈ B → P x y (BINOP_1.apply2 f x y) := by
  let D := ZFMISC_1.product A B
  let R : TarskiSet.{u} → TarskiSet.{u} → Prop :=
    fun p z => ∀ x y, p = TARSKI.pair x y → P x y z
  have hexR : ∀ p, p ∈ D → ∃ z, R p z := by
    intro p hp
    obtain ⟨x1, y1, hx1, hy1, hpair⟩ := (ZFMISC_1.def2 A B p).mp hp
    obtain ⟨z, hz⟩ := hex x1 y1 hx1 hy1
    refine ⟨z, ?_⟩
    intro x y heq
    have ⟨hx, hy⟩ := XTUPLE_0.th1 (hpair.symm.trans heq)
    exact Eq.subst (motive := fun s => P s y z) hx
      (Eq.subst (motive := fun s => P x1 s z) hy hz)
  have hfunR : ∀ p y1 y2, p ∈ D → R p y1 → R p y2 → y1 = y2 := by
    intro p y1 y2 hp h1 h2
    obtain ⟨x1, x2, hx1, hx2, hpair⟩ := (ZFMISC_1.def2 A B p).mp hp
    exact hfun x1 x2 y1 y2 hx1 hx2 (h1 x1 x2 hpair) (h2 x1 x2 hpair)
  obtain ⟨f, hf, hdom, hv⟩ := FUNCT_1.sch_FuncEx D R hfunR hexR
  refine ⟨f, hf, hdom, ?_⟩
  intro x y hx hy
  have hp : TARSKI.pair x y ∈ D :=
    (ZFMISC_1.th87 (x := x) (y := y) (X := A) (Y := B)).mpr ⟨hx, hy⟩
  exact hv (TARSKI.pair x y) hp x y rfl

/-- `FUNCT_3:sch Lambda3` -/
theorem sch_Lambda3 (A B : TarskiSet.{u})
    (F : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u}) :
    ∃ f, FUNCT_1.isFunction f ∧
      RELAT_1.dom f = ZFMISC_1.product A B ∧
      ∀ x y, x ∈ A → y ∈ B → BINOP_1.apply2 f x y = F x y :=
  sch_FuncEx3 A B (fun x y z => z = F x y)
    (fun _ _ _ _ _ _ h1 h2 => h1.trans h2.symm)
    (fun _ _ _ _ => ⟨_, rfl⟩)

/-- `FUNCT_3:6` (`Th6`) -/
theorem th6 {f g X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (hdF : RELAT_1.dom f = ZFMISC_1.product X Y)
    (hdG : RELAT_1.dom g = ZFMISC_1.product X Y)
    (hv : ∀ x y, x ∈ X → y ∈ Y →
      BINOP_1.apply2 f x y = BINOP_1.apply2 g x y) :
    f = g := by
  refine FUNCT_1.th2 hf hg (hdF.trans hdG.symm) ?_
  intro p hp
  obtain ⟨x, y, hx, hy, hpair⟩ :=
    (ZFMISC_1.def2 X Y p).mp
      (Eq.subst (motive := fun s => p ∈ s) hdF hp)
  have happ : BINOP_1.apply2 f x y = BINOP_1.apply2 g x y := hv x y hx hy
  have hf' : FUNCT_1.apply f p = FUNCT_1.apply f (TARSKI.pair x y) :=
    congrArg (FUNCT_1.apply f) hpair
  have hg' : FUNCT_1.apply g p = FUNCT_1.apply g (TARSKI.pair x y) :=
    congrArg (FUNCT_1.apply g) hpair
  exact hf'.trans (happ.trans hg'.symm)

/-! ## Function indicated by the image (`FUNCT_3:def 1`) -/

/-- `FUNCT_3:def 1` — `.:f`. -/
noncomputable def imageFunc (f : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (FUNCT_1.sch_Lambda (ZFMISC_1.bool (RELAT_1.dom f))
      (fun X => RELAT_1.image f X))

theorem imageFunc_isFunction (f : TarskiSet.{u}) :
    FUNCT_1.isFunction (imageFunc f) :=
  (Classical.choose_spec
    (FUNCT_1.sch_Lambda (ZFMISC_1.bool (RELAT_1.dom f))
      (fun X => RELAT_1.image f X))).1

theorem imageFunc_dom (f : TarskiSet.{u}) :
    RELAT_1.dom (imageFunc f) = ZFMISC_1.bool (RELAT_1.dom f) :=
  (Classical.choose_spec
    (FUNCT_1.sch_Lambda (ZFMISC_1.bool (RELAT_1.dom f))
      (fun X => RELAT_1.image f X))).2.1

theorem def1 {f X : TarskiSet.{u}} (h : X ⊆ RELAT_1.dom f) :
    FUNCT_1.apply (imageFunc f) X = RELAT_1.image f X := by
  have hx : X ∈ ZFMISC_1.bool (RELAT_1.dom f) := (ZFMISC_1.def1 _ _).mpr h
  have hxD : X ∈ RELAT_1.dom (imageFunc f) :=
    Eq.subst (motive := fun s => X ∈ s) (imageFunc_dom f).symm hx
  exact (Classical.choose_spec
    (FUNCT_1.sch_Lambda (ZFMISC_1.bool (RELAT_1.dom f))
      (fun X => RELAT_1.image f X))).2.2 X hx

theorem imageFunc_unique {f g1 g2 : TarskiSet.{u}}
    (hg1 : FUNCT_1.isFunction g1) (hg2 : FUNCT_1.isFunction g2)
    (hd1 : RELAT_1.dom g1 = ZFMISC_1.bool (RELAT_1.dom f))
    (hd2 : RELAT_1.dom g2 = ZFMISC_1.bool (RELAT_1.dom f))
    (hv1 : ∀ X, X ⊆ RELAT_1.dom f → FUNCT_1.apply g1 X = RELAT_1.image f X)
    (hv2 : ∀ X, X ⊆ RELAT_1.dom f → FUNCT_1.apply g2 X = RELAT_1.image f X) :
    g1 = g2 := by
  refine FUNCT_1.th2 hg1 hg2 (hd1.trans hd2.symm) ?_
  intro x hx
  have hxB : x ∈ ZFMISC_1.bool (RELAT_1.dom f) :=
    Eq.subst (motive := fun s => x ∈ s) hd1 hx
  have hsub : x ⊆ RELAT_1.dom f := (ZFMISC_1.def1 _ _).mp hxB
  exact (hv1 x hsub).trans (hv2 x hsub).symm

/-- `FUNCT_3:7` (`Th7`) -/
theorem th7 {f X : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f)
    (h : X ∈ RELAT_1.dom (imageFunc f)) :
    FUNCT_1.apply (imageFunc f) X = RELAT_1.image f X := by
  have hxB : X ∈ ZFMISC_1.bool (RELAT_1.dom f) :=
    Eq.subst (motive := fun s => X ∈ s) (imageFunc_dom f) h
  exact def1 ((ZFMISC_1.def1 _ _).mp hxB)

/-- Unlabeled `FUNCT_3` (`Th8`) -/
theorem th8 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    FUNCT_1.apply (imageFunc f) (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) := by
  have hsub : (∅ : TarskiSet.{u}) ⊆ RELAT_1.dom f := XBOOLE_1.th2
  have himg : RELAT_1.image f (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) := by
    apply eq_of_mem
    intro y
    constructor
    · intro hy
      obtain ⟨x, _, hxE, _⟩ := (FUNCT_1.def6 hf.2).mp hy
      exact ((XBOOLE_0.empty_iff x).mp hxE).elim
    · intro hy
      exact ((XBOOLE_0.empty_iff y).mp hy).elim
  exact (def1 hsub).trans himg

/-- `FUNCT_3:9` (`Th9`) -/
theorem th9 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    RELAT_1.rng (imageFunc f) ⊆ ZFMISC_1.bool (RELAT_1.rng f) := by
  intro y hy
  obtain ⟨x, hxD, heq⟩ := (FUNCT_1.def3 (imageFunc_isFunction f).2).mp hy
  have himg : y = RELAT_1.image f x :=
    heq.trans (th7 hf hxD)
  have hsub : RELAT_1.image f x ⊆ RELAT_1.rng f := RELAT_1.th111
  exact (ZFMISC_1.def1 _ _).mpr
    (Eq.subst (motive := fun s => s ⊆ RELAT_1.rng f) himg.symm hsub)

/-- Unlabeled `FUNCT_3` (`Th10`) -/
theorem th10 {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    RELAT_1.image (imageFunc f) A ⊆ ZFMISC_1.bool (RELAT_1.rng f) :=
  XBOOLE_1.th1 (RELAT_1.th111 (R := imageFunc f) (X := A)) (th9 hf)

/-- `FUNCT_3:11` (`Th11`) -/
theorem th11 {f B : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f) :
    RELAT_1.invimage (imageFunc f) B ⊆ ZFMISC_1.bool (RELAT_1.dom f) := by
  have hd : RELAT_1.dom (imageFunc f) = ZFMISC_1.bool (RELAT_1.dom f) :=
    imageFunc_dom f
  exact Eq.subst (motive := fun s => RELAT_1.invimage (imageFunc f) B ⊆ s)
    hd (RELAT_1.th132 (R := imageFunc f) (Y := B))

/-- Unlabeled `FUNCT_3` (`Th12`) -/
theorem th12 {f X D B : TarskiSet.{u}} (hf : FUNCT_2.isFunctionOf f X D)
    (hD : D ≠ (∅ : TarskiSet.{u})) :
    RELAT_1.invimage (imageFunc f) B ⊆ ZFMISC_1.bool X := by
  have hd : RELAT_1.dom f = X := FUNCT_2.functionOf_dom_eq hf hD
  exact Eq.subst (motive := fun s =>
      RELAT_1.invimage (imageFunc f) B ⊆ ZFMISC_1.bool s) hd
    (th11 (FUNCT_2.functionOf_isFunction hf))

/-- `FUNCT_3:13` (`Th13`) -/
theorem th13 {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    TARSKI.union (RELAT_1.image (imageFunc f) A) ⊆
      RELAT_1.image f (TARSKI.union A) := by
  intro y hy
  obtain ⟨Z, hyZ, hZ⟩ := (TARSKI.def4 (RELAT_1.image (imageFunc f) A) y).mp hy
  obtain ⟨X, hxD, hxA, hZeq⟩ :=
    (FUNCT_1.def6 (imageFunc_isFunction f).2).mp hZ
  have hy' : y ∈ RELAT_1.image f X :=
    Eq.subst (motive := fun s => y ∈ s) (hZeq.trans (th7 hf hxD)) hyZ
  obtain ⟨x, hxDf, hxX, heq⟩ := (FUNCT_1.def6 hf.2).mp hy'
  have hxU : x ∈ TARSKI.union A :=
    (TARSKI.def4 A x).mpr ⟨X, hxX, hxA⟩
  exact (FUNCT_1.def6 hf.2).mpr ⟨x, hxDf, hxU, heq⟩

/-- `FUNCT_3:14` (`Th14`) -/
theorem th14 {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hA : A ⊆ ZFMISC_1.bool (RELAT_1.dom f)) :
    RELAT_1.image f (TARSKI.union A) =
      TARSKI.union (RELAT_1.image (imageFunc f) A) := by
  refine (XBOOLE_0.def10).mpr ⟨?_, th13 hf⟩
  intro y hy
  obtain ⟨x, hxD, hxU, heq⟩ := (FUNCT_1.def6 hf.2).mp hy
  obtain ⟨X, hxX, hxA⟩ := (TARSKI.def4 A x).mp hxU
  have hxB : X ∈ ZFMISC_1.bool (RELAT_1.dom f) := hA X hxA
  have hxDom : X ∈ RELAT_1.dom (imageFunc f) :=
    Eq.subst (motive := fun s => X ∈ s) (imageFunc_dom f).symm hxB
  have hIm : FUNCT_1.apply (imageFunc f) X ∈ RELAT_1.image (imageFunc f) A :=
    (FUNCT_1.def6 (imageFunc_isFunction f).2).mpr ⟨X, hxDom, hxA, rfl⟩
  have hyX : y ∈ RELAT_1.image f X :=
    (FUNCT_1.def6 hf.2).mpr ⟨x, hxD, hxX, heq⟩
  have hyAppl : y ∈ FUNCT_1.apply (imageFunc f) X :=
    Eq.subst (motive := fun s => y ∈ s)
      (def1 ((ZFMISC_1.def1 _ _).mp hxB)).symm hyX
  exact (TARSKI.def4 (RELAT_1.image (imageFunc f) A) y).mpr
    ⟨FUNCT_1.apply (imageFunc f) X, hyAppl, hIm⟩

/-- Unlabeled `FUNCT_3` (`Th15`) -/
theorem th15 {f X D A : TarskiSet.{u}} (hf : FUNCT_2.isFunctionOf f X D)
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hA : A ⊆ ZFMISC_1.bool X) :
    RELAT_1.image f (TARSKI.union A) =
      TARSKI.union (RELAT_1.image (imageFunc f) A) := by
  have hd : RELAT_1.dom f = X := FUNCT_2.functionOf_dom_eq hf hD
  exact th14 (FUNCT_2.functionOf_isFunction hf)
    (Eq.subst (motive := fun s => A ⊆ ZFMISC_1.bool s) hd.symm hA)


/-- `FUNCT_3:16` (`Th16`) -/
theorem th16 {f B : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    TARSKI.union (RELAT_1.invimage (imageFunc f) B) ⊆
      RELAT_1.invimage f (TARSKI.union B) := by
  intro x hx
  obtain ⟨X, hxX, hX⟩ := (TARSKI.def4 (RELAT_1.invimage (imageFunc f) B) x).mp hx
  have hdImg : RELAT_1.dom (imageFunc f) = ZFMISC_1.bool (RELAT_1.dom f) :=
    imageFunc_dom f
  have ⟨hXD, hAppl⟩ := (FUNCT_1.def7 (imageFunc_isFunction f).2).mp hX
  have hxB : X ∈ ZFMISC_1.bool (RELAT_1.dom f) :=
    Eq.subst (motive := fun s => X ∈ s) hdImg hXD
  have hsub : X ⊆ RELAT_1.dom f := (ZFMISC_1.def1 _ _).mp hxB
  have hfx : FUNCT_1.apply f x ∈ RELAT_1.image f X :=
    (FUNCT_1.def6 hf.2).mpr ⟨x, hsub x hxX, hxX, rfl⟩
  have hImgB : RELAT_1.image f X ∈ B :=
    Eq.subst (motive := fun s => s ∈ B) (def1 hsub) hAppl
  have hfxU : FUNCT_1.apply f x ∈ TARSKI.union B :=
    (TARSKI.def4 B (FUNCT_1.apply f x)).mpr ⟨RELAT_1.image f X, hfx, hImgB⟩
  exact (FUNCT_1.def7 hf.2).mpr ⟨hsub x hxX, hfxU⟩

/-- Unlabeled `FUNCT_3` (`Th17`) -/
theorem th17 {f B : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hB : B ⊆ ZFMISC_1.bool (RELAT_1.rng f)) :
    RELAT_1.invimage f (TARSKI.union B) =
      TARSKI.union (RELAT_1.invimage (imageFunc f) B) := by
  refine (XBOOLE_0.def10).mpr ⟨?_, th16 hf⟩
  intro x hx
  have ⟨hxD, hfxU⟩ := (FUNCT_1.def7 hf.2).mp hx
  obtain ⟨Y, hfxY, hYB⟩ := (TARSKI.def4 B (FUNCT_1.apply f x)).mp hfxU
  have hInvSub : RELAT_1.invimage f Y ⊆ RELAT_1.dom f := RELAT_1.th132
  have hInvB : RELAT_1.invimage f Y ∈ ZFMISC_1.bool (RELAT_1.dom f) :=
    (ZFMISC_1.def1 _ _).mpr hInvSub
  have hInvDom : RELAT_1.invimage f Y ∈ RELAT_1.dom (imageFunc f) :=
    Eq.subst (motive := fun s => RELAT_1.invimage f Y ∈ s)
      (imageFunc_dom f).symm hInvB
  have hYsub : Y ⊆ RELAT_1.rng f := (ZFMISC_1.def1 _ _).mp (hB Y hYB)
  have himg : RELAT_1.image f (RELAT_1.invimage f Y) = Y :=
    FUNCT_1.th77 hf.2 hYsub
  have hApplB : FUNCT_1.apply (imageFunc f) (RELAT_1.invimage f Y) ∈ B :=
    Eq.subst (motive := fun s => s ∈ B)
      (def1 hInvSub).symm (Eq.subst (motive := fun s => s ∈ B) himg.symm hYB)
  have hInvMem : RELAT_1.invimage f Y ∈ RELAT_1.invimage (imageFunc f) B :=
    (FUNCT_1.def7 (imageFunc_isFunction f).2).mpr ⟨hInvDom, hApplB⟩
  have hxInv : x ∈ RELAT_1.invimage f Y :=
    (FUNCT_1.def7 hf.2).mpr ⟨hxD, hfxY⟩
  exact (TARSKI.def4 (RELAT_1.invimage (imageFunc f) B) x).mpr
    ⟨RELAT_1.invimage f Y, hxInv, hInvMem⟩

/-- Unlabeled `FUNCT_3` (`Th18`) — `.:(g*f) = .:g * .:f`. -/
theorem th18 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    imageFunc (RELAT_1.comp f g) =
      RELAT_1.comp (imageFunc f) (imageFunc g) := by
  have hdom : ∀ x, x ∈ RELAT_1.dom (imageFunc (RELAT_1.comp f g)) ↔
      x ∈ RELAT_1.dom (RELAT_1.comp (imageFunc f) (imageFunc g)) := by
    intro x
    constructor
    · intro hx
      have hxB : x ∈ ZFMISC_1.bool (RELAT_1.dom (RELAT_1.comp f g)) :=
        Eq.subst (motive := fun s => x ∈ s)
          (imageFunc_dom (RELAT_1.comp f g)) hx
      have hsub : x ⊆ RELAT_1.dom (RELAT_1.comp f g) :=
        (ZFMISC_1.def1 _ _).mp hxB
      have hdomSub : RELAT_1.dom (RELAT_1.comp f g) ⊆ RELAT_1.dom f :=
        RELAT_1.th25
      have hxF : x ⊆ RELAT_1.dom f := XBOOLE_1.th1 hsub hdomSub
      have hxDomF : x ∈ RELAT_1.dom (imageFunc f) :=
        Eq.subst (motive := fun s => x ∈ s) (imageFunc_dom f).symm
          ((ZFMISC_1.def1 _ _).mpr hxF)
      have himgDom : RELAT_1.image f x ⊆ RELAT_1.dom g :=
        th2 hf hg hsub
      have himgDomG : RELAT_1.image f x ∈ RELAT_1.dom (imageFunc g) :=
        Eq.subst (motive := fun s => RELAT_1.image f x ∈ s)
          (imageFunc_dom g).symm ((ZFMISC_1.def1 _ _).mpr himgDom)
      have happ : FUNCT_1.apply (imageFunc f) x ∈ RELAT_1.dom (imageFunc g) :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.dom (imageFunc g))
          (def1 hxF).symm himgDomG
      exact (FUNCT_1.th11 (imageFunc_isFunction f).2).mpr ⟨hxDomF, happ⟩
    · intro hx
      have ⟨hxF, happ⟩ := (FUNCT_1.th11 (imageFunc_isFunction f).2).mp hx
      have himg : FUNCT_1.apply (imageFunc f) x =
          RELAT_1.image f x := th7 hf hxF
      have himgDom : RELAT_1.image f x ∈ RELAT_1.dom (imageFunc g) :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.dom (imageFunc g)) himg happ
      have himgB : RELAT_1.image f x ∈ ZFMISC_1.bool (RELAT_1.dom g) :=
        Eq.subst (motive := fun s => RELAT_1.image f x ∈ s)
          (imageFunc_dom g) himgDom
      have himgSub : RELAT_1.image f x ⊆ RELAT_1.dom g :=
        (ZFMISC_1.def1 _ _).mp himgB
      have hxB : x ∈ ZFMISC_1.bool (RELAT_1.dom f) :=
        Eq.subst (motive := fun s => x ∈ s) (imageFunc_dom f) hxF
      have hxSub : x ⊆ RELAT_1.dom f := (ZFMISC_1.def1 _ _).mp hxB
      have hcompSub : x ⊆ RELAT_1.dom (RELAT_1.comp f g) :=
        th3 hf hg hxSub himgSub
      exact Eq.subst (motive := fun s => x ∈ s)
        (imageFunc_dom (RELAT_1.comp f g)).symm
        ((ZFMISC_1.def1 _ _).mpr hcompSub)
  have hdEq : RELAT_1.dom (imageFunc (RELAT_1.comp f g)) =
      RELAT_1.dom (RELAT_1.comp (imageFunc f) (imageFunc g)) :=
    eq_of_mem hdom
  refine FUNCT_1.th2 (imageFunc_isFunction _)
    (FUNCT_1.comp_isFunction (imageFunc_isFunction f) (imageFunc_isFunction g))
    hdEq ?_
  intro x hx
  have hxB : x ∈ ZFMISC_1.bool (RELAT_1.dom (RELAT_1.comp f g)) :=
    Eq.subst (motive := fun s => x ∈ s)
      (imageFunc_dom (RELAT_1.comp f g)) hx
  have hsub : x ⊆ RELAT_1.dom (RELAT_1.comp f g) :=
    (ZFMISC_1.def1 _ _).mp hxB
  have himgDom : RELAT_1.image f x ⊆ RELAT_1.dom g := th2 hf hg hsub
  have hdomSub : RELAT_1.dom (RELAT_1.comp f g) ⊆ RELAT_1.dom f :=
    RELAT_1.th25
  have hxF : x ⊆ RELAT_1.dom f := XBOOLE_1.th1 hsub hdomSub
  have hxDomF : x ∈ RELAT_1.dom (imageFunc f) :=
    Eq.subst (motive := fun s => x ∈ s) (imageFunc_dom f).symm
      ((ZFMISC_1.def1 _ _).mpr hxF)
  exact (th7 (FUNCT_1.comp_isFunction hf hg) hx).trans
    ((RELAT_1.th126 (P := f) (R := g) (X := x)).trans
      ((def1 himgDom).symm.trans
        ((congrArg (FUNCT_1.apply (imageFunc g)) (def1 hxF).symm).trans
          (FUNCT_1.th13 (imageFunc_isFunction f).2
            (imageFunc_isFunction g).2 hxDomF).symm)))


/-- `FUNCT_3:19` (`Th19`) -/
theorem th19 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    FUNCT_2.isFunctionOf (imageFunc f)
      (ZFMISC_1.bool (RELAT_1.dom f)) (ZFMISC_1.bool (RELAT_1.rng f)) := by
  have hd : RELAT_1.dom (imageFunc f) = ZFMISC_1.bool (RELAT_1.dom f) :=
    imageFunc_dom f
  have hr : RELAT_1.rng (imageFunc f) ⊆ ZFMISC_1.bool (RELAT_1.rng f) :=
    th9 hf
  exact Eq.subst (motive := fun s =>
      FUNCT_2.isFunctionOf (imageFunc f) s (ZFMISC_1.bool (RELAT_1.rng f)))
    hd (FUNCT_2.th2 (imageFunc_isFunction f) hr)

/-- `FUNCT_3:20` (`Th20`) -/
theorem th20 {f X Y : TarskiSet.{u}} (hf : FUNCT_2.isFunctionOf f X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    FUNCT_2.isFunctionOf (imageFunc f)
      (ZFMISC_1.bool X) (ZFMISC_1.bool Y) := by
  have hdF : RELAT_1.dom f = X := FUNCT_2.functionOf_dom_eq' hf h
  have hrF : RELAT_1.rng f ⊆ Y := FUNCT_2.functionOf_rng_sub hf
  have hbool : ZFMISC_1.bool (RELAT_1.rng f) ⊆ ZFMISC_1.bool Y :=
    ZFMISC_1.th67 hrF
  have hrImg : RELAT_1.rng (imageFunc f) ⊆ ZFMISC_1.bool (RELAT_1.rng f) :=
    th9 (FUNCT_2.functionOf_isFunction hf)
  have hr : RELAT_1.rng (imageFunc f) ⊆ ZFMISC_1.bool Y :=
    XBOOLE_1.th1 hrImg hbool
  exact FUNCT_2.functionOf_of (imageFunc_isFunction f)
    (Eq.subst (motive := fun s => RELAT_1.dom (imageFunc f) = ZFMISC_1.bool s)
      hdF (imageFunc_dom f))
    hr


/-- Coherence: `.:f` for `Function of X,D` (nonempty `D`). -/
theorem imageFunc_isFunctionOf {f X D : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f X D) (hD : D ≠ (∅ : TarskiSet.{u})) :
    FUNCT_2.isFunctionOf (imageFunc f)
      (ZFMISC_1.bool X) (ZFMISC_1.bool D) :=
  th20 hf (fun h => (hD h).elim)

/-! ## Inverse-image function (`FUNCT_3:def 2`) -/

/-- `FUNCT_3:def 2` — `"f`. -/
noncomputable def invimageFunc (f : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (FUNCT_1.sch_Lambda (ZFMISC_1.bool (RELAT_1.rng f))
      (fun Y => RELAT_1.invimage f Y))

theorem invimageFunc_isFunction (f : TarskiSet.{u}) :
    FUNCT_1.isFunction (invimageFunc f) :=
  (Classical.choose_spec
    (FUNCT_1.sch_Lambda (ZFMISC_1.bool (RELAT_1.rng f))
      (fun Y => RELAT_1.invimage f Y))).1

theorem invimageFunc_dom (f : TarskiSet.{u}) :
    RELAT_1.dom (invimageFunc f) = ZFMISC_1.bool (RELAT_1.rng f) :=
  (Classical.choose_spec
    (FUNCT_1.sch_Lambda (ZFMISC_1.bool (RELAT_1.rng f))
      (fun Y => RELAT_1.invimage f Y))).2.1

theorem def2 {f Y : TarskiSet.{u}} (h : Y ⊆ RELAT_1.rng f) :
    FUNCT_1.apply (invimageFunc f) Y = RELAT_1.invimage f Y := by
  have hy : Y ∈ ZFMISC_1.bool (RELAT_1.rng f) := (ZFMISC_1.def1 _ _).mpr h
  exact (Classical.choose_spec
    (FUNCT_1.sch_Lambda (ZFMISC_1.bool (RELAT_1.rng f))
      (fun Y => RELAT_1.invimage f Y))).2.2 Y hy

/-- `FUNCT_3:21` (`Th21`) -/
theorem th21 {f Y : TarskiSet.{u}}
    (h : Y ∈ RELAT_1.dom (invimageFunc f)) :
    FUNCT_1.apply (invimageFunc f) Y = RELAT_1.invimage f Y := by
  have hyB : Y ∈ ZFMISC_1.bool (RELAT_1.rng f) :=
    Eq.subst (motive := fun s => Y ∈ s) (invimageFunc_dom f) h
  exact def2 ((ZFMISC_1.def1 _ _).mp hyB)

/-- `FUNCT_3:22` (`Th22`) -/
theorem th22 {f : TarskiSet.{u}} :
    RELAT_1.rng (invimageFunc f) ⊆ ZFMISC_1.bool (RELAT_1.dom f) := by
  intro x hy
  obtain ⟨y, hyD, heq⟩ := (FUNCT_1.def3 (invimageFunc_isFunction f).2).mp hy
  have hin : x = RELAT_1.invimage f y := heq.trans (th21 hyD)
  exact (ZFMISC_1.def1 _ _).mpr
    (Eq.subst (motive := fun s => s ⊆ RELAT_1.dom f) hin.symm RELAT_1.th132)

/-- Unlabeled `FUNCT_3` (`Th23`) -/
theorem th23 {f B : TarskiSet.{u}} :
    RELAT_1.image (invimageFunc f) B ⊆ ZFMISC_1.bool (RELAT_1.dom f) :=
  XBOOLE_1.th1 (RELAT_1.th111 (R := invimageFunc f) (X := B)) th22

/-- Unlabeled `FUNCT_3` (`Th24`) -/
theorem th24 {f A : TarskiSet.{u}} :
    RELAT_1.invimage (invimageFunc f) A ⊆ ZFMISC_1.bool (RELAT_1.rng f) :=
  Eq.subst (motive := fun s => RELAT_1.invimage (invimageFunc f) A ⊆ s)
    (invimageFunc_dom f) (RELAT_1.th132 (R := invimageFunc f) (Y := A))


/-- `FUNCT_3:25` (`Th25`) -/
theorem th25 {f B : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    TARSKI.union (RELAT_1.image (invimageFunc f) B) ⊆
      RELAT_1.invimage f (TARSKI.union B) := by
  intro x hx
  obtain ⟨X, hxX, hX⟩ := (TARSKI.def4 (RELAT_1.image (invimageFunc f) B) x).mp hx
  obtain ⟨Y, hyD, hyB, hXeq⟩ :=
    (FUNCT_1.def6 (invimageFunc_isFunction f).2).mp hX
  have hInvEq : FUNCT_1.apply (invimageFunc f) Y = RELAT_1.invimage f Y :=
    th21 hyD
  have hXInv : X = RELAT_1.invimage f Y := hXeq.trans hInvEq
  have hyBool : Y ∈ ZFMISC_1.bool (RELAT_1.rng f) :=
    Eq.subst (motive := fun s => Y ∈ s) (invimageFunc_dom f) hyD
  have hYsub : Y ⊆ RELAT_1.rng f := (ZFMISC_1.def1 _ _).mp hyBool
  have himgY : RELAT_1.image f X = Y := by
    have h := FUNCT_1.th77 hf.2 hYsub
    exact Eq.subst (motive := fun s => RELAT_1.image f s = Y) hXInv.symm h
  have himgB : RELAT_1.image f X ∈ B :=
    Eq.subst (motive := fun s => s ∈ B) himgY.symm hyB
  have hsub : X ⊆ RELAT_1.dom f :=
    Eq.subst (motive := fun s => s ⊆ RELAT_1.dom f) hXInv.symm RELAT_1.th132
  have hfx : FUNCT_1.apply f x ∈ RELAT_1.image f X :=
    (FUNCT_1.def6 hf.2).mpr ⟨x, hsub x hxX, hxX, rfl⟩
  have hfxU : FUNCT_1.apply f x ∈ TARSKI.union B :=
    (TARSKI.def4 B _).mpr ⟨RELAT_1.image f X, hfx, himgB⟩
  exact (FUNCT_1.def7 hf.2).mpr ⟨hsub x hxX, hfxU⟩

/-- Unlabeled `FUNCT_3` (`Th26`) -/
theorem th26 {f B : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hB : B ⊆ ZFMISC_1.bool (RELAT_1.rng f)) :
    TARSKI.union (RELAT_1.image (invimageFunc f) B) =
      RELAT_1.invimage f (TARSKI.union B) := by
  refine (XBOOLE_0.def10).mpr ⟨th25 hf, ?_⟩
  intro x hx
  have ⟨hxD, hfxU⟩ := (FUNCT_1.def7 hf.2).mp hx
  obtain ⟨Y, hfxY, hYB⟩ := (TARSKI.def4 B _).mp hfxU
  have hxInv : x ∈ RELAT_1.invimage f Y :=
    (FUNCT_1.def7 hf.2).mpr ⟨hxD, hfxY⟩
  have hyB : Y ∈ ZFMISC_1.bool (RELAT_1.rng f) := hB Y hYB
  have hyDom : Y ∈ RELAT_1.dom (invimageFunc f) :=
    Eq.subst (motive := fun s => Y ∈ s) (invimageFunc_dom f).symm hyB
  have hAppl : FUNCT_1.apply (invimageFunc f) Y = RELAT_1.invimage f Y :=
    def2 ((ZFMISC_1.def1 _ _).mp hyB)
  have hIm : RELAT_1.invimage f Y ∈ RELAT_1.image (invimageFunc f) B :=
    (FUNCT_1.def6 (invimageFunc_isFunction f).2).mpr
      ⟨Y, hyDom, hYB, hAppl.symm⟩
  exact (TARSKI.def4 _ x).mpr ⟨RELAT_1.invimage f Y, hxInv, hIm⟩


/-- `FUNCT_3:27` (`Th27`) -/
theorem th27 {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    TARSKI.union (RELAT_1.invimage (invimageFunc f) A) ⊆
      RELAT_1.image f (TARSKI.union A) := by
  intro y hy
  obtain ⟨Y, hyY, hY⟩ := (TARSKI.def4 (RELAT_1.invimage (invimageFunc f) A) y).mp hy
  have hdInv : RELAT_1.dom (invimageFunc f) = ZFMISC_1.bool (RELAT_1.rng f) :=
    invimageFunc_dom f
  have ⟨hyDom, hAppl⟩ := (FUNCT_1.def7 (invimageFunc_isFunction f).2).mp hY
  have hyB : Y ∈ ZFMISC_1.bool (RELAT_1.rng f) :=
    Eq.subst (motive := fun s => Y ∈ s) hdInv hyDom
  have hyRng : y ∈ RELAT_1.rng f := (ZFMISC_1.def1 _ _).mp hyB y hyY
  obtain ⟨x, hxD, heq⟩ := (FUNCT_1.def3 hf.2).mp hyRng
  have hInvA : RELAT_1.invimage f Y ∈ A :=
    Eq.subst (motive := fun s => s ∈ A) (def2 ((ZFMISC_1.def1 _ _).mp hyB)) hAppl
  have hxInv : x ∈ RELAT_1.invimage f Y :=
    (FUNCT_1.def7 hf.2).mpr ⟨hxD,
      Eq.subst (motive := fun s => s ∈ Y) heq hyY⟩
  have hxU : x ∈ TARSKI.union A :=
    (TARSKI.def4 A x).mpr ⟨RELAT_1.invimage f Y, hxInv, hInvA⟩
  exact (FUNCT_1.def6 hf.2).mpr ⟨x, hxD, hxU, heq⟩

/-- Unlabeled `FUNCT_3` (`Th28`) -/
theorem th28 {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hA : A ⊆ ZFMISC_1.bool (RELAT_1.dom f)) (h1 : FUNCT_1.isOneToOne f) :
    TARSKI.union (RELAT_1.invimage (invimageFunc f) A) =
      RELAT_1.image f (TARSKI.union A) := by
  refine (XBOOLE_0.def10).mpr ⟨th27 hf, ?_⟩
  intro y hy
  obtain ⟨x, hxD, hxU, heq⟩ := (FUNCT_1.def6 hf.2).mp hy
  obtain ⟨X, hxX, hxA⟩ := (TARSKI.def4 A x).mp hxU
  have h82 : RELAT_1.invimage f (RELAT_1.image f X) ⊆ X :=
    FUNCT_1.th82 hf.2 h1
  have himgSub : RELAT_1.image f X ⊆ RELAT_1.rng f := RELAT_1.th111
  have himgDom : RELAT_1.image f X ∈ RELAT_1.dom (invimageFunc f) :=
    Eq.subst (motive := fun s => RELAT_1.image f X ∈ s)
      (invimageFunc_dom f).symm ((ZFMISC_1.def1 _ _).mpr himgSub)
  have h76 : X ⊆ RELAT_1.invimage f (RELAT_1.image f X) :=
    FUNCT_1.th76 (R := f) (X := X) ((ZFMISC_1.def1 _ _).mp (hA X hxA))
  have hInvEq : RELAT_1.invimage f (RELAT_1.image f X) = X :=
    (XBOOLE_0.def10).mpr ⟨h82, h76⟩
  have hApplA : FUNCT_1.apply (invimageFunc f) (RELAT_1.image f X) ∈ A :=
    Eq.subst (motive := fun s => s ∈ A)
      (def2 himgSub).symm
      (Eq.subst (motive := fun s => s ∈ A) hInvEq.symm hxA)
  have hInvMem : RELAT_1.image f X ∈ RELAT_1.invimage (invimageFunc f) A :=
    (FUNCT_1.def7 (invimageFunc_isFunction f).2).mpr ⟨himgDom, hApplA⟩
  have hyIm : y ∈ RELAT_1.image f X :=
    (FUNCT_1.def6 hf.2).mpr ⟨x, hxD, hxX, heq⟩
  exact (TARSKI.def4 _ y).mpr ⟨RELAT_1.image f X, hyIm, hInvMem⟩

/-- `FUNCT_3:29` (`Th29`) -/
theorem th29 {f B : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    RELAT_1.image (invimageFunc f) B ⊆
      RELAT_1.invimage (imageFunc f) B := by
  intro x hx
  obtain ⟨Y, hyD, hyB, heq⟩ :=
    (FUNCT_1.def6 (invimageFunc_isFunction f).2).mp hx
  have hInv : FUNCT_1.apply (invimageFunc f) Y = RELAT_1.invimage f Y :=
    th21 hyD
  have hxInv : x = RELAT_1.invimage f Y := heq.trans hInv
  have hsub : x ⊆ RELAT_1.dom f :=
    Eq.subst (motive := fun s => s ⊆ RELAT_1.dom f) hxInv.symm RELAT_1.th132
  have hxDom : x ∈ RELAT_1.dom (imageFunc f) :=
    Eq.subst (motive := fun s => x ∈ s) (imageFunc_dom f).symm
      ((ZFMISC_1.def1 _ _).mpr hsub)
  have hyBool : Y ∈ ZFMISC_1.bool (RELAT_1.rng f) :=
    Eq.subst (motive := fun s => Y ∈ s) (invimageFunc_dom f) hyD
  have himgB : RELAT_1.image f x ∈ B := by
    have h77 := FUNCT_1.th77 hf.2 ((ZFMISC_1.def1 _ _).mp hyBool)
    have : RELAT_1.image f (RELAT_1.invimage f Y) = Y := h77
    exact Eq.subst (motive := fun s => s ∈ B)
      (Eq.subst (motive := fun t => RELAT_1.image f t = Y) hxInv.symm this).symm
      hyB
  have happB : FUNCT_1.apply (imageFunc f) x ∈ B :=
    Eq.subst (motive := fun s => s ∈ B) (def1 hsub).symm himgB
  exact (FUNCT_1.def7 (imageFunc_isFunction f).2).mpr ⟨hxDom, happB⟩

/-- Unlabeled `FUNCT_3` (`Th30`) -/
theorem th30 {f B : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (h1 : FUNCT_1.isOneToOne f) :
    RELAT_1.image (invimageFunc f) B =
      RELAT_1.invimage (imageFunc f) B := by
  refine (XBOOLE_0.def10).mpr ⟨th29 hf, ?_⟩
  intro x hx
  have himgSub : RELAT_1.image f x ⊆ RELAT_1.rng f := RELAT_1.th111
  have himgDom : RELAT_1.image f x ∈ RELAT_1.dom (invimageFunc f) :=
    Eq.subst (motive := fun s => RELAT_1.image f x ∈ s)
      (invimageFunc_dom f).symm ((ZFMISC_1.def1 _ _).mpr himgSub)
  have ⟨hxDom, happ⟩ := (FUNCT_1.def7 (imageFunc_isFunction f).2).mp hx
  have hxBool : x ∈ ZFMISC_1.bool (RELAT_1.dom f) :=
    Eq.subst (motive := fun s => x ∈ s) (imageFunc_dom f) hxDom
  have h76 : x ⊆ RELAT_1.invimage f (RELAT_1.image f x) :=
    FUNCT_1.th76 (R := f) (X := x) ((ZFMISC_1.def1 _ _).mp hxBool)
  have h82 : RELAT_1.invimage f (RELAT_1.image f x) ⊆ x :=
    FUNCT_1.th82 hf.2 h1
  have hxEq : x = RELAT_1.invimage f (RELAT_1.image f x) :=
    (XBOOLE_0.def10).mpr ⟨h76, h82⟩
  have hxAppl : x = FUNCT_1.apply (invimageFunc f) (RELAT_1.image f x) :=
    hxEq.trans (def2 himgSub).symm
  have himgB : RELAT_1.image f x ∈ B :=
    Eq.subst (motive := fun s => s ∈ B) (th7 hf hxDom) happ
  exact (FUNCT_1.def6 (invimageFunc_isFunction f).2).mpr
    ⟨RELAT_1.image f x, himgDom, himgB, hxAppl⟩

/-- `FUNCT_3:31` (`Th31`) -/
theorem th31 {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hA : A ⊆ ZFMISC_1.bool (RELAT_1.dom f)) :
    RELAT_1.invimage (invimageFunc f) A ⊆
      RELAT_1.image (imageFunc f) A := by
  intro y hy
  have ⟨hyDom, hAppl⟩ := (FUNCT_1.def7 (invimageFunc_isFunction f).2).mp hy
  have hyBool : y ∈ ZFMISC_1.bool (RELAT_1.rng f) :=
    Eq.subst (motive := fun s => y ∈ s) (invimageFunc_dom f) hyDom
  have hInvA : RELAT_1.invimage f y ∈ A :=
    Eq.subst (motive := fun s => s ∈ A) (def2 ((ZFMISC_1.def1 _ _).mp hyBool))
      hAppl
  have hInvBool : RELAT_1.invimage f y ∈ ZFMISC_1.bool (RELAT_1.dom f) :=
    hA _ hInvA
  have hInvDom : RELAT_1.invimage f y ∈ RELAT_1.dom (imageFunc f) :=
    Eq.subst (motive := fun s => RELAT_1.invimage f y ∈ s)
      (imageFunc_dom f).symm hInvBool
  have himg : RELAT_1.image f (RELAT_1.invimage f y) = y :=
    FUNCT_1.th77 hf.2 ((ZFMISC_1.def1 _ _).mp hyBool)
  have happ : FUNCT_1.apply (imageFunc f) (RELAT_1.invimage f y) = y :=
    (def1 ((ZFMISC_1.def1 _ _).mp hInvBool)).trans himg
  exact (FUNCT_1.def6 (imageFunc_isFunction f).2).mpr
    ⟨RELAT_1.invimage f y, hInvDom, hInvA, happ.symm⟩

/-- `FUNCT_3:32` (`Th32`) -/
theorem th32 {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (h1 : FUNCT_1.isOneToOne f) :
    RELAT_1.image (imageFunc f) A ⊆
      RELAT_1.invimage (invimageFunc f) A := by
  intro y hy
  obtain ⟨x, hxDom, hxA, heq⟩ :=
    (FUNCT_1.def6 (imageFunc_isFunction f).2).mp hy
  have hxBool : x ∈ ZFMISC_1.bool (RELAT_1.dom f) :=
    Eq.subst (motive := fun s => x ∈ s) (imageFunc_dom f) hxDom
  have hyIm : y = RELAT_1.image f x := heq.trans (def1 ((ZFMISC_1.def1 _ _).mp hxBool))
  have h76 : x ⊆ RELAT_1.invimage f y :=
    Eq.subst (motive := fun s => x ⊆ RELAT_1.invimage f s) hyIm.symm
      (FUNCT_1.th76 (R := f) (X := x) ((ZFMISC_1.def1 _ _).mp hxBool))
  have himgSub : y ⊆ RELAT_1.rng f :=
    Eq.subst (motive := fun s => s ⊆ RELAT_1.rng f) hyIm.symm RELAT_1.th111
  have hyDom : y ∈ RELAT_1.dom (invimageFunc f) :=
    Eq.subst (motive := fun s => y ∈ s) (invimageFunc_dom f).symm
      ((ZFMISC_1.def1 _ _).mpr himgSub)
  have h82 : RELAT_1.invimage f y ⊆ x :=
    Eq.subst (motive := fun s => RELAT_1.invimage f s ⊆ x) hyIm.symm
      (FUNCT_1.th82 hf.2 h1)
  have hInvA : RELAT_1.invimage f y ∈ A := by
    have heq' : RELAT_1.invimage f y = x :=
      (XBOOLE_0.def10).mpr ⟨h82, h76⟩
    exact Eq.subst (motive := fun s => s ∈ A) heq'.symm hxA
  have happA : FUNCT_1.apply (invimageFunc f) y ∈ A :=
    Eq.subst (motive := fun s => s ∈ A) (def2 himgSub).symm hInvA
  exact (FUNCT_1.def7 (invimageFunc_isFunction f).2).mpr ⟨hyDom, happA⟩

/-- Unlabeled `FUNCT_3` (`Th33`) -/
theorem th33 {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (h1 : FUNCT_1.isOneToOne f) (hA : A ⊆ ZFMISC_1.bool (RELAT_1.dom f)) :
    RELAT_1.invimage (invimageFunc f) A =
      RELAT_1.image (imageFunc f) A :=
  (XBOOLE_0.def10).mpr ⟨th31 hf hA, th32 hf h1⟩

/-- Unlabeled `FUNCT_3` (`Th34`) — `"(g*f) = "f * "g`. -/
theorem th34 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (h1 : FUNCT_1.isOneToOne g) :
    invimageFunc (RELAT_1.comp f g) =
      RELAT_1.comp (invimageFunc g) (invimageFunc f) := by
  have hdom : ∀ y, y ∈ RELAT_1.dom (invimageFunc (RELAT_1.comp f g)) ↔
      y ∈ RELAT_1.dom (RELAT_1.comp (invimageFunc g) (invimageFunc f)) := by
    intro y
    constructor
    · intro hy
      have hyB : y ∈ ZFMISC_1.bool (RELAT_1.rng (RELAT_1.comp f g)) :=
        Eq.subst (motive := fun s => y ∈ s)
          (invimageFunc_dom (RELAT_1.comp f g)) hy
      have hsub : y ⊆ RELAT_1.rng (RELAT_1.comp f g) :=
        (ZFMISC_1.def1 _ _).mp hyB
      have hrngSub : RELAT_1.rng (RELAT_1.comp f g) ⊆ RELAT_1.rng g :=
        RELAT_1.th26
      have hyG : y ⊆ RELAT_1.rng g := XBOOLE_1.th1 hsub hrngSub
      have hyDomG : y ∈ RELAT_1.dom (invimageFunc g) :=
        Eq.subst (motive := fun s => y ∈ s) (invimageFunc_dom g).symm
          ((ZFMISC_1.def1 _ _).mpr hyG)
      have hInvSub : RELAT_1.invimage g y ⊆ RELAT_1.rng f :=
        th4 hf hg hsub h1
      have hInvDomF : RELAT_1.invimage g y ∈ RELAT_1.dom (invimageFunc f) :=
        Eq.subst (motive := fun s => RELAT_1.invimage g y ∈ s)
          (invimageFunc_dom f).symm ((ZFMISC_1.def1 _ _).mpr hInvSub)
      have happ : FUNCT_1.apply (invimageFunc g) y ∈
          RELAT_1.dom (invimageFunc f) :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.dom (invimageFunc f))
          (def2 hyG).symm hInvDomF
      exact (FUNCT_1.th11 (invimageFunc_isFunction g).2).mpr ⟨hyDomG, happ⟩
    · intro hy
      have ⟨hyG, happ⟩ := (FUNCT_1.th11 (invimageFunc_isFunction g).2).mp hy
      have hInv : FUNCT_1.apply (invimageFunc g) y = RELAT_1.invimage g y :=
        th21 hyG
      have hInvDom : RELAT_1.invimage g y ∈ RELAT_1.dom (invimageFunc f) :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.dom (invimageFunc f)) hInv happ
      have hInvB : RELAT_1.invimage g y ∈ ZFMISC_1.bool (RELAT_1.rng f) :=
        Eq.subst (motive := fun s => RELAT_1.invimage g y ∈ s)
          (invimageFunc_dom f) hInvDom
      have hInvSub : RELAT_1.invimage g y ⊆ RELAT_1.rng f :=
        (ZFMISC_1.def1 _ _).mp hInvB
      have hyB : y ∈ ZFMISC_1.bool (RELAT_1.rng g) :=
        Eq.subst (motive := fun s => y ∈ s) (invimageFunc_dom g) hyG
      have hySub : y ⊆ RELAT_1.rng g := (ZFMISC_1.def1 _ _).mp hyB
      have hcompSub : y ⊆ RELAT_1.rng (RELAT_1.comp f g) :=
        th5 hf hg hySub hInvSub
      exact Eq.subst (motive := fun s => y ∈ s)
        (invimageFunc_dom (RELAT_1.comp f g)).symm
        ((ZFMISC_1.def1 _ _).mpr hcompSub)
  have hdEq := eq_of_mem hdom
  refine FUNCT_1.th2 (invimageFunc_isFunction _)
    (FUNCT_1.comp_isFunction (invimageFunc_isFunction g)
      (invimageFunc_isFunction f)) hdEq ?_
  intro y hy
  have hyB : y ∈ ZFMISC_1.bool (RELAT_1.rng (RELAT_1.comp f g)) :=
    Eq.subst (motive := fun s => y ∈ s)
      (invimageFunc_dom (RELAT_1.comp f g)) hy
  have hsub : y ⊆ RELAT_1.rng (RELAT_1.comp f g) :=
    (ZFMISC_1.def1 _ _).mp hyB
  have hInvSub : RELAT_1.invimage g y ⊆ RELAT_1.rng f := th4 hf hg hsub h1
  have hrngSub : RELAT_1.rng (RELAT_1.comp f g) ⊆ RELAT_1.rng g :=
    RELAT_1.th26
  have hyG : y ⊆ RELAT_1.rng g := XBOOLE_1.th1 hsub hrngSub
  have hyDomG : y ∈ RELAT_1.dom (invimageFunc g) :=
    Eq.subst (motive := fun s => y ∈ s) (invimageFunc_dom g).symm
      ((ZFMISC_1.def1 _ _).mpr hyG)
  exact (th21 hy).trans
    ((RELAT_1.th146 (P := f) (R := g) (Y := y)).trans
      ((def2 hInvSub).symm.trans
        ((congrArg (FUNCT_1.apply (invimageFunc f)) (def2 hyG).symm).trans
          (FUNCT_1.th13 (invimageFunc_isFunction g).2
            (invimageFunc_isFunction f).2 hyDomG).symm)))


/-- Unlabeled `FUNCT_3` (`Th35`) -/
theorem th35 {f : TarskiSet.{u}} :
    FUNCT_2.isFunctionOf (invimageFunc f)
      (ZFMISC_1.bool (RELAT_1.rng f)) (ZFMISC_1.bool (RELAT_1.dom f)) :=
  Eq.subst (motive := fun s =>
      FUNCT_2.isFunctionOf (invimageFunc f) s
        (ZFMISC_1.bool (RELAT_1.dom f)))
    (invimageFunc_dom f)
    (FUNCT_2.th2 (invimageFunc_isFunction f) th22)


/-! ## Characteristic function (`FUNCT_3:def 3`) -/

/-- `FUNCT_3:def 3` — `chi(A,X)`. -/
noncomputable def chi (A X : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (FUNCT_1.sch_FuncEx X
      (fun x y => (x ∈ A → y = one) ∧ (x ∉ A → y = (∅ : TarskiSet.{u})))
      (fun x y1 y2 _ h1 h2 => by
        have := Classical.propDecidable (x ∈ A)
        by_cases hx : x ∈ A
        · exact (h1.1 hx).trans (h2.1 hx).symm
        · exact (h1.2 hx).trans (h2.2 hx).symm)
      (fun x _ => by
        have := Classical.propDecidable (x ∈ A)
        by_cases hx : x ∈ A
        · exact ⟨one, ⟨fun _ => rfl, fun hne => (hne hx).elim⟩⟩
        · exact ⟨∅, ⟨fun hin => (hx hin).elim, fun _ => rfl⟩⟩))

theorem chi_isFunction (A X : TarskiSet.{u}) : FUNCT_1.isFunction (chi A X) :=
  (Classical.choose_spec
    (FUNCT_1.sch_FuncEx X
      (fun x y => (x ∈ A → y = one) ∧ (x ∉ A → y = (∅ : TarskiSet.{u})))
      (fun x y1 y2 _ h1 h2 => by
        have := Classical.propDecidable (x ∈ A)
        by_cases hx : x ∈ A
        · exact (h1.1 hx).trans (h2.1 hx).symm
        · exact (h1.2 hx).trans (h2.2 hx).symm)
      (fun x _ => by
        have := Classical.propDecidable (x ∈ A)
        by_cases hx : x ∈ A
        · exact ⟨one, ⟨fun _ => rfl, fun hne => (hne hx).elim⟩⟩
        · exact ⟨∅, ⟨fun hin => (hx hin).elim, fun _ => rfl⟩⟩))).1

theorem chi_dom (A X : TarskiSet.{u}) : RELAT_1.dom (chi A X) = X :=
  (Classical.choose_spec
    (FUNCT_1.sch_FuncEx X
      (fun x y => (x ∈ A → y = one) ∧ (x ∉ A → y = (∅ : TarskiSet.{u})))
      (fun x y1 y2 _ h1 h2 => by
        have := Classical.propDecidable (x ∈ A)
        by_cases hx : x ∈ A
        · exact (h1.1 hx).trans (h2.1 hx).symm
        · exact (h1.2 hx).trans (h2.2 hx).symm)
      (fun x _ => by
        have := Classical.propDecidable (x ∈ A)
        by_cases hx : x ∈ A
        · exact ⟨one, ⟨fun _ => rfl, fun hne => (hne hx).elim⟩⟩
        · exact ⟨∅, ⟨fun hin => (hx hin).elim, fun _ => rfl⟩⟩))).2.1

private theorem chi_spec (A X : TarskiSet.{u}) :
    ∀ x, x ∈ X →
      (x ∈ A → FUNCT_1.apply (chi A X) x = one) ∧
      (x ∉ A → FUNCT_1.apply (chi A X) x = (∅ : TarskiSet.{u})) :=
  (Classical.choose_spec
    (FUNCT_1.sch_FuncEx X
      (fun x y => (x ∈ A → y = one) ∧ (x ∉ A → y = (∅ : TarskiSet.{u})))
      (fun x y1 y2 _ h1 h2 => by
        have := Classical.propDecidable (x ∈ A)
        by_cases hx : x ∈ A
        · exact (h1.1 hx).trans (h2.1 hx).symm
        · exact (h1.2 hx).trans (h2.2 hx).symm)
      (fun x _ => by
        have := Classical.propDecidable (x ∈ A)
        by_cases hx : x ∈ A
        · exact ⟨one, ⟨fun _ => rfl, fun hne => (hne hx).elim⟩⟩
        · exact ⟨∅, ⟨fun hin => (hx hin).elim, fun _ => rfl⟩⟩))).2.2

theorem def3 {A X x : TarskiSet.{u}} (hx : x ∈ X) :
    (x ∈ A → FUNCT_1.apply (chi A X) x = one) ∧
    (x ∉ A → FUNCT_1.apply (chi A X) x = (∅ : TarskiSet.{u})) :=
  chi_spec A X x hx

/-- `FUNCT_3:36` (`Th36`) -/
theorem th36 {A X x : TarskiSet.{u}}
    (h : FUNCT_1.apply (chi A X) x = one) : x ∈ A := by
  have := Classical.propDecidable (x ∈ X)
  by_cases hx : x ∈ X
  · have := Classical.propDecidable (x ∈ A)
    by_cases ha : x ∈ A
    · exact ha
    · have heq := (def3 hx).2 ha
      exact False.elim (one_ne_empty (h.symm.trans heq))
  · have hnd : x ∉ RELAT_1.dom (chi A X) :=
      fun hd => hx (Eq.subst (motive := fun s => x ∈ s) (chi_dom A X) hd)
    have heq := FUNCT_1.apply_of_not_mem hnd
    exact False.elim (one_ne_empty (h.symm.trans heq))

/-- Unlabeled `FUNCT_3` (`Th37`) -/
theorem th37 {A X x : TarskiSet.{u}} (h : x ∈ X \ A) :
    FUNCT_1.apply (chi A X) x = (∅ : TarskiSet.{u}) := by
  have ⟨hx, hna⟩ := (XBOOLE_0.def5 X A x).mp h
  exact (def3 hx).2 hna

/-- Unlabeled `FUNCT_3` (`Th38`) -/
theorem th38 {A B X : TarskiSet.{u}} (hA : A ⊆ X) (hB : B ⊆ X)
    (h : chi A X = chi B X) : A = B := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    have happ : FUNCT_1.apply (chi A X) x = one := (def3 (hA x hx)).1 hx
    exact th36 (Eq.subst (motive := fun s => FUNCT_1.apply s x = one) h happ)
  · intro hx
    have happ : FUNCT_1.apply (chi B X) x = one := (def3 (hB x hx)).1 hx
    exact th36 (Eq.subst (motive := fun s => FUNCT_1.apply s x = one) h.symm happ)

/-- `FUNCT_3:39` (`Th39`) -/
theorem th39 {A X : TarskiSet.{u}} :
    RELAT_1.rng (chi A X) ⊆ TARSKI.upair (∅ : TarskiSet.{u}) one := by
  intro y hy
  obtain ⟨x, hxD, heq⟩ := (FUNCT_1.def3 (chi_isFunction A X).2).mp hy
  have hx : x ∈ X := Eq.subst (motive := fun s => x ∈ s) (chi_dom A X) hxD
  have := Classical.propDecidable (x ∈ A)
  by_cases ha : x ∈ A
  · exact (TARSKI.def2 _ _ _).mpr (Or.inr (heq.trans ((def3 hx).1 ha)))
  · exact (TARSKI.def2 _ _ _).mpr (Or.inl (heq.trans ((def3 hx).2 ha)))

/-- Unlabeled `FUNCT_3` (`Th40`) -/
theorem th40 {f X : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f X (TARSKI.upair (∅ : TarskiSet.{u}) one)) :
    f = chi (RELAT_1.invimage f (TARSKI.singleton one)) X := by
  have hcod : TARSKI.upair (∅ : TarskiSet.{u}) one ≠ (∅ : TarskiSet.{u}) :=
    fun hempty =>
      (XBOOLE_0.empty_iff one).mp
        (Eq.subst (motive := fun s => one ∈ s) hempty
          ((TARSKI.def2 _ _ _).mpr (Or.inr rfl)))
  have hd : RELAT_1.dom f = X := FUNCT_2.functionOf_dom_eq hf hcod
  refine FUNCT_1.th2 (FUNCT_2.functionOf_isFunction hf) (chi_isFunction _ X)
    (hd.trans (chi_dom _ X).symm) ?_
  intro x hx
  have hxX : x ∈ X := Eq.subst (motive := fun s => x ∈ s) hd hx
  have := Classical.propDecidable
    (x ∈ RELAT_1.invimage f (TARSKI.singleton one))
  by_cases hin : x ∈ RELAT_1.invimage f (TARSKI.singleton one)
  · have ⟨_, hfx⟩ := (FUNCT_1.def7 (FUNCT_2.functionOf_isFunction hf).2).mp hin
    have heq : FUNCT_1.apply f x = one :=
      (TARSKI.singleton_iff _ _).mp hfx
    exact heq.trans ((def3 hxX).1 hin).symm
  · have hna : FUNCT_1.apply f x ∉ TARSKI.singleton one := by
      intro h1
      exact hin ((FUNCT_1.def7 (FUNCT_2.functionOf_isFunction hf).2).mpr
        ⟨hx, h1⟩)
    have hrng : RELAT_1.rng f ⊆ TARSKI.upair (∅ : TarskiSet.{u}) one :=
      FUNCT_2.functionOf_rng_sub hf
    have hfxRng : FUNCT_1.apply f x ∈ RELAT_1.rng f :=
      (FUNCT_1.def3 (FUNCT_2.functionOf_isFunction hf).2).mpr ⟨x, hx, rfl⟩
    have hfxUp : FUNCT_1.apply f x ∈ TARSKI.upair (∅ : TarskiSet.{u}) one :=
      hrng _ hfxRng
    have hfxEmpty : FUNCT_1.apply f x = (∅ : TarskiSet.{u}) := by
      rcases (TARSKI.def2 _ _ _).mp hfxUp with h | h
      · exact h
      · exact False.elim (hna ((TARSKI.singleton_iff _ _).mpr h))
    exact hfxEmpty.trans ((def3 hxX).2 hin).symm


/-- Coherence: `chi(A,X)` is `Function of X,{{},1}`. -/
theorem chi_isFunctionOf (A X : TarskiSet.{u}) :
    FUNCT_2.isFunctionOf (chi A X) X
      (TARSKI.upair (∅ : TarskiSet.{u}) one) :=
  Eq.subst (motive := fun s =>
      FUNCT_2.isFunctionOf (chi A X) s
        (TARSKI.upair (∅ : TarskiSet.{u}) one))
    (chi_dom A X)
    (FUNCT_2.th2 (chi_isFunction A X) th39)

/-! ## Inclusion map (`incl A` = `id A`) -/

/-- Synonym `incl A` for `id A`. -/
noncomputable def incl (A : TarskiSet.{u}) : TarskiSet.{u} :=
  RELAT_1.id A

theorem incl_eq_id (A : TarskiSet.{u}) : incl A = RELAT_1.id A := rfl

/-- Coherence: `incl A` is `Function of A,Y` when `A ⊆ Y`. -/
theorem incl_isFunctionOf {A Y : TarskiSet.{u}} (hA : A ⊆ Y) :
    FUNCT_2.isFunctionOf (incl A) A Y := by
  have hr : RELAT_1.rng (RELAT_1.id A) ⊆ Y :=
    Eq.subst (motive := fun s => s ⊆ Y) (RELAT_1.id_rng A).symm hA
  exact FUNCT_2.functionOf_of (FUNCT_1.id_isFunction A) (RELAT_1.id_dom A) hr

/-- Unlabeled `FUNCT_3` (`Th41`) -/
theorem th41 {A Y : TarskiSet.{u}} (hA : A ⊆ Y) :
    incl A = RELAT_1.restrict (RELAT_1.id Y) A :=
  th1 hA

/-- Unlabeled `FUNCT_3` (`Th42`) -/
theorem th42 {A Y x : TarskiSet.{u}} (hA : A ⊆ Y) (hx : x ∈ A) :
    FUNCT_1.apply (incl A) x ∈ Y := by
  have happ : FUNCT_1.apply (incl A) x = x :=
    FUNCT_1.th18 hx
  exact Eq.subst (motive := fun s => s ∈ Y) happ.symm (hA x hx)


/-! ## Projections (`FUNCT_3:def 4–5`) -/

/-- `FUNCT_3:def 4` — `pr1(X,Y)`. -/
noncomputable def pr1 (X Y : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (sch_Lambda3 X Y (fun x _ => x))

theorem pr1_isFunction (X Y : TarskiSet.{u}) :
    FUNCT_1.isFunction (pr1 X Y) :=
  (Classical.choose_spec (sch_Lambda3 X Y (fun x _ => x))).1

theorem pr1_dom (X Y : TarskiSet.{u}) :
    RELAT_1.dom (pr1 X Y) = ZFMISC_1.product X Y :=
  (Classical.choose_spec (sch_Lambda3 X Y (fun x _ => x))).2.1

theorem def4 {X Y x y : TarskiSet.{u}} (hx : x ∈ X) (hy : y ∈ Y) :
    BINOP_1.apply2 (pr1 X Y) x y = x :=
  (Classical.choose_spec (sch_Lambda3 X Y (fun x _ => x))).2.2 x y hx hy

/-- `FUNCT_3:def 5` — `pr2(X,Y)`. -/
noncomputable def pr2 (X Y : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (sch_Lambda3 X Y (fun _ y => y))

theorem pr2_isFunction (X Y : TarskiSet.{u}) :
    FUNCT_1.isFunction (pr2 X Y) :=
  (Classical.choose_spec (sch_Lambda3 X Y (fun _ y => y))).1

theorem pr2_dom (X Y : TarskiSet.{u}) :
    RELAT_1.dom (pr2 X Y) = ZFMISC_1.product X Y :=
  (Classical.choose_spec (sch_Lambda3 X Y (fun _ y => y))).2.1

theorem def5 {X Y x y : TarskiSet.{u}} (hx : x ∈ X) (hy : y ∈ Y) :
    BINOP_1.apply2 (pr2 X Y) x y = y :=
  (Classical.choose_spec (sch_Lambda3 X Y (fun _ y => y))).2.2 x y hx hy

/-- `FUNCT_3:43` (`Th43`) -/
theorem th43 {X Y : TarskiSet.{u}} :
    RELAT_1.rng (pr1 X Y) ⊆ X := by
  intro x hx
  obtain ⟨p, hpD, heq⟩ := (FUNCT_1.def3 (pr1_isFunction X Y).2).mp hx
  have hp : p ∈ ZFMISC_1.product X Y :=
    Eq.subst (motive := fun s => p ∈ s) (pr1_dom X Y) hpD
  obtain ⟨x1, y1, hx1, hy1, hpair⟩ := (ZFMISC_1.def2 X Y p).mp hp
  have happ : x = BINOP_1.apply2 (pr1 X Y) x1 y1 :=
    heq.trans (congrArg (FUNCT_1.apply (pr1 X Y)) hpair)
  exact Eq.subst (motive := fun s => s ∈ X) (happ.trans (def4 hx1 hy1)).symm hx1

/-- Unlabeled `FUNCT_3` (`Th44`) -/
theorem th44 {X Y : TarskiSet.{u}} (hY : Y ≠ (∅ : TarskiSet.{u})) :
    RELAT_1.rng (pr1 X Y) = X := by
  refine (XBOOLE_0.def10).mpr ⟨th43, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := XBOOLE_0.th7 hY
  have hp : TARSKI.pair x y ∈ ZFMISC_1.product X Y :=
    (ZFMISC_1.th87).mpr ⟨hx, hy⟩
  have hpD : TARSKI.pair x y ∈ RELAT_1.dom (pr1 X Y) :=
    Eq.subst (motive := fun s => TARSKI.pair x y ∈ s) (pr1_dom X Y).symm hp
  have happ : BINOP_1.apply2 (pr1 X Y) x y = x := def4 hx hy
  exact (FUNCT_1.def3 (pr1_isFunction X Y).2).mpr
    ⟨TARSKI.pair x y, hpD, happ.symm⟩

/-- `FUNCT_3:45` (`Th45`) -/
theorem th45 {X Y : TarskiSet.{u}} :
    RELAT_1.rng (pr2 X Y) ⊆ Y := by
  intro y hy
  obtain ⟨p, hpD, heq⟩ := (FUNCT_1.def3 (pr2_isFunction X Y).2).mp hy
  have hp : p ∈ ZFMISC_1.product X Y :=
    Eq.subst (motive := fun s => p ∈ s) (pr2_dom X Y) hpD
  obtain ⟨x1, y1, hx1, hy1, hpair⟩ := (ZFMISC_1.def2 X Y p).mp hp
  have happ : y = BINOP_1.apply2 (pr2 X Y) x1 y1 :=
    heq.trans (congrArg (FUNCT_1.apply (pr2 X Y)) hpair)
  exact Eq.subst (motive := fun s => s ∈ Y) (happ.trans (def5 hx1 hy1)).symm hy1

/-- Unlabeled `FUNCT_3` (`Th46`) -/
theorem th46 {X Y : TarskiSet.{u}} (hX : X ≠ (∅ : TarskiSet.{u})) :
    RELAT_1.rng (pr2 X Y) = Y := by
  refine (XBOOLE_0.def10).mpr ⟨th45, ?_⟩
  intro y hy
  obtain ⟨x, hx⟩ := XBOOLE_0.th7 hX
  have hp : TARSKI.pair x y ∈ ZFMISC_1.product X Y :=
    (ZFMISC_1.th87).mpr ⟨hx, hy⟩
  have hpD : TARSKI.pair x y ∈ RELAT_1.dom (pr2 X Y) :=
    Eq.subst (motive := fun s => TARSKI.pair x y ∈ s) (pr2_dom X Y).symm hp
  have happ : BINOP_1.apply2 (pr2 X Y) x y = y := def5 hx hy
  exact (FUNCT_1.def3 (pr2_isFunction X Y).2).mpr
    ⟨TARSKI.pair x y, hpD, happ.symm⟩


/-- Coherence: `pr1(X,Y)` is `Function of [:X,Y:],X`. -/
theorem pr1_isFunctionOf (X Y : TarskiSet.{u}) :
    FUNCT_2.isFunctionOf (pr1 X Y) (ZFMISC_1.product X Y) X :=
  FUNCT_2.functionOf_of (pr1_isFunction X Y) (pr1_dom X Y) th43

/-- Coherence: `pr2(X,Y)` is `Function of [:X,Y:],Y`. -/
theorem pr2_isFunctionOf (X Y : TarskiSet.{u}) :
    FUNCT_2.isFunctionOf (pr2 X Y) (ZFMISC_1.product X Y) Y :=
  FUNCT_2.functionOf_of (pr2_isFunction X Y) (pr2_dom X Y) th45

/-! ## Diagonal (`FUNCT_3:def 6`) -/

/-- `FUNCT_3:def 6` — `delta(X)`. -/
noncomputable def delta (X : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (FUNCT_1.sch_Lambda X (fun x => TARSKI.pair x x))

theorem delta_isFunction (X : TarskiSet.{u}) :
    FUNCT_1.isFunction (delta X) :=
  (Classical.choose_spec
    (FUNCT_1.sch_Lambda X (fun x => TARSKI.pair x x))).1

theorem delta_dom (X : TarskiSet.{u}) :
    RELAT_1.dom (delta X) = X :=
  (Classical.choose_spec
    (FUNCT_1.sch_Lambda X (fun x => TARSKI.pair x x))).2.1

theorem def6 {X x : TarskiSet.{u}} (hx : x ∈ X) :
    FUNCT_1.apply (delta X) x = TARSKI.pair x x :=
  (Classical.choose_spec
    (FUNCT_1.sch_Lambda X (fun x => TARSKI.pair x x))).2.2 x hx

/-- `FUNCT_3:47` (`Th47`) -/
theorem th47 {X : TarskiSet.{u}} :
    RELAT_1.rng (delta X) ⊆ ZFMISC_1.product X X := by
  intro y hy
  obtain ⟨x, hxD, heq⟩ := (FUNCT_1.def3 (delta_isFunction X).2).mp hy
  have hx : x ∈ X := Eq.subst (motive := fun s => x ∈ s) (delta_dom X) hxD
  have heq' : y = TARSKI.pair x x := heq.trans (def6 hx)
  exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product X X) heq'.symm
    ((ZFMISC_1.th87).mpr ⟨hx, hx⟩)

theorem delta_isFunctionOf (X : TarskiSet.{u}) :
    FUNCT_2.isFunctionOf (delta X) X (ZFMISC_1.product X X) :=
  FUNCT_2.functionOf_of (delta_isFunction X) (delta_dom X) th47


/-! ## Complex functions (`FUNCT_3:def 7`) -/

/-- `FUNCT_3:def 7` — `<:f,g:>`. -/
noncomputable def complex (f g : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (FUNCT_1.sch_Lambda (RELAT_1.dom f ∩ RELAT_1.dom g)
      (fun x => TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x)))

theorem complex_isFunction (f g : TarskiSet.{u}) :
    FUNCT_1.isFunction (complex f g) :=
  (Classical.choose_spec
    (FUNCT_1.sch_Lambda (RELAT_1.dom f ∩ RELAT_1.dom g)
      (fun x => TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x)))).1

theorem complex_dom (f g : TarskiSet.{u}) :
    RELAT_1.dom (complex f g) = RELAT_1.dom f ∩ RELAT_1.dom g :=
  (Classical.choose_spec
    (FUNCT_1.sch_Lambda (RELAT_1.dom f ∩ RELAT_1.dom g)
      (fun x => TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x)))).2.1

theorem def7 {f g x : TarskiSet.{u}}
    (hx : x ∈ RELAT_1.dom (complex f g)) :
    FUNCT_1.apply (complex f g) x =
      TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x) := by
  have hxI : x ∈ RELAT_1.dom f ∩ RELAT_1.dom g :=
    Eq.subst (motive := fun s => x ∈ s) (complex_dom f g) hx
  exact (Classical.choose_spec
    (FUNCT_1.sch_Lambda (RELAT_1.dom f ∩ RELAT_1.dom g)
      (fun x => TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x)))).2.2 x hxI

/-- Registration: `<:f,g:>` empty when `f` is empty. -/
theorem complex_empty_left {f g : TarskiSet.{u}}
    (hf : f = (∅ : TarskiSet.{u})) :
    complex f g = (∅ : TarskiSet.{u}) := by
  have hdom : RELAT_1.dom (complex f g) = (∅ : TarskiSet.{u}) := by
    have h1 : RELAT_1.dom f = (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u})) hf.symm
        RELAT_1.th38.1
    exact (complex_dom f g).trans
      (Eq.subst (motive := fun s => s ∩ RELAT_1.dom g = (∅ : TarskiSet.{u}))
        h1.symm (by
          apply eq_of_mem; intro x; constructor
          · intro hx
            exact ((XBOOLE_0.def4 (∅ : TarskiSet) (RELAT_1.dom g) x).mp hx).1
          · intro hx; exact ((XBOOLE_0.empty_iff x).mp hx).elim))
  exact RELAT_1.th41 (complex_isFunction f g).1 (Or.inl hdom)

theorem complex_empty_right {f g : TarskiSet.{u}}
    (hg : g = (∅ : TarskiSet.{u})) :
    complex f g = (∅ : TarskiSet.{u}) := by
  have hdom : RELAT_1.dom (complex f g) = (∅ : TarskiSet.{u}) := by
    have h1 : RELAT_1.dom g = (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u})) hg.symm
        RELAT_1.th38.1
    exact (complex_dom f g).trans
      (Eq.subst (motive := fun s => RELAT_1.dom f ∩ s = (∅ : TarskiSet.{u}))
        h1.symm (by
          apply eq_of_mem; intro x; constructor
          · intro hx
            exact ((XBOOLE_0.def4 (RELAT_1.dom f) (∅ : TarskiSet) x).mp hx).2
          · intro hx; exact ((XBOOLE_0.empty_iff x).mp hx).elim))
  exact RELAT_1.th41 (complex_isFunction f g).1 (Or.inl hdom)

/-- `FUNCT_3:48` (`Th48`) -/
theorem th48 {f g x : TarskiSet.{u}}
    (hx : x ∈ RELAT_1.dom f ∩ RELAT_1.dom g) :
    FUNCT_1.apply (complex f g) x =
      TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x) :=
  def7 (Eq.subst (motive := fun s => x ∈ s) (complex_dom f g).symm hx)

/-- `FUNCT_3:49` (`Th49`) -/
theorem th49 {f g X x : TarskiSet.{u}}
    (hdF : RELAT_1.dom f = X) (hdG : RELAT_1.dom g = X) (hx : x ∈ X) :
    FUNCT_1.apply (complex f g) x =
      TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x) := by
  have hxI : x ∈ RELAT_1.dom f ∩ RELAT_1.dom g :=
    (XBOOLE_0.def4 _ _ _).mpr
      ⟨Eq.subst (motive := fun s => x ∈ s) hdF.symm hx,
        Eq.subst (motive := fun s => x ∈ s) hdG.symm hx⟩
  exact th48 hxI

/-- `FUNCT_3:50` (`Th50`) -/
theorem th50 {f g X : TarskiSet.{u}}
    (hdF : RELAT_1.dom f = X) (hdG : RELAT_1.dom g = X) :
    RELAT_1.dom (complex f g) = X :=
  (complex_dom f g).trans
    (Eq.subst (motive := fun s => s ∩ RELAT_1.dom g = X) hdF.symm
      (Eq.subst (motive := fun s => X ∩ s = X) hdG.symm
        (XBOOLE_1.th28 (fun _ h => h))))

/-- `FUNCT_3:51` (`Th51`) -/
theorem th51 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    RELAT_1.rng (complex f g) ⊆
      ZFMISC_1.product (RELAT_1.rng f) (RELAT_1.rng g) := by
  intro q hq
  obtain ⟨x, hxD, heq⟩ := (FUNCT_1.def3 (complex_isFunction f g).2).mp hq
  have hxI : x ∈ RELAT_1.dom f ∩ RELAT_1.dom g :=
    Eq.subst (motive := fun s => x ∈ s) (complex_dom f g) hxD
  have ⟨hxF, hxG⟩ := (XBOOLE_0.def4 _ _ _).mp hxI
  have hfR : FUNCT_1.apply f x ∈ RELAT_1.rng f :=
    (FUNCT_1.def3 hf.2).mpr ⟨x, hxF, rfl⟩
  have hgR : FUNCT_1.apply g x ∈ RELAT_1.rng g :=
    (FUNCT_1.def3 hg.2).mpr ⟨x, hxG, rfl⟩
  have heq' : q = TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x) :=
    heq.trans (def7 hxD)
  exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product _ _) heq'.symm
    ((ZFMISC_1.th87).mpr ⟨hfR, hgR⟩)

/-- `FUNCT_3:52` (`Th52`) -/
theorem th52 {f g Y Z : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hd : RELAT_1.dom f = RELAT_1.dom g)
    (hrF : RELAT_1.rng f ⊆ Y) (hrG : RELAT_1.rng g ⊆ Z) :
    RELAT_1.comp (complex f g) (pr1 Y Z) = f ∧
    RELAT_1.comp (complex f g) (pr2 Y Z) = g := by
  have hprod : ZFMISC_1.product (RELAT_1.rng f) (RELAT_1.rng g) ⊆
      ZFMISC_1.product Y Z := ZFMISC_1.th96 hrF hrG
  have hrC := th51 hf hg
  have hdC : RELAT_1.dom (complex f g) = RELAT_1.dom f :=
    th50 (X := RELAT_1.dom f) rfl hd.symm
  have hrngSub1 : RELAT_1.rng (complex f g) ⊆ RELAT_1.dom (pr1 Y Z) :=
    Eq.subst (motive := fun s => RELAT_1.rng (complex f g) ⊆ s)
      (pr1_dom Y Z).symm (XBOOLE_1.th1 hrC hprod)
  have hdEq1 : RELAT_1.dom (RELAT_1.comp (complex f g) (pr1 Y Z)) =
      RELAT_1.dom f :=
    (RELAT_1.th27 hrngSub1).trans hdC
  have left : RELAT_1.comp (complex f g) (pr1 Y Z) = f := by
    refine FUNCT_1.th2 (FUNCT_1.comp_isFunction (complex_isFunction f g)
        (pr1_isFunction Y Z)) hf hdEq1 ?_
    intro x hx
    have hxF : x ∈ RELAT_1.dom f :=
      Eq.subst (motive := fun s => x ∈ s) hdEq1 hx
    have hxC : x ∈ RELAT_1.dom (complex f g) :=
      Eq.subst (motive := fun s => x ∈ s) hdC.symm hxF
    have hxG : x ∈ RELAT_1.dom g :=
      Eq.subst (motive := fun s => x ∈ s) hd hxF
    have hfR : FUNCT_1.apply f x ∈ RELAT_1.rng f :=
      (FUNCT_1.def3 hf.2).mpr ⟨x, hxF, rfl⟩
    have hgR : FUNCT_1.apply g x ∈ RELAT_1.rng g :=
      (FUNCT_1.def3 hg.2).mpr ⟨x, hxG, rfl⟩
    exact (FUNCT_1.th12 (complex_isFunction f g).2 (pr1_isFunction Y Z).2 hx).trans
      (Eq.subst (motive := fun s => FUNCT_1.apply (pr1 Y Z) s = FUNCT_1.apply f x)
        (def7 hxC).symm (def4 (hrF _ hfR) (hrG _ hgR)))
  have hrngSub2 : RELAT_1.rng (complex f g) ⊆ RELAT_1.dom (pr2 Y Z) :=
    Eq.subst (motive := fun s => RELAT_1.rng (complex f g) ⊆ s)
      (pr2_dom Y Z).symm (XBOOLE_1.th1 hrC hprod)
  have hdEq2 : RELAT_1.dom (RELAT_1.comp (complex f g) (pr2 Y Z)) =
      RELAT_1.dom g :=
    (RELAT_1.th27 hrngSub2).trans
      (th50 (X := RELAT_1.dom g) hd rfl)
  have right : RELAT_1.comp (complex f g) (pr2 Y Z) = g := by
    refine FUNCT_1.th2 (FUNCT_1.comp_isFunction (complex_isFunction f g)
        (pr2_isFunction Y Z)) hg hdEq2 ?_
    intro x hx
    have hxG : x ∈ RELAT_1.dom g :=
      Eq.subst (motive := fun s => x ∈ s) hdEq2 hx
    have hxC : x ∈ RELAT_1.dom (complex f g) :=
      Eq.subst (motive := fun s => x ∈ s)
        (th50 (X := RELAT_1.dom g) hd rfl).symm hxG
    have hxF : x ∈ RELAT_1.dom f :=
      Eq.subst (motive := fun s => x ∈ s) hd.symm hxG
    have hfR : FUNCT_1.apply f x ∈ RELAT_1.rng f :=
      (FUNCT_1.def3 hf.2).mpr ⟨x, hxF, rfl⟩
    have hgR : FUNCT_1.apply g x ∈ RELAT_1.rng g :=
      (FUNCT_1.def3 hg.2).mpr ⟨x, hxG, rfl⟩
    exact (FUNCT_1.th12 (complex_isFunction f g).2 (pr2_isFunction Y Z).2 hx).trans
      (Eq.subst (motive := fun s => FUNCT_1.apply (pr2 Y Z) s = FUNCT_1.apply g x)
        (def7 hxC).symm (def5 (hrF _ hfR) (hrG _ hgR)))
  exact ⟨left, right⟩

/-- `FUNCT_3:53` (`Th53`) -/
theorem th53 {X Y : TarskiSet.{u}} :
    complex (pr1 X Y) (pr2 X Y) = RELAT_1.id (ZFMISC_1.product X Y) := by
  have hd : RELAT_1.dom (complex (pr1 X Y) (pr2 X Y)) =
      ZFMISC_1.product X Y :=
    th50 (pr1_dom X Y) (pr2_dom X Y)
  refine th6 (complex_isFunction _ _) (FUNCT_1.id_isFunction _)
    hd (RELAT_1.id_dom _) ?_
  intro x y hx hy
  have hp : TARSKI.pair x y ∈ ZFMISC_1.product X Y :=
    (ZFMISC_1.th87).mpr ⟨hx, hy⟩
  have hxI : TARSKI.pair x y ∈ RELAT_1.dom (pr1 X Y) ∩ RELAT_1.dom (pr2 X Y) :=
    (XBOOLE_0.def4 _ _ _).mpr
      ⟨Eq.subst (motive := fun s => TARSKI.pair x y ∈ s) (pr1_dom X Y).symm hp,
        Eq.subst (motive := fun s => TARSKI.pair x y ∈ s) (pr2_dom X Y).symm hp⟩
  exact (th48 hxI).trans
    ((Eq.trans
        (congrArg (fun a => TARSKI.pair a (BINOP_1.apply2 (pr2 X Y) x y))
          (def4 hx hy))
        (congrArg (TARSKI.pair x) (def5 hx hy))).trans
      (FUNCT_1.th18 hp).symm)

/-- `FUNCT_3:54` (`Th54`) -/
theorem th54 {f g h k : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (hk : FUNCT_1.isFunction k)
    (hd1 : RELAT_1.dom f = RELAT_1.dom g)
    (hd2 : RELAT_1.dom k = RELAT_1.dom h)
    (heq : complex f g = complex k h) :
    f = k ∧ g = h := by
  have hdC : RELAT_1.dom (complex f g) = RELAT_1.dom f :=
    th50 (X := RELAT_1.dom f) rfl hd1.symm
  have hdCk : RELAT_1.dom (complex k h) = RELAT_1.dom k :=
    th50 (X := RELAT_1.dom k) rfl hd2.symm
  have hdFk : RELAT_1.dom f = RELAT_1.dom k :=
    hdC.symm.trans (Eq.subst (motive := fun s => RELAT_1.dom s = RELAT_1.dom k)
      heq.symm hdCk)
  refine ⟨FUNCT_1.th2 hf hk hdFk ?_, ?_⟩
  · intro x hx
    have hxC : x ∈ RELAT_1.dom (complex f g) :=
      Eq.subst (motive := fun s => x ∈ s) hdC.symm hx
    have h1 := def7 hxC
    have hxCk : x ∈ RELAT_1.dom (complex k h) :=
      Eq.subst (motive := fun s => x ∈ RELAT_1.dom s) heq hxC
    have h2 := def7 hxCk
    have heqApp : FUNCT_1.apply (complex f g) x =
        FUNCT_1.apply (complex k h) x :=
      congrArg (fun s => FUNCT_1.apply s x) heq
    exact (XTUPLE_0.th1 (h1.symm.trans (heqApp.trans h2))).1
  · have hdCg : RELAT_1.dom (complex f g) = RELAT_1.dom g :=
      th50 (X := RELAT_1.dom g) hd1 rfl
    have hdCh : RELAT_1.dom (complex k h) = RELAT_1.dom h :=
      th50 (X := RELAT_1.dom h) hd2 rfl
    have hdGh : RELAT_1.dom g = RELAT_1.dom h :=
      hdCg.symm.trans (Eq.subst (motive := fun s =>
          RELAT_1.dom s = RELAT_1.dom h) heq.symm hdCh)
    refine FUNCT_1.th2 hg hh hdGh ?_
    intro x hx
    have hxC : x ∈ RELAT_1.dom (complex f g) :=
      Eq.subst (motive := fun s => x ∈ s) hdCg.symm hx
    have h1 := def7 hxC
    have hxCk : x ∈ RELAT_1.dom (complex k h) :=
      Eq.subst (motive := fun s => x ∈ RELAT_1.dom s) heq hxC
    have h2 := def7 hxCk
    have heqApp : FUNCT_1.apply (complex f g) x =
        FUNCT_1.apply (complex k h) x :=
      congrArg (fun s => FUNCT_1.apply s x) heq
    exact (XTUPLE_0.th1 (h1.symm.trans (heqApp.trans h2))).2



/-- Unlabeled `FUNCT_3` (`Th55`) — `<:f*h,g*h:> = <:f,g:>*h`. -/
theorem th55 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h) :
    complex (RELAT_1.comp h f) (RELAT_1.comp h g) =
      RELAT_1.comp h (complex f g) := by
  have hdom : ∀ x, x ∈ RELAT_1.dom (complex (RELAT_1.comp h f) (RELAT_1.comp h g)) ↔
      x ∈ RELAT_1.dom (RELAT_1.comp h (complex f g)) := by
    intro x
    constructor
    · intro hx
      have hxI : x ∈ RELAT_1.dom (RELAT_1.comp h f) ∩ RELAT_1.dom (RELAT_1.comp h g) :=
        Eq.subst (motive := fun s => x ∈ s)
          (complex_dom (RELAT_1.comp h f) (RELAT_1.comp h g)) hx
      have ⟨hxF, hxG⟩ := (XBOOLE_0.def4 _ _ _).mp hxI
      have ⟨hxH, hfx⟩ := (FUNCT_1.th11 hh.2).mp hxF
      have ⟨_, hgx⟩ := (FUNCT_1.th11 hh.2).mp hxG
      have hhC : FUNCT_1.apply h x ∈ RELAT_1.dom f ∩ RELAT_1.dom g :=
        (XBOOLE_0.def4 _ _ _).mpr ⟨hfx, hgx⟩
      have hhDom : FUNCT_1.apply h x ∈ RELAT_1.dom (complex f g) :=
        Eq.subst (motive := fun s => FUNCT_1.apply h x ∈ s)
          (complex_dom f g).symm hhC
      exact (FUNCT_1.th11 hh.2).mpr ⟨hxH, hhDom⟩
    · intro hx
      have ⟨hxH, hhDom⟩ := (FUNCT_1.th11 hh.2).mp hx
      have hhI : FUNCT_1.apply h x ∈ RELAT_1.dom f ∩ RELAT_1.dom g :=
        Eq.subst (motive := fun s => FUNCT_1.apply h x ∈ s)
          (complex_dom f g) hhDom
      have ⟨hfx, hgx⟩ := (XBOOLE_0.def4 _ _ _).mp hhI
      have hxF : x ∈ RELAT_1.dom (RELAT_1.comp h f) :=
        (FUNCT_1.th11 hh.2).mpr ⟨hxH, hfx⟩
      have hxG : x ∈ RELAT_1.dom (RELAT_1.comp h g) :=
        (FUNCT_1.th11 hh.2).mpr ⟨hxH, hgx⟩
      exact Eq.subst (motive := fun s => x ∈ s)
        (complex_dom (RELAT_1.comp h f) (RELAT_1.comp h g)).symm
        ((XBOOLE_0.def4 _ _ _).mpr ⟨hxF, hxG⟩)
  have hdEq := eq_of_mem hdom
  refine FUNCT_1.th2 (complex_isFunction _ _)
    (FUNCT_1.comp_isFunction hh (complex_isFunction f g)) hdEq ?_
  intro x hx
  have hxI : x ∈ RELAT_1.dom (RELAT_1.comp h f) ∩ RELAT_1.dom (RELAT_1.comp h g) :=
    Eq.subst (motive := fun s => x ∈ s)
      (complex_dom (RELAT_1.comp h f) (RELAT_1.comp h g)) hx
  have ⟨hxF, hxG⟩ := (XBOOLE_0.def4 _ _ _).mp hxI
  have ⟨hxH, _⟩ := (FUNCT_1.th11 hh.2).mp hxF
  have hhI : FUNCT_1.apply h x ∈ RELAT_1.dom f ∩ RELAT_1.dom g := by
    have ⟨_, hfx⟩ := (FUNCT_1.th11 hh.2).mp hxF
    have ⟨_, hgx⟩ := (FUNCT_1.th11 hh.2).mp hxG
    exact (XBOOLE_0.def4 _ _ _).mpr ⟨hfx, hgx⟩
  exact (def7 hx).trans
    ((Eq.trans
        (congrArg (fun a => TARSKI.pair a (FUNCT_1.apply (RELAT_1.comp h g) x))
          (FUNCT_1.th12 hh.2 hf.2 hxF))
        (congrArg (TARSKI.pair (FUNCT_1.apply f (FUNCT_1.apply h x)))
          (FUNCT_1.th12 hh.2 hg.2 hxG))).trans
      ((th48 hhI).symm.trans
        (FUNCT_1.th13 hh.2 (complex_isFunction f g).2 hxH).symm))

/-- Unlabeled `FUNCT_3` (`Th56`) -/
theorem th56 {f g A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    RELAT_1.image (complex f g) A ⊆
      ZFMISC_1.product (RELAT_1.image f A) (RELAT_1.image g A) := by
  intro y hy
  obtain ⟨x, hxD, hxA, heq⟩ :=
    (FUNCT_1.def6 (complex_isFunction f g).2).mp hy
  have hxI : x ∈ RELAT_1.dom f ∩ RELAT_1.dom g :=
    Eq.subst (motive := fun s => x ∈ s) (complex_dom f g) hxD
  have ⟨hxF, hxG⟩ := (XBOOLE_0.def4 _ _ _).mp hxI
  have hfA : FUNCT_1.apply f x ∈ RELAT_1.image f A :=
    (FUNCT_1.def6 hf.2).mpr ⟨x, hxF, hxA, rfl⟩
  have hgA : FUNCT_1.apply g x ∈ RELAT_1.image g A :=
    (FUNCT_1.def6 hg.2).mpr ⟨x, hxG, hxA, rfl⟩
  have heq' : y = TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x) :=
    heq.trans (def7 hxD)
  exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product _ _) heq'.symm
    ((ZFMISC_1.def2 _ _ _).mpr ⟨FUNCT_1.apply f x, FUNCT_1.apply g x, hfA, hgA, rfl⟩)

/-- Unlabeled `FUNCT_3` (`Th57`) -/
theorem th57 {f g B C : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    RELAT_1.invimage (complex f g) (ZFMISC_1.product B C) =
      RELAT_1.invimage f B ∩ RELAT_1.invimage g C := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    have ⟨hxD, happ⟩ := (FUNCT_1.def7 (complex_isFunction f g).2).mp hx
    have hxI : x ∈ RELAT_1.dom f ∩ RELAT_1.dom g :=
      Eq.subst (motive := fun s => x ∈ s) (complex_dom f g) hxD
    have ⟨hxF, hxG⟩ := (XBOOLE_0.def4 _ _ _).mp hxI
    have heq : FUNCT_1.apply (complex f g) x =
        TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x) := def7 hxD
    have hp : TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x) ∈
        ZFMISC_1.product B C :=
      Eq.subst (motive := fun s => s ∈ ZFMISC_1.product B C) heq happ
    obtain ⟨y1, y2, hy1, hy2, hpair⟩ := (ZFMISC_1.def2 B C _).mp hp
    have ⟨e1, e2⟩ := XTUPLE_0.th1 hpair
    have hxGB : x ∈ RELAT_1.invimage g C :=
      (FUNCT_1.def7 hg.2).mpr ⟨hxG,
        Eq.subst (motive := fun s => s ∈ C) e2.symm hy2⟩
    have hxFB : x ∈ RELAT_1.invimage f B :=
      (FUNCT_1.def7 hf.2).mpr ⟨hxF,
        Eq.subst (motive := fun s => s ∈ B) e1.symm hy1⟩
    exact (XBOOLE_0.def4 _ _ _).mpr ⟨hxFB, hxGB⟩
  · intro hx
    have ⟨hxF, hxG⟩ := (XBOOLE_0.def4 _ _ _).mp hx
    have ⟨hdF, hfB⟩ := (FUNCT_1.def7 hf.2).mp hxF
    have ⟨hdG, hgC⟩ := (FUNCT_1.def7 hg.2).mp hxG
    have hxI : x ∈ RELAT_1.dom f ∩ RELAT_1.dom g :=
      (XBOOLE_0.def4 _ _ _).mpr ⟨hdF, hdG⟩
    have hxD : x ∈ RELAT_1.dom (complex f g) :=
      Eq.subst (motive := fun s => x ∈ s) (complex_dom f g).symm hxI
    have hp : TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x) ∈
        ZFMISC_1.product B C :=
      (ZFMISC_1.def2 _ _ _).mpr ⟨_, _, hfB, hgC, rfl⟩
    exact (FUNCT_1.def7 (complex_isFunction f g).2).mpr
      ⟨hxD, Eq.subst (motive := fun s => s ∈ ZFMISC_1.product B C)
        (th48 hxI).symm hp⟩

/-! ## Product-functions (`FUNCT_3:def 8`) -/

/-- `FUNCT_3:def 8` — `[:f,g:]`. -/
noncomputable def productFunc (f g : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (sch_Lambda3 (RELAT_1.dom f) (RELAT_1.dom g)
      (fun x y => TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g y)))

theorem productFunc_isFunction (f g : TarskiSet.{u}) :
    FUNCT_1.isFunction (productFunc f g) :=
  (Classical.choose_spec
    (sch_Lambda3 (RELAT_1.dom f) (RELAT_1.dom g)
      (fun x y => TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g y)))).1

theorem productFunc_dom (f g : TarskiSet.{u}) :
    RELAT_1.dom (productFunc f g) =
      ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom g) :=
  (Classical.choose_spec
    (sch_Lambda3 (RELAT_1.dom f) (RELAT_1.dom g)
      (fun x y => TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g y)))).2.1

theorem def8 {f g x y : TarskiSet.{u}}
    (hx : x ∈ RELAT_1.dom f) (hy : y ∈ RELAT_1.dom g) :
    BINOP_1.apply2 (productFunc f g) x y =
      TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g y) :=
  (Classical.choose_spec
    (sch_Lambda3 (RELAT_1.dom f) (RELAT_1.dom g)
      (fun x y => TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g y)))).2.2
    x y hx hy

/-- Unlabeled `FUNCT_3` (`Th59`) -/
theorem th59 {f1 f2 C D1 D2 c : TarskiSet.{u}}
    (hC : C ≠ (∅ : TarskiSet.{u}))
    (hD1 : D1 ≠ (∅ : TarskiSet.{u})) (hD2 : D2 ≠ (∅ : TarskiSet.{u}))
    (hf1 : FUNCT_2.isFunctionOf f1 C D1)
    (hf2 : FUNCT_2.isFunctionOf f2 C D2)
    (hc : SUBSET_1.isElement c C) :
    FUNCT_1.apply (complex f1 f2) c =
      TARSKI.pair (FUNCT_1.apply f1 c) (FUNCT_1.apply f2 c) := by
  have hd1 := FUNCT_2.functionOf_dom_eq hf1 hD1
  have hd2 := FUNCT_2.functionOf_dom_eq hf2 hD2
  have hc' : c ∈ C := SUBSET_1.isElement_mem (ne_imp_not_empty hC) hc
  exact th49 hd1 hd2 hc'

/-- Unlabeled `FUNCT_3` (`Th60`) -/
theorem th60 {f g X Y Z : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f X Y) (hg : FUNCT_2.isFunctionOf g X Z) :
    RELAT_1.rng (complex f g) ⊆ ZFMISC_1.product Y Z :=
  XBOOLE_1.th1
    (th51 (FUNCT_2.functionOf_isFunction hf)
      (FUNCT_2.functionOf_isFunction hg))
    (ZFMISC_1.th96 (FUNCT_2.functionOf_rng_sub hf)
      (FUNCT_2.functionOf_rng_sub hg))


/-- `FUNCT_3:65` (`Th65`) -/
theorem th65 {f g x y : TarskiSet.{u}}
    (h : TARSKI.pair x y ∈
      ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom g)) :
    BINOP_1.apply2 (productFunc f g) x y =
      TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g y) :=
  let ⟨hx, hy⟩ := (ZFMISC_1.th87).mp h
  def8 hx hy

/-- `FUNCT_3:67` (`Th67`) -/
theorem th67 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    RELAT_1.rng (productFunc f g) =
      ZFMISC_1.product (RELAT_1.rng f) (RELAT_1.rng g) := by
  apply eq_of_mem
  intro q
  constructor
  · intro hq
    obtain ⟨p, hpD, heq⟩ :=
      (FUNCT_1.def3 (productFunc_isFunction f g).2).mp hq
    have hp : p ∈ ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom g) :=
      Eq.subst (motive := fun s => p ∈ s) (productFunc_dom f g) hpD
    obtain ⟨x, y, hx, hy, hpair⟩ :=
      (ZFMISC_1.def2 (RELAT_1.dom f) (RELAT_1.dom g) p).mp hp
    have hfR : FUNCT_1.apply f x ∈ RELAT_1.rng f :=
      (FUNCT_1.def3 hf.2).mpr ⟨x, hx, rfl⟩
    have hgR : FUNCT_1.apply g y ∈ RELAT_1.rng g :=
      (FUNCT_1.def3 hg.2).mpr ⟨y, hy, rfl⟩
    have heq' : q = TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g y) :=
      (heq.trans (congrArg (FUNCT_1.apply (productFunc f g)) hpair)).trans
        (def8 hx hy)
    exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product _ _) heq'.symm
      ((ZFMISC_1.th87).mpr ⟨hfR, hgR⟩)
  · intro hq
    obtain ⟨y1, y2, hy1, hy2, hpair⟩ :=
      (ZFMISC_1.def2 (RELAT_1.rng f) (RELAT_1.rng g) q).mp hq
    obtain ⟨x2, hx2, he2⟩ := (FUNCT_1.def3 hg.2).mp hy2
    obtain ⟨x1, hx1, he1⟩ := (FUNCT_1.def3 hf.2).mp hy1
    have hp : TARSKI.pair x1 x2 ∈
        ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom g) :=
      (ZFMISC_1.th87).mpr ⟨hx1, hx2⟩
    have hpD : TARSKI.pair x1 x2 ∈ RELAT_1.dom (productFunc f g) :=
      Eq.subst (motive := fun s => TARSKI.pair x1 x2 ∈ s)
        (productFunc_dom f g).symm hp
    have happ : BINOP_1.apply2 (productFunc f g) x1 x2 = q :=
      (def8 hx1 hx2).trans
        (Eq.trans
          (congrArg (fun a => TARSKI.pair a (FUNCT_1.apply g x2)) he1.symm)
          (Eq.trans (congrArg (TARSKI.pair y1) he2.symm) hpair.symm))
    exact (FUNCT_1.def3 (productFunc_isFunction f g).2).mpr
      ⟨TARSKI.pair x1 x2, hpD, happ.symm⟩

/-- `FUNCT_3:66` (`Th66`) -/
theorem th66 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    productFunc f g =
      complex (RELAT_1.comp (pr1 (RELAT_1.dom f) (RELAT_1.dom g)) f)
        (RELAT_1.comp (pr2 (RELAT_1.dom f) (RELAT_1.dom g)) g) := by
  let Df := RELAT_1.dom f
  let Dg := RELAT_1.dom g
  let D := ZFMISC_1.product Df Dg
  have hdPr1 := pr1_dom Df Dg
  have hdPr2 := pr2_dom Df Dg
  have hdF : RELAT_1.dom (RELAT_1.comp (pr1 Df Dg) f) = D := by
    have hr : RELAT_1.rng (pr1 Df Dg) ⊆ Df := th43
    exact (RELAT_1.th27 hr).trans hdPr1
  have hdG : RELAT_1.dom (RELAT_1.comp (pr2 Df Dg) g) = D := by
    have hr : RELAT_1.rng (pr2 Df Dg) ⊆ Dg := th45
    exact (RELAT_1.th27 hr).trans hdPr2
  have hdC : RELAT_1.dom
      (complex (RELAT_1.comp (pr1 Df Dg) f)
        (RELAT_1.comp (pr2 Df Dg) g)) = D :=
    th50 hdF hdG
  have hdP : RELAT_1.dom (productFunc f g) = D := productFunc_dom f g
  refine FUNCT_1.th2 (productFunc_isFunction f g)
    (complex_isFunction _ _) (hdP.trans hdC.symm) ?_
  intro p hp
  have hpD : p ∈ D := Eq.subst (motive := fun s => p ∈ s) hdP hp
  obtain ⟨x, y, hx, hy, hpair⟩ := (ZFMISC_1.def2 Df Dg p).mp hpD
  have hxI : p ∈ RELAT_1.dom
      (complex (RELAT_1.comp (pr1 Df Dg) f)
        (RELAT_1.comp (pr2 Df Dg) g)) :=
    Eq.subst (motive := fun s => p ∈ s) hdC.symm hpD
  have hf' : FUNCT_1.apply (RELAT_1.comp (pr1 Df Dg) f) p =
      FUNCT_1.apply f x := by
    have hpPr : p ∈ RELAT_1.dom (pr1 Df Dg) :=
      Eq.subst (motive := fun s => p ∈ s) hdPr1.symm hpD
    have happ : FUNCT_1.apply (pr1 Df Dg) p = x :=
      (congrArg (FUNCT_1.apply (pr1 Df Dg)) hpair).trans (def4 hx hy)
    exact (FUNCT_1.th12 (pr1_isFunction Df Dg).2 hf.2
      ((FUNCT_1.th11 (pr1_isFunction Df Dg).2).mpr
        ⟨hpPr, Eq.subst (motive := fun s => s ∈ Df) happ.symm hx⟩)).trans
      (congrArg (FUNCT_1.apply f) happ)
  have hg' : FUNCT_1.apply (RELAT_1.comp (pr2 Df Dg) g) p =
      FUNCT_1.apply g y := by
    have hpPr : p ∈ RELAT_1.dom (pr2 Df Dg) :=
      Eq.subst (motive := fun s => p ∈ s) hdPr2.symm hpD
    have happ : FUNCT_1.apply (pr2 Df Dg) p = y :=
      (congrArg (FUNCT_1.apply (pr2 Df Dg)) hpair).trans (def5 hx hy)
    exact (FUNCT_1.th12 (pr2_isFunction Df Dg).2 hg.2
      ((FUNCT_1.th11 (pr2_isFunction Df Dg).2).mpr
        ⟨hpPr, Eq.subst (motive := fun s => s ∈ Dg) happ.symm hy⟩)).trans
      (congrArg (FUNCT_1.apply g) happ)
  exact ((congrArg (FUNCT_1.apply (productFunc f g)) hpair).trans
      (def8 hx hy)).trans
    ((Eq.trans
        (congrArg (fun a => TARSKI.pair a (FUNCT_1.apply g y)) hf'.symm)
        (congrArg
          (TARSKI.pair (FUNCT_1.apply (RELAT_1.comp (pr1 Df Dg) f) p))
          hg'.symm)).trans (def7 hxI).symm)

/-- `FUNCT_3:68` (`Th68`) -/
theorem th68 {f g X : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g)
    (hdF : RELAT_1.dom f = X) (hdG : RELAT_1.dom g = X) :
    complex f g = RELAT_1.comp (delta X) (productFunc f g) := by
  have hdDel := delta_dom X
  have hrDel : RELAT_1.rng (delta X) ⊆ ZFMISC_1.product X X := th47
  have hdP : RELAT_1.dom (productFunc f g) = ZFMISC_1.product X X :=
    Eq.trans (productFunc_dom f g)
      (Eq.trans (congrArg (fun s => ZFMISC_1.product s (RELAT_1.dom g)) hdF)
        (congrArg (ZFMISC_1.product X) hdG))
  have hrSub : RELAT_1.rng (delta X) ⊆ RELAT_1.dom (productFunc f g) :=
    Eq.subst (motive := fun s => RELAT_1.rng (delta X) ⊆ s) hdP.symm hrDel
  have hdComp : RELAT_1.dom (RELAT_1.comp (delta X) (productFunc f g)) = X :=
    (RELAT_1.th27 hrSub).trans hdDel
  have hdC : RELAT_1.dom (complex f g) = X := th50 hdF hdG
  refine FUNCT_1.th2 (complex_isFunction f g)
    (FUNCT_1.comp_isFunction (delta_isFunction X) (productFunc_isFunction f g))
    (hdC.trans hdComp.symm) ?_
  intro x hx
  have hxX : x ∈ X := Eq.subst (motive := fun s => x ∈ s) hdC hx
  exact (def7 hx).trans
    ((def8 (Eq.subst (motive := fun s => x ∈ s) hdF.symm hxX)
        (Eq.subst (motive := fun s => x ∈ s) hdG.symm hxX)).symm.trans
      ((congrArg (FUNCT_1.apply (productFunc f g)) (def6 hxX).symm).trans
        (FUNCT_1.th12 (delta_isFunction X).2
          (productFunc_isFunction f g).2
          (Eq.subst (motive := fun s => x ∈ s) hdComp.symm hxX)).symm))

/-- `FUNCT_3:58` (`Th58`) -/
theorem th58 {f g X Y Z : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f X Y) (hg : FUNCT_2.isFunctionOf g X Z)
    (hY : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (hZ : Z = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    FUNCT_2.isFunctionOf (complex f g) X (ZFMISC_1.product Y Z) := by
  have := Classical.propDecidable
    (ZFMISC_1.product Y Z = (∅ : TarskiSet.{u}))
  by_cases hYZ : ZFMISC_1.product Y Z = (∅ : TarskiSet.{u})
  · have := Classical.propDecidable (X = (∅ : TarskiSet.{u}))
    by_cases hX : X = (∅ : TarskiSet.{u})
    · have hdF := FUNCT_2.functionOf_dom_eq' hf hY
      have hdG := FUNCT_2.functionOf_dom_eq' hg hZ
      have hdC : RELAT_1.dom (complex f g) = (∅ : TarskiSet.{u}) :=
        (th50 hdF hdG).trans hX
      have hrngE : RELAT_1.rng (complex f g) = (∅ : TarskiSet.{u}) :=
        (RELAT_1.th42 (complex_isFunction f g).1).mp hdC
      exact FUNCT_2.functionOf_of (complex_isFunction f g)
        (th50 hdF hdG)
        (Eq.subst (motive := fun s => s ⊆ ZFMISC_1.product Y Z) hrngE.symm
          (Eq.subst (motive := fun t => (∅ : TarskiSet.{u}) ⊆ t) hYZ.symm
            XBOOLE_1.th2))
    · exact False.elim
        (Or.elim ((ZFMISC_1.th90 (X := Y) (Y := Z)).mp hYZ)
          (fun hY0 => hX (hY hY0)) (fun hZ0 => hX (hZ hZ0)))
  · have hYne : Y ≠ (∅ : TarskiSet.{u}) := fun h =>
      hYZ ((ZFMISC_1.th90).mpr (Or.inl h))
    have hZne : Z ≠ (∅ : TarskiSet.{u}) := fun h =>
      hYZ ((ZFMISC_1.th90).mpr (Or.inr h))
    have hdF := FUNCT_2.functionOf_dom_eq hf hYne
    have hdG := FUNCT_2.functionOf_dom_eq hg hZne
    have hr := XBOOLE_1.th1
      (th51 (FUNCT_2.functionOf_isFunction hf)
        (FUNCT_2.functionOf_isFunction hg))
      (ZFMISC_1.th96 (FUNCT_2.functionOf_rng_sub hf)
        (FUNCT_2.functionOf_rng_sub hg))
    exact FUNCT_2.functionOf_of (complex_isFunction f g) (th50 hdF hdG) hr

/-- `FUNCT_3:61` (`Th61`) -/
theorem th61 {f g X Y Z : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f X Y) (hg : FUNCT_2.isFunctionOf g X Z)
    (hY : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (hZ : Z = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    RELAT_1.comp (complex f g) (pr1 Y Z) = f ∧
    RELAT_1.comp (complex f g) (pr2 Y Z) = g := by
  have hdF := FUNCT_2.functionOf_dom_eq' hf hY
  have hdG := FUNCT_2.functionOf_dom_eq' hg hZ
  exact th52 (FUNCT_2.functionOf_isFunction hf)
    (FUNCT_2.functionOf_isFunction hg) (hdF.trans hdG.symm)
    (FUNCT_2.functionOf_rng_sub hf) (FUNCT_2.functionOf_rng_sub hg)

/-- Unlabeled `FUNCT_3` (`Th62`) -/
theorem th62 {f g X D1 D2 : TarskiSet.{u}}
    (hD1 : D1 ≠ (∅ : TarskiSet.{u})) (hD2 : D2 ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X D1)
    (hg : FUNCT_2.isFunctionOf g X D2) :
    RELAT_1.comp (complex f g) (pr1 D1 D2) = f ∧
    RELAT_1.comp (complex f g) (pr2 D1 D2) = g :=
  th61 hf hg (fun h => (hD1 h).elim) (fun h => (hD2 h).elim)

/-- Unlabeled `FUNCT_3` (`Th63`) -/
theorem th63 {f1 f2 g1 g2 X Y Z : TarskiSet.{u}}
    (hf1 : FUNCT_2.isFunctionOf f1 X Y) (hf2 : FUNCT_2.isFunctionOf f2 X Y)
    (hg1 : FUNCT_2.isFunctionOf g1 X Z) (hg2 : FUNCT_2.isFunctionOf g2 X Z)
    (hY : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (hZ : Z = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u}))
    (heq : complex f1 g1 = complex f2 g2) :
    f1 = f2 ∧ g1 = g2 := by
  have hdF1 := FUNCT_2.functionOf_dom_eq' hf1 hY
  have hdF2 := FUNCT_2.functionOf_dom_eq' hf2 hY
  have hdG1 := FUNCT_2.functionOf_dom_eq' hg1 hZ
  have hdG2 := FUNCT_2.functionOf_dom_eq' hg2 hZ
  exact th54 (FUNCT_2.functionOf_isFunction hf1)
    (FUNCT_2.functionOf_isFunction hg1)
    (FUNCT_2.functionOf_isFunction hg2)
    (FUNCT_2.functionOf_isFunction hf2)
    (hdF1.trans hdG1.symm) (hdF2.trans hdG2.symm) heq

/-- Unlabeled `FUNCT_3` (`Th64`) -/
theorem th64 {f1 f2 g1 g2 X D1 D2 : TarskiSet.{u}}
    (hD1 : D1 ≠ (∅ : TarskiSet.{u})) (hD2 : D2 ≠ (∅ : TarskiSet.{u}))
    (hf1 : FUNCT_2.isFunctionOf f1 X D1)
    (hf2 : FUNCT_2.isFunctionOf f2 X D1)
    (hg1 : FUNCT_2.isFunctionOf g1 X D2)
    (hg2 : FUNCT_2.isFunctionOf g2 X D2)
    (heq : complex f1 g1 = complex f2 g2) :
    f1 = f2 ∧ g1 = g2 :=
  th63 hf1 hf2 hg1 hg2 (fun h => (hD1 h).elim) (fun h => (hD2 h).elim) heq


/-- Unlabeled `FUNCT_3` (`Th69`) — `[:id X, id Y:] = id [:X,Y:]`. -/
theorem th69 (X Y : TarskiSet.{u}) :
    productFunc (RELAT_1.id X) (RELAT_1.id Y) =
      RELAT_1.id (ZFMISC_1.product X Y) := by
  have h1 : RELAT_1.comp (pr1 X Y) (RELAT_1.id X) = pr1 X Y :=
    RELAT_1.th53 (pr1_isFunction X Y).1 th43
  have h2 : RELAT_1.comp (pr2 X Y) (RELAT_1.id Y) = pr2 X Y :=
    RELAT_1.th53 (pr2_isFunction X Y).1 th45
  have hdX : RELAT_1.dom (RELAT_1.id X) = X := RELAT_1.id_dom X
  have hdY : RELAT_1.dom (RELAT_1.id Y) = Y := RELAT_1.id_dom Y
  have h := th66 (FUNCT_1.id_isFunction X) (FUNCT_1.id_isFunction Y)
  exact (Eq.trans h
    (Eq.trans
      (congrArg (fun s =>
          complex s (RELAT_1.comp (pr2 (RELAT_1.dom (RELAT_1.id X))
            (RELAT_1.dom (RELAT_1.id Y))) (RELAT_1.id Y)))
        (Eq.trans
          (congrArg (fun s => RELAT_1.comp (pr1 s
              (RELAT_1.dom (RELAT_1.id Y))) (RELAT_1.id X)) hdX)
          (Eq.trans (congrArg (fun t => RELAT_1.comp (pr1 X t) (RELAT_1.id X))
            hdY) h1)))
      (congrArg (complex (pr1 X Y))
        (Eq.trans
          (congrArg (fun s => RELAT_1.comp (pr2 s
              (RELAT_1.dom (RELAT_1.id Y))) (RELAT_1.id Y)) hdX)
          (Eq.trans (congrArg (fun t => RELAT_1.comp (pr2 X t) (RELAT_1.id Y))
            hdY) h2))))).trans th53

/-- Unlabeled `FUNCT_3` (`Th70`) — `[:f,h:]*<:g,k:> = <:f*g,h*k:>`. -/
theorem th70 {f g h k : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (hk : FUNCT_1.isFunction k) :
    RELAT_1.comp (complex g k) (productFunc f h) =
      complex (RELAT_1.comp g f) (RELAT_1.comp k h) := by
  have hdom : ∀ x,
      x ∈ RELAT_1.dom (RELAT_1.comp (complex g k) (productFunc f h)) ↔
      x ∈ RELAT_1.dom (complex (RELAT_1.comp g f) (RELAT_1.comp k h)) := by
    intro x
    constructor
    · intro hx
      have ⟨hxC, hApp⟩ := (FUNCT_1.th11 (complex_isFunction g k).2).mp hx
      have hxI : x ∈ RELAT_1.dom g ∩ RELAT_1.dom k :=
        Eq.subst (motive := fun s => x ∈ s) (complex_dom g k) hxC
      have ⟨hxG, hxK⟩ := (XBOOLE_0.def4 _ _ _).mp hxI
      have heq : FUNCT_1.apply (complex g k) x =
          TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k x) := def7 hxC
      have hp : TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k x) ∈
          RELAT_1.dom (productFunc f h) :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.dom (productFunc f h))
          heq hApp
      have hpD : TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k x) ∈
          ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom h) :=
        Eq.subst (motive := fun s =>
            TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k x) ∈ s)
          (productFunc_dom f h) hp
      have ⟨hgF, hkH⟩ := (ZFMISC_1.th87).mp hpD
      have hxFG : x ∈ RELAT_1.dom (RELAT_1.comp g f) :=
        (FUNCT_1.th11 hg.2).mpr ⟨hxG, hgF⟩
      have hxKH : x ∈ RELAT_1.dom (RELAT_1.comp k h) :=
        (FUNCT_1.th11 hk.2).mpr ⟨hxK, hkH⟩
      exact Eq.subst (motive := fun s => x ∈ s)
        (complex_dom (RELAT_1.comp g f) (RELAT_1.comp k h)).symm
        ((XBOOLE_0.def4 _ _ _).mpr ⟨hxFG, hxKH⟩)
    · intro hx
      have hxI : x ∈ RELAT_1.dom (RELAT_1.comp g f) ∩
          RELAT_1.dom (RELAT_1.comp k h) :=
        Eq.subst (motive := fun s => x ∈ s)
          (complex_dom (RELAT_1.comp g f) (RELAT_1.comp k h)) hx
      have ⟨hxFG, hxKH⟩ := (XBOOLE_0.def4 _ _ _).mp hxI
      have ⟨hxG, hgF⟩ := (FUNCT_1.th11 hg.2).mp hxFG
      have ⟨hxK, hkH⟩ := (FUNCT_1.th11 hk.2).mp hxKH
      have hxC : x ∈ RELAT_1.dom (complex g k) :=
        Eq.subst (motive := fun s => x ∈ s) (complex_dom g k).symm
          ((XBOOLE_0.def4 _ _ _).mpr ⟨hxG, hxK⟩)
      have hpD : TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k x) ∈
          ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom h) :=
        (ZFMISC_1.th87).mpr ⟨hgF, hkH⟩
      have hp : TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k x) ∈
          RELAT_1.dom (productFunc f h) :=
        Eq.subst (motive := fun s =>
            TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k x) ∈ s)
          (productFunc_dom f h).symm hpD
      have hApp : FUNCT_1.apply (complex g k) x ∈
          RELAT_1.dom (productFunc f h) :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.dom (productFunc f h))
          (def7 hxC).symm hp
      exact (FUNCT_1.th11 (complex_isFunction g k).2).mpr ⟨hxC, hApp⟩
  have hdEq := eq_of_mem hdom
  refine FUNCT_1.th2
    (FUNCT_1.comp_isFunction (complex_isFunction g k)
      (productFunc_isFunction f h))
    (complex_isFunction _ _) hdEq ?_
  intro x hx
  have ⟨hxC, hApp⟩ := (FUNCT_1.th11 (complex_isFunction g k).2).mp hx
  have hxI : x ∈ RELAT_1.dom g ∩ RELAT_1.dom k :=
    Eq.subst (motive := fun s => x ∈ s) (complex_dom g k) hxC
  have ⟨hxG, hxK⟩ := (XBOOLE_0.def4 _ _ _).mp hxI
  have heqC : FUNCT_1.apply (complex g k) x =
      TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k x) := def7 hxC
  have hp : TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k x) ∈
      RELAT_1.dom (productFunc f h) :=
    Eq.subst (motive := fun s => s ∈ RELAT_1.dom (productFunc f h))
      heqC hApp
  have hpD : TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k x) ∈
      ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom h) :=
    Eq.subst (motive := fun s =>
        TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k x) ∈ s)
      (productFunc_dom f h) hp
  have ⟨hgF, hkH⟩ := (ZFMISC_1.th87).mp hpD
  have hxFG : x ∈ RELAT_1.dom (RELAT_1.comp g f) :=
    (FUNCT_1.th11 hg.2).mpr ⟨hxG, hgF⟩
  have hxKH : x ∈ RELAT_1.dom (RELAT_1.comp k h) :=
    (FUNCT_1.th11 hk.2).mpr ⟨hxK, hkH⟩
  have hxCI : x ∈ RELAT_1.dom (RELAT_1.comp g f) ∩
      RELAT_1.dom (RELAT_1.comp k h) :=
    (XBOOLE_0.def4 _ _ _).mpr ⟨hxFG, hxKH⟩
  exact (FUNCT_1.th12 (complex_isFunction g k).2
      (productFunc_isFunction f h).2 hx).trans
    ((Eq.trans (congrArg (FUNCT_1.apply (productFunc f h)) heqC)
        (def8 hgF hkH)).trans
      ((Eq.trans
          (congrArg (fun a => TARSKI.pair a (FUNCT_1.apply h (FUNCT_1.apply k x)))
            (FUNCT_1.th13 hg.2 hf.2 hxG).symm)
          (congrArg (TARSKI.pair (FUNCT_1.apply (RELAT_1.comp g f) x))
            (FUNCT_1.th13 hk.2 hh.2 hxK).symm)).trans
        (th48 hxCI).symm))

/-- Unlabeled `FUNCT_3` (`Th71`) — `[:f,h:]*[:g,k:] = [:f*g,h*k:]`. -/
theorem th71 {f g h k : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (hk : FUNCT_1.isFunction k) :
    RELAT_1.comp (productFunc g k) (productFunc f h) =
      productFunc (RELAT_1.comp g f) (RELAT_1.comp k h) := by
  have hdGK := productFunc_dom g k
  have hdFH := productFunc_dom f h
  have hdLeft : RELAT_1.dom
      (RELAT_1.comp (productFunc g k) (productFunc f h)) =
      ZFMISC_1.product (RELAT_1.dom (RELAT_1.comp g f))
        (RELAT_1.dom (RELAT_1.comp k h)) := by
    apply eq_of_mem; intro p; constructor
    · intro hp
      have ⟨hpGK, hApp⟩ := (FUNCT_1.th11 (productFunc_isFunction g k).2).mp hp
      have hpD : p ∈ ZFMISC_1.product (RELAT_1.dom g) (RELAT_1.dom k) :=
        Eq.subst (motive := fun s => p ∈ s) hdGK hpGK
      obtain ⟨x1, x2, hx1, hx2, hpair⟩ := (ZFMISC_1.def2 _ _ p).mp hpD
      have happ : FUNCT_1.apply (productFunc g k) p =
          TARSKI.pair (FUNCT_1.apply g x1) (FUNCT_1.apply k x2) :=
        (congrArg (FUNCT_1.apply (productFunc g k)) hpair).trans
          (def8 hx1 hx2)
      have hpFH : TARSKI.pair (FUNCT_1.apply g x1) (FUNCT_1.apply k x2) ∈
          RELAT_1.dom (productFunc f h) :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.dom (productFunc f h))
          happ hApp
      have hpFHD : TARSKI.pair (FUNCT_1.apply g x1) (FUNCT_1.apply k x2) ∈
          ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom h) :=
        Eq.subst (motive := fun s =>
            TARSKI.pair (FUNCT_1.apply g x1) (FUNCT_1.apply k x2) ∈ s)
          hdFH hpFH
      have ⟨hgF, hkH⟩ := (ZFMISC_1.th87).mp hpFHD
      have hxFG : x1 ∈ RELAT_1.dom (RELAT_1.comp g f) :=
        (FUNCT_1.th11 hg.2).mpr ⟨hx1, hgF⟩
      have hxKH : x2 ∈ RELAT_1.dom (RELAT_1.comp k h) :=
        (FUNCT_1.th11 hk.2).mpr ⟨hx2, hkH⟩
      exact Eq.subst (motive := fun s => s ∈
          ZFMISC_1.product (RELAT_1.dom (RELAT_1.comp g f))
            (RELAT_1.dom (RELAT_1.comp k h))) hpair.symm
        ((ZFMISC_1.th87).mpr ⟨hxFG, hxKH⟩)
    · intro hp
      obtain ⟨x1, x2, hxFG, hxKH, hpair⟩ := (ZFMISC_1.def2 _ _ p).mp hp
      have ⟨hx1, hgF⟩ := (FUNCT_1.th11 hg.2).mp hxFG
      have ⟨hx2, hkH⟩ := (FUNCT_1.th11 hk.2).mp hxKH
      have hpGK : TARSKI.pair x1 x2 ∈ RELAT_1.dom (productFunc g k) :=
        Eq.subst (motive := fun s => TARSKI.pair x1 x2 ∈ s) hdGK.symm
          ((ZFMISC_1.th87).mpr ⟨hx1, hx2⟩)
      have hpFH : TARSKI.pair (FUNCT_1.apply g x1) (FUNCT_1.apply k x2) ∈
          RELAT_1.dom (productFunc f h) :=
        Eq.subst (motive := fun s =>
            TARSKI.pair (FUNCT_1.apply g x1) (FUNCT_1.apply k x2) ∈ s)
          hdFH.symm ((ZFMISC_1.th87).mpr ⟨hgF, hkH⟩)
      have happ : FUNCT_1.apply (productFunc g k) (TARSKI.pair x1 x2) ∈
          RELAT_1.dom (productFunc f h) :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.dom (productFunc f h))
          (def8 hx1 hx2).symm hpFH
      exact Eq.subst (motive := fun s => s ∈
          RELAT_1.dom (RELAT_1.comp (productFunc g k) (productFunc f h)))
        hpair.symm
        ((FUNCT_1.th11 (productFunc_isFunction g k).2).mpr ⟨hpGK, happ⟩)
  have hdRight := productFunc_dom (RELAT_1.comp g f) (RELAT_1.comp k h)
  refine FUNCT_1.th2
    (FUNCT_1.comp_isFunction (productFunc_isFunction g k)
      (productFunc_isFunction f h))
    (productFunc_isFunction _ _) (hdLeft.trans hdRight.symm) ?_
  intro p hp
  have ⟨hpGK, hApp⟩ := (FUNCT_1.th11 (productFunc_isFunction g k).2).mp hp
  have hpD : p ∈ ZFMISC_1.product (RELAT_1.dom g) (RELAT_1.dom k) :=
    Eq.subst (motive := fun s => p ∈ s) hdGK hpGK
  obtain ⟨x, y, hx, hy, hpair⟩ := (ZFMISC_1.def2 _ _ p).mp hpD
  have happGK : FUNCT_1.apply (productFunc g k) p =
      TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k y) :=
    (congrArg (FUNCT_1.apply (productFunc g k)) hpair).trans (def8 hx hy)
  have hpFH : TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k y) ∈
      ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom h) :=
    Eq.subst (motive := fun s =>
        TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply k y) ∈ s) hdFH
      (Eq.subst (motive := fun s => s ∈ RELAT_1.dom (productFunc f h))
        happGK hApp)
  have hgF : FUNCT_1.apply g x ∈ RELAT_1.dom f := ((ZFMISC_1.th87).mp hpFH).1
  have hkH : FUNCT_1.apply k y ∈ RELAT_1.dom h := ((ZFMISC_1.th87).mp hpFH).2
  have hxFG : x ∈ RELAT_1.dom (RELAT_1.comp g f) :=
    (FUNCT_1.th11 hg.2).mpr ⟨hx, hgF⟩
  have hxKH : y ∈ RELAT_1.dom (RELAT_1.comp k h) :=
    (FUNCT_1.th11 hk.2).mpr ⟨hy, hkH⟩
  exact (FUNCT_1.th12 (productFunc_isFunction g k).2
      (productFunc_isFunction f h).2 hp).trans
    ((Eq.trans
        (congrArg (FUNCT_1.apply (productFunc f h)) happGK)
        (def8 hgF hkH)).trans
      ((Eq.trans
          (congrArg (fun a => TARSKI.pair a (FUNCT_1.apply h (FUNCT_1.apply k y)))
            (FUNCT_1.th12 hg.2 hf.2 hxFG).symm)
          (congrArg (TARSKI.pair (FUNCT_1.apply (RELAT_1.comp g f) x))
            (FUNCT_1.th12 hk.2 hh.2 hxKH).symm)).trans
        ((congrArg
            (FUNCT_1.apply (productFunc (RELAT_1.comp g f) (RELAT_1.comp k h)))
            hpair).trans (def8 hxFG hxKH)).symm))


/-- Unlabeled `FUNCT_3` (`Th72`) -/
theorem th72 {f g B A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    RELAT_1.image (productFunc f g) (ZFMISC_1.product B A) =
      ZFMISC_1.product (RELAT_1.image f B) (RELAT_1.image g A) := by
  apply eq_of_mem
  intro q
  constructor
  · intro hq
    obtain ⟨p, hpD, hpBA, heq⟩ :=
      (FUNCT_1.def6 (productFunc_isFunction f g).2).mp hq
    have hp : p ∈ ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom g) :=
      Eq.subst (motive := fun s => p ∈ s) (productFunc_dom f g) hpD
    obtain ⟨x, y, hx, hy, hpair⟩ := (ZFMISC_1.def2 _ _ p).mp hp
    have ⟨hxB, hyA⟩ := (ZFMISC_1.th87).mp
      (Eq.subst (motive := fun s => s ∈ ZFMISC_1.product B A) hpair hpBA)
    have hfB : FUNCT_1.apply f x ∈ RELAT_1.image f B :=
      (FUNCT_1.def6 hf.2).mpr ⟨x, hx, hxB, rfl⟩
    have hgA : FUNCT_1.apply g y ∈ RELAT_1.image g A :=
      (FUNCT_1.def6 hg.2).mpr ⟨y, hy, hyA, rfl⟩
    have heq' : q = TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g y) :=
      (heq.trans (congrArg (FUNCT_1.apply (productFunc f g)) hpair)).trans
        (def8 hx hy)
    exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product _ _) heq'.symm
      ((ZFMISC_1.th87).mpr ⟨hfB, hgA⟩)
  · intro hq
    obtain ⟨y1, y2, hy1, hy2, hpair⟩ := (ZFMISC_1.def2 _ _ q).mp hq
    obtain ⟨x, hxD, hxB, he1⟩ := (FUNCT_1.def6 hf.2).mp hy1
    obtain ⟨z, hzD, hzA, he2⟩ := (FUNCT_1.def6 hg.2).mp hy2
    have hp : TARSKI.pair x z ∈
        ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom g) :=
      (ZFMISC_1.th87).mpr ⟨hxD, hzD⟩
    have hpD : TARSKI.pair x z ∈ RELAT_1.dom (productFunc f g) :=
      Eq.subst (motive := fun s => TARSKI.pair x z ∈ s)
        (productFunc_dom f g).symm hp
    have hpBA : TARSKI.pair x z ∈ ZFMISC_1.product B A :=
      (ZFMISC_1.th87).mpr ⟨hxB, hzA⟩
    have happ : FUNCT_1.apply (productFunc f g) (TARSKI.pair x z) = q :=
      (def8 hxD hzD).trans
        (Eq.trans (congrArg (fun a => TARSKI.pair a (FUNCT_1.apply g z)) he1.symm)
          (Eq.trans (congrArg (TARSKI.pair y1) he2.symm) hpair.symm))
    exact (FUNCT_1.def6 (productFunc_isFunction f g).2).mpr
      ⟨TARSKI.pair x z, hpD, hpBA, happ.symm⟩

/-- Unlabeled `FUNCT_3` (`Th73`) -/
theorem th73 {f g B A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    RELAT_1.invimage (productFunc f g) (ZFMISC_1.product B A) =
      ZFMISC_1.product (RELAT_1.invimage f B) (RELAT_1.invimage g A) := by
  apply eq_of_mem
  intro q
  constructor
  · intro hq
    have ⟨hqD, happ⟩ := (FUNCT_1.def7 (productFunc_isFunction f g).2).mp hq
    have hqP : q ∈ ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom g) :=
      Eq.subst (motive := fun s => q ∈ s) (productFunc_dom f g) hqD
    obtain ⟨x1, x2, hx1, hx2, hpair⟩ := (ZFMISC_1.def2 _ _ q).mp hqP
    have heq : FUNCT_1.apply (productFunc f g) q =
        TARSKI.pair (FUNCT_1.apply f x1) (FUNCT_1.apply g x2) :=
      (congrArg (FUNCT_1.apply (productFunc f g)) hpair).trans (def8 hx1 hx2)
    have hp : TARSKI.pair (FUNCT_1.apply f x1) (FUNCT_1.apply g x2) ∈
        ZFMISC_1.product B A :=
      Eq.subst (motive := fun s => s ∈ ZFMISC_1.product B A) heq happ
    have ⟨hfB, hgA⟩ := (ZFMISC_1.th87).mp hp
    have hx1B : x1 ∈ RELAT_1.invimage f B :=
      (FUNCT_1.def7 hf.2).mpr ⟨hx1, hfB⟩
    have hx2A : x2 ∈ RELAT_1.invimage g A :=
      (FUNCT_1.def7 hg.2).mpr ⟨hx2, hgA⟩
    exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product _ _) hpair.symm
      ((ZFMISC_1.th87).mpr ⟨hx1B, hx2A⟩)
  · intro hq
    obtain ⟨x1, x2, hx1, hx2, hpair⟩ := (ZFMISC_1.def2 _ _ q).mp hq
    have ⟨hdF, hfB⟩ := (FUNCT_1.def7 hf.2).mp hx1
    have ⟨hdG, hgA⟩ := (FUNCT_1.def7 hg.2).mp hx2
    have hp : TARSKI.pair x1 x2 ∈
        ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom g) :=
      (ZFMISC_1.th87).mpr ⟨hdF, hdG⟩
    have hqD : TARSKI.pair x1 x2 ∈ RELAT_1.dom (productFunc f g) :=
      Eq.subst (motive := fun s => TARSKI.pair x1 x2 ∈ s)
        (productFunc_dom f g).symm hp
    have happ : FUNCT_1.apply (productFunc f g) (TARSKI.pair x1 x2) ∈
        ZFMISC_1.product B A :=
      Eq.subst (motive := fun s => s ∈ ZFMISC_1.product B A)
        (def8 hdF hdG).symm ((ZFMISC_1.th87).mpr ⟨hfB, hgA⟩)
    exact Eq.subst (motive := fun s =>
        s ∈ RELAT_1.invimage (productFunc f g) (ZFMISC_1.product B A))
      hpair.symm
      ((FUNCT_1.def7 (productFunc_isFunction f g).2).mpr ⟨hqD, happ⟩)

/-- `FUNCT_3:74` (`Th74`) — full Function-of for product, incl. empty/quasi-total. -/
theorem th74 {f g X V Y Z : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f X Y) (hg : FUNCT_2.isFunctionOf g V Z) :
    FUNCT_2.isFunctionOf (productFunc f g)
      (ZFMISC_1.product X V) (ZFMISC_1.product Y Z) := by
  have := Classical.propDecidable
    (ZFMISC_1.product Y Z = (∅ : TarskiSet.{u}))
  by_cases hYZ : ZFMISC_1.product Y Z = (∅ : TarskiSet.{u})
  · have := Classical.propDecidable
      (ZFMISC_1.product X V = (∅ : TarskiSet.{u}))
    by_cases hXV : ZFMISC_1.product X V = (∅ : TarskiSet.{u})
    · -- both products empty: dom matches, rng ⊆
      have hdomF : RELAT_1.dom f = (∅ : TarskiSet.{u}) ∨
          RELAT_1.dom g = (∅ : TarskiSet.{u}) := by
        exact Or.elim ((ZFMISC_1.th90 (X := X) (Y := V)).mp hXV)
          (fun hX => Or.inl ((XBOOLE_0.def10).mpr
            ⟨Eq.subst (motive := fun s => RELAT_1.dom f ⊆ s) hX
              (FUNCT_2.functionOf_dom_sub hf), XBOOLE_1.th2⟩))
          (fun hV => Or.inr ((XBOOLE_0.def10).mpr
            ⟨Eq.subst (motive := fun s => RELAT_1.dom g ⊆ s) hV
              (FUNCT_2.functionOf_dom_sub hg), XBOOLE_1.th2⟩))
      have hprodDom : ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom g) =
          (∅ : TarskiSet.{u}) :=
        (ZFMISC_1.th90).mpr hdomF
      have hd : RELAT_1.dom (productFunc f g) = ZFMISC_1.product X V :=
        (productFunc_dom f g).trans (hprodDom.trans hXV.symm)
      have hr : RELAT_1.rng (productFunc f g) ⊆ ZFMISC_1.product Y Z :=
        Eq.subst (motive := fun s => s ⊆ ZFMISC_1.product Y Z)
          (th67 (FUNCT_2.functionOf_isFunction hf)
            (FUNCT_2.functionOf_isFunction hg)).symm
          (ZFMISC_1.th96 (FUNCT_2.functionOf_rng_sub hf)
            (FUNCT_2.functionOf_rng_sub hg))
      exact FUNCT_2.functionOf_of (productFunc_isFunction f g) hd hr
    · -- Y×Z empty, X×V nonempty: productFunc empty, quasi-total
      have hYZ' : Y = (∅ : TarskiSet.{u}) ∨ Z = (∅ : TarskiSet.{u}) :=
        (ZFMISC_1.th90 (X := Y) (Y := Z)).mp hYZ
      have hfOrG : f = (∅ : TarskiSet.{u}) ∨ g = (∅ : TarskiSet.{u}) :=
        Or.elim hYZ'
          (fun hY => Or.inl (FUNCT_2.functionOf_empty_cod hf hY))
          (fun hZ => Or.inr (FUNCT_2.functionOf_empty_cod hg hZ))
      have hdomE : RELAT_1.dom f = (∅ : TarskiSet.{u}) ∨
          RELAT_1.dom g = (∅ : TarskiSet.{u}) :=
        Or.elim hfOrG
          (fun hfE => Or.inl (Eq.subst
            (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u}))
            hfE.symm RELAT_1.th38.1))
          (fun hgE => Or.inr (Eq.subst
            (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u}))
            hgE.symm RELAT_1.th38.1))
      have hprodDom : ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.dom g) =
          (∅ : TarskiSet.{u}) :=
        (ZFMISC_1.th90).mpr hdomE
      have hd : RELAT_1.dom (productFunc f g) = (∅ : TarskiSet.{u}) :=
        (productFunc_dom f g).trans hprodDom
      have hempty : productFunc f g = (∅ : TarskiSet.{u}) :=
        RELAT_1.th41 (productFunc_isFunction f g).1 (Or.inl hd)
      have hrngE : RELAT_1.rng (productFunc f g) = (∅ : TarskiSet.{u}) :=
        Eq.subst (motive := fun s => RELAT_1.rng s = (∅ : TarskiSet.{u}))
          hempty.symm RELAT_1.th38.2
      have hRel : RELSET_1.isRelationOf (productFunc f g)
          (ZFMISC_1.product X V) (ZFMISC_1.product Y Z) :=
        RELSET_1.th4 (productFunc_isFunction f g).1
          (Eq.subst (motive := fun s => s ⊆ ZFMISC_1.product X V) hd.symm
            XBOOLE_1.th2)
          (Eq.subst (motive := fun s => s ⊆ ZFMISC_1.product Y Z) hrngE.symm
            (Eq.subst (motive := fun t => (∅ : TarskiSet.{u}) ⊆ t) hYZ.symm
              XBOOLE_1.th2))
      refine ⟨⟨productFunc_isFunction f g, hRel⟩, ?_⟩
      exact ⟨fun hne => (hne hYZ).elim,
        fun _ => hempty⟩
  · -- Y×Z nonempty
    have hYne : Y ≠ (∅ : TarskiSet.{u}) := fun h =>
      hYZ ((ZFMISC_1.th90).mpr (Or.inl h))
    have hZne : Z ≠ (∅ : TarskiSet.{u}) := fun h =>
      hYZ ((ZFMISC_1.th90).mpr (Or.inr h))
    have hdF := FUNCT_2.functionOf_dom_eq hf hYne
    have hdG := FUNCT_2.functionOf_dom_eq hg hZne
    have hr : RELAT_1.rng (productFunc f g) ⊆ ZFMISC_1.product Y Z :=
      Eq.subst (motive := fun s => s ⊆ ZFMISC_1.product Y Z)
        (th67 (FUNCT_2.functionOf_isFunction hf)
          (FUNCT_2.functionOf_isFunction hg)).symm
        (ZFMISC_1.th96 (FUNCT_2.functionOf_rng_sub hf)
          (FUNCT_2.functionOf_rng_sub hg))
    exact FUNCT_2.functionOf_of (productFunc_isFunction f g)
      (Eq.trans (productFunc_dom f g)
        (Eq.trans (congrArg (fun s => ZFMISC_1.product s (RELAT_1.dom g)) hdF)
          (congrArg (ZFMISC_1.product X) hdG)))
      hr

/-- Unlabeled `FUNCT_3` (`Th75`) -/
theorem th75 {f1 f2 C1 C2 D1 D2 c1 c2 : TarskiSet.{u}}
    (hC1 : C1 ≠ (∅ : TarskiSet.{u})) (hC2 : C2 ≠ (∅ : TarskiSet.{u}))
    (hD1 : D1 ≠ (∅ : TarskiSet.{u})) (hD2 : D2 ≠ (∅ : TarskiSet.{u}))
    (hf1 : FUNCT_2.isFunctionOf f1 C1 D1)
    (hf2 : FUNCT_2.isFunctionOf f2 C2 D2)
    (hc1 : SUBSET_1.isElement c1 C1)
    (hc2 : SUBSET_1.isElement c2 C2) :
    BINOP_1.apply2 (productFunc f1 f2) c1 c2 =
      TARSKI.pair (FUNCT_1.apply f1 c1) (FUNCT_1.apply f2 c2) := by
  have hd1 := FUNCT_2.functionOf_dom_eq hf1 hD1
  have hd2 := FUNCT_2.functionOf_dom_eq hf2 hD2
  have hc1' : c1 ∈ C1 := SUBSET_1.isElement_mem (ne_imp_not_empty hC1) hc1
  have hc2' : c2 ∈ C2 := SUBSET_1.isElement_mem (ne_imp_not_empty hC2) hc2
  exact def8 (Eq.subst (motive := fun s => c1 ∈ s) hd1.symm hc1')
    (Eq.subst (motive := fun s => c2 ∈ s) hd2.symm hc2')

/-- Unlabeled `FUNCT_3` (`Th76`) -/
theorem th76 {f1 f2 X1 X2 Y1 Y2 : TarskiSet.{u}}
    (hf1 : FUNCT_2.isFunctionOf f1 X1 Y1)
    (hf2 : FUNCT_2.isFunctionOf f2 X2 Y2)
    (hY1 : Y1 = (∅ : TarskiSet.{u}) → X1 = (∅ : TarskiSet.{u}))
    (hY2 : Y2 = (∅ : TarskiSet.{u}) → X2 = (∅ : TarskiSet.{u})) :
    productFunc f1 f2 =
      complex (RELAT_1.comp (pr1 X1 X2) f1)
        (RELAT_1.comp (pr2 X1 X2) f2) := by
  have hd1 := FUNCT_2.functionOf_dom_eq' hf1 hY1
  have hd2 := FUNCT_2.functionOf_dom_eq' hf2 hY2
  exact Eq.trans (th66 (FUNCT_2.functionOf_isFunction hf1)
      (FUNCT_2.functionOf_isFunction hf2))
    (Eq.trans
      (congrArg (fun s =>
          complex (RELAT_1.comp (pr1 s (RELAT_1.dom f2)) f1)
            (RELAT_1.comp (pr2 s (RELAT_1.dom f2)) f2)) hd1)
      (congrArg (fun t =>
          complex (RELAT_1.comp (pr1 X1 t) f1)
            (RELAT_1.comp (pr2 X1 t) f2)) hd2))

/-- Unlabeled `FUNCT_3` (`Th77`) -/
theorem th77 {f1 f2 X1 X2 D1 D2 : TarskiSet.{u}}
    (hD1 : D1 ≠ (∅ : TarskiSet.{u})) (hD2 : D2 ≠ (∅ : TarskiSet.{u}))
    (hf1 : FUNCT_2.isFunctionOf f1 X1 D1)
    (hf2 : FUNCT_2.isFunctionOf f2 X2 D2) :
    productFunc f1 f2 =
      complex (RELAT_1.comp (pr1 X1 X2) f1)
        (RELAT_1.comp (pr2 X1 X2) f2) :=
  th76 hf1 hf2 (fun h => (hD1 h).elim) (fun h => (hD2 h).elim)

/-- Unlabeled `FUNCT_3` (`Th78`) -/
theorem th78 {f1 f2 X Y1 Y2 : TarskiSet.{u}}
    (hf1 : FUNCT_2.isFunctionOf f1 X Y1)
    (hf2 : FUNCT_2.isFunctionOf f2 X Y2) :
    complex f1 f2 = RELAT_1.comp (delta X) (productFunc f1 f2) := by
  have := Classical.propDecidable (Y1 = (∅ : TarskiSet.{u}))
  by_cases hY1 : Y1 = (∅ : TarskiSet.{u})
  · have hfE : f1 = (∅ : TarskiSet.{u}) := FUNCT_2.functionOf_empty_cod hf1 hY1
    have hd1 : RELAT_1.dom f1 = (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u}))
        hfE.symm RELAT_1.th38.1
    have hC : complex f1 f2 = (∅ : TarskiSet.{u}) := complex_empty_left hfE
    have hdP : RELAT_1.dom (productFunc f1 f2) = (∅ : TarskiSet.{u}) :=
      (productFunc_dom f1 f2).trans
        ((ZFMISC_1.th90).mpr (Or.inl hd1))
    have hP : productFunc f1 f2 = (∅ : TarskiSet.{u}) :=
      RELAT_1.th41 (productFunc_isFunction f1 f2).1 (Or.inl hdP)
    exact hC.trans
      (((RELAT_1.th39 (R := delta X)).2).symm.trans
        (congrArg (RELAT_1.comp (delta X)) hP.symm))
  · have := Classical.propDecidable (Y2 = (∅ : TarskiSet.{u}))
    by_cases hY2 : Y2 = (∅ : TarskiSet.{u})
    · have hgE : f2 = (∅ : TarskiSet.{u}) :=
        FUNCT_2.functionOf_empty_cod hf2 hY2
      have hd2 : RELAT_1.dom f2 = (∅ : TarskiSet.{u}) :=
        Eq.subst (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u}))
          hgE.symm RELAT_1.th38.1
      have hC : complex f1 f2 = (∅ : TarskiSet.{u}) := complex_empty_right hgE
      have hdP : RELAT_1.dom (productFunc f1 f2) = (∅ : TarskiSet.{u}) :=
        (productFunc_dom f1 f2).trans
          ((ZFMISC_1.th90).mpr (Or.inr hd2))
      have hP : productFunc f1 f2 = (∅ : TarskiSet.{u}) :=
        RELAT_1.th41 (productFunc_isFunction f1 f2).1 (Or.inl hdP)
      exact hC.trans
        (((RELAT_1.th39 (R := delta X)).2).symm.trans
          (congrArg (RELAT_1.comp (delta X)) hP.symm))
    · have hd1 := FUNCT_2.functionOf_dom_eq hf1 hY1
      have hd2 := FUNCT_2.functionOf_dom_eq hf2 hY2
      exact th68 (FUNCT_2.functionOf_isFunction hf1)
        (FUNCT_2.functionOf_isFunction hf2) hd1 hd2


/-! ## Addenda (from AMI_1) -/

/-- Unlabeled `FUNCT_3` (`Th79`) — `pr1(dom f,rng f).:f = dom f`. -/
theorem th79 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    RELAT_1.image (pr1 (RELAT_1.dom f) (RELAT_1.rng f)) f =
      RELAT_1.dom f := by
  apply eq_of_mem
  intro y
  constructor
  · intro hy
    obtain ⟨x, hxD, hxF, heq⟩ :=
      (FUNCT_1.def6 (pr1_isFunction (RELAT_1.dom f) (RELAT_1.rng f)).2).mp hy
    have hxP : x ∈ ZFMISC_1.product (RELAT_1.dom f) (RELAT_1.rng f) :=
      Eq.subst (motive := fun s => x ∈ s)
        (pr1_dom (RELAT_1.dom f) (RELAT_1.rng f)) hxD
    obtain ⟨x1, x2, hx1, hx2, hpair⟩ := (ZFMISC_1.def2 _ _ x).mp hxP
    have heq' : y = BINOP_1.apply2 (pr1 (RELAT_1.dom f) (RELAT_1.rng f)) x1 x2 :=
      (heq.trans (congrArg (FUNCT_1.apply (pr1 (RELAT_1.dom f) (RELAT_1.rng f)))
        hpair)).trans rfl
    exact Eq.subst (motive := fun s => s ∈ RELAT_1.dom f)
      (heq'.trans (def4 hx1 hx2)).symm hx1
  · intro hy
    refine (FUNCT_1.def6 (pr1_isFunction (RELAT_1.dom f) (RELAT_1.rng f)).2).mpr ?_
    refine ⟨TARSKI.pair y (FUNCT_1.apply f y), ?_, ?_, ?_⟩
    · have hfy : FUNCT_1.apply f y ∈ RELAT_1.rng f :=
        (FUNCT_1.def3 hf.2).mpr ⟨y, hy, rfl⟩
      exact Eq.subst (motive := fun s => TARSKI.pair y (FUNCT_1.apply f y) ∈ s)
        (pr1_dom (RELAT_1.dom f) (RELAT_1.rng f)).symm
        ((ZFMISC_1.th87).mpr ⟨hy, hfy⟩)
    · exact (FUNCT_1.th1 hf.2).mpr ⟨hy, rfl⟩
    · have hfy : FUNCT_1.apply f y ∈ RELAT_1.rng f :=
        (FUNCT_1.def3 hf.2).mpr ⟨y, hy, rfl⟩
      exact (def4 hy hfy).symm

/-- Unlabeled `FUNCT_3` (`Th80`) — equality via matching projections. -/
theorem th80 {A B C f g : TarskiSet.{u}}
    (_hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hC : C ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f A (ZFMISC_1.product B C))
    (hg : FUNCT_2.isFunctionOf g A (ZFMISC_1.product B C))
    (h1 : RELAT_1.comp f (pr1 B C) = RELAT_1.comp g (pr1 B C))
    (h2 : RELAT_1.comp f (pr2 B C) = RELAT_1.comp g (pr2 B C)) :
    f = g := by
  have hPne : ZFMISC_1.product B C ≠ (∅ : TarskiSet.{u}) := fun hempty =>
    Or.elim ((ZFMISC_1.th90 (X := B) (Y := C)).mp hempty)
      (fun h => hB h) (fun h => hC h)
  have hdF := FUNCT_2.functionOf_dom_eq hf hPne
  have hdG := FUNCT_2.functionOf_dom_eq hg hPne
  refine FUNCT_2.th63 hf hg ?_
  intro a ha
  have hfA : FUNCT_1.apply f a ∈ ZFMISC_1.product B C :=
    FUNCT_2.th5 hf hPne ha
  have hgA : FUNCT_1.apply g a ∈ ZFMISC_1.product B C :=
    FUNCT_2.th5 hg hPne ha
  obtain ⟨b1, c1, hb1, hc1, hfEq⟩ :=
    (DOMAIN_1.th1 (a := FUNCT_1.apply f a) (X1 := B) (X2 := C) hB hC hfA)
  obtain ⟨b2, c2, hb2, hc2, hgEq⟩ :=
    (DOMAIN_1.th1 (a := FUNCT_1.apply g a) (X1 := B) (X2 := C) hB hC hgA)
  have hb1' : b1 ∈ B := SUBSET_1.isElement_mem (ne_imp_not_empty hB) hb1
  have hc1' : c1 ∈ C := SUBSET_1.isElement_mem (ne_imp_not_empty hC) hc1
  have hb2' : b2 ∈ B := SUBSET_1.isElement_mem (ne_imp_not_empty hB) hb2
  have hc2' : c2 ∈ C := SUBSET_1.isElement_mem (ne_imp_not_empty hC) hc2
  have hpr1f : FUNCT_1.apply (pr1 B C) (FUNCT_1.apply f a) = b1 :=
    (congrArg (FUNCT_1.apply (pr1 B C)) hfEq).trans (def4 hb1' hc1')
  have hpr1g : FUNCT_1.apply (pr1 B C) (FUNCT_1.apply g a) = b2 :=
    (congrArg (FUNCT_1.apply (pr1 B C)) hgEq).trans (def4 hb2' hc2')
  have hpr2f : FUNCT_1.apply (pr2 B C) (FUNCT_1.apply f a) = c1 :=
    (congrArg (FUNCT_1.apply (pr2 B C)) hfEq).trans (def5 hb1' hc1')
  have hpr2g : FUNCT_1.apply (pr2 B C) (FUNCT_1.apply g a) = c2 :=
    (congrArg (FUNCT_1.apply (pr2 B C)) hgEq).trans (def5 hb2' hc2')
  have heq1 : FUNCT_1.apply (RELAT_1.comp f (pr1 B C)) a =
      FUNCT_1.apply (RELAT_1.comp g (pr1 B C)) a :=
    congrArg (fun s => FUNCT_1.apply s a) h1
  have heq2 : FUNCT_1.apply (RELAT_1.comp f (pr2 B C)) a =
      FUNCT_1.apply (RELAT_1.comp g (pr2 B C)) a :=
    congrArg (fun s => FUNCT_1.apply s a) h2
  have hbEq : b1 = b2 :=
    (hpr1f.symm.trans
      ((FUNCT_2.th15 hf (pr1_isFunction B C) hPne ha).symm.trans
        (heq1.trans
          ((FUNCT_2.th15 hg (pr1_isFunction B C) hPne ha).trans hpr1g))))
  have hcEq : c1 = c2 :=
    (hpr2f.symm.trans
      ((FUNCT_2.th15 hf (pr2_isFunction B C) hPne ha).symm.trans
        (heq2.trans
          ((FUNCT_2.th15 hg (pr2_isFunction B C) hPne ha).trans hpr2g))))
  exact hfEq.trans
    (Eq.trans (congrArg (fun b => TARSKI.pair b c1) hbEq)
      (Eq.trans (congrArg (TARSKI.pair b2) hcEq) hgEq.symm))

/-- Registration: `[:F,G:]` one-to-one when both factors are. -/
theorem productFunc_oneToOne {F G : TarskiSet.{u}}
    (_hf : FUNCT_1.isFunction F) (_hg : FUNCT_1.isFunction G)
    (hF : FUNCT_1.isOneToOne F) (hG : FUNCT_1.isOneToOne G) :
    FUNCT_1.isOneToOne (productFunc F G) := by
  intro z1 z2 hz1 hz2 heq
  have hd := productFunc_dom F G
  have hz1D : z1 ∈ ZFMISC_1.product (RELAT_1.dom F) (RELAT_1.dom G) :=
    Eq.subst (motive := fun s => z1 ∈ s) hd hz1
  have hz2D : z2 ∈ ZFMISC_1.product (RELAT_1.dom F) (RELAT_1.dom G) :=
    Eq.subst (motive := fun s => z2 ∈ s) hd hz2
  obtain ⟨x1, y1, hx1, hy1, hp1⟩ := (ZFMISC_1.def2 _ _ z1).mp hz1D
  obtain ⟨x2, y2, hx2, hy2, hp2⟩ := (ZFMISC_1.def2 _ _ z2).mp hz2D
  have left : FUNCT_1.apply (productFunc F G) z1 =
      TARSKI.pair (FUNCT_1.apply F x1) (FUNCT_1.apply G y1) :=
    (congrArg (FUNCT_1.apply (productFunc F G)) hp1).trans (def8 hx1 hy1)
  have right : FUNCT_1.apply (productFunc F G) z2 =
      TARSKI.pair (FUNCT_1.apply F x2) (FUNCT_1.apply G y2) :=
    (congrArg (FUNCT_1.apply (productFunc F G)) hp2).trans (def8 hx2 hy2)
  have ⟨hFx, hGy⟩ := XTUPLE_0.th1 (left.symm.trans (heq.trans right))
  have hxeq : x1 = x2 := hF x1 x2 hx1 hx2 hFx
  have hyeq : y1 = y2 := hG y1 y2 hy1 hy2 hGy
  exact hp1.trans
    (Eq.trans (congrArg (fun a => TARSKI.pair a y1) hxeq)
      (Eq.trans (congrArg (TARSKI.pair x2) hyeq) hp2.symm))

/-- Idempotent `BinOp` witness: `pr1(A,A)`. -/
theorem exists_idempotent_binop (A : TarskiSet.{u}) :
    ∃ b, BINOP_1.isBinOp b A ∧ BINOP_1.isIdempotent b A := by
  refine ⟨pr1 A A, pr1_isFunctionOf A A, ?_⟩
  intro a ha
  have := Classical.propDecidable (A = (∅ : TarskiSet.{u}))
  by_cases hA : A = (∅ : TarskiSet.{u})
  · have haE : a = (∅ : TarskiSet.{u}) :=
      XBOOLE_0.empty_eq
        ((SUBSET_1.isElement_iff_empty (x := a) (X := A)
          (Eq.subst (motive := fun s => XBOOLE_0.isEmpty s) hA.symm
            XBOOLE_0.emptySet_isEmpty)).mp ha)
    have hnd : TARSKI.pair a a ∉ RELAT_1.dom (pr1 A A) := by
      intro hp
      have : TARSKI.pair a a ∈ ZFMISC_1.product A A :=
        Eq.subst (motive := fun s => TARSKI.pair a a ∈ s) (pr1_dom A A) hp
      exact (XBOOLE_0.empty_iff _).mp
        (Eq.subst (motive := fun s => TARSKI.pair a a ∈ s)
          ((ZFMISC_1.th90 (X := A) (Y := A)).mpr (Or.inl hA)) this)
    exact (show BINOP_1.apply2 (pr1 A A) a a = (∅ : TarskiSet.{u}) from
      FUNCT_1.apply_of_not_mem hnd).trans haE.symm
  · have ha' : a ∈ A := SUBSET_1.isElement_mem (ne_imp_not_empty hA) ha
    exact def4 ha' ha'

/-- Reduce: idempotent `b.(a,a) = a`. -/
theorem idempotent_reduce {A b a : TarskiSet.{u}}
    (_hb : BINOP_1.isBinOp b A) (hi : BINOP_1.isIdempotent b A)
    (ha : SUBSET_1.isElement a A) :
    BINOP_1.apply2 b a a = a :=
  hi a ha

end FUNCT_3
