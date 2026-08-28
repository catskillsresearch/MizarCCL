import MizarCCL.FUNCOP_1
import MizarCCL.ORDINAL1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/funct_4.miz`.
Authors: Czesław Byliński (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# The Modification of a Function by a Function

1–1 Lean rendering of Mizar article `FUNCT_4`
(`vendor/mml/funct_4.miz`). Import is `FUNCOP_1` and `ORDINAL1`
(last queue deps actually used). Mizar `g*f` is Lean `RELAT_1.comp f g`.
Mizar `f +* g` is Lean `override f g`. Mizar domain-swap `~f` is Lean
`swapDom f` (distinct from `FUNCOP_1.tilde`).
-/

universe u

open TarskiSet TARSKI

namespace FUNCT_4

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

private theorem ne_imp_not_empty {X : TarskiSet.{u}}
    (h : X ≠ (∅ : TarskiSet.{u})) : ¬ XBOOLE_0.isEmpty X :=
  fun he => h (XBOOLE_0.empty_eq he)

private theorem exists_mem_of_ne {X : TarskiSet.{u}}
    (h : X ≠ (∅ : TarskiSet.{u})) : ∃ x, x ∈ X :=
  XBOOLE_0.th7 h

private theorem congr_pair {a b c d : TarskiSet.{u}} (h1 : a = c) (h2 : b = d) :
    TARSKI.pair a b = TARSKI.pair c d :=
  (congrArg (fun s => TARSKI.pair s b) h1).trans (congrArg (TARSKI.pair c) h2)

private theorem congr_union {a b c d : TarskiSet.{u}} (h1 : a = c) (h2 : b = d) :
    a ∪ b = c ∪ d :=
  (congrArg (fun s => s ∪ b) h1).trans (congrArg (c ∪ ·) h2)

/-! ## Auxiliary: `Lm1` -/

/-- `FUNCT_4:lm 1` -/
theorem lm1 {x x9 y y9 x1 x19 y1 y19 : TarskiSet.{u}}
    (h : TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) =
      TARSKI.pair (TARSKI.pair x1 x19) (TARSKI.pair y1 y19)) :
    x = x1 ∧ y = y1 ∧ x9 = x19 ∧ y9 = y19 := by
  have ⟨hp1, hp2⟩ :=
    XTUPLE_0.th1 (x1 := TARSKI.pair x x9) (x2 := TARSKI.pair y y9)
      (y1 := TARSKI.pair x1 x19) (y2 := TARSKI.pair y1 y19) h
  have ⟨hx, hx9⟩ := XTUPLE_0.th1 (x1 := x) (x2 := x9) (y1 := x1) (y2 := x19) hp1
  have ⟨hy, hy9⟩ := XTUPLE_0.th1 (x1 := y) (x2 := y9) (y1 := y1) (y2 := y19) hp2
  exact ⟨hx, hy, hx9, hy9⟩

/-- `FUNCT_4:1` (`Th1`) -/
theorem th1 {Z : TarskiSet.{u}}
    (h : ∀ z, z ∈ Z → ∃ x y, z = TARSKI.pair x y) :
    ∃ X Y, Z ⊆ ZFMISC_1.product X Y := by
  obtain ⟨X, hX⟩ := XBOOLE_0.sch_separation (TARSKI.union (TARSKI.union Z))
    (fun x => ∃ y, TARSKI.pair x y ∈ Z)
  obtain ⟨Y, hY⟩ := XBOOLE_0.sch_separation (TARSKI.union (TARSKI.union Z))
    (fun y => ∃ x, TARSKI.pair x y ∈ Z)
  refine ⟨X, Y, fun z hz => ?_⟩
  obtain ⟨x, y, heq⟩ := h z hz
  have hz' : TARSKI.pair x y ∈ Z :=
    Eq.subst (motive := fun s => s ∈ Z) heq hz
  have hxU : x ∈ TARSKI.union (TARSKI.union Z) := (ZFMISC_1.th134 hz').1
  have hyU : y ∈ TARSKI.union (TARSKI.union Z) := (ZFMISC_1.th134 hz').2
  have hxX : x ∈ X := (hX x).mpr ⟨hxU, y, hz'⟩
  have hyY : y ∈ Y := (hY y).mpr ⟨hyU, x, hz'⟩
  exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product X Y) heq.symm
    ((ZFMISC_1.th87).mpr ⟨hxX, hyY⟩)

/-- `FUNCT_4:2` — `g*f = (g|rng f)*f`. -/
theorem th2 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    RELAT_1.comp f g =
      RELAT_1.comp f (RELAT_1.restrict g (RELAT_1.rng f)) := by
  have hrest :
      RELAT_1.dom (RELAT_1.restrict g (RELAT_1.rng f)) =
        RELAT_1.dom g ∩ RELAT_1.rng f := RELAT_1.th61
  have hdom : ∀ x, x ∈ RELAT_1.dom (RELAT_1.comp f g) ↔
      x ∈ RELAT_1.dom (RELAT_1.comp f (RELAT_1.restrict g (RELAT_1.rng f))) := by
    intro x
    constructor
    · intro hx
      have ⟨hxf, hfxg⟩ := (FUNCT_1.th11 hf.2 (f := f) (g := g) (x := x)).mp hx
      have hfxr : FUNCT_1.apply f x ∈ RELAT_1.rng f := FUNCT_1.th3 hf.2 hxf
      have hfxd : FUNCT_1.apply f x ∈
          RELAT_1.dom (RELAT_1.restrict g (RELAT_1.rng f)) :=
        Eq.subst (motive := fun s => FUNCT_1.apply f x ∈ s) hrest.symm
          ((XBOOLE_0.def4 _ _ _).mpr ⟨hfxg, hfxr⟩)
      exact (FUNCT_1.th11 hf.2 (f := f) (g := RELAT_1.restrict g (RELAT_1.rng f))
        (x := x)).mpr ⟨hxf, hfxd⟩
    · intro hx
      have ⟨hxf, hfxr⟩ := (FUNCT_1.th11 hf.2 (f := f)
        (g := RELAT_1.restrict g (RELAT_1.rng f)) (x := x)).mp hx
      have hfxg : FUNCT_1.apply f x ∈ RELAT_1.dom g :=
        ((XBOOLE_0.def4 _ _ _).mp
          (Eq.subst (motive := fun s => FUNCT_1.apply f x ∈ s) hrest hfxr)).1
      exact (FUNCT_1.th11 hf.2 (f := f) (g := g) (x := x)).mpr ⟨hxf, hfxg⟩
  have hdomeq : RELAT_1.dom (RELAT_1.comp f g) =
      RELAT_1.dom (RELAT_1.comp f (RELAT_1.restrict g (RELAT_1.rng f))) :=
    eq_of_mem hdom
  refine FUNCT_1.th2 (FUNCT_1.comp_isFunction hf hg)
    (FUNCT_1.comp_isFunction hf
      (FUNCT_1.restrict_isFunction (X := RELAT_1.rng f) hg)) hdomeq ?_
  intro x hx
  have ⟨hxf, _⟩ := (FUNCT_1.th11 hf.2 (f := f) (g := g) (x := x)).mp hx
  have hfxr : FUNCT_1.apply f x ∈ RELAT_1.rng f := FUNCT_1.th3 hf.2 hxf
  have h1 := FUNCT_1.th12 hf.2 hg.2 hx
  have h2 := FUNCT_1.th49 hg.2 hfxr
  have h3 := FUNCT_1.th13 hf.2
    (FUNCT_1.restrict_isFunction (X := RELAT_1.rng f) hg).2 hxf
  exact h1.trans (h2.symm.trans h3.symm)

/-- `FUNCT_4:3` — `id X ⊆ id Y ↔ X ⊆ Y`. -/
theorem th3 (X Y : TarskiSet.{u}) :
    RELAT_1.id X ⊆ RELAT_1.id Y ↔ X ⊆ Y := by
  constructor
  · intro h x hx
    exact ((RELAT_1.def10 Y x x).mp
      (h _ ((RELAT_1.def10 X x x).mpr ⟨hx, rfl⟩))).1
  · intro hXY
    exact RELAT_1.rel_subset (RELAT_1.id_isRelation X) fun x y hp =>
      let ⟨hx, heq⟩ := (RELAT_1.def10 X x y).mp hp
      (RELAT_1.def10 Y x y).mpr ⟨hXY _ hx, heq⟩

/-- `FUNCT_4:4` — `X ⊆ Y → X --> a ⊆ Y --> a`. -/
theorem th4 {X Y a : TarskiSet.{u}} (h : X ⊆ Y) :
    FUNCOP_1.mapsTo X a ⊆ FUNCOP_1.mapsTo Y a := by
  have hdX : RELAT_1.dom (FUNCOP_1.mapsTo X a) = X := FUNCOP_1.mapsTo_dom X a
  have hdY : RELAT_1.dom (FUNCOP_1.mapsTo Y a) = Y := FUNCOP_1.mapsTo_dom Y a
  refine (GRFUNC_1.th2 (FUNCOP_1.mapsTo_isFunction X a)
    (FUNCOP_1.mapsTo_isFunction Y a)).mpr ⟨?_, ?_⟩
  · exact Eq.subst (motive := fun s => s ⊆ RELAT_1.dom (FUNCOP_1.mapsTo Y a))
      hdX.symm (Eq.subst (motive := fun s => X ⊆ s) hdY.symm h)
  · intro x hx
    have hxX : x ∈ X := Eq.subst (motive := fun s => x ∈ s) hdX hx
    have hxY : x ∈ Y := h _ hxX
    exact (FUNCOP_1.th7 hxX).trans (FUNCOP_1.th7 hxY).symm

/-- `FUNCT_4:5` (`Th5`) -/
theorem th5 {X Y a b : TarskiSet.{u}}
    (h : FUNCOP_1.mapsTo X a ⊆ FUNCOP_1.mapsTo Y b) : X ⊆ Y := by
  have hd := (RELAT_1.th11 h).1
  exact Eq.subst (motive := fun s => s ⊆ Y) (FUNCOP_1.mapsTo_dom X a)
    (Eq.subst (motive := fun s => RELAT_1.dom (FUNCOP_1.mapsTo X a) ⊆ s)
      (FUNCOP_1.mapsTo_dom Y b) hd)

/-- `FUNCT_4:6` -/
theorem th6 {X Y a b : TarskiSet.{u}} (hX : X ≠ (∅ : TarskiSet.{u}))
    (h : FUNCOP_1.mapsTo X a ⊆ FUNCOP_1.mapsTo Y b) : a = b := by
  obtain ⟨x, hx⟩ := exists_mem_of_ne hX
  have hXY := th5 h
  have hxY : x ∈ Y := hXY _ hx
  have hYa : FUNCT_1.apply (FUNCOP_1.mapsTo Y b) x = b := FUNCOP_1.th7 hxY
  have hXa : FUNCT_1.apply (FUNCOP_1.mapsTo X a) x = a := FUNCOP_1.th7 hx
  have hdX : RELAT_1.dom (FUNCOP_1.mapsTo X a) = X := FUNCOP_1.mapsTo_dom X a
  have hxD : x ∈ RELAT_1.dom (FUNCOP_1.mapsTo X a) :=
    Eq.subst (motive := fun s => x ∈ s) hdX.symm hx
  have heq := ((GRFUNC_1.th2 (FUNCOP_1.mapsTo_isFunction X a)
    (FUNCOP_1.mapsTo_isFunction Y b)).mp h).2 x hxD
  exact hXa.symm.trans (heq.trans hYa)

/-- `FUNCT_4:7` -/
theorem th7 {f x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hx : x ∈ RELAT_1.dom f) :
    FUNCOP_1.dotArrow x (FUNCT_1.apply f x) ⊆ f := by
  refine (GRFUNC_1.th2 (FUNCOP_1.dotArrow_isFunction x (FUNCT_1.apply f x)) hf).mpr
    ⟨?_, ?_⟩
  · intro y hy
    exact Eq.subst (motive := fun s => s ∈ RELAT_1.dom f)
      (FUNCOP_1.th75 hy).symm hx
  · intro y hy
    have hyx : y = x := FUNCOP_1.th75 hy
    exact Eq.subst (motive := fun z =>
        FUNCT_1.apply (FUNCOP_1.dotArrow x (FUNCT_1.apply f x)) z =
          FUNCT_1.apply f z)
      hyx.symm (FUNCOP_1.th72 x (FUNCT_1.apply f x))

/-- `FUNCT_4:8` — `Y|`f|X ⊆ f`. -/
theorem th8 (f X Y : TarskiSet.{u}) :
    RELAT_1.restrict (RELAT_1.restrictRng Y f) X ⊆ f :=
  XBOOLE_1.th1 (RELAT_1.th59 (R := RELAT_1.restrictRng Y f) (X := X))
    (RELAT_1.th86 (Y := Y) (R := f))

/-- `FUNCT_4:9` -/
theorem th9 {f g X Y : TarskiSet.{u}} (h : f ⊆ g) :
    RELAT_1.restrict (RELAT_1.restrictRng Y f) X ⊆
      RELAT_1.restrict (RELAT_1.restrictRng Y g) X :=
  RELAT_1.th76 (RELAT_1.th101 (Y := Y) h) (X := X)

/-! ## `f +* g` (`FUNCT_4:def 1`) — override -/

/-- Witness for `f +* g`. -/
noncomputable def overrideWitness (f g : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (PARTFUN1.sch_LambdaC
    (RELAT_1.dom f ∪ RELAT_1.dom g)
    (fun x => x ∈ RELAT_1.dom g)
    (FUNCT_1.apply g) (FUNCT_1.apply f))

private theorem overrideWitness_spec (f g : TarskiSet.{u}) :
    FUNCT_1.isFunction (overrideWitness f g) ∧
      RELAT_1.dom (overrideWitness f g) = RELAT_1.dom f ∪ RELAT_1.dom g ∧
      ∀ x, x ∈ RELAT_1.dom f ∪ RELAT_1.dom g →
        (x ∈ RELAT_1.dom g →
          FUNCT_1.apply (overrideWitness f g) x = FUNCT_1.apply g x) ∧
        (x ∉ RELAT_1.dom g →
          FUNCT_1.apply (overrideWitness f g) x = FUNCT_1.apply f x) :=
  Classical.choose_spec (PARTFUN1.sch_LambdaC
    (RELAT_1.dom f ∪ RELAT_1.dom g)
    (fun x => x ∈ RELAT_1.dom g)
    (FUNCT_1.apply g) (FUNCT_1.apply f))

/-- Uniqueness of the override characterization. -/
theorem override_unique {f g h1 h2 : TarskiSet.{u}}
    (hh1 : FUNCT_1.isFunction h1) (hh2 : FUNCT_1.isFunction h2)
    (hd1 : RELAT_1.dom h1 = RELAT_1.dom f ∪ RELAT_1.dom g)
    (hv1 : ∀ x, x ∈ RELAT_1.dom f ∪ RELAT_1.dom g →
      (x ∈ RELAT_1.dom g → FUNCT_1.apply h1 x = FUNCT_1.apply g x) ∧
        (x ∉ RELAT_1.dom g → FUNCT_1.apply h1 x = FUNCT_1.apply f x))
    (hd2 : RELAT_1.dom h2 = RELAT_1.dom f ∪ RELAT_1.dom g)
    (hv2 : ∀ x, x ∈ RELAT_1.dom f ∪ RELAT_1.dom g →
      (x ∈ RELAT_1.dom g → FUNCT_1.apply h2 x = FUNCT_1.apply g x) ∧
        (x ∉ RELAT_1.dom g → FUNCT_1.apply h2 x = FUNCT_1.apply f x)) :
    h1 = h2 := by
  refine FUNCT_1.th2 hh1 hh2 (hd1.trans hd2.symm) ?_
  intro x hx
  have hxU : x ∈ RELAT_1.dom f ∪ RELAT_1.dom g :=
    Eq.subst (motive := fun s => x ∈ s) hd1 hx
  exact Or.elim (Classical.em (x ∈ RELAT_1.dom g))
    (fun hg => ((hv1 x hxU).1 hg).trans ((hv2 x hxU).1 hg).symm)
    (fun hng => ((hv1 x hxU).2 hng).trans ((hv2 x hxU).2 hng).symm)

/-- `FUNCT_4:def 1` — `f +* g`. -/
noncomputable def override (f g : TarskiSet.{u}) : TarskiSet.{u} :=
  overrideWitness f g

/-- `FUNCT_4:def 1` characterization. -/
theorem def1 (f g : TarskiSet.{u}) :
    FUNCT_1.isFunction (override f g) ∧
      RELAT_1.dom (override f g) = RELAT_1.dom f ∪ RELAT_1.dom g ∧
      ∀ x, x ∈ RELAT_1.dom f ∪ RELAT_1.dom g →
        (x ∈ RELAT_1.dom g →
          FUNCT_1.apply (override f g) x = FUNCT_1.apply g x) ∧
        (x ∉ RELAT_1.dom g →
          FUNCT_1.apply (override f g) x = FUNCT_1.apply f x) :=
  overrideWitness_spec f g

theorem override_isFunction (f g : TarskiSet.{u}) :
    FUNCT_1.isFunction (override f g) :=
  (def1 f g).1

theorem override_dom (f g : TarskiSet.{u}) :
    RELAT_1.dom (override f g) = RELAT_1.dom f ∪ RELAT_1.dom g :=
  (def1 f g).2.1

/-- Idempotence cluster: `f +* f = f`. -/
theorem override_idempotence (f : TarskiSet.{u}) (hf : FUNCT_1.isFunction f) :
    override f f = f := by
  refine override_unique (override_isFunction f f) hf
    (override_dom f f) (fun x hx => (def1 f f).2.2 x hx)
    (XBOOLE_0.union_idem (RELAT_1.dom f)).symm ?_
  intro x hx
  have hxD : x ∈ RELAT_1.dom f :=
    (XBOOLE_0.def3 _ _ _).mp hx |>.elim id id
  exact ⟨fun _ => rfl, fun hng => (hng hxD).elim⟩

/-- `FUNCT_4:10` (`Th10`) -/
theorem th10 (f g : TarskiSet.{u}) :
    RELAT_1.dom f ⊆ RELAT_1.dom (override f g) ∧
      RELAT_1.dom g ⊆ RELAT_1.dom (override f g) := by
  have hd := override_dom f g
  exact ⟨Eq.subst (motive := fun s => RELAT_1.dom f ⊆ s) hd.symm
      (XBOOLE_1.th7 (X := RELAT_1.dom f) (Y := RELAT_1.dom g)),
    Eq.subst (motive := fun s => RELAT_1.dom g ⊆ s) hd.symm
      (Eq.subst (motive := fun s => RELAT_1.dom g ⊆ s)
        (XBOOLE_0.union_comm (RELAT_1.dom g) (RELAT_1.dom f))
        (XBOOLE_1.th7 (X := RELAT_1.dom g) (Y := RELAT_1.dom f)))⟩

/-- `FUNCT_4:11` (`Th11`) -/
theorem th11 {f g x : TarskiSet.{u}} (hx : x ∉ RELAT_1.dom g) :
    FUNCT_1.apply (override f g) x = FUNCT_1.apply f x := by
  have := Classical.propDecidable (x ∈ RELAT_1.dom f ∪ RELAT_1.dom g)
  by_cases hU : x ∈ RELAT_1.dom f ∪ RELAT_1.dom g
  · exact ((def1 f g).2.2 x hU).2 hx
  · have hnf : x ∉ RELAT_1.dom f := fun hf =>
      hU ((XBOOLE_0.def3 _ _ _).mpr (Or.inl hf))
    have hnd : x ∉ RELAT_1.dom (override f g) := fun hd =>
      hU (Eq.subst (motive := fun s => x ∈ s) (override_dom f g) hd)
    exact (FUNCT_1.apply_of_not_mem hnd).trans
      (FUNCT_1.apply_of_not_mem hnf).symm

/-- `FUNCT_4:12` (`Th12`) -/
theorem th12 (f g x : TarskiSet.{u}) :
    x ∈ RELAT_1.dom (override f g) ↔
      x ∈ RELAT_1.dom f ∨ x ∈ RELAT_1.dom g :=
  (Eq.subst (motive := fun s => x ∈ s ↔ x ∈ RELAT_1.dom f ∨ x ∈ RELAT_1.dom g)
    (override_dom f g).symm (XBOOLE_0.def3 _ _ x))

/-- `FUNCT_4:13` (`Th13`) -/
theorem th13 {f g x : TarskiSet.{u}} (hx : x ∈ RELAT_1.dom g) :
    FUNCT_1.apply (override f g) x = FUNCT_1.apply g x := by
  have hU : x ∈ RELAT_1.dom f ∪ RELAT_1.dom g :=
    (XBOOLE_0.def3 _ _ _).mpr (Or.inr hx)
  exact ((def1 f g).2.2 x hU).1 hx

/-- `FUNCT_4:14` (`Th14`) — associativity. -/
theorem th14 (f g h : TarskiSet.{u}) :
    override (override f g) h = override f (override g h) := by
  have hL := override_isFunction (override f g) h
  have hR := override_isFunction f (override g h)
  have hdL : RELAT_1.dom (override (override f g) h) =
      RELAT_1.dom f ∪ RELAT_1.dom g ∪ RELAT_1.dom h :=
    (override_dom (override f g) h).trans
      (congrArg (fun s => s ∪ RELAT_1.dom h) (override_dom f g))
  have hdR : RELAT_1.dom (override f (override g h)) =
      RELAT_1.dom f ∪ (RELAT_1.dom g ∪ RELAT_1.dom h) :=
    (override_dom f (override g h)).trans
      (congrArg (fun s => RELAT_1.dom f ∪ s) (override_dom g h))
  have hAssoc := XBOOLE_1.th4 (X := RELAT_1.dom f) (Y := RELAT_1.dom g)
    (Z := RELAT_1.dom h)
  refine FUNCT_1.th2 hL hR (hdL.trans (hAssoc.trans hdR.symm)) ?_
  intro x hx
  have hxL : x ∈ RELAT_1.dom f ∪ RELAT_1.dom g ∪ RELAT_1.dom h :=
    Eq.subst (motive := fun s => x ∈ s) hdL hx
  exact Or.elim (Classical.em (x ∈ RELAT_1.dom h))
    (fun hh => by
      have hgh : x ∈ RELAT_1.dom (override g h) :=
        Eq.subst (motive := fun s => x ∈ s) (override_dom g h).symm
          ((XBOOLE_0.def3 _ _ _).mpr (Or.inr hh))
      exact (th13 (f := override f g) (g := h) hh).trans
        ((th13 (f := f) (g := override g h) hgh).trans
          (th13 (f := g) (g := h) hh)).symm)
    (fun hnh =>
      (th11 (f := override f g) (g := h) hnh).trans <|
      Or.elim (Classical.em (x ∈ RELAT_1.dom g))
        (fun hg => by
          have hgh : x ∈ RELAT_1.dom (override g h) :=
            Eq.subst (motive := fun s => x ∈ s) (override_dom g h).symm
              ((XBOOLE_0.def3 _ _ _).mpr (Or.inl hg))
          exact (th13 (f := f) (g := g) hg).trans
            ((th13 (f := f) (g := override g h) hgh).trans
              (th11 (f := g) (g := h) hnh)).symm)
        (fun hng => by
          have hngh : x ∉ RELAT_1.dom (override g h) := fun hmem =>
            (Or.elim ((XBOOLE_0.def3 _ _ _).mp
                (Eq.subst (motive := fun s => x ∈ s) (override_dom g h) hmem))
              hng hnh)
          exact (th11 (f := f) (g := g) hng).trans
            (th11 (f := f) (g := override g h) hngh).symm))

/-- `FUNCT_4:15` (`Th15`) -/
theorem th15 {f g x : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g) (ht : PARTFUN1.tolerates f g)
    (hx : x ∈ RELAT_1.dom f) :
    FUNCT_1.apply (override f g) x = FUNCT_1.apply f x :=
  Or.elim (Classical.em (x ∈ RELAT_1.dom g))
    (fun hxg =>
      (th13 (f := f) (g := g) hxg).trans
        (ht x ((XBOOLE_0.def4 _ _ _).mpr ⟨hx, hxg⟩)).symm)
    (fun hng => th11 (f := f) (g := g) hng)

/-- `FUNCT_4:16` -/
theorem th16 {f g x : TarskiSet.{u}}
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f) (RELAT_1.dom g))
    (hx : x ∈ RELAT_1.dom f) :
    FUNCT_1.apply (override f g) x = FUNCT_1.apply f x := by
  have hng : x ∉ RELAT_1.dom g := fun hxg =>
    (XBOOLE_0.empty_iff x).mp
      (Eq.subst (motive := fun s => x ∈ s) hmiss
        ((XBOOLE_0.def4 _ _ _).mpr ⟨hx, hxg⟩))
  exact th11 (f := f) (g := g) hng

/-- `FUNCT_4:17` (`Th17`) -/
theorem th17 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    RELAT_1.rng (override f g) ⊆ RELAT_1.rng f ∪ RELAT_1.rng g := by
  intro y hy
  obtain ⟨x, hx, heq⟩ := (FUNCT_1.def3 (override_isFunction f g).2).mp hy
  have hxU : x ∈ RELAT_1.dom f ∨ x ∈ RELAT_1.dom g := (th12 f g x).mp hx
  refine Eq.subst (motive := fun s => s ∈ RELAT_1.rng f ∪ RELAT_1.rng g) heq.symm ?_
  exact Or.elim hxU
    (fun hxf =>
      Or.elim (Classical.em (x ∈ RELAT_1.dom g))
        (fun hxg =>
          (XBOOLE_0.def3 _ _ _).mpr (Or.inr
            (Eq.subst (motive := fun s => s ∈ RELAT_1.rng g)
              (th13 (f := f) (g := g) hxg).symm (FUNCT_1.th3 hg.2 hxg))))
        (fun hng =>
          (XBOOLE_0.def3 _ _ _).mpr (Or.inl
            (Eq.subst (motive := fun s => s ∈ RELAT_1.rng f)
              (th11 (f := f) (g := g) hng).symm (FUNCT_1.th3 hf.2 hxf)))))
    (fun hxg =>
      (XBOOLE_0.def3 _ _ _).mpr (Or.inr
        (Eq.subst (motive := fun s => s ∈ RELAT_1.rng g)
          (th13 (f := f) (g := g) hxg).symm (FUNCT_1.th3 hg.2 hxg))))

/-- `FUNCT_4:18` -/
theorem th18 {f g : TarskiSet.{u}} (hg : FUNCT_1.isFunction g) :
    RELAT_1.rng g ⊆ RELAT_1.rng (override f g) := by
  intro y hy
  obtain ⟨x, hx, heq⟩ := (FUNCT_1.def3 hg.2).mp hy
  have hxO : x ∈ RELAT_1.dom (override f g) := (th12 f g x).mpr (Or.inr hx)
  exact (FUNCT_1.def3 (override_isFunction f g).2).mpr
    ⟨x, hxO, heq.trans (th13 (f := f) (g := g) hx).symm⟩

/-- `FUNCT_4:19` (`Th19`) -/
theorem th19 {f g : TarskiSet.{u}} (hg : FUNCT_1.isFunction g)
    (h : RELAT_1.dom f ⊆ RELAT_1.dom g) : override f g = g := by
  have hd : RELAT_1.dom (override f g) = RELAT_1.dom g :=
    (override_dom f g).trans (XBOOLE_1.th12 h)
  refine FUNCT_1.th2 (override_isFunction f g) hg hd ?_
  intro x hx
  have hxg : x ∈ RELAT_1.dom g := Eq.subst (motive := fun s => x ∈ s) hd hx
  exact th13 (f := f) (g := g) hxg

/-- Registration: `{} +* f = f` reducibility (`reg1`). -/
theorem reg1 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (he : g = (∅ : TarskiSet.{u})) : override g f = f := by
  have hdom : RELAT_1.dom g ⊆ RELAT_1.dom f :=
    Eq.subst (motive := fun s => RELAT_1.dom s ⊆ RELAT_1.dom f) he.symm
      (Eq.subst (motive := fun s => s ⊆ RELAT_1.dom f) RELAT_1.th38.1.symm
        (XBOOLE_1.th2 (X := RELAT_1.dom f)))
  exact th19 (f := g) (g := f) hf hdom

/-- `FUNCT_4:20` (`Th20`) -/
theorem th20 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    override (∅ : TarskiSet.{u}) f = f :=
  reg1 hf rfl

/-- `FUNCT_4:21` (`Th21`) -/
theorem th21 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    override f (∅ : TarskiSet.{u}) = f := by
  have hdom : RELAT_1.dom (override f (∅ : TarskiSet.{u})) = RELAT_1.dom f :=
    (override_dom f (∅ : TarskiSet.{u})).trans
      ((congrArg (fun s => RELAT_1.dom f ∪ s) RELAT_1.th38.1).trans
        ((XBOOLE_0.union_comm (RELAT_1.dom f) (∅ : TarskiSet.{u})).trans
          (XBOOLE_1.th12 (XBOOLE_1.th2 (X := RELAT_1.dom f)))))
  refine FUNCT_1.th2 (override_isFunction f (∅ : TarskiSet.{u})) hf hdom ?_
  intro x hx
  have hng : x ∉ RELAT_1.dom (∅ : TarskiSet.{u}) := fun hxg =>
    ((XBOOLE_0.empty_iff x).mp
      (Eq.subst (motive := fun s => x ∈ s) RELAT_1.th38.1 hxg)).elim
  exact th11 (f := f) (g := (∅ : TarskiSet.{u})) hng

/-- `FUNCT_4:22` — `id(X) +* id(Y) = id(X ∪ Y)`. -/
theorem th22 (X Y : TarskiSet.{u}) :
    override (RELAT_1.id X) (RELAT_1.id Y) = RELAT_1.id (X ∪ Y) := by
  have hh := FUNCT_1.id_isFunction (X ∪ Y)
  have hdomXY : RELAT_1.dom (RELAT_1.id X) ∪ RELAT_1.dom (RELAT_1.id Y) =
      X ∪ Y :=
    (congrArg (fun s => s ∪ RELAT_1.dom (RELAT_1.id Y)) (RELAT_1.id_dom X)).trans
      (congrArg (fun s => X ∪ s) (RELAT_1.id_dom Y))
  have hd : RELAT_1.dom (override (RELAT_1.id X) (RELAT_1.id Y)) =
      RELAT_1.dom (RELAT_1.id (X ∪ Y)) :=
    (override_dom _ _).trans (hdomXY.trans (RELAT_1.id_dom (X ∪ Y)).symm)
  refine FUNCT_1.th2 (override_isFunction _ _) hh hd ?_
  intro x hx
  have hxU : x ∈ X ∪ Y :=
    Eq.subst (motive := fun s => x ∈ s)
      ((override_dom (RELAT_1.id X) (RELAT_1.id Y)).trans hdomXY) hx
  have happ' : FUNCT_1.apply (RELAT_1.id (X ∪ Y)) x = x :=
    FUNCT_1.id_apply hxU
  exact Or.elim (Classical.em (x ∈ RELAT_1.dom (RELAT_1.id Y)))
    (fun hy =>
      (th13 (f := RELAT_1.id X) (g := RELAT_1.id Y) hy).trans
        ((FUNCT_1.id_apply
          (Eq.subst (motive := fun s => x ∈ s) (RELAT_1.id_dom Y) hy)).trans
          happ'.symm))
    (fun hny =>
      have hxX : x ∈ X :=
        Or.elim ((XBOOLE_0.def3 _ _ _).mp hxU) id fun hyY =>
          (hny (Eq.subst (motive := fun s => x ∈ s)
            (RELAT_1.id_dom Y).symm hyY)).elim
      (th11 (f := RELAT_1.id X) (g := RELAT_1.id Y) hny).trans
        ((FUNCT_1.id_apply hxX).trans happ'.symm))

/-- `FUNCT_4:23` — `(f +* g)|(dom g) = g`. -/
theorem th23 {f g : TarskiSet.{u}} (hg : FUNCT_1.isFunction g) :
    RELAT_1.restrict (override f g) (RELAT_1.dom g) = g := by
  have hsub : RELAT_1.dom g ⊆ RELAT_1.dom (override f g) := (th10 f g).2
  have hd : RELAT_1.dom (RELAT_1.restrict (override f g) (RELAT_1.dom g)) =
      RELAT_1.dom g := RELAT_1.th62 hsub
  refine FUNCT_1.th2 (FUNCT_1.restrict_isFunction (override_isFunction f g)) hg hd ?_
  intro x hx
  have hxg : x ∈ RELAT_1.dom g := Eq.subst (motive := fun s => x ∈ s) hd hx
  exact (FUNCT_1.th47 (override_isFunction f g).2 hx).trans (th13 (f := f) hxg)

/-- `FUNCT_4:24` (`Th24`) -/
theorem th24 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    RELAT_1.restrict (override f g) (RELAT_1.dom f \ RELAT_1.dom g) ⊆ f := by
  have hfO := override_isFunction f g
  have hdsub : RELAT_1.dom
      (RELAT_1.restrict (override f g) (RELAT_1.dom f \ RELAT_1.dom g)) ⊆
      RELAT_1.dom f \ RELAT_1.dom g := RELAT_1.th58
  refine (GRFUNC_1.th2 (FUNCT_1.restrict_isFunction hfO) hf).mpr ⟨?_, ?_⟩
  · exact XBOOLE_1.th1 hdsub (fun x hx => ((XBOOLE_0.def5 _ _ _).mp hx).1)
  · intro x hx
    have hxD : x ∈ RELAT_1.dom f \ RELAT_1.dom g := hdsub _ hx
    have hng : x ∉ RELAT_1.dom g := ((XBOOLE_0.def5 _ _ _).mp hxD).2
    exact (FUNCT_1.th47 hfO.2 hx).trans (th11 (f := f) (g := g) hng)

/-- `FUNCT_4:25` (`Th25`) -/
theorem th25 {f g : TarskiSet.{u}} (hg : FUNCT_1.isFunction g) :
    g ⊆ override f g := by
  refine (GRFUNC_1.th2 hg (override_isFunction f g)).mpr ⟨(th10 f g).2, ?_⟩
  intro x hx
  exact (th13 (f := f) (g := g) hx).symm

/-- `FUNCT_4:26` -/
theorem th26 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g) (_hh : FUNCT_1.isFunction h)
    (ht : PARTFUN1.tolerates f (override g h)) :
    PARTFUN1.tolerates
      (RELAT_1.restrict f (RELAT_1.dom f \ RELAT_1.dom h)) g := by
  intro x hx
  have ⟨hxfR, hxg⟩ := (XBOOLE_0.def4 _ _ _).mp hx
  have hdsub := RELAT_1.th58 (R := f) (X := RELAT_1.dom f \ RELAT_1.dom h)
  have hxD : x ∈ RELAT_1.dom f \ RELAT_1.dom h := hdsub _ hxfR
  have ⟨hxf, hnh⟩ := (XBOOLE_0.def5 _ _ _).mp hxD
  have hxgh : x ∈ RELAT_1.dom (override g h) := (th12 g h x).mpr (Or.inl hxg)
  have ht' := ht x ((XBOOLE_0.def4 _ _ _).mpr ⟨hxf, hxgh⟩)
  have hrest := FUNCT_1.th49 hf.2 hxD
  have hgh := th11 (f := g) (g := h) hnh
  exact hrest.trans (ht'.trans hgh)

/-- `FUNCT_4:27` (`Th27`) -/
theorem th27 {f g h : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g) (_hh : FUNCT_1.isFunction h)
    (ht : PARTFUN1.tolerates f (override g h)) :
    PARTFUN1.tolerates f h := by
  intro x hx
  have ⟨hxf, hxh⟩ := (XBOOLE_0.def4 _ _ _).mp hx
  have hxgh : x ∈ RELAT_1.dom (override g h) := (th12 g h x).mpr (Or.inr hxh)
  have ht' := ht x ((XBOOLE_0.def4 _ _ _).mpr ⟨hxf, hxgh⟩)
  exact ht'.trans (th13 (f := g) (g := h) hxh)

/-- `FUNCT_4:28` (`Th28`) -/
theorem th28 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    PARTFUN1.tolerates f g ↔ f ⊆ override f g := by
  constructor
  · intro ht
    refine (GRFUNC_1.th2 hf (override_isFunction f g)).mpr ⟨(th10 f g).1, ?_⟩
    intro x hx
    exact (th15 hf hg ht hx).symm
  · intro hsub
    exact th27 (f := f) (g := f) (h := g) hf hf hg
      (PARTFUN1.th54 hf (override_isFunction f g) hsub)

/-- `FUNCT_4:29` (`Th29`) -/
theorem th29 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    override f g ⊆ f ∪ g := by
  intro p hp
  obtain ⟨x, y, heq⟩ := (override_isFunction f g).1 _ hp
  have hp' : TARSKI.pair x y ∈ override f g :=
    Eq.subst (motive := fun s => s ∈ override f g) heq hp
  have hxO : x ∈ RELAT_1.dom (override f g) := RELAT_1.pair_mem_dom hp'
  have hy : y = FUNCT_1.apply (override f g) x :=
    (FUNCT_1.apply_of_mem (override_isFunction f g).2 hp').symm
  exact Or.elim ((th12 f g x).mp hxO)
    (fun hxf =>
      Or.elim (Classical.em (x ∈ RELAT_1.dom g))
        (fun hxg =>
          (XBOOLE_0.def3 _ _ _).mpr (Or.inr
            (Eq.subst (motive := fun s => s ∈ g) heq.symm
              ((FUNCT_1.th1 hg.2).mpr ⟨hxg,
                hy.trans (th13 (f := f) (g := g) hxg)⟩))))
        (fun hng =>
          (XBOOLE_0.def3 _ _ _).mpr (Or.inl
            (Eq.subst (motive := fun s => s ∈ f) heq.symm
              ((FUNCT_1.th1 hf.2).mpr ⟨hxf,
                hy.trans (th11 (f := f) (g := g) hng)⟩)))))
    (fun hxg =>
      (XBOOLE_0.def3 _ _ _).mpr (Or.inr
        (Eq.subst (motive := fun s => s ∈ g) heq.symm
          ((FUNCT_1.th1 hg.2).mpr ⟨hxg,
            hy.trans (th13 (f := f) (g := g) hxg)⟩))))

/-- `FUNCT_4:30` (`Th30`) -/
theorem th30 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    PARTFUN1.tolerates f g ↔ f ∪ g = override f g := by
  constructor
  · intro ht
    have h1 : f ⊆ override f g := (th28 hf hg).mp ht
    have h2 : override f g ⊆ f ∪ g := th29 hf hg
    have h3 : g ⊆ override f g := th25 (f := f) hg
    have h4 : f ∪ g ⊆ override f g := XBOOLE_1.th8 h1 h3
    exact (XBOOLE_0.def10 (X := f ∪ g) (Y := override f g)).mpr ⟨h4, h2⟩
  · intro heq
    exact (PARTFUN1.th51 hf hg).mpr ⟨override f g, override_isFunction f g, heq⟩

/-- `FUNCT_4:31` (`Th31`) -/
theorem th31 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f) (RELAT_1.dom g)) :
    f ∪ g = override f g :=
  (th30 hf hg).mp (PARTFUN1.th56 hf hg hmiss)

/-- `FUNCT_4:32` (`Th32`) -/
theorem th32 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f) (RELAT_1.dom g)) :
    f ⊆ override f g :=
  Eq.subst (motive := fun s => f ⊆ s) (th31 hf hg hmiss)
    (XBOOLE_1.th7 (X := f) (Y := g))

/-- `FUNCT_4:33` -/
theorem th33 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f) (RELAT_1.dom g)) :
    RELAT_1.restrict (override f g) (RELAT_1.dom f) = f := by
  have hdiff : RELAT_1.dom f \ RELAT_1.dom g = RELAT_1.dom f :=
    (XBOOLE_1.th83).mp hmiss
  have hd : RELAT_1.dom (RELAT_1.restrict (override f g) (RELAT_1.dom f)) =
      RELAT_1.dom f :=
    (RELAT_1.th61 (R := override f g) (X := RELAT_1.dom f)).trans
      ((congrArg (fun s => s ∩ RELAT_1.dom f) (override_dom f g)).trans
        ((XBOOLE_0.inter_comm (RELAT_1.dom f ∪ RELAT_1.dom g)
            (RELAT_1.dom f)).trans
          (XBOOLE_1.th21 (X := RELAT_1.dom f) (Y := RELAT_1.dom g))))
  have hsub : RELAT_1.restrict (override f g) (RELAT_1.dom f) ⊆ f :=
    Eq.subst (motive := fun s =>
        RELAT_1.restrict (override f g) s ⊆ f) hdiff (th24 (f := f) (g := g) hf)
  exact GRFUNC_1.th3 (FUNCT_1.restrict_isFunction (override_isFunction f g))
    hf hd hsub


/-- `FUNCT_4:34` (`Th34`) -/
theorem th34 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    PARTFUN1.tolerates f g ↔ override f g = override g f := by
  constructor
  · intro ht
    have hd : RELAT_1.dom (override f g) = RELAT_1.dom (override g f) :=
      (override_dom f g).trans
        ((XBOOLE_0.union_comm (RELAT_1.dom f) (RELAT_1.dom g)).trans
          (override_dom g f).symm)
    refine FUNCT_1.th2 (override_isFunction f g) (override_isFunction g f) hd ?_
    intro x hx
    have hxU : x ∈ RELAT_1.dom f ∪ RELAT_1.dom g :=
      Eq.subst (motive := fun s => x ∈ s) (override_dom f g) hx
    exact Or.elim ((XBOOLE_0.def3 _ _ _).mp hxU)
      (fun hxf =>
        Or.elim (Classical.em (x ∈ RELAT_1.dom g))
          (fun hxg =>
            (th13 (f := f) (g := g) hxg).trans
              ((ht x ((XBOOLE_0.def4 _ _ _).mpr ⟨hxf, hxg⟩)).symm.trans
                (th13 (f := g) (g := f) hxf).symm))
          (fun hng =>
            (th11 (f := f) (g := g) hng).trans
              (th13 (f := g) (g := f) hxf).symm))
      (fun hxg =>
        Or.elim (Classical.em (x ∈ RELAT_1.dom f))
          (fun hxf =>
            (th13 (f := f) (g := g) hxg).trans
              ((ht x ((XBOOLE_0.def4 _ _ _).mpr ⟨hxf, hxg⟩)).symm.trans
                (th13 (f := g) (g := f) hxf).symm))
          (fun hnf =>
            (th13 (f := f) (g := g) hxg).trans
              (th11 (f := g) (g := f) hnf).symm))
  · intro heq x hx
    have ⟨hxf, hxg⟩ := (XBOOLE_0.def4 _ _ _).mp hx
    have h1 := th13 (f := f) (g := g) hxg
    have h2 := th13 (f := g) (g := f) hxf
    exact h2.symm.trans (Eq.subst (motive := fun s =>
        FUNCT_1.apply s x = FUNCT_1.apply g x) heq h1)

/-- `FUNCT_4:35` (`Th35`) -/
theorem th35 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f) (RELAT_1.dom g)) :
    override f g = override g f :=
  (th34 hf hg).mp (PARTFUN1.th56 hf hg hmiss)

/-- `FUNCT_4:36` -/
theorem th36 {f g X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (hg : PARTFUN1.isPartFunc g X Y) (ht : PARTFUN1.isTotal g X) :
    override f g = g :=
  th19 hg.1 (Eq.subst (motive := fun s => RELAT_1.dom f ⊆ s) ht.symm
    (RELSET_1.relationOf_defined hf.2))

/-- `FUNCT_4:37` (`Th37`) -/
theorem th37 {f g X Y : TarskiSet.{u}} (hf : FUNCT_2.isFunctionOf f X Y)
    (hg : FUNCT_2.isFunctionOf g X Y)
    (h : Y = (∅ : TarskiSet.{u}) → X = (∅ : TarskiSet.{u})) :
    override f g = g := by
  have hd : RELAT_1.dom f = X ∧ RELAT_1.dom g = X := by
    have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
    by_cases hY : Y = (∅ : TarskiSet.{u})
    · have hX := h hY
      have hf0 := FUNCT_2.functionOf_empty_cod hf hY
      have hg0 := FUNCT_2.functionOf_empty_cod hg hY
      exact ⟨Eq.subst (motive := fun s => RELAT_1.dom s = X) hf0.symm
          (Eq.subst (motive := fun s => s = X) RELAT_1.th38.1.symm hX.symm),
        Eq.subst (motive := fun s => RELAT_1.dom s = X) hg0.symm
          (Eq.subst (motive := fun s => s = X) RELAT_1.th38.1.symm hX.symm)⟩
    · exact ⟨FUNCT_2.functionOf_dom_eq hf hY, FUNCT_2.functionOf_dom_eq hg hY⟩
  exact th19 (FUNCT_2.functionOf_isFunction hg)
    (Eq.subst (motive := fun s => RELAT_1.dom f ⊆ s) hd.2.symm
      (Eq.subst (motive := fun s => s ⊆ X) hd.1.symm (fun _ h => h)))

/-- `FUNCT_4:38` -/
theorem th38 {f g X : TarskiSet.{u}} (hf : FUNCT_2.isFunctionOf f X X)
    (hg : FUNCT_2.isFunctionOf g X X) : override f g = g :=
  th37 hf hg (fun h => h)

/-- `FUNCT_4:39` — Mizar reserve makes `D` nonempty; Lean states the general form. -/
theorem th39 {f g X D : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f X D) (hg : FUNCT_2.isFunctionOf g X D) :
    override f g = g := by
  have := Classical.propDecidable (D = (∅ : TarskiSet.{u}))
  by_cases hD : D = (∅ : TarskiSet.{u})
  · have hf0 := FUNCT_2.functionOf_empty_cod hf hD
    have hg0 := FUNCT_2.functionOf_empty_cod hg hD
    exact
      Eq.subst (motive := fun s => override s g = g) hf0.symm
        (Eq.subst (motive := fun t => override (∅ : TarskiSet.{u}) t = t) hg0.symm
          (th20 FUNCT_1.empty_isFunction))
  · exact th37 hf hg (fun h => (hD h).elim)

/-- `FUNCT_4:40` -/
theorem th40 {f g X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (hg : PARTFUN1.isPartFunc g X Y) :
    PARTFUN1.isPartFunc (override f g) X Y := by
  have hrng : RELAT_1.rng (override f g) ⊆ RELAT_1.rng f ∪ RELAT_1.rng g :=
    th17 hf.1 hg.1
  have hrY : RELAT_1.rng (override f g) ⊆ Y :=
    XBOOLE_1.th1 hrng (XBOOLE_1.th8 (RELSET_1.relationOf_valued hf.2)
      (RELSET_1.relationOf_valued hg.2))
  have hd : RELAT_1.dom (override f g) = RELAT_1.dom f ∪ RELAT_1.dom g :=
    override_dom f g
  have hdX : RELAT_1.dom (override f g) ⊆ X :=
    Eq.subst (motive := fun s => s ⊆ X) hd.symm
      (XBOOLE_1.th8 (RELSET_1.relationOf_defined hf.2)
        (RELSET_1.relationOf_defined hg.2))
  exact PARTFUN1.partFunc_of (override_isFunction f g) hdX hrY

/-! ## `~f` (`FUNCT_4:def 2`) — domain-pair swap (`swapDom`) -/

private def swapDomPred (f x v : TarskiSet.{u}) : Prop :=
  ∃ y z, x = TARSKI.pair z y ∧ v = FUNCT_1.apply f (TARSKI.pair y z)

noncomputable def swapDomDomain (f : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (XBOOLE_0.sch_separation
    (ZFMISC_1.product (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
      (TARSKI.union (TARSKI.union (RELAT_1.dom f))))
    (fun x => ∃ y z, x = TARSKI.pair z y ∧ TARSKI.pair y z ∈ RELAT_1.dom f))

private theorem swapDomDomain_spec (f : TarskiSet.{u}) :
    ∀ x, x ∈ swapDomDomain f ↔
      x ∈ ZFMISC_1.product (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
        (TARSKI.union (TARSKI.union (RELAT_1.dom f))) ∧
      ∃ y z, x = TARSKI.pair z y ∧ TARSKI.pair y z ∈ RELAT_1.dom f :=
  Classical.choose_spec (XBOOLE_0.sch_separation
    (ZFMISC_1.product (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
      (TARSKI.union (TARSKI.union (RELAT_1.dom f))))
    (fun x => ∃ y z, x = TARSKI.pair z y ∧ TARSKI.pair y z ∈ RELAT_1.dom f))

private theorem swapDom_exists (f : TarskiSet.{u}) :
    ∃ h, FUNCT_1.isFunction h ∧ RELAT_1.dom h = swapDomDomain f ∧
      ∀ x, x ∈ swapDomDomain f → swapDomPred f x (FUNCT_1.apply h x) := by
  refine FUNCT_1.sch_FuncEx (swapDomDomain f) (swapDomPred f) ?_ ?_
  · intro x y1 y2 _hx hp1 hp2
    obtain ⟨y, z, heq, hv1⟩ := hp1
    obtain ⟨y9, z9, heq2, hv2⟩ := hp2
    have ⟨hz, hy⟩ := XTUPLE_0.th1 (x1 := z) (x2 := y) (y1 := z9) (y2 := y9)
      (heq.symm.trans heq2)
    have hpair : TARSKI.pair y z = TARSKI.pair y9 z9 :=
      (congrArg (fun s => TARSKI.pair s z) hy).trans (congrArg (TARSKI.pair y9) hz)
    exact hv1.trans ((congrArg (FUNCT_1.apply f) hpair).trans hv2.symm)
  · intro x hx
    obtain ⟨_, hex⟩ := (swapDomDomain_spec f x).mp hx
    obtain ⟨y, z, heq, hdom⟩ := hex
    exact ⟨FUNCT_1.apply f (TARSKI.pair y z), y, z, heq, rfl⟩

/-- `FUNCT_4:def 2` — `~f`. -/
noncomputable def swapDom (f : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (swapDom_exists f)

theorem swapDom_isFunction (f : TarskiSet.{u}) :
    FUNCT_1.isFunction (swapDom f) :=
  (Classical.choose_spec (swapDom_exists f)).1

private theorem swapDom_dom_eq (f : TarskiSet.{u}) :
    RELAT_1.dom (swapDom f) = swapDomDomain f :=
  (Classical.choose_spec (swapDom_exists f)).2.1

private theorem swapDom_apply_pred {f x : TarskiSet.{u}}
    (hx : x ∈ RELAT_1.dom (swapDom f)) :
    swapDomPred f x (FUNCT_1.apply (swapDom f) x) :=
  (Classical.choose_spec (swapDom_exists f)).2.2 x
    (Eq.subst (motive := fun s => x ∈ s) (swapDom_dom_eq f) hx)

/-- `FUNCT_4:def 2` characterization. -/
theorem def2 (f : TarskiSet.{u}) :
    (∀ x, x ∈ RELAT_1.dom (swapDom f) ↔
      ∃ y z, x = TARSKI.pair z y ∧ TARSKI.pair y z ∈ RELAT_1.dom f) ∧
    ∀ y z, TARSKI.pair y z ∈ RELAT_1.dom f →
      FUNCT_1.apply (swapDom f) (TARSKI.pair z y) =
        FUNCT_1.apply f (TARSKI.pair y z) := by
  constructor
  · intro x
    constructor
    · intro hx
      have hxD : x ∈ swapDomDomain f :=
        Eq.subst (motive := fun s => x ∈ s) (swapDom_dom_eq f) hx
      obtain ⟨y, z, heq, hdom⟩ := ((swapDomDomain_spec f x).mp hxD).2
      exact ⟨y, z, heq, hdom⟩
    · intro ⟨y, z, heq, hdom⟩
      have hyU := (ZFMISC_1.th134 hdom).1
      have hzU := (ZFMISC_1.th134 hdom).2
      have hp : TARSKI.pair z y ∈
          ZFMISC_1.product (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
            (TARSKI.union (TARSKI.union (RELAT_1.dom f))) :=
        (ZFMISC_1.th87).mpr ⟨hzU, hyU⟩
      have hxD : TARSKI.pair z y ∈ swapDomDomain f :=
        (swapDomDomain_spec f _).mpr ⟨hp, y, z, rfl, hdom⟩
      exact Eq.subst (motive := fun s => s ∈ RELAT_1.dom (swapDom f)) heq.symm
        (Eq.subst (motive := fun s => TARSKI.pair z y ∈ s)
          (swapDom_dom_eq f).symm hxD)
  · intro y z hdom
    have hyU := (ZFMISC_1.th134 hdom).1
    have hzU := (ZFMISC_1.th134 hdom).2
    have hp : TARSKI.pair z y ∈
        ZFMISC_1.product (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
          (TARSKI.union (TARSKI.union (RELAT_1.dom f))) :=
      (ZFMISC_1.th87).mpr ⟨hzU, hyU⟩
    have hxD : TARSKI.pair z y ∈ swapDomDomain f :=
      (swapDomDomain_spec f _).mpr ⟨hp, y, z, rfl, hdom⟩
    have hx : TARSKI.pair z y ∈ RELAT_1.dom (swapDom f) :=
      Eq.subst (motive := fun s => TARSKI.pair z y ∈ s)
        (swapDom_dom_eq f).symm hxD
    obtain ⟨y9, z9, heq, hv⟩ := swapDom_apply_pred hx
    have ⟨hz, hy⟩ := XTUPLE_0.th1 (x1 := z) (x2 := y) (y1 := z9) (y2 := y9) heq
    have heqyz : TARSKI.pair y9 z9 = TARSKI.pair y z :=
      (congrArg (fun s => TARSKI.pair s z9) hy.symm).trans
        (congrArg (TARSKI.pair y) hz.symm)
    exact hv.trans (congrArg (FUNCT_1.apply f) heqyz)

/-- `FUNCT_4:41` (`Th41`) -/
theorem th41 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    RELAT_1.rng (swapDom f) ⊆ RELAT_1.rng f := by
  intro y hy
  obtain ⟨x, hx, heq⟩ := (FUNCT_1.def3 (swapDom_isFunction f).2).mp hy
  obtain ⟨x1, x2, hxeq, hdom⟩ := ((def2 f).1 x).mp hx
  have happ : FUNCT_1.apply (swapDom f) x =
      FUNCT_1.apply f (TARSKI.pair x1 x2) :=
    Eq.subst (motive := fun s =>
        FUNCT_1.apply (swapDom f) s =
          FUNCT_1.apply f (TARSKI.pair x1 x2)) hxeq.symm
      ((def2 f).2 x1 x2 hdom)
  exact Eq.subst (motive := fun s => s ∈ RELAT_1.rng f) heq.symm
    (Eq.subst (motive := fun s => s ∈ RELAT_1.rng f) happ.symm
      (FUNCT_1.th3 hf.2 hdom))

/-- `FUNCT_4:42` (`Th42`) -/
theorem th42 (f x y : TarskiSet.{u}) :
    TARSKI.pair x y ∈ RELAT_1.dom f ↔
      TARSKI.pair y x ∈ RELAT_1.dom (swapDom f) := by
  constructor
  · intro h
    exact ((def2 f).1 _).mpr ⟨x, y, rfl, h⟩
  · intro h
    obtain ⟨x1, y1, heq, hdom⟩ := ((def2 f).1 _).mp h
    have ⟨hy, hx⟩ := XTUPLE_0.th1 (x1 := y) (x2 := x) (y1 := y1) (y2 := x1) heq
    exact Eq.subst (motive := fun s => TARSKI.pair s y ∈ RELAT_1.dom f) hx.symm
      (Eq.subst (motive := fun s => TARSKI.pair x1 s ∈ RELAT_1.dom f) hy.symm hdom)

/-- `FUNCT_4:43` -/
theorem th43 {f y x : TarskiSet.{u}}
    (h : TARSKI.pair y x ∈ RELAT_1.dom (swapDom f)) :
    FUNCT_1.apply (swapDom f) (TARSKI.pair y x) =
      FUNCT_1.apply f (TARSKI.pair x y) := by
  have hdom : TARSKI.pair x y ∈ RELAT_1.dom f := (th42 f x y).mpr h
  exact (def2 f).2 x y hdom

/-- `FUNCT_4:44` -/
theorem th44 (f : TarskiSet.{u}) :
    ∃ X Y, RELAT_1.dom (swapDom f) ⊆ ZFMISC_1.product X Y := by
  have hrel : ∀ z, z ∈ RELAT_1.dom (swapDom f) →
      ∃ x y, z = TARSKI.pair x y := by
    intro z hz
    obtain ⟨y, x, heq, _⟩ := ((def2 f).1 z).mp hz
    exact ⟨x, y, heq⟩
  exact th1 hrel

/-- `FUNCT_4:45` (`Th45`) -/
theorem th45 {f X Y : TarskiSet.{u}}
    (h : RELAT_1.dom f ⊆ ZFMISC_1.product X Y) :
    RELAT_1.dom (swapDom f) ⊆ ZFMISC_1.product Y X := by
  intro z hz
  obtain ⟨x, y, heq, hdom⟩ := ((def2 f).1 z).mp hz
  have hp : TARSKI.pair x y ∈ ZFMISC_1.product X Y := h _ hdom
  have ⟨hx, hy⟩ := (ZFMISC_1.th87).mp hp
  exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product Y X) heq.symm
    ((ZFMISC_1.th87).mpr ⟨hy, hx⟩)

/-- `FUNCT_4:46` (`Th46`) -/
theorem th46 {f X Y : TarskiSet.{u}}
    (h : RELAT_1.dom f = ZFMISC_1.product X Y) :
    RELAT_1.dom (swapDom f) = ZFMISC_1.product Y X := by
  apply (XBOOLE_0.def10 (X := RELAT_1.dom (swapDom f))
    (Y := ZFMISC_1.product Y X)).mpr
  refine ⟨th45 (Eq.subst (motive := fun s => s ⊆ ZFMISC_1.product X Y) h.symm
      (fun _ hx => hx)), ?_⟩
  intro z hz
  obtain ⟨y, x, hy, hx, heq⟩ := (ZFMISC_1.def2 Y X z).mp hz
  have hdom : TARSKI.pair x y ∈ RELAT_1.dom f :=
    Eq.subst (motive := fun s => TARSKI.pair x y ∈ s) h.symm
      ((ZFMISC_1.def2 X Y _).mpr ⟨x, y, hx, hy, rfl⟩)
  exact Eq.subst (motive := fun s => s ∈ RELAT_1.dom (swapDom f)) heq.symm
    ((th42 f x y).mp hdom)

/-- `FUNCT_4:47` (`Th47`) -/
theorem th47 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (h : RELAT_1.dom f ⊆ ZFMISC_1.product X Y) :
    RELAT_1.rng (swapDom f) = RELAT_1.rng f := by
  apply (XBOOLE_0.def10 (X := RELAT_1.rng (swapDom f)) (Y := RELAT_1.rng f)).mpr
  refine ⟨th41 hf, ?_⟩
  intro y hy
  obtain ⟨x, hx, heq⟩ := (FUNCT_1.def3 hf.2).mp hy
  obtain ⟨x1, y1, _, _, hxeq⟩ := ZFMISC_1.th84 h hx
  have hx' : TARSKI.pair x1 y1 ∈ RELAT_1.dom f :=
    Eq.subst (motive := fun s => s ∈ RELAT_1.dom f) hxeq hx
  have hswap : TARSKI.pair y1 x1 ∈ RELAT_1.dom (swapDom f) :=
    (th42 f x1 y1).mp hx'
  have happ : FUNCT_1.apply (swapDom f) (TARSKI.pair y1 x1) =
      FUNCT_1.apply f (TARSKI.pair x1 y1) := (def2 f).2 x1 y1 hx'
  exact (FUNCT_1.def3 (swapDom_isFunction f).2).mpr
    ⟨TARSKI.pair y1 x1, hswap,
      heq.trans ((congrArg (FUNCT_1.apply f) hxeq).trans happ.symm)⟩

/-- `FUNCT_4:48` -/
theorem th48 {f X Y Z : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f (ZFMISC_1.product X Y) Z) :
    PARTFUN1.isPartFunc (swapDom f) (ZFMISC_1.product Y X) Z := by
  have hd0 : RELAT_1.dom f ⊆ ZFMISC_1.product X Y :=
    RELSET_1.relationOf_defined hf.2
  have hd : RELAT_1.dom (swapDom f) ⊆ ZFMISC_1.product Y X := th45 hd0
  have hr : RELAT_1.rng (swapDom f) ⊆ Z :=
    Eq.subst (motive := fun s => s ⊆ Z) (th47 hf.1 hd0).symm
      (RELSET_1.relationOf_valued hf.2)
  exact PARTFUN1.partFunc_of (swapDom_isFunction f) hd hr

/-- `FUNCT_4:49` (`Th49`) -/
theorem th49 {f X Y Z : TarskiSet.{u}} (hZ : Z ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f (ZFMISC_1.product X Y) Z) :
    FUNCT_2.isFunctionOf (swapDom f) (ZFMISC_1.product Y X) Z := by
  have hdom : RELAT_1.dom f = ZFMISC_1.product X Y :=
    FUNCT_2.functionOf_dom_eq hf hZ
  have hpf := th48 (f := f) (X := X) (Y := Y) (Z := Z) hf.1
  refine ⟨hpf, ?_⟩
  constructor
  · intro _
    exact th46 hdom
  · intro hZe
    exact (hZ hZe).elim

/-- `FUNCT_4:50` -/
theorem th50 {f X Y D : TarskiSet.{u}} (hD : D ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f (ZFMISC_1.product X Y) D) :
    FUNCT_2.isFunctionOf (swapDom f) (ZFMISC_1.product Y X) D :=
  th49 hD hf

/-- `FUNCT_4:51` (`Th51`) -/
theorem th51 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    swapDom (swapDom f) ⊆ f := by
  refine (GRFUNC_1.th2 (swapDom_isFunction (swapDom f)) hf).mpr ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨y, z, heq, hdom⟩ := ((def2 (swapDom f)).1 x).mp hx
    have hdom' : TARSKI.pair z y ∈ RELAT_1.dom f := (th42 f z y).mpr hdom
    exact Eq.subst (motive := fun s => s ∈ RELAT_1.dom f) heq.symm hdom'
  · intro x hx
    obtain ⟨y, z, heq, hdom⟩ := ((def2 (swapDom f)).1 x).mp hx
    have hdomyz : TARSKI.pair z y ∈ RELAT_1.dom f := (th42 f z y).mpr hdom
    have happ := (def2 (swapDom f)).2 y z hdom
    have happ2 := (def2 f).2 z y hdomyz
    exact
      Eq.subst (motive := fun s =>
          FUNCT_1.apply (swapDom (swapDom f)) s =
            FUNCT_1.apply f s) heq.symm
        (happ.trans happ2)

/-- `FUNCT_4:52` (`Th52`) -/
theorem th52 {f X Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (h : RELAT_1.dom f ⊆ ZFMISC_1.product X Y) :
    swapDom (swapDom f) = f := by
  have hsub := th51 hf
  have hd : RELAT_1.dom (swapDom (swapDom f)) = RELAT_1.dom f := by
    apply eq_of_mem
    intro x
    constructor
    · intro hx
      exact ((GRFUNC_1.th2 (swapDom_isFunction (swapDom f)) hf).mp hsub).1 _ hx
    · intro hx
      obtain ⟨x1, y1, _, _, hxeq⟩ := ZFMISC_1.th84 h hx
      have hx' : TARSKI.pair x1 y1 ∈ RELAT_1.dom f :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.dom f) hxeq hx
      have hswap : TARSKI.pair y1 x1 ∈ RELAT_1.dom (swapDom f) :=
        (th42 f x1 y1).mp hx'
      have hss : TARSKI.pair x1 y1 ∈ RELAT_1.dom (swapDom (swapDom f)) :=
        (th42 (swapDom f) y1 x1).mp hswap
      exact Eq.subst (motive := fun s => s ∈ RELAT_1.dom (swapDom (swapDom f)))
        hxeq.symm hss
  exact GRFUNC_1.th3 (swapDom_isFunction (swapDom f)) hf hd hsub

/-- `FUNCT_4:53` — `~~f = f` for PartFunc of `[:X,Y:]`,`Z`. -/
theorem th53 {f X Y Z : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f (ZFMISC_1.product X Y) Z) :
    swapDom (swapDom f) = f :=
  th52 hf.1 (RELSET_1.relationOf_defined hf.2)

/-! ## `|：f,g：|` (`FUNCT_4:def 3`) — product of binary functions (`productPair`) -/

private def productPairPred (f g z v : TarskiSet.{u}) : Prop :=
  ∃ x y x9 y9,
    z = TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∧
    v = TARSKI.pair (FUNCT_1.apply f (TARSKI.pair x y))
      (FUNCT_1.apply g (TARSKI.pair x9 y9))

private noncomputable def productPairDomain (f g : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (XBOOLE_0.sch_separation
    (ZFMISC_1.product
      (ZFMISC_1.product
        (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
        (TARSKI.union (TARSKI.union (RELAT_1.dom g))))
      (ZFMISC_1.product
        (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
        (TARSKI.union (TARSKI.union (RELAT_1.dom g)))))
    (fun z => ∃ x y x9 y9,
      z = TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∧
      TARSKI.pair x y ∈ RELAT_1.dom f ∧
      TARSKI.pair x9 y9 ∈ RELAT_1.dom g))

private theorem productPairDomain_spec (f g : TarskiSet.{u}) :
    ∀ z, z ∈ productPairDomain f g ↔
      z ∈ ZFMISC_1.product
        (ZFMISC_1.product
          (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
          (TARSKI.union (TARSKI.union (RELAT_1.dom g))))
        (ZFMISC_1.product
          (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
          (TARSKI.union (TARSKI.union (RELAT_1.dom g)))) ∧
      ∃ x y x9 y9,
        z = TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∧
        TARSKI.pair x y ∈ RELAT_1.dom f ∧
        TARSKI.pair x9 y9 ∈ RELAT_1.dom g :=
  Classical.choose_spec (XBOOLE_0.sch_separation
    (ZFMISC_1.product
      (ZFMISC_1.product
        (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
        (TARSKI.union (TARSKI.union (RELAT_1.dom g))))
      (ZFMISC_1.product
        (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
        (TARSKI.union (TARSKI.union (RELAT_1.dom g)))))
    (fun z => ∃ x y x9 y9,
      z = TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∧
      TARSKI.pair x y ∈ RELAT_1.dom f ∧
      TARSKI.pair x9 y9 ∈ RELAT_1.dom g))

private theorem productPair_exists (f g : TarskiSet.{u}) :
    ∃ h, FUNCT_1.isFunction h ∧ RELAT_1.dom h = productPairDomain f g ∧
      ∀ z, z ∈ productPairDomain f g →
        productPairPred f g z (FUNCT_1.apply h z) := by
  refine FUNCT_1.sch_FuncEx (productPairDomain f g) (productPairPred f g) ?_ ?_
  · intro z v1 v2 _hz hp1 hp2
    obtain ⟨x, y, x9, y9, heq, hv1⟩ := hp1
    obtain ⟨x1, y1, x19, y19, heq2, hv2⟩ := hp2
    have ⟨hx, hy, hx9, hy9⟩ := lm1 (heq.symm.trans heq2)
    have hxy : TARSKI.pair x y = TARSKI.pair x1 y1 :=
      (congrArg (fun s => TARSKI.pair s y) hx).trans (congrArg (TARSKI.pair x1) hy)
    have hx9y9 : TARSKI.pair x9 y9 = TARSKI.pair x19 y19 :=
      (congrArg (fun s => TARSKI.pair s y9) hx9).trans
        (congrArg (TARSKI.pair x19) hy9)
    exact hv1.trans
      ((congr_pair (congrArg (FUNCT_1.apply f) hxy)
          (congrArg (FUNCT_1.apply g) hx9y9)).trans hv2.symm)
  · intro z hz
    obtain ⟨_, hex⟩ := (productPairDomain_spec f g z).mp hz
    obtain ⟨x, y, x9, y9, heq, _, _⟩ := hex
    exact ⟨TARSKI.pair (FUNCT_1.apply f (TARSKI.pair x y))
        (FUNCT_1.apply g (TARSKI.pair x9 y9)), x, y, x9, y9, heq, rfl⟩

/-- `FUNCT_4:def 3` — `|：f,g：|`. -/
noncomputable def productPair (f g : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (productPair_exists f g)

theorem productPair_isFunction (f g : TarskiSet.{u}) :
    FUNCT_1.isFunction (productPair f g) :=
  (Classical.choose_spec (productPair_exists f g)).1

private theorem productPair_dom_eq (f g : TarskiSet.{u}) :
    RELAT_1.dom (productPair f g) = productPairDomain f g :=
  (Classical.choose_spec (productPair_exists f g)).2.1

private theorem productPair_apply_pred {f g z : TarskiSet.{u}}
    (hz : z ∈ RELAT_1.dom (productPair f g)) :
    productPairPred f g z (FUNCT_1.apply (productPair f g) z) :=
  (Classical.choose_spec (productPair_exists f g)).2.2 z
    (Eq.subst (motive := fun s => z ∈ s) (productPair_dom_eq f g) hz)

/-- `FUNCT_4:def 3` characterization. -/
theorem def3 (f g : TarskiSet.{u}) :
    (∀ z, z ∈ RELAT_1.dom (productPair f g) ↔
      ∃ x y x9 y9,
        z = TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∧
        TARSKI.pair x y ∈ RELAT_1.dom f ∧
        TARSKI.pair x9 y9 ∈ RELAT_1.dom g) ∧
    ∀ x y x9 y9,
      TARSKI.pair x y ∈ RELAT_1.dom f →
      TARSKI.pair x9 y9 ∈ RELAT_1.dom g →
        FUNCT_1.apply (productPair f g)
            (TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9)) =
          TARSKI.pair (FUNCT_1.apply f (TARSKI.pair x y))
            (FUNCT_1.apply g (TARSKI.pair x9 y9)) := by
  constructor
  · intro z
    constructor
    · intro hz
      have hzD : z ∈ productPairDomain f g :=
        Eq.subst (motive := fun s => z ∈ s) (productPair_dom_eq f g) hz
      exact ((productPairDomain_spec f g z).mp hzD).2
    · intro ⟨x, y, x9, y9, heq, hf, hg⟩
      have hxU := (ZFMISC_1.th134 hf).1
      have hyU := (ZFMISC_1.th134 hf).2
      have hx9U := (ZFMISC_1.th134 hg).1
      have hy9U := (ZFMISC_1.th134 hg).2
      have hxx9 : TARSKI.pair x x9 ∈
          ZFMISC_1.product (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
            (TARSKI.union (TARSKI.union (RELAT_1.dom g))) :=
        (ZFMISC_1.th87).mpr ⟨hxU, hx9U⟩
      have hyy9 : TARSKI.pair y y9 ∈
          ZFMISC_1.product (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
            (TARSKI.union (TARSKI.union (RELAT_1.dom g))) :=
        (ZFMISC_1.th87).mpr ⟨hyU, hy9U⟩
      have hzP : TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∈
          ZFMISC_1.product
            (ZFMISC_1.product
              (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
              (TARSKI.union (TARSKI.union (RELAT_1.dom g))))
            (ZFMISC_1.product
              (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
              (TARSKI.union (TARSKI.union (RELAT_1.dom g)))) :=
        (ZFMISC_1.th87).mpr ⟨hxx9, hyy9⟩
      have hzD : TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∈
          productPairDomain f g :=
        (productPairDomain_spec f g _).mpr
          ⟨hzP, x, y, x9, y9, rfl, hf, hg⟩
      exact Eq.subst (motive := fun s => s ∈ RELAT_1.dom (productPair f g))
        heq.symm (Eq.subst (motive := fun s =>
            TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∈ s)
          (productPair_dom_eq f g).symm hzD)
  · intro x y x9 y9 hf hg
    have hxU := (ZFMISC_1.th134 hf).1
    have hyU := (ZFMISC_1.th134 hf).2
    have hx9U := (ZFMISC_1.th134 hg).1
    have hy9U := (ZFMISC_1.th134 hg).2
    have hxx9 : TARSKI.pair x x9 ∈
        ZFMISC_1.product (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
          (TARSKI.union (TARSKI.union (RELAT_1.dom g))) :=
      (ZFMISC_1.th87).mpr ⟨hxU, hx9U⟩
    have hyy9 : TARSKI.pair y y9 ∈
        ZFMISC_1.product (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
          (TARSKI.union (TARSKI.union (RELAT_1.dom g))) :=
      (ZFMISC_1.th87).mpr ⟨hyU, hy9U⟩
    have hzP : TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∈
        ZFMISC_1.product
          (ZFMISC_1.product
            (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
            (TARSKI.union (TARSKI.union (RELAT_1.dom g))))
          (ZFMISC_1.product
            (TARSKI.union (TARSKI.union (RELAT_1.dom f)))
            (TARSKI.union (TARSKI.union (RELAT_1.dom g)))) :=
      (ZFMISC_1.th87).mpr ⟨hxx9, hyy9⟩
    have hzD : TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∈
        productPairDomain f g :=
      (productPairDomain_spec f g _).mpr ⟨hzP, x, y, x9, y9, rfl, hf, hg⟩
    have hz : TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∈
        RELAT_1.dom (productPair f g) :=
      Eq.subst (motive := fun s =>
          TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∈ s)
        (productPair_dom_eq f g).symm hzD
    obtain ⟨x1, y1, x19, y19, heq, hv⟩ := productPair_apply_pred hz
    have ⟨hx, hy, hx9, hy9⟩ := lm1 heq
    have hxy : TARSKI.pair x y = TARSKI.pair x1 y1 :=
      (congrArg (fun s => TARSKI.pair s y) hx).trans (congrArg (TARSKI.pair x1) hy)
    have hx9y9 : TARSKI.pair x9 y9 = TARSKI.pair x19 y19 :=
      (congrArg (fun s => TARSKI.pair s y9) hx9).trans
        (congrArg (TARSKI.pair x19) hy9)
    exact hv.trans (congr_pair
      (congrArg (FUNCT_1.apply f) hxy.symm)
      (congrArg (FUNCT_1.apply g) hx9y9.symm))

/-- `FUNCT_4:54` (`Th54`) -/
theorem th54 (f g x x9 y y9 : TarskiSet.{u}) :
    TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∈
        RELAT_1.dom (productPair f g) ↔
      TARSKI.pair x y ∈ RELAT_1.dom f ∧
        TARSKI.pair x9 y9 ∈ RELAT_1.dom g := by
  constructor
  · intro hz
    obtain ⟨x1, y1, x19, y19, heq, hf, hg⟩ := ((def3 f g).1 _).mp hz
    have ⟨hx, hy, hx9, hy9⟩ := lm1 heq
    have hxy : TARSKI.pair x y = TARSKI.pair x1 y1 :=
      (congrArg (fun s => TARSKI.pair s y) hx).trans (congrArg (TARSKI.pair x1) hy)
    have hx9y9 : TARSKI.pair x9 y9 = TARSKI.pair x19 y19 :=
      (congrArg (fun s => TARSKI.pair s y9) hx9).trans
        (congrArg (TARSKI.pair x19) hy9)
    exact ⟨Eq.subst (motive := fun s => s ∈ RELAT_1.dom f) hxy.symm hf,
      Eq.subst (motive := fun s => s ∈ RELAT_1.dom g) hx9y9.symm hg⟩
  · intro ⟨hf, hg⟩
    exact ((def3 f g).1 _).mpr ⟨x, y, x9, y9, rfl, hf, hg⟩

/-- `FUNCT_4:55` -/
theorem th55 {f g x x9 y y9 : TarskiSet.{u}}
    (hz : TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∈
      RELAT_1.dom (productPair f g)) :
    FUNCT_1.apply (productPair f g)
        (TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9)) =
      TARSKI.pair (FUNCT_1.apply f (TARSKI.pair x y))
        (FUNCT_1.apply g (TARSKI.pair x9 y9)) := by
  have ⟨hf, hg⟩ := (th54 f g x x9 y y9).mp hz
  exact (def3 f g).2 x y x9 y9 hf hg

/-- `FUNCT_4:56` (`Th56`) -/
theorem th56 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    RELAT_1.rng (productPair f g) ⊆
      ZFMISC_1.product (RELAT_1.rng f) (RELAT_1.rng g) := by
  intro z hz
  obtain ⟨p, hp, heq⟩ := (FUNCT_1.def3 (productPair_isFunction f g).2).mp hz
  obtain ⟨x, y, x9, y9, hpEq, hfd, hgd⟩ := ((def3 f g).1 p).mp hp
  have happ : FUNCT_1.apply (productPair f g) p =
      TARSKI.pair (FUNCT_1.apply f (TARSKI.pair x y))
        (FUNCT_1.apply g (TARSKI.pair x9 y9)) :=
    Eq.subst (motive := fun s =>
        FUNCT_1.apply (productPair f g) s =
          TARSKI.pair (FUNCT_1.apply f (TARSKI.pair x y))
            (FUNCT_1.apply g (TARSKI.pair x9 y9))) hpEq.symm
      ((def3 f g).2 x y x9 y9 hfd hgd)
  have hfr : FUNCT_1.apply f (TARSKI.pair x y) ∈ RELAT_1.rng f :=
    FUNCT_1.th3 hf.2 hfd
  have hgr : FUNCT_1.apply g (TARSKI.pair x9 y9) ∈ RELAT_1.rng g :=
    FUNCT_1.th3 hg.2 hgd
  exact Eq.subst (motive := fun s => s ∈
      ZFMISC_1.product (RELAT_1.rng f) (RELAT_1.rng g))
    (heq.trans happ).symm ((ZFMISC_1.th87).mpr ⟨hfr, hgr⟩)

/-- `FUNCT_4:57` (`Th57`) -/
theorem th57 {f g X Y X9 Y9 : TarskiSet.{u}}
    (hf : RELAT_1.dom f ⊆ ZFMISC_1.product X Y)
    (hg : RELAT_1.dom g ⊆ ZFMISC_1.product X9 Y9) :
    RELAT_1.dom (productPair f g) ⊆
      ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9) := by
  intro xy hxy
  obtain ⟨x, y, x9, y9, heq, hfd, hgd⟩ := ((def3 f g).1 xy).mp hxy
  have ⟨hx, hy⟩ := (ZFMISC_1.th87).mp (hf _ hfd)
  have ⟨hx9, hy9⟩ := (ZFMISC_1.th87).mp (hg _ hgd)
  have hxx9 : TARSKI.pair x x9 ∈ ZFMISC_1.product X X9 :=
    (ZFMISC_1.th87).mpr ⟨hx, hx9⟩
  have hyy9 : TARSKI.pair y y9 ∈ ZFMISC_1.product Y Y9 :=
    (ZFMISC_1.th87).mpr ⟨hy, hy9⟩
  exact Eq.subst (motive := fun s => s ∈
      ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9))
    heq.symm ((ZFMISC_1.th87).mpr ⟨hxx9, hyy9⟩)

/-- `FUNCT_4:58` (`Th58`) -/
theorem th58 {f g X Y X9 Y9 : TarskiSet.{u}}
    (hf : RELAT_1.dom f = ZFMISC_1.product X Y)
    (hg : RELAT_1.dom g = ZFMISC_1.product X9 Y9) :
    RELAT_1.dom (productPair f g) =
      ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9) := by
  apply (XBOOLE_0.def10
    (X := RELAT_1.dom (productPair f g))
    (Y := ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9))).mpr
  refine ⟨th57 (fun z h => Eq.subst (motive := fun s => z ∈ s) hf h)
      (fun z h => Eq.subst (motive := fun s => z ∈ s) hg h), ?_⟩
  intro z hz
  obtain ⟨xx, yy, hxx, hyy, heq⟩ := (ZFMISC_1.def2 _ _ z).mp hz
  obtain ⟨y, y9, hy, hy9, hyyEq⟩ := (ZFMISC_1.def2 Y Y9 yy).mp hyy
  obtain ⟨x, x9, hx, hx9, hxxEq⟩ := (ZFMISC_1.def2 X X9 xx).mp hxx
  have hfd : TARSKI.pair x y ∈ RELAT_1.dom f :=
    Eq.subst (motive := fun s => TARSKI.pair x y ∈ s) hf.symm
      ((ZFMISC_1.th87).mpr ⟨hx, hy⟩)
  have hgd : TARSKI.pair x9 y9 ∈ RELAT_1.dom g :=
    Eq.subst (motive := fun s => TARSKI.pair x9 y9 ∈ s) hg.symm
      ((ZFMISC_1.th87).mpr ⟨hx9, hy9⟩)
  have hz' : TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) ∈
      RELAT_1.dom (productPair f g) :=
    ((def3 f g).1 _).mpr ⟨x, y, x9, y9, rfl, hfd, hgd⟩
  have heq' : z = TARSKI.pair (TARSKI.pair x x9) (TARSKI.pair y y9) :=
    heq.trans (congr_pair hxxEq hyyEq)
  exact Eq.subst (motive := fun s => s ∈ RELAT_1.dom (productPair f g))
    heq'.symm hz'

/-- `FUNCT_4:59` -/
theorem th59 {f g X Y Z X9 Y9 Z9 : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f (ZFMISC_1.product X Y) Z)
    (hg : PARTFUN1.isPartFunc g (ZFMISC_1.product X9 Y9) Z9) :
    PARTFUN1.isPartFunc (productPair f g)
      (ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9))
      (ZFMISC_1.product Z Z9) := by
  have hrng : RELAT_1.rng (productPair f g) ⊆
      ZFMISC_1.product (RELAT_1.rng f) (RELAT_1.rng g) := th56 hf.1 hg.1
  have hrng' : RELAT_1.rng (productPair f g) ⊆ ZFMISC_1.product Z Z9 :=
    XBOOLE_1.th1 hrng (ZFMISC_1.th96 (RELSET_1.relationOf_valued hf.2)
      (RELSET_1.relationOf_valued hg.2))
  have hdom : RELAT_1.dom (productPair f g) ⊆
      ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9) :=
    th57 (RELSET_1.relationOf_defined hf.2) (RELSET_1.relationOf_defined hg.2)
  exact PARTFUN1.partFunc_of (productPair_isFunction f g) hdom hrng'

/-- `FUNCT_4:60` (`Th60`) -/
theorem th60 {f g X Y Z X9 Y9 Z9 : TarskiSet.{u}}
    (hZ : Z ≠ (∅ : TarskiSet.{u})) (hZ9 : Z9 ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f (ZFMISC_1.product X Y) Z)
    (hg : FUNCT_2.isFunctionOf g (ZFMISC_1.product X9 Y9) Z9) :
    FUNCT_2.isFunctionOf (productPair f g)
      (ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9))
      (ZFMISC_1.product Z Z9) := by
  have hrng : RELAT_1.rng (productPair f g) ⊆ ZFMISC_1.product Z Z9 :=
    XBOOLE_1.th1 (th56 (FUNCT_2.functionOf_isFunction hf)
        (FUNCT_2.functionOf_isFunction hg))
      (ZFMISC_1.th96 (FUNCT_2.functionOf_rng_sub hf)
        (FUNCT_2.functionOf_rng_sub hg))
  have hdom : RELAT_1.dom (productPair f g) =
      ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9) :=
    th58 (FUNCT_2.functionOf_dom_eq hf hZ) (FUNCT_2.functionOf_dom_eq hg hZ9)
  exact FUNCT_2.functionOf_of (productPair_isFunction f g) hdom hrng

/-- `FUNCT_4:61` — Mizar reserve makes `D`,`D9` nonempty; Lean states the general form. -/
theorem th61 {f g X Y D X9 Y9 D9 : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f (ZFMISC_1.product X Y) D)
    (hg : FUNCT_2.isFunctionOf g (ZFMISC_1.product X9 Y9) D9) :
    FUNCT_2.isFunctionOf (productPair f g)
      (ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9))
      (ZFMISC_1.product D D9) := by
  have := Classical.propDecidable (D = (∅ : TarskiSet.{u}))
  by_cases hD : D = (∅ : TarskiSet.{u})
  · have hf0 := FUNCT_2.functionOf_empty_cod hf hD
    have hprod : ZFMISC_1.product D D9 = (∅ : TarskiSet.{u}) :=
      (ZFMISC_1.th90 (X := D) (Y := D9)).mpr (Or.inl hD)
    have hdomf : RELAT_1.dom f = (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u})) hf0.symm
        RELAT_1.th38.1
    have hdomPP : RELAT_1.dom (productPair f g) = (∅ : TarskiSet.{u}) := by
      apply (XBOOLE_0.def10 (X := RELAT_1.dom (productPair f g))
        (Y := (∅ : TarskiSet.{u}))).mpr
      refine ⟨fun z hz => ?_, XBOOLE_1.th2⟩
      obtain ⟨x, y, x9, y9, _, hfd, _⟩ := ((def3 f g).1 z).mp hz
      exact ((XBOOLE_0.empty_iff (TARSKI.pair x y)).mp
        (Eq.subst (motive := fun s => TARSKI.pair x y ∈ s) hdomf hfd)).elim
    have hpp0 : productPair f g = (∅ : TarskiSet.{u}) :=
      RELAT_1.th41 (productPair_isFunction f g).1 (Or.inl hdomPP)
    exact Eq.subst (motive := fun s => FUNCT_2.isFunctionOf s
        (ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9))
        (ZFMISC_1.product D D9)) hpp0.symm
      (Eq.subst (motive := fun s => FUNCT_2.isFunctionOf (∅ : TarskiSet.{u})
          (ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9)) s)
        hprod.symm
        (FUNCT_2.empty_isFunctionOf
          (ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9))))
  · have := Classical.propDecidable (D9 = (∅ : TarskiSet.{u}))
    by_cases hD9 : D9 = (∅ : TarskiSet.{u})
    · have hg0 := FUNCT_2.functionOf_empty_cod hg hD9
      have hprod : ZFMISC_1.product D D9 = (∅ : TarskiSet.{u}) :=
        (ZFMISC_1.th90 (X := D) (Y := D9)).mpr (Or.inr hD9)
      have hdomg : RELAT_1.dom g = (∅ : TarskiSet.{u}) :=
        Eq.subst (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u})) hg0.symm
          RELAT_1.th38.1
      have hdomPP : RELAT_1.dom (productPair f g) = (∅ : TarskiSet.{u}) := by
        apply (XBOOLE_0.def10 (X := RELAT_1.dom (productPair f g))
          (Y := (∅ : TarskiSet.{u}))).mpr
        refine ⟨fun z hz => ?_, XBOOLE_1.th2⟩
        obtain ⟨x, y, x9, y9, _, _, hgd⟩ := ((def3 f g).1 z).mp hz
        exact ((XBOOLE_0.empty_iff (TARSKI.pair x9 y9)).mp
          (Eq.subst (motive := fun s => TARSKI.pair x9 y9 ∈ s) hdomg hgd)).elim
      have hpp0 : productPair f g = (∅ : TarskiSet.{u}) :=
        RELAT_1.th41 (productPair_isFunction f g).1 (Or.inl hdomPP)
      exact Eq.subst (motive := fun s => FUNCT_2.isFunctionOf s
          (ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9))
          (ZFMISC_1.product D D9)) hpp0.symm
        (Eq.subst (motive := fun s => FUNCT_2.isFunctionOf (∅ : TarskiSet.{u})
            (ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9)) s)
          hprod.symm
          (FUNCT_2.empty_isFunctionOf
            (ZFMISC_1.product (ZFMISC_1.product X X9) (ZFMISC_1.product Y Y9))))
    · exact th60 hD hD9 hf hg

/-! ## `(x,y)-->(a,b)` (`FUNCT_4:def 4`) — `pairMapsTo` -/

/-- `FUNCT_4:def 4` — `(x,y) --> (a,b)`. -/
noncomputable def pairMapsTo (x y a b : TarskiSet.{u}) : TarskiSet.{u} :=
  override (FUNCOP_1.dotArrow x a) (FUNCOP_1.dotArrow y b)

theorem pairMapsTo_isFunction (x y a b : TarskiSet.{u}) :
    FUNCT_1.isFunction (pairMapsTo x y a b) :=
  override_isFunction _ _

private theorem upair_eq_sing_union (x1 x2 : TarskiSet.{u}) :
    TARSKI.upair x1 x2 = TARSKI.singleton x1 ∪ TARSKI.singleton x2 :=
  ENUMSET1.th1

/-- `FUNCT_4:62` (`Th62`) -/
theorem th62 (x1 x2 y1 y2 : TarskiSet.{u}) :
    RELAT_1.dom (pairMapsTo x1 x2 y1 y2) = TARSKI.upair x1 x2 ∧
      RELAT_1.rng (pairMapsTo x1 x2 y1 y2) ⊆ TARSKI.upair y1 y2 := by
  have hd : RELAT_1.dom (pairMapsTo x1 x2 y1 y2) =
      RELAT_1.dom (FUNCOP_1.dotArrow x1 y1) ∪
        RELAT_1.dom (FUNCOP_1.dotArrow x2 y2) :=
    override_dom _ _
  have hd1 : RELAT_1.dom (FUNCOP_1.dotArrow x1 y1) = TARSKI.singleton x1 :=
    FUNCOP_1.mapsTo_dom (TARSKI.singleton x1) y1
  have hd2 : RELAT_1.dom (FUNCOP_1.dotArrow x2 y2) = TARSKI.singleton x2 :=
    FUNCOP_1.mapsTo_dom (TARSKI.singleton x2) y2
  have hdom : RELAT_1.dom (pairMapsTo x1 x2 y1 y2) = TARSKI.upair x1 x2 :=
    hd.trans ((congr_union hd1 hd2).trans (upair_eq_sing_union x1 x2).symm)
  have hrng : RELAT_1.rng (pairMapsTo x1 x2 y1 y2) ⊆
      RELAT_1.rng (FUNCOP_1.dotArrow x1 y1) ∪
        RELAT_1.rng (FUNCOP_1.dotArrow x2 y2) :=
    th17 (FUNCOP_1.dotArrow_isFunction x1 y1) (FUNCOP_1.dotArrow_isFunction x2 y2)
  have hr1 := (FUNCOP_1.th13 (TARSKI.singleton x1) y1).2
  have hr2 := (FUNCOP_1.th13 (TARSKI.singleton x2) y2).2
  have hrU : RELAT_1.rng (FUNCOP_1.dotArrow x1 y1) ∪
      RELAT_1.rng (FUNCOP_1.dotArrow x2 y2) ⊆
      TARSKI.singleton y1 ∪ TARSKI.singleton y2 :=
    XBOOLE_1.th13 hr1 hr2
  exact ⟨hdom, XBOOLE_1.th1 hrng
    (Eq.subst (motive := fun s =>
        RELAT_1.rng (FUNCOP_1.dotArrow x1 y1) ∪
          RELAT_1.rng (FUNCOP_1.dotArrow x2 y2) ⊆ s)
      (upair_eq_sing_union y1 y2).symm hrU)⟩

/-- `FUNCT_4:63` (`Th63`) -/
theorem th63 (x1 x2 y1 y2 : TarskiSet.{u}) :
    (x1 ≠ x2 → FUNCT_1.apply (pairMapsTo x1 x2 y1 y2) x1 = y1) ∧
      FUNCT_1.apply (pairMapsTo x1 x2 y1 y2) x2 = y2 := by
  have hx2 : x2 ∈ TARSKI.singleton x2 := (TARSKI.def1 x2 x2).mpr rfl
  have hx1 : x1 ∈ TARSKI.singleton x1 := (TARSKI.def1 x1 x1).mpr rfl
  have hd2 : RELAT_1.dom (FUNCOP_1.dotArrow x2 y2) = TARSKI.singleton x2 :=
    FUNCOP_1.mapsTo_dom (TARSKI.singleton x2) y2
  constructor
  · intro hne
    have hng : x1 ∉ RELAT_1.dom (FUNCOP_1.dotArrow x2 y2) := by
      intro hx
      have hxEq : x1 = x2 := (TARSKI.def1 x2 x1).mp
        (Eq.subst (motive := fun s => x1 ∈ s) hd2 hx)
      exact hne hxEq
    exact (th11 (f := FUNCOP_1.dotArrow x1 y1)
        (g := FUNCOP_1.dotArrow x2 y2) hng).trans (FUNCOP_1.th7 hx1)
  · have hx2d : x2 ∈ RELAT_1.dom (FUNCOP_1.dotArrow x2 y2) :=
      Eq.subst (motive := fun s => x2 ∈ s) hd2.symm hx2
    exact (th13 (f := FUNCOP_1.dotArrow x1 y1)
        (g := FUNCOP_1.dotArrow x2 y2) hx2d).trans (FUNCOP_1.th7 hx2)

/-- `FUNCT_4:64` -/
theorem th64 {x1 x2 y1 y2 : TarskiSet.{u}} (hne : x1 ≠ x2) :
    RELAT_1.rng (pairMapsTo x1 x2 y1 y2) = TARSKI.upair y1 y2 := by
  apply (XBOOLE_0.def10 (X := RELAT_1.rng (pairMapsTo x1 x2 y1 y2))
    (Y := TARSKI.upair y1 y2)).mpr
  refine ⟨(th62 x1 x2 y1 y2).2, ?_⟩
  intro y hy
  have hyOr : y = y1 ∨ y = y2 := (TARSKI.def2 y1 y2 y).mp hy
  have hd : RELAT_1.dom (pairMapsTo x1 x2 y1 y2) = TARSKI.upair x1 x2 :=
    (th62 x1 x2 y1 y2).1
  have hx1d : x1 ∈ RELAT_1.dom (pairMapsTo x1 x2 y1 y2) :=
    Eq.subst (motive := fun s => x1 ∈ s) hd.symm
      ((TARSKI.def2 x1 x2 x1).mpr (Or.inl rfl))
  have hx2d : x2 ∈ RELAT_1.dom (pairMapsTo x1 x2 y1 y2) :=
    Eq.subst (motive := fun s => x2 ∈ s) hd.symm
      ((TARSKI.def2 x1 x2 x2).mpr (Or.inr rfl))
  exact Or.elim hyOr
    (fun hy1 => (FUNCT_1.def3 (pairMapsTo_isFunction x1 x2 y1 y2).2).mpr
      ⟨x1, hx1d, hy1.trans ((th63 x1 x2 y1 y2).1 hne).symm⟩)
    (fun hy2 => (FUNCT_1.def3 (pairMapsTo_isFunction x1 x2 y1 y2).2).mpr
      ⟨x2, hx2d, hy2.trans (th63 x1 x2 y1 y2).2.symm⟩)

/-- `FUNCT_4:65` — `(x1,x2)-->(y,y) = {x1,x2} --> y`. -/
theorem th65 (x1 x2 y : TarskiSet.{u}) :
    pairMapsTo x1 x2 y y = FUNCOP_1.mapsTo (TARSKI.upair x1 x2) y := by
  have hdF : RELAT_1.dom (pairMapsTo x1 x2 y y) = TARSKI.upair x1 x2 :=
    (th62 x1 x2 y y).1
  have hdF9 : RELAT_1.dom (FUNCOP_1.mapsTo (TARSKI.upair x1 x2) y) =
      TARSKI.upair x1 x2 := FUNCOP_1.mapsTo_dom _ _
  have hd : RELAT_1.dom (pairMapsTo x1 x2 y y) =
      RELAT_1.dom (FUNCOP_1.mapsTo (TARSKI.upair x1 x2) y) :=
    hdF.trans hdF9.symm
  refine FUNCT_1.th2 (pairMapsTo_isFunction x1 x2 y y)
    (FUNCOP_1.mapsTo_isFunction _ _) hd ?_
  intro x hx
  have hxU : x ∈ TARSKI.upair x1 x2 :=
    Eq.subst (motive := fun s => x ∈ s) hdF hx
  have hright : FUNCT_1.apply (FUNCOP_1.mapsTo (TARSKI.upair x1 x2) y) x = y :=
    FUNCOP_1.th7 hxU
  have hd2 : RELAT_1.dom (FUNCOP_1.dotArrow x2 y) = TARSKI.singleton x2 :=
    FUNCOP_1.mapsTo_dom (TARSKI.singleton x2) y
  have hd1 : RELAT_1.dom (FUNCOP_1.dotArrow x1 y) = TARSKI.singleton x1 :=
    FUNCOP_1.mapsTo_dom (TARSKI.singleton x1) y
  exact Or.elim (Classical.em (x ∈ RELAT_1.dom (FUNCOP_1.dotArrow x2 y)))
    (fun hxg =>
      (th13 (f := FUNCOP_1.dotArrow x1 y) (g := FUNCOP_1.dotArrow x2 y) hxg).trans
        ((FUNCOP_1.th7 (Eq.subst (motive := fun s => x ∈ s) hd2 hxg)).trans
          hright.symm))
    (fun hngx =>
      have hx1d : x ∈ RELAT_1.dom (FUNCOP_1.dotArrow x1 y) :=
        Or.elim ((th12 (FUNCOP_1.dotArrow x1 y) (FUNCOP_1.dotArrow x2 y) x).mp hx)
          id (fun h => (hngx h).elim)
      (th11 (f := FUNCOP_1.dotArrow x1 y) (g := FUNCOP_1.dotArrow x2 y) hngx).trans
        ((FUNCOP_1.th7 (Eq.subst (motive := fun s => x ∈ s) hd1 hx1d)).trans
          hright.symm))

/-- Redefinition: `(x1,x2)-->(y1,y2)` is a function from
`{x1,x2}` to `A`. -/
theorem pairMapsTo_isFunctionOf {A x1 x2 y1 y2 : TarskiSet.{u}}
    (hy1 : y1 ∈ A) (hy2 : y2 ∈ A) :
    FUNCT_2.isFunctionOf (pairMapsTo x1 x2 y1 y2) (TARSKI.upair x1 x2) A := by
  have hrng : RELAT_1.rng (pairMapsTo x1 x2 y1 y2) ⊆ A :=
    XBOOLE_1.th1 (th62 x1 x2 y1 y2).2
      (fun y hy => Or.elim ((TARSKI.def2 y1 y2 y).mp hy)
        (fun h => Eq.subst (motive := fun s => s ∈ A) h.symm hy1)
        (fun h => Eq.subst (motive := fun s => s ∈ A) h.symm hy2))
  exact FUNCT_2.functionOf_of (pairMapsTo_isFunction x1 x2 y1 y2)
    (th62 x1 x2 y1 y2).1 hrng

/-- `FUNCT_4:66` — uniqueness from values on a two-point domain. -/
theorem th66 {a b c d g : TarskiSet.{u}} (hg : FUNCT_1.isFunction g)
    (hd : RELAT_1.dom g = TARSKI.upair a b)
    (ha : FUNCT_1.apply g a = c) (hb : FUNCT_1.apply g b = d) :
    g = pairMapsTo a b c d := by
  have hd1 : RELAT_1.dom (FUNCOP_1.dotArrow a c) = TARSKI.singleton a :=
    FUNCOP_1.mapsTo_dom _ _
  have hd2 : RELAT_1.dom (FUNCOP_1.dotArrow b d) = TARSKI.singleton b :=
    FUNCOP_1.mapsTo_dom _ _
  have hdomEq : RELAT_1.dom g =
      RELAT_1.dom (FUNCOP_1.dotArrow a c) ∪
        RELAT_1.dom (FUNCOP_1.dotArrow b d) :=
    hd.trans ((upair_eq_sing_union a b).trans (congr_union hd1.symm hd2.symm))
  have hv : ∀ x, x ∈ RELAT_1.dom (FUNCOP_1.dotArrow a c) ∪
      RELAT_1.dom (FUNCOP_1.dotArrow b d) →
      (x ∈ RELAT_1.dom (FUNCOP_1.dotArrow b d) →
        FUNCT_1.apply g x = FUNCT_1.apply (FUNCOP_1.dotArrow b d) x) ∧
      (x ∉ RELAT_1.dom (FUNCOP_1.dotArrow b d) →
        FUNCT_1.apply g x = FUNCT_1.apply (FUNCOP_1.dotArrow a c) x) := by
    intro x hxU
    constructor
    · intro hxg
      have hxEq : x = b := (TARSKI.def1 b x).mp
        (Eq.subst (motive := fun s => x ∈ s) hd2 hxg)
      exact Eq.subst (motive := fun s => FUNCT_1.apply g s =
          FUNCT_1.apply (FUNCOP_1.dotArrow b d) s) hxEq.symm
        (hb.trans (FUNCOP_1.th72 b d).symm)
    · intro hngx
      have hx1d : x ∈ RELAT_1.dom (FUNCOP_1.dotArrow a c) :=
        Or.elim ((XBOOLE_0.def3 _ _ _).mp hxU) id (fun h => (hngx h).elim)
      have hxEq : x = a := (TARSKI.def1 a x).mp
        (Eq.subst (motive := fun s => x ∈ s) hd1 hx1d)
      exact Eq.subst (motive := fun s => FUNCT_1.apply g s =
          FUNCT_1.apply (FUNCOP_1.dotArrow a c) s) hxEq.symm
        (ha.trans (FUNCOP_1.th72 a c).symm)
  exact override_unique hg (override_isFunction _ _) hdomEq hv
    (override_dom _ _) (fun x hx => (def1 _ _).2.2 x hx)

/-- `FUNCT_4:67` (`Th67`) — `(a,c)-->(b,d) = {[a,b],[c,d]}` when `a ≠ c`. -/
theorem th67 {a b c d : TarskiSet.{u}} (hne : a ≠ c) :
    pairMapsTo a c b d =
      TARSKI.upair (TARSKI.pair a b) (TARSKI.pair c d) := by
  have hd1 : RELAT_1.dom (FUNCOP_1.dotArrow a b) = TARSKI.singleton a :=
    FUNCOP_1.mapsTo_dom _ _
  have hd2 : RELAT_1.dom (FUNCOP_1.dotArrow c d) = TARSKI.singleton c :=
    FUNCOP_1.mapsTo_dom _ _
  have hmiss : XBOOLE_0.misses (RELAT_1.dom (FUNCOP_1.dotArrow a b))
      (RELAT_1.dom (FUNCOP_1.dotArrow c d)) := by
    apply (XBOOLE_0.def10
      (X := RELAT_1.dom (FUNCOP_1.dotArrow a b) ∩
        RELAT_1.dom (FUNCOP_1.dotArrow c d))
      (Y := (∅ : TarskiSet.{u}))).mpr
    refine ⟨fun x hx => ?_, XBOOLE_1.th2⟩
    have ⟨hx1, hx2⟩ := (XBOOLE_0.def4 _ _ _).mp hx
    have ha : x = a := (TARSKI.def1 a x).mp
      (Eq.subst (motive := fun s => x ∈ s) hd1 hx1)
    have hc : x = c := (TARSKI.def1 c x).mp
      (Eq.subst (motive := fun s => x ∈ s) hd2 hx2)
    exact (hne (ha.symm.trans hc)).elim
  have hfEq : FUNCOP_1.dotArrow a b = TARSKI.singleton (TARSKI.pair a b) :=
    (FUNCOP_1.dotArrow_eq a b).trans
      ((FUNCOP_1.def2 (TARSKI.singleton a) b).trans ZFMISC_1.th29)
  have hgEq : FUNCOP_1.dotArrow c d = TARSKI.singleton (TARSKI.pair c d) :=
    (FUNCOP_1.dotArrow_eq c d).trans
      ((FUNCOP_1.def2 (TARSKI.singleton c) d).trans ZFMISC_1.th29)
  have hover : pairMapsTo a c b d =
      FUNCOP_1.dotArrow a b ∪ FUNCOP_1.dotArrow c d :=
    (th31 (FUNCOP_1.dotArrow_isFunction a b) (FUNCOP_1.dotArrow_isFunction c d)
      hmiss).symm
  exact hover.trans
    ((congr_union hfEq hgEq).trans (upair_eq_sing_union _ _).symm)

/-- `FUNCT_4:68` -/
theorem th68 {a b x y x9 y9 : TarskiSet.{u}} (hne : a ≠ b)
    (heq : pairMapsTo a b x y = pairMapsTo a b x9 y9) :
    x = x9 ∧ y = y9 := by
  have hx : FUNCT_1.apply (pairMapsTo a b x y) a = x := (th63 a b x y).1 hne
  have hx9 : FUNCT_1.apply (pairMapsTo a b x9 y9) a = x9 :=
    (th63 a b x9 y9).1 hne
  have hy : FUNCT_1.apply (pairMapsTo a b x y) b = y := (th63 a b x y).2
  have hy9 : FUNCT_1.apply (pairMapsTo a b x9 y9) b = y9 :=
    (th63 a b x9 y9).2
  exact ⟨hx.symm.trans ((congrArg (fun s => FUNCT_1.apply s a) heq).trans hx9),
    hy.symm.trans ((congrArg (fun s => FUNCT_1.apply s b) heq).trans hy9)⟩

/-! ## Addenda -/

/-- `FUNCT_4:69` — from CIRCCOMB. -/
theorem th69 {f1 f2 g1 g2 : TarskiSet.{u}}
    (hf1 : FUNCT_1.isFunction f1) (hf2 : FUNCT_1.isFunction f2)
    (hg1 : FUNCT_1.isFunction g1) (hg2 : FUNCT_1.isFunction g2)
    (hr1 : RELAT_1.rng g1 ⊆ RELAT_1.dom f1)
    (hr2 : RELAT_1.rng g2 ⊆ RELAT_1.dom f2)
    (ht : PARTFUN1.tolerates f1 f2) :
    RELAT_1.comp (override g1 g2) (override f1 f2) =
      override (RELAT_1.comp g1 f1) (RELAT_1.comp g2 f2) := by
  have hrngO : RELAT_1.rng (override g1 g2) ⊆ RELAT_1.rng g1 ∪ RELAT_1.rng g2 :=
    th17 hg1 hg2
  have hdomO : RELAT_1.dom (override f1 f2) = RELAT_1.dom f1 ∪ RELAT_1.dom f2 :=
    override_dom f1 f2
  have hrngSub : RELAT_1.rng g1 ∪ RELAT_1.rng g2 ⊆
      RELAT_1.dom f1 ∪ RELAT_1.dom f2 := XBOOLE_1.th13 hr1 hr2
  have hrngSub' : RELAT_1.rng (override g1 g2) ⊆ RELAT_1.dom (override f1 f2) :=
    Eq.subst (motive := fun s => RELAT_1.rng (override g1 g2) ⊆ s) hdomO.symm
      (XBOOLE_1.th1 hrngO hrngSub)
  have hdL : RELAT_1.dom (RELAT_1.comp (override g1 g2) (override f1 f2)) =
      RELAT_1.dom (override g1 g2) := RELAT_1.th27 hrngSub'
  have hdL' : RELAT_1.dom (RELAT_1.comp (override g1 g2) (override f1 f2)) =
      RELAT_1.dom g1 ∪ RELAT_1.dom g2 := hdL.trans (override_dom g1 g2)
  have hd1 : RELAT_1.dom (RELAT_1.comp g1 f1) = RELAT_1.dom g1 := RELAT_1.th27 hr1
  have hd2 : RELAT_1.dom (RELAT_1.comp g2 f2) = RELAT_1.dom g2 := RELAT_1.th27 hr2
  have hdR : RELAT_1.dom (override (RELAT_1.comp g1 f1) (RELAT_1.comp g2 f2)) =
      RELAT_1.dom g1 ∪ RELAT_1.dom g2 :=
    (override_dom _ _).trans (congr_union hd1 hd2)
  refine FUNCT_1.th2
    (FUNCT_1.comp_isFunction (override_isFunction g1 g2) (override_isFunction f1 f2))
    (override_isFunction _ _) (hdL'.trans hdR.symm) ?_
  intro x hx
  have hxU : x ∈ RELAT_1.dom g1 ∪ RELAT_1.dom g2 :=
    Eq.subst (motive := fun s => x ∈ s) hdL' hx
  have happL : FUNCT_1.apply (RELAT_1.comp (override g1 g2) (override f1 f2)) x =
      FUNCT_1.apply (override f1 f2)
        (FUNCT_1.apply (override g1 g2) x) :=
    FUNCT_1.th12 (override_isFunction g1 g2).2 (override_isFunction f1 f2).2 hx
  exact Or.elim (Classical.em (x ∈ RELAT_1.dom g2))
    (fun hxg2 => by
      have hg2x : FUNCT_1.apply (override g1 g2) x = FUNCT_1.apply g2 x :=
        th13 (f := g1) (g := g2) hxg2
      have hxg2d : x ∈ RELAT_1.dom (RELAT_1.comp g2 f2) :=
        Eq.subst (motive := fun s => x ∈ s) hd2.symm hxg2
      have hR : FUNCT_1.apply
          (override (RELAT_1.comp g1 f1) (RELAT_1.comp g2 f2)) x =
          FUNCT_1.apply (RELAT_1.comp g2 f2) x :=
        th13 (f := RELAT_1.comp g1 f1) (g := RELAT_1.comp g2 f2) hxg2d
      have hcomp' : FUNCT_1.apply (RELAT_1.comp g2 f2) x =
          FUNCT_1.apply f2 (FUNCT_1.apply g2 x) :=
        FUNCT_1.th12 hg2.2 hf2.2 hxg2d
      have hg2d : FUNCT_1.apply g2 x ∈ RELAT_1.dom f2 :=
        hr2 _ (FUNCT_1.th3 hg2.2 hxg2)
      have hf2x : FUNCT_1.apply (override f1 f2) (FUNCT_1.apply g2 x) =
          FUNCT_1.apply f2 (FUNCT_1.apply g2 x) :=
        th13 (f := f1) (g := f2) hg2d
      have step1 := congrArg (FUNCT_1.apply (override f1 f2)) hg2x
      have step2 := hf2x
      have step3 := hcomp'.symm
      have step4 := hR.symm
      exact happL.trans (step1.trans (step2.trans (step3.trans step4))))
    (fun hngx2 => by
      have hxg1 : x ∈ RELAT_1.dom g1 :=
        Or.elim ((XBOOLE_0.def3 _ _ _).mp hxU) id (fun h => (hngx2 h).elim)
      have hg1x : FUNCT_1.apply (override g1 g2) x = FUNCT_1.apply g1 x :=
        th11 (f := g1) (g := g2) hngx2
      have hxg1d : x ∈ RELAT_1.dom (RELAT_1.comp g1 f1) :=
        Eq.subst (motive := fun s => x ∈ s) hd1.symm hxg1
      have hngx2c : x ∉ RELAT_1.dom (RELAT_1.comp g2 f2) :=
        fun h => hngx2 (Eq.subst (motive := fun s => x ∈ s) hd2 h)
      have hR : FUNCT_1.apply
          (override (RELAT_1.comp g1 f1) (RELAT_1.comp g2 f2)) x =
          FUNCT_1.apply (RELAT_1.comp g1 f1) x :=
        th11 (f := RELAT_1.comp g1 f1) (g := RELAT_1.comp g2 f2) hngx2c
      have hcomp' : FUNCT_1.apply (RELAT_1.comp g1 f1) x =
          FUNCT_1.apply f1 (FUNCT_1.apply g1 x) :=
        FUNCT_1.th12 hg1.2 hf1.2 hxg1d
      have hg1d : FUNCT_1.apply g1 x ∈ RELAT_1.dom f1 :=
        hr1 _ (FUNCT_1.th3 hg1.2 hxg1)
      have hf1x : FUNCT_1.apply (override f1 f2) (FUNCT_1.apply g1 x) =
          FUNCT_1.apply f1 (FUNCT_1.apply g1 x) :=
        Or.elim (Classical.em (FUNCT_1.apply g1 x ∈ RELAT_1.dom f2))
          (fun hin =>
            (th13 (f := f1) (g := f2) hin).trans
              (ht _ ((XBOOLE_0.def4 _ _ _).mpr ⟨hg1d, hin⟩)).symm)
          (fun hnin => th11 (f := f1) (g := f2) hnin)
      have step1 := congrArg (FUNCT_1.apply (override f1 f2)) hg1x
      have step2 := hf1x
      have step3 := hcomp'.symm
      have step4 := hR.symm
      exact happL.trans (step1.trans (step2.trans (step3.trans step4))))

/-- `FUNCT_4:70` (`Th70`) — `dom f ⊆ A ∪ B → f|A +* f|B = f`. -/
theorem th70 {f A B : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (h : RELAT_1.dom f ⊆ A ∪ B) :
    override (RELAT_1.restrict f A) (RELAT_1.restrict f B) = f := by
  have hdA : RELAT_1.dom (RELAT_1.restrict f A) = RELAT_1.dom f ∩ A := RELAT_1.th61
  have hdB : RELAT_1.dom (RELAT_1.restrict f B) = RELAT_1.dom f ∩ B := RELAT_1.th61
  have hdom : RELAT_1.dom f =
      RELAT_1.dom (RELAT_1.restrict f A) ∪ RELAT_1.dom (RELAT_1.restrict f B) :=
    (XBOOLE_1.th28 h).symm.trans
      ((XBOOLE_1.th23 (X := RELAT_1.dom f) (Y := A) (Z := B)).trans
        (congr_union hdA.symm hdB.symm))
  have hv : ∀ x, x ∈ RELAT_1.dom (RELAT_1.restrict f A) ∪
      RELAT_1.dom (RELAT_1.restrict f B) →
      (x ∈ RELAT_1.dom (RELAT_1.restrict f B) →
        FUNCT_1.apply f x = FUNCT_1.apply (RELAT_1.restrict f B) x) ∧
      (x ∉ RELAT_1.dom (RELAT_1.restrict f B) →
        FUNCT_1.apply f x = FUNCT_1.apply (RELAT_1.restrict f A) x) := by
    intro x hxU
    constructor
    · intro hxB
      exact (FUNCT_1.th47 hf.2 hxB).symm
    · intro hnxB
      have hxA : x ∈ RELAT_1.dom (RELAT_1.restrict f A) :=
        Or.elim ((XBOOLE_0.def3 _ _ _).mp hxU) id (fun h => (hnxB h).elim)
      exact (FUNCT_1.th47 hf.2 hxA).symm
  exact (override_unique hf (override_isFunction _ _) hdom hv
    (override_dom _ _) (fun x hx => (def1 _ _).2.2 x hx)).symm

/-- `FUNCT_4:71` (`Th71`) — `(p +* q)|A = p|A +* q|A`. -/
theorem th71 {p q A : TarskiSet.{u}} (hp : FUNCT_1.isFunction p)
    (hq : FUNCT_1.isFunction q) :
    RELAT_1.restrict (override p q) A =
      override (RELAT_1.restrict p A) (RELAT_1.restrict q A) := by
  let pA := RELAT_1.restrict p A
  let qA := RELAT_1.restrict q A
  let lhs := RELAT_1.restrict (override p q) A
  let rhs := override pA qA
  have hpA : FUNCT_1.isFunction pA := FUNCT_1.restrict_isFunction (X := A) hp
  have hqA : FUNCT_1.isFunction qA := FUNCT_1.restrict_isFunction (X := A) hq
  have hlhs : FUNCT_1.isFunction lhs :=
    FUNCT_1.restrict_isFunction (X := A) (override_isFunction p q)
  have hrhs : FUNCT_1.isFunction rhs := override_isFunction pA qA
  have hdL : RELAT_1.dom lhs = (RELAT_1.dom p ∪ RELAT_1.dom q) ∩ A :=
    (RELAT_1.th61 (R := override p q) (X := A)).trans
      (congrArg (fun s => s ∩ A) (override_dom p q))
  have hdistrib :
      (RELAT_1.dom p ∪ RELAT_1.dom q) ∩ A =
        (RELAT_1.dom p ∩ A) ∪ (RELAT_1.dom q ∩ A) :=
    (XBOOLE_0.inter_comm (RELAT_1.dom p ∪ RELAT_1.dom q) A).trans
      ((XBOOLE_1.th23 (X := A) (Y := RELAT_1.dom p) (Z := RELAT_1.dom q)).trans
        (congr_union (XBOOLE_0.inter_comm A (RELAT_1.dom p))
          (XBOOLE_0.inter_comm A (RELAT_1.dom q))))
  have hdR : RELAT_1.dom rhs = (RELAT_1.dom p ∩ A) ∪ (RELAT_1.dom q ∩ A) :=
    (override_dom pA qA).trans (congr_union RELAT_1.th61 RELAT_1.th61)
  have hdom : RELAT_1.dom lhs = RELAT_1.dom rhs :=
    hdL.trans (hdistrib.trans hdR.symm)
  refine FUNCT_1.th2 hlhs hrhs hdom ?_
  intro x hx
  have hxR : x ∈ RELAT_1.dom rhs :=
    Eq.subst (motive := fun s => x ∈ s) hdom hx
  have hxU : x ∈ RELAT_1.dom pA ∪ RELAT_1.dom qA :=
    Eq.subst (motive := fun s => x ∈ s) (override_dom pA qA) hxR
  have hxA : x ∈ A :=
    Or.elim ((XBOOLE_0.def3 _ _ _).mp hxU)
      (fun hxpA => ((XBOOLE_0.def4 _ _ _).mp
        (Eq.subst (motive := fun s => x ∈ s) RELAT_1.th61 hxpA)).2)
      (fun hxqA => ((XBOOLE_0.def4 _ _ _).mp
        (Eq.subst (motive := fun s => x ∈ s) RELAT_1.th61 hxqA)).2)
  exact Or.elim (Classical.em (x ∈ RELAT_1.dom qA))
    (fun hxqA => by
      have hxq : x ∈ RELAT_1.dom q :=
        ((XBOOLE_0.def4 _ _ _).mp
          (Eq.subst (motive := fun s => x ∈ s) RELAT_1.th61 hxqA)).1
      have hxO0 : x ∈ RELAT_1.dom (override p q) :=
        (th12 p q x).mpr (Or.inr hxq)
      have hxO : x ∈ RELAT_1.dom lhs :=
        Eq.subst (motive := fun s => x ∈ s) RELAT_1.th61.symm
          ((XBOOLE_0.def4 _ _ _).mpr ⟨hxO0, hxA⟩)
      have hL : FUNCT_1.apply lhs x = FUNCT_1.apply (override p q) x :=
        FUNCT_1.th47 (override_isFunction p q).2 hxO
      have hO : FUNCT_1.apply (override p q) x = FUNCT_1.apply q x :=
        th13 (f := p) (g := q) hxq
      have hR : FUNCT_1.apply rhs x = FUNCT_1.apply qA x :=
        th13 (f := pA) (g := qA) hxqA
      have hQA : FUNCT_1.apply qA x = FUNCT_1.apply q x :=
        FUNCT_1.th47 hq.2 hxqA
      exact hL.trans (hO.trans (hQA.symm.trans hR.symm)))
    (fun hnxqA => by
      have hxpA : x ∈ RELAT_1.dom pA :=
        Or.elim ((XBOOLE_0.def3 _ _ _).mp hxU) id (fun h => (hnxqA h).elim)
      have hxp : x ∈ RELAT_1.dom p :=
        ((XBOOLE_0.def4 _ _ _).mp
          (Eq.subst (motive := fun s => x ∈ s) RELAT_1.th61 hxpA)).1
      have hnxq : x ∉ RELAT_1.dom q := by
        intro hxq
        exact hnxqA (Eq.subst (motive := fun s => x ∈ s) RELAT_1.th61.symm
          ((XBOOLE_0.def4 _ _ _).mpr ⟨hxq, hxA⟩))
      have hxO0 : x ∈ RELAT_1.dom (override p q) :=
        (th12 p q x).mpr (Or.inl hxp)
      have hxO : x ∈ RELAT_1.dom lhs :=
        Eq.subst (motive := fun s => x ∈ s) RELAT_1.th61.symm
          ((XBOOLE_0.def4 _ _ _).mpr ⟨hxO0, hxA⟩)
      have hL : FUNCT_1.apply lhs x = FUNCT_1.apply (override p q) x :=
        FUNCT_1.th47 (override_isFunction p q).2 hxO
      have hO : FUNCT_1.apply (override p q) x = FUNCT_1.apply p x :=
        th11 (f := p) (g := q) hnxq
      have hR : FUNCT_1.apply rhs x = FUNCT_1.apply pA x :=
        th11 (f := pA) (g := qA) hnxqA
      have hPA : FUNCT_1.apply pA x = FUNCT_1.apply p x :=
        FUNCT_1.th47 hp.2 hxpA
      exact hL.trans (hO.trans (hPA.symm.trans hR.symm)))

/-- `FUNCT_4:72` (`Th72`) — `A misses dom g → (f+*g)|A = f|A`. -/
theorem th72 {f g A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (hmiss : XBOOLE_0.misses A (RELAT_1.dom g)) :
    RELAT_1.restrict (override f g) A = RELAT_1.restrict f A := by
  have hmiss' : XBOOLE_0.misses (RELAT_1.dom g) A :=
    XBOOLE_0.misses_symm hmiss
  have hgA0 : RELAT_1.restrict g A = (∅ : TarskiSet.{u}) :=
    (RELAT_1.th66 (R := g) (X := A)).mpr hmiss'
  exact
    (th71 hf hg (A := A)).trans
      (Eq.subst (motive := fun s =>
          override (RELAT_1.restrict f A) s = RELAT_1.restrict f A)
        hgA0.symm (th21 (FUNCT_1.restrict_isFunction (X := A) hf)))

/-- `FUNCT_4:73` — `dom f misses A → (f+*g)|A = g|A`. -/
theorem th73 {f g A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f) A) :
    RELAT_1.restrict (override f g) A = RELAT_1.restrict g A := by
  have hfA0 : RELAT_1.restrict f A = (∅ : TarskiSet.{u}) :=
    (RELAT_1.th66 (R := f) (X := A)).mpr hmiss
  exact
    (th71 hf hg (A := A)).trans
      (Eq.subst (motive := fun s =>
          override s (RELAT_1.restrict g A) = RELAT_1.restrict g A)
        hfA0.symm (th20 (FUNCT_1.restrict_isFunction (X := A) hg)))

/-- `FUNCT_4:74` — `dom g = dom h → f+*g+*h = f+*h`. -/
theorem th74 {f g h : TarskiSet.{u}} (_hg : FUNCT_1.isFunction g)
    (hh : FUNCT_1.isFunction h) (hd : RELAT_1.dom g = RELAT_1.dom h) :
    override (override f g) h = override f h :=
  (th14 f g h).trans
    (congrArg (override f)
      (th19 (f := g) (g := h) hh
        (Eq.subst (motive := fun s => RELAT_1.dom g ⊆ s) hd
          (fun _ hx => hx))))

/-- `FUNCT_4:Lm2` — `f ⊆ g → g+*f = g`. -/
theorem lm2 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hsub : f ⊆ g) : override g f = g := by
  have ht : PARTFUN1.tolerates g f :=
    PARTFUN1.tolerates_symm (PARTFUN1.th54 hf hg hsub)
  have heq : g ∪ f = override g f := (th30 hg hf).mp ht
  have hun : g ∪ f = g :=
    (XBOOLE_0.union_comm g f).trans (XBOOLE_1.th12 hsub)
  exact heq.symm.trans hun

/-- `FUNCT_4:75` — `f +* f|A = f`. -/
theorem th75 {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    override f (RELAT_1.restrict f A) = f :=
  lm2 (FUNCT_1.restrict_isFunction (X := A) hf) hf RELAT_1.th59

/-- `FUNCT_4:76` — disjoint domains: restrictions recover summands. -/
theorem th76 {f g B C : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (hfB : RELAT_1.dom f ⊆ B) (hgC : RELAT_1.dom g ⊆ C)
    (hmiss : XBOOLE_0.misses B C) :
    RELAT_1.restrict (override f g) B = f ∧
      RELAT_1.restrict (override f g) C = g := by
  have hmissfC : XBOOLE_0.misses (RELAT_1.dom f) C :=
    XBOOLE_1.th63 hfB hmiss
  have hfC0 : RELAT_1.restrict f C = (∅ : TarskiSet.{u}) :=
    (RELAT_1.th66 (R := f) (X := C)).mpr hmissfC
  have hmissgB : XBOOLE_0.misses (RELAT_1.dom g) B :=
    XBOOLE_1.th63 hgC (XBOOLE_0.misses_symm hmiss)
  have hgB0 : RELAT_1.restrict g B = (∅ : TarskiSet.{u}) :=
    (RELAT_1.th66 (R := g) (X := B)).mpr hmissgB
  constructor
  · have h1 :=
      (th71 hf hg (A := B)).trans
        (Eq.subst (motive := fun s =>
            override (RELAT_1.restrict f B) s = RELAT_1.restrict f B)
          hgB0.symm (th21 (FUNCT_1.restrict_isFunction (X := B) hf)))
    exact h1.trans (RELAT_1.th68 hf.1 hfB)
  · have h1 :=
      (th71 hf hg (A := C)).trans
        (Eq.subst (motive := fun s =>
            override s (RELAT_1.restrict g C) = RELAT_1.restrict g C)
          hfC0.symm (th20 (FUNCT_1.restrict_isFunction (X := C) hg)))
    exact h1.trans (RELAT_1.th68 hg.1 hgC)

/-- `FUNCT_4:77` — `dom p ⊆ A` and `dom q misses A` → `(p+*q)|A = p`. -/
theorem th77 {p q A : TarskiSet.{u}} (hp : FUNCT_1.isFunction p)
    (hq : FUNCT_1.isFunction q) (hpA : RELAT_1.dom p ⊆ A)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom q) A) :
    RELAT_1.restrict (override p q) A = p :=
  (th72 hp hq (XBOOLE_0.misses_symm hmiss)).trans
    (RELAT_1.th68 hp.1 hpA)

/-- `FUNCT_4:78` — `f|(A ∪ B) = f|A +* f|B`. -/
theorem th78 {f A B : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    RELAT_1.restrict f (A ∪ B) =
      override (RELAT_1.restrict f A) (RELAT_1.restrict f B) := by
  have hInterB : (A ∪ B) ∩ B = B :=
    (XBOOLE_0.inter_comm (A ∪ B) B).trans
      ((congrArg (fun s => B ∩ s) (XBOOLE_0.union_comm A B)).trans
        (XBOOLE_1.th21 (X := B) (Y := A)))
  have hInterA : (A ∪ B) ∩ A = A :=
    (XBOOLE_0.inter_comm (A ∪ B) A).trans (XBOOLE_1.th21 (X := A) (Y := B))
  have hB : RELAT_1.restrict (RELAT_1.restrict f (A ∪ B)) B =
      RELAT_1.restrict f B :=
    (RELAT_1.th71 (R := f) (X := A ∪ B) (Y := B)).trans
      (congrArg (RELAT_1.restrict f) hInterB)
  have hA : RELAT_1.restrict (RELAT_1.restrict f (A ∪ B)) A =
      RELAT_1.restrict f A :=
    (RELAT_1.th71 (R := f) (X := A ∪ B) (Y := A)).trans
      (congrArg (RELAT_1.restrict f) hInterA)
  have hdom : RELAT_1.dom (RELAT_1.restrict f (A ∪ B)) ⊆ A ∪ B :=
    RELAT_1.th58
  have hmain :=
    th70 (FUNCT_1.restrict_isFunction (X := A ∪ B) hf) hdom
  have h1 : override (RELAT_1.restrict f A)
      (RELAT_1.restrict (RELAT_1.restrict f (A ∪ B)) B) =
      RELAT_1.restrict f (A ∪ B) :=
    Eq.subst (motive := fun s =>
        override s (RELAT_1.restrict (RELAT_1.restrict f (A ∪ B)) B) =
          RELAT_1.restrict f (A ∪ B)) hA hmain
  have h2 : override (RELAT_1.restrict f A) (RELAT_1.restrict f B) =
      RELAT_1.restrict f (A ∪ B) :=
    Eq.subst (motive := fun s =>
        override (RELAT_1.restrict f A) s =
          RELAT_1.restrict f (A ∪ B)) hB h1
  exact h2.symm

/-- `FUNCT_4:79` — `(i,j):->k = [i,j].-->k`. -/
theorem th79 (i j k : TarskiSet.{u}) :
    FUNCOP_1.mapsTo2 i j k = FUNCOP_1.dotArrow (TARSKI.pair i j) k :=
  (FUNCOP_1.def7 i j k).trans
    (FUNCOP_1.dotArrow_eq (TARSKI.pair i j) k).symm

/-- `FUNCT_4:80` — `((i,j):->k).(i,j) = k`. -/
theorem th80 (i j k : TarskiSet.{u}) :
    BINOP_1.apply2 (FUNCOP_1.mapsTo2 i j k) i j = k :=
  FUNCOP_1.th71 i j k

/-- `FUNCT_4:81` — `(a,a)-->(b,c) = a .--> c`. -/
theorem th81 (a b c : TarskiSet.{u}) :
    pairMapsTo a a b c = FUNCOP_1.dotArrow a c := by
  have hd : RELAT_1.dom (FUNCOP_1.dotArrow a b) = TARSKI.singleton a :=
    FUNCOP_1.mapsTo_dom _ _
  have hd' : RELAT_1.dom (FUNCOP_1.dotArrow a c) = TARSKI.singleton a :=
    FUNCOP_1.mapsTo_dom _ _
  have hsub : RELAT_1.dom (FUNCOP_1.dotArrow a b) ⊆
      RELAT_1.dom (FUNCOP_1.dotArrow a c) :=
    Eq.subst (motive := fun s => RELAT_1.dom (FUNCOP_1.dotArrow a b) ⊆ s)
      (hd.trans hd'.symm) (fun _ hx => hx)
  exact th19 (FUNCOP_1.dotArrow_isFunction a c) hsub

/-- `FUNCT_4:82` — `x .--> y = {[x,y]}`. -/
theorem th82 (x y : TarskiSet.{u}) :
    FUNCOP_1.dotArrow x y = TARSKI.singleton (TARSKI.pair x y) :=
  (FUNCOP_1.dotArrow_eq x y).trans
    ((FUNCOP_1.def2 (TARSKI.singleton x) y).trans ZFMISC_1.th29)

/-- `FUNCT_4:83` — `a ≠ c → (f +* (a .--> b)).c = f.c`. -/
theorem th83 {f a b c : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f)
    (hne : a ≠ c) :
    FUNCT_1.apply (override f (FUNCOP_1.dotArrow a b)) c =
      FUNCT_1.apply f c := by
  have hdom : RELAT_1.dom (FUNCOP_1.dotArrow a b) = TARSKI.singleton a :=
    FUNCOP_1.mapsTo_dom _ _
  have hnc : c ∉ RELAT_1.dom (FUNCOP_1.dotArrow a b) := fun hc =>
    hne ((TARSKI.def1 a c).mp
      (Eq.subst (motive := fun s => c ∈ s) hdom hc)).symm
  exact th11 (f := f) (g := FUNCOP_1.dotArrow a b) hnc

/-- `FUNCT_4:84` — overriding by a two-point map sets both values. -/
theorem th84 {f a b c d : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f)
    (hne : a ≠ b) :
    FUNCT_1.apply (override f (pairMapsTo a b c d)) a = c ∧
      FUNCT_1.apply (override f (pairMapsTo a b c d)) b = d := by
  have hd : RELAT_1.dom (pairMapsTo a b c d) = TARSKI.upair a b :=
    (th62 a b c d).1
  have ha : a ∈ RELAT_1.dom (pairMapsTo a b c d) :=
    Eq.subst (motive := fun s => a ∈ s) hd.symm
      ((TARSKI.def2 a b a).mpr (Or.inl rfl))
  have hb : b ∈ RELAT_1.dom (pairMapsTo a b c d) :=
    Eq.subst (motive := fun s => b ∈ s) hd.symm
      ((TARSKI.def2 a b b).mpr (Or.inr rfl))
  exact
    ⟨(th13 (f := f) (g := pairMapsTo a b c d) ha).trans
        ((th63 a b c d).1 hne),
      (th13 (f := f) (g := pairMapsTo a b c d) hb).trans
        (th63 a b c d).2⟩

/-- `FUNCT_4:85` (`Th85`) — `a ∈ dom f ∧ f.a = b → a .--> b ⊆ f`. -/
theorem th85 {a b f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (ha : a ∈ RELAT_1.dom f) (hb : FUNCT_1.apply f a = b) :
    FUNCOP_1.dotArrow a b ⊆ f :=
  Eq.subst (motive := fun s => FUNCOP_1.dotArrow a s ⊆ f) hb
    (FUNCOP_1.th84 hf ha)

/-- `FUNCT_4:86` — both values in domain imply pairMapsTo ⊆ f. -/
theorem th86 {a b c d f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (ha : a ∈ RELAT_1.dom f) (hc : c ∈ RELAT_1.dom f)
    (hb : FUNCT_1.apply f a = b) (hd : FUNCT_1.apply f c = d) :
    pairMapsTo a c b d ⊆ f := by
  have this := Classical.propDecidable (a = c)
  by_cases heq : a = c
  · have hb' : FUNCT_1.apply f a = d :=
      Eq.subst (motive := fun s => FUNCT_1.apply f s = d) heq.symm hd
    have hpm : pairMapsTo a c b d = FUNCOP_1.dotArrow a d :=
      Eq.subst (motive := fun s =>
          pairMapsTo a s b d = FUNCOP_1.dotArrow a d) heq (th81 a b d)
    exact Eq.subst (motive := fun s => s ⊆ f) hpm.symm (th85 hf ha hb')
  · have hup : TARSKI.upair (TARSKI.pair a b) (TARSKI.pair c d) ⊆ f :=
      (ZFMISC_1.th32).mpr ⟨(FUNCT_1.th1 hf.2).mpr ⟨ha, hb.symm⟩,
        (FUNCT_1.th1 hf.2).mpr ⟨hc, hd.symm⟩⟩
    exact Eq.subst (motive := fun s => s ⊆ f) (th67 heq).symm hup

/-- `FUNCT_4:87` (`Th87`) — `f ⊆ h ∧ g ⊆ h → f+*g ⊆ h`. -/
theorem th87 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hfsub : f ⊆ h) (hgsub : g ⊆ h) :
    override f g ⊆ h :=
  XBOOLE_1.th1 (th29 hf hg) (XBOOLE_1.th8 hfsub hgsub)

/-- `FUNCT_4:88` — `(f+*(g|A))|A = g|A` when domains agree on A. -/
theorem th88 {f g A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (h : A ∩ RELAT_1.dom f ⊆ A ∩ RELAT_1.dom g) :
    RELAT_1.restrict (override f (RELAT_1.restrict g A)) A =
      RELAT_1.restrict g A := by
  have hdA : RELAT_1.dom (RELAT_1.restrict f A) = A ∩ RELAT_1.dom f :=
    (RELAT_1.th61 (R := f) (X := A)).trans (XBOOLE_0.inter_comm _ _)
  have hdB : RELAT_1.dom (RELAT_1.restrict g A) = A ∩ RELAT_1.dom g :=
    (RELAT_1.th61 (R := g) (X := A)).trans (XBOOLE_0.inter_comm _ _)
  have hsub : RELAT_1.dom (RELAT_1.restrict f A) ⊆
      RELAT_1.dom (RELAT_1.restrict g A) :=
    Eq.subst (motive := fun s => s ⊆ RELAT_1.dom (RELAT_1.restrict g A))
      hdA.symm
      (Eq.subst (motive := fun s => A ∩ RELAT_1.dom f ⊆ s) hdB.symm h)
  have h1 : RELAT_1.restrict (override f (RELAT_1.restrict g A)) A =
      override (RELAT_1.restrict f A)
        (RELAT_1.restrict (RELAT_1.restrict g A) A) :=
    th71 hf (FUNCT_1.restrict_isFunction (X := A) hg) (A := A)
  have h2 : RELAT_1.restrict (RELAT_1.restrict g A) A =
      RELAT_1.restrict g A :=
    RELAT_1.th68 (FUNCT_1.restrict_isFunction (X := A) hg).1 RELAT_1.th58
  exact
    h1.trans
      ((congrArg (override (RELAT_1.restrict f A)) h2).trans
        (th19 (FUNCT_1.restrict_isFunction (X := A) hg) hsub))

/-- `FUNCT_4:89` — `(f +* (a.-->b) +* (m.-->n)).m = n`. -/
theorem th89 (f a b n m : TarskiSet.{u}) :
    FUNCT_1.apply
      (override (override f (FUNCOP_1.dotArrow a b)) (FUNCOP_1.dotArrow m n))
      m = n := by
  have hd : RELAT_1.dom (FUNCOP_1.dotArrow m n) = TARSKI.singleton m :=
    FUNCOP_1.mapsTo_dom _ _
  have hm : m ∈ RELAT_1.dom (FUNCOP_1.dotArrow m n) :=
    Eq.subst (motive := fun s => m ∈ s) hd.symm
      ((TARSKI.def1 m m).mpr rfl)
  exact (th13 (f := override f (FUNCOP_1.dotArrow a b))
      (g := FUNCOP_1.dotArrow m n) hm).trans (FUNCOP_1.th72 m n)

/-- `FUNCT_4:90` — `(f +* (n.-->m) +* (m.-->n)).n = m`. -/
theorem th90 (f n m : TarskiSet.{u}) :
    FUNCT_1.apply
      (override (override f (FUNCOP_1.dotArrow n m)) (FUNCOP_1.dotArrow m n))
      n = m := by
  have this := Classical.propDecidable (n = m)
  by_cases heq : n = m
  · have hd : RELAT_1.dom (FUNCOP_1.dotArrow m n) = TARSKI.singleton m :=
      FUNCOP_1.mapsTo_dom _ _
    have hm : m ∈ RELAT_1.dom (FUNCOP_1.dotArrow m n) :=
      Eq.subst (motive := fun s => m ∈ s) hd.symm
        ((TARSKI.def1 m m).mpr rfl)
    have h1 := th13 (f := override f (FUNCOP_1.dotArrow n m))
      (g := FUNCOP_1.dotArrow m n) hm
    exact Eq.subst (motive := fun s =>
        FUNCT_1.apply
          (override (override f (FUNCOP_1.dotArrow n m))
            (FUNCOP_1.dotArrow m n)) s = m) heq.symm
      (h1.trans (Eq.subst (motive := fun s =>
          FUNCT_1.apply (FUNCOP_1.dotArrow m n) m = s) heq
          (FUNCOP_1.th72 m n)))
  · have hdnm : RELAT_1.dom (FUNCOP_1.dotArrow n m) = TARSKI.singleton n :=
      FUNCOP_1.mapsTo_dom _ _
    have hdn : n ∈ RELAT_1.dom (FUNCOP_1.dotArrow n m) :=
      Eq.subst (motive := fun s => n ∈ s) hdnm.symm
        ((TARSKI.def1 n n).mpr rfl)
    have hdmn : RELAT_1.dom (FUNCOP_1.dotArrow m n) = TARSKI.singleton m :=
      FUNCOP_1.mapsTo_dom _ _
    have hnn : n ∉ RELAT_1.dom (FUNCOP_1.dotArrow m n) := fun hn =>
      heq ((TARSKI.def1 m n).mp
        (Eq.subst (motive := fun s => n ∈ s) hdmn hn))
    exact (th11 (f := override f (FUNCOP_1.dotArrow n m))
        (g := FUNCOP_1.dotArrow m n) hnn).trans
      ((th13 (f := f) (g := FUNCOP_1.dotArrow n m) hdn).trans
        (FUNCOP_1.th72 n m))

/-- `FUNCT_4:91` — off support: apply of double override is f. -/
theorem th91 {f a b n m x : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f)
    (hxm : x ≠ m) (hxa : x ≠ a) :
    FUNCT_1.apply
      (override (override f (FUNCOP_1.dotArrow a b)) (FUNCOP_1.dotArrow m n))
      x = FUNCT_1.apply f x := by
  have hda : RELAT_1.dom (FUNCOP_1.dotArrow a b) = TARSKI.singleton a :=
    FUNCOP_1.mapsTo_dom _ _
  have hdm : RELAT_1.dom (FUNCOP_1.dotArrow m n) = TARSKI.singleton m :=
    FUNCOP_1.mapsTo_dom _ _
  have hnxa : x ∉ RELAT_1.dom (FUNCOP_1.dotArrow a b) := fun hx =>
    hxa ((TARSKI.def1 a x).mp
      (Eq.subst (motive := fun s => x ∈ s) hda hx))
  have hnxm : x ∉ RELAT_1.dom (FUNCOP_1.dotArrow m n) := fun hx =>
    hxm ((TARSKI.def1 m x).mp
      (Eq.subst (motive := fun s => x ∈ s) hdm hx))
  exact (th11 (f := override f (FUNCOP_1.dotArrow a b))
      (g := FUNCOP_1.dotArrow m n) hnxm).trans
    (th11 (f := f) (g := FUNCOP_1.dotArrow a b) hnxa)

/-- `FUNCT_4:92` — one-to-one + disjoint ranges → override one-to-one. -/
theorem th92 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (h1f : FUNCT_1.isOneToOne f)
    (h1g : FUNCT_1.isOneToOne g)
    (hmiss : XBOOLE_0.misses (RELAT_1.rng f) (RELAT_1.rng g)) :
    FUNCT_1.isOneToOne (override f g) := by
  refine (FUNCT_1.def4 (override f g)).mpr ?_
  intro x1 x2 hx1 hx2 happ
  have hx1U := (th12 f g x1).mp hx1
  have hx2U := (th12 f g x2).mp hx2
  exact Or.elim (Classical.em (x1 ∈ RELAT_1.dom g))
    (fun hx1g =>
      Or.elim (Classical.em (x2 ∈ RELAT_1.dom g))
        (fun hx2g => by
          have h1 := th13 (f := f) (g := g) hx1g
          have h2 := th13 (f := f) (g := g) hx2g
          have heq : FUNCT_1.apply g x1 = FUNCT_1.apply g x2 :=
            h1.symm.trans (happ.trans h2)
          exact ((FUNCT_1.def4 g).mp h1g) x1 x2 hx1g hx2g heq)
        (fun hnx2g => by
          have hx2f : x2 ∈ RELAT_1.dom f :=
            Or.elim hx2U id (fun h => (hnx2g h).elim)
          have hyf : FUNCT_1.apply f x2 ∈ RELAT_1.rng f :=
            FUNCT_1.th3 hf.2 hx2f
          have hyg : FUNCT_1.apply g x1 ∈ RELAT_1.rng g :=
            FUNCT_1.th3 hg.2 hx1g
          have heq : FUNCT_1.apply g x1 = FUNCT_1.apply f x2 :=
            (th13 (f := f) (g := g) hx1g).symm.trans
              (happ.trans (th11 (f := f) (g := g) hnx2g))
          have hinter : FUNCT_1.apply f x2 ∈
              RELAT_1.rng f ∩ RELAT_1.rng g :=
            (XBOOLE_0.def4 _ _ _).mpr ⟨hyf,
              Eq.subst (motive := fun s => s ∈ RELAT_1.rng g) heq hyg⟩
          have hempty : FUNCT_1.apply f x2 ∈ (∅ : TarskiSet.{u}) :=
            Eq.subst (motive := fun s => FUNCT_1.apply f x2 ∈ s)
              ((XBOOLE_0.def7 _ _).mp hmiss) hinter
          exact ((XBOOLE_0.empty_iff _).mp hempty).elim))
    (fun hnx1g =>
      Or.elim (Classical.em (x2 ∈ RELAT_1.dom g))
        (fun hx2g => by
          have hx1f : x1 ∈ RELAT_1.dom f :=
            Or.elim hx1U id (fun h => (hnx1g h).elim)
          have hyf : FUNCT_1.apply f x1 ∈ RELAT_1.rng f :=
            FUNCT_1.th3 hf.2 hx1f
          have hyg : FUNCT_1.apply g x2 ∈ RELAT_1.rng g :=
            FUNCT_1.th3 hg.2 hx2g
          have heq : FUNCT_1.apply f x1 = FUNCT_1.apply g x2 :=
            (th11 (f := f) (g := g) hnx1g).symm.trans
              (happ.trans (th13 (f := f) (g := g) hx2g))
          have hinter : FUNCT_1.apply f x1 ∈
              RELAT_1.rng f ∩ RELAT_1.rng g :=
            (XBOOLE_0.def4 _ _ _).mpr ⟨hyf,
              Eq.subst (motive := fun s => s ∈ RELAT_1.rng g) heq.symm hyg⟩
          have hempty : FUNCT_1.apply f x1 ∈ (∅ : TarskiSet.{u}) :=
            Eq.subst (motive := fun s => FUNCT_1.apply f x1 ∈ s)
              ((XBOOLE_0.def7 _ _).mp hmiss) hinter
          exact ((XBOOLE_0.empty_iff _).mp hempty).elim)
        (fun hnx2g => by
          have hx1f : x1 ∈ RELAT_1.dom f :=
            Or.elim hx1U id (fun h => (hnx1g h).elim)
          have hx2f : x2 ∈ RELAT_1.dom f :=
            Or.elim hx2U id (fun h => (hnx2g h).elim)
          have heq : FUNCT_1.apply f x1 = FUNCT_1.apply f x2 :=
            (th11 (f := f) (g := g) hnx1g).symm.trans
              (happ.trans (th11 (f := f) (g := g) hnx2g))
          exact ((FUNCT_1.def4 f).mp h1f) x1 x2 hx1f hx2f heq))

/-- Registration reduce: `f +* g +* g = f +* g`. -/
theorem reg_override_idem {f g : TarskiSet.{u}}
    (_hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g) :
    override (override f g) g = override f g :=
  (th14 f g g).trans (congrArg (override f) (th19 hg (fun _ hx => hx)))

/-- `FUNCT_4:93` — same as `reg_override_idem`. -/
theorem th93 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    override (override f g) g = override f g :=
  reg_override_idem hf hg

/-- `FUNCT_4:94` — `(f+*g)|D = h|D → (h+*g)|D = (f+*g)|D`. -/
theorem th94 {f g h D : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (heq : RELAT_1.restrict (override f g) D = RELAT_1.restrict h D) :
    RELAT_1.restrict (override h g) D = RELAT_1.restrict (override f g) D := by
  have hdFG : RELAT_1.dom (RELAT_1.restrict (override f g) D) =
      (RELAT_1.dom f ∪ RELAT_1.dom g) ∩ D :=
    (RELAT_1.th61 (R := override f g) (X := D)).trans
      (congrArg (fun s => s ∩ D) (override_dom f g))
  have hdHG0 : RELAT_1.dom (RELAT_1.restrict (override h g) D) =
      (RELAT_1.dom h ∪ RELAT_1.dom g) ∩ D :=
    (RELAT_1.th61 (R := override h g) (X := D)).trans
      (congrArg (fun s => s ∩ D) (override_dom h g))
  have hdH : RELAT_1.dom (RELAT_1.restrict h D) =
      (RELAT_1.dom f ∪ RELAT_1.dom g) ∩ D :=
    (congrArg RELAT_1.dom heq.symm).trans hdFG
  have hdomEq : RELAT_1.dom (RELAT_1.restrict (override h g) D) =
      RELAT_1.dom (RELAT_1.restrict (override f g) D) := by
    have hdistrib : (RELAT_1.dom h ∪ RELAT_1.dom g) ∩ D =
        (RELAT_1.dom h ∩ D) ∪ (RELAT_1.dom g ∩ D) :=
      (XBOOLE_0.inter_comm _ _).trans
        ((XBOOLE_1.th23 (X := D) (Y := RELAT_1.dom h) (Z := RELAT_1.dom g)).trans
          (congr_union (XBOOLE_0.inter_comm D (RELAT_1.dom h))
            (XBOOLE_0.inter_comm D (RELAT_1.dom g))))
    have hAbs : RELAT_1.dom g ∩ D ⊆ (RELAT_1.dom f ∪ RELAT_1.dom g) ∩ D := by
      intro x hx
      have ⟨hxg, hxD⟩ := (XBOOLE_0.def4 _ _ _).mp hx
      exact (XBOOLE_0.def4 _ _ _).mpr
        ⟨(XBOOLE_0.def3 _ _ _).mpr (Or.inr hxg), hxD⟩
    have hstep :
        (RELAT_1.dom h ∩ D) ∪ (RELAT_1.dom g ∩ D) =
          (RELAT_1.dom f ∪ RELAT_1.dom g) ∩ D :=
      (congrArg (fun s => s ∪ (RELAT_1.dom g ∩ D))
        ((RELAT_1.th61 (R := h) (X := D)).symm.trans hdH)).trans
        ((XBOOLE_0.union_comm ((RELAT_1.dom f ∪ RELAT_1.dom g) ∩ D)
            (RELAT_1.dom g ∩ D)).trans (XBOOLE_1.th12 hAbs))
    exact hdHG0.trans (hdistrib.trans (hstep.trans hdFG.symm))
  refine FUNCT_1.th2
    (FUNCT_1.restrict_isFunction (X := D) (override_isFunction h g))
    (FUNCT_1.restrict_isFunction (X := D) (override_isFunction f g))
    hdomEq ?_
  intro x hx
  have hxFG : x ∈ RELAT_1.dom (RELAT_1.restrict (override f g) D) :=
    Eq.subst (motive := fun s => x ∈ s) hdomEq hx
  have hxD : x ∈ D :=
    ((XBOOLE_0.def4 _ _ _).mp
      (Eq.subst (motive := fun s => x ∈ s) hdFG hxFG)).2
  have happFG := FUNCT_1.th47 (override_isFunction f g).2 hxFG
  have happHG := FUNCT_1.th47 (override_isFunction h g).2 hx
  exact Or.elim (Classical.em (x ∈ RELAT_1.dom g))
    (fun hxg =>
      happHG.trans ((th13 (f := h) (g := g) hxg).trans
        ((th13 (f := f) (g := g) hxg).symm.trans happFG.symm)))
    (fun hnxg => by
      have hxH : x ∈ RELAT_1.dom (RELAT_1.restrict h D) :=
        Eq.subst (motive := fun s => x ∈ s) (congrArg RELAT_1.dom heq) hxFG
      exact happHG.trans
        ((th11 (f := h) (g := g) hnxg).trans
          ((FUNCT_1.th47 hh.2 hxH).symm.trans
            (congrArg (fun s => FUNCT_1.apply s x) heq.symm))))

/-- `FUNCT_4:95` — `f|D = h|D → (h+*g)|D = (f+*g)|D`. -/
theorem th95 {f g h D : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (heq : RELAT_1.restrict f D = RELAT_1.restrict h D) :
    RELAT_1.restrict (override h g) D = RELAT_1.restrict (override f g) D := by
  have hdFG : RELAT_1.dom (RELAT_1.restrict (override f g) D) =
      (RELAT_1.dom f ∪ RELAT_1.dom g) ∩ D :=
    (RELAT_1.th61 (R := override f g) (X := D)).trans
      (congrArg (fun s => s ∩ D) (override_dom f g))
  have hdHG0 : RELAT_1.dom (RELAT_1.restrict (override h g) D) =
      (RELAT_1.dom h ∪ RELAT_1.dom g) ∩ D :=
    (RELAT_1.th61 (R := override h g) (X := D)).trans
      (congrArg (fun s => s ∩ D) (override_dom h g))
  have hdH : RELAT_1.dom h ∩ D = RELAT_1.dom f ∩ D :=
    (RELAT_1.th61 (R := h) (X := D)).symm.trans
      ((congrArg RELAT_1.dom heq.symm).trans RELAT_1.th61)
  have hdomEq : RELAT_1.dom (RELAT_1.restrict (override h g) D) =
      RELAT_1.dom (RELAT_1.restrict (override f g) D) := by
    have h1 : (RELAT_1.dom h ∪ RELAT_1.dom g) ∩ D =
        (RELAT_1.dom h ∩ D) ∪ (RELAT_1.dom g ∩ D) :=
      (XBOOLE_0.inter_comm _ _).trans
        ((XBOOLE_1.th23 (X := D) (Y := RELAT_1.dom h) (Z := RELAT_1.dom g)).trans
          (congr_union (XBOOLE_0.inter_comm D (RELAT_1.dom h))
            (XBOOLE_0.inter_comm D (RELAT_1.dom g))))
    have h2 : (RELAT_1.dom f ∪ RELAT_1.dom g) ∩ D =
        (RELAT_1.dom f ∩ D) ∪ (RELAT_1.dom g ∩ D) :=
      (XBOOLE_0.inter_comm _ _).trans
        ((XBOOLE_1.th23 (X := D) (Y := RELAT_1.dom f) (Z := RELAT_1.dom g)).trans
          (congr_union (XBOOLE_0.inter_comm D (RELAT_1.dom f))
            (XBOOLE_0.inter_comm D (RELAT_1.dom g))))
    exact hdHG0.trans (h1.trans
      ((congrArg (fun s => s ∪ (RELAT_1.dom g ∩ D)) hdH).trans
        (h2.symm.trans hdFG.symm)))
  refine FUNCT_1.th2
    (FUNCT_1.restrict_isFunction (X := D) (override_isFunction h g))
    (FUNCT_1.restrict_isFunction (X := D) (override_isFunction f g))
    hdomEq ?_
  intro x hx
  have hxFG : x ∈ RELAT_1.dom (RELAT_1.restrict (override f g) D) :=
    Eq.subst (motive := fun s => x ∈ s) hdomEq hx
  have hxD : x ∈ D :=
    ((XBOOLE_0.def4 _ _ _).mp
      (Eq.subst (motive := fun s => x ∈ s) hdFG hxFG)).2
  have happFG := FUNCT_1.th47 (override_isFunction f g).2 hxFG
  have happHG := FUNCT_1.th47 (override_isFunction h g).2 hx
  exact Or.elim (Classical.em (x ∈ RELAT_1.dom g))
    (fun hxg =>
      happHG.trans ((th13 (f := h) (g := g) hxg).trans
        ((th13 (f := f) (g := g) hxg).symm.trans happFG.symm)))
    (fun hnxg =>
      happHG.trans ((th11 (f := h) (g := g) hnxg).trans
        ((FUNCT_1.th49 hh.2 hxD).symm.trans
          ((congrArg (fun s => FUNCT_1.apply s x) heq.symm).trans
            ((FUNCT_1.th49 hf.2 hxD).trans
              ((th11 (f := f) (g := g) hnxg).symm.trans happFG.symm))))))

/-- `FUNCT_4:96` (`Th96`) — `x .--> x = id {x}`. -/
theorem th96 (x : TarskiSet.{u}) :
    FUNCOP_1.dotArrow x x = RELAT_1.id (TARSKI.singleton x) := by
  refine FUNCT_1.th2 (FUNCOP_1.dotArrow_isFunction x x)
    (FUNCT_1.id_isFunction (TARSKI.singleton x)) ?_ ?_
  · exact (FUNCOP_1.mapsTo_dom _ _).trans (RELAT_1.id_dom _).symm
  · intro y hy
    have hyx : y = x := (TARSKI.def1 x y).mp
      (Eq.subst (motive := fun s => y ∈ s) (FUNCOP_1.mapsTo_dom _ _) hy)
    exact Eq.subst (motive := fun s =>
        FUNCT_1.apply (FUNCOP_1.dotArrow x x) s =
          FUNCT_1.apply (RELAT_1.id (TARSKI.singleton x)) s) hyx.symm
      ((FUNCOP_1.th72 x x).trans
        (FUNCT_1.id_apply ((TARSKI.def1 x x).mpr rfl)).symm)

/-- `FUNCT_4:97` (`Th97`) — `f ⊆ g → f+*g = g`. -/
theorem th97 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hsub : f ⊆ g) : override f g = g := by
  have heq : f ∪ g = override f g := (th30 hf hg).mp (PARTFUN1.th54 hf hg hsub)
  exact heq.symm.trans (XBOOLE_1.th12 hsub)

/-- `FUNCT_4:98` (`Th98`) — `f ⊆ g → g+*f = g`. -/
theorem th98 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hsub : f ⊆ g) : override g f = g :=
  lm2 hf hg hsub

/-! ## `f+~(x,y)` (`FUNCT_4:def 5`) — range-value update (`rangeUpdate`) -/

/-- `FUNCT_4:def 5` — `f +~ (x,y)`. -/
noncomputable def rangeUpdate (f x y : TarskiSet.{u}) : TarskiSet.{u} :=
  override f (RELAT_1.comp f (FUNCOP_1.dotArrow x y))

theorem rangeUpdate_isFunction {f : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f)
    (x y : TarskiSet.{u}) : FUNCT_1.isFunction (rangeUpdate f x y) :=
  override_isFunction _ _

/-- `FUNCT_4:99` (`Th99`) — `dom(f+~(x,y)) = dom f`. -/
theorem th99 {f x y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    RELAT_1.dom (rangeUpdate f x y) = RELAT_1.dom f :=
  (override_dom f (RELAT_1.comp f (FUNCOP_1.dotArrow x y))).trans
    ((XBOOLE_0.union_comm (RELAT_1.dom f)
        (RELAT_1.dom (RELAT_1.comp f (FUNCOP_1.dotArrow x y)))).trans
      (XBOOLE_1.th12 (RELAT_1.th25 (P := f) (R := FUNCOP_1.dotArrow x y))))

/-- `FUNCT_4:100` (`Th100`) — `x ≠ y → x ∉ rng(f+~(x,y))`. -/
theorem th100 {f x y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hne : x ≠ y) : x ∉ RELAT_1.rng (rangeUpdate f x y) := by
  intro hx
  obtain ⟨z, hz, heq⟩ := (FUNCT_1.def3 (rangeUpdate_isFunction hf x y).2).mp hx
  have hzf : z ∈ RELAT_1.dom f :=
    Eq.subst (motive := fun s => z ∈ s) (th99 hf (x := x) (y := y)) hz
  let g := RELAT_1.comp f (FUNCOP_1.dotArrow x y)
  have hgF : FUNCT_1.isFunction g :=
    FUNCT_1.comp_isFunction hf (FUNCOP_1.dotArrow_isFunction x y)
  have hru : rangeUpdate f x y = override f g := rfl
  exact Or.elim (Classical.em (z ∈ RELAT_1.dom g))
    (fun hzg => by
      have happ : FUNCT_1.apply (rangeUpdate f x y) z = FUNCT_1.apply g z :=
        Eq.subst (motive := fun s => FUNCT_1.apply s z = FUNCT_1.apply g z)
          hru.symm (th13 (f := f) (g := g) hzg)
      have happ2 : FUNCT_1.apply g z =
          FUNCT_1.apply (FUNCOP_1.dotArrow x y) (FUNCT_1.apply f z) :=
        FUNCT_1.th12 hf.2 (FUNCOP_1.dotArrow_isFunction x y).2 hzg
      have heq' : FUNCT_1.apply (FUNCOP_1.dotArrow x y) (FUNCT_1.apply f z) = x :=
        happ2.symm.trans (happ.symm.trans heq.symm)
      have hfxDom : FUNCT_1.apply f z ∈ RELAT_1.dom (FUNCOP_1.dotArrow x y) :=
        ((FUNCT_1.th11 hf.2).mp hzg).2
      have hfxEq : FUNCT_1.apply f z = x :=
        (TARSKI.def1 x (FUNCT_1.apply f z)).mp
          (Eq.subst (motive := fun s => FUNCT_1.apply f z ∈ s)
            (FUNCOP_1.mapsTo_dom _ _) hfxDom)
      have happY : FUNCT_1.apply (FUNCOP_1.dotArrow x y) (FUNCT_1.apply f z) = y :=
        Eq.subst (motive := fun s =>
            FUNCT_1.apply (FUNCOP_1.dotArrow x y) s = y) hfxEq.symm
          (FUNCOP_1.th72 x y)
      exact hne (heq'.symm.trans happY))
    (fun hnzg => by
      have happ : FUNCT_1.apply (rangeUpdate f x y) z = FUNCT_1.apply f z :=
        Eq.subst (motive := fun s => FUNCT_1.apply s z = FUNCT_1.apply f z)
          hru.symm (th11 (f := f) (g := g) hnzg)
      have hfx : FUNCT_1.apply f z = x := happ.symm.trans heq.symm
      have hfxDom : FUNCT_1.apply f z ∈ RELAT_1.dom (FUNCOP_1.dotArrow x y) :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.dom (FUNCOP_1.dotArrow x y))
          hfx.symm
          (Eq.subst (motive := fun s => x ∈ s)
            (FUNCOP_1.mapsTo_dom (TARSKI.singleton x) y).symm
            ((TARSKI.def1 x x).mpr rfl))
      exact hnzg ((FUNCT_1.th11 hf.2).mpr ⟨hzf, hfxDom⟩))

/-- `FUNCT_4:101` — `x ∈ rng f → y ∈ rng(f+~(x,y))`. -/
theorem th101 {f x y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hx : x ∈ RELAT_1.rng f) : y ∈ RELAT_1.rng (rangeUpdate f x y) := by
  obtain ⟨z, hz, heq⟩ := (FUNCT_1.def3 hf.2).mp hx
  let g := RELAT_1.comp f (FUNCOP_1.dotArrow x y)
  have hfxDom : FUNCT_1.apply f z ∈ RELAT_1.dom (FUNCOP_1.dotArrow x y) :=
    Eq.subst (motive := fun s => s ∈ RELAT_1.dom (FUNCOP_1.dotArrow x y))
      heq
      (Eq.subst (motive := fun s => x ∈ s)
        (FUNCOP_1.mapsTo_dom (TARSKI.singleton x) y).symm
        ((TARSKI.def1 x x).mpr rfl))
  have hzg : z ∈ RELAT_1.dom g := (FUNCT_1.th11 hf.2).mpr ⟨hz, hfxDom⟩
  have hsub : RELAT_1.dom g ⊆ RELAT_1.dom (rangeUpdate f x y) :=
    Eq.subst (motive := fun s => RELAT_1.dom g ⊆ s) (th99 hf (x := x) (y := y)).symm
      (RELAT_1.th25 (P := f) (R := FUNCOP_1.dotArrow x y))
  have hzR : z ∈ RELAT_1.dom (rangeUpdate f x y) := hsub _ hzg
  have happ : FUNCT_1.apply (rangeUpdate f x y) z = y := by
    have h1 : FUNCT_1.apply (rangeUpdate f x y) z = FUNCT_1.apply g z :=
      th13 (f := f) (g := g) hzg
    have h2 : FUNCT_1.apply g z =
        FUNCT_1.apply (FUNCOP_1.dotArrow x y) (FUNCT_1.apply f z) :=
      FUNCT_1.th12 hf.2 (FUNCOP_1.dotArrow_isFunction x y).2 hzg
    exact h1.trans (h2.trans
      (Eq.subst (motive := fun s =>
          FUNCT_1.apply (FUNCOP_1.dotArrow x y) s = y) heq
        (FUNCOP_1.th72 x y)))
  exact (FUNCT_1.def3 (rangeUpdate_isFunction hf x y).2).mpr ⟨z, hzR, happ.symm⟩

/-- `FUNCT_4:102` (`Th102`) — `f+~(x,x) = f`. -/
theorem th102 {f x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    rangeUpdate f x x = f := by
  have h1 : rangeUpdate f x x =
      override f (RELAT_1.comp f (RELAT_1.id (TARSKI.singleton x))) :=
    congrArg (fun s => override f (RELAT_1.comp f s)) (th96 x)
  have hsub : RELAT_1.comp f (RELAT_1.id (TARSKI.singleton x)) ⊆ f :=
    RELAT_1.th50.1
  exact h1.trans (th98 (FUNCT_1.comp_isFunction hf (FUNCT_1.id_isFunction _))
    hf hsub)

/-- `FUNCT_4:103` (`Th103`) — `x ∉ rng f → f+~(x,y) = f`. -/
theorem th103 {f x y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hnx : x ∉ RELAT_1.rng f) : rangeUpdate f x y = f := by
  have hdom : RELAT_1.dom (FUNCOP_1.dotArrow x y) = TARSKI.singleton x :=
    FUNCOP_1.mapsTo_dom _ _
  have hmiss : XBOOLE_0.misses (RELAT_1.rng f)
      (RELAT_1.dom (FUNCOP_1.dotArrow x y)) :=
    Eq.subst (motive := fun s => XBOOLE_0.misses (RELAT_1.rng f) s)
      hdom.symm (XBOOLE_0.misses_symm (ZFMISC_1.th50 hnx))
  have hemp : RELAT_1.comp f (FUNCOP_1.dotArrow x y) = (∅ : TarskiSet.{u}) :=
    RELAT_1.th44 (P := FUNCOP_1.dotArrow x y) (R := f) hmiss
  exact Eq.subst (motive := fun s => override f s = f) hemp.symm
    (th21 hf)

/-- `FUNCT_4:104` — `rng(f+~(x,y)) ⊆ (rng f \ {x}) ∪ {y}`. -/
theorem th104 {f x y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    RELAT_1.rng (rangeUpdate f x y) ⊆
      (RELAT_1.rng f \ TARSKI.singleton x) ∪ TARSKI.singleton y := by
  have this := Classical.propDecidable (x ∈ RELAT_1.rng f)
  by_cases hx : x ∈ RELAT_1.rng f
  · have this2 := Classical.propDecidable (x = y)
    by_cases heq : x = y
    · have hru : rangeUpdate f x y = f :=
        Eq.subst (motive := fun s => rangeUpdate f x s = f) heq (th102 hf)
      intro z hz
      have hzf : z ∈ RELAT_1.rng f :=
        Eq.subst (motive := fun s => z ∈ RELAT_1.rng s) hru hz
      exact Eq.subst (motive := fun s =>
          z ∈ (RELAT_1.rng f \ TARSKI.singleton x) ∪ TARSKI.singleton s) heq
        (Eq.subst (motive := fun s => z ∈ s) (ZFMISC_1.th116 hx).symm hzf)
    · have hnx : x ∉ RELAT_1.rng (rangeUpdate f x y) := th100 hf heq
      have hdiff : RELAT_1.rng (rangeUpdate f x y) \
          TARSKI.singleton x = RELAT_1.rng (rangeUpdate f x y) :=
        (ZFMISC_1.th57).mpr hnx
      have hrngDot : RELAT_1.rng (FUNCOP_1.dotArrow x y) = TARSKI.singleton y :=
        FUNCOP_1.th88 x y
      have hcompR : RELAT_1.rng (RELAT_1.comp f (FUNCOP_1.dotArrow x y)) ⊆
          TARSKI.singleton y :=
        Eq.subst (motive := fun s =>
            RELAT_1.rng (RELAT_1.comp f (FUNCOP_1.dotArrow x y)) ⊆ s)
          hrngDot RELAT_1.th26
      have hcomp : RELAT_1.rng f ∪
          RELAT_1.rng (RELAT_1.comp f (FUNCOP_1.dotArrow x y)) ⊆
            RELAT_1.rng f ∪ TARSKI.singleton y :=
        XBOOLE_1.th13 (fun _ hz => hz) hcompR
      have hsub : RELAT_1.rng (rangeUpdate f x y) ⊆
          RELAT_1.rng f ∪ RELAT_1.rng (RELAT_1.comp f (FUNCOP_1.dotArrow x y)) :=
        th17 hf (FUNCT_1.comp_isFunction hf (FUNCOP_1.dotArrow_isFunction x y))
      have h1 : RELAT_1.rng (rangeUpdate f x y) ⊆
          RELAT_1.rng f ∪ TARSKI.singleton y :=
        XBOOLE_1.th1 hsub hcomp
      have h2 : RELAT_1.rng (rangeUpdate f x y) \ TARSKI.singleton x ⊆
          (RELAT_1.rng f ∪ TARSKI.singleton y) \ TARSKI.singleton x :=
        XBOOLE_1.th33 h1
      have h3 : RELAT_1.rng (rangeUpdate f x y) ⊆
          (RELAT_1.rng f ∪ TARSKI.singleton y) \ TARSKI.singleton x :=
        Eq.subst (motive := fun s =>
            s ⊆ (RELAT_1.rng f ∪ TARSKI.singleton y) \ TARSKI.singleton x)
          hdiff h2
      have hne : y ≠ x := fun h => heq h.symm
      exact Eq.subst (motive := fun s =>
          RELAT_1.rng (rangeUpdate f x y) ⊆ s)
        (ZFMISC_1.th123 hne) h3
  · have hru : rangeUpdate f x y = f := th103 hf hx
    intro z hz
    have hzf : z ∈ RELAT_1.rng f :=
      Eq.subst (motive := fun s => z ∈ RELAT_1.rng s) hru hz
    have hsub : RELAT_1.rng f ⊆ RELAT_1.rng f \ TARSKI.singleton x :=
      fun w hw => (XBOOLE_0.def5 _ _ _).mpr ⟨hw, fun hwX =>
        hx (Eq.subst (motive := fun s => s ∈ RELAT_1.rng f)
          ((TARSKI.def1 x w).mp hwX) hw)⟩
    exact (XBOOLE_0.def3 _ _ _).mpr (Or.inl (hsub _ hzf))

/-- `FUNCT_4:105` — `f.z ≠ x → (f+~(x,y)).z = f.z`. -/
theorem th105 {f x y z : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hne : FUNCT_1.apply f z ≠ x) :
    FUNCT_1.apply (rangeUpdate f x y) z = FUNCT_1.apply f z := by
  have hdom : RELAT_1.dom (FUNCOP_1.dotArrow x y) = TARSKI.singleton x :=
    FUNCOP_1.mapsTo_dom _ _
  have hnf : FUNCT_1.apply f z ∉ RELAT_1.dom (FUNCOP_1.dotArrow x y) := fun h =>
    hne ((TARSKI.def1 x (FUNCT_1.apply f z)).mp
      (Eq.subst (motive := fun s => FUNCT_1.apply f z ∈ s) hdom h))
  have hnz : z ∉ RELAT_1.dom (RELAT_1.comp f (FUNCOP_1.dotArrow x y)) := fun hz =>
    hnf ((FUNCT_1.th11 hf.2).mp hz).2
  exact th11 (f := f) (g := RELAT_1.comp f (FUNCOP_1.dotArrow x y)) hnz

/-- `FUNCT_4:106` — `z ∈ dom f ∧ f.z = x → (f+~(x,y)).z = y`. -/
theorem th106 {f x y z : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hz : z ∈ RELAT_1.dom f) (heq : FUNCT_1.apply f z = x) :
    FUNCT_1.apply (rangeUpdate f x y) z = y := by
  have hfxDom : FUNCT_1.apply f z ∈ RELAT_1.dom (FUNCOP_1.dotArrow x y) :=
    Eq.subst (motive := fun s => s ∈ RELAT_1.dom (FUNCOP_1.dotArrow x y))
      heq.symm
      (Eq.subst (motive := fun s => x ∈ s)
        (FUNCOP_1.mapsTo_dom (TARSKI.singleton x) y).symm
        ((TARSKI.def1 x x).mpr rfl))
  have hzg : z ∈ RELAT_1.dom (RELAT_1.comp f (FUNCOP_1.dotArrow x y)) :=
    (FUNCT_1.th11 hf.2).mpr ⟨hz, hfxDom⟩
  have h1 := th13 (f := f)
    (g := RELAT_1.comp f (FUNCOP_1.dotArrow x y)) hzg
  have h2 := FUNCT_1.th12 hf.2 (FUNCOP_1.dotArrow_isFunction x y).2 hzg
  exact h1.trans (h2.trans
    (Eq.subst (motive := fun s =>
        FUNCT_1.apply (FUNCOP_1.dotArrow x y) s = y) heq.symm
      (FUNCOP_1.th72 x y)))

/-- `FUNCT_4:107` — `x ∉ dom f → f ⊆ f +* (x .--> y)`. -/
theorem th107 {f x y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hnx : x ∉ RELAT_1.dom f) :
    f ⊆ override f (FUNCOP_1.dotArrow x y) := by
  have hmiss : XBOOLE_0.misses (RELAT_1.dom f) (TARSKI.singleton x) :=
    XBOOLE_0.misses_symm (ZFMISC_1.th50 hnx)
  have hmiss' : XBOOLE_0.misses (RELAT_1.dom f)
      (RELAT_1.dom (FUNCOP_1.dotArrow x y)) :=
    Eq.subst (motive := fun s => XBOOLE_0.misses (RELAT_1.dom f) s)
      (FUNCOP_1.mapsTo_dom (TARSKI.singleton x) y).symm hmiss
  exact th32 hf (FUNCOP_1.dotArrow_isFunction x y) hmiss'

/-- `FUNCT_4:108` — PartFunc closed under `+* (x.-->y)`. -/
theorem th108 {f X Y x y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (hx : x ∈ X) (hy : y ∈ Y) :
    PARTFUN1.isPartFunc (override f (FUNCOP_1.dotArrow x y)) X Y := by
  have hxX : TARSKI.singleton x ⊆ X := (ZFMISC_1.th31).mpr hx
  have hyY : TARSKI.singleton y ⊆ Y := (ZFMISC_1.th31).mpr hy
  have hrngDot : RELAT_1.rng (FUNCOP_1.dotArrow x y) = TARSKI.singleton y :=
    FUNCOP_1.th88 x y
  have hrngDotY : RELAT_1.rng (FUNCOP_1.dotArrow x y) ⊆ Y :=
    Eq.subst (motive := fun s => s ⊆ Y) hrngDot.symm hyY
  have hrngU : RELAT_1.rng f ∪ RELAT_1.rng (FUNCOP_1.dotArrow x y) ⊆ Y :=
    XBOOLE_1.th8 (RELSET_1.relationOf_valued hf.2) hrngDotY
  have hrng : RELAT_1.rng (override f (FUNCOP_1.dotArrow x y)) ⊆ Y :=
    XBOOLE_1.th1 (th17 hf.1 (FUNCOP_1.dotArrow_isFunction x y)) hrngU
  have hdom : RELAT_1.dom (override f (FUNCOP_1.dotArrow x y)) =
      RELAT_1.dom f ∪ TARSKI.singleton x :=
    (override_dom _ _).trans
      (congrArg (fun s => RELAT_1.dom f ∪ s) (FUNCOP_1.mapsTo_dom _ _))
  have hdomX : RELAT_1.dom (override f (FUNCOP_1.dotArrow x y)) ⊆ X :=
    Eq.subst (motive := fun s => s ⊆ X) hdom.symm
      (XBOOLE_1.th8 (RELSET_1.relationOf_defined hf.2) hxX)
  exact ⟨override_isFunction _ _,
    RELSET_1.th4 (override_isFunction f (FUNCOP_1.dotArrow x y)).1 hdomX hrng⟩

/-- Registration: nonempty override when second (resp. first) is nonempty. -/
theorem override_nonempty_right {f g : TarskiSet.{u}}
    (_hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (hne : ¬ XBOOLE_0.isEmpty g) :
    ¬ XBOOLE_0.isEmpty (override f g) := by
  intro hemp
  have hover0 : override f g = (∅ : TarskiSet.{u}) := XBOOLE_0.empty_eq hemp
  have hd0 : RELAT_1.dom (override f g) = (∅ : TarskiSet.{u}) :=
    Eq.subst (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u}))
      hover0.symm RELAT_1.th38.1
  have hU : RELAT_1.dom f ∪ RELAT_1.dom g = (∅ : TarskiSet.{u}) :=
    (override_dom f g).symm.trans hd0
  have hg0 : RELAT_1.dom g = (∅ : TarskiSet.{u}) :=
    XBOOLE_1.th15
      ((XBOOLE_0.union_comm (RELAT_1.dom g) (RELAT_1.dom f)).trans hU)
  have g0 : g = (∅ : TarskiSet.{u}) := RELAT_1.th41 hg.1 (Or.inl hg0)
  exact hne (Eq.subst (motive := XBOOLE_0.isEmpty) g0.symm
    (fun ⟨x, hx⟩ => ((XBOOLE_0.empty_iff x).mp hx).elim))

theorem override_nonempty_left {f g : TarskiSet.{u}}
    (hf : FUNCT_1.isFunction f) (_hg : FUNCT_1.isFunction g)
    (hne : ¬ XBOOLE_0.isEmpty f) :
    ¬ XBOOLE_0.isEmpty (override g f) :=
  override_nonempty_right (f := g) (g := f) _hg hf hne

/-- Registration: override of non-empty-yielding functions is
non-empty-yielding. -/
theorem override_isEmptyYielding {f g : TarskiSet.{u}}
    (hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (hEf : RELAT_1.isEmptyYielding f) (hEg : RELAT_1.isEmptyYielding g) :
    RELAT_1.isEmptyYielding (override f g) := by
  intro hempty
  obtain ⟨x, hx, heq⟩ :=
    (FUNCT_1.def3 (override_isFunction f g).2).mp hempty
  exact Or.elim ((th12 f g x).mp hx)
    (fun hxf =>
      Or.elim (Classical.em (x ∈ RELAT_1.dom g))
        (fun hxg =>
          hEg ((FUNCT_1.def3 hg.2).mpr
            ⟨x, hxg, heq.trans (th13 (f := f) (g := g) hxg)⟩))
        (fun hnxg =>
          hEf ((FUNCT_1.def3 hf.2).mpr
            ⟨x, hxf, heq.trans (th11 (f := f) (g := g) hnxg)⟩)))
    (fun hxg =>
      hEg ((FUNCT_1.def3 hg.2).mpr
        ⟨x, hxg, heq.trans (th13 (f := f) (g := g) hxg)⟩))

/-- Redefinition: override of partial functions has the same source and
target bounds. -/
theorem override_isPartFunc {f g X Y : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f X Y) (hg : PARTFUN1.isPartFunc g X Y) :
    PARTFUN1.isPartFunc (override f g) X Y := by
  refine PARTFUN1.partFunc_of (override_isFunction f g) ?_ ?_
  · exact Eq.subst (motive := fun s => s ⊆ X) (override_dom f g).symm
      (XBOOLE_1.th8 (RELSET_1.relationOf_defined hf.2)
        (RELSET_1.relationOf_defined hg.2))
  · exact XBOOLE_1.th1 (th17 hf.1 hg.1)
      (XBOOLE_1.th8 (RELSET_1.relationOf_valued hf.2)
        (RELSET_1.relationOf_valued hg.2))

/-- `FUNCT_4:109` — `dom ((x --> y) +* (x .--> z)) = succ x`. -/
theorem th109 (x y z : TarskiSet.{u}) :
    RELAT_1.dom (override (FUNCOP_1.mapsTo x y) (FUNCOP_1.dotArrow x z)) =
      ORDINAL1.succ x := by
  have h1 : RELAT_1.dom (override (FUNCOP_1.mapsTo x y) (FUNCOP_1.dotArrow x z)) =
      RELAT_1.dom (FUNCOP_1.mapsTo x y) ∪ RELAT_1.dom (FUNCOP_1.dotArrow x z) :=
    override_dom _ _
  have h2 : RELAT_1.dom (FUNCOP_1.mapsTo x y) = x := FUNCOP_1.mapsTo_dom x y
  have h3 : RELAT_1.dom (FUNCOP_1.dotArrow x z) = TARSKI.singleton x :=
    FUNCOP_1.mapsTo_dom _ _
  exact h1.trans ((congr_union h2 h3).trans (ORDINAL1.succ_def x).symm)

/-- `FUNCT_4:110` — double succ domain. -/
theorem th110 (x y z : TarskiSet.{u}) :
    RELAT_1.dom (override
      (override (FUNCOP_1.mapsTo x y) (FUNCOP_1.dotArrow x z))
      (FUNCOP_1.dotArrow (ORDINAL1.succ x) z)) =
      ORDINAL1.succ (ORDINAL1.succ x) := by
  have h1 := override_dom
    (override (FUNCOP_1.mapsTo x y) (FUNCOP_1.dotArrow x z))
    (FUNCOP_1.dotArrow (ORDINAL1.succ x) z)
  have h2 := th109 x y z
  have h3 : RELAT_1.dom (FUNCOP_1.dotArrow (ORDINAL1.succ x) z) =
      TARSKI.singleton (ORDINAL1.succ x) := FUNCOP_1.mapsTo_dom _ _
  exact h1.trans ((congr_union h2 h3).trans
    (ORDINAL1.succ_def (ORDINAL1.succ x)).symm)

/-- Registration: override of Function-yielding is Function-yielding. -/
theorem override_isFunctionYielding {f g : TarskiSet.{u}}
    (_hf : FUNCT_1.isFunction f) (_hg : FUNCT_1.isFunction g)
    (hYf : FUNCOP_1.isFunctionYielding f) (hYg : FUNCOP_1.isFunctionYielding g) :
    FUNCOP_1.isFunctionYielding (override f g) := by
  intro x hx
  exact Or.elim ((th12 f g x).mp hx)
    (fun hxf =>
      Or.elim (Classical.em (x ∈ RELAT_1.dom g))
        (fun hxg =>
          Eq.subst (motive := fun s => FUNCT_1.isFunction s)
            (th13 (f := f) (g := g) hxg).symm (hYg x hxg))
        (fun hnxg =>
          Eq.subst (motive := fun s => FUNCT_1.isFunction s)
            (th11 (f := f) (g := g) hnxg).symm (hYf x hxf)))
    (fun hxg =>
      Eq.subst (motive := fun s => FUNCT_1.isFunction s)
        (th13 (f := f) (g := g) hxg).symm (hYg x hxg))

/-- Registration: override preserves I-defined. -/
theorem override_isXdefined {f g I : TarskiSet.{u}}
    (hf : RELAT_1.isXdefined f I) (hg : RELAT_1.isXdefined g I) :
    RELAT_1.isXdefined (override f g) I := by
  intro x hx
  exact Or.elim ((th12 f g x).mp hx) (hf x) (hg x)

/-- Registration: total I-defined override stays total. -/
theorem override_isTotal_left {f g I : TarskiSet.{u}}
    (hf : PARTFUN1.isTotal f I) (hg : RELAT_1.isXdefined g I) :
    PARTFUN1.isTotal (override f g) I := by
  have hdom : RELAT_1.dom (override f g) = I ∪ RELAT_1.dom g :=
    (override_dom f g).trans (congrArg (fun s => s ∪ RELAT_1.dom g) hf)
  exact hdom.trans
    ((XBOOLE_0.union_comm I (RELAT_1.dom g)).trans (XBOOLE_1.th12 hg))

theorem override_isTotal_right {f g I : TarskiSet.{u}}
    (hf : PARTFUN1.isTotal f I) (hg : RELAT_1.isXdefined g I) :
    PARTFUN1.isTotal (override g f) I := by
  have hdom : RELAT_1.dom (override g f) = RELAT_1.dom g ∪ I :=
    (override_dom g f).trans (congrArg (fun s => RELAT_1.dom g ∪ s) hf)
  exact hdom.trans (XBOOLE_1.th12 hg)

/-- Registration: override preserves I-valued. -/
theorem override_isXvalued {f g I : TarskiSet.{u}}
    (hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (hvf : RELAT_1.isXvalued f I) (hvg : RELAT_1.isXvalued g I) :
    RELAT_1.isXvalued (override f g) I :=
  XBOOLE_1.th1 (th17 hf hg) (XBOOLE_1.th8 hvf hvg)

/-- Registration: override preserves f-compatible. -/
theorem override_isCompatible {f g h : TarskiSet.{u}}
    (_hg : FUNCT_1.isFunction g) (_hh : FUNCT_1.isFunction h)
    (hcg : FUNCT_1.isCompatible g f) (hch : FUNCT_1.isCompatible h f) :
    FUNCT_1.isCompatible (override g h) f := by
  intro x hx
  exact Or.elim ((th12 g h x).mp hx)
    (fun hxg =>
      Or.elim (Classical.em (x ∈ RELAT_1.dom h))
        (fun hxh =>
          Eq.subst (motive := fun s => s ∈ FUNCT_1.apply f x)
            (th13 (f := g) (g := h) hxh).symm (hch x hxh))
        (fun hnxh =>
          Eq.subst (motive := fun s => s ∈ FUNCT_1.apply f x)
            (th11 (f := g) (g := h) hnxh).symm (hcg x hxg)))
    (fun hxh =>
      Eq.subst (motive := fun s => s ∈ FUNCT_1.apply f x)
        (th13 (f := g) (g := h) hxh).symm (hch x hxh))

/-- `FUNCT_4:111` — `f|A +* f = f`. -/
theorem th111 {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    override (RELAT_1.restrict f A) f = f :=
  th97 (FUNCT_1.restrict_isFunction (X := A) hf) hf RELAT_1.th59

/-- `FUNCT_4:112` — singleton-dom/rng relation is a dotArrow. -/
theorem th112 {R x y : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hd : RELAT_1.dom R = TARSKI.singleton x)
    (hr : RELAT_1.rng R = TARSKI.singleton y) :
    R = FUNCOP_1.dotArrow x y := by
  have heq : FUNCOP_1.dotArrow x y = TARSKI.singleton (TARSKI.pair x y) :=
    th82 x y
  refine RELAT_1.rel_eq hR (FUNCOP_1.dotArrow_isFunction x y).1 fun a b => ?_
  constructor
  · intro hp
    have ha : a ∈ RELAT_1.dom R := RELAT_1.pair_mem_dom hp
    have hb : b ∈ RELAT_1.rng R := RELAT_1.pair_mem_rng hp
    have haEq : a = x := (TARSKI.def1 x a).mp
      (Eq.subst (motive := fun s => a ∈ s) hd ha)
    have hbEq : b = y := (TARSKI.def1 y b).mp
      (Eq.subst (motive := fun s => b ∈ s) hr hb)
    exact Eq.subst (motive := fun s => TARSKI.pair s b ∈ FUNCOP_1.dotArrow x y)
      haEq.symm
      (Eq.subst (motive := fun s => TARSKI.pair x s ∈ FUNCOP_1.dotArrow x y)
        hbEq.symm
        (Eq.subst (motive := fun s => TARSKI.pair x y ∈ s) heq.symm
          ((TARSKI.def1 (TARSKI.pair x y) (TARSKI.pair x y)).mpr rfl)))
  · intro hp
    have hp' : TARSKI.pair a b ∈ TARSKI.singleton (TARSKI.pair x y) :=
      Eq.subst (motive := fun s => TARSKI.pair a b ∈ s) heq hp
    have heqp : TARSKI.pair a b = TARSKI.pair x y :=
      (TARSKI.def1 (TARSKI.pair x y) (TARSKI.pair a b)).mp hp'
    have ⟨haEq, hbEq⟩ := XTUPLE_0.th1 heqp
    have ha : a ∈ RELAT_1.dom R :=
      Eq.subst (motive := fun s => a ∈ s) hd.symm
        ((TARSKI.def1 x a).mpr haEq)
    obtain ⟨b', hpR⟩ := (RELAT_1.dom_iff R a).mp ha
    have hb' : b' ∈ RELAT_1.rng R := RELAT_1.pair_mem_rng hpR
    have hb'Eq : b' = y := (TARSKI.def1 y b').mp
      (Eq.subst (motive := fun s => b' ∈ s) hr hb')
    exact Eq.subst (motive := fun s => TARSKI.pair a s ∈ R)
      (hb'Eq.trans hbEq.symm) hpR

/-- `FUNCT_4:113` — `(f +* (x .--> y)).x = y`. -/
theorem th113 (f x y : TarskiSet.{u}) :
    FUNCT_1.apply (override f (FUNCOP_1.dotArrow x y)) x = y := by
  have hd : RELAT_1.dom (FUNCOP_1.dotArrow x y) = TARSKI.singleton x :=
    FUNCOP_1.mapsTo_dom _ _
  have hx : x ∈ RELAT_1.dom (FUNCOP_1.dotArrow x y) :=
    Eq.subst (motive := fun s => x ∈ s) hd.symm ((TARSKI.def1 x x).mpr rfl)
  exact (th13 (f := f) (g := FUNCOP_1.dotArrow x y) hx).trans (FUNCOP_1.th72 x y)

/-- `FUNCT_4:114` — cancel successive same-key overrides. -/
theorem th114 (f x z1 z2 : TarskiSet.{u}) :
    override (override f (FUNCOP_1.dotArrow x z1)) (FUNCOP_1.dotArrow x z2) =
      override f (FUNCOP_1.dotArrow x z2) := by
  have hd1 : RELAT_1.dom (FUNCOP_1.dotArrow x z1) = TARSKI.singleton x :=
    FUNCOP_1.mapsTo_dom _ _
  have hd2 : RELAT_1.dom (FUNCOP_1.dotArrow x z2) = TARSKI.singleton x :=
    FUNCOP_1.mapsTo_dom _ _
  exact th74 (FUNCOP_1.dotArrow_isFunction x z1)
    (FUNCOP_1.dotArrow_isFunction x z2) (hd1.trans hd2.symm)

/-- Registration: pairMapsTo is A-defined when a,b ∈ A. -/
theorem pairMapsTo_isXdefined {A a b x y : TarskiSet.{u}}
    (ha : a ∈ A) (hb : b ∈ A) :
    RELAT_1.isXdefined (pairMapsTo a b x y) A := by
  intro z hz
  have hd := (th62 a b x y).1
  have hzU : z ∈ TARSKI.upair a b :=
    Eq.subst (motive := fun s => z ∈ s) hd hz
  exact Or.elim ((TARSKI.def2 a b z).mp hzU)
    (fun heq => Eq.subst (motive := fun s => s ∈ A) heq.symm ha)
    (fun heq => Eq.subst (motive := fun s => s ∈ A) heq.symm hb)

/-- `FUNCT_4:115` — `dom g misses dom h → f+*g+*h+*g = f+*g+*h`. -/
theorem th115 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom g) (RELAT_1.dom h)) :
    override (override (override f g) h) g =
      override (override f g) h := by
  have h1 := th14 f g h
  have h2 : override (override (override f g) h) g =
      override (override f (override g h)) g :=
    congrArg (fun s => override s g) h1
  have h3 : override (override f (override g h)) g =
      override f (override (override g h) g) := th14 f (override g h) g
  have h4 : override (override g h) g = override (override h g) g :=
    congrArg (fun s => override s g) (th35 hg hh hmiss)
  have h5 : override (override h g) g = override h g := th93 hh hg
  have h6 : override h g = override g h := (th35 hg hh hmiss).symm
  exact h2.trans (h3.trans
    ((congrArg (override f) (h4.trans (h5.trans h6))).trans h1.symm))

/-- `FUNCT_4:116` — `dom f misses dom h ∧ f ⊆ g+*h → f ⊆ g`. -/
theorem th116 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f) (RELAT_1.dom h))
    (hsub : f ⊆ override g h) : f ⊆ g := by
  have hrest : RELAT_1.restrict (override g h) (RELAT_1.dom f) =
      RELAT_1.restrict g (RELAT_1.dom f) := by
    have h1 := th71 hg hh (A := RELAT_1.dom f)
    have hmiss' : XBOOLE_0.misses (RELAT_1.dom h) (RELAT_1.dom f) :=
      XBOOLE_0.misses_symm hmiss
    have h0 : RELAT_1.restrict h (RELAT_1.dom f) = (∅ : TarskiSet.{u}) :=
      (RELAT_1.th66 (R := h) (X := RELAT_1.dom f)).mpr hmiss'
    exact h1.trans
      (Eq.subst (motive := fun s =>
          override (RELAT_1.restrict g (RELAT_1.dom f)) s =
            RELAT_1.restrict g (RELAT_1.dom f)) h0.symm
        (th21 (FUNCT_1.restrict_isFunction (X := RELAT_1.dom f) hg)))
  have hfRest : RELAT_1.restrict f (RELAT_1.dom f) = f :=
    RELAT_1.th68 hf.1 (fun _ hx => hx)
  have hsub' : f ⊆ RELAT_1.restrict g (RELAT_1.dom f) :=
    Eq.subst (motive := fun s => f ⊆ s) hrest
      (Eq.subst (motive := fun s => s ⊆ RELAT_1.restrict (override g h)
          (RELAT_1.dom f)) hfRest (RELAT_1.th76 hsub))
  exact (RELAT_1.th184 hf.1).mpr hsub'

/-- `FUNCT_4:117` (`Th117`) — `dom f misses dom h ∧ f ⊆ g → f ⊆ g+*h`. -/
theorem th117 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f) (RELAT_1.dom h))
    (hsub : f ⊆ g) : f ⊆ override g h := by
  have hrest : RELAT_1.restrict (override g h) (RELAT_1.dom f) =
      RELAT_1.restrict g (RELAT_1.dom f) := by
    have h1 := th71 hg hh (A := RELAT_1.dom f)
    have hmiss' : XBOOLE_0.misses (RELAT_1.dom h) (RELAT_1.dom f) :=
      XBOOLE_0.misses_symm hmiss
    have h0 : RELAT_1.restrict h (RELAT_1.dom f) = (∅ : TarskiSet.{u}) :=
      (RELAT_1.th66 (R := h) (X := RELAT_1.dom f)).mpr hmiss'
    exact h1.trans
      (Eq.subst (motive := fun s =>
          override (RELAT_1.restrict g (RELAT_1.dom f)) s =
            RELAT_1.restrict g (RELAT_1.dom f)) h0.symm
        (th21 (FUNCT_1.restrict_isFunction (X := RELAT_1.dom f) hg)))
  have hfRest : RELAT_1.restrict f (RELAT_1.dom f) = f :=
    RELAT_1.th68 hf.1 (fun _ hx => hx)
  have hsub' : f ⊆ RELAT_1.restrict (override g h) (RELAT_1.dom f) :=
    Eq.subst (motive := fun s => f ⊆ s) hrest.symm
      (Eq.subst (motive := fun s => s ⊆ RELAT_1.restrict g (RELAT_1.dom f))
        hfRest (RELAT_1.th76 hsub))
  exact (RELAT_1.th184 hf.1).mpr hsub'

/-- `FUNCT_4:118` — `dom g misses dom h → f+*g+*h = f+*h+*g`. -/
theorem th118 {f g h : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom g) (RELAT_1.dom h)) :
    override (override f g) h = override (override f h) g :=
  (th14 f g h).trans
    ((congrArg (override f) (th35 hg hh hmiss)).trans (th14 f h g).symm)

/-- `FUNCT_4:119` — `dom f misses dom g → (f+*g) \ g = f`. -/
theorem th119 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f) (RELAT_1.dom g)) :
    override f g \ g = f := by
  have hmissR : XBOOLE_0.misses f g := RELAT_1.th179 hf.1 hmiss
  exact
    (congrArg (fun s => s \ g) (th31 hf hg hmiss).symm).trans
      (XBOOLE_1.th88 hmissR)

/-- `FUNCT_4:120` — `dom f misses dom g → f \ g = f`. -/
theorem th120 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f) (RELAT_1.dom g)) :
    f \ g = f :=
  (XBOOLE_1.th83).mp (RELAT_1.th179 hf.1 hmiss)

/-- `FUNCT_4:121` — override commutes with difference from a
domain-disjoint function. -/
theorem th121 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom g) (RELAT_1.dom h)) :
    override (f \ g) h = override f h \ g := by
  have hfd : FUNCT_1.isFunction (f \ g) := GRFUNC_1.diff_isFunction hf
  have hl : FUNCT_1.isFunction (override (f \ g) h) :=
    override_isFunction (f \ g) h
  have hr : FUNCT_1.isFunction (override f h \ g) :=
    GRFUNC_1.diff_isFunction (override_isFunction f h)
  have hdom : RELAT_1.dom (override (f \ g) h) =
      RELAT_1.dom (override f h \ g) := by
    apply eq_of_mem
    intro x
    constructor
    · intro hx
      exact Or.elim ((th12 (f \ g) h x).mp hx)
        (fun hxfd => by
          obtain ⟨y, hp⟩ := (RELAT_1.dom_iff (f \ g) x).mp hxfd
          have ⟨hpf, hnpg⟩ := (XBOOLE_0.def5 f g (TARSKI.pair x y)).mp hp
          have hxf : x ∈ RELAT_1.dom f := RELAT_1.pair_mem_dom hpf
          exact Or.elim (Classical.em (x ∈ RELAT_1.dom h))
            (fun hxh => by
              have hnxg : x ∉ RELAT_1.dom g := fun hxg =>
                ((XBOOLE_0.empty_iff x).mp
                  (Eq.subst (motive := fun s => x ∈ s)
                    ((XBOOLE_0.def7 _ _).mp hmiss)
                    ((XBOOLE_0.def4 _ _ _).mpr ⟨hxg, hxh⟩))).elim
              have hxoh : x ∈ RELAT_1.dom (override f h) :=
                (th12 f h x).mpr (Or.inr hxh)
              have hxd : x ∈ RELAT_1.dom (override f h) \ RELAT_1.dom g :=
                (XBOOLE_0.def5 _ _ _).mpr ⟨hxoh, hnxg⟩
              exact RELAT_1.th3 (P := override f h) (R := g) x hxd)
            (fun hnxh => by
              have hxoh : x ∈ RELAT_1.dom (override f h) :=
                (th12 f h x).mpr (Or.inl hxf)
              have happ : FUNCT_1.apply (override f h) x =
                  FUNCT_1.apply f x := th11 hnxh
              have hpfd : TARSKI.pair x (FUNCT_1.apply f x) ∈ f \ g := by
                have hp' : TARSKI.pair x y ∈ f \ g := hp
                have hy : y = FUNCT_1.apply f x :=
                  (FUNCT_1.apply_of_mem hf.2 hpf).symm
                exact Eq.subst
                  (motive := fun s => TARSKI.pair x s ∈ f \ g) hy hp'
              have hnpg' : TARSKI.pair x (FUNCT_1.apply f x) ∉ g :=
                ((XBOOLE_0.def5 _ _ _).mp hpfd).2
              have hpor : TARSKI.pair x (FUNCT_1.apply f x) ∈
                  override f h :=
                (FUNCT_1.th1 (override_isFunction f h).2).mpr
                  ⟨hxoh, happ.symm⟩
              have hpd : TARSKI.pair x (FUNCT_1.apply f x) ∈
                  override f h \ g :=
                (XBOOLE_0.def5 _ _ _).mpr ⟨hpor, hnpg'⟩
              exact RELAT_1.pair_mem_dom hpd))
        (fun hxh => by
          have hnxg : x ∉ RELAT_1.dom g := fun hxg =>
            ((XBOOLE_0.empty_iff x).mp
              (Eq.subst (motive := fun s => x ∈ s)
                ((XBOOLE_0.def7 _ _).mp hmiss)
                ((XBOOLE_0.def4 _ _ _).mpr ⟨hxg, hxh⟩))).elim
          have hxoh : x ∈ RELAT_1.dom (override f h) :=
            (th12 f h x).mpr (Or.inr hxh)
          exact RELAT_1.th3 (P := override f h) (R := g) x
            ((XBOOLE_0.def5 _ _ _).mpr ⟨hxoh, hnxg⟩))
    · intro hx
      obtain ⟨y, hp⟩ := (RELAT_1.dom_iff (override f h \ g) x).mp hx
      have ⟨hpoh, hnpg⟩ :=
        (XBOOLE_0.def5 (override f h) g (TARSKI.pair x y)).mp hp
      have hxoh : x ∈ RELAT_1.dom (override f h) := RELAT_1.pair_mem_dom hpoh
      exact Or.elim ((th12 f h x).mp hxoh)
        (fun hxf =>
          Or.elim (Classical.em (x ∈ RELAT_1.dom h))
            (fun hxh => (th12 (f \ g) h x).mpr (Or.inr hxh))
            (fun hnxh => by
              have happ : FUNCT_1.apply (override f h) x =
                  FUNCT_1.apply f x := th11 hnxh
              have hy : y = FUNCT_1.apply (override f h) x :=
                (FUNCT_1.apply_of_mem (override_isFunction f h).2 hpoh).symm
              have hpf : TARSKI.pair x (FUNCT_1.apply f x) ∈ f :=
                (FUNCT_1.th1 hf.2).mpr ⟨hxf, rfl⟩
              have hnpg' : TARSKI.pair x (FUNCT_1.apply f x) ∉ g :=
                fun hpg => hnpg
                  (Eq.subst (motive := fun s => TARSKI.pair x s ∈ g)
                    (hy.trans happ).symm hpg)
              have hpfd : TARSKI.pair x (FUNCT_1.apply f x) ∈ f \ g :=
                (XBOOLE_0.def5 _ _ _).mpr ⟨hpf, hnpg'⟩
              exact (th12 (f \ g) h x).mpr
                (Or.inl (RELAT_1.pair_mem_dom hpfd))))
        (fun hxh => (th12 (f \ g) h x).mpr (Or.inr hxh))
  refine FUNCT_1.th2 hl hr hdom ?_
  intro x hx
  exact Or.elim (Classical.em (x ∈ RELAT_1.dom h))
    (fun hxh => by
      have hnxg : x ∉ RELAT_1.dom g := fun hxg =>
        ((XBOOLE_0.empty_iff x).mp
          (Eq.subst (motive := fun s => x ∈ s)
            ((XBOOLE_0.def7 _ _).mp hmiss)
            ((XBOOLE_0.def4 _ _ _).mpr ⟨hxg, hxh⟩))).elim
      have hxoh : x ∈ RELAT_1.dom (override f h) :=
        (th12 f h x).mpr (Or.inr hxh)
      have hxd : x ∈ RELAT_1.dom (override f h) \ RELAT_1.dom g :=
        (XBOOLE_0.def5 _ _ _).mpr ⟨hxoh, hnxg⟩
      exact (th13 (f := f \ g) (g := h) hxh).trans
        ((th13 (f := f) (g := h) hxh).symm.trans
          (GRFUNC_1.th32 (override_isFunction f h) hg hxd).symm))
    (fun hnxh => by
      have hxfd : x ∈ RELAT_1.dom (f \ g) :=
        Or.elim ((th12 (f \ g) h x).mp hx) id
          (fun hxh => (hnxh hxh).elim)
      have hpfd : TARSKI.pair x (FUNCT_1.apply (f \ g) x) ∈ f \ g :=
        FUNCT_1.apply_spec hxfd
      have ⟨hpf, hnpg⟩ := (XBOOLE_0.def5 f g _).mp hpfd
      have hxf : x ∈ RELAT_1.dom f := RELAT_1.pair_mem_dom hpf
      have hxoh : x ∈ RELAT_1.dom (override f h) :=
        (th12 f h x).mpr (Or.inl hxf)
      have happf : FUNCT_1.apply (f \ g) x = FUNCT_1.apply f x :=
        (FUNCT_1.apply_of_mem hf.2 hpf).symm
      have hpor : TARSKI.pair x (FUNCT_1.apply (f \ g) x) ∈ override f h :=
        (FUNCT_1.th1 (override_isFunction f h).2).mpr
          ⟨hxoh, happf.trans (th11 (f := f) (g := h) hnxh).symm⟩
      have hprd : TARSKI.pair x (FUNCT_1.apply (f \ g) x) ∈
          override f h \ g :=
        (XBOOLE_0.def5 _ _ _).mpr ⟨hpor, hnpg⟩
      exact (th11 (f := f \ g) (g := h) hnxh).trans
        (FUNCT_1.apply_of_mem hr.2 hprd).symm)

/-- `FUNCT_4:122` — subset of overrides under miss. -/
theorem th122 {f1 f2 g1 g2 : TarskiSet.{u}}
    (hf1 : FUNCT_1.isFunction f1) (hf2 : FUNCT_1.isFunction f2)
    (hg1 : FUNCT_1.isFunction g1) (hg2 : FUNCT_1.isFunction g2)
    (h1 : f1 ⊆ g1) (h2 : f2 ⊆ g2)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f1) (RELAT_1.dom g2)) :
    override f1 f2 ⊆ override g1 g2 :=
  th87 hf1 hf2 (th117 hf1 hg1 hg2 hmiss h1)
    (XBOOLE_1.th1 h2 (th25 (f := g1) hg2))

/-- `FUNCT_4:123` (`Th123`) — `f ⊆ g → f+*h ⊆ g+*h`. -/
theorem th123 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (hsub : f ⊆ g) : override f h ⊆ override g h := by
  refine (GRFUNC_1.th2 (override_isFunction f h) (override_isFunction g h)).mpr
    ⟨?_, ?_⟩
  · have hd : RELAT_1.dom (override f h) = RELAT_1.dom f ∪ RELAT_1.dom h :=
      override_dom f h
    have hd' : RELAT_1.dom (override g h) = RELAT_1.dom g ∪ RELAT_1.dom h :=
      override_dom g h
    exact Eq.subst (motive := fun s => s ⊆ RELAT_1.dom (override g h)) hd.symm
      (Eq.subst (motive := fun s => RELAT_1.dom f ∪ RELAT_1.dom h ⊆ s) hd'.symm
        (XBOOLE_1.th9 (RELAT_1.th11 hsub).1))
  · intro x hx
    exact Or.elim (Classical.em (x ∈ RELAT_1.dom h))
      (fun hxh =>
        (th13 (f := f) (g := h) hxh).trans (th13 (f := g) (g := h) hxh).symm)
      (fun hnxh => by
        have hxU := (th12 f h x).mp hx
        have hxf : x ∈ RELAT_1.dom f :=
          Or.elim hxU id (fun h => (hnxh h).elim)
        have hxg : x ∈ RELAT_1.dom g := (RELAT_1.th11 hsub).1 _ hxf
        have happ : FUNCT_1.apply f x = FUNCT_1.apply g x :=
          ((GRFUNC_1.th2 hf hg).mp hsub).2 x hxf
        exact (th11 (f := f) (g := h) hnxh).trans
          (happ.trans (th11 (f := g) (g := h) hnxh).symm))

/-- `FUNCT_4:124` — `f ⊆ g ∧ dom f misses dom h → f ⊆ g+*h`. -/
theorem th124 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (hsub : f ⊆ g)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f) (RELAT_1.dom h)) :
    f ⊆ override g h :=
  XBOOLE_1.th1 (th32 hf hh hmiss) (th123 hf hg hh hsub)

/-- Registration: `x .--> y` is trivial. -/
theorem dotArrow_isTrivial (x y : TarskiSet.{u}) :
    ZFMISC_1.isTrivial (FUNCOP_1.dotArrow x y) :=
  Eq.subst (motive := ZFMISC_1.isTrivial) (th82 x y).symm
    (ZFMISC_1.singleton_trivial (TARSKI.pair x y))

/-- `FUNCT_4:125` — tolerates triangle → override tolerates. -/
theorem th125 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (hfg : PARTFUN1.tolerates f g) (hgh : PARTFUN1.tolerates g h)
    (hhf : PARTFUN1.tolerates h f) :
    PARTFUN1.tolerates (override f g) h := by
  intro x hx
  have ⟨hxO, hxh⟩ := (XBOOLE_0.def4 _ _ _).mp hx
  exact Or.elim ((th12 f g x).mp hxO)
    (fun hxf =>
      Or.elim (Classical.em (x ∈ RELAT_1.dom g))
        (fun hxg =>
          (th13 (f := f) (g := g) hxg).trans
            (hgh x ((XBOOLE_0.def4 _ _ _).mpr ⟨hxg, hxh⟩)))
        (fun hnxg =>
          (th11 (f := f) (g := g) hnxg).trans
            (hhf x ((XBOOLE_0.def4 _ _ _).mpr ⟨hxh, hxf⟩)).symm))
    (fun hxg =>
      (th13 (f := f) (g := g) hxg).trans
        (hgh x ((XBOOLE_0.def4 _ _ _).mpr ⟨hxg, hxh⟩)))

end FUNCT_4
