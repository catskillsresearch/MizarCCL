import MizarCCL.FUNCT_1
import MizarCCL.ENUMSET1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/grfunc_1.miz`.
Authors: Czesław Byliński (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Graphs of Functions

1–1 Lean rendering of Mizar article `GRFUNC_1`
(`vendor/mml/grfunc_1.miz`). A subset of a function is a function.
Import is `FUNCT_1` and `ENUMSET1`. Canceled: `th18`, `th19`.
-/

universe u

open TarskiSet TARSKI

namespace GRFUNC_1

/-- `GRFUNC_1:1` (`Th1`) -/
theorem th1 {G f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) (h : G ⊆ f) :
    FUNCT_1.isFunction G :=
  ⟨fun p hp => hf.1 p (h p hp),
    fun a b1 b2 h1 h2 => hf.2 a b1 b2 (h _ h1) (h _ h2)⟩

/-- `GRFUNC_1:2` (`Th2`) -/
theorem th2 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    f ⊆ g ↔
      RELAT_1.dom f ⊆ RELAT_1.dom g ∧
        ∀ x, x ∈ RELAT_1.dom f → FUNCT_1.apply f x = FUNCT_1.apply g x := by
  constructor
  · intro h
    exact ⟨(RELAT_1.th11 h).1, fun x hx =>
      (FUNCT_1.apply_of_mem (f := g) hg.2 (h _ (FUNCT_1.apply_spec hx))).symm⟩
  · intro ⟨hd, hv⟩
    exact RELAT_1.rel_subset hf.1 fun a b hp =>
      let ha := RELAT_1.pair_mem_dom hp
      (FUNCT_1.th1 hg.2 (x := a) (y := b)).mpr ⟨hd _ ha,
        (FUNCT_1.apply_of_mem hf.2 hp).symm.trans (hv a ha)⟩

/-- `GRFUNC_1:3` -/
theorem th3 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hd : RELAT_1.dom f = RELAT_1.dom g)
    (h : f ⊆ g) : f = g :=
  RELAT_1.rel_eq hf.1 hg.1 fun a b =>
    ⟨fun hp => h _ hp, fun hp =>
      let ha : a ∈ RELAT_1.dom f :=
        Eq.subst (motive := fun d => a ∈ d) hd.symm (RELAT_1.pair_mem_dom hp)
      let hfab := FUNCT_1.apply_spec ha
      let hb : b = FUNCT_1.apply f a :=
        (FUNCT_1.apply_of_mem (f := g) hg.2 hp).symm.trans
          (FUNCT_1.apply_of_mem (f := g) hg.2 (h _ hfab))
      Eq.subst (motive := fun y => TARSKI.pair a y ∈ f) hb.symm hfab⟩

/-- `GRFUNC_1:lm 1` -/
theorem lm1 {f h x y : TarskiSet.{u}} (hf : FUNCT_1.isFunctionLike f)
    (hh : FUNCT_1.isFunctionLike h)
    (hmiss : RELAT_1.rng f ∩ RELAT_1.rng h = (∅ : TarskiSet.{u}))
    (hx : x ∈ RELAT_1.dom f) (hy : y ∈ RELAT_1.dom h) :
    FUNCT_1.apply f x ≠ FUNCT_1.apply h y :=
  fun heq =>
    (XBOOLE_0.empty_iff (FUNCT_1.apply f x)).mp
      (Eq.subst (motive := fun s => FUNCT_1.apply f x ∈ s) hmiss
        ((XBOOLE_0.def4 (RELAT_1.rng f) (RELAT_1.rng h)
          (FUNCT_1.apply f x)).mpr
          ⟨FUNCT_1.th3 hf hx,
            Eq.subst (motive := fun z => z ∈ RELAT_1.rng h) heq.symm
              (FUNCT_1.th3 hh hy)⟩))

/-- `GRFUNC_1:4` -- `[x,z] ∈ g*f` with `g*f = comp f g`. -/
theorem th4 {f g x z : TarskiSet.{u}} (hf : FUNCT_1.isFunctionLike f)
    (hp : TARSKI.pair x z ∈ RELAT_1.comp f g) :
    TARSKI.pair x (FUNCT_1.apply f x) ∈ f ∧
      TARSKI.pair (FUNCT_1.apply f x) z ∈ g :=
  let ⟨_y, hfxy, hgyz⟩ := (RELAT_1.def8 f g x z).mp hp
  let hy := FUNCT_1.apply_of_mem hf hfxy
  ⟨Eq.subst (motive := fun w => TARSKI.pair x w ∈ f) hy.symm hfxy,
    Eq.subst (motive := fun w => TARSKI.pair w z ∈ g) hy.symm hgyz⟩

/-- `GRFUNC_1:5` -/
theorem th5 {x y : TarskiSet.{u}} :
    FUNCT_1.isFunction (TARSKI.singleton (TARSKI.pair x y)) :=
  FUNCT_1.singleton_pair_isFunction x y

/-- `GRFUNC_1:lm 2` -/
theorem lm2 {x y x1 y1 : TarskiSet.{u}}
    (h : TARSKI.pair x y ∈ TARSKI.singleton (TARSKI.pair x1 y1)) :
    x = x1 ∧ y = y1 :=
  pair_inj.mp ((singleton_iff (TARSKI.pair x1 y1) (TARSKI.pair x y)).mp h)

/-- `GRFUNC_1:6` -/
theorem th6 {f x y : TarskiSet.{u}} (hf : FUNCT_1.isFunctionLike f)
    (heq : f = TARSKI.singleton (TARSKI.pair x y)) :
    FUNCT_1.apply f x = y :=
  FUNCT_1.apply_of_mem hf
    (Eq.subst (motive := fun s => TARSKI.pair x y ∈ s) heq.symm
      ((singleton_iff (TARSKI.pair x y) (TARSKI.pair x y)).mpr rfl))

/-- `GRFUNC_1:7` (`Th7`) -/
theorem th7 {f x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hd : RELAT_1.dom f = TARSKI.singleton x) :
    f = TARSKI.singleton (TARSKI.pair x (FUNCT_1.apply f x)) := by
  have hg := FUNCT_1.singleton_pair_isFunction x (FUNCT_1.apply f x)
  exact RELAT_1.rel_eq hf.1 hg.1 fun a b => by
    constructor
    · intro hp
      have ha := RELAT_1.pair_mem_dom hp
      have haX : a = x :=
        (singleton_iff x a).mp
          (Eq.subst (motive := fun d => a ∈ d) hd ha)
      have hb : b = FUNCT_1.apply f x :=
        (FUNCT_1.apply_of_mem hf.2 hp).symm.trans (congrArg (FUNCT_1.apply f) haX)
      exact (singleton_iff (TARSKI.pair x (FUNCT_1.apply f x))
        (TARSKI.pair a b)).mpr
        ((congrArg (TARSKI.pair a) hb).trans
          (congrArg (fun t => TARSKI.pair t (FUNCT_1.apply f x)) haX))
    · intro hp
      have ⟨ha, hb⟩ := lm2 (x := a) (y := b) (x1 := x)
        (y1 := FUNCT_1.apply f x) hp
      have hx : x ∈ RELAT_1.dom f :=
        Eq.subst (motive := fun d => x ∈ d) hd.symm
          ((singleton_iff x x).mpr rfl)
      exact
        Eq.subst (motive := fun t => TARSKI.pair t b ∈ f) ha.symm
          (Eq.subst (motive := fun t => TARSKI.pair x t ∈ f) hb.symm
            (FUNCT_1.apply_spec hx))

/-- `GRFUNC_1:8` -/
theorem th8 {x1 y1 x2 y2 : TarskiSet.{u}} :
    FUNCT_1.isFunction (upair (TARSKI.pair x1 y1) (TARSKI.pair x2 y2)) ↔
      (x1 = x2 → y1 = y2) := by
  constructor
  · intro hf hxy
    have h1 : TARSKI.pair x1 y1 ∈
        upair (TARSKI.pair x1 y1) (TARSKI.pair x2 y2) :=
      (upair_iff _ _ _).mpr (Or.inl rfl)
    have h2 : TARSKI.pair x2 y2 ∈
        upair (TARSKI.pair x1 y1) (TARSKI.pair x2 y2) :=
      (upair_iff _ _ _).mpr (Or.inr rfl)
    exact hf.2 x1 y1 y2 h1 (hxy ▸ h2)
  · intro himp
    refine ⟨?rel, ?funl⟩
    · intro p hp
      exact Or.elim ((upair_iff _ _ p).mp hp)
        (fun heq => ⟨x1, y1, heq⟩)
        (fun heq => ⟨x2, y2, heq⟩)
    · intro a b1 b2 h1 h2
      have e1 := (upair_iff (TARSKI.pair x1 y1) (TARSKI.pair x2 y2)
        (TARSKI.pair a b1)).mp h1
      have e2 := (upair_iff (TARSKI.pair x1 y1) (TARSKI.pair x2 y2)
        (TARSKI.pair a b2)).mp h2
      exact Or.elim e1
        (fun he1 => Or.elim e2
          (fun he2 => (pair_inj.mp he1).2.trans (pair_inj.mp he2).2.symm)
          (fun he2 =>
            let ⟨ha1, hb1⟩ := pair_inj.mp he1
            let ⟨ha2, hb2⟩ := pair_inj.mp he2
            hb1.trans ((himp (ha1.symm.trans ha2)).trans hb2.symm)))
        (fun he1 => Or.elim e2
          (fun he2 =>
            let ⟨ha1, hb1⟩ := pair_inj.mp he1
            let ⟨ha2, hb2⟩ := pair_inj.mp he2
            hb1.trans ((himp (ha2.symm.trans ha1)).symm.trans hb2.symm))
          (fun he2 => (pair_inj.mp he1).2.trans (pair_inj.mp he2).2.symm))

/-- `GRFUNC_1:9` (`Th9`) -/
theorem th9 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    FUNCT_1.isOneToOne f ↔
      ∀ x1 x2 y, TARSKI.pair x1 y ∈ f → TARSKI.pair x2 y ∈ f → x1 = x2 := by
  constructor
  · intro h1 a b c ha hb
    exact h1 a b (RELAT_1.pair_mem_dom ha) (RELAT_1.pair_mem_dom hb)
      ((FUNCT_1.apply_of_mem hf.2 ha).trans (FUNCT_1.apply_of_mem hf.2 hb).symm)
  · intro h a b ha hb heq
    exact h a b (FUNCT_1.apply f a) (FUNCT_1.apply_spec ha)
      (heq ▸ FUNCT_1.apply_spec hb)

/-- `GRFUNC_1:10` (`Th10`) -/
theorem th10 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hsub : g ⊆ f) (h1 : FUNCT_1.isOneToOne f) :
    FUNCT_1.isOneToOne g :=
  (th9 hg).mpr fun a b c ha hb =>
    (th9 hf).mp h1 a b c (hsub _ ha) (hsub _ hb)

theorem inter_isFunction {f X : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    FUNCT_1.isFunction (f ∩ X) :=
  th1 hf (XBOOLE_1.th17 (X := f) (Y := X))

/-- `GRFUNC_1:11` -/
theorem th11 {f g x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hx : x ∈ RELAT_1.dom (f ∩ g)) :
    FUNCT_1.apply (f ∩ g) x = FUNCT_1.apply f x :=
  (FUNCT_1.apply_of_mem (f := f) hf.2
    ((XBOOLE_0.def4 f g (TARSKI.pair x (FUNCT_1.apply (f ∩ g) x))).mp
      (FUNCT_1.apply_spec hx)).1).symm

/-- `GRFUNC_1:12` -/
theorem th12 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g) (h1 : FUNCT_1.isOneToOne f) :
    FUNCT_1.isOneToOne (f ∩ g) :=
  th10 hf (inter_isFunction hf (X := g)) (XBOOLE_1.th17 (X := f) (Y := g)) h1

/-- `GRFUNC_1:13` -/
theorem th13 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (hmiss : XBOOLE_0.misses (RELAT_1.dom f) (RELAT_1.dom g)) :
    FUNCT_1.isFunction (f ∪ g) := by
  have hrel := RELAT_1.union_isRelation hf.1 hg.1
  refine ⟨hrel, fun a b1 b2 h1 h2 => ?_⟩
  have o1 := (XBOOLE_0.def3 f g (TARSKI.pair a b1)).mp h1
  have o2 := (XBOOLE_0.def3 f g (TARSKI.pair a b2)).mp h2
  have hnd : ¬ (a ∈ RELAT_1.dom f ∧ a ∈ RELAT_1.dom g) := fun hd =>
    (XBOOLE_0.empty_iff a).mp
      (Eq.subst (motive := fun s => a ∈ s)
        ((XBOOLE_0.def7 (RELAT_1.dom f) (RELAT_1.dom g)).mp hmiss)
        ((XBOOLE_0.def4 (RELAT_1.dom f) (RELAT_1.dom g) a).mpr hd))
  exact Or.elim o1
    (fun hf1 => Or.elim o2
      (fun hf2 => hf.2 a b1 b2 hf1 hf2)
      (fun hg2 => (hnd ⟨RELAT_1.pair_mem_dom hf1, RELAT_1.pair_mem_dom hg2⟩).elim))
    (fun hg1 => Or.elim o2
      (fun hf2 => (hnd ⟨RELAT_1.pair_mem_dom hf2, RELAT_1.pair_mem_dom hg1⟩).elim)
      (fun hg2 => hg.2 a b1 b2 hg1 hg2))

/-- `GRFUNC_1:14` -/
theorem th14 {f g h : TarskiSet.{u}} (hh : FUNCT_1.isFunction h)
    (hf : f ⊆ h) (hg : g ⊆ h) : FUNCT_1.isFunction (f ∪ g) :=
  th1 hh (XBOOLE_1.th8 (X := f) (Y := g) (Z := h) hf hg)

/-- `GRFUNC_1:lm 3` -/
theorem lm3 {f g h x : TarskiSet.{u}} (heq : h = f ∪ g) :
    x ∈ RELAT_1.dom h ↔ x ∈ RELAT_1.dom f ∨ x ∈ RELAT_1.dom g := by
  have hd : RELAT_1.dom h = RELAT_1.dom f ∪ RELAT_1.dom g :=
    heq ▸ RELAT_1.th1 (P := f) (R := g)
  exact Eq.subst
    (motive := fun d => x ∈ d ↔ x ∈ RELAT_1.dom f ∨ x ∈ RELAT_1.dom g)
    hd.symm (XBOOLE_0.def3 (RELAT_1.dom f) (RELAT_1.dom g) x)

/-- `GRFUNC_1:15` (`Th15`) -/
theorem th15 {f g h x : TarskiSet.{u}} (hh : FUNCT_1.isFunctionLike h)
    (_hg : FUNCT_1.isFunctionLike g)
    (hx : x ∈ RELAT_1.dom g) (heq : h = f ∪ g) :
    FUNCT_1.apply h x = FUNCT_1.apply g x :=
  FUNCT_1.apply_of_mem hh
    (Eq.subst (motive := fun s => TARSKI.pair x (FUNCT_1.apply g x) ∈ s)
      heq.symm
      ((XBOOLE_0.def3 f g (TARSKI.pair x (FUNCT_1.apply g x))).mpr
        (Or.inr (FUNCT_1.apply_spec hx))))

/-- `GRFUNC_1:16` -/
theorem th16 {f g h x : TarskiSet.{u}} (_hh : FUNCT_1.isFunctionLike h)
    (hf : FUNCT_1.isFunctionLike f) (hg : FUNCT_1.isFunctionLike g)
    (hx : x ∈ RELAT_1.dom h) (heq : h = f ∪ g) :
    FUNCT_1.apply h x = FUNCT_1.apply f x ∨
      FUNCT_1.apply h x = FUNCT_1.apply g x :=
  Or.imp
    (fun hpf => (FUNCT_1.apply_of_mem hf hpf).symm)
    (fun hpg => (FUNCT_1.apply_of_mem hg hpg).symm)
    ((XBOOLE_0.def3 f g (TARSKI.pair x (FUNCT_1.apply h x))).mp
      (Eq.subst (motive := fun s => TARSKI.pair x (FUNCT_1.apply h x) ∈ s)
        heq (FUNCT_1.apply_spec hx)))

/-- `GRFUNC_1:17` -/
theorem th17 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (h1f : FUNCT_1.isOneToOne f) (h1g : FUNCT_1.isOneToOne g)
    (heq : h = f ∪ g)
    (hmiss : XBOOLE_0.misses (RELAT_1.rng f) (RELAT_1.rng g)) :
    FUNCT_1.isOneToOne h := by
  intro x1 x2 hx1 hx2 happ
  have hmiss' : RELAT_1.rng f ∩ RELAT_1.rng g = (∅ : TarskiSet.{u}) :=
    (XBOOLE_0.def7 (RELAT_1.rng f) (RELAT_1.rng g)).mp hmiss
  have hapg : ∀ x, x ∈ RELAT_1.dom g →
      FUNCT_1.apply h x = FUNCT_1.apply g x :=
    fun x hx => th15 hh.2 hg.2 hx heq
  have hapf : ∀ x, x ∈ RELAT_1.dom f →
      FUNCT_1.apply h x = FUNCT_1.apply f x :=
    fun x hx => th15 hh.2 hf.2 hx (heq.trans (XBOOLE_0.union_comm f g))
  have o1 := (lm3 (f := f) (g := g) (h := h) (x := x1) heq).mp hx1
  have o2 := (lm3 (f := f) (g := g) (h := h) (x := x2) heq).mp hx2
  have hmix :
      ¬ ((x1 ∈ RELAT_1.dom f ∧ x2 ∈ RELAT_1.dom g) ∨
          (x1 ∈ RELAT_1.dom g ∧ x2 ∈ RELAT_1.dom f)) := by
    intro hm
    exact Or.elim hm
      (fun ⟨hf1, hg2⟩ =>
        lm1 hf.2 hg.2 hmiss' hf1 hg2
          ((hapf x1 hf1).symm.trans (happ.trans (hapg x2 hg2))))
      (fun ⟨hg1, hf2⟩ =>
        lm1 hf.2 hg.2 hmiss' hf2 hg1
          ((hapf x2 hf2).symm.trans (happ.symm.trans (hapg x1 hg1))))
  exact Or.elim o1
    (fun hf1 => Or.elim o2
      (fun hf2 => h1f x1 x2 hf1 hf2
        ((hapf x1 hf1).symm.trans (happ.trans (hapf x2 hf2))))
      (fun hg2 => (hmix (Or.inl ⟨hf1, hg2⟩)).elim))
    (fun hg1 => Or.elim o2
      (fun hf2 => (hmix (Or.inr ⟨hg1, hf2⟩)).elim)
      (fun hg2 => h1g x1 x2 hg1 hg2
        ((hapg x1 hg1).symm.trans (happ.trans (hapg x2 hg2)))))

/-- `GRFUNC_1:20` -- canceled `18`, `19`. -/
theorem th20 {f x y : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f)
    (_h1 : FUNCT_1.isOneToOne f) :
    TARSKI.pair y x ∈ FUNCT_1.inv f ↔ TARSKI.pair x y ∈ f :=
  RELAT_1.def7 f y x

/-- `GRFUNC_1:21` -/
theorem th21 {f : TarskiSet.{u}} (heq : f = (∅ : TarskiSet.{u})) :
    FUNCT_1.inv f = (∅ : TarskiSet.{u}) :=
  heq ▸ RELAT_1.th43

/-- `GRFUNC_1:22` -/
theorem th22 {f X x : TarskiSet.{u}} :
    (x ∈ RELAT_1.dom f ∧ x ∈ X) ↔
      TARSKI.pair x (FUNCT_1.apply f x) ∈ RELAT_1.restrict f X :=
  Iff.trans
    ⟨fun ⟨hd, hx⟩ => ⟨hx, FUNCT_1.apply_spec hd⟩,
      fun ⟨hx, hp⟩ => ⟨RELAT_1.pair_mem_dom hp, hx⟩⟩
    (RELAT_1.def11 f X x (FUNCT_1.apply f x)).symm

/-- `GRFUNC_1:23` (`Th23`) -/
theorem th23 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hsub : g ⊆ f) :
    RELAT_1.restrict f (RELAT_1.dom g) = g := by
  have hfg : RELAT_1.restrict f (RELAT_1.dom g) ⊆ g :=
    RELAT_1.rel_subset (RELAT_1.restrict_isRelation f (RELAT_1.dom g))
      fun a b hp =>
        let ⟨ha, hpf⟩ := (RELAT_1.def11 f (RELAT_1.dom g) a b).mp hp
        let hpg := FUNCT_1.apply_spec ha
        Eq.subst (motive := fun y => TARSKI.pair a y ∈ g)
          (hf.2 a (FUNCT_1.apply g a) b (hsub _ hpg) hpf) hpg
  have hgf : g ⊆ RELAT_1.restrict f (RELAT_1.dom g) :=
    Eq.subst (motive := fun s => s ⊆ RELAT_1.restrict f (RELAT_1.dom g))
      (RELAT_1.th69 hg.1) (RELAT_1.th76 (X := RELAT_1.dom g) hsub)
  exact (XBOOLE_0.def10).mpr ⟨hfg, hgf⟩

/-- `GRFUNC_1:24` -/
theorem th24 {f Y x : TarskiSet.{u}} :
    (x ∈ RELAT_1.dom f ∧ FUNCT_1.apply f x ∈ Y) ↔
      TARSKI.pair x (FUNCT_1.apply f x) ∈ RELAT_1.restrictRng Y f :=
  Iff.trans
    ⟨fun ⟨hd, hy⟩ => ⟨hy, FUNCT_1.apply_spec hd⟩,
      fun ⟨hy, hp⟩ => ⟨RELAT_1.pair_mem_dom hp, hy⟩⟩
    (RELAT_1.def12 Y f x (FUNCT_1.apply f x)).symm

/-- `GRFUNC_1:25` -/
theorem th25 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hsub : g ⊆ f) (h1 : FUNCT_1.isOneToOne f) :
    RELAT_1.restrictRng (RELAT_1.rng g) f = g := by
  have hfg : RELAT_1.restrictRng (RELAT_1.rng g) f ⊆ g :=
    RELAT_1.rel_subset (RELAT_1.restrictRng_isRelation (RELAT_1.rng g) f)
      fun a b hp =>
        let ⟨hb, hpf⟩ := (RELAT_1.def12 (RELAT_1.rng g) f a b).mp hp
        let ⟨x1, hpg⟩ := (RELAT_1.rng_iff g b).mp hb
        Eq.subst (motive := fun z => TARSKI.pair z b ∈ g)
          ((th9 hf).mp h1 x1 a b (hsub _ hpg) hpf) hpg
  have hgf : g ⊆ RELAT_1.restrictRng (RELAT_1.rng g) f :=
    Eq.subst (motive := fun s => s ⊆ RELAT_1.restrictRng (RELAT_1.rng g) f)
      (RELAT_1.th95 hg.1) (RELAT_1.th101 (Y := RELAT_1.rng g) hsub)
  exact (XBOOLE_0.def10).mpr ⟨hfg, hgf⟩

/-- `GRFUNC_1:26` -/
theorem th26 {f Y x : TarskiSet.{u}} (hf : FUNCT_1.isFunctionLike f) :
    x ∈ RELAT_1.invimage f Y ↔
      TARSKI.pair x (FUNCT_1.apply f x) ∈ f ∧ FUNCT_1.apply f x ∈ Y := by
  constructor
  · intro hx
    obtain ⟨y, hp, hy⟩ := (RELAT_1.def14 f Y x).mp hx
    have heq := FUNCT_1.apply_of_mem hf hp
    exact ⟨Eq.subst (motive := fun z => TARSKI.pair x z ∈ f) heq.symm hp,
      Eq.subst (motive := fun z => z ∈ Y) heq.symm hy⟩
  · intro ⟨hp, hy⟩
    exact (RELAT_1.def14 f Y x).mpr ⟨FUNCT_1.apply f x, hp, hy⟩

/-- `GRFUNC_1:27` -/
theorem th27 {X f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hX : X ⊆ RELAT_1.dom f) (hsub : f ⊆ g) :
    RELAT_1.restrict f X = RELAT_1.restrict g X :=
  ((congrArg (fun s => RELAT_1.restrict s X) (th23 hg hf hsub).symm).trans
    (RELAT_1.th71 (R := g) (X := RELAT_1.dom f) (Y := X))).trans
    (congrArg (RELAT_1.restrict g)
      ((XBOOLE_0.inter_comm (RELAT_1.dom f) X).trans (XBOOLE_1.th28 hX)))

/-- `GRFUNC_1:28` (`Th28`) -/
theorem th28 {f x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hx : x ∈ RELAT_1.dom f) :
    RELAT_1.restrict f (TARSKI.singleton x) =
      TARSKI.singleton (TARSKI.pair x (FUNCT_1.apply f x)) := by
  have hd : RELAT_1.dom (RELAT_1.restrict f (TARSKI.singleton x)) =
      TARSKI.singleton x :=
    (RELAT_1.th61 (R := f) (X := TARSKI.singleton x)).trans
      (ZFMISC_1.th46 hx)
  have hr := FUNCT_1.restrict_isFunction hf (X := TARSKI.singleton x)
  have hxS : x ∈ TARSKI.singleton x := (singleton_iff x x).mpr rfl
  exact (th7 hr hd).trans
    (congrArg (fun y => TARSKI.singleton (TARSKI.pair x y))
      (FUNCT_1.th49 hf.2 hxS))

/-- `GRFUNC_1:29` (`Th29`) -/
theorem th29 {f g x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hd : RELAT_1.dom f = RELAT_1.dom g)
    (heq : FUNCT_1.apply f x = FUNCT_1.apply g x) :
    RELAT_1.restrict f (TARSKI.singleton x) =
      RELAT_1.restrict g (TARSKI.singleton x) := by
  by_cases hx : x ∈ RELAT_1.dom f
  · have hxg : x ∈ RELAT_1.dom g :=
      Eq.subst (motive := fun d => x ∈ d) hd hx
    exact (th28 hf hx).trans
      ((congrArg (fun y => TARSKI.singleton (TARSKI.pair x y)) heq).trans
        (th28 hg hxg).symm)
  · have hxf := ZFMISC_1.th50 hx
    have hxg := ZFMISC_1.th50
      (show x ∉ RELAT_1.dom g from fun h =>
        hx (Eq.subst (motive := fun d => x ∈ d) hd.symm h))
    exact ((RELAT_1.th66 (R := f) (X := TARSKI.singleton x)).mpr
        (XBOOLE_0.misses_symm hxf)).trans
      ((RELAT_1.th66 (R := g) (X := TARSKI.singleton x)).mpr
        (XBOOLE_0.misses_symm hxg)).symm

/-- `GRFUNC_1:30` (`Th30`) -/
theorem th30 {f g x y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hd : RELAT_1.dom f = RELAT_1.dom g)
    (hx : FUNCT_1.apply f x = FUNCT_1.apply g x)
    (hy : FUNCT_1.apply f y = FUNCT_1.apply g y) :
    RELAT_1.restrict f (upair x y) = RELAT_1.restrict g (upair x y) :=
  let h1 := th29 hf hg hd hx
  let h2 := th29 hf hg hd hy
  ENUMSET1.th1 (x1 := x) (x2 := y) ▸
    RELAT_1.th150 (f := f) (g := g) (A := TARSKI.singleton x)
      (B := TARSKI.singleton y) h1 h2

/-- `GRFUNC_1:31` -/
theorem th31 {f g x y z : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hd : RELAT_1.dom f = RELAT_1.dom g)
    (hx : FUNCT_1.apply f x = FUNCT_1.apply g x)
    (hy : FUNCT_1.apply f y = FUNCT_1.apply g y)
    (hz : FUNCT_1.apply f z = FUNCT_1.apply g z) :
    RELAT_1.restrict f (ENUMSET1.enumset3 x y z) =
      RELAT_1.restrict g (ENUMSET1.enumset3 x y z) :=
  let h1 := th30 hf hg hd hx hy
  let h2 := th29 hf hg hd hz
  ENUMSET1.th3 (x1 := x) (x2 := y) (x3 := z) ▸
    RELAT_1.th150 (f := f) (g := g) (A := upair x y)
      (B := TARSKI.singleton z) h1 h2

theorem diff_isFunction {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    FUNCT_1.isFunction (f \ A) :=
  th1 hf (XBOOLE_1.th36 (X := f) (Y := A))

/-- `GRFUNC_1:32` -/
theorem th32 {f g x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g) (hx : x ∈ RELAT_1.dom f \ RELAT_1.dom g) :
    FUNCT_1.apply (f \ g) x = FUNCT_1.apply f x :=
  ((th2 (diff_isFunction hf (A := g)) hf).mp
    (XBOOLE_1.th36 (X := f) (Y := g))).2 x
    (RELAT_1.th3 (P := f) (R := g) x hx)

/-- `GRFUNC_1:33` -/
theorem th33 {f g h : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hh : FUNCT_1.isFunction h)
    (hfg : f ⊆ g) (hfh : f ⊆ h) :
    RELAT_1.restrict g (RELAT_1.dom f) = RELAT_1.restrict h (RELAT_1.dom f) :=
  (th23 hg hf hfg).trans (th23 hh hf hfh).symm

/-- `GRFUNC_1:34` (`Th34`) -/
theorem th34 {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hsub : g ⊆ f) :
    g = RELAT_1.restrict f (RELAT_1.dom g) :=
  (th23 hf hg hsub).symm

theorem compatible_of_subset {f g F : TarskiSet.{u}}
    (hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (_hF : FUNCT_1.isFunction F) (hsub : g ⊆ f)
    (hcomp : FUNCT_1.isCompatible F g) : FUNCT_1.isCompatible F f := by
  intro x hx
  have hFxg : FUNCT_1.apply F x ∈ FUNCT_1.apply g x := hcomp x hx
  have hxg : x ∈ RELAT_1.dom g :=
    Classical.byContradiction fun hnd =>
      (XBOOLE_0.empty_iff (FUNCT_1.apply F x)).mp
        (Eq.subst (motive := fun s => FUNCT_1.apply F x ∈ s)
          (FUNCT_1.apply_of_not_mem hnd) hFxg)
  exact Eq.subst (motive := fun s => FUNCT_1.apply F x ∈ s)
    (((th2 hg hf).mp hsub).2 x hxg) hFxg

theorem compatible_subset {f g h : TarskiSet.{u}}
    (_hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (hh : FUNCT_1.isFunction h) (hsub : h ⊆ g)
    (hcomp : FUNCT_1.isCompatible g f) : FUNCT_1.isCompatible h f :=
  fun x hx =>
    let ⟨hd, hv⟩ := (th2 hh hg).mp hsub
    Eq.subst (motive := fun s => s ∈ FUNCT_1.apply f x) (hv x hx).symm
      (hcomp x (hd x hx))

/-- `GRFUNC_1:35` -/
theorem th35 {f g X x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hsub : g ⊆ f) (hxX : x ∈ X)
    (hXg : X ∩ RELAT_1.dom f ⊆ RELAT_1.dom g) :
    FUNCT_1.apply f x = FUNCT_1.apply g x := by
  by_cases hx : x ∈ RELAT_1.dom g
  · exact (((th2 hg hf).mp hsub).2 x hx).symm
  · have hndf : x ∉ RELAT_1.dom f := fun hdf =>
      hx (hXg x ((XBOOLE_0.def4 X (RELAT_1.dom f) x).mpr ⟨hxX, hdf⟩))
    exact (FUNCT_1.apply_of_not_mem hndf).trans
      (FUNCT_1.apply_of_not_mem hx).symm

end GRFUNC_1
