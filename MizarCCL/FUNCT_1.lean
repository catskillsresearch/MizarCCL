import MizarCCL.RELAT_1
import MizarCCL.SETFAM_1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/funct_1.miz`.
Authors: Czesław Byliński (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Functions and Their Basic Properties

1–1 Lean rendering of Mizar article `FUNCT_1`
(`vendor/mml/funct_1.miz`). A function is a function-like relation.
Import is `RELAT_1` and `SETFAM_1` (siblings under `SUBSET_1`).
-/

universe u

open TarskiSet TARSKI RELAT_1

namespace FUNCT_1

variable {X Y A f g h R S x y y1 y2 z : TarskiSet.{u}}

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

/-! ## Function-like (`FUNCT_1:def 1`) -/

def isFunctionLike (IT : TarskiSet.{u}) : Prop :=
  ∀ x y1 y2, TARSKI.pair x y1 ∈ IT → TARSKI.pair x y2 ∈ IT → y1 = y2

theorem def1 (IT : TarskiSet.{u}) :
    isFunctionLike IT ↔
      ∀ x y1 y2, TARSKI.pair x y1 ∈ IT → TARSKI.pair x y2 ∈ IT → y1 = y2 :=
  Iff.rfl

def isFunction (IT : TarskiSet.{u}) : Prop :=
  isRelation IT ∧ isFunctionLike IT

theorem empty_isFunctionLike : isFunctionLike (∅ : TarskiSet.{u}) :=
  fun _ _ _ hp => ((XBOOLE_0.empty_iff _).mp hp).elim

theorem empty_isFunction : isFunction (∅ : TarskiSet.{u}) :=
  ⟨empty_isRelation, empty_isFunctionLike⟩

theorem singleton_pair_isFunctionLike (a b : TarskiSet.{u}) :
    isFunctionLike (TARSKI.singleton (TARSKI.pair a b)) := by
  intro x y1 y2 h1 h2
  have e1 := (singleton_iff (TARSKI.pair a b) (TARSKI.pair x y1)).mp h1
  have e2 := (singleton_iff (TARSKI.pair a b) (TARSKI.pair x y2)).mp h2
  exact (pair_inj.mp e1).2.trans (pair_inj.mp e2).2.symm

theorem singleton_pair_isFunction (a b : TarskiSet.{u}) :
    isFunction (TARSKI.singleton (TARSKI.pair a b)) :=
  ⟨singleton_pair_isRelation a b, singleton_pair_isFunctionLike a b⟩

/-! ## `FUNCT_1:sch GraphFunc` -/

theorem sch_GraphFunc (A : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hfun : ∀ x y1 y2, P x y1 → P x y2 → y1 = y2) :
    ∃ f, isFunction f ∧
      ∀ x y, TARSKI.pair x y ∈ f ↔ x ∈ A ∧ P x y := by
  obtain ⟨Y, hY⟩ := TARSKI.sch1 A (fun x y => P x y) hfun
  obtain ⟨F, hF⟩ :=
    XBOOLE_0.sch_separation (ZFMISC_1.product A Y)
      (fun p => ∃ x y, p = TARSKI.pair x y ∧ P x y)
  refine ⟨F, ?_, ?_⟩
  · constructor
    · intro p hp
      obtain ⟨_, x, y, heq, _⟩ := (hF p).mp hp
      exact ⟨x, y, heq⟩
    · intro x y1 y2 h1 h2
      obtain ⟨_, x1, z1, e1, p1⟩ := (hF _).mp h1
      obtain ⟨_, x2, z2, e2, p2⟩ := (hF _).mp h2
      have ⟨hx1, hy1⟩ := pair_inj.mp e1
      have ⟨hx2, hy2⟩ := pair_inj.mp e2
      exact hfun x y1 y2 (hx1 ▸ hy1 ▸ p1) (hx2 ▸ hy2 ▸ p2)
  · intro x y
    constructor
    · intro hp
      obtain ⟨hpY, x1, y1, heq, hP⟩ := (hF _).mp hp
      have ⟨hx, hy⟩ := pair_inj.mp heq
      have ⟨hxA, _⟩ :=
        (ZFMISC_1.th87 (x := x) (y := y) (X := A) (Y := Y)).mp (heq ▸ hpY)
      exact ⟨hxA, hx ▸ hy ▸ hP⟩
    · intro ⟨hxA, hP⟩
      have hyY : y ∈ Y := (hY y).mpr ⟨x, hxA, hP⟩
      exact (hF (TARSKI.pair x y)).mpr
        ⟨(ZFMISC_1.th87 (x := x) (y := y) (X := A) (Y := Y)).mpr ⟨hxA, hyY⟩,
          ⟨x, y, rfl, hP⟩⟩

/-! ## Application `f.x` (`FUNCT_1:def 2`) -/

noncomputable def apply (f x : TarskiSet.{u}) : TarskiSet.{u} :=
  have := Classical.propDecidable (x ∈ dom f)
  if h : x ∈ dom f then Classical.choose ((dom_iff f x).mp h) else ∅

theorem apply_eq_choose {f x : TarskiSet.{u}} (hx : x ∈ dom f) :
    apply f x = Classical.choose ((dom_iff f x).mp hx) := by
  have := Classical.propDecidable (x ∈ dom f)
  exact dif_pos hx

theorem apply_spec {f x : TarskiSet.{u}} (hx : x ∈ dom f) :
    TARSKI.pair x (apply f x) ∈ f :=
  (apply_eq_choose hx) ▸ Classical.choose_spec ((dom_iff f x).mp hx)

theorem apply_of_mem {f x y : TarskiSet.{u}} (hf : isFunctionLike f)
    (hp : TARSKI.pair x y ∈ f) : apply f x = y :=
  hf x (apply f x) y (apply_spec (pair_mem_dom hp)) hp

theorem apply_of_not_mem {f x : TarskiSet.{u}} (hx : x ∉ dom f) :
    apply f x = (∅ : TarskiSet.{u}) := by
  have := Classical.propDecidable (x ∈ dom f)
  exact dif_neg hx

theorem def2 {f x : TarskiSet.{u}} :
    (x ∈ dom f → TARSKI.pair x (apply f x) ∈ f) ∧
    (x ∉ dom f → apply f x = (∅ : TarskiSet.{u})) :=
  ⟨apply_spec, apply_of_not_mem⟩

/-- `FUNCT_1:1` (`Th1`) -/
theorem th1 {f : TarskiSet.{u}} (hf : isFunctionLike f) :
    TARSKI.pair x y ∈ f ↔ x ∈ dom f ∧ y = apply f x :=
  ⟨fun hp => ⟨pair_mem_dom hp, (apply_of_mem hf hp).symm⟩,
    fun ⟨hx, hy⟩ => hy ▸ apply_spec hx⟩

/-- `FUNCT_1:2` (`Th2`) -/
theorem th2 {f g : TarskiSet.{u}} (hf : isFunction f) (hg : isFunction g)
    (hd : dom f = dom g)
    (hv : ∀ x, x ∈ dom f → apply f x = apply g x) : f = g :=
  rel_eq hf.1 hg.1 fun x y =>
    (th1 hf.2 (x := x) (y := y)).trans <|
      Iff.trans
        ⟨fun ⟨hx, hy⟩ => ⟨hd ▸ hx, (hv x hx ▸ hy : y = apply g x)⟩,
          fun ⟨hx, hy⟩ => ⟨hd ▸ hx, (hv x (hd ▸ hx) ▸ hy : y = apply f x)⟩⟩
        (th1 hg.2 (x := x) (y := y)).symm

/-- `FUNCT_1:def 3` — range via application. -/
theorem def3 {f y : TarskiSet.{u}} (hf : isFunctionLike f) :
    y ∈ rng f ↔ ∃ x, x ∈ dom f ∧ y = apply f x :=
  (rng_iff f y).trans
    ⟨fun ⟨x, hp⟩ => ⟨x, pair_mem_dom hp, (apply_of_mem hf hp).symm⟩,
      fun ⟨x, hx, hy⟩ => ⟨x, hy ▸ apply_spec hx⟩⟩

/-- `FUNCT_1:3` -/
theorem th3 {f x : TarskiSet.{u}} (hf : isFunctionLike f) (hx : x ∈ dom f) :
    apply f x ∈ rng f :=
  (def3 hf).mpr ⟨x, hx, rfl⟩

/-- `FUNCT_1:4` (`Th4`) -/
theorem th4 {f x : TarskiSet.{u}} (hf : isFunctionLike f)
    (hd : dom f = TARSKI.singleton x) :
    rng f = TARSKI.singleton (apply f x) := by
  apply eq_of_mem
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz, heq⟩ := (def3 hf).mp hy
    have hzX : z = x := (singleton_iff x z).mp (hd ▸ hz)
    exact (singleton_iff (apply f x) y).mpr (heq.trans (congrArg (apply f) hzX))
  · intro hy
    have : y = apply f x := (singleton_iff (apply f x) y).mp hy
    exact (def3 hf).mpr ⟨x, hd ▸ (singleton_iff x x).mpr rfl, this⟩

end FUNCT_1
