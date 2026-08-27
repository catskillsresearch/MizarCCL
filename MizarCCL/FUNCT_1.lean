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

private theorem exists_mem_of_ne {A : TarskiSet.{u}}
    (h : A ≠ (∅ : TarskiSet.{u})) : ∃ x, x ∈ A :=
  Classical.byContradiction fun hne =>
    h (XBOOLE_0.empty_eq (fun hex => hne hex))

/-! ## `FUNCT_1:sch FuncEx` and `Lambda` -/

theorem sch_FuncEx (A : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hfun : ∀ x y1 y2, x ∈ A → P x y1 → P x y2 → y1 = y2)
    (hex : ∀ x, x ∈ A → ∃ y, P x y) :
    ∃ f, isFunction f ∧ dom f = A ∧ ∀ x, x ∈ A → P x (apply f x) := by
  obtain ⟨f, hf, hchar⟩ :=
    sch_GraphFunc A (fun x y => x ∈ A ∧ P x y)
      (fun x _ _ hp1 hp2 => hfun x _ _ hp1.1 hp1.2 hp2.2)
  have hdom : dom f = A := by
    apply eq_of_mem
    intro x
    constructor
    · intro hx
      obtain ⟨y, hp⟩ := (dom_iff f x).mp hx
      exact ((hchar x y).mp hp).1
    · intro hx
      obtain ⟨y, hP⟩ := hex x hx
      exact (dom_iff f x).mpr ⟨y, (hchar x y).mpr ⟨hx, hx, hP⟩⟩
  refine ⟨f, hf, hdom, ?_⟩
  intro x hx
  have hp := apply_spec (hdom ▸ hx)
  exact ((hchar x (apply f x)).mp hp).2.2

theorem sch_Lambda (A : TarskiSet.{u}) (F : TarskiSet.{u} → TarskiSet.{u}) :
    ∃ f, isFunction f ∧ dom f = A ∧ ∀ x, x ∈ A → apply f x = F x :=
  sch_FuncEx A (fun x y => y = F x)
    (fun _ y1 y2 _ h1 h2 => h1.trans h2.symm)
    (fun x _ => ⟨F x, rfl⟩)

theorem id_isFunctionLike (X : TarskiSet.{u}) : isFunctionLike (RELAT_1.id X) :=
  fun x y1 y2 h1 h2 =>
    ((def10 X x y1).mp h1).2.symm.trans ((def10 X x y2).mp h2).2

theorem id_isFunction (X : TarskiSet.{u}) : isFunction (RELAT_1.id X) :=
  ⟨id_isRelation X, id_isFunctionLike X⟩

theorem id_apply (hx : x ∈ X) : apply (RELAT_1.id X) x = x :=
  apply_of_mem (id_isFunctionLike X) ((def10 X x x).mpr ⟨hx, rfl⟩)

/-- FUNCT_1 writes `g*f` for `RELAT_1.comp f g` (apply `f` then `g`). -/
theorem comp_isFunctionLike {f g : TarskiSet.{u}}
    (hf : isFunctionLike f) (hg : isFunctionLike g) :
    isFunctionLike (comp f g) :=
  fun x y1 y2 h1 h2 =>
    let ⟨z1, hf1, hg1⟩ := (def8 f g x y1).mp h1
    let ⟨z2, hf2, hg2⟩ := (def8 f g x y2).mp h2
    have hz : z1 = z2 := hf x z1 z2 hf1 hf2
    hg z1 y1 y2 hg1 (hz ▸ hg2)

theorem comp_isFunction {f g : TarskiSet.{u}}
    (hf : isFunction f) (hg : isFunction g) : isFunction (comp f g) :=
  ⟨comp_isRelation f g, comp_isFunctionLike hf.2 hg.2⟩

/-- `FUNCT_1:5` (`Th5`) -/
theorem th5 (hX : X ≠ (∅ : TarskiSet.{u})) (y : TarskiSet.{u}) :
    ∃ f, isFunction f ∧ dom f = X ∧ rng f = TARSKI.singleton y := by
  obtain ⟨f, hf, hdom, hv⟩ := sch_Lambda X (fun _ => y)
  refine ⟨f, hf, hdom, ?_⟩
  apply eq_of_mem
  intro y1
  constructor
  · intro hy
    obtain ⟨x, hx, heq⟩ := (def3 hf.2).mp hy
    exact (singleton_iff y y1).mpr (heq.trans (hv x (hdom ▸ hx)))
  · intro hy
    have hyy : y1 = y := (singleton_iff y y1).mp hy
    obtain ⟨x, hx⟩ := exists_mem_of_ne hX
    exact (def3 hf.2).mpr ⟨x, hdom ▸ hx, hyy.trans (hv x hx).symm⟩

/-- `FUNCT_1:6` -/
theorem th6 (h : ∀ f g, isFunction f → isFunction g →
    dom f = X → dom g = X → f = g) : X = (∅ : TarskiSet.{u}) := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨f, hf, hfd, hfv⟩ := sch_Lambda X (fun _ => (∅ : TarskiSet.{u}))
  obtain ⟨g, hg, hgd, hgv⟩ :=
    sch_Lambda X (fun _ => TARSKI.singleton (∅ : TarskiSet.{u}))
  obtain ⟨x, hx⟩ := exists_mem_of_ne hne
  have heq : (∅ : TarskiSet.{u}) = TARSKI.singleton (∅ : TarskiSet.{u}) :=
    (hfv x hx).symm.trans
      ((congrArg (fun s => apply s x) (h f g hf hg hfd hgd)).trans (hgv x hx))
  exact (XBOOLE_0.singleton_nonempty (∅ : TarskiSet.{u}))
    (heq ▸ XBOOLE_0.emptySet_isEmpty)

/-- `FUNCT_1:7` -/
theorem th7 {f g y : TarskiSet.{u}} (hf : isFunction f) (hg : isFunction g)
    (hd : dom f = dom g)
    (hrf : rng f = TARSKI.singleton y)
    (hrg : rng g = TARSKI.singleton y) : f = g :=
  th2 hf hg hd fun x hx =>
    ((singleton_iff y (apply f x)).mp (hrf ▸ th3 hf.2 hx)).trans
      ((singleton_iff y (apply g x)).mp (hrg ▸ th3 hg.2 (hd ▸ hx))).symm

/-- `FUNCT_1:8` -/
theorem th8 (h : Y ≠ (∅ : TarskiSet.{u}) ∨ X = (∅ : TarskiSet.{u})) :
    ∃ f, isFunction f ∧ X = dom f ∧ rng f ⊆ Y := by
  rcases h with hY | hX
  · obtain ⟨y, hy⟩ := exists_mem_of_ne hY
    obtain ⟨f, hf, hdom, hv⟩ := sch_Lambda X (fun _ => y)
    refine ⟨f, hf, hdom.symm, ?_⟩
    intro z hz
    obtain ⟨x, hx, heq⟩ := (def3 hf.2).mp hz
    exact heq ▸ (hv x (hdom ▸ hx)) ▸ hy
  · refine ⟨∅, empty_isFunction, hX.trans th38.1.symm, ?_⟩
    exact Eq.subst (motive := fun s => s ⊆ Y) th38.2.symm
      (XBOOLE_1.th2 (X := Y))

/-- `FUNCT_1:9` -/
theorem th9 {f Y : TarskiSet.{u}} (hf : isFunctionLike f)
    (h : ∀ y, y ∈ Y → ∃ x, x ∈ dom f ∧ y = apply f x) : Y ⊆ rng f :=
  fun y hy => (def3 hf).mpr (h y hy)

/-- `FUNCT_1:11` (`Th11`) — `x ∈ dom (g*f)` with `g*f = comp f g`. -/
theorem th11 {f g x : TarskiSet.{u}} (hf : isFunctionLike f) :
    x ∈ dom (comp f g) ↔ x ∈ dom f ∧ apply f x ∈ dom g := by
  constructor
  · intro hx
    obtain ⟨y, hp⟩ := (dom_iff (comp f g) x).mp hx
    obtain ⟨z, hfz, hgz⟩ := (def8 f g x y).mp hp
    exact ⟨pair_mem_dom hfz, apply_of_mem hf hfz ▸ pair_mem_dom hgz⟩
  · intro ⟨hx, hfx⟩
    obtain ⟨y, hgy⟩ := (dom_iff g (apply f x)).mp hfx
    exact (dom_iff (comp f g) x).mpr
      ⟨y, (def8 f g x y).mpr ⟨apply f x, apply_spec hx, hgy⟩⟩

/-- `FUNCT_1:12` (`Th12`) -/
theorem th12 {f g x : TarskiSet.{u}} (hf : isFunctionLike f)
    (hg : isFunctionLike g) (hx : x ∈ dom (comp f g)) :
    apply (comp f g) x = apply g (apply f x) := by
  obtain ⟨y, hp⟩ := (dom_iff (comp f g) x).mp hx
  obtain ⟨z, hfz, hgz⟩ := (def8 f g x y).mp hp
  have hz : z = apply f x := (apply_of_mem hf hfz).symm
  have hy : y = apply g (apply f x) :=
    hz ▸ (apply_of_mem hg hgz).symm
  exact (apply_of_mem (comp_isFunctionLike hf hg) hp).trans hy

/-- `FUNCT_1:13` (`Th13`) -/
theorem th13 {f g x : TarskiSet.{u}} (hf : isFunctionLike f)
    (hg : isFunctionLike g) (hx : x ∈ dom f) :
    apply (comp f g) x = apply g (apply f x) := by
  by_cases hfx : apply f x ∈ dom g
  · exact th12 hf hg ((th11 hf).mpr ⟨hx, hfx⟩)
  · have hnc : x ∉ dom (comp f g) := fun hc => hfx ((th11 hf).mp hc).2
    exact (apply_of_not_mem hnc).trans (apply_of_not_mem hfx).symm

/-- `FUNCT_1:10` -/
theorem th10 {f g h : TarskiSet.{u}} (hf : isFunction f) (hg : isFunction g)
    (hh : isFunction h)
    (hd : ∀ x, x ∈ dom h ↔ x ∈ dom f ∧ apply f x ∈ dom g)
    (hv : ∀ x, x ∈ dom h → apply h x = apply g (apply f x)) :
    h = comp f g :=
  th2 hh (comp_isFunction hf hg)
    (eq_of_mem fun x => (hd x).trans (th11 hf.2 (f := f) (g := g) (x := x)).symm)
    fun x hx => (hv x hx).trans (th12 hf.2 hg.2 ((th11 hf.2).mpr ((hd x).mp hx))).symm

/-- `FUNCT_1:14` -/
theorem th14 {f g z : TarskiSet.{u}} (hf : isFunctionLike f)
    (hg : isFunctionLike g) (hz : z ∈ rng (comp f g)) : z ∈ rng g := by
  obtain ⟨x, hx, heq⟩ := (def3 (comp_isFunctionLike hf hg)).mp hz
  have hfx := ((th11 hf).mp hx).2
  exact (def3 hg).mpr ⟨apply f x, hfx, heq.trans (th12 hf hg hx)⟩

/-- `FUNCT_1:15` (`Th15`) -/
theorem th15 {f g : TarskiSet.{u}} (hf : isFunctionLike f)
    (h : dom (comp f g) = dom f) : rng f ⊆ dom g :=
  fun _ hy =>
    let ⟨_, hx, heq⟩ := (def3 hf).mp hy
    heq ▸ ((th11 (f := f) (g := g) hf).mp (h ▸ hx)).2

/-- `FUNCT_1:17` (`Th17`) -/
theorem th17 {f X : TarskiSet.{u}} (hf : isFunction f) :
    f = RELAT_1.id X ↔ dom f = X ∧ ∀ x, x ∈ X → apply f x = x := by
  constructor
  · intro h
    exact ⟨h ▸ id_dom X, fun x hx => h ▸ id_apply hx⟩
  · intro ⟨hd, hv⟩
    exact th2 hf (id_isFunction X) (hd.trans (id_dom X).symm) fun x hx =>
      (hv x (hd ▸ hx)).trans (id_apply (hd ▸ hx)).symm

/-- `FUNCT_1:18` -/
theorem th18 (hx : x ∈ X) : apply (RELAT_1.id X) x = x :=
  id_apply hx

/-- `FUNCT_1:19` (`Th19`) — `f*(RELAT_1.id X)` is `comp (RELAT_1.id X) f`. -/
theorem th19 {f X : TarskiSet.{u}} (_hf : isFunctionLike f) :
    dom (comp (RELAT_1.id X) f) = dom f ∩ X := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    have ⟨hid, hfx⟩ :=
      (th11 (id_isFunctionLike X) (f := RELAT_1.id X) (g := f) (x := x)).mp hx
    have hxX : x ∈ X := (id_dom X) ▸ hid
    exact (XBOOLE_0.def4 (dom f) X x).mpr ⟨id_apply hxX ▸ hfx, hxX⟩
  · intro hx
    have ⟨hd, hxX⟩ := (XBOOLE_0.def4 (dom f) X x).mp hx
    exact (th11 (id_isFunctionLike X) (f := RELAT_1.id X) (g := f) (x := x)).mpr
      ⟨(id_dom X).symm ▸ hxX,
        show apply (RELAT_1.id X) x ∈ dom f from (id_apply hxX).symm ▸ hd⟩

/-- `FUNCT_1:20` -/
theorem th20 {f X x : TarskiSet.{u}} (hf : isFunctionLike f)
    (hx : x ∈ dom f ∩ X) :
    apply f x = apply (comp (RELAT_1.id X) f) x := by
  have ⟨_, hxX⟩ := (XBOOLE_0.def4 (dom f) X x).mp hx
  have hid : apply (RELAT_1.id X) x = x := id_apply hxX
  have h13 := th13 (id_isFunctionLike X) hf ((id_dom X).symm ▸ hxX)
  exact (congrArg (apply f) hid.symm).trans h13.symm

/-- `FUNCT_1:21` -/
theorem th21 {f Y x : TarskiSet.{u}} (hf : isFunctionLike f) :
    x ∈ dom (comp f (RELAT_1.id Y)) ↔ x ∈ dom f ∧ apply f x ∈ Y :=
  (th11 hf (f := f) (g := RELAT_1.id Y) (x := x)).trans
    (and_congr Iff.rfl
      ⟨fun h => (id_dom Y) ▸ h, fun h => (id_dom Y).symm ▸ h⟩)

/-- `FUNCT_1:22` -/
theorem th22 : comp (RELAT_1.id Y) (RELAT_1.id X) = RELAT_1.id (X ∩ Y) := by
  have hf : isFunction (comp (RELAT_1.id Y) (RELAT_1.id X)) :=
    comp_isFunction (id_isFunction Y) (id_isFunction X)
  have hd : dom (comp (RELAT_1.id Y) (RELAT_1.id X)) = X ∩ Y :=
    (th19 (id_isFunctionLike X) (f := RELAT_1.id X) (X := Y)).trans
      (congrArg (fun s => s ∩ Y) (id_dom X))
  exact th2 hf (id_isFunction (X ∩ Y))
    (hd.trans (id_dom (X ∩ Y)).symm) fun z hz => by
      have hzI : z ∈ X ∩ Y := hd ▸ hz
      have ⟨hzX, hzY⟩ := (XBOOLE_0.def4 X Y z).mp hzI
      have h12 := th12 (id_isFunctionLike Y) (id_isFunctionLike X) hz
      exact h12.trans
        ((congrArg (apply (RELAT_1.id X)) (id_apply hzY)).trans
          ((id_apply hzX).trans (id_apply hzI).symm))

/-- `FUNCT_1:23` (`Th23`) -/
theorem th23 {f g : TarskiSet.{u}} (hf : isFunction f) (hg : isFunction g)
    (hr : rng f = dom g) (hcomp : comp f g = f) : g = RELAT_1.id (dom g) :=
  (th17 hg).mpr ⟨rfl, fun x hx => by
    obtain ⟨y, hy, heq⟩ := (def3 hf.2).mp (hr.symm ▸ hx)
    have h13 := th13 hf.2 hg.2 hy
    have hgf : apply f y = apply g (apply f y) :=
      (congrArg (fun s => apply s y) hcomp).symm.trans h13
    exact (congrArg (apply g) heq).trans (hgf.symm.trans heq.symm)⟩

/-! ## One-to-one (`FUNCT_1:def 4`) -/

def isOneToOne (f : TarskiSet.{u}) : Prop :=
  ∀ x1 x2, x1 ∈ dom f → x2 ∈ dom f → apply f x1 = apply f x2 → x1 = x2

theorem def4 (f : TarskiSet.{u}) :
    isOneToOne f ↔
      ∀ x1 x2, x1 ∈ dom f → x2 ∈ dom f → apply f x1 = apply f x2 → x1 = x2 :=
  Iff.rfl

/-- `FUNCT_1:24` (`Th24`) -/
theorem th24 {f g : TarskiSet.{u}} (hf : isFunctionLike f)
    (hg : isFunctionLike g) (h1 : isOneToOne f) (h2 : isOneToOne g) :
    isOneToOne (comp f g) := by
  intro x1 x2 hx1 hx2 heq
  have ⟨hd1, hg1⟩ := (th11 hf (f := f) (g := g) (x := x1)).mp hx1
  have ⟨hd2, hg2⟩ := (th11 hf (f := f) (g := g) (x := x2)).mp hx2
  have h12 : apply g (apply f x1) = apply g (apply f x2) :=
    (th12 hf hg hx1).symm.trans (heq.trans (th12 hf hg hx2))
  have hf12 : apply f x1 = apply f x2 := h2 (apply f x1) (apply f x2) hg1 hg2 h12
  exact h1 x1 x2 hd1 hd2 hf12

/-- `FUNCT_1:25` (`Th25`) -/
theorem th25 {f g : TarskiSet.{u}} (hf : isFunctionLike f)
    (hg : isFunctionLike g) (h : isOneToOne (comp f g))
    (hr : rng f ⊆ dom g) : isOneToOne f := by
  intro x1 x2 hx1 hx2 heq
  have hc1 : x1 ∈ dom (comp f g) := (th11 hf).mpr ⟨hx1, hr _ (th3 hf hx1)⟩
  have hc2 : x2 ∈ dom (comp f g) := (th11 hf).mpr ⟨hx2, hr _ (th3 hf hx2)⟩
  have : apply (comp f g) x1 = apply (comp f g) x2 :=
    (th12 hf hg hc1).trans ((congrArg (apply g) heq).trans (th12 hf hg hc2).symm)
  exact h x1 x2 hc1 hc2 this

/-- `FUNCT_1:26` -/
theorem th26 {f g : TarskiSet.{u}} (hf : isFunctionLike f)
    (hg : isFunctionLike g) (h : isOneToOne (comp f g))
    (hr : rng f = dom g) : isOneToOne f ∧ isOneToOne g :=
  ⟨th25 hf hg h (hr ▸ fun _ hx => hx),
    fun y1 y2 hy1 hy2 heq => by
      obtain ⟨x1, hx1, e1⟩ := (def3 hf).mp (hr.symm ▸ hy1)
      obtain ⟨x2, hx2, e2⟩ := (def3 hf).mp (hr.symm ▸ hy2)
      have hc1 : x1 ∈ dom (comp f g) := (th11 hf).mpr ⟨hx1, e1 ▸ hy1⟩
      have hc2 : x2 ∈ dom (comp f g) := (th11 hf).mpr ⟨hx2, e2 ▸ hy2⟩
      have : apply (comp f g) x1 = apply (comp f g) x2 :=
        (th12 hf hg hc1).trans
          ((congrArg (apply g) e1).symm.trans (heq.trans (congrArg (apply g) e2))
            |>.trans (th12 hf hg hc2).symm)
      have hx : x1 = x2 := h x1 x2 hc1 hc2 this
      have he1 : y1 = apply f x1 := e1
      have he2 : y2 = apply f x2 := e2
      exact he1.trans ((congrArg (apply f) hx).trans he2.symm)⟩

/-- `FUNCT_1:31` — skip canceled `th30`. -/
theorem th31 {f g : TarskiSet.{u}} (hf : isFunctionLike f)
    (hg : isFunctionLike g) (h : comp f g = RELAT_1.id (dom f)) :
    isOneToOne f := by
  have hdom : dom (comp f g) = dom f :=
    (congrArg dom h).trans (id_dom (dom f))
  exact th25 hf hg
    (fun x1 x2 hx1 hx2 heq =>
      (id_apply ((hdom ▸ hx1) : x1 ∈ dom f)).symm.trans
        ((congrArg (fun s => apply s x1) h).symm.trans
          (heq.trans
            ((congrArg (fun s => apply s x2) h).trans
              (id_apply ((hdom ▸ hx2) : x2 ∈ dom f))))))
    (th15 hf hdom)

/-! ## Inverse `f"` (`FUNCT_1:def 5`) — `converse` when one-to-one. -/

noncomputable def inv (f : TarskiSet.{u}) : TarskiSet.{u} := converse f

theorem converse_isFunctionLike_of_inj {f : TarskiSet.{u}}
    (hf : isFunctionLike f) (h1 : isOneToOne f) :
    isFunctionLike (converse f) := by
  intro x y1 y2 hp1 hp2
  have h1f := (def7 f x y1).mp hp1
  have h2f := (def7 f x y2).mp hp2
  exact h1 y1 y2 (pair_mem_dom h1f) (pair_mem_dom h2f)
    ((apply_of_mem hf h1f).trans (apply_of_mem hf h2f).symm)

theorem inv_isFunction {f : TarskiSet.{u}} (hf : isFunction f)
    (h1 : isOneToOne f) : isFunction (inv f) :=
  ⟨converse_isRelation f, converse_isFunctionLike_of_inj hf.2 h1⟩

theorem def5 {f : TarskiSet.{u}} (_h1 : isOneToOne f) : inv f = converse f :=
  rfl

/-- `FUNCT_1:33` (`Th33`) -/
theorem th33 {f : TarskiSet.{u}} (_h1 : isOneToOne f) :
    rng f = dom (inv f) ∧ dom f = rng (inv f) :=
  RELAT_1.th20 (R := f)

/-- `FUNCT_1:32` (`Th32`) -/
theorem th32 {f g : TarskiSet.{u}} (hf : isFunction f) (hg : isFunction g)
    (h1 : isOneToOne f) :
    g = inv f ↔
      dom g = rng f ∧
        ∀ y x, (y ∈ rng f ∧ x = apply g y) ↔ (x ∈ dom f ∧ y = apply f x) := by
  constructor
  · intro hginv
    have hdom : dom g = rng f :=
      hginv ▸ (RELAT_1.th20 (R := f)).1.symm
    refine ⟨hdom, fun y x => ⟨?fwd, ?bwd⟩⟩
    · intro ⟨hy, hxeq⟩
      have hyD : y ∈ dom (inv f) := (RELAT_1.th20 (R := f)).1 ▸ hy
      have hp : TARSKI.pair y x ∈ inv f :=
        hxeq ▸ (hginv ▸ apply_spec (show y ∈ dom g from hdom.symm ▸ hy))
      have hpf : TARSKI.pair x y ∈ f := (def7 f y x).mp hp
      exact ⟨pair_mem_dom hpf, (apply_of_mem hf.2 hpf).symm⟩
    · intro ⟨hx, hyeq⟩
      have hpf : TARSKI.pair x y ∈ f := (th1 hf.2).mpr ⟨hx, hyeq⟩
      have hp : TARSKI.pair y x ∈ inv f := (def7 f y x).mpr hpf
      have hyR : y ∈ rng f := hyeq ▸ th3 hf.2 hx
      have hyD : y ∈ dom g := hdom.symm ▸ hyR
      exact ⟨hyR,
        (apply_of_mem hg.2 (show TARSKI.pair y x ∈ g from hginv ▸ hp)).symm⟩
  · intro ⟨hdom, hchar⟩
    exact th2 hg (inv_isFunction hf h1)
      (hdom.trans (RELAT_1.th20 (R := f)).1) fun y hy => by
        have hyR : y ∈ rng f := hdom ▸ hy
        obtain ⟨x, hx, heq⟩ := (def3 hf.2).mp hyR
        have hgval : apply g y = x := ((hchar y x).mpr ⟨hx, heq⟩).2.symm
        have hpf : TARSKI.pair x y ∈ f := (th1 hf.2).mpr ⟨hx, heq⟩
        have hival : apply (inv f) y = x :=
          apply_of_mem (converse_isFunctionLike_of_inj hf.2 h1)
            ((def7 f y x).mpr hpf)
        exact hgval.trans hival.symm

/-- `FUNCT_1:34` (`Th34`) -/
theorem th34 {f x : TarskiSet.{u}} (hf : isFunction f) (h1 : isOneToOne f)
    (hx : x ∈ dom f) :
    apply (inv f) (apply f x) = x ∧ apply (comp f (inv f)) x = x := by
  have hy : apply f x ∈ rng f := th3 hf.2 hx
  have hinv : apply (inv f) (apply f x) = x :=
    ((th32 hf (inv_isFunction hf h1) h1).mp rfl).2 (apply f x) x |>.mpr
      ⟨hx, rfl⟩ |>.2.symm
  exact ⟨hinv, (th13 hf.2 (converse_isFunctionLike_of_inj hf.2 h1) hx).trans hinv⟩

/-- `FUNCT_1:35` (`Th35`) -/
theorem th35 {f y : TarskiSet.{u}} (hf : isFunction f) (h1 : isOneToOne f)
    (hy : y ∈ rng f) :
    apply f (apply (inv f) y) = y ∧ apply (comp (inv f) f) y = y := by
  have ⟨hx, heq⟩ :=
    ((th32 hf (inv_isFunction hf h1) h1).mp rfl).2 y (apply (inv f) y) |>.mp
      ⟨hy, rfl⟩
  have hfy : apply f (apply (inv f) y) = y := heq.symm
  have hyd : y ∈ dom (inv f) := (th33 h1).1 ▸ hy
  exact ⟨hfy, (th13 (converse_isFunctionLike_of_inj hf.2 h1) hf.2 hyd).trans hfy⟩

/-- `FUNCT_1:39` (`Th39`) -/
theorem th39 {f : TarskiSet.{u}} (hf : isFunction f) (h1 : isOneToOne f) :
    comp f (inv f) = RELAT_1.id (dom f) ∧
      comp (inv f) f = RELAT_1.id (rng f) := by
  constructor
  · exact (th17 (comp_isFunction hf (inv_isFunction hf h1))).mpr
      ⟨(RELAT_1.th27 (P := inv f) (R := f)
          (show rng f ⊆ dom (inv f) from (th33 h1).1 ▸ fun _ h => h)),
        fun x hx => (th34 hf h1 hx).2⟩
  · exact (th17 (comp_isFunction (inv_isFunction hf h1) hf)).mpr
      ⟨(RELAT_1.th27 (P := f) (R := inv f)
          (fun z hz => (th33 h1).2.symm ▸ hz)).trans (th33 h1).1.symm,
        fun y hy => (th35 hf h1 hy).2⟩

end FUNCT_1
