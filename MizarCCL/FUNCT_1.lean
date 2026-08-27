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

/-- `FUNCT_1:27` -/
theorem th27 {f : TarskiSet.{u}} (hf : isFunction f) :
    isOneToOne f ↔
      ∀ g h, isFunction g → isFunction h →
        rng g ⊆ dom f → rng h ⊆ dom f → dom g = dom h →
        comp g f = comp h f → g = h := by
  constructor
  · intro h1 g h hg hh hrg hrh hd hcomp
    exact th2 hg hh hd fun x hx =>
      h1 (apply g x) (apply h x) (hrg _ (th3 hg.2 hx))
        (hrh _ (th3 hh.2 (hd ▸ hx)))
        ((th13 hg.2 hf.2 hx).symm.trans
          ((congrArg (fun s => apply s x) hcomp).trans (th13 hh.2 hf.2 (hd ▸ hx))))
  · intro hcan
    intro x1 x2 hx1 hx2 heq
    let U := TARSKI.singleton (∅ : TarskiSet.{u})
    obtain ⟨g, hg, hgd, hgv⟩ := sch_Lambda U (fun _ => x1)
    obtain ⟨hfn, hh, hhd, hhv⟩ := sch_Lambda U (fun _ => x2)
    have hempty : (∅ : TarskiSet.{u}) ∈ U := (singleton_iff _ _).mpr rfl
    have hrg' : rng g ⊆ dom f := by
      have hr : rng g = TARSKI.singleton x1 :=
        (th4 hg.2 hgd).trans (congrArg TARSKI.singleton (hgv (∅) hempty))
      exact (hr ▸ (ZFMISC_1.th31 (x := x1) (X := dom f)).mpr hx1)
    have hrh' : rng hfn ⊆ dom f := by
      have hr : rng hfn = TARSKI.singleton x2 :=
        (th4 hh.2 hhd).trans (congrArg TARSKI.singleton (hhv (∅) hempty))
      exact (hr ▸ (ZFMISC_1.th31 (x := x2) (X := dom f)).mpr hx2)
    have hdgcomp : dom (comp g f) = U :=
      (RELAT_1.th27 (P := f) (R := g) hrg').trans hgd
    have hdhcomp : dom (comp hfn f) = U :=
      (RELAT_1.th27 (P := f) (R := hfn) hrh').trans hhd
    have hcomp : comp g f = comp hfn f :=
      th2 (comp_isFunction hg hf) (comp_isFunction hh hf)
        (hdgcomp.trans hdhcomp.symm)
        fun z hz => by
          have hzU : z ∈ U := hdgcomp ▸ hz
          exact (th12 hg.2 hf.2 hz).trans
            ((congrArg (apply f) (hgv z hzU)).trans
              (heq.trans
                ((congrArg (apply f) (hhv z hzU)).symm.trans
                  (th12 hh.2 hf.2 (hdhcomp.symm ▸ hzU)).symm)))
    have heqgh := hcan g hfn hg hh hrg' hrh' (hgd.trans hhd.symm) hcomp
    exact (hgv (∅) hempty).symm.trans
      ((congrArg (fun s => apply s (∅ : TarskiSet.{u})) heqgh).trans (hhv (∅) hempty))

/-- `FUNCT_1:28` -/
theorem th28 {f g X : TarskiSet.{u}} (hf : isFunction f) (hg : isFunction g)
    (hdf : dom f = X) (hdg : dom g = X) (hrg : rng g ⊆ X)
    (h1 : isOneToOne f) (hcomp : comp g f = f) : g = RELAT_1.id X :=
  (th17 hg).mpr ⟨hdg, fun x hx =>
    h1 (apply g x) x (hdf.symm ▸ hrg _ (th3 hg.2 (hdg.symm ▸ hx)))
      (hdf.symm ▸ hx)
      ((th13 hg.2 hf.2 (hdg.symm ▸ hx)).symm.trans
        (congrArg (fun s => apply s x) hcomp))⟩

/-- `FUNCT_1:29` -/
theorem th29 {f g : TarskiSet.{u}} (hf : isFunctionLike f)
    (hg : isFunctionLike g) (hr : rng (comp f g) = rng g)
    (h1 : isOneToOne g) : dom g ⊆ rng f := by
  intro y hy
  have hgy : apply g y ∈ rng (comp f g) := hr.symm ▸ th3 hg hy
  obtain ⟨x, hx, heq⟩ := (def3 (comp_isFunctionLike hf hg)).mp hgy
  have ⟨hxf, hfx⟩ := (th11 hf).mp hx
  have : y = apply f x :=
    h1 y (apply f x) hy hfx (heq.trans (th12 hf hg hx))
  exact this ▸ th3 hf hxf

/-- `FUNCT_1:36` (`Th36`) -/
theorem th36 {f : TarskiSet.{u}} (_hf : isFunction f) (h1 : isOneToOne f) :
    dom (comp f (inv f)) = dom f ∧ rng (comp f (inv f)) = dom f :=
  ⟨RELAT_1.th27 (P := inv f) (R := f)
      (fun z hz => (th33 h1).1 ▸ hz),
    (RELAT_1.th28 (P := inv f) (R := f)
        (fun z hz => (th33 h1).1.symm ▸ hz)).trans (th33 h1).2.symm⟩

/-- `FUNCT_1:37` (`Th37`) -/
theorem th37 {f : TarskiSet.{u}} (_hf : isFunction f) (h1 : isOneToOne f) :
    dom (comp (inv f) f) = rng f ∧ rng (comp (inv f) f) = rng f :=
  ⟨(RELAT_1.th27 (P := f) (R := inv f)
        (fun z hz => (th33 h1).2.symm ▸ hz)).trans (th33 h1).1.symm,
    (RELAT_1.th28 (P := f) (R := inv f)
        (fun z hz => (th33 h1).2 ▸ hz)).trans rfl⟩

/-- `FUNCT_1:lm 1` -/
theorem lm1 {g1 g2 f X : TarskiSet.{u}}
    (hg1 : isFunction g1) (hg2 : isFunction g2) (_hf : isFunction f)
    (hr : rng g2 = X) (h1 : comp g2 f = RELAT_1.id (dom g1))
    (h2 : comp f g1 = RELAT_1.id X) : g1 = g2 :=
  RELAT_1.th56 hg1.1 hg2.1 (fun z hz => hr ▸ hz) h1 h2

/-- `FUNCT_1:38` -/
theorem th38 {f g : TarskiSet.{u}} (hf : isFunction f) (hg : isFunction g)
    (h1 : isOneToOne f) (_hd : dom f = rng g) (hr : rng f = dom g)
    (hchar : ∀ x y, x ∈ dom f → y ∈ dom g → (apply f x = y ↔ apply g y = x)) :
    g = inv f :=
  th2 hg (inv_isFunction hf h1) (hr.symm.trans (th33 h1).1) fun y hy =>
    let ⟨x, hx, heq⟩ := (def3 hf.2).mp (hr.symm ▸ hy)
    have hgval : apply g y = x := (hchar x y hx hy).mp heq.symm
    have hival : apply (inv f) y = x := heq ▸ (th34 hf h1 hx).1
    hgval.trans hival.symm

/-- `FUNCT_1:40` (`Th40`) -/
theorem th40 {f : TarskiSet.{u}} (hf : isFunction f) (h1 : isOneToOne f) :
    isOneToOne (inv f) :=
  fun y1 y2 hy1 hy2 heq =>
    ((th35 hf h1 ((th33 h1).1.symm ▸ hy1)).1.symm.trans
      (congrArg (apply f) heq)).trans
      (th35 hf h1 ((th33 h1).1.symm ▸ hy2)).1

/-- `FUNCT_1:41` (`Th41`) -/
theorem th41 {f g : TarskiSet.{u}} (hf : isFunction f) (hg : isFunction g)
    (h1 : isOneToOne f) (hr : rng f = dom g)
    (hcomp : comp f g = RELAT_1.id (dom f)) : g = inv f :=
  lm1 hg (inv_isFunction hf h1) hf (th33 h1).2.symm
    ((th39 hf h1).2.trans (congrArg RELAT_1.id hr)) hcomp

/-- `FUNCT_1:42` -/
theorem th42 {f g : TarskiSet.{u}} (hf : isFunction f) (hg : isFunction g)
    (h1 : isOneToOne f) (hr : rng g = dom f)
    (hcomp : comp g f = RELAT_1.id (rng f)) : g = inv f :=
  (lm1 (inv_isFunction hf h1) hg hf hr
    (hcomp.trans (congrArg RELAT_1.id (th33 h1).1)) (th39 hf h1).1).symm

/-- `FUNCT_1:43` -/
theorem th43 {f : TarskiSet.{u}} (hf : isFunction f) (h1 : isOneToOne f) :
    inv (inv f) = f :=
  (th41 (inv_isFunction hf h1) hf (th40 hf h1) (th33 h1).2.symm
    ((th39 hf h1).2.trans (congrArg RELAT_1.id (th33 h1).1))).symm

/-- `FUNCT_1:44` -/
theorem th44 {f g : TarskiSet.{u}} (_hf : isFunction f) (_hg : isFunction g)
    (_h1 : isOneToOne f) (_h2 : isOneToOne g) :
    inv (comp f g) = comp (inv g) (inv f) :=
  RELAT_1.th35 (P := f) (R := g)

/-- `FUNCT_1:45` -/
theorem th45 : inv (RELAT_1.id X) = RELAT_1.id X :=
  RELAT_1.th46

theorem id_isOneToOne (X : TarskiSet.{u}) : isOneToOne (RELAT_1.id X) :=
  fun x1 x2 hx1 hx2 heq =>
    (id_apply ((id_dom X) ▸ hx1)).symm.trans
      (heq.trans (id_apply ((id_dom X) ▸ hx2)))

/-! ## Restriction of a function -/

theorem restrict_isFunctionLike {f X : TarskiSet.{u}} (hf : isFunctionLike f) :
    isFunctionLike (restrict f X) :=
  fun x y1 y2 h1 h2 =>
    hf x y1 y2 ((def11 f X x y1).mp h1).2 ((def11 f X x y2).mp h2).2

theorem restrict_isFunction {f X : TarskiSet.{u}} (hf : isFunction f) :
    isFunction (restrict f X) :=
  ⟨restrict_isRelation f X, restrict_isFunctionLike hf.2⟩

theorem restrictRng_isFunctionLike {Y f : TarskiSet.{u}}
    (hf : isFunctionLike f) : isFunctionLike (restrictRng Y f) :=
  fun x y1 y2 h1 h2 =>
    hf x y1 y2 ((def12 Y f x y1).mp h1).2 ((def12 Y f x y2).mp h2).2

theorem restrictRng_isFunction {Y f : TarskiSet.{u}} (hf : isFunction f) :
    isFunction (restrictRng Y f) :=
  ⟨restrictRng_isRelation Y f, restrictRng_isFunctionLike hf.2⟩

/-- `FUNCT_1:46` -/
theorem th46 {f g X : TarskiSet.{u}} (hf : isFunction f) (hg : isFunction g)
    (hd : dom g = dom f ∩ X)
    (hv : ∀ x, x ∈ dom g → apply g x = apply f x) :
    g = restrict f X :=
  rel_eq hg.1 (restrict_isRelation f X) fun x y => by
    constructor
    · intro hp
      have hx := pair_mem_dom hp
      have ⟨hdf, hxX⟩ := (XBOOLE_0.def4 (dom f) X x).mp (hd ▸ hx)
      have hy : y = apply f x :=
        (apply_of_mem hg.2 hp).symm.trans (hv x hx)
      exact (def11 f X x y).mpr ⟨hxX, (th1 hf.2).mpr ⟨hdf, hy⟩⟩
    · intro hp
      have ⟨hxX, hpf⟩ := (def11 f X x y).mp hp
      have hdf := pair_mem_dom hpf
      have hxg : x ∈ dom g :=
        hd.symm ▸ (XBOOLE_0.def4 (dom f) X x).mpr ⟨hdf, hxX⟩
      have hy : y = apply g x :=
        (apply_of_mem hf.2 hpf).symm.trans (hv x hxg).symm
      exact (th1 hg.2).mpr ⟨hxg, hy⟩

/-- `FUNCT_1:47` (`Th47`) -/
theorem th47 {f X x : TarskiSet.{u}} (hf : isFunctionLike f)
    (hx : x ∈ dom (restrict f X)) :
    apply (restrict f X) x = apply f x :=
  (apply_of_mem hf ((def11 f X x (apply (restrict f X) x)).mp
    (apply_spec hx)).2).symm

/-- `FUNCT_1:48` (`Th48`) -/
theorem th48 {f X x : TarskiSet.{u}} (hf : isFunctionLike f)
    (hx : x ∈ dom f ∩ X) :
    apply (restrict f X) x = apply f x :=
  th47 hf ((th61 (R := f) (X := X)).symm ▸ hx)

/-- `FUNCT_1:49` (`Th49`) -/
theorem th49 {f X x : TarskiSet.{u}} (hf : isFunctionLike f) (hx : x ∈ X) :
    apply (restrict f X) x = apply f x := by
  by_cases hd : x ∈ dom f
  · exact th47 hf ((th57 (R := f) (X := X) (x := x)).mpr ⟨hx, hd⟩)
  · exact (apply_of_not_mem (fun h => hd ((th57 (R := f) (X := X) (x := x)).mp h).2)).trans
      (apply_of_not_mem hd).symm

/-- `FUNCT_1:50` -/
theorem th50 {f X x : TarskiSet.{u}} (hf : isFunctionLike f)
    (hd : x ∈ dom f) (hx : x ∈ X) :
    apply f x ∈ rng (restrict f X) :=
  (def3 (restrict_isFunctionLike hf)).mpr
    ⟨x, (th57 (R := f) (X := X) (x := x)).mpr ⟨hx, hd⟩, (th49 hf hx).symm⟩

/-- `FUNCT_1:51` -/
theorem th51 (h : X ⊆ Y) :
    restrict (restrict f X) Y = restrict f X ∧
      restrict (restrict f Y) X = restrict f X :=
  ⟨RELAT_1.th73 (R := f) (X := X) (Y := Y) h,
    RELAT_1.th74 (R := f) (X := Y) (Y := X) h⟩

/-- `FUNCT_1:52` -/
theorem th52 {f X : TarskiSet.{u}} (hf : isFunctionLike f)
    (h1 : isOneToOne f) : isOneToOne (restrict f X) :=
  fun x1 x2 hx1 hx2 heq =>
    h1 x1 x2 ((th57 (R := f) (X := X) (x := x1)).mp hx1).2
      ((th57 (R := f) (X := X) (x := x2)).mp hx2).2
      ((th47 hf hx1).symm.trans (heq.trans (th47 hf hx2)))

/-- `FUNCT_1:53` (`Th53`) -/
theorem th53 {f g Y : TarskiSet.{u}} (hf : isFunction f) (hg : isFunction g) :
    g = restrictRng Y f ↔
      (∀ x, x ∈ dom g ↔ x ∈ dom f ∧ apply f x ∈ Y) ∧
        ∀ x, x ∈ dom g → apply g x = apply f x := by
  constructor
  · intro h
    constructor
    · intro x
      constructor
      · intro hx
        have hp := apply_spec hx
        have ⟨hy, hpf⟩ := (def12 Y f x (apply g x)).mp (h ▸ hp)
        exact ⟨pair_mem_dom hpf, apply_of_mem hf.2 hpf ▸ hy⟩
      · intro ⟨hdf, hY⟩
        have hpf := apply_spec hdf
        exact (dom_iff g x).mpr
          ⟨apply f x, h ▸ (def12 Y f x (apply f x)).mpr ⟨hY, hpf⟩⟩
    · intro x hx
      have hp := apply_spec hx
      exact (apply_of_mem hf.2 ((def12 Y f x (apply g x)).mp (h ▸ hp)).2).symm
  · intro ⟨hd, hv⟩
    exact rel_eq hg.1 (restrictRng_isRelation Y f) fun x y => by
      constructor
      · intro hp
        have hx := pair_mem_dom hp
        have hy : y = apply f x := (apply_of_mem hg.2 hp).symm.trans (hv x hx)
        have ⟨hdf, hY⟩ := (hd x).mp hx
        exact (def12 Y f x y).mpr ⟨hy ▸ hY, (th1 hf.2).mpr ⟨hdf, hy⟩⟩
      · intro hp
        have ⟨hY, hpf⟩ := (def12 Y f x y).mp hp
        have hdf := pair_mem_dom hpf
        have hyf : y = apply f x := (apply_of_mem hf.2 hpf).symm
        have hxg : x ∈ dom g := (hd x).mpr ⟨hdf, hyf ▸ hY⟩
        exact (th1 hg.2).mpr ⟨hxg, hyf.trans (hv x hxg).symm⟩

/-- `FUNCT_1:54` -/
theorem th54 {f Y x : TarskiSet.{u}} (hf : isFunction f) :
    x ∈ dom (restrictRng Y f) ↔ x ∈ dom f ∧ apply f x ∈ Y :=
  ((th53 hf (restrictRng_isFunction hf) (Y := Y)).mp rfl).1 x

/-- `FUNCT_1:55` -/
theorem th55 {f Y x : TarskiSet.{u}} (hf : isFunction f)
    (hx : x ∈ dom (restrictRng Y f)) :
    apply (restrictRng Y f) x = apply f x :=
  ((th53 hf (restrictRng_isFunction hf) (Y := Y)).mp rfl).2 x hx

/-- `FUNCT_1:56` -/
theorem th56 {f Y : TarskiSet.{u}} (hf : isFunction f) :
    dom (restrictRng Y f) ⊆ dom f :=
  fun x hx => ((th54 hf).mp hx).1

/-- `FUNCT_1:57` -/
theorem th57 (h : X ⊆ Y) :
    restrictRng Y (restrictRng X f) = restrictRng X f ∧
      restrictRng X (restrictRng Y f) = restrictRng X f :=
  ⟨RELAT_1.th98 (R := f) (X := X) (Y := Y) h,
    RELAT_1.th99 (R := f) (X := Y) (Y := X) h⟩

/-- `FUNCT_1:58` -/
theorem th58 {f Y : TarskiSet.{u}} (hf : isFunction f) (h1 : isOneToOne f) :
    isOneToOne (restrictRng Y f) :=
  fun x1 x2 hx1 hx2 heq =>
    h1 x1 x2 ((th54 hf).mp hx1).1 ((th54 hf).mp hx2).1
      ((th55 hf hx1).symm.trans (heq.trans (th55 hf hx2)))

/-! ## Image via application (`FUNCT_1:def 6`) -/

theorem def6 {f X y : TarskiSet.{u}} (hf : isFunctionLike f) :
    y ∈ image f X ↔ ∃ x, x ∈ dom f ∧ x ∈ X ∧ y = apply f x :=
  (def13 f X y).trans
    ⟨fun ⟨x, hp, hx⟩ => ⟨x, pair_mem_dom hp, hx, (apply_of_mem hf hp).symm⟩,
      fun ⟨x, hd, hx, hy⟩ => ⟨x, (th1 hf).mpr ⟨hd, hy⟩, hx⟩⟩

/-- `FUNCT_1:59` (`Th59`) -/
theorem th59 {f x : TarskiSet.{u}} (hf : isFunctionLike f) (hx : x ∈ dom f) :
    Im f x = TARSKI.singleton (apply f x) := by
  apply eq_of_mem
  intro y
  exact (def6 hf (X := TARSKI.singleton x) (y := y)).trans
    ⟨fun ⟨z, hd, hz, heq⟩ =>
      (singleton_iff (apply f x) y).mpr
        (heq.trans (congrArg (apply f) ((singleton_iff x z).mp hz))),
      fun hy =>
        ⟨x, hx, (singleton_iff x x).mpr rfl, (singleton_iff (apply f x) y).mp hy⟩⟩


/-- `FUNCT_1:16` -/
theorem th16 {f Y : TarskiSet.{u}} (hf : isFunction f)
    (hr : rng f ⊆ Y)
    (hcan : ∀ g h, isFunction g → isFunction h →
      dom g = Y → dom h = Y → comp f g = comp f h → g = h) :
    Y = rng f := by
  refine (XBOOLE_0.def10).mpr ⟨?_, hr⟩
  intro y hy
  refine Classical.byContradiction fun hnr => ?_
  obtain ⟨g, hg, hgd, hgv⟩ :=
    sch_Lambda Y (fun _ => (∅ : TarskiSet.{u}))
  let one : TarskiSet.{u} := TARSKI.singleton (∅ : TarskiSet.{u})
  obtain ⟨hfn, hh, hhd, hhv⟩ :=
    sch_FuncEx Y
      (fun x z => (x = y → z = one) ∧ (x ≠ y → z = (∅ : TarskiSet.{u})))
      (fun x z1 z2 _ hz1 hz2 => by
        by_cases hxy : x = y
        · exact (hz1.1 hxy).trans (hz2.1 hxy).symm
        · exact (hz1.2 hxy).trans (hz2.2 hxy).symm)
      (fun x _ => by
        by_cases hxy : x = y
        · exact ⟨one, ⟨fun _ => rfl, fun hne => (hne hxy).elim⟩⟩
        · exact ⟨(∅ : TarskiSet.{u}), ⟨fun heq => (hxy heq).elim, fun _ => rfl⟩⟩)
  have hrg : rng f ⊆ dom g := hgd ▸ hr
  have hrh : rng f ⊆ dom hfn := hhd ▸ hr
  have hdomg : dom (comp f g) = dom f := RELAT_1.th27 (P := g) (R := f) hrg
  have hdomh : dom (comp f hfn) = dom f := RELAT_1.th27 (P := hfn) (R := f) hrh
  have hcomp : comp f g = comp f hfn :=
    th2 (comp_isFunction hf hg) (comp_isFunction hf hh)
      (hdomg.trans hdomh.symm)
      fun x hx => by
        have hxd : x ∈ dom f := hdomg.symm ▸ hx
        have hfx : apply f x ∈ rng f := th3 hf.2 hxd
        have hne : apply f x ≠ y := fun heq => hnr (heq ▸ hfx)
        have hgval := hgv (apply f x) (hr _ hfx)
        have hhval := (hhv (apply f x) (hr _ hfx)).2 hne
        exact (th12 hf.2 hg.2 hx).trans
          (hgval.trans (hhval.symm.trans (th12 hf.2 hh.2 (hdomh.symm ▸ hxd)).symm))
  have heqgh := hcan g hfn hg hh hgd hhd hcomp
  have hbad : one = (∅ : TarskiSet.{u}) :=
    ((hhv y hy).1 rfl).symm.trans
      ((congrArg (fun s => apply s y) heqgh.symm).trans (hgv y hy))
  exact XBOOLE_0.singleton_nonempty (∅ : TarskiSet.{u})
    (show XBOOLE_0.isEmpty one from
      hbad.symm ▸ XBOOLE_0.emptySet_isEmpty)

/-- `FUNCT_1:60` -/
theorem th60 {f x1 x2 : TarskiSet.{u}} (hf : isFunctionLike f)
    (hx1 : x1 ∈ dom f) (hx2 : x2 ∈ dom f) :
    image f (upair x1 x2) = upair (apply f x1) (apply f x2) := by
  apply eq_of_mem
  intro y
  exact (def6 hf (X := upair x1 x2) (y := y)).trans
    ⟨fun ⟨x, hd, hx, heq⟩ =>
      (upair_iff (apply f x1) (apply f x2) y).mpr
        (Or.elim ((upair_iff x1 x2 x).mp hx)
          (fun h => Or.inl (heq.trans (congrArg (apply f) h)))
          (fun h => Or.inr (heq.trans (congrArg (apply f) h)))),
      fun hy =>
        Or.elim ((upair_iff (apply f x1) (apply f x2) y).mp hy)
          (fun h => ⟨x1, hx1, (upair_iff x1 x2 x1).mpr (Or.inl rfl), h⟩)
          (fun h => ⟨x2, hx2, (upair_iff x1 x2 x2).mpr (Or.inr rfl), h⟩)⟩

/-- `FUNCT_1:61` -/
theorem th61 {f X Y : TarskiSet.{u}} (hf : isFunction f) :
    image (restrictRng Y f) X ⊆ image f X :=
  fun y hy =>
    let ⟨x, hd, hx, heq⟩ := (def6 (restrictRng_isFunctionLike hf.2)).mp hy
    (def6 hf.2).mpr ⟨x, ((th54 hf).mp hd).1, hx, heq.trans (th55 hf hd)⟩

/-- `FUNCT_1:62` (`Th62`) -/
theorem th62 {f X1 X2 : TarskiSet.{u}} (hf : isFunctionLike f)
    (h1 : isOneToOne f) :
    image f (X1 ∩ X2) = image f X1 ∩ image f X2 := by
  apply (XBOOLE_0.def10).mpr
  constructor
  · exact RELAT_1.th121 (R := f) (X := X1) (Y := X2)
  · intro y hy
    have ⟨hy1, hy2⟩ := (XBOOLE_0.def4 (image f X1) (image f X2) y).mp hy
    obtain ⟨x1, hd1, hx1, he1⟩ := (def6 hf (X := X1)).mp hy1
    obtain ⟨x2, hd2, hx2, he2⟩ := (def6 hf (X := X2)).mp hy2
    have hxeq : x1 = x2 := h1 x1 x2 hd1 hd2 (he1.symm.trans he2)
    exact (def6 hf).mpr ⟨x1, hd1,
      (XBOOLE_0.def4 X1 X2 x1).mpr ⟨hx1, hxeq ▸ hx2⟩, he1⟩

private theorem image_empty {f : TarskiSet.{u}} (hf : isFunctionLike f) :
    image f (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) :=
  eq_of_mem fun y =>
    ⟨fun hy =>
      let ⟨_, _, hx, _⟩ := (def6 hf).mp hy
      ((XBOOLE_0.empty_iff _).mp hx).elim,
      fun hy => ((XBOOLE_0.empty_iff y).mp hy).elim⟩

/-- `FUNCT_1:63` -/
theorem th63 {f : TarskiSet.{u}} (hf : isFunctionLike f)
    (h : ∀ X1 X2, image f (X1 ∩ X2) = image f X1 ∩ image f X2) :
    isOneToOne f := by
  intro x1 x2 hx1 hx2 heq
  refine Classical.byContradiction fun hne => ?_
  have hinter : TARSKI.singleton x1 ∩ TARSKI.singleton x2 = (∅ : TarskiSet.{u}) :=
    (XBOOLE_0.def7 _ _).mp (ZFMISC_1.th11 (x := x1) (y := x2) hne)
  have himg := h (TARSKI.singleton x1) (TARSKI.singleton x2)
  have hL : image f (TARSKI.singleton x1 ∩ TARSKI.singleton x2) = (∅ : TarskiSet.{u}) :=
    (congrArg (image f) hinter).trans (image_empty hf)
  have hR : image f (TARSKI.singleton x1) ∩ image f (TARSKI.singleton x2) =
      TARSKI.singleton (apply f x1) :=
    (congrArg (fun s => s ∩ image f (TARSKI.singleton x2)) (th59 hf hx1)).trans
      ((congrArg (fun s => TARSKI.singleton (apply f x1) ∩ s) (th59 hf hx2)).trans
        (heq ▸ XBOOLE_0.inter_idem (TARSKI.singleton (apply f x1))))
  have hempty : TARSKI.singleton (apply f x1) = (∅ : TarskiSet.{u}) :=
    hR.symm.trans (himg.symm.trans hL)
  exact XBOOLE_0.singleton_nonempty (apply f x1)
    (Eq.subst (motive := fun s => XBOOLE_0.isEmpty s) hempty.symm
      XBOOLE_0.emptySet_isEmpty)

/-- `FUNCT_1:64` -/
theorem th64 {f X1 X2 : TarskiSet.{u}} (hf : isFunctionLike f)
    (h1 : isOneToOne f) :
    image f (X1 \ X2) = image f X1 \ image f X2 := by
  apply (XBOOLE_0.def10).mpr
  constructor
  · intro y hy
    obtain ⟨x, hd, hx, heq⟩ := (def6 hf (X := X1 \ X2)).mp hy
    have ⟨hx1, hnx2⟩ := (XBOOLE_0.def5 X1 X2 x).mp hx
    have hny : y ∉ image f X2 := fun hy2 =>
      let ⟨z, hdz, hxz, hez⟩ := (def6 hf (X := X2)).mp hy2
      hnx2 (h1 x z hd hdz (heq.symm.trans hez) ▸ hxz)
    exact (XBOOLE_0.def5 (image f X1) (image f X2) y).mpr
      ⟨(def6 hf).mpr ⟨x, hd, hx1, heq⟩, hny⟩
  · exact RELAT_1.th122 (R := f) (X := X1) (Y := X2)

/-- `FUNCT_1:65` -/
theorem th65 {f : TarskiSet.{u}} (hf : isFunctionLike f)
    (h : ∀ X1 X2, image f (X1 \ X2) = image f X1 \ image f X2) :
    isOneToOne f := by
  intro x1 x2 hx1 hx2 heq
  refine Classical.byContradiction fun hne => ?_
  have hdiff : TARSKI.singleton x1 \ TARSKI.singleton x2 = TARSKI.singleton x1 :=
    (ZFMISC_1.th14 (x := x1) (y := x2)).mpr hne
  have himg := h (TARSKI.singleton x1) (TARSKI.singleton x2)
  have hL : image f (TARSKI.singleton x1 \ TARSKI.singleton x2) =
      TARSKI.singleton (apply f x1) :=
    (congrArg (image f) hdiff).trans (th59 hf hx1)
  have hsub : TARSKI.singleton (apply f x1) ⊆ TARSKI.singleton (apply f x2) :=
    (ZFMISC_1.th31 (x := apply f x1) (X := TARSKI.singleton (apply f x2))).mpr
      ((singleton_iff (apply f x2) (apply f x1)).mpr heq)
  have hR : image f (TARSKI.singleton x1) \ image f (TARSKI.singleton x2) =
      (∅ : TarskiSet.{u}) :=
    (congrArg (fun s => s \ image f (TARSKI.singleton x2)) (th59 hf hx1)).trans
      ((congrArg (fun s => TARSKI.singleton (apply f x1) \ s) (th59 hf hx2)).trans
        ((XBOOLE_1.th37 (X := TARSKI.singleton (apply f x1))
          (Y := TARSKI.singleton (apply f x2))).mpr hsub))
  have hempty : TARSKI.singleton (apply f x1) = (∅ : TarskiSet.{u}) :=
    hL.symm.trans (himg.trans hR)
  exact XBOOLE_0.singleton_nonempty (apply f x1)
    (Eq.subst (motive := fun s => XBOOLE_0.isEmpty s) hempty.symm
      XBOOLE_0.emptySet_isEmpty)

/-- `FUNCT_1:66` -/
theorem th66 {f X Y : TarskiSet.{u}} (hf : isFunctionLike f)
    (hmiss : XBOOLE_0.misses X Y) (h1 : isOneToOne f) :
    XBOOLE_0.misses (image f X) (image f Y) :=
  (XBOOLE_0.def7 _ _).mpr
    ((th62 hf h1 (X1 := X) (X2 := Y)).symm.trans
      (((XBOOLE_0.def7 X Y).mp hmiss) ▸ image_empty hf))

/-- `FUNCT_1:67` -/
theorem th67 {f X Y : TarskiSet.{u}} (hf : isFunction f) :
    image (restrictRng Y f) X = Y ∩ image f X := by
  apply eq_of_mem
  intro y
  constructor
  · intro hy
    obtain ⟨x, hd, hx, heq⟩ := (def6 (restrictRng_isFunctionLike hf.2)).mp hy
    have ⟨hdf, hY⟩ := (th54 hf).mp hd
    have heqf : y = apply f x := heq.trans (th55 hf hd)
    exact (XBOOLE_0.def4 Y (image f X) y).mpr
      ⟨heqf ▸ hY, (def6 hf.2).mpr ⟨x, hdf, hx, heqf⟩⟩
  · intro hy
    have ⟨hY, himg⟩ := (XBOOLE_0.def4 Y (image f X) y).mp hy
    obtain ⟨x, hdf, hx, heq⟩ := (def6 hf.2).mp himg
    have hd : x ∈ dom (restrictRng Y f) :=
      (th54 hf).mpr ⟨hdf, heq ▸ hY⟩
    exact (def6 (restrictRng_isFunctionLike hf.2)).mpr
      ⟨x, hd, hx, heq.trans (th55 hf hd).symm⟩

/-! ## Inverse image via application (`FUNCT_1:def 7`) -/

theorem def7 {f Y x : TarskiSet.{u}} (hf : isFunctionLike f) :
    x ∈ invimage f Y ↔ x ∈ dom f ∧ apply f x ∈ Y :=
  (def14 f Y x).trans
    ⟨fun ⟨y, hp, hy⟩ => ⟨pair_mem_dom hp, apply_of_mem hf hp ▸ hy⟩,
      fun ⟨hd, hY⟩ => ⟨apply f x, apply_spec hd, hY⟩⟩

/-- `FUNCT_1:68` (`Th68`) -/
theorem th68 {f Y1 Y2 : TarskiSet.{u}} (hf : isFunctionLike f) :
    invimage f (Y1 ∩ Y2) = invimage f Y1 ∩ invimage f Y2 := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    have ⟨hd, hY⟩ := (def7 hf (Y := Y1 ∩ Y2)).mp hx
    have ⟨hy1, hy2⟩ := (XBOOLE_0.def4 Y1 Y2 (apply f x)).mp hY
    exact (XBOOLE_0.def4 (invimage f Y1) (invimage f Y2) x).mpr
      ⟨(def7 hf).mpr ⟨hd, hy1⟩, (def7 hf).mpr ⟨hd, hy2⟩⟩
  · intro hx
    have ⟨hx1, hx2⟩ := (XBOOLE_0.def4 (invimage f Y1) (invimage f Y2) x).mp hx
    have ⟨hd, hy1⟩ := (def7 hf (Y := Y1)).mp hx1
    have ⟨_, hy2⟩ := (def7 hf (Y := Y2)).mp hx2
    exact (def7 hf).mpr ⟨hd, (XBOOLE_0.def4 Y1 Y2 (apply f x)).mpr ⟨hy1, hy2⟩⟩

/-- `FUNCT_1:69` -/
theorem th69 {f Y1 Y2 : TarskiSet.{u}} (hf : isFunctionLike f) :
    invimage f (Y1 \ Y2) = invimage f Y1 \ invimage f Y2 := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    have ⟨hd, hY⟩ := (def7 hf (Y := Y1 \ Y2)).mp hx
    have ⟨hy1, hny2⟩ := (XBOOLE_0.def5 Y1 Y2 (apply f x)).mp hY
    exact (XBOOLE_0.def5 (invimage f Y1) (invimage f Y2) x).mpr
      ⟨(def7 hf).mpr ⟨hd, hy1⟩, fun hx2 => hny2 ((def7 hf (Y := Y2)).mp hx2).2⟩
  · intro hx
    have ⟨hx1, hnx2⟩ := (XBOOLE_0.def5 (invimage f Y1) (invimage f Y2) x).mp hx
    have ⟨hd, hy1⟩ := (def7 hf (Y := Y1)).mp hx1
    exact (def7 hf).mpr ⟨hd, (XBOOLE_0.def5 Y1 Y2 (apply f x)).mpr
      ⟨hy1, fun hy2 => hnx2 ((def7 hf).mpr ⟨hd, hy2⟩)⟩⟩

/-- `FUNCT_1:70` -/
theorem th70 {R X Y : TarskiSet.{u}} :
    invimage (restrict R X) Y = X ∩ invimage R Y := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    obtain ⟨y, hp, hy⟩ := (def14 (restrict R X) Y x).mp hx
    have ⟨hxX, hpR⟩ := (def11 R X x y).mp hp
    exact (XBOOLE_0.def4 X (invimage R Y) x).mpr
      ⟨hxX, (def14 R Y x).mpr ⟨y, hpR, hy⟩⟩
  · intro hx
    have ⟨hxX, hi⟩ := (XBOOLE_0.def4 X (invimage R Y) x).mp hx
    obtain ⟨y, hp, hy⟩ := (def14 R Y x).mp hi
    exact (def14 (restrict R X) Y x).mpr
      ⟨y, (def11 R X x y).mpr ⟨hxX, hp⟩, hy⟩

/-- `FUNCT_1:71` -/
theorem th71 {f A B : TarskiSet.{u}} (hf : isFunctionLike f)
    (hmiss : XBOOLE_0.misses A B) :
    XBOOLE_0.misses (invimage f A) (invimage f B) :=
  (XBOOLE_0.def7 _ _).mpr
    ((th68 hf (Y1 := A) (Y2 := B)).symm.trans
      (Eq.trans (congrArg (invimage f) ((XBOOLE_0.def7 A B).mp hmiss))
        (eq_of_mem fun x =>
          ⟨fun hx =>
            ((XBOOLE_0.empty_iff _).mp ((def7 hf (Y := (∅ : TarskiSet.{u}))).mp hx).2).elim,
            fun hx => ((XBOOLE_0.empty_iff x).mp hx).elim⟩)))


/-- `FUNCT_1:72` (`Th72`) -/
theorem th72 {R y : TarskiSet.{u}} :
    y ∈ rng R ↔ invimage R (TARSKI.singleton y) ≠ (∅ : TarskiSet.{u}) := by
  constructor
  · intro hy
    obtain ⟨x, hp⟩ := (rng_iff R y).mp hy
    exact fun h => (XBOOLE_0.empty_iff x).mp
      (h ▸ (def14 R (TARSKI.singleton y) x).mpr
        ⟨y, hp, (singleton_iff y y).mpr rfl⟩)
  · intro hne
    obtain ⟨x, hx⟩ := exists_mem_of_ne hne
    obtain ⟨z, hp, hz⟩ := (def14 R (TARSKI.singleton y) x).mp hx
    exact (rng_iff R y).mpr ⟨x, (singleton_iff y z).mp hz ▸ hp⟩

/-- `FUNCT_1:73` -/
theorem th73 {R Y : TarskiSet.{u}}
    (h : ∀ y, y ∈ Y → invimage R (TARSKI.singleton y) ≠ (∅ : TarskiSet.{u})) :
    Y ⊆ rng R :=
  fun y hy => (th72 (R := R) (y := y)).mpr (h y hy)

/-- `FUNCT_1:74` (`Th74`) -/
theorem th74 {f : TarskiSet.{u}} (hf : isFunctionLike f) :
    (∀ y, y ∈ rng f → ∃ x, invimage f (TARSKI.singleton y) = TARSKI.singleton x) ↔
      isOneToOne f := by
  constructor
  · intro h x1 x2 hx1 hx2 heq
    obtain ⟨y1, hy1⟩ := h (apply f x1) (th3 hf hx1)
    have hx1s : x1 ∈ TARSKI.singleton y1 :=
      hy1 ▸ (def7 hf).mpr ⟨hx1, (singleton_iff (apply f x1) (apply f x1)).mpr rfl⟩
    have hy1x : x1 = y1 := (singleton_iff y1 x1).mp hx1s
    have hx2s : x2 ∈ invimage f (TARSKI.singleton (apply f x1)) :=
      (def7 hf).mpr ⟨hx2, (singleton_iff (apply f x1) (apply f x2)).mpr heq.symm⟩
    have hx2y : x2 = y1 := (singleton_iff y1 x2).mp (hy1 ▸ hx2s)
    exact hy1x.trans hx2y.symm
  · intro h1 y hy
    obtain ⟨x, hx, heq⟩ := (def3 hf).mp hy
    refine ⟨x, eq_of_mem fun z => ?_⟩
    constructor
    · intro hz
      have ⟨hdz, hfz⟩ := (def7 hf).mp hz
      have hzval : apply f z = y := (singleton_iff y (apply f z)).mp hfz
      exact (singleton_iff x z).mpr (h1 z x hdz hx (hzval.trans heq))
    · intro hz
      have hzX : z = x := (singleton_iff x z).mp hz
      exact (def7 hf).mpr ⟨hzX ▸ hx,
        (singleton_iff y (apply f z)).mpr (hzX ▸ heq.symm)⟩

/-- `FUNCT_1:75` (`Th75`) -/
theorem th75 {f Y : TarskiSet.{u}} (hf : isFunctionLike f) :
    image f (invimage f Y) ⊆ Y :=
  fun y hy =>
    let ⟨x, _, hx, heq⟩ := (def6 hf).mp hy
    heq ▸ ((def7 hf).mp hx).2

/-- `FUNCT_1:76` (`Th76`) -/
theorem th76 {R X : TarskiSet.{u}} (h : X ⊆ dom R) :
    X ⊆ invimage R (image R X) :=
  fun x hx =>
    let ⟨y, hp⟩ := (dom_iff R x).mp (h x hx)
    (def14 R (image R X) x).mpr ⟨y, hp, (def13 R X y).mpr ⟨x, hp, hx⟩⟩

/-- `FUNCT_1:77` -/
theorem th77 {f Y : TarskiSet.{u}} (hf : isFunctionLike f) (h : Y ⊆ rng f) :
    image f (invimage f Y) = Y := by
  apply (XBOOLE_0.def10).mpr
  constructor
  · exact th75 hf
  · intro y hy
    obtain ⟨x, hx, heq⟩ := (def3 hf).mp (h y hy)
    exact (def6 hf).mpr ⟨x, hx, (def7 hf).mpr ⟨hx, heq ▸ hy⟩, heq⟩

/-- `FUNCT_1:78` -/
theorem th78 {f Y : TarskiSet.{u}} (hf : isFunctionLike f) :
    image f (invimage f Y) = Y ∩ image f (dom f) := by
  apply (XBOOLE_0.def10).mpr
  constructor
  · exact XBOOLE_1.th19 (th75 hf) (RELAT_1.th114 (R := f) (X := invimage f Y))
  · intro y hy
    have ⟨hY, himg⟩ := (XBOOLE_0.def4 Y (image f (dom f)) y).mp hy
    obtain ⟨x, hd, _, heq⟩ := (def6 hf (X := dom f)).mp himg
    exact (def6 hf).mpr ⟨x, hd, (def7 hf).mpr ⟨hd, heq ▸ hY⟩, heq⟩

/-- `FUNCT_1:79` (`Th79`) -/
theorem th79 {f X Y : TarskiSet.{u}} (hf : isFunctionLike f) :
    image f (X ∩ invimage f Y) ⊆ image f X ∩ Y :=
  fun y hy =>
    let ⟨x, hd, hx, heq⟩ := (def6 hf).mp hy
    let ⟨hxX, hxi⟩ := (XBOOLE_0.def4 X (invimage f Y) x).mp hx
    (XBOOLE_0.def4 (image f X) Y y).mpr
      ⟨(def6 hf).mpr ⟨x, hd, hxX, heq⟩, heq ▸ ((def7 hf).mp hxi).2⟩

/-- `FUNCT_1:80` -/
theorem th80 {f X Y : TarskiSet.{u}} (hf : isFunctionLike f) :
    image f (X ∩ invimage f Y) = image f X ∩ Y := by
  apply (XBOOLE_0.def10).mpr
  constructor
  · exact th79 hf
  · intro y hy
    have ⟨himg, hY⟩ := (XBOOLE_0.def4 (image f X) Y y).mp hy
    obtain ⟨x, hd, hx, heq⟩ := (def6 hf (X := X)).mp himg
    exact (def6 hf).mpr ⟨x, hd,
      (XBOOLE_0.def4 X (invimage f Y) x).mpr ⟨hx, (def7 hf).mpr ⟨hd, heq ▸ hY⟩⟩, heq⟩

/-- `FUNCT_1:81` -/
theorem th81 {R X Y : TarskiSet.{u}} :
    X ∩ invimage R Y ⊆ invimage R (image R X ∩ Y) :=
  fun x hx =>
    let ⟨hxX, hi⟩ := (XBOOLE_0.def4 X (invimage R Y) x).mp hx
    let ⟨y, hp, hy⟩ := (def14 R Y x).mp hi
    (def14 R (image R X ∩ Y) x).mpr
      ⟨y, hp, (XBOOLE_0.def4 (image R X) Y y).mpr
        ⟨(def13 R X y).mpr ⟨x, hp, hxX⟩, hy⟩⟩

/-- `FUNCT_1:82` (`Th82`) -/
theorem th82 {f X : TarskiSet.{u}} (hf : isFunctionLike f) (h1 : isOneToOne f) :
    invimage f (image f X) ⊆ X :=
  fun x hx =>
    let ⟨hd, himg⟩ := (def7 hf).mp hx
    let ⟨z, hdz, hzX, heq⟩ := (def6 hf).mp himg
    h1 x z hd hdz heq ▸ hzX

/-- `FUNCT_1:83` -/
theorem th83 {f : TarskiSet.{u}} (hf : isFunctionLike f)
    (h : ∀ X, invimage f (image f X) ⊆ X) : isOneToOne f := by
  intro x1 x2 hx1 hx2 heq
  have hx2in : x2 ∈ invimage f (image f (TARSKI.singleton x1)) :=
    (def7 hf).mpr ⟨hx2,
      Eq.subst (motive := fun s => apply f x2 ∈ s) (th59 hf hx1).symm
        ((singleton_iff (apply f x1) (apply f x2)).mpr heq.symm)⟩
  exact ((singleton_iff x1 x2).mp (h (TARSKI.singleton x1) x2 hx2in)).symm

/-- `FUNCT_1:84` -/
theorem th84 {f X : TarskiSet.{u}} (hf : isFunction f) (h1 : isOneToOne f) :
    image f X = invimage (inv f) X := by
  apply eq_of_mem
  intro y
  constructor
  · intro hy
    obtain ⟨x, hd, hx, heq⟩ := (def6 hf.2).mp hy
    have hyd : y ∈ dom (inv f) := (th33 h1).1 ▸ (heq ▸ th3 hf.2 hd)
    exact (def7 (converse_isFunctionLike_of_inj hf.2 h1)).mpr
      ⟨hyd, (heq ▸ (th34 hf h1 hd).1) ▸ hx⟩
  · intro hy
    have ⟨hyd, hinv⟩ := (def7 (converse_isFunctionLike_of_inj hf.2 h1)).mp hy
    have hyR : y ∈ rng f := (th33 h1).1.symm ▸ hyd
    obtain ⟨x, hx, heq⟩ := (def3 hf.2).mp hyR
    have : apply (inv f) y = x := heq ▸ (th34 hf h1 hx).1
    exact (def6 hf.2).mpr ⟨x, hx, this ▸ hinv, heq⟩

/-- `FUNCT_1:85` -/
theorem th85 {f Y : TarskiSet.{u}} (hf : isFunction f) (h1 : isOneToOne f) :
    invimage f Y = image (inv f) Y := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    have ⟨hd, hY⟩ := (def7 hf.2).mp hx
    have hfxd : apply f x ∈ dom (inv f) := (th33 h1).1 ▸ th3 hf.2 hd
    exact (def6 (converse_isFunctionLike_of_inj hf.2 h1)).mpr
      ⟨apply f x, hfxd, hY, (th34 hf h1 hd).1.symm⟩
  · intro hx
    obtain ⟨y, hyd, hyY, heq⟩ := (def6 (converse_isFunctionLike_of_inj hf.2 h1)).mp hx
    have hyR : y ∈ rng f := (th33 h1).1.symm ▸ hyd
    obtain ⟨z, hz, hzval⟩ := (def3 hf.2).mp hyR
    have : apply (inv f) y = z := hzval ▸ (th34 hf h1 hz).1
    have hxdom : x ∈ dom f := heq ▸ this ▸ hz
    exact (def7 hf.2).mpr ⟨hxdom, (heq ▸ this ▸ hzval) ▸ hyY⟩

/-- `FUNCT_1:86` -/
theorem th86 {f g h Y : TarskiSet.{u}} (hf : isFunction f)
    (hg : isFunction g) (hh : isFunction h)
    (hY : Y = rng f) (hdg : dom g = Y) (hdh : dom h = Y)
    (hcomp : comp f g = comp f h) : g = h :=
  th2 hg hh (hdg.trans hdh.symm) fun y hy =>
    let ⟨x, hx, heq⟩ := (def3 hf.2).mp (hY ▸ (hdg ▸ hy))
    (heq ▸ (th13 hf.2 hg.2 hx)).symm.trans
      ((congrArg (fun s => apply s x) hcomp).trans (heq ▸ th13 hf.2 hh.2 hx))

/-- `FUNCT_1:87` -/
theorem th87 {f X1 X2 : TarskiSet.{u}} (hf : isFunctionLike f)
    (himg : image f X1 ⊆ image f X2) (hX : X1 ⊆ dom f) (h1 : isOneToOne f) :
    X1 ⊆ X2 :=
  fun x hx =>
    let ⟨z, hdz, hzX, heq⟩ := (def6 hf).mp (himg _ ((def6 hf).mpr ⟨x, hX _ hx, hx, rfl⟩))
    h1 x z (hX _ hx) hdz heq ▸ hzX

/-- `FUNCT_1:88` (`Th88`) -/
theorem th88 {f Y1 Y2 : TarskiSet.{u}} (hf : isFunctionLike f)
    (hinv : invimage f Y1 ⊆ invimage f Y2) (hY : Y1 ⊆ rng f) :
    Y1 ⊆ Y2 :=
  fun y hy =>
    let ⟨x, hx, heq⟩ := (def3 hf).mp (hY y hy)
    heq ▸ ((def7 hf).mp (hinv _ ((def7 hf).mpr ⟨hx, heq ▸ hy⟩))).2

/-- `FUNCT_1:89` -/
theorem th89 {f : TarskiSet.{u}} (hf : isFunctionLike f) :
    isOneToOne f ↔ ∀ y, ∃ x, invimage f (TARSKI.singleton y) ⊆ TARSKI.singleton x := by
  have hiff :
      (∀ y, ∃ x, invimage f (TARSKI.singleton y) ⊆ TARSKI.singleton x) ↔
        (∀ y, y ∈ rng f → ∃ x, invimage f (TARSKI.singleton y) = TARSKI.singleton x) := by
    constructor
    · intro h y hy
      obtain ⟨x, hxsub⟩ := h y
      have hne : invimage f (TARSKI.singleton y) ≠ (∅ : TarskiSet.{u}) :=
        (th72 (R := f) (y := y)).mp hy
      exact ⟨x, ((ZFMISC_1.th33 (Y := invimage f (TARSKI.singleton y)) (x := x)).mp hxsub).resolve_left
        (fun hempty => hne hempty)⟩
    · intro h y
      by_cases hy : y ∈ rng f
      · obtain ⟨x, hx⟩ := h y hy
        exact ⟨x, fun z hz => hx ▸ hz⟩
      · refine ⟨(∅ : TarskiSet.{u}), ?_⟩
        have hempty : invimage f (TARSKI.singleton y) = (∅ : TarskiSet.{u}) :=
          (RELAT_1.th138 (R := f) (Y := TARSKI.singleton y)).mpr
            (XBOOLE_0.misses_symm (ZFMISC_1.th50 hy))
        exact hempty ▸ (XBOOLE_1.th2 (X := TARSKI.singleton (∅ : TarskiSet.{u})))
  exact Iff.trans (th74 hf).symm hiff.symm

/-- `FUNCT_1:90` -/
theorem th90 {R S X : TarskiSet.{u}} (h : rng R ⊆ dom S) :
    invimage R X ⊆ invimage (comp R S) (image S X) := by
  intro x hx
  obtain ⟨y, hpR, hyX⟩ := (def14 R X x).mp hx
  have hyd : y ∈ dom S := h y (pair_mem_rng hpR)
  obtain ⟨z, hpS⟩ := (dom_iff S y).mp hyd
  exact (def14 (comp R S) (image S X) x).mpr
    ⟨z, (def8 R S x z).mpr ⟨y, hpR, hpS⟩,
      (def13 S X z).mpr ⟨y, hpS, hyX⟩⟩

/-- `FUNCT_1:91` -/
theorem th91 {f X Y : TarskiSet.{u}} (hf : isFunctionLike f)
    (heq : invimage f X = invimage f Y) (hX : X ⊆ rng f) (hY : Y ⊆ rng f) :
    X = Y :=
  (XBOOLE_0.def10).mpr ⟨th88 hf (fun _ hx => heq ▸ hx) hX,
    th88 hf (fun _ hy => heq.symm ▸ hy) hY⟩

/-- `FUNCT_1:92` -/
theorem th92 {X A : TarskiSet.{u}} (hA : A ⊆ X) :
    image (RELAT_1.id X) A = A := by
  apply eq_of_mem
  intro e
  constructor
  · intro he
    obtain ⟨u, hd, hu, heq⟩ := (def6 (id_isFunctionLike X)).mp he
    have huX : u ∈ X := (id_dom X) ▸ hd
    exact (heq.trans (id_apply huX)) ▸ hu
  · intro he
    exact (def6 (id_isFunctionLike X)).mpr
      ⟨e, (id_dom X).symm ▸ hA e he, he, (id_apply (hA e he)).symm⟩


/-! ## Empty-yielding and non-empty functions (`FUNCT_1:def 8`, `def 9`) -/

theorem def8 {f : TarskiSet.{u}} (hf : isFunctionLike f) :
    RELAT_1.isEmptyYieldingSet f ↔
      ∀ x, x ∈ dom f → XBOOLE_0.isEmpty (apply f x) := by
  constructor
  · intro h x hx
    have : apply f x = (∅ : TarskiSet.{u}) :=
      (singleton_iff (∅ : TarskiSet.{u}) (apply f x)).mp (h _ (th3 hf hx))
    exact this ▸ XBOOLE_0.emptySet_isEmpty
  · intro h y hy
    obtain ⟨x, hx, heq⟩ := (def3 hf).mp hy
    exact (singleton_iff (∅ : TarskiSet.{u}) y).mpr
      (heq.trans (XBOOLE_0.empty_eq (h x hx)))

theorem def9 {F : TarskiSet.{u}} (hF : isFunctionLike F) :
    RELAT_1.isEmptyYielding F ↔
      ∀ n, n ∈ dom F → ¬ XBOOLE_0.isEmpty (apply F n) := by
  constructor
  · intro h n hn hempty
    exact h ((def3 hF).mpr ⟨n, hn, (XBOOLE_0.empty_eq hempty).symm⟩)
  · intro h hempty
    obtain ⟨i, hi, heq⟩ := (def3 hF).mp hempty
    exact h i hi (heq ▸ XBOOLE_0.emptySet_isEmpty)

theorem sch_LambdaB (D : TarskiSet.{u}) (_hD : ¬ XBOOLE_0.isEmpty D)
    (F : TarskiSet.{u} → TarskiSet.{u}) :
    ∃ f, isFunction f ∧ dom f = D ∧ ∀ d, d ∈ D → apply f d = F d :=
  sch_Lambda D F

/-- `FUNCT_1:def 10` -/
def isConstant (f : TarskiSet.{u}) : Prop :=
  ∀ x y, x ∈ dom f → y ∈ dom f → apply f x = apply f y

theorem def10 {f : TarskiSet.{u}} :
    isConstant f ↔ ∀ x y, x ∈ dom f → y ∈ dom f → apply f x = apply f y :=
  Iff.rfl

/-- `FUNCT_1:93` -/
theorem th93 {f A B : TarskiSet.{u}} (hf : isFunctionLike f)
    (hA : A ⊆ dom f) (himg : image f A ⊆ B) :
    A ⊆ invimage f B :=
  XBOOLE_1.th1 (th76 hA) (RELAT_1.th143 (R := f) himg)

/-- `FUNCT_1:94` -/
theorem th94 {f X : TarskiSet.{u}} (hf : isFunctionLike f)
    (hX : X ⊆ dom f) (h1 : isOneToOne f) :
    invimage f (image f X) = X := by
  apply (XBOOLE_0.def10).mpr
  constructor
  · exact th82 hf h1
  · intro x hx
    exact (def7 hf).mpr ⟨hX _ hx, (def6 hf).mpr ⟨x, hX _ hx, hx, rfl⟩⟩

/-- `FUNCT_1:95` -/
theorem th95 {f g D : TarskiSet.{u}} (hf : isFunction f) (hg : isFunction g)
    (hDf : D ⊆ dom f) (hDg : D ⊆ dom g) :
    restrict f D = restrict g D ↔ ∀ x, x ∈ D → apply f x = apply g x := by
  have hdf : dom (restrict f D) = D :=
    (RELAT_1.th61 (R := f) (X := D)).trans
      ((XBOOLE_0.inter_comm (dom f) D).trans (XBOOLE_1.th28 hDf))
  have hdg : dom (restrict g D) = D :=
    (RELAT_1.th61 (R := g) (X := D)).trans
      ((XBOOLE_0.inter_comm (dom g) D).trans (XBOOLE_1.th28 hDg))
  constructor
  · intro h x hx
    exact (th49 hf.2 hx).symm.trans
      ((congrArg (fun s => apply s x) h).trans (th49 hg.2 hx))
  · intro hv
    exact th2 (restrict_isFunction hf) (restrict_isFunction hg)
      (hdf.trans hdg.symm)
      fun x hx =>
        let hxD : x ∈ D := hdf ▸ hx
        (th49 hf.2 hxD).trans ((hv x hxD).trans (th49 hg.2 hxD).symm)

/-- `FUNCT_1:96` -/
theorem th96 {f g X : TarskiSet.{u}} (hf : isFunction f) (hg : isFunction g)
    (hd : dom f = dom g) (hv : ∀ x, x ∈ X → apply f x = apply g x) :
    restrict f X = restrict g X := by
  have hdf := RELAT_1.th61 (R := f) (X := X)
  have hdg := RELAT_1.th61 (R := g) (X := X)
  refine th2 (restrict_isFunction hf) (restrict_isFunction hg)
    (hdf.trans ((congrArg (fun s => s ∩ X) hd).trans hdg.symm)) ?_
  intro x hx
  have hxX : x ∈ X := ((RELAT_1.th57 (R := f) (X := X) (x := x)).mp hx).1
  have hxg : x ∈ dom (restrict g X) :=
    hdg.symm ▸ (congrArg (fun s => s ∩ X) hd ▸ (hdf ▸ hx))
  exact (th47 hf.2 hx).trans ((hv x hxX).trans (th47 hg.2 hxg).symm)

/-- `FUNCT_1:97` (`Th97`) -/
theorem th97 {f X : TarskiSet.{u}} (hf : isFunctionLike f) :
    rng (restrict f (TARSKI.singleton X)) ⊆ TARSKI.singleton (apply f X) :=
  fun x hx =>
    let ⟨y, hy, heq⟩ := (def3 (restrict_isFunctionLike hf)).mp hx
    have hyX : y = X :=
      (singleton_iff X y).mp (RELAT_1.th58 (R := f) (X := TARSKI.singleton X) y hy)
    (singleton_iff (apply f X) x).mpr
      (heq.trans ((th47 hf hy).trans (congrArg (apply f) hyX)))

/-- `FUNCT_1:98` -/
theorem th98 {f X : TarskiSet.{u}} (hf : isFunctionLike f) (hX : X ∈ dom f) :
    rng (restrict f (TARSKI.singleton X)) = TARSKI.singleton (apply f X) := by
  apply (XBOOLE_0.def10).mpr
  constructor
  · exact th97 hf
  · intro x hx
    have hxval : x = apply f X := (singleton_iff (apply f X) x).mp hx
    have hd : X ∈ dom (restrict f (TARSKI.singleton X)) :=
      (RELAT_1.th57 (R := f) (X := TARSKI.singleton X) (x := X)).mpr
        ⟨(singleton_iff X X).mpr rfl, hX⟩
    exact (def3 (restrict_isFunctionLike hf)).mpr
      ⟨X, hd, hxval.trans (th47 hf hd).symm⟩


/-- `FUNCT_1:99` — `(G|(F.:X))*(F|X) = (G*F)|X`. -/
theorem th99 {F G X : TarskiSet.{u}} (hF : isFunction F) (hG : isFunction G) :
    comp (restrict F X) (restrict G (image F X)) = restrict (comp F G) X := by
  apply th2 (comp_isFunction (restrict_isFunction hF) (restrict_isFunction hG))
    (restrict_isFunction (comp_isFunction hF hG))
  · apply eq_of_mem
    intro x
    constructor
    · intro hx
      have ⟨hxF, hxG⟩ := (th11 (restrict_isFunctionLike hF.2)).mp hx
      have ⟨hxX, hdf⟩ := (RELAT_1.th57 (R := F) (X := X) (x := x)).mp hxF
      have hfxeq := th47 hF.2 hxF
      have ⟨_, hfxG⟩ := (RELAT_1.th57 (R := G) (X := image F X)
        (x := apply (restrict F X) x)).mp hxG
      exact (RELAT_1.th57 (R := comp F G) (X := X) (x := x)).mpr
        ⟨hxX, (th11 hF.2).mpr ⟨hdf, hfxeq ▸ hfxG⟩⟩
    · intro hx
      have ⟨hxX, hxcomp⟩ := (RELAT_1.th57 (R := comp F G) (X := X) (x := x)).mp hx
      have ⟨hdf, hfx⟩ := (th11 hF.2).mp hxcomp
      have hxF : x ∈ dom (restrict F X) :=
        (RELAT_1.th57 (R := F) (X := X) (x := x)).mpr ⟨hxX, hdf⟩
      have himg : apply F x ∈ image F X := (def6 hF.2).mpr ⟨x, hdf, hxX, rfl⟩
      have hfxeq := th47 hF.2 hxF
      exact (th11 (restrict_isFunctionLike hF.2)).mpr
        ⟨hxF, (RELAT_1.th57 (R := G) (X := image F X)
          (x := apply (restrict F X) x)).mpr ⟨hfxeq ▸ himg, hfxeq ▸ hfx⟩⟩
  · intro x hx
    have ⟨hxF, hxG⟩ := (th11 (restrict_isFunctionLike hF.2)).mp hx
    have ⟨hxX, hdf⟩ := (RELAT_1.th57 (R := F) (X := X) (x := x)).mp hxF
    have himg : apply F x ∈ image F X := (def6 hF.2).mpr ⟨x, hdf, hxX, rfl⟩
    have hfxeq := th47 hF.2 hxF
    have ⟨_, hfxG⟩ := (RELAT_1.th57 (R := G) (X := image F X)
      (x := apply (restrict F X) x)).mp hxG
    have hxcomp : x ∈ dom (comp F G) := (th11 hF.2).mpr ⟨hdf, hfxeq ▸ hfxG⟩
    exact (th12 (restrict_isFunctionLike hF.2) (restrict_isFunctionLike hG.2) hx).trans
      ((congrArg (apply (restrict G (image F X))) hfxeq).trans
        ((th49 hG.2 himg).trans
          ((th13 hF.2 hG.2 hdf).symm.trans
            (th48 (comp_isFunctionLike hF.2 hG.2)
              ((XBOOLE_0.def4 (dom (comp F G)) X x).mpr ⟨hxcomp, hxX⟩)).symm)))

/-- `FUNCT_1:100` — `(G|X1)*(F|X) = (G*F)|(X /\ (F"X1))`. -/
theorem th100 {F G X X1 : TarskiSet.{u}} (hF : isFunction F) (hG : isFunction G) :
    comp (restrict F X) (restrict G X1) =
      restrict (comp F G) (X ∩ invimage F X1) := by
  apply th2 (comp_isFunction (restrict_isFunction hF) (restrict_isFunction hG))
    (restrict_isFunction (comp_isFunction hF hG))
  · apply eq_of_mem
    intro x
    constructor
    · intro hx
      have ⟨hxF, hxG⟩ := (th11 (restrict_isFunctionLike hF.2)).mp hx
      have ⟨hxX, hdf⟩ := (RELAT_1.th57 (R := F) (X := X) (x := x)).mp hxF
      have hfxeq := th47 hF.2 hxF
      have ⟨hX1, hfxG⟩ := (RELAT_1.th57 (R := G) (X := X1)
        (x := apply (restrict F X) x)).mp hxG
      exact (RELAT_1.th57 (R := comp F G) (X := X ∩ invimage F X1) (x := x)).mpr
        ⟨(XBOOLE_0.def4 X (invimage F X1) x).mpr
          ⟨hxX, (def7 hF.2).mpr ⟨hdf, hfxeq ▸ hX1⟩⟩,
          (th11 hF.2).mpr ⟨hdf, hfxeq ▸ hfxG⟩⟩
    · intro hx
      have ⟨hxi, hxcomp⟩ :=
        (RELAT_1.th57 (R := comp F G) (X := X ∩ invimage F X1) (x := x)).mp hx
      have ⟨hxX, hinv⟩ := (XBOOLE_0.def4 X (invimage F X1) x).mp hxi
      have ⟨hdf, hfx⟩ := (th11 hF.2).mp hxcomp
      have ⟨_, hX1⟩ := (def7 hF.2).mp hinv
      have hxF : x ∈ dom (restrict F X) :=
        (RELAT_1.th57 (R := F) (X := X) (x := x)).mpr ⟨hxX, hdf⟩
      have hfxeq := th47 hF.2 hxF
      exact (th11 (restrict_isFunctionLike hF.2)).mpr
        ⟨hxF, (RELAT_1.th57 (R := G) (X := X1)
          (x := apply (restrict F X) x)).mpr ⟨hfxeq ▸ hX1, hfxeq ▸ hfx⟩⟩
  · intro x hx
    have ⟨hxF, hxG⟩ := (th11 (restrict_isFunctionLike hF.2)).mp hx
    have ⟨hxX, hdf⟩ := (RELAT_1.th57 (R := F) (X := X) (x := x)).mp hxF
    have hfxeq := th47 hF.2 hxF
    have ⟨hX1, hfxG⟩ := (RELAT_1.th57 (R := G) (X := X1)
      (x := apply (restrict F X) x)).mp hxG
    have hxI : x ∈ X ∩ invimage F X1 :=
      (XBOOLE_0.def4 X (invimage F X1) x).mpr
        ⟨hxX, (def7 hF.2).mpr ⟨hdf, hfxeq ▸ hX1⟩⟩
    exact (th12 (restrict_isFunctionLike hF.2) (restrict_isFunctionLike hG.2) hx).trans
      ((congrArg (apply (restrict G X1)) hfxeq).trans
        ((th49 hG.2 (hfxeq ▸ hX1)).trans
          ((th13 hF.2 hG.2 hdf).symm.trans
            (th49 (comp_isFunctionLike hF.2 hG.2) hxI).symm)))

/-- `FUNCT_1:101` -/
theorem th101 {F G X : TarskiSet.{u}} (hF : isFunctionLike F) :
    X ⊆ dom (comp F G) ↔ X ⊆ dom F ∧ image F X ⊆ dom G := by
  constructor
  · intro h
    refine ⟨fun x hx => ((th11 hF).mp (h x hx)).1, ?_⟩
    intro y hy
    obtain ⟨x, _, hx, heq⟩ := (def6 hF).mp hy
    exact heq ▸ ((th11 hF).mp (h x hx)).2
  · intro ⟨hX, himg⟩ x hx
    exact (th11 hF).mpr ⟨hX x hx, himg _ ((def6 hF).mpr ⟨x, hX x hx, hx, rfl⟩)⟩

/-! ## `the_value_of` a nonempty constant function -/

noncomputable def the_value_of (f : TarskiSet.{u}) : TarskiSet.{u} :=
  have := Classical.propDecidable (dom f = (∅ : TarskiSet.{u}))
  if h : dom f ≠ (∅ : TarskiSet.{u}) then
    apply f (Classical.choose (exists_mem_of_ne h))
  else (∅ : TarskiSet.{u})

theorem the_value_of_spec {f : TarskiSet.{u}}
    (hne : dom f ≠ (∅ : TarskiSet.{u})) :
    ∃ x, x ∈ dom f ∧ the_value_of f = apply f x := by
  have := Classical.propDecidable (dom f = (∅ : TarskiSet.{u}))
  refine ⟨Classical.choose (exists_mem_of_ne hne),
    Classical.choose_spec (exists_mem_of_ne hne), ?_⟩
  exact dif_pos hne

/-- `FUNCT_1:102` -/
theorem th102 {f X x : TarskiSet.{u}} (hf : isFunctionLike f)
    (hv : RELAT_1.isXvalued f X) (hx : x ∈ dom f) : apply f x ∈ X :=
  hv _ (th3 hf hx)

/-- `FUNCT_1:def 13` -/
def isFunctional (IT : TarskiSet.{u}) : Prop :=
  ∀ x, x ∈ IT → isFunction x

theorem def13_functional (IT : TarskiSet.{u}) :
    isFunctional IT ↔ ∀ x, x ∈ IT → isFunction x :=
  Iff.rfl

/-- `FUNCT_1:def 14` — `f` is `g`-compatible. -/
def isCompatible (f g : TarskiSet.{u}) : Prop :=
  ∀ x, x ∈ dom f → apply f x ∈ apply g x

theorem def14_compatible {f g : TarskiSet.{u}} :
    isCompatible f g ↔ ∀ x, x ∈ dom f → apply f x ∈ apply g x :=
  Iff.rfl

/-- `FUNCT_1:103` -/
theorem th103 {f g : TarskiSet.{u}} (hg : isFunctionLike g)
    (hcomp : isCompatible f g) (hd : dom f = dom g) :
    RELAT_1.isEmptyYielding g :=
  fun hempty =>
    let ⟨x, hx, heq⟩ := (def3 hg).mp hempty
    (XBOOLE_0.empty_iff (apply f x)).mp (heq ▸ hcomp x (hd.symm ▸ hx))

/-- `FUNCT_1:104` (`Th104`) -/
theorem th104 (f : TarskiSet.{u}) :
    isCompatible (∅ : TarskiSet.{u}) f :=
  fun x hx => ((XBOOLE_0.empty_iff x).mp (RELAT_1.th38.1 ▸ hx)).elim

/-- `FUNCT_1:105` (`Th105`) -/
theorem th105 {f g : TarskiSet.{u}} (hf : isFunctionLike f)
    (hcomp : isCompatible g f) : dom g ⊆ dom f :=
  fun x hx =>
    Classical.byContradiction fun hnd =>
      (XBOOLE_0.empty_iff (apply g x)).mp
        ((apply_of_not_mem hnd) ▸ hcomp x hx)

/-- `FUNCT_1:106` -/
theorem th106 {f X x : TarskiSet.{u}} (hf : isFunctionLike f)
    (hv : RELAT_1.isXvalued f X) (hx : x ∈ dom f) : apply f x ∈ X :=
  th102 hf hv hx

/-- `FUNCT_1:107` -/
theorem th107 {f A : TarskiSet.{u}} (hf : isFunction f) (h1 : isOneToOne f)
    (hA : A ⊆ dom f) : image (inv f) (image f A) = A :=
  (th85 hf h1 (Y := image f A)).symm.trans (th94 hf.2 hA h1)

/-- `FUNCT_1:108` (`Th108`) -/
theorem th108 {f X x : TarskiSet.{u}} (hf : isFunctionLike f)
    (hxX : x ∈ X) (hx : x ∈ dom f) : apply f x ∈ image f X :=
  (def6 hf).mpr ⟨x, hx, hxX, rfl⟩

/-- `FUNCT_1:109` -/
theorem th109 {f X : TarskiSet.{u}} (hf : isFunctionLike f)
    (hne : X ≠ (∅ : TarskiSet.{u})) (hX : X ⊆ dom f) :
    image f X ≠ (∅ : TarskiSet.{u}) :=
  let ⟨x, hx⟩ := exists_mem_of_ne hne
  fun hempty => (XBOOLE_0.empty_iff (apply f x)).mp
    (hempty ▸ th108 hf hx (hX x hx))

/-- `FUNCT_1:110` -/
theorem th110 {B f : TarskiSet.{u}} (_hB : ¬ XBOOLE_0.isEmpty B)
    (hfun : isFunctional B) (hf : isFunction f) (heq : f = union B) :
    (∃ Doms, (∀ z, z ∈ Doms ↔ ∃ g, g ∈ B ∧ z = dom g) ∧
      dom f = union Doms) ∧
    (∃ Rngs, (∀ z, z ∈ Rngs ↔ ∃ g, g ∈ B ∧ z = rng g) ∧
      rng f = union Rngs) := by
  obtain ⟨Doms, hDoms⟩ :=
    TARSKI.fraenkel B (fun g z => z = dom g)
      (fun _ _ _ h1 h2 => h1.trans h2.symm)
  obtain ⟨Rngs, hRngs⟩ :=
    TARSKI.fraenkel B (fun g z => z = rng g)
      (fun _ _ _ h1 h2 => h1.trans h2.symm)
  refine ⟨⟨Doms, hDoms, ?_⟩, ⟨Rngs, hRngs, ?_⟩⟩
  · apply eq_of_mem
    intro x
    constructor
    · intro hx
      have hp := apply_spec hx
      have : TARSKI.pair x (apply f x) ∈ union B := heq ▸ hp
      obtain ⟨g, hpg, hgB⟩ := (union_iff B (TARSKI.pair x (apply f x))).mp this
      have hg := hfun g hgB
      exact (union_iff Doms x).mpr
        ⟨dom g, pair_mem_dom hpg, (hDoms (dom g)).mpr ⟨g, hgB, rfl⟩⟩
    · intro hx
      obtain ⟨Z, hxZ, hZD⟩ := (union_iff Doms x).mp hx
      obtain ⟨g, hgB, hZ⟩ := (hDoms Z).mp hZD
      have hg := hfun g hgB
      have hpg : TARSKI.pair x (apply g x) ∈ g := apply_spec (hZ ▸ hxZ)
      have hpf : TARSKI.pair x (apply g x) ∈ f :=
        heq.symm ▸ (union_iff B (TARSKI.pair x (apply g x))).mpr ⟨g, hpg, hgB⟩
      exact pair_mem_dom hpf
  · apply eq_of_mem
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, heqy⟩ := (def3 hf.2).mp hy
      have hp : TARSKI.pair x y ∈ f := (th1 hf.2).mpr ⟨hx, heqy⟩
      have : TARSKI.pair x y ∈ union B := heq ▸ hp
      obtain ⟨g, hpg, hgB⟩ := (union_iff B (TARSKI.pair x y)).mp this
      have hg := hfun g hgB
      exact (union_iff Rngs y).mpr
        ⟨rng g, (def3 hg.2).mpr ⟨x, pair_mem_dom hpg, (apply_of_mem hg.2 hpg).symm⟩,
          (hRngs (rng g)).mpr ⟨g, hgB, rfl⟩⟩
    · intro hy
      obtain ⟨Z, hyZ, hZR⟩ := (union_iff Rngs y).mp hy
      obtain ⟨g, hgB, hZ⟩ := (hRngs Z).mp hZR
      have hg := hfun g hgB
      obtain ⟨x, hx, heqy⟩ := (def3 hg.2).mp (hZ ▸ hyZ)
      have hpg : TARSKI.pair x y ∈ g := (th1 hg.2).mpr ⟨hx, heqy⟩
      have hpf : TARSKI.pair x y ∈ f :=
        heq.symm ▸ (union_iff B (TARSKI.pair x y)).mpr ⟨g, hpg, hgB⟩
      exact (rng_iff f y).mpr ⟨x, hpf⟩

/-- `FUNCT_1:111` (`Th111`) — choice. -/
theorem th111 {M : TarskiSet.{u}}
    (h : ∀ X, X ∈ M → X ≠ (∅ : TarskiSet.{u})) :
    ∃ f, isFunction f ∧ dom f = M ∧ ∀ X, X ∈ M → apply f X ∈ X := by
  obtain ⟨f, hf, hdom, hv⟩ :=
    sch_Lambda M (fun X =>
      have := Classical.propDecidable (X = (∅ : TarskiSet.{u}))
      if hx : X ≠ (∅ : TarskiSet.{u}) then
        Classical.choose (exists_mem_of_ne hx)
      else (∅ : TarskiSet.{u}))
  refine ⟨f, hf, hdom, fun X hX => ?_⟩
  have hne := h X hX
  have := Classical.propDecidable (X = (∅ : TarskiSet.{u}))
  exact (hv X hX) ▸ (dif_pos hne) ▸ Classical.choose_spec (exists_mem_of_ne hne)


/-! ## `FUNCT_1:sch NonUniqBoundFuncEx` -/

theorem sch_NonUniqBoundFuncEx (X Y : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hP : ∀ x, x ∈ X → ∃ y, y ∈ Y ∧ P x y) :
    ∃ f, isFunction f ∧ dom f = X ∧ rng f ⊆ Y ∧
      ∀ x, x ∈ X → P x (apply f x) := by
  have := Classical.propDecidable (X = (∅ : TarskiSet.{u}))
  by_cases hX : X = (∅ : TarskiSet.{u})
  · refine ⟨(∅ : TarskiSet.{u}), empty_isFunction,
      RELAT_1.th38.1.trans hX.symm, ?_, ?_⟩
    · exact fun y hy => ((XBOOLE_0.empty_iff y).mp (RELAT_1.th38.2 ▸ hy)).elim
    · intro x hx
      exact ((XBOOLE_0.empty_iff x).mp (hX ▸ hx)).elim
  · obtain ⟨G, hG, hGd, hGv⟩ :=
      sch_FuncEx X (fun x S => ∀ y, y ∈ S ↔ y ∈ Y ∧ P x y)
        (fun x S1 S2 _ h1 h2 => eq_of_mem fun y => (h1 y).trans (h2 y).symm)
        (fun x hx => by
          obtain ⟨S, hS⟩ := XBOOLE_0.sch_separation Y (P x)
          exact ⟨S, fun y => hS y⟩)
    have hfib : ∀ Z, Z ∈ rng G → Z ≠ (∅ : TarskiSet.{u}) := by
      intro Z hZ
      obtain ⟨x, hx, heq⟩ := (def3 hG.2).mp hZ
      obtain ⟨y, hyY, hyP⟩ := hP x (hGd ▸ hx)
      have hyG : y ∈ apply G x := (hGv x (hGd ▸ hx) y).mpr ⟨hyY, hyP⟩
      exact fun hempty => (XBOOLE_0.empty_iff y).mp (hempty ▸ heq ▸ hyG)
    obtain ⟨F, hF, hFd, hFv⟩ := th111 hfib
    have hsub : rng G ⊆ dom F := fun z hz => hFd.symm ▸ hz
    have hdom : dom (comp G F) = X :=
      (RELAT_1.th27 (P := F) (R := G) hsub).trans hGd
    refine ⟨comp G F, comp_isFunction hG hF, hdom, ?_, ?_⟩
    · intro z hz
      obtain ⟨x, hx, heq⟩ := (def3 (comp_isFunctionLike hG.2 hF.2)).mp hz
      have hxX : x ∈ X := hdom ▸ hx
      have hGx : apply G x ∈ rng G := th3 hG.2 (hGd.symm ▸ hxX)
      have hFx : apply (comp G F) x = apply F (apply G x) :=
        th12 hG.2 hF.2 hx
      have hFval : apply F (apply G x) ∈ apply G x :=
        hFv (apply G x) (hFd.symm ▸ hGx)
      exact (heq.trans hFx) ▸ ((hGv x hxX (apply F (apply G x))).mp hFval).1
    · intro x hx
      have hxC : x ∈ dom (comp G F) := hdom.symm ▸ hx
      have hval := th12 hG.2 hF.2 hxC
      have hGx : apply G x ∈ rng G := th3 hG.2 (hGd.symm ▸ hx)
      have hFval : apply F (apply G x) ∈ apply G x :=
        hFv (apply G x) (hFd.symm ▸ hGx)
      exact hval.symm ▸ ((hGv x hx (apply F (apply G x))).mp hFval).2

end FUNCT_1

