import MizarCCL.RELAT_1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/relset_1.miz`.
Authors: Edmund Woronowicz (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Relations Defined on Sets

1–1 Lean rendering of Mizar article `RELSET_1`
(`vendor/mml/relset_1.miz`). Import is `RELAT_1` only.
`Relation of X,Y` is a subset of `[:X,Y:]`.
-/

universe u

open TarskiSet TARSKI

namespace RELSET_1

/-- Mizar mode `Relation of X,Y` is `Subset of [:X,Y:]`. -/
def isRelationOf (R X Y : TarskiSet.{u}) : Prop :=
  R ⊆ ZFMISC_1.product X Y

theorem relationOf_isRelation {R X Y : TarskiSet.{u}}
    (h : isRelationOf R X Y) : RELAT_1.isRelation R :=
  RELAT_1.subset_isRelation (RELAT_1.product_isRelation X Y) h

theorem relationOf_defined {R X Y : TarskiSet.{u}}
    (h : isRelationOf R X Y) : RELAT_1.isXdefined R X :=
  fun x hx =>
    let ⟨y, hp⟩ := (RELAT_1.dom_iff R x).mp hx
    ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp (h _ hp)).1

theorem relationOf_valued {R X Y : TarskiSet.{u}}
    (h : isRelationOf R X Y) : RELAT_1.isXvalued R Y :=
  fun y hy =>
    let ⟨x, hp⟩ := (RELAT_1.rng_iff R y).mp hy
    ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp (h _ hp)).2

/-- Unlabeled `RELSET_1` (`L119`). -/
theorem th1 {A R X Y : TarskiSet.{u}} (hR : isRelationOf R X Y)
    (hA : A ⊆ R) : isRelationOf A X Y :=
  XBOOLE_1.th1 (X := A) (Y := R) (Z := ZFMISC_1.product X Y) hA hR

/-- Unlabeled `RELSET_1` (`L122`). -/
theorem th2 {R X Y a : TarskiSet.{u}} (hR : isRelationOf R X Y)
    (ha : a ∈ R) :
    ∃ x y, a = TARSKI.pair x y ∧ x ∈ X ∧ y ∈ Y :=
  let ⟨x, y, heq⟩ := relationOf_isRelation hR a ha
  let ⟨hx, hy⟩ :=
    (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp
      (Eq.subst (motive := fun s => s ∈ ZFMISC_1.product X Y) heq
        (hR a ha))
  ⟨x, y, heq, hx, hy⟩

/-- Unlabeled `RELSET_1` (`L133`). -/
theorem th3 {X Y x y : TarskiSet.{u}} (hx : x ∈ X) (hy : y ∈ Y) :
    isRelationOf (TARSKI.singleton (TARSKI.pair x y)) X Y :=
  (ZFMISC_1.th31 (x := TARSKI.pair x y) (X := ZFMISC_1.product X Y)).mpr
    ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mpr ⟨hx, hy⟩)

/-- Unlabeled `RELSET_1` (`L141`). -/
theorem th4 {R X Y : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hd : RELAT_1.dom R ⊆ X) (hr : RELAT_1.rng R ⊆ Y) :
    isRelationOf R X Y :=
  XBOOLE_1.th1 (X := R) (Y := ZFMISC_1.product (RELAT_1.dom R) (RELAT_1.rng R))
    (Z := ZFMISC_1.product X Y) (RELAT_1.th7 hR) (ZFMISC_1.th96 hd hr)

/-- Unlabeled `RELSET_1` (`L151`). -/
theorem th5 {R X Y X1 : TarskiSet.{u}} (hR : isRelationOf R X Y)
    (hd : RELAT_1.dom R ⊆ X1) : isRelationOf R X1 Y :=
  th4 (relationOf_isRelation hR) hd (relationOf_valued hR)

/-- Unlabeled `RELSET_1` (`L161`). -/
theorem th6 {R X Y Y1 : TarskiSet.{u}} (hR : isRelationOf R X Y)
    (hr : RELAT_1.rng R ⊆ Y1) : isRelationOf R X Y1 :=
  th4 (relationOf_isRelation hR) (relationOf_defined hR) hr

/-- Unlabeled `RELSET_1` (`L171`). -/
theorem th7 {R X Y X1 Y1 : TarskiSet.{u}} (hR : isRelationOf R X Y)
    (hX : X ⊆ X1) (hY : Y ⊆ Y1) : isRelationOf R X1 Y1 :=
  XBOOLE_1.th1 (X := R) (Y := ZFMISC_1.product X Y)
    (Z := ZFMISC_1.product X1 Y1) hR (ZFMISC_1.th96 hX hY)

/-- Unlabeled `RELSET_1` (`L241`). -/
theorem th8 {R X Y : TarskiSet.{u}} (hR : isRelationOf R X Y) :
    RELAT_1.field R ⊆ X ∪ Y :=
  XBOOLE_1.th13 (X := RELAT_1.dom R) (Y := X) (Z := RELAT_1.rng R) (V := Y)
    (relationOf_defined hR) (relationOf_valued hR)

/-- Unlabeled `RELSET_1` (`L248`). -/
theorem th9 {R X Y : TarskiSet.{u}} (hR : isRelationOf R X Y) :
    (∀ x, x ∈ X → ∃ y, TARSKI.pair x y ∈ R) ↔ RELAT_1.dom R = X := by
  constructor
  · intro h
    apply (XBOOLE_0.def10 (X := RELAT_1.dom R) (Y := X)).mpr
    constructor
    · exact relationOf_defined hR
    · intro x hx
      obtain ⟨y, hp⟩ := h x hx
      exact (RELAT_1.dom_iff R x).mpr ⟨y, hp⟩
  · intro heq x hx
    exact (RELAT_1.dom_iff R x).mp
      (Eq.subst (motive := fun s => x ∈ s) heq.symm hx)

/-- Unlabeled `RELSET_1` (`L269`). -/
theorem th10 {R X Y : TarskiSet.{u}} (hR : isRelationOf R X Y) :
    (∀ y, y ∈ Y → ∃ x, TARSKI.pair x y ∈ R) ↔ RELAT_1.rng R = Y := by
  constructor
  · intro h
    apply (XBOOLE_0.def10 (X := RELAT_1.rng R) (Y := Y)).mpr
    constructor
    · exact relationOf_valued hR
    · intro y hy
      obtain ⟨x, hp⟩ := h y hy
      exact (RELAT_1.rng_iff R y).mpr ⟨x, hp⟩
  · intro heq y hy
    exact (RELAT_1.rng_iff R y).mp
      (Eq.subst (motive := fun s => y ∈ s) heq.symm hy)

/-- Converse of a `Relation of X,Y` is a `Relation of Y,X`. -/
theorem converse_isRelationOf {R X Y : TarskiSet.{u}}
    (hR : isRelationOf R X Y) :
    isRelationOf (RELAT_1.converse R) Y X :=
  RELAT_1.rel_subset (RELAT_1.converse_isRelation R) fun x y hp =>
    ZFMISC_1.th88
      (hR _ ((RELAT_1.def7 R x y).mp hp))

/-- Composition of relations of `X,Y1` and `Y2,Z` is a relation of `X,Z`. -/
theorem comp_isRelationOf {P R X Y1 Y2 Z : TarskiSet.{u}}
    (hP : isRelationOf P X Y1) (hR : isRelationOf R Y2 Z) :
    isRelationOf (RELAT_1.comp P R) X Z :=
  RELAT_1.rel_subset (RELAT_1.comp_isRelation P R) fun x z hp =>
    let ⟨y, hxy, hyz⟩ := (RELAT_1.def8 P R x z).mp hp
    (ZFMISC_1.th87 (x := x) (y := z) (X := X) (Y := Z)).mpr
      ⟨((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y1)).mp
          (hP _ hxy)).1,
        ((ZFMISC_1.th87 (x := y) (y := z) (X := Y2) (Y := Z)).mp
          (hR _ hyz)).2⟩

/-- Unlabeled `RELSET_1` (`L323`). -/
theorem th11 (R : TarskiSet.{u}) :
    RELAT_1.dom (RELAT_1.converse R) = RELAT_1.rng R ∧
      RELAT_1.rng (RELAT_1.converse R) = RELAT_1.dom R :=
  ⟨(RELAT_1.th20 (R := R)).1.symm, (RELAT_1.th20 (R := R)).2.symm⟩

/-- Unlabeled `RELSET_1` (`L366`). -/
theorem th12 (X Y : TarskiSet.{u}) :
    isRelationOf (∅ : TarskiSet.{u}) X Y :=
  XBOOLE_1.th2

/-- `RELSET_1:13` (`Th13`) -/
theorem th13 (X : TarskiSet.{u}) :
    RELAT_1.id X ⊆ ZFMISC_1.product X X :=
  RELAT_1.rel_subset (RELAT_1.id_isRelation X) fun x y hp =>
    let ⟨hx, heq⟩ := (RELAT_1.def10 X x y).mp hp
    (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := X)).mpr
      ⟨hx, Eq.subst (motive := fun s => s ∈ X) heq hx⟩

/-- Unlabeled `RELSET_1` after `Th13` (`L391`). -/
theorem th14 (X : TarskiSet.{u}) :
    isRelationOf (RELAT_1.id X) X X :=
  th13 X

/-- `RELSET_1:15` (`Th15`) -/
theorem th15 {A R : TarskiSet.{u}} (h : RELAT_1.id A ⊆ R) :
    A ⊆ RELAT_1.dom R ∧ A ⊆ RELAT_1.rng R := by
  constructor
  · intro x hx
    exact (RELAT_1.dom_iff R x).mpr
      ⟨x, h _ ((RELAT_1.def10 A x x).mpr ⟨hx, rfl⟩)⟩
  · intro x hx
    exact (RELAT_1.rng_iff R x).mpr
      ⟨x, h _ ((RELAT_1.def10 A x x).mpr ⟨hx, rfl⟩)⟩

/-- Unlabeled `RELSET_1` after `Th15` (`L415`). -/
theorem th16 {R X Y : TarskiSet.{u}} (hR : isRelationOf R X Y)
    (h : RELAT_1.id X ⊆ R) :
    X = RELAT_1.dom R ∧ X ⊆ RELAT_1.rng R :=
  ⟨(XBOOLE_0.def10 (X := X) (Y := RELAT_1.dom R)).mpr
      ⟨(th15 h).1, relationOf_defined hR⟩,
    (th15 h).2⟩

/-- Unlabeled `RELSET_1` (`L425`). -/
theorem th17 {R X Y : TarskiSet.{u}} (hR : isRelationOf R X Y)
    (h : RELAT_1.id Y ⊆ R) :
    Y ⊆ RELAT_1.dom R ∧ Y = RELAT_1.rng R :=
  ⟨(th15 h).1,
    (XBOOLE_0.def10 (X := Y) (Y := RELAT_1.rng R)).mpr
      ⟨(th15 h).2, relationOf_valued hR⟩⟩

theorem restrict_isRelationOf {R X Y A : TarskiSet.{u}}
    (hR : isRelationOf R X Y) :
    isRelationOf (RELAT_1.restrict R A) X Y :=
  RELAT_1.rel_subset (RELAT_1.restrict_isRelation R A) fun x y hp =>
    hR _ ((RELAT_1.def11 R A x y).mp hp).2

theorem restrictRng_isRelationOf {R X Y B : TarskiSet.{u}}
    (hR : isRelationOf R X Y) :
    isRelationOf (RELAT_1.restrictRng B R) X Y :=
  RELAT_1.rel_subset (RELAT_1.restrictRng_isRelation B R) fun x y hp =>
    hR _ ((RELAT_1.def12 B R x y).mp hp).2

/-- Unlabeled `RELSET_1` (`L465`). -/
theorem th18 {R X Y X1 : TarskiSet.{u}} (hR : isRelationOf R X Y) :
    isRelationOf (RELAT_1.restrict R X1) X1 Y :=
  RELAT_1.rel_subset (RELAT_1.restrict_isRelation R X1) fun x y hp =>
    let ⟨hx, hpR⟩ := (RELAT_1.def11 R X1 x y).mp hp
    (ZFMISC_1.th87 (x := x) (y := y) (X := X1) (Y := Y)).mpr
      ⟨hx, ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp
        (hR _ hpR)).2⟩

/-- Unlabeled `RELSET_1` (`L477`). -/
theorem th19 {R X Y X1 : TarskiSet.{u}} (hR : isRelationOf R X Y)
    (hX : X ⊆ X1) : RELAT_1.restrict R X1 = R :=
  RELAT_1.rel_eq (RELAT_1.restrict_isRelation R X1) (relationOf_isRelation hR)
    fun x y =>
      ⟨fun hp => ((RELAT_1.def11 R X1 x y).mp hp).2,
        fun hp =>
          (RELAT_1.def11 R X1 x y).mpr
            ⟨hX x ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp
                (hR _ hp)).1,
              hp⟩⟩

/-- Unlabeled `RELSET_1` (`L495`). -/
theorem th20 {R X Y Y1 : TarskiSet.{u}} (hR : isRelationOf R X Y) :
    isRelationOf (RELAT_1.restrictRng Y1 R) X Y1 :=
  RELAT_1.rel_subset (RELAT_1.restrictRng_isRelation Y1 R) fun x y hp =>
    let ⟨hy, hpR⟩ := (RELAT_1.def12 Y1 R x y).mp hp
    (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y1)).mpr
      ⟨((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp
        (hR _ hpR)).1, hy⟩

/-- Unlabeled `RELSET_1` (`L507`). -/
theorem th21 {R X Y Y1 : TarskiSet.{u}} (hR : isRelationOf R X Y)
    (hY : Y ⊆ Y1) : RELAT_1.restrictRng Y1 R = R :=
  RELAT_1.rel_eq (RELAT_1.restrictRng_isRelation Y1 R)
    (relationOf_isRelation hR) fun x y =>
      ⟨fun hp => ((RELAT_1.def12 Y1 R x y).mp hp).2,
        fun hp =>
          (RELAT_1.def12 Y1 R x y).mpr
            ⟨hY y ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp
                (hR _ hp)).2,
              hp⟩⟩

/-- `RELSET_1:22` (`Th22`) -/
theorem th22 {R X Y : TarskiSet.{u}} (hR : isRelationOf R X Y) :
    RELAT_1.image R X = RELAT_1.rng R ∧
      RELAT_1.invimage R Y = RELAT_1.dom R := by
  constructor
  · apply (XBOOLE_0.def10 (X := RELAT_1.image R X)
        (Y := RELAT_1.rng R)).mpr
    constructor
    · intro y hy
      obtain ⟨x, hp, _⟩ := (RELAT_1.def13 R X y).mp hy
      exact (RELAT_1.rng_iff R y).mpr ⟨x, hp⟩
    · intro y hy
      obtain ⟨x, hp⟩ := (RELAT_1.rng_iff R y).mp hy
      exact (RELAT_1.def13 R X y).mpr
        ⟨x, hp, ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp
          (hR _ hp)).1⟩
  · apply (XBOOLE_0.def10 (X := RELAT_1.invimage R Y)
        (Y := RELAT_1.dom R)).mpr
    constructor
    · intro x hx
      obtain ⟨y, hp, _⟩ := (RELAT_1.def14 R Y x).mp hx
      exact (RELAT_1.dom_iff R x).mpr ⟨y, hp⟩
    · intro x hx
      obtain ⟨y, hp⟩ := (RELAT_1.dom_iff R x).mp hx
      exact (RELAT_1.def14 R Y x).mpr
        ⟨y, hp, ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp
          (hR _ hp)).2⟩

/-- Unlabeled `RELSET_1` after `Th22` (`L580`). -/
theorem th23 {R X Y : TarskiSet.{u}} (hR : isRelationOf R X Y) :
    RELAT_1.image R (RELAT_1.invimage R Y) = RELAT_1.rng R ∧
      RELAT_1.invimage R (RELAT_1.image R X) = RELAT_1.dom R := by
  have ⟨himg, hinv⟩ := th22 hR
  have h1 : RELAT_1.image R (RELAT_1.invimage R Y) = RELAT_1.rng R :=
    Eq.subst (motive := fun s => RELAT_1.image R s = RELAT_1.rng R) hinv.symm
      (RELAT_1.th113 (R := R))
  have h2 : RELAT_1.invimage R (RELAT_1.image R X) = RELAT_1.dom R :=
    Eq.subst (motive := fun s => RELAT_1.invimage R s = RELAT_1.dom R)
      himg.symm (RELAT_1.th134 (R := R))
  exact ⟨h1, h2⟩

/-- `RELSET_1:sch RelOnSetEx` -/
theorem sch_RelOnSetEx (A B : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop) :
    ∃ R, isRelationOf R A B ∧
      ∀ x y, TARSKI.pair x y ∈ R ↔ x ∈ A ∧ y ∈ B ∧ P x y := by
  obtain ⟨R, hrel, hchar⟩ := RELAT_1.sch_RelExistence A B P
  refine ⟨R, ?_, hchar⟩
  exact RELAT_1.rel_subset hrel fun x y hp =>
    let ⟨hx, hy, _⟩ := (hchar x y).mp hp
    (ZFMISC_1.th87 (x := x) (y := y) (X := A) (Y := B)).mpr ⟨hx, hy⟩

/-- Unlabeled `RELSET_1` (`L632`). -/
theorem th24 {R D E x : TarskiSet.{u}} (hR : isRelationOf R D E)
    (_hx : x ∈ D) :
    x ∈ RELAT_1.dom R ↔ ∃ y, y ∈ E ∧ TARSKI.pair x y ∈ R := by
  constructor
  · intro hd
    obtain ⟨y, hp⟩ := (RELAT_1.dom_iff R x).mp hd
    exact ⟨y, ((ZFMISC_1.th87 (x := x) (y := y) (X := D) (Y := E)).mp
      (hR _ hp)).2, hp⟩
  · intro ⟨y, _, hp⟩
    exact (RELAT_1.dom_iff R x).mpr ⟨y, hp⟩

/-- Unlabeled `RELSET_1` (`L651`). -/
theorem th25 {R D E y : TarskiSet.{u}} (hR : isRelationOf R D E) :
    y ∈ RELAT_1.rng R ↔ ∃ x, x ∈ D ∧ TARSKI.pair x y ∈ R := by
  constructor
  · intro hr
    obtain ⟨x, hp⟩ := (RELAT_1.rng_iff R y).mp hr
    exact ⟨x, ((ZFMISC_1.th87 (x := x) (y := y) (X := D) (Y := E)).mp
      (hR _ hp)).1, hp⟩
  · intro ⟨x, _, hp⟩
    exact (RELAT_1.rng_iff R y).mpr ⟨x, hp⟩

/-- Unlabeled `RELSET_1` (`L669`). -/
theorem th26 {R D E : TarskiSet.{u}} (hR : isRelationOf R D E)
    (hne : RELAT_1.dom R ≠ (∅ : TarskiSet.{u})) :
    ∃ y, y ∈ E ∧ y ∈ RELAT_1.rng R := by
  have hrne : RELAT_1.rng R ≠ (∅ : TarskiSet.{u}) :=
    fun he => hne ((RELAT_1.th42 (relationOf_isRelation hR)).mpr he)
  obtain ⟨y, hy⟩ := (XBOOLE_0.th7 hrne)
  exact ⟨y, relationOf_valued hR y hy, hy⟩

/-- Unlabeled `RELSET_1` (`L678`). -/
theorem th27 {R D E : TarskiSet.{u}} (hR : isRelationOf R D E)
    (hne : RELAT_1.rng R ≠ (∅ : TarskiSet.{u})) :
    ∃ x, x ∈ D ∧ x ∈ RELAT_1.dom R := by
  have hdne : RELAT_1.dom R ≠ (∅ : TarskiSet.{u}) :=
    fun he => hne ((RELAT_1.th42 (relationOf_isRelation hR)).mp he)
  obtain ⟨x, hx⟩ := (XBOOLE_0.th7 hdne)
  exact ⟨x, relationOf_defined hR x hx, hx⟩

/-- Unlabeled `RELSET_1` (`L687`). -/
theorem th28 {P R D E F x z : TarskiSet.{u}}
    (hP : isRelationOf P D E) (_hR : isRelationOf R E F) :
    TARSKI.pair x z ∈ RELAT_1.comp P R ↔
      ∃ y, y ∈ E ∧ TARSKI.pair x y ∈ P ∧ TARSKI.pair y z ∈ R := by
  constructor
  · intro hp
    obtain ⟨y, hxy, hyz⟩ := (RELAT_1.def8 P R x z).mp hp
    exact ⟨y, ((ZFMISC_1.th87 (x := x) (y := y) (X := D) (Y := E)).mp
      (hP _ hxy)).2, hxy, hyz⟩
  · intro ⟨y, _, hxy, hyz⟩
    exact (RELAT_1.def8 P R x z).mpr ⟨y, hxy, hyz⟩

/-- Unlabeled `RELSET_1` (`L708`). -/
theorem th29 {R D E D1 y : TarskiSet.{u}} (hR : isRelationOf R D E) :
    y ∈ RELAT_1.image R D1 ↔
      ∃ x, x ∈ D ∧ TARSKI.pair x y ∈ R ∧ x ∈ D1 := by
  constructor
  · intro hy
    obtain ⟨x, hp, hx⟩ := (RELAT_1.def13 R D1 y).mp hy
    exact ⟨x, ((ZFMISC_1.th87 (x := x) (y := y) (X := D) (Y := E)).mp
      (hR _ hp)).1, hp, hx⟩
  · intro ⟨x, _, hp, hx⟩
    exact (RELAT_1.def13 R D1 y).mpr ⟨x, hp, hx⟩

/-- Unlabeled `RELSET_1` (`L726`). -/
theorem th30 {R D E D2 x : TarskiSet.{u}} (hR : isRelationOf R D E) :
    x ∈ RELAT_1.invimage R D2 ↔
      ∃ y, y ∈ E ∧ TARSKI.pair x y ∈ R ∧ y ∈ D2 := by
  constructor
  · intro hx
    obtain ⟨y, hp, hy⟩ := (RELAT_1.def14 R D2 x).mp hx
    exact ⟨y, ((ZFMISC_1.th87 (x := x) (y := y) (X := D) (Y := E)).mp
      (hR _ hp)).2, hp, hy⟩
  · intro ⟨y, _, hp, hy⟩
    exact (RELAT_1.def14 R D2 x).mpr ⟨y, hp, hy⟩

/-- `RELSET_1:sch RelOnDomEx` -/
theorem sch_RelOnDomEx (A B : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop) :
    ∃ R, isRelationOf R A B ∧
      ∀ x y, x ∈ A → y ∈ B → (TARSKI.pair x y ∈ R ↔ P x y) := by
  obtain ⟨R, hR, hchar⟩ := sch_RelOnSetEx A B P
  refine ⟨R, hR, fun x y hx hy => ?_⟩
  constructor
  · intro hp
    exact ((hchar x y).mp hp).2.2
  · intro hP
    exact (hchar x y).mpr ⟨hx, hy, hP⟩

/-- Unlabeled scheme after `RelOnDomEx` (`L758`). -/
theorem sch_ImEx (N M : TarskiSet.{u}) (hM : M ⊆ N)
    (F : TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ i, i ∈ N → i ∈ M → F i ⊆ M) :
    ∃ R, isRelationOf R M M ∧
      ∀ i, i ∈ N → i ∈ M → RELAT_1.Im R i = F i := by
  obtain ⟨R, hR, hchar⟩ :=
    sch_RelOnSetEx M M (fun x y => y ∈ F x)
  refine ⟨R, hR, fun i _ hiM => ?_⟩
  apply (XBOOLE_0.def10 (X := RELAT_1.Im R i) (Y := F i)).mpr
  constructor
  · intro e he
    obtain ⟨u, hp, hu⟩ := (RELAT_1.def13 R (TARSKI.singleton i) e).mp he
    have heq : u = i := (singleton_iff i u).mp hu
    have ⟨_, _, heF⟩ := (hchar u e).mp hp
    exact Eq.subst (motive := fun s => e ∈ F s) heq heF
  · intro e he
    have heM : e ∈ M := hF i (hM i hiM) hiM e he
    have hp : TARSKI.pair i e ∈ R :=
      (hchar i e).mpr ⟨hiM, heM, he⟩
    exact (RELAT_1.def13 R (TARSKI.singleton i) e).mpr
      ⟨i, hp, (singleton_iff i i).mpr rfl⟩

/-- Unlabeled `RELSET_1` (`L790`). -/
theorem th31 {N R S : TarskiSet.{u}} (hR : isRelationOf R N N)
    (hS : isRelationOf S N N)
    (hIm : ∀ i, i ∈ N → RELAT_1.Im R i = RELAT_1.Im S i) : R = S :=
  RELAT_1.rel_eq (relationOf_isRelation hR) (relationOf_isRelation hS)
    fun a b => by
      constructor
      · intro hp
        have ha : a ∈ N :=
          ((ZFMISC_1.th87 (x := a) (y := b) (X := N) (Y := N)).mp
            (hR _ hp)).1
        have hbIm : b ∈ RELAT_1.Im R a :=
          (RELAT_1.def13 R (TARSKI.singleton a) b).mpr
            ⟨a, hp, (singleton_iff a a).mpr rfl⟩
        have hbS : b ∈ RELAT_1.Im S a :=
          Eq.subst (motive := fun s => b ∈ s) (hIm a ha) hbIm
        obtain ⟨e, hpS, he⟩ :=
          (RELAT_1.def13 S (TARSKI.singleton a) b).mp hbS
        exact Eq.subst (motive := fun s => TARSKI.pair s b ∈ S)
          ((singleton_iff a e).mp he) hpS
      · intro hp
        have ha : a ∈ N :=
          ((ZFMISC_1.th87 (x := a) (y := b) (X := N) (Y := N)).mp
            (hS _ hp)).1
        have hbIm : b ∈ RELAT_1.Im S a :=
          (RELAT_1.def13 S (TARSKI.singleton a) b).mpr
            ⟨a, hp, (singleton_iff a a).mpr rfl⟩
        have hbR : b ∈ RELAT_1.Im R a :=
          Eq.subst (motive := fun s => b ∈ s) (hIm a ha).symm hbIm
        obtain ⟨e, hpR, he⟩ :=
          (RELAT_1.def13 R (TARSKI.singleton a) b).mp hbR
        exact Eq.subst (motive := fun s => TARSKI.pair s b ∈ R)
          ((singleton_iff a e).mp he) hpR

/-- Unlabeled scheme (`L822`). -/
theorem sch_RelEq {A B P R : TarskiSet.{u}}
    (hP : isRelationOf P A B) (hR : isRelationOf R A B)
    (pred : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (h1 : ∀ p q, p ∈ A → q ∈ B → (TARSKI.pair p q ∈ P ↔ pred p q))
    (h2 : ∀ p q, p ∈ A → q ∈ B → (TARSKI.pair p q ∈ R ↔ pred p q)) :
    P = R :=
  RELAT_1.rel_eq (relationOf_isRelation hP) (relationOf_isRelation hR)
    fun p q => by
      constructor
      · intro hp
        have ⟨hpA, hqB⟩ :=
          (ZFMISC_1.th87 (x := p) (y := q) (X := A) (Y := B)).mp (hP _ hp)
        exact (h2 p q hpA hqB).mpr ((h1 p q hpA hqB).mp hp)
      · intro hp
        have ⟨hpA, hqB⟩ :=
          (ZFMISC_1.th87 (x := p) (y := q) (X := A) (Y := B)).mp (hR _ hp)
        exact (h1 p q hpA hqB).mpr ((h2 p q hpA hqB).mp hp)

/-- Unlabeled `RELSET_1` (`L853`). -/
theorem th32 {A X P Y : TarskiSet.{u}} (hP : isRelationOf P X Y)
    (hmiss : XBOOLE_0.misses A X) :
    RELAT_1.restrict P A = (∅ : TarskiSet.{u}) :=
  RELAT_1.th152 (f := P)
    (XBOOLE_0.misses_symm
      (XBOOLE_1.th63 (X := RELAT_1.dom P) (Y := X) (Z := A)
        (relationOf_defined hP) (XBOOLE_0.misses_symm hmiss)))

end RELSET_1
