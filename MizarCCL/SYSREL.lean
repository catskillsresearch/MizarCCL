import MizarCCL.RELAT_1

/-
Copyright (c) 1992-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/sysrel.miz`.
Authors: Waldemar Korczyński (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Some Properties of Binary Relations

1–1 Lean rendering of Mizar article `SYSREL`
(`vendor/mml/sysrel.miz`). Diagonal and closure relations on
binary relations. Import is `RELAT_1` only. Nothing canceled.
-/

universe u

open TarskiSet TARSKI

namespace SYSREL

variable {X Y Z W R S T x y z t : TarskiSet.{u}}

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

private theorem not_mem_of_misses {A B a : TarskiSet.{u}}
    (hmiss : XBOOLE_0.misses A B) (ha : a ∈ A) : a ∉ B :=
  fun hb =>
    (XBOOLE_0.empty_iff a).mp
      (hmiss ▸ (XBOOLE_0.def4 A B a).mpr ⟨ha, hb⟩)

/-- `SYSREL` local `Lm1` -/
theorem lm1 (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u})) :
    RELAT_1.dom (ZFMISC_1.product X Y) = X ∧
      RELAT_1.rng (ZFMISC_1.product X Y) = Y :=
  RELAT_1.th160 hX hY

private theorem inter_subset_right {A B : TarskiSet.{u}} : A ∩ B ⊆ B :=
  fun x hx => ((XBOOLE_0.def4 A B x).mp hx).2

/-- `SYSREL:1` (`Th1`) -/
theorem th1 {R X Y : TarskiSet.{u}} (_hR : RELAT_1.isRelation R) :
    RELAT_1.dom (R ∩ ZFMISC_1.product X Y) ⊆ X ∧
      RELAT_1.rng (R ∩ ZFMISC_1.product X Y) ⊆ Y := by
  by_cases hXY : X = (∅ : TarskiSet.{u}) ∨ Y = (∅ : TarskiSet.{u})
  · have hprod : ZFMISC_1.product X Y = (∅ : TarskiSet.{u}) :=
      (ZFMISC_1.th90 (X := X) (Y := Y)).mpr hXY
    have hinter : R ∩ ZFMISC_1.product X Y = (∅ : TarskiSet.{u}) := by
      rw [hprod, XBOOLE_0.inter_comm]
      exact XBOOLE_1.th28 (X := (∅ : TarskiSet.{u})) (Y := R) XBOOLE_1.th2
    constructor
    · intro u hu
      have : u ∈ RELAT_1.dom (∅ : TarskiSet.{u}) := hinter ▸ hu
      exact False.elim ((XBOOLE_0.empty_iff u).mp (RELAT_1.th38.1 ▸ this))
    · intro v hv
      have : v ∈ RELAT_1.rng (∅ : TarskiSet.{u}) := hinter ▸ hv
      exact False.elim ((XBOOLE_0.empty_iff v).mp (RELAT_1.th38.2 ▸ this))
  · have hX : X ≠ (∅ : TarskiSet.{u}) := fun h => hXY (Or.inl h)
    have hY : Y ≠ (∅ : TarskiSet.{u}) := fun h => hXY (Or.inr h)
    have ⟨hdomProd, hrngProd⟩ := lm1 hX hY
    have hrng :
        RELAT_1.rng (R ∩ ZFMISC_1.product X Y) ⊆
          RELAT_1.rng R ∩ RELAT_1.rng (ZFMISC_1.product X Y) :=
      RELAT_1.th13
    have hrngY :
        RELAT_1.rng (R ∩ ZFMISC_1.product X Y) ⊆ RELAT_1.rng R ∩ Y :=
      fun v hv =>
        let ⟨hr, hp⟩ :=
          (XBOOLE_0.def4 (RELAT_1.rng R)
            (RELAT_1.rng (ZFMISC_1.product X Y)) v).mp (hrng v hv)
        (XBOOLE_0.def4 (RELAT_1.rng R) Y v).mpr ⟨hr, hrngProd ▸ hp⟩
    have hdom :
        RELAT_1.dom (R ∩ ZFMISC_1.product X Y) ⊆
          RELAT_1.dom R ∩ RELAT_1.dom (ZFMISC_1.product X Y) :=
      RELAT_1.th2
    have hdomX :
        RELAT_1.dom (R ∩ ZFMISC_1.product X Y) ⊆ RELAT_1.dom R ∩ X :=
      fun u hu =>
        let ⟨hd, hp⟩ :=
          (XBOOLE_0.def4 (RELAT_1.dom R)
            (RELAT_1.dom (ZFMISC_1.product X Y)) u).mp (hdom u hu)
        (XBOOLE_0.def4 (RELAT_1.dom R) X u).mpr ⟨hd, hdomProd ▸ hp⟩
    exact ⟨
      XBOOLE_1.th1 hdomX inter_subset_right,
      XBOOLE_1.th1 hrngY inter_subset_right⟩

/-- `SYSREL:2` -/
theorem th2 {R X Y : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hmiss : XBOOLE_0.misses X Y) :
    XBOOLE_0.misses
      (RELAT_1.dom (R ∩ ZFMISC_1.product X Y))
      (RELAT_1.rng (R ∩ ZFMISC_1.product X Y)) := by
  have ⟨hd, hr⟩ := th1 (R := R) (X := X) (Y := Y) hR
  have h1 :
      RELAT_1.dom (R ∩ ZFMISC_1.product X Y) ∩
          RELAT_1.rng (R ∩ ZFMISC_1.product X Y) ⊆
        X ∩ RELAT_1.rng (R ∩ ZFMISC_1.product X Y) :=
    XBOOLE_1.th26 hd
  have h2 :
      X ∩ RELAT_1.rng (R ∩ ZFMISC_1.product X Y) ⊆ X ∩ Y := by
    rw [XBOOLE_0.inter_comm X _, XBOOLE_0.inter_comm X Y]
    exact XBOOLE_1.th26 hr
  exact XBOOLE_1.th3
    (XBOOLE_1.th1 h1 (XBOOLE_1.th1 h2 (fun z hz =>
      False.elim ((XBOOLE_0.empty_iff z).mp (hmiss ▸ hz)))))

/-- `SYSREL:3` (`Th3`) -/
theorem th3 {R X Y : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (h : R ⊆ ZFMISC_1.product X Y) :
    RELAT_1.dom R ⊆ X ∧ RELAT_1.rng R ⊆ Y := by
  have hinter : R ∩ ZFMISC_1.product X Y = R := XBOOLE_1.th28 h
  exact hinter ▸ th1 (R := R) (X := X) (Y := Y) hR

/-- `SYSREL:4` -/
theorem th4 {R X Y : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (h : R ⊆ ZFMISC_1.product X Y) :
    RELAT_1.converse R ⊆ ZFMISC_1.product Y X :=
  RELAT_1.rel_subset (RELAT_1.converse_isRelation R) fun z t hp =>
    let ⟨ht, hz⟩ :=
      (ZFMISC_1.th87 (x := t) (y := z) (X := X) (Y := Y)).mp
        (h _ ((RELAT_1.def7 R z t).mp hp))
    (ZFMISC_1.th87 (x := z) (y := t) (X := Y) (Y := X)).mpr ⟨hz, ht⟩

/-- `SYSREL:5` -/
theorem th5 (X Y : TarskiSet.{u}) :
    RELAT_1.converse (ZFMISC_1.product X Y) = ZFMISC_1.product Y X :=
  RELAT_1.rel_eq
    (RELAT_1.converse_isRelation _)
    (RELAT_1.product_isRelation Y X) fun x y => by
    constructor
    · intro h
      have hp := (RELAT_1.def7 (ZFMISC_1.product X Y) x y).mp h
      have ⟨hy, hx⟩ :=
        (ZFMISC_1.th87 (x := y) (y := x) (X := X) (Y := Y)).mp hp
      exact (ZFMISC_1.th87 (x := x) (y := y) (X := Y) (Y := X)).mpr
        ⟨hx, hy⟩
    · intro h
      have ⟨hy, hx⟩ :=
        (ZFMISC_1.th87 (x := x) (y := y) (X := Y) (Y := X)).mp h
      exact (RELAT_1.def7 (ZFMISC_1.product X Y) x y).mpr
        ((ZFMISC_1.th87 (x := y) (y := x) (X := X) (Y := Y)).mpr
          ⟨hx, hy⟩)

/-- `SYSREL:6` (`Th6`) -/
theorem th6 (R S T : TarskiSet.{u}) :
    RELAT_1.comp (R ∪ S) T = RELAT_1.comp R T ∪ RELAT_1.comp S T :=
  RELAT_1.rel_eq
    (RELAT_1.comp_isRelation _ _)
    (RELAT_1.union_isRelation (RELAT_1.comp_isRelation R T)
      (RELAT_1.comp_isRelation S T)) fun x y => by
    constructor
    · intro h
      obtain ⟨z, hzRS, hzT⟩ := (RELAT_1.def8 (R ∪ S) T x y).mp h
      rcases (XBOOLE_0.def3 R S (TARSKI.pair x z)).mp hzRS with hzR | hzS
      · exact (XBOOLE_0.def3 _ _ _).mpr
          (Or.inl ((RELAT_1.def8 R T x y).mpr ⟨z, hzR, hzT⟩))
      · exact (XBOOLE_0.def3 _ _ _).mpr
          (Or.inr ((RELAT_1.def8 S T x y).mpr ⟨z, hzS, hzT⟩))
    · intro h
      rcases (XBOOLE_0.def3 _ _ _).mp h with hR | hS
      · obtain ⟨z, hzR, hzT⟩ := (RELAT_1.def8 R T x y).mp hR
        exact (RELAT_1.def8 (R ∪ S) T x y).mpr
          ⟨z, (XBOOLE_0.def3 R S _).mpr (Or.inl hzR), hzT⟩
      · obtain ⟨z, hzS, hzT⟩ := (RELAT_1.def8 S T x y).mp hS
        exact (RELAT_1.def8 (R ∪ S) T x y).mpr
          ⟨z, (XBOOLE_0.def3 R S _).mpr (Or.inr hzS), hzT⟩

/-- `SYSREL:7` -/
theorem th7 {R X Y x y : TarskiSet.{u}} (_hR : RELAT_1.isRelation R) :
    (XBOOLE_0.misses X Y → R ⊆ ZFMISC_1.product X Y ∪ ZFMISC_1.product Y X →
      TARSKI.pair x y ∈ R → x ∈ X →
        x ∉ Y ∧ y ∉ X ∧ y ∈ Y) ∧
    (XBOOLE_0.misses X Y → R ⊆ ZFMISC_1.product X Y ∪ ZFMISC_1.product Y X →
      TARSKI.pair x y ∈ R → y ∈ Y →
        y ∉ X ∧ x ∉ Y ∧ x ∈ X) ∧
    (XBOOLE_0.misses X Y → R ⊆ ZFMISC_1.product X Y ∪ ZFMISC_1.product Y X →
      TARSKI.pair x y ∈ R → x ∈ Y →
        x ∉ X ∧ y ∉ Y ∧ y ∈ X) ∧
    (XBOOLE_0.misses X Y → R ⊆ ZFMISC_1.product X Y ∪ ZFMISC_1.product Y X →
      TARSKI.pair x y ∈ R → y ∈ X →
        x ∉ X ∧ y ∉ Y ∧ x ∈ Y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hmiss hsub hp hx
    have hnotYX : TARSKI.pair x y ∉ ZFMISC_1.product Y X := fun h =>
      not_mem_of_misses hmiss hx
        ((ZFMISC_1.th87 (x := x) (y := y) (X := Y) (Y := X)).mp h).1
    have hprodXY : TARSKI.pair x y ∈ ZFMISC_1.product X Y := by
      have hU := hsub _ hp
      rcases (XBOOLE_0.th5
          (ZFMISC_1.th104 (Or.inl hmiss)) hU) with h | h
      · exact h.1
      · exact (hnotYX h.1).elim
    have ⟨_, hy⟩ :=
      (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp hprodXY
    exact ⟨not_mem_of_misses hmiss hx, not_mem_of_misses
      (XBOOLE_0.misses_symm hmiss) hy, hy⟩
  · intro hmiss hsub hp hy
    have hnotYX : TARSKI.pair x y ∉ ZFMISC_1.product Y X := fun h =>
      not_mem_of_misses (XBOOLE_0.misses_symm hmiss) hy
        ((ZFMISC_1.th87 (x := x) (y := y) (X := Y) (Y := X)).mp h).2
    have hprodXY : TARSKI.pair x y ∈ ZFMISC_1.product X Y := by
      rcases (XBOOLE_0.def3 _ _ _).mp (hsub _ hp) with h | h
      · exact h
      · exact (hnotYX h).elim
    have ⟨hx, _⟩ :=
      (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp hprodXY
    exact ⟨not_mem_of_misses (XBOOLE_0.misses_symm hmiss) hy,
      not_mem_of_misses hmiss hx, hx⟩
  · intro hmiss hsub hp hxY
    have hnotXY : TARSKI.pair x y ∉ ZFMISC_1.product X Y := fun h =>
      not_mem_of_misses (XBOOLE_0.misses_symm hmiss) hxY
        ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp h).1
    have hprodYX : TARSKI.pair x y ∈ ZFMISC_1.product Y X := by
      rcases (XBOOLE_0.def3 _ _ _).mp (hsub _ hp) with h | h
      · exact (hnotXY h).elim
      · exact h
    have ⟨_, hy⟩ :=
      (ZFMISC_1.th87 (x := x) (y := y) (X := Y) (Y := X)).mp hprodYX
    exact ⟨not_mem_of_misses (XBOOLE_0.misses_symm hmiss) hxY,
      not_mem_of_misses hmiss hy, hy⟩
  · intro hmiss hsub hp hyX
    have hnotXY : TARSKI.pair x y ∉ ZFMISC_1.product X Y := fun h =>
      not_mem_of_misses hmiss hyX
        ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp h).2
    have hprodYX : TARSKI.pair x y ∈ ZFMISC_1.product Y X := by
      rcases (XBOOLE_0.def3 _ _ _).mp (hsub _ hp) with h | h
      · exact (hnotXY h).elim
      · exact h
    have ⟨hx, _⟩ :=
      (ZFMISC_1.th87 (x := x) (y := y) (X := Y) (Y := X)).mp hprodYX
    exact ⟨not_mem_of_misses (XBOOLE_0.misses_symm hmiss) hx,
      not_mem_of_misses hmiss hyX, hx⟩

/-- `SYSREL:8` (`Th8`) -/
theorem th8 {R X Y Z : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (h : R ⊆ ZFMISC_1.product X Y) :
    RELAT_1.restrict R Z = R ∩ ZFMISC_1.product Z Y ∧
      RELAT_1.restrictRng Z R = R ∩ ZFMISC_1.product X Z := by
  constructor
  · exact RELAT_1.rel_eq (RELAT_1.restrict_isRelation R Z)
      (RELAT_1.inter_isRelation hR) fun x y => by
      constructor
      · intro hp
        have ⟨hxZ, hpR⟩ := (RELAT_1.def11 R Z x y).mp hp
        have ⟨_, hy⟩ :=
          (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp
            (h _ hpR)
        exact (XBOOLE_0.def4 R (ZFMISC_1.product Z Y)
            (TARSKI.pair x y)).mpr
          ⟨hpR, (ZFMISC_1.th87 (x := x) (y := y) (X := Z) (Y := Y)).mpr
            ⟨hxZ, hy⟩⟩
      · intro hp
        have ⟨hpR, hprod⟩ :=
          (XBOOLE_0.def4 R (ZFMISC_1.product Z Y)
            (TARSKI.pair x y)).mp hp
        have ⟨hxZ, _⟩ :=
          (ZFMISC_1.th87 (x := x) (y := y) (X := Z) (Y := Y)).mp
            hprod
        exact (RELAT_1.def11 R Z x y).mpr ⟨hxZ, hpR⟩
  · exact RELAT_1.rel_eq (RELAT_1.restrictRng_isRelation Z R)
      (RELAT_1.inter_isRelation hR) fun x y => by
      constructor
      · intro hp
        have ⟨hyZ, hpR⟩ := (RELAT_1.def12 Z R x y).mp hp
        have ⟨hx, _⟩ :=
          (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp
            (h _ hpR)
        exact (XBOOLE_0.def4 R (ZFMISC_1.product X Z)
            (TARSKI.pair x y)).mpr
          ⟨hpR, (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Z)).mpr
            ⟨hx, hyZ⟩⟩
      · intro hp
        have ⟨hpR, hprod⟩ :=
          (XBOOLE_0.def4 R (ZFMISC_1.product X Z)
            (TARSKI.pair x y)).mp hp
        have ⟨_, hyZ⟩ :=
          (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Z)).mp
            hprod
        exact (RELAT_1.def12 Z R x y).mpr ⟨hyZ, hpR⟩

/-- `SYSREL:9` -/
theorem th9 {R X Y Z W : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (h : R ⊆ ZFMISC_1.product X Y) (hX : X = Z ∪ W) :
    R = RELAT_1.restrict R Z ∪ RELAT_1.restrict R W := by
  have h1 : R = R ∩ ZFMISC_1.product X Y := (XBOOLE_1.th28 h).symm
  have hprod : ZFMISC_1.product X Y =
      ZFMISC_1.product Z Y ∪ ZFMISC_1.product W Y := by
    rw [hX]; exact (ZFMISC_1.th97 (X := Z) (Y := W) (Z := Y)).1
  have h2 : R ∩ ZFMISC_1.product X Y =
      R ∩ (ZFMISC_1.product Z Y ∪ ZFMISC_1.product W Y) :=
    congrArg (fun P => R ∩ P) hprod
  have h3 :
      R ∩ (ZFMISC_1.product Z Y ∪ ZFMISC_1.product W Y) =
        (R ∩ ZFMISC_1.product Z Y) ∪ (R ∩ ZFMISC_1.product W Y) :=
    XBOOLE_1.th23
  have ⟨hrZ, _⟩ := th8 (R := R) (X := X) (Y := Y) (Z := Z) hR h
  have ⟨hrW, _⟩ := th8 (R := R) (X := X) (Y := Y) (Z := W) hR h
  rw [hrZ, hrW]
  exact h1.trans (h2.trans h3)

/-- `SYSREL:10` -/
theorem th10 {R X Y : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hmiss : XBOOLE_0.misses X Y)
    (h : R ⊆ ZFMISC_1.product X Y ∪ ZFMISC_1.product Y X) :
    RELAT_1.restrict R X ⊆ ZFMISC_1.product X Y := by
  have hrest :
      RELAT_1.restrict R X =
        R ∩ ZFMISC_1.product X (RELAT_1.rng R) :=
    RELAT_1.th67 hR
  have hsub :
      RELAT_1.restrict R X ⊆
        (ZFMISC_1.product X Y ∪ ZFMISC_1.product Y X) ∩
          ZFMISC_1.product X (RELAT_1.rng R) := by
    rw [hrest]; exact XBOOLE_1.th26 h
  have hdist :
      (ZFMISC_1.product X Y ∪ ZFMISC_1.product Y X) ∩
          ZFMISC_1.product X (RELAT_1.rng R) =
        (ZFMISC_1.product X Y ∩ ZFMISC_1.product X (RELAT_1.rng R)) ∪
          (ZFMISC_1.product Y X ∩ ZFMISC_1.product X (RELAT_1.rng R)) := by
    rw [XBOOLE_0.inter_comm]
    have h23 := XBOOLE_1.th23
      (X := ZFMISC_1.product X (RELAT_1.rng R))
      (Y := ZFMISC_1.product X Y) (Z := ZFMISC_1.product Y X)
    rw [h23, XBOOLE_0.inter_comm (ZFMISC_1.product X (RELAT_1.rng R)),
      XBOOLE_0.inter_comm (ZFMISC_1.product X (RELAT_1.rng R))]
  have hempty :
      ZFMISC_1.product Y X ∩ ZFMISC_1.product X (RELAT_1.rng R) =
        (∅ : TarskiSet.{u}) := by
    have hprod :
        ZFMISC_1.product Y X ∩ ZFMISC_1.product X (RELAT_1.rng R) =
          ZFMISC_1.product (Y ∩ X) (X ∩ RELAT_1.rng R) :=
      (ZFMISC_1.th100 (X1 := Y) (X2 := X) (Y1 := X)
        (Y2 := RELAT_1.rng R)).symm
    have hYX : Y ∩ X = (∅ : TarskiSet.{u}) := by
      rw [XBOOLE_0.inter_comm]; exact hmiss
    rw [hprod, hYX]
    exact (ZFMISC_1.th90 (X := (∅ : TarskiSet.{u}))
      (Y := X ∩ RELAT_1.rng R)).mpr (Or.inl rfl)
  have hB :
      RELAT_1.restrict R X ⊆
        ZFMISC_1.product X Y ∩ ZFMISC_1.product X (RELAT_1.rng R) := by
    intro p hp
    have hp' := hdist ▸ hsub p hp
    rcases (XBOOLE_0.def3 _ _ p).mp hp' with hL | hR'
    · exact hL
    · exact False.elim ((XBOOLE_0.empty_iff p).mp (hempty ▸ hR'))
  exact XBOOLE_1.th18 hB

/-- `SYSREL:11` -/
theorem th11 {R S : TarskiSet.{u}} (h : R ⊆ S) :
    RELAT_1.converse R ⊆ RELAT_1.converse S := by
  have hunion : R ∪ S = S := XBOOLE_1.th12 h
  have hconv :
      RELAT_1.converse R ∪ RELAT_1.converse S = RELAT_1.converse S := by
    rw [← RELAT_1.th23 (P := R) (R := S), hunion]
  intro p hp
  exact hconv ▸ (XBOOLE_0.def3 _ _ p).mpr (Or.inl hp)

/-- `SYSREL` local `Lm2` -/
theorem lm2 (X : TarskiSet.{u}) :
    RELAT_1.id X ⊆ ZFMISC_1.product X X :=
  RELAT_1.rel_subset (RELAT_1.id_isRelation X) fun x y hp =>
    let ⟨hx, heq⟩ := (RELAT_1.def10 X x y).mp hp
    (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := X)).mpr
      ⟨hx, heq ▸ hx⟩

/-- `SYSREL:12` (`Th12`) -/
theorem th12 (X : TarskiSet.{u}) :
    RELAT_1.comp (RELAT_1.id X) (RELAT_1.id X) = RELAT_1.id X := by
  have h := RELAT_1.th52 (RELAT_1.id_isRelation X)
  rw [RELAT_1.id_dom] at h
  exact h

/-- `SYSREL:13` -/
theorem th13 (x : TarskiSet.{u}) :
    RELAT_1.id (TARSKI.singleton x) =
      TARSKI.singleton (TARSKI.pair x x) := by
  have hx : x ∈ TARSKI.singleton x := (singleton_iff x x).mpr rfl
  have hp : TARSKI.pair x x ∈ RELAT_1.id (TARSKI.singleton x) :=
    (RELAT_1.def10 (TARSKI.singleton x) x x).mpr ⟨hx, rfl⟩
  have h1 :
      TARSKI.singleton (TARSKI.pair x x) ⊆
        RELAT_1.id (TARSKI.singleton x) :=
    (ZFMISC_1.th31 (x := TARSKI.pair x x)
      (X := RELAT_1.id (TARSKI.singleton x))).mpr hp
  have hprod :
      ZFMISC_1.product (TARSKI.singleton x) (TARSKI.singleton x) =
        TARSKI.singleton (TARSKI.pair x x) :=
    ZFMISC_1.th29
  have h2 :
      RELAT_1.id (TARSKI.singleton x) ⊆
        TARSKI.singleton (TARSKI.pair x x) := by
    rw [← hprod]; exact lm2 (TARSKI.singleton x)
  exact (XBOOLE_0.def10).mpr ⟨h2, h1⟩

/-- `SYSREL:14` (`Th14`) -/
theorem th14 (X Y : TarskiSet.{u}) :
    RELAT_1.id (X ∪ Y) = RELAT_1.id X ∪ RELAT_1.id Y ∧
      RELAT_1.id (X ∩ Y) = RELAT_1.id X ∩ RELAT_1.id Y ∧
      RELAT_1.id (X \ Y) = RELAT_1.id X \ RELAT_1.id Y := by
  refine ⟨?_, ?_, ?_⟩
  · exact RELAT_1.rel_eq (RELAT_1.id_isRelation _)
      (RELAT_1.union_isRelation (RELAT_1.id_isRelation X)
        (RELAT_1.id_isRelation Y)) fun x y => by
      constructor
      · intro h
        have ⟨hx, heq⟩ := (RELAT_1.def10 (X ∪ Y) x y).mp h
        rcases (XBOOLE_0.def3 X Y x).mp hx with hxX | hxY
        · exact (XBOOLE_0.def3 _ _ _).mpr
            (Or.inl ((RELAT_1.def10 X x y).mpr ⟨hxX, heq⟩))
        · exact (XBOOLE_0.def3 _ _ _).mpr
            (Or.inr ((RELAT_1.def10 Y x y).mpr ⟨hxY, heq⟩))
      · intro h
        rcases (XBOOLE_0.def3 _ _ _).mp h with hX | hY
        · have ⟨hx, heq⟩ := (RELAT_1.def10 X x y).mp hX
          exact (RELAT_1.def10 (X ∪ Y) x y).mpr
            ⟨(XBOOLE_0.def3 X Y x).mpr (Or.inl hx), heq⟩
        · have ⟨hy, heq⟩ := (RELAT_1.def10 Y x y).mp hY
          exact (RELAT_1.def10 (X ∪ Y) x y).mpr
            ⟨(XBOOLE_0.def3 X Y x).mpr (Or.inr hy), heq⟩
  · exact RELAT_1.rel_eq (RELAT_1.id_isRelation _)
      (RELAT_1.inter_isRelation (RELAT_1.id_isRelation X)) fun x y => by
      constructor
      · intro h
        have ⟨hx, heq⟩ := (RELAT_1.def10 (X ∩ Y) x y).mp h
        have ⟨hxX, hxY⟩ := (XBOOLE_0.def4 X Y x).mp hx
        exact (XBOOLE_0.def4 _ _ _).mpr
          ⟨(RELAT_1.def10 X x y).mpr ⟨hxX, heq⟩,
            (RELAT_1.def10 Y x y).mpr ⟨hxY, heq⟩⟩
      · intro h
        have ⟨hX, hY⟩ := (XBOOLE_0.def4 _ _ _).mp h
        have ⟨hx, heq⟩ := (RELAT_1.def10 X x y).mp hX
        have ⟨hy, _⟩ := (RELAT_1.def10 Y x y).mp hY
        exact (RELAT_1.def10 (X ∩ Y) x y).mpr
          ⟨(XBOOLE_0.def4 X Y x).mpr ⟨hx, hy⟩, heq⟩
  · exact RELAT_1.rel_eq (RELAT_1.id_isRelation _)
      (RELAT_1.diff_isRelation (RELAT_1.id_isRelation X)) fun x y => by
      constructor
      · intro h
        have ⟨hx, heq⟩ := (RELAT_1.def10 (X \ Y) x y).mp h
        have ⟨hxX, hxY⟩ := (XBOOLE_0.def5 X Y x).mp hx
        have hnot : TARSKI.pair x y ∉ RELAT_1.id Y := fun hid =>
          hxY ((RELAT_1.def10 Y x y).mp hid).1
        exact (XBOOLE_0.def5 _ _ _).mpr
          ⟨(RELAT_1.def10 X x y).mpr ⟨hxX, heq⟩, hnot⟩
      · intro h
        have ⟨hX, hnot⟩ := (XBOOLE_0.def5 _ _ _).mp h
        have ⟨hx, heq⟩ := (RELAT_1.def10 X x y).mp hX
        have hxY : x ∉ Y := fun hy =>
          hnot ((RELAT_1.def10 Y x y).mpr ⟨hy, heq⟩)
        exact (RELAT_1.def10 (X \ Y) x y).mpr
          ⟨(XBOOLE_0.def5 X Y x).mpr ⟨hx, hxY⟩, heq⟩

/-- `SYSREL:15` (`Th15`) -/
theorem th15 {X Y : TarskiSet.{u}} (h : X ⊆ Y) :
    RELAT_1.id X ⊆ RELAT_1.id Y := by
  have hunion : X ∪ Y = Y := XBOOLE_1.th12 h
  have hid : RELAT_1.id X ∪ RELAT_1.id Y = RELAT_1.id Y := by
    rw [← (th14 X Y).1, hunion]
  intro p hp
  exact hid ▸ (XBOOLE_0.def3 _ _ p).mpr (Or.inl hp)

/-- `SYSREL:16` -/
theorem th16 (X Y : TarskiSet.{u}) :
    RELAT_1.id (X \ Y) \ RELAT_1.id X = (∅ : TarskiSet.{u}) :=
  (XBOOLE_1.th37).mpr
    (th15 (XBOOLE_1.th36 (X := X) (Y := Y)))

/-- `SYSREL:17` -/
theorem th17 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (h : R ⊆ RELAT_1.id (RELAT_1.dom R)) :
    R = RELAT_1.id (RELAT_1.dom R) :=
  RELAT_1.rel_eq hR (RELAT_1.id_isRelation _) fun x y => by
    constructor
    · intro hp
      exact h _ hp
    · intro hp
      have ⟨hx, heq⟩ := (RELAT_1.def10 (RELAT_1.dom R) x y).mp hp
      obtain ⟨z, hz⟩ := (RELAT_1.dom_iff R x).mp hx
      have hid := h _ hz
      have ⟨_, heqz⟩ := (RELAT_1.def10 (RELAT_1.dom R) x z).mp hid
      exact heq ▸ heqz ▸ hz

/-- `SYSREL:18` -/
theorem th18 {R X : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (h : RELAT_1.id X ⊆ R ∪ RELAT_1.converse R) :
    RELAT_1.id X ⊆ R ∧ RELAT_1.id X ⊆ RELAT_1.converse R := by
  have hxx : ∀ x, x ∈ X → TARSKI.pair x x ∈ R ∧
      TARSKI.pair x x ∈ RELAT_1.converse R := by
    intro x hx
    have hid : TARSKI.pair x x ∈ RELAT_1.id X :=
      (RELAT_1.def10 X x x).mpr ⟨hx, rfl⟩
    have hor := (XBOOLE_0.def3 R (RELAT_1.converse R) _).mp (h _ hid)
    have hRxx : TARSKI.pair x x ∈ R := by
      rcases hor with hR' | hC
      · exact hR'
      · exact (RELAT_1.def7 R x x).mp hC
    exact ⟨hRxx, (RELAT_1.def7 R x x).mpr hRxx⟩
  exact ⟨
    RELAT_1.th47 (fun x hx => (hxx x hx).1),
    RELAT_1.th47 (fun x hx => (hxx x hx).2)⟩

/-- `SYSREL:19` -/
theorem th19 {R X : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (h : RELAT_1.id X ⊆ R) : RELAT_1.id X ⊆ RELAT_1.converse R :=
  RELAT_1.th47 fun x hx =>
    (RELAT_1.def7 R x x).mpr
      (h _ ((RELAT_1.def10 X x x).mpr ⟨hx, rfl⟩))

/-- `SYSREL:20` -/
theorem th20 {R X : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (h : R ⊆ ZFMISC_1.product X X) :
    R \ RELAT_1.id (RELAT_1.dom R) = R \ RELAT_1.id X ∧
      R \ RELAT_1.id (RELAT_1.rng R) = R \ RELAT_1.id X := by
  have hdom : RELAT_1.dom R ⊆ X := (th3 hR h).1
  have hrng : RELAT_1.rng R ⊆ X := (th3 hR h).2
  have hidDom : RELAT_1.id (RELAT_1.dom R) ⊆ RELAT_1.id X :=
    th15 hdom
  have hidRng : RELAT_1.id (RELAT_1.rng R) ⊆ RELAT_1.id X :=
    th15 hrng
  have h1 : R \ RELAT_1.id (RELAT_1.dom R) ⊆ R \ RELAT_1.id X := by
    intro p hp
    have ⟨hpR, hnot⟩ :=
      (XBOOLE_0.def5 R (RELAT_1.id (RELAT_1.dom R)) p).mp hp
    have ⟨a, b, heq⟩ := hR p hpR
    have hpab : TARSKI.pair a b ∈ R := heq ▸ hpR
    have hnotab :
        TARSKI.pair a b ∉ RELAT_1.id (RELAT_1.dom R) :=
      fun hid => hnot (heq ▸ hid)
    have hnotX : TARSKI.pair a b ∉ RELAT_1.id X := fun hid =>
      let ⟨ha, heqab⟩ := (RELAT_1.def10 X a b).mp hid
      hnotab
        ((RELAT_1.def10 (RELAT_1.dom R) a b).mpr
          ⟨RELAT_1.pair_mem_dom hpab, heqab⟩)
    exact (XBOOLE_0.def5 R (RELAT_1.id X) p).mpr
      ⟨hpR, fun hid => hnotX (heq ▸ hid)⟩
  have h2 : R \ RELAT_1.id (RELAT_1.rng R) ⊆ R \ RELAT_1.id X := by
    intro p hp
    have ⟨hpR, hnot⟩ :=
      (XBOOLE_0.def5 R (RELAT_1.id (RELAT_1.rng R)) p).mp hp
    have ⟨a, b, heq⟩ := hR p hpR
    have hpab : TARSKI.pair a b ∈ R := heq ▸ hpR
    have hnotab :
        TARSKI.pair a b ∉ RELAT_1.id (RELAT_1.rng R) :=
      fun hid => hnot (heq ▸ hid)
    have hnotX : TARSKI.pair a b ∉ RELAT_1.id X := fun hid =>
      let ⟨_, heqab⟩ := (RELAT_1.def10 X a b).mp hid
      hnotab
        ((RELAT_1.def10 (RELAT_1.rng R) a b).mpr
          ⟨heqab ▸ RELAT_1.pair_mem_rng hpab, heqab⟩)
    exact (XBOOLE_0.def5 R (RELAT_1.id X) p).mpr
      ⟨hpR, fun hid => hnotX (heq ▸ hid)⟩
  exact ⟨
    (XBOOLE_0.def10).mpr
      ⟨h1, XBOOLE_1.th34 hidDom⟩,
    (XBOOLE_0.def10).mpr
      ⟨h2, XBOOLE_1.th34 hidRng⟩⟩

/-- `SYSREL:21` -/
theorem th21 {R X : TarskiSet.{u}} (_hR : RELAT_1.isRelation R) :
    (RELAT_1.comp (RELAT_1.id X) (R \ RELAT_1.id X) = (∅ : TarskiSet.{u}) →
      RELAT_1.dom (R \ RELAT_1.id X) = RELAT_1.dom R \ X) ∧
    (RELAT_1.comp (R \ RELAT_1.id X) (RELAT_1.id X) = (∅ : TarskiSet.{u}) →
      RELAT_1.rng (R \ RELAT_1.id X) = RELAT_1.rng R \ X) := by
  constructor
  · intro hcomp
    have h1 : RELAT_1.dom (R \ RELAT_1.id X) ⊆ RELAT_1.dom R \ X := by
      intro u hu
      obtain ⟨v, hp⟩ := (RELAT_1.dom_iff (R \ RELAT_1.id X) u).mp hu
      have ⟨hpR, _⟩ := (XBOOLE_0.def5 R (RELAT_1.id X) _).mp hp
      have hnotX : u ∉ X := fun huX =>
        (XBOOLE_0.empty_iff (TARSKI.pair u v)).mp
          (hcomp ▸ (RELAT_1.def8 (RELAT_1.id X) (R \ RELAT_1.id X)
            u v).mpr ⟨u, (RELAT_1.def10 X u u).mpr ⟨huX, rfl⟩, hp⟩)
      exact (XBOOLE_0.def5 (RELAT_1.dom R) X u).mpr
        ⟨RELAT_1.pair_mem_dom hpR, hnotX⟩
    have h2 : RELAT_1.dom R \ X ⊆ RELAT_1.dom (R \ RELAT_1.id X) := by
      have h := RELAT_1.th3 (P := R) (R := RELAT_1.id X)
      rw [RELAT_1.id_dom] at h
      exact h
    exact (XBOOLE_0.def10).mpr ⟨h1, h2⟩
  · intro hcomp
    have h1 : RELAT_1.rng (R \ RELAT_1.id X) ⊆ RELAT_1.rng R \ X := by
      intro v hv
      obtain ⟨u, hp⟩ := (RELAT_1.rng_iff (R \ RELAT_1.id X) v).mp hv
      have ⟨hpR, _⟩ := (XBOOLE_0.def5 R (RELAT_1.id X) _).mp hp
      have hnotX : v ∉ X := fun hvX =>
        (XBOOLE_0.empty_iff (TARSKI.pair u v)).mp
          (hcomp ▸ (RELAT_1.def8 (R \ RELAT_1.id X) (RELAT_1.id X)
            u v).mpr ⟨v, hp, (RELAT_1.def10 X v v).mpr ⟨hvX, rfl⟩⟩)
      exact (XBOOLE_0.def5 (RELAT_1.rng R) X v).mpr
        ⟨RELAT_1.pair_mem_rng hpR, hnotX⟩
    have h2 : RELAT_1.rng R \ X ⊆ RELAT_1.rng (R \ RELAT_1.id X) := by
      have h := RELAT_1.th14 (P := R) (R := RELAT_1.id X)
      rw [RELAT_1.id_rng] at h
      exact h
    exact (XBOOLE_0.def10).mpr ⟨h1, h2⟩

/-- `SYSREL:22` (`Th22`) -/
theorem th22 {R : TarskiSet.{u}} (_hR : RELAT_1.isRelation R) :
    (R ⊆ RELAT_1.comp R R →
      RELAT_1.comp R (R \ RELAT_1.id (RELAT_1.rng R)) =
        (∅ : TarskiSet.{u}) →
      RELAT_1.id (RELAT_1.rng R) ⊆ R) ∧
    (R ⊆ RELAT_1.comp R R →
      RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R)) R =
        (∅ : TarskiSet.{u}) →
      RELAT_1.id (RELAT_1.dom R) ⊆ R) := by
  constructor
  · intro hRR hcomp
    exact RELAT_1.th47 fun y hy => by
      obtain ⟨x, hp⟩ := (RELAT_1.rng_iff R y).mp hy
      obtain ⟨z, hz1, hz2⟩ :=
        (RELAT_1.def8 R R x y).mp (hRR _ hp)
      have heq : z = y := by
        by_cases hzy : z = y
        · exact hzy
        · have hnot :
              TARSKI.pair z y ∉ RELAT_1.id (RELAT_1.rng R) :=
            fun hid => hzy ((RELAT_1.def10 _ z y).mp hid).2
          have hdiff :
              TARSKI.pair z y ∈ R \ RELAT_1.id (RELAT_1.rng R) :=
            (XBOOLE_0.def5 _ _ _).mpr ⟨hz2, hnot⟩
          exact ((XBOOLE_0.empty_iff _).mp
            (hcomp ▸ (RELAT_1.def8 R (R \ RELAT_1.id (RELAT_1.rng R))
              x y).mpr ⟨z, hz1, hdiff⟩)).elim
      exact heq ▸ hz2
  · intro hRR hcomp
    exact RELAT_1.th47 fun x hx => by
      obtain ⟨y, hp⟩ := (RELAT_1.dom_iff R x).mp hx
      obtain ⟨z, hz1, hz2⟩ :=
        (RELAT_1.def8 R R x y).mp (hRR _ hp)
      have heq : z = x := by
        by_cases hzx : z = x
        · exact hzx
        · have hnot :
              TARSKI.pair x z ∉ RELAT_1.id (RELAT_1.dom R) :=
            fun hid => hzx ((RELAT_1.def10 _ x z).mp hid).2.symm
          have hdiff :
              TARSKI.pair x z ∈ R \ RELAT_1.id (RELAT_1.dom R) :=
            (XBOOLE_0.def5 _ _ _).mpr ⟨hz1, hnot⟩
          exact ((XBOOLE_0.empty_iff _).mp
            (hcomp ▸ (RELAT_1.def8 (R \ RELAT_1.id (RELAT_1.dom R)) R
              x y).mpr ⟨z, hdiff, hz2⟩)).elim
      exact heq ▸ hz1

/-- `SYSREL:23` -/
theorem th23 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    (R ⊆ RELAT_1.comp R R →
      RELAT_1.comp R (R \ RELAT_1.id (RELAT_1.rng R)) =
        (∅ : TarskiSet.{u}) →
      R ∩ RELAT_1.id (RELAT_1.rng R) = RELAT_1.id (RELAT_1.rng R)) ∧
    (R ⊆ RELAT_1.comp R R →
      RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R)) R =
        (∅ : TarskiSet.{u}) →
      R ∩ RELAT_1.id (RELAT_1.dom R) = RELAT_1.id (RELAT_1.dom R)) :=
  ⟨fun h1 h2 => by
      rw [XBOOLE_0.inter_comm]
      exact XBOOLE_1.th28 ((th22 hR).1 h1 h2),
    fun h1 h2 => by
      rw [XBOOLE_0.inter_comm]
      exact XBOOLE_1.th28 ((th22 hR).2 h1 h2)⟩

/-- `SYSREL:24` -/
theorem th24 {R X : TarskiSet.{u}} (_hR : RELAT_1.isRelation R) :
    (RELAT_1.comp R (R \ RELAT_1.id X) = (∅ : TarskiSet.{u}) →
      RELAT_1.comp R (R \ RELAT_1.id (RELAT_1.rng R)) =
        (∅ : TarskiSet.{u})) ∧
    (RELAT_1.comp (R \ RELAT_1.id X) R = (∅ : TarskiSet.{u}) →
      RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R)) R =
        (∅ : TarskiSet.{u})) := by
  constructor
  · intro hcomp
    refine RELAT_1.th37 (RELAT_1.comp_isRelation _ _) fun a b hp => ?_
    obtain ⟨z, hzR, hzdiff⟩ :=
      (RELAT_1.def8 R (R \ RELAT_1.id (RELAT_1.rng R)) a b).mp hp
    have ⟨hzR', hnot⟩ :=
      (XBOOLE_0.def5 R (RELAT_1.id (RELAT_1.rng R)) _).mp hzdiff
    have hzrng : z ∈ RELAT_1.rng R := RELAT_1.pair_mem_rng hzR
    have hzne : z ≠ b := fun heq =>
      hnot ((RELAT_1.def10 (RELAT_1.rng R) z b).mpr ⟨hzrng, heq⟩)
    have hnotX : TARSKI.pair z b ∉ RELAT_1.id X := fun hid =>
      hzne ((RELAT_1.def10 X z b).mp hid).2
    have hdiff : TARSKI.pair z b ∈ R \ RELAT_1.id X :=
      (XBOOLE_0.def5 _ _ _).mpr ⟨hzR', hnotX⟩
    exact (XBOOLE_0.empty_iff _).mp
      (hcomp ▸ (RELAT_1.def8 R (R \ RELAT_1.id X) a b).mpr
        ⟨z, hzR, hdiff⟩)
  · intro hcomp
    refine RELAT_1.th37 (RELAT_1.comp_isRelation _ _) fun a b hp => ?_
    obtain ⟨z, hzdiff, hzR⟩ :=
      (RELAT_1.def8 (R \ RELAT_1.id (RELAT_1.dom R)) R a b).mp hp
    have ⟨hzR', hnot⟩ :=
      (XBOOLE_0.def5 R (RELAT_1.id (RELAT_1.dom R)) _).mp hzdiff
    have hnotX : TARSKI.pair a z ∉ RELAT_1.id X := fun hid =>
      let ⟨_, heq⟩ := (RELAT_1.def10 X a z).mp hid
      hnot ((RELAT_1.def10 (RELAT_1.dom R) a z).mpr
        ⟨RELAT_1.pair_mem_dom hzR', heq⟩)
    have hdiff : TARSKI.pair a z ∈ R \ RELAT_1.id X :=
      (XBOOLE_0.def5 _ _ _).mpr ⟨hzR', hnotX⟩
    exact (XBOOLE_0.empty_iff _).mp
      (hcomp ▸ (RELAT_1.def8 (R \ RELAT_1.id X) R a b).mpr
        ⟨z, hdiff, hzR⟩)

/-! ## Closure relation `CL R` (`SYSREL:def 1`) -/

/-- Mizar `CL R` = `R /\ id dom R`. -/
noncomputable def CL (R : TarskiSet.{u}) : TarskiSet.{u} :=
  R ∩ RELAT_1.id (RELAT_1.dom R)

theorem CL_isRelation {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    RELAT_1.isRelation (CL R) :=
  RELAT_1.inter_isRelation hR

theorem CL_eq (R : TarskiSet.{u}) :
    CL R = R ∩ RELAT_1.id (RELAT_1.dom R) :=
  rfl

/-- `SYSREL:25` (`Th25`) -/
theorem th25 {R x y : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (h : TARSKI.pair x y ∈ CL R) :
    x ∈ RELAT_1.dom (CL R) ∧ x = y := by
  have ⟨_, hid⟩ :=
    (XBOOLE_0.def4 R (RELAT_1.id (RELAT_1.dom R)) _).mp h
  have ⟨_, heq⟩ := (RELAT_1.def10 (RELAT_1.dom R) x y).mp hid
  exact ⟨RELAT_1.pair_mem_dom h, heq⟩

/-- `SYSREL:26` (`Th26`) -/
theorem th26 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    RELAT_1.dom (CL R) = RELAT_1.rng (CL R) := by
  apply eq_of_mem
  intro u
  constructor
  · intro hu
    obtain ⟨v, hp⟩ := (RELAT_1.dom_iff (CL R) u).mp hu
    have ⟨_, hid⟩ :=
      (XBOOLE_0.def4 R (RELAT_1.id (RELAT_1.dom R)) _).mp hp
    have ⟨_, heq⟩ := (RELAT_1.def10 (RELAT_1.dom R) u v).mp hid
    have hp' : TARSKI.pair u u ∈ CL R := heq ▸ hp
    exact (RELAT_1.rng_iff (CL R) u).mpr ⟨u, hp'⟩
  · intro hu
    obtain ⟨v, hp⟩ := (RELAT_1.rng_iff (CL R) u).mp hu
    have ⟨_, hid⟩ :=
      (XBOOLE_0.def4 R (RELAT_1.id (RELAT_1.dom R)) _).mp hp
    have ⟨_, heq⟩ := (RELAT_1.def10 (RELAT_1.dom R) v u).mp hid
    have hp' : TARSKI.pair u u ∈ CL R := heq ▸ hp
    exact (RELAT_1.dom_iff (CL R) u).mpr ⟨u, hp'⟩

/-- `SYSREL:27` (`Th27`) -/
theorem th27 {R x : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    (x ∈ RELAT_1.dom (CL R) ↔ x ∈ RELAT_1.dom R ∧ TARSKI.pair x x ∈ R) ∧
    (x ∈ RELAT_1.rng (CL R) ↔ x ∈ RELAT_1.dom R ∧ TARSKI.pair x x ∈ R) ∧
    (x ∈ RELAT_1.rng (CL R) ↔ x ∈ RELAT_1.rng R ∧ TARSKI.pair x x ∈ R) ∧
    (x ∈ RELAT_1.dom (CL R) ↔ x ∈ RELAT_1.rng R ∧ TARSKI.pair x x ∈ R) := by
  have hA : x ∈ RELAT_1.dom R ∧ TARSKI.pair x x ∈ R →
      x ∈ RELAT_1.dom (CL R) := fun ⟨hx, hp⟩ =>
    (RELAT_1.dom_iff (CL R) x).mpr
      ⟨x, (XBOOLE_0.def4 R (RELAT_1.id (RELAT_1.dom R)) _).mpr
        ⟨hp, (RELAT_1.def10 (RELAT_1.dom R) x x).mpr ⟨hx, rfl⟩⟩⟩
  have hB : x ∈ RELAT_1.dom (CL R) →
      x ∈ RELAT_1.dom R ∧ TARSKI.pair x x ∈ R := fun hx =>
    let ⟨y, hp⟩ := (RELAT_1.dom_iff (CL R) x).mp hx
    let ⟨hpR, hid⟩ :=
      (XBOOLE_0.def4 R (RELAT_1.id (RELAT_1.dom R)) _).mp hp
    let ⟨hd, heq⟩ := (RELAT_1.def10 (RELAT_1.dom R) x y).mp hid
    ⟨hd, heq ▸ hpR⟩
  have hdom : x ∈ RELAT_1.dom (CL R) ↔
      x ∈ RELAT_1.dom R ∧ TARSKI.pair x x ∈ R :=
    ⟨hB, hA⟩
  have hrng_dom : x ∈ RELAT_1.rng (CL R) ↔
      x ∈ RELAT_1.dom R ∧ TARSKI.pair x x ∈ R :=
    (th26 hR ▸ Iff.rfl : x ∈ RELAT_1.rng (CL R) ↔
      x ∈ RELAT_1.dom (CL R)).trans hdom
  have hrng :
      x ∈ RELAT_1.rng (CL R) ↔
        x ∈ RELAT_1.rng R ∧ TARSKI.pair x x ∈ R := by
    constructor
    · intro hx
      have ⟨hd, hp⟩ := hrng_dom.mp hx
      obtain ⟨y, hy⟩ := (RELAT_1.dom_iff R x).mp hd
      exact ⟨RELAT_1.pair_mem_rng hp, hp⟩
    · intro ⟨hr, hp⟩
      have hd : x ∈ RELAT_1.dom R := RELAT_1.pair_mem_dom hp
      exact hrng_dom.mpr ⟨hd, hp⟩
  have hdom_rng :
      x ∈ RELAT_1.dom (CL R) ↔
        x ∈ RELAT_1.rng R ∧ TARSKI.pair x x ∈ R :=
    hdom.trans ⟨
      fun ⟨hd, hp⟩ => ⟨RELAT_1.pair_mem_rng hp, hp⟩,
      fun ⟨_, hp⟩ => ⟨RELAT_1.pair_mem_dom hp, hp⟩⟩
  exact ⟨hdom, hrng_dom, hrng, hdom_rng⟩

/-- `SYSREL:28` (`Th28`) -/
theorem th28 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    CL R = RELAT_1.id (RELAT_1.dom (CL R)) :=
  RELAT_1.rel_eq (CL_isRelation hR) (RELAT_1.id_isRelation _)
    fun x y => by
    constructor
    · intro h
      have ⟨_, hid⟩ :=
        (XBOOLE_0.def4 R (RELAT_1.id (RELAT_1.dom R)) _).mp h
      have ⟨_, heq⟩ := (RELAT_1.def10 (RELAT_1.dom R) x y).mp hid
      exact (RELAT_1.def10 (RELAT_1.dom (CL R)) x y).mpr
        ⟨RELAT_1.pair_mem_dom h, heq⟩
    · intro h
      have ⟨hx, heq⟩ :=
        (RELAT_1.def10 (RELAT_1.dom (CL R)) x y).mp h
      obtain ⟨z, hz⟩ := (RELAT_1.dom_iff (CL R) x).mp hx
      have ⟨_, heqz⟩ := th25 hR hz
      exact heq ▸ heqz ▸ hz

/-- `SYSREL:29` (`Th29`) -/
theorem th29 {R x y : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    (RELAT_1.comp R R = R →
      RELAT_1.comp R (R \ CL R) = (∅ : TarskiSet.{u}) →
      TARSKI.pair x y ∈ R → x ≠ y →
        x ∈ RELAT_1.dom R \ RELAT_1.dom (CL R) ∧
          y ∈ RELAT_1.dom (CL R)) ∧
    (RELAT_1.comp R R = R →
      RELAT_1.comp (R \ CL R) R = (∅ : TarskiSet.{u}) →
      TARSKI.pair x y ∈ R → x ≠ y →
        y ∈ RELAT_1.rng R \ RELAT_1.dom (CL R) ∧
          x ∈ RELAT_1.dom (CL R)) := by
  constructor
  · intro hRR hcomp hp hne
    obtain ⟨z, hz1, hz2⟩ :=
      (RELAT_1.def8 R R x y).mp (hRR.symm ▸ hp)
    have heq : z = y := by
      by_cases hzy : z = y
      · exact hzy
      · have hnot :
            TARSKI.pair z y ∉ RELAT_1.id (RELAT_1.dom R) :=
          fun hid => hzy ((RELAT_1.def10 _ z y).mp hid).2
        have hnotCL : TARSKI.pair z y ∉ CL R := fun hCL =>
          hnot ((XBOOLE_0.def4 _ _ _).mp hCL).2
        have hdiff : TARSKI.pair z y ∈ R \ CL R :=
          (XBOOLE_0.def5 _ _ _).mpr ⟨hz2, hnotCL⟩
        exact False.elim ((XBOOLE_0.empty_iff _).mp
          (hcomp ▸ (RELAT_1.def8 R (R \ CL R) x y).mpr
            ⟨z, hz1, hdiff⟩))
    have hnotid : TARSKI.pair x y ∉ RELAT_1.id (RELAT_1.dom R) :=
      fun hid => hne ((RELAT_1.def10 _ x y).mp hid).2
    have hnotCL : TARSKI.pair x y ∉ CL R := fun hCL =>
      hnotid ((XBOOLE_0.def4 _ _ _).mp hCL).2
    have hdiff : TARSKI.pair x y ∈ R \ CL R :=
      (XBOOLE_0.def5 _ _ _).mpr ⟨hp, hnotCL⟩
    have hnotx : x ∉ RELAT_1.dom (CL R) := fun hx =>
      False.elim ((XBOOLE_0.empty_iff _).mp
        (hcomp ▸ (RELAT_1.def8 R (R \ CL R) x y).mpr
          ⟨x, ((th27 hR).1.mp hx).2, hdiff⟩))
    have hxdom : x ∈ RELAT_1.dom R := RELAT_1.pair_mem_dom hz1
    have hydom : y ∈ RELAT_1.dom (CL R) :=
      ((th27 hR).2.2.2).mpr ⟨RELAT_1.pair_mem_rng hp, heq ▸ hz2⟩
    exact ⟨(XBOOLE_0.def5 _ _ _).mpr ⟨hxdom, hnotx⟩, hydom⟩
  · intro hRR hcomp hp hne
    obtain ⟨z, hz1, hz2⟩ :=
      (RELAT_1.def8 R R x y).mp (hRR.symm ▸ hp)
    have heq : z = x := by
      by_cases hzx : z = x
      · exact hzx
      · have hnot :
            TARSKI.pair x z ∉ RELAT_1.id (RELAT_1.dom R) :=
          fun hid => hzx ((RELAT_1.def10 _ x z).mp hid).2.symm
        have hnotCL : TARSKI.pair x z ∉ CL R := fun hCL =>
          hnot ((XBOOLE_0.def4 _ _ _).mp hCL).2
        have hdiff : TARSKI.pair x z ∈ R \ CL R :=
          (XBOOLE_0.def5 _ _ _).mpr ⟨hz1, hnotCL⟩
        exact False.elim ((XBOOLE_0.empty_iff _).mp
          (hcomp ▸ (RELAT_1.def8 (R \ CL R) R x y).mpr
            ⟨z, hdiff, hz2⟩))
    have hnotid : TARSKI.pair x y ∉ RELAT_1.id (RELAT_1.dom R) :=
      fun hid => hne ((RELAT_1.def10 _ x y).mp hid).2
    have hnotCL : TARSKI.pair x y ∉ CL R := fun hCL =>
      hnotid ((XBOOLE_0.def4 _ _ _).mp hCL).2
    have hdiff : TARSKI.pair x y ∈ R \ CL R :=
      (XBOOLE_0.def5 _ _ _).mpr ⟨hp, hnotCL⟩
    have hnoty : y ∉ RELAT_1.dom (CL R) := fun hy =>
      False.elim ((XBOOLE_0.empty_iff _).mp
        (hcomp ▸ (RELAT_1.def8 (R \ CL R) R x y).mpr
          ⟨y, hdiff, ((th27 hR).1.mp hy).2⟩))
    have hyrng : y ∈ RELAT_1.rng R := RELAT_1.pair_mem_rng hz2
    have hxdom : x ∈ RELAT_1.dom (CL R) :=
      (th27 hR).1.mpr ⟨RELAT_1.pair_mem_dom hp, heq ▸ hz1⟩
    exact ⟨(XBOOLE_0.def5 _ _ _).mpr ⟨hyrng, hnoty⟩, hxdom⟩

/-- `SYSREL:30` -/
theorem th30 {R x y : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    (RELAT_1.comp R R = R →
      RELAT_1.comp R (R \ RELAT_1.id (RELAT_1.dom R)) =
        (∅ : TarskiSet.{u}) →
      TARSKI.pair x y ∈ R → x ≠ y →
        x ∈ RELAT_1.dom R \ RELAT_1.dom (CL R) ∧
          y ∈ RELAT_1.dom (CL R)) ∧
    (RELAT_1.comp R R = R →
      RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R)) R =
        (∅ : TarskiSet.{u}) →
      TARSKI.pair x y ∈ R → x ≠ y →
        y ∈ RELAT_1.rng R \ RELAT_1.dom (CL R) ∧
          x ∈ RELAT_1.dom (CL R)) := by
  have hCL : R \ CL R = R \ RELAT_1.id (RELAT_1.dom R) :=
    XBOOLE_1.th47
  exact ⟨
    fun h1 h2 => (th29 hR).1 h1 (hCL ▸ h2),
    fun h1 h2 => (th29 hR).2 h1 (hCL ▸ h2)⟩

/-- `SYSREL:31` -/
theorem th31 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    (RELAT_1.comp R R = R →
      RELAT_1.comp R (R \ RELAT_1.id (RELAT_1.dom R)) =
        (∅ : TarskiSet.{u}) →
      RELAT_1.dom (CL R) = RELAT_1.rng R ∧
        RELAT_1.rng (CL R) = RELAT_1.rng R) ∧
    (RELAT_1.comp R R = R →
      RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R)) R =
        (∅ : TarskiSet.{u}) →
      RELAT_1.dom (CL R) = RELAT_1.dom R ∧
        RELAT_1.rng (CL R) = RELAT_1.dom R) := by
  constructor
  · intro hRR hcomp
    have hsub : RELAT_1.rng R ⊆ RELAT_1.dom (CL R) := by
      intro y hy
      obtain ⟨x, hp⟩ := (RELAT_1.rng_iff R y).mp hy
      obtain ⟨z, hz1, hz2⟩ :=
        (RELAT_1.def8 R R x y).mp (hRR.symm ▸ hp)
      have heq : z = y := by
        by_cases hzy : z = y
        · exact hzy
        · have hnot :
              TARSKI.pair z y ∉ RELAT_1.id (RELAT_1.dom R) :=
            fun hid => hzy ((RELAT_1.def10 _ z y).mp hid).2
          have hdiff :
              TARSKI.pair z y ∈ R \ RELAT_1.id (RELAT_1.dom R) :=
            (XBOOLE_0.def5 _ _ _).mpr ⟨hz2, hnot⟩
          exact False.elim ((XBOOLE_0.empty_iff _).mp
            (hcomp ▸ (RELAT_1.def8 R
              (R \ RELAT_1.id (RELAT_1.dom R)) x y).mpr
              ⟨z, hz1, hdiff⟩))
      have hzdom : z ∈ RELAT_1.dom R := RELAT_1.pair_mem_dom hz2
      have hid : TARSKI.pair z y ∈ RELAT_1.id (RELAT_1.dom R) :=
        (RELAT_1.def10 _ z y).mpr ⟨hzdom, heq⟩
      have hCL : TARSKI.pair z y ∈ CL R :=
        (XBOOLE_0.def4 _ _ _).mpr ⟨hz2, hid⟩
      exact heq ▸ RELAT_1.pair_mem_dom hCL
    have hCL_sub : CL R ⊆ R := XBOOLE_1.th17
    have hrng : RELAT_1.rng (CL R) ⊆ RELAT_1.rng R :=
      (RELAT_1.th11 hCL_sub).2
    have hdom : RELAT_1.dom (CL R) ⊆ RELAT_1.rng R :=
      th26 hR ▸ hrng
    have heq : RELAT_1.dom (CL R) = RELAT_1.rng R :=
      (XBOOLE_0.def10).mpr ⟨hdom, hsub⟩
    exact ⟨heq, th26 hR ▸ heq⟩
  · intro hRR hcomp
    have hsub : RELAT_1.dom R ⊆ RELAT_1.dom (CL R) := by
      intro x hx
      obtain ⟨y, hp⟩ := (RELAT_1.dom_iff R x).mp hx
      obtain ⟨z, hz1, hz2⟩ :=
        (RELAT_1.def8 R R x y).mp (hRR.symm ▸ hp)
      have heq : z = x := by
        by_cases hzx : z = x
        · exact hzx
        · have hnot :
              TARSKI.pair x z ∉ RELAT_1.id (RELAT_1.dom R) :=
            fun hid => hzx ((RELAT_1.def10 _ x z).mp hid).2.symm
          have hdiff :
              TARSKI.pair x z ∈ R \ RELAT_1.id (RELAT_1.dom R) :=
            (XBOOLE_0.def5 _ _ _).mpr ⟨hz1, hnot⟩
          exact False.elim ((XBOOLE_0.empty_iff _).mp
            (hcomp ▸ (RELAT_1.def8
              (R \ RELAT_1.id (RELAT_1.dom R)) R x y).mpr
              ⟨z, hdiff, hz2⟩))
      have hid : TARSKI.pair x z ∈ RELAT_1.id (RELAT_1.dom R) :=
        (RELAT_1.def10 _ x z).mpr ⟨hx, heq.symm⟩
      have hCL : TARSKI.pair x z ∈ CL R :=
        (XBOOLE_0.def4 _ _ _).mpr ⟨hz1, hid⟩
      exact heq ▸ (th26 hR ▸ RELAT_1.pair_mem_rng hCL)
    have hCL_sub : CL R ⊆ R := XBOOLE_1.th17
    have hdom : RELAT_1.dom (CL R) ⊆ RELAT_1.dom R :=
      (RELAT_1.th11 hCL_sub).1
    have heq : RELAT_1.dom (CL R) = RELAT_1.dom R :=
      (XBOOLE_0.def10).mpr ⟨hdom, hsub⟩
    exact ⟨heq, th26 hR ▸ heq⟩

/-- `SYSREL:32` (`Th32`) -/
theorem th32 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    RELAT_1.dom (CL R) ⊆ RELAT_1.dom R ∧
      RELAT_1.rng (CL R) ⊆ RELAT_1.rng R ∧
      RELAT_1.rng (CL R) ⊆ RELAT_1.dom R ∧
      RELAT_1.dom (CL R) ⊆ RELAT_1.rng R := by
  have hCL : CL R ⊆ R := XBOOLE_1.th17
  have ⟨hd, hr⟩ := RELAT_1.th11 hCL
  exact ⟨hd, hr, th26 hR ▸ hd, th26 hR ▸ hr⟩

/-- `SYSREL:33` -/
theorem th33 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    RELAT_1.id (RELAT_1.dom (CL R)) ⊆ RELAT_1.id (RELAT_1.dom R) ∧
      RELAT_1.id (RELAT_1.rng (CL R)) ⊆ RELAT_1.id (RELAT_1.dom R) := by
  have h1 := th15 (th32 hR).1
  exact ⟨h1, th26 hR ▸ h1⟩

/-- `SYSREL:34` (`Th34`) -/
theorem th34 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    RELAT_1.id (RELAT_1.dom (CL R)) ⊆ R ∧
      RELAT_1.id (RELAT_1.rng (CL R)) ⊆ R := by
  have h1 : RELAT_1.id (RELAT_1.dom (CL R)) ⊆ R :=
    RELAT_1.rel_subset (RELAT_1.id_isRelation _) fun x y hp =>
      let ⟨hx, heq⟩ := (RELAT_1.def10 (RELAT_1.dom (CL R)) x y).mp hp
      heq ▸ ((th27 hR).1.mp hx).2
  exact ⟨h1, th26 hR ▸ h1⟩

/-- `SYSREL:35` (`Th35`) -/
theorem th35 {R X : TarskiSet.{u}} (_hR : RELAT_1.isRelation R) :
    (RELAT_1.id X ⊆ R →
      RELAT_1.comp (RELAT_1.id X) (R \ RELAT_1.id X) =
        (∅ : TarskiSet.{u}) →
      RELAT_1.restrict R X = RELAT_1.id X) ∧
    (RELAT_1.id X ⊆ R →
      RELAT_1.comp (R \ RELAT_1.id X) (RELAT_1.id X) =
        (∅ : TarskiSet.{u}) →
      RELAT_1.restrictRng X R = RELAT_1.id X) := by
  constructor
  · intro hid hcomp
    have hRU : R ∪ RELAT_1.id X = R := by
      rw [XBOOLE_0.union_comm]; exact XBOOLE_1.th12 hid
    have hdiffU :
        (R \ RELAT_1.id X) ∪ RELAT_1.id X = R ∪ RELAT_1.id X := by
      rw [XBOOLE_0.union_comm (R \ RELAT_1.id X),
        XBOOLE_0.union_comm R (RELAT_1.id X)]
      exact XBOOLE_1.th39
    calc
      RELAT_1.restrict R X
          = RELAT_1.comp (RELAT_1.id X) R := RELAT_1.th65
      _ = RELAT_1.comp (RELAT_1.id X) (R ∪ RELAT_1.id X) := by
            rw [hRU]
      _ = RELAT_1.comp (RELAT_1.id X)
            ((R \ RELAT_1.id X) ∪ RELAT_1.id X) := by
            rw [hdiffU]
      _ = RELAT_1.comp (RELAT_1.id X) (R \ RELAT_1.id X) ∪
            RELAT_1.comp (RELAT_1.id X) (RELAT_1.id X) :=
            RELAT_1.th32
      _ = (∅ : TarskiSet.{u}) ∪ RELAT_1.id X := by
            rw [hcomp, th12 X]
      _ = RELAT_1.id X := XBOOLE_1.th12 XBOOLE_1.th2
  · intro hid hcomp
    have hRU : R ∪ RELAT_1.id X = R := by
      rw [XBOOLE_0.union_comm]; exact XBOOLE_1.th12 hid
    have hdiffU :
        (R \ RELAT_1.id X) ∪ RELAT_1.id X = R ∪ RELAT_1.id X := by
      rw [XBOOLE_0.union_comm (R \ RELAT_1.id X),
        XBOOLE_0.union_comm R (RELAT_1.id X)]
      exact XBOOLE_1.th39
    calc
      RELAT_1.restrictRng X R
          = RELAT_1.comp R (RELAT_1.id X) := RELAT_1.th92
      _ = RELAT_1.comp (R ∪ RELAT_1.id X) (RELAT_1.id X) := by
            rw [hRU]
      _ = RELAT_1.comp ((R \ RELAT_1.id X) ∪ RELAT_1.id X)
            (RELAT_1.id X) := by
            rw [hdiffU]
      _ = RELAT_1.comp (R \ RELAT_1.id X) (RELAT_1.id X) ∪
            RELAT_1.comp (RELAT_1.id X) (RELAT_1.id X) :=
            th6 _ _ _
      _ = (∅ : TarskiSet.{u}) ∪ RELAT_1.id X := by
            rw [hcomp, th12 X]
      _ = RELAT_1.id X := XBOOLE_1.th12 XBOOLE_1.th2

/-- `SYSREL:36` -/
theorem th36 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    (RELAT_1.comp (RELAT_1.id (RELAT_1.dom (CL R)))
        (R \ RELAT_1.id (RELAT_1.dom (CL R))) =
        (∅ : TarskiSet.{u}) →
      RELAT_1.restrict R (RELAT_1.dom (CL R)) =
          RELAT_1.id (RELAT_1.dom (CL R)) ∧
        RELAT_1.restrict R (RELAT_1.rng (CL R)) =
          RELAT_1.id (RELAT_1.dom (CL R))) ∧
    (RELAT_1.comp (R \ RELAT_1.id (RELAT_1.rng (CL R)))
        (RELAT_1.id (RELAT_1.rng (CL R))) =
        (∅ : TarskiSet.{u}) →
      RELAT_1.restrictRng (RELAT_1.dom (CL R)) R =
          RELAT_1.id (RELAT_1.dom (CL R)) ∧
        RELAT_1.restrictRng (RELAT_1.rng (CL R)) R =
          RELAT_1.id (RELAT_1.rng (CL R))) := by
  constructor
  · intro hcomp
    have hrest :=
      (th35 hR).1 (th34 hR).1 hcomp
    exact ⟨hrest, th26 hR ▸ hrest⟩
  · intro hcomp
    have hrest :=
      (th35 hR).2 (th34 hR).2 hcomp
    exact ⟨th26 hR ▸ hrest, hrest⟩

/-- `SYSREL:37` -/
theorem th37 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    (RELAT_1.comp R (R \ RELAT_1.id (RELAT_1.dom R)) =
        (∅ : TarskiSet.{u}) →
      RELAT_1.comp (RELAT_1.id (RELAT_1.dom (CL R)))
          (R \ RELAT_1.id (RELAT_1.dom (CL R))) =
        (∅ : TarskiSet.{u})) ∧
    (RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R)) R =
        (∅ : TarskiSet.{u}) →
      RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom (CL R)))
          (RELAT_1.id (RELAT_1.dom (CL R))) =
        (∅ : TarskiSet.{u})) := by
  constructor
  · intro hcomp
    have hid : RELAT_1.id (RELAT_1.dom (CL R)) ⊆ R := (th34 hR).1
    have hdiff :
        R \ RELAT_1.id (RELAT_1.dom R) =
          R \ RELAT_1.id (RELAT_1.dom (CL R)) := by
      have h1 : R \ RELAT_1.id (RELAT_1.dom R) = R \ CL R :=
        (XBOOLE_1.th47 (X := R) (Y := RELAT_1.id (RELAT_1.dom R))).symm
      have h2 : R \ CL R = R \ RELAT_1.id (RELAT_1.dom (CL R)) :=
        congrArg (fun P => R \ P) (th28 hR)
      exact h1.trans h2
    have hsub :
        RELAT_1.comp (RELAT_1.id (RELAT_1.dom (CL R)))
            (R \ RELAT_1.id (RELAT_1.dom (CL R))) ⊆
          RELAT_1.comp R (R \ RELAT_1.id (RELAT_1.dom R)) := by
      rw [← hdiff]; exact RELAT_1.th30 hid
    have hempty :
        RELAT_1.comp (RELAT_1.id (RELAT_1.dom (CL R)))
            (R \ RELAT_1.id (RELAT_1.dom (CL R))) ⊆
          (∅ : TarskiSet.{u}) := by
      rw [← hcomp]; exact hsub
    exact XBOOLE_1.th3 hempty
  · intro hcomp
    have hid : RELAT_1.id (RELAT_1.dom (CL R)) ⊆ R := (th34 hR).1
    have hdiff :
        R \ RELAT_1.id (RELAT_1.dom R) =
          R \ RELAT_1.id (RELAT_1.dom (CL R)) := by
      have h1 : R \ RELAT_1.id (RELAT_1.dom R) = R \ CL R :=
        (XBOOLE_1.th47 (X := R) (Y := RELAT_1.id (RELAT_1.dom R))).symm
      have h2 : R \ CL R = R \ RELAT_1.id (RELAT_1.dom (CL R)) :=
        congrArg (fun P => R \ P) (th28 hR)
      exact h1.trans h2
    have hsub :
        RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom (CL R)))
            (RELAT_1.id (RELAT_1.dom (CL R))) ⊆
          RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R)) R := by
      rw [← hdiff]; exact RELAT_1.th29 hid
    have hempty :
        RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom (CL R)))
            (RELAT_1.id (RELAT_1.dom (CL R))) ⊆
          (∅ : TarskiSet.{u}) := by
      rw [← hcomp]; exact hsub
    exact XBOOLE_1.th3 hempty

/-- `SYSREL:38` (`Th38`) -/
theorem th38 {R S : TarskiSet.{u}} :
    (RELAT_1.comp S R = S →
      RELAT_1.comp R (R \ RELAT_1.id (RELAT_1.dom R)) =
        (∅ : TarskiSet.{u}) →
      RELAT_1.comp S (R \ RELAT_1.id (RELAT_1.dom R)) =
        (∅ : TarskiSet.{u})) ∧
    (RELAT_1.comp R S = S →
      RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R)) R =
        (∅ : TarskiSet.{u}) →
      RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R)) S =
        (∅ : TarskiSet.{u})) := by
  constructor
  · intro hSR hcomp
    calc
      RELAT_1.comp S (R \ RELAT_1.id (RELAT_1.dom R))
          = RELAT_1.comp (RELAT_1.comp S R)
              (R \ RELAT_1.id (RELAT_1.dom R)) := by rw [hSR]
      _ = RELAT_1.comp S
            (RELAT_1.comp R (R \ RELAT_1.id (RELAT_1.dom R))) :=
            RELAT_1.th36
      _ = RELAT_1.comp S (∅ : TarskiSet.{u}) := by rw [hcomp]
      _ = (∅ : TarskiSet.{u}) := RELAT_1.th39.2
  · intro hRS hcomp
    calc
      RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R)) S
          = RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R))
              (RELAT_1.comp R S) := by rw [hRS]
      _ = RELAT_1.comp
            (RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R)) R) S :=
            (RELAT_1.th36).symm
      _ = RELAT_1.comp (∅ : TarskiSet.{u}) S := by rw [hcomp]
      _ = (∅ : TarskiSet.{u}) := RELAT_1.th39.1

/-- `SYSREL:39` (`Th39`) -/
theorem th39 {R S : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hS : RELAT_1.isRelation S) :
    (RELAT_1.comp S R = S →
      RELAT_1.comp R (R \ RELAT_1.id (RELAT_1.dom R)) =
        (∅ : TarskiSet.{u}) →
      CL S ⊆ CL R) ∧
    (RELAT_1.comp R S = S →
      RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R)) R =
        (∅ : TarskiSet.{u}) →
      CL S ⊆ CL R) := by
  constructor
  · intro hSR hcomp
    have hScomp := (th38 (R := R) (S := S)).1 hSR hcomp
    exact RELAT_1.rel_subset (CL_isRelation hS) fun x y hp => by
      have ⟨hpS, hid⟩ :=
        (XBOOLE_0.def4 S (RELAT_1.id (RELAT_1.dom S)) _).mp hp
      obtain ⟨z, hzS, hzR⟩ :=
        (RELAT_1.def8 S R x y).mp (hSR.symm ▸ hpS)
      have heq : z = y := by
        by_cases hzy : z = y
        · exact hzy
        · have hnot :
              TARSKI.pair z y ∉ RELAT_1.id (RELAT_1.dom R) :=
            fun hid' => hzy ((RELAT_1.def10 _ z y).mp hid').2
          have hdiff :
              TARSKI.pair z y ∈ R \ RELAT_1.id (RELAT_1.dom R) :=
            (XBOOLE_0.def5 _ _ _).mpr ⟨hzR, hnot⟩
          exact False.elim ((XBOOLE_0.empty_iff _).mp
            (hScomp ▸ (RELAT_1.def8 S
              (R \ RELAT_1.id (RELAT_1.dom R)) x y).mpr
              ⟨z, hzS, hdiff⟩))
      have ⟨_, heqxy⟩ := (RELAT_1.def10 (RELAT_1.dom S) x y).mp hid
      have hzx : z = x := heq.trans heqxy.symm
      have hxdom : x ∈ RELAT_1.dom R := hzx ▸ RELAT_1.pair_mem_dom hzR
      have hidR : TARSKI.pair x y ∈ RELAT_1.id (RELAT_1.dom R) :=
        (RELAT_1.def10 _ x y).mpr ⟨hxdom, heqxy⟩
      have hpR : TARSKI.pair x y ∈ R := hzx ▸ hzR
      exact (XBOOLE_0.def4 R (RELAT_1.id (RELAT_1.dom R)) _).mpr
        ⟨hpR, hidR⟩
  · intro hRS hcomp
    have hScomp := (th38 (R := R) (S := S)).2 hRS hcomp
    exact RELAT_1.rel_subset (CL_isRelation hS) fun x y hp => by
      have ⟨hpS, hid⟩ :=
        (XBOOLE_0.def4 S (RELAT_1.id (RELAT_1.dom S)) _).mp hp
      have ⟨_, heqxy⟩ := (RELAT_1.def10 (RELAT_1.dom S) x y).mp hid
      obtain ⟨z, hzR, hzS⟩ :=
        (RELAT_1.def8 R S x y).mp (hRS.symm ▸ hpS)
      have hxdom : x ∈ RELAT_1.dom R := RELAT_1.pair_mem_dom hzR
      have hidR : TARSKI.pair x y ∈ RELAT_1.id (RELAT_1.dom R) :=
        (RELAT_1.def10 _ x y).mpr ⟨hxdom, heqxy⟩
      have heq : z = x := by
        by_cases hzx : z = x
        · exact hzx
        · have hnot :
              TARSKI.pair x z ∉ RELAT_1.id (RELAT_1.dom R) :=
            fun hid' => hzx ((RELAT_1.def10 _ x z).mp hid').2.symm
          have hdiff :
              TARSKI.pair x z ∈ R \ RELAT_1.id (RELAT_1.dom R) :=
            (XBOOLE_0.def5 _ _ _).mpr ⟨hzR, hnot⟩
          exact False.elim ((XBOOLE_0.empty_iff _).mp
            (hScomp ▸ (RELAT_1.def8
              (R \ RELAT_1.id (RELAT_1.dom R)) S x y).mpr
              ⟨z, hdiff, hzS⟩))
      have hpR : TARSKI.pair x y ∈ R := by
        have hxx : TARSKI.pair x x ∈ R := heq ▸ hzR
        exact (show y = x from heqxy.symm) ▸ hxx
      exact (XBOOLE_0.def4 R (RELAT_1.id (RELAT_1.dom R)) _).mpr
        ⟨hpR, hidR⟩

/-- `SYSREL:40` -/
theorem th40 {R S : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hS : RELAT_1.isRelation S) :
    (RELAT_1.comp S R = S →
      RELAT_1.comp R (R \ RELAT_1.id (RELAT_1.dom R)) =
        (∅ : TarskiSet.{u}) →
      RELAT_1.comp R S = R →
      RELAT_1.comp S (S \ RELAT_1.id (RELAT_1.dom S)) =
        (∅ : TarskiSet.{u}) →
      CL S = CL R) ∧
    (RELAT_1.comp R S = S →
      RELAT_1.comp (R \ RELAT_1.id (RELAT_1.dom R)) R =
        (∅ : TarskiSet.{u}) →
      RELAT_1.comp S R = R →
      RELAT_1.comp (S \ RELAT_1.id (RELAT_1.dom S)) S =
        (∅ : TarskiSet.{u}) →
      CL S = CL R) := by
  constructor
  · intro hSR hRcomp hRS hScomp
    have h1 := (th39 hR hS).1 hSR hRcomp
    have h2 := (th39 hS hR).1 hRS hScomp
    exact (XBOOLE_0.def10).mpr ⟨h1, h2⟩
  · intro hRS hRcomp hSR hScomp
    have h1 := (th39 hR hS).2 hRS hRcomp
    have h2 := (th39 hS hR).2 hSR hScomp
    exact (XBOOLE_0.def10).mpr ⟨h1, h2⟩

end SYSREL
