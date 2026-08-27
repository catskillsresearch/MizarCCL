import MizarCCL.FUNCT_1
import MizarCCL.ENUMSET1
import MizarCCL.XREGULAR

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/mcart_1.miz`.
Authors: Andrzej Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Tuples, Projections and Cartesian Products

1–1 Lean rendering of Mizar article `MCART_1`
(`vendor/mml/mcart_1.miz`). Import is `FUNCT_1`, `ENUMSET1`, and
`XREGULAR`.
-/

universe u

open TarskiSet TARSKI

namespace MCART_1

private theorem not_mem_self (x : TarskiSet.{u}) : x ∉ x :=
  fun hx =>
    let ⟨Y, hY, hdisj⟩ := TARSKI.th2 ((singleton_iff x x).mpr rfl)
    let heq : Y = x := (singleton_iff x Y).mp hY
    hdisj ⟨x, (singleton_iff x x).mpr rfl,
      Eq.subst (motive := fun s => x ∈ s) heq.symm hx⟩

private theorem not_two_cycle {x y : TarskiSet.{u}} : ¬ (x ∈ y ∧ y ∈ x) :=
  fun ⟨hxy, hyx⟩ =>
    let ⟨Z, hZ, hdisj⟩ :=
      TARSKI.th2 (X := upair x y) ((upair_iff x y x).mpr (Or.inl rfl))
    Or.elim ((upair_iff x y Z).mp hZ)
      (fun hZx =>
        hdisj ⟨y, (upair_iff x y y).mpr (Or.inr rfl),
          Eq.subst (motive := fun s => y ∈ s) hZx.symm hyx⟩)
      (fun hZy =>
        hdisj ⟨x, (upair_iff x y x).mpr (Or.inl rfl),
          Eq.subst (motive := fun s => x ∈ s) hZy.symm hxy⟩)

private theorem nonempty_of_ne {X : TarskiSet.{u}}
    (h : X ≠ (∅ : TarskiSet.{u})) : ¬ XBOOLE_0.isEmpty X :=
  fun hempty => h (XBOOLE_0.empty_eq hempty)

/-- `MCART_1:7` (`Th7`). `MCART_1:1`–`6` are canceled. -/
theorem th7 (x y : TarskiSet.{u}) :
    XTUPLE_0.fst (TARSKI.pair x y) = x ∧
      XTUPLE_0.snd (TARSKI.pair x y) = y :=
  ⟨XTUPLE_0.fst_pair x y, XTUPLE_0.snd_pair x y⟩

/-- `MCART_1:8` (`Th8`) -/
theorem th8 {p : TarskiSet.{u}} (hp : XTUPLE_0.isPair p) :
    TARSKI.pair (XTUPLE_0.fst p) (XTUPLE_0.snd p) = p :=
  XTUPLE_0.pair_eta hp

/-- Unlabeled `MCART_1` (`L52`). -/
theorem th9 {X : TarskiSet.{u}} (hX : X ≠ (∅ : TarskiSet.{u})) :
    ∃ v, v ∈ X ∧
      ¬ ∃ x y, (x ∈ X ∨ y ∈ X) ∧ v = TARSKI.pair x y := by
  obtain ⟨v, hvX, hall⟩ := XREGULAR.th2 (nonempty_of_ne hX)
  refine ⟨v, hvX, ?_⟩
  intro ⟨x, y, hxy, heq⟩
  have hup : TARSKI.upair x y ∈ v :=
    Eq.subst (motive := fun s => TARSKI.upair x y ∈ s) heq.symm
      ((TARSKI.def2 (TARSKI.upair x y) (TARSKI.singleton x)
        (TARSKI.upair x y)).mpr (Or.inl rfl))
  have hmeet : XBOOLE_0.meets (TARSKI.upair x y) X :=
    (XBOOLE_0.th3 (TARSKI.upair x y) X).mpr
      (Or.elim hxy
        (fun hx => ⟨x, (TARSKI.upair_iff x y x).mpr (Or.inl rfl), hx⟩)
        (fun hy => ⟨y, (TARSKI.upair_iff x y y).mpr (Or.inr rfl), hy⟩))
  exact hmeet (hall (TARSKI.upair x y) hup)

/-- `MCART_1:10` (`Th10`) -/
theorem th10 {z X Y : TarskiSet.{u}} (hz : z ∈ ZFMISC_1.product X Y) :
    XTUPLE_0.fst z ∈ X ∧ XTUPLE_0.snd z ∈ Y := by
  obtain ⟨x, y, hx, hy, heq⟩ := (ZFMISC_1.def2 X Y z).mp hz
  exact ⟨
    Eq.subst (motive := fun s => s ∈ X) (XTUPLE_0.def1 heq).symm hx,
    Eq.subst (motive := fun s => s ∈ Y) (XTUPLE_0.def2 heq).symm hy⟩

/-- Unlabeled `MCART_1` (`L83`). -/
theorem th11 {z X Y : TarskiSet.{u}} (hp : XTUPLE_0.isPair z)
    (h1 : XTUPLE_0.fst z ∈ X) (h2 : XTUPLE_0.snd z ∈ Y) :
    z ∈ ZFMISC_1.product X Y :=
  (ZFMISC_1.def2 X Y z).mpr
    ⟨XTUPLE_0.fst z, XTUPLE_0.snd z, h1, h2, (th8 hp).symm⟩

/-- Unlabeled `MCART_1` (`L91`). -/
theorem th12 {z x Y : TarskiSet.{u}}
    (hz : z ∈ ZFMISC_1.product (TARSKI.singleton x) Y) :
    XTUPLE_0.fst z = x ∧ XTUPLE_0.snd z ∈ Y :=
  let ⟨h1, h2⟩ := th10 hz
  ⟨(singleton_iff x (XTUPLE_0.fst z)).mp h1, h2⟩

/-- Unlabeled `MCART_1` (`L100`). -/
theorem th13 {z X y : TarskiSet.{u}}
    (hz : z ∈ ZFMISC_1.product X (TARSKI.singleton y)) :
    XTUPLE_0.fst z ∈ X ∧ XTUPLE_0.snd z = y :=
  let ⟨h1, h2⟩ := th10 hz
  ⟨h1, (singleton_iff y (XTUPLE_0.snd z)).mp h2⟩

/-- Unlabeled `MCART_1` (`L109`). -/
theorem th14 {z x y : TarskiSet.{u}}
    (hz : z ∈ ZFMISC_1.product (TARSKI.singleton x) (TARSKI.singleton y)) :
    XTUPLE_0.fst z = x ∧ XTUPLE_0.snd z = y :=
  let ⟨h1, h2⟩ := th10 hz
  ⟨(singleton_iff x (XTUPLE_0.fst z)).mp h1,
    (singleton_iff y (XTUPLE_0.snd z)).mp h2⟩

/-- Unlabeled `MCART_1` (`L117`). -/
theorem th15 {z x1 x2 Y : TarskiSet.{u}}
    (hz : z ∈ ZFMISC_1.product (TARSKI.upair x1 x2) Y) :
    (XTUPLE_0.fst z = x1 ∨ XTUPLE_0.fst z = x2) ∧ XTUPLE_0.snd z ∈ Y :=
  let ⟨h1, h2⟩ := th10 hz
  ⟨(TARSKI.upair_iff x1 x2 (XTUPLE_0.fst z)).mp h1, h2⟩

/-- Unlabeled `MCART_1` (`L126`). -/
theorem th16 {z X y1 y2 : TarskiSet.{u}}
    (hz : z ∈ ZFMISC_1.product X (TARSKI.upair y1 y2)) :
    XTUPLE_0.fst z ∈ X ∧
      (XTUPLE_0.snd z = y1 ∨ XTUPLE_0.snd z = y2) :=
  let ⟨h1, h2⟩ := th10 hz
  ⟨h1, (TARSKI.upair_iff y1 y2 (XTUPLE_0.snd z)).mp h2⟩

/-- Unlabeled `MCART_1` (`L135`). -/
theorem th17 {z x1 x2 y : TarskiSet.{u}}
    (hz : z ∈ ZFMISC_1.product (TARSKI.upair x1 x2) (TARSKI.singleton y)) :
    (XTUPLE_0.fst z = x1 ∨ XTUPLE_0.fst z = x2) ∧ XTUPLE_0.snd z = y :=
  let ⟨h1, h2⟩ := th10 hz
  ⟨(TARSKI.upair_iff x1 x2 (XTUPLE_0.fst z)).mp h1,
    (singleton_iff y (XTUPLE_0.snd z)).mp h2⟩

/-- Unlabeled `MCART_1` (`L143`). -/
theorem th18 {z x y1 y2 : TarskiSet.{u}}
    (hz : z ∈ ZFMISC_1.product (TARSKI.singleton x) (TARSKI.upair y1 y2)) :
    XTUPLE_0.fst z = x ∧
      (XTUPLE_0.snd z = y1 ∨ XTUPLE_0.snd z = y2) :=
  let ⟨h1, h2⟩ := th10 hz
  ⟨(singleton_iff x (XTUPLE_0.fst z)).mp h1,
    (TARSKI.upair_iff y1 y2 (XTUPLE_0.snd z)).mp h2⟩

/-- Unlabeled `MCART_1` (`L151`). -/
theorem th19 {z x1 x2 y1 y2 : TarskiSet.{u}}
    (hz : z ∈ ZFMISC_1.product (TARSKI.upair x1 x2) (TARSKI.upair y1 y2)) :
    (XTUPLE_0.fst z = x1 ∨ XTUPLE_0.fst z = x2) ∧
      (XTUPLE_0.snd z = y1 ∨ XTUPLE_0.snd z = y2) :=
  let ⟨h1, h2⟩ := th10 hz
  ⟨(TARSKI.upair_iff x1 x2 (XTUPLE_0.fst z)).mp h1,
    (TARSKI.upair_iff y1 y2 (XTUPLE_0.snd z)).mp h2⟩

/-- `MCART_1:20` (`Th20`) -/
theorem th20 {x : TarskiSet.{u}} (hp : XTUPLE_0.isPair x) :
    x ≠ XTUPLE_0.fst x ∧ x ≠ XTUPLE_0.snd x := by
  obtain ⟨y, z, heq⟩ := hp
  constructor
  · intro hxf
    have hyx : y = x :=
      (XTUPLE_0.def1 heq).symm.trans hxf.symm
    have hsing : TARSKI.singleton y ∈ TARSKI.pair y z :=
      (TARSKI.def2 (TARSKI.upair y z) (TARSKI.singleton y)
        (TARSKI.singleton y)).mpr (Or.inr rfl)
    have hsingx : TARSKI.singleton y ∈ x :=
      Eq.subst (motive := fun s => TARSKI.singleton y ∈ s) heq.symm hsing
    have hyin : y ∈ TARSKI.singleton y := (singleton_iff y y).mpr rfl
    have hsingy : TARSKI.singleton y ∈ y :=
      Eq.subst (motive := fun s => TARSKI.singleton y ∈ s) hyx.symm hsingx
    exact not_two_cycle ⟨hyin, hsingy⟩
  · intro hxs
    have hzx : z = x :=
      (XTUPLE_0.def2 heq).symm.trans hxs.symm
    have hup : TARSKI.upair y z ∈ TARSKI.pair y z :=
      (TARSKI.def2 (TARSKI.upair y z) (TARSKI.singleton y)
        (TARSKI.upair y z)).mpr (Or.inl rfl)
    have hupx : TARSKI.upair y z ∈ x :=
      Eq.subst (motive := fun s => TARSKI.upair y z ∈ s) heq.symm hup
    have hzin : z ∈ TARSKI.upair y z :=
      (TARSKI.upair_iff y z z).mpr (Or.inr rfl)
    have hupz : TARSKI.upair y z ∈ z :=
      Eq.subst (motive := fun s => TARSKI.upair y z ∈ s) hzx.symm hupx
    exact not_two_cycle ⟨hzin, hupz⟩

/-- `MCART_1:21` (`Th21`) -/
theorem th21 {x R : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hx : x ∈ R) :
    x = TARSKI.pair (XTUPLE_0.fst x) (XTUPLE_0.snd x) := by
  obtain ⟨x1, x2, heq⟩ := hR x hx
  exact (th8 ⟨x1, x2, heq⟩).symm

/-- Unlabeled `MCART_1` (`L193`). -/
theorem th22 {X Y x : TarskiSet.{u}} (_hX : X ≠ (∅ : TarskiSet.{u}))
    (_hY : Y ≠ (∅ : TarskiSet.{u})) (hx : x ∈ ZFMISC_1.product X Y) :
    x = TARSKI.pair (XTUPLE_0.fst x) (XTUPLE_0.snd x) :=
  th21 (RELAT_1.product_isRelation X Y) hx

/-- `MCART_1:lm 1` -/
theorem lm1 {X1 X2 x : TarskiSet.{u}}
    (_h1 : X1 ≠ (∅ : TarskiSet.{u})) (_h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product X1 X2) :
    ∃ xx1 xx2, xx1 ∈ X1 ∧ xx2 ∈ X2 ∧ x = TARSKI.pair xx1 xx2 :=
  (ZFMISC_1.def2 X1 X2 x).mp hx

/-- `MCART_1:23` (`Th23`) -/
theorem th23 (x1 x2 y1 y2 : TarskiSet.{u}) :
    ZFMISC_1.product (TARSKI.upair x1 x2) (TARSKI.upair y1 y2) =
      ENUMSET1.enumset4 (TARSKI.pair x1 y1) (TARSKI.pair x1 y2)
        (TARSKI.pair x2 y1) (TARSKI.pair x2 y2) := by
  have h1 : ZFMISC_1.product (TARSKI.upair x1 x2) (TARSKI.upair y1 y2) =
      ZFMISC_1.product (TARSKI.singleton x1) (TARSKI.upair y1 y2) ∪
        ZFMISC_1.product (TARSKI.singleton x2) (TARSKI.upair y1 y2) :=
    (ZFMISC_1.th109 (x := x1) (y := x2) (X := TARSKI.upair y1 y2)).1
  have h2 : ZFMISC_1.product (TARSKI.singleton x1) (TARSKI.upair y1 y2) =
      TARSKI.upair (TARSKI.pair x1 y1) (TARSKI.pair x1 y2) :=
    (ZFMISC_1.th30 (x := x1) (y := y1) (z := y2)).1
  have h3 : ZFMISC_1.product (TARSKI.singleton x2) (TARSKI.upair y1 y2) =
      TARSKI.upair (TARSKI.pair x2 y1) (TARSKI.pair x2 y2) :=
    (ZFMISC_1.th30 (x := x2) (y := y1) (z := y2)).1
  have h4 :
      TARSKI.upair (TARSKI.pair x1 y1) (TARSKI.pair x1 y2) ∪
        TARSKI.upair (TARSKI.pair x2 y1) (TARSKI.pair x2 y2) =
      ENUMSET1.enumset4 (TARSKI.pair x1 y1) (TARSKI.pair x1 y2)
        (TARSKI.pair x2 y1) (TARSKI.pair x2 y2) :=
    (ENUMSET1.th5 (x1 := TARSKI.pair x1 y1) (x2 := TARSKI.pair x1 y2)
      (x3 := TARSKI.pair x2 y1) (x4 := TARSKI.pair x2 y2)).symm
  have h23 :
      ZFMISC_1.product (TARSKI.singleton x1) (TARSKI.upair y1 y2) ∪
        ZFMISC_1.product (TARSKI.singleton x2) (TARSKI.upair y1 y2) =
      TARSKI.upair (TARSKI.pair x1 y1) (TARSKI.pair x1 y2) ∪
        TARSKI.upair (TARSKI.pair x2 y1) (TARSKI.pair x2 y2) :=
    Eq.subst (motive := fun s =>
        s ∪ ZFMISC_1.product (TARSKI.singleton x2) (TARSKI.upair y1 y2) =
          TARSKI.upair (TARSKI.pair x1 y1) (TARSKI.pair x1 y2) ∪
            TARSKI.upair (TARSKI.pair x2 y1) (TARSKI.pair x2 y2))
      h2.symm
      (Eq.subst (motive := fun s =>
          TARSKI.upair (TARSKI.pair x1 y1) (TARSKI.pair x1 y2) ∪ s =
            TARSKI.upair (TARSKI.pair x1 y1) (TARSKI.pair x1 y2) ∪
              TARSKI.upair (TARSKI.pair x2 y1) (TARSKI.pair x2 y2))
        h3.symm rfl)
  exact h1.trans (h23.trans h4)

/-- `MCART_1:24` (`Th24`) -/
theorem th24 {X Y x : TarskiSet.{u}} (hX : X ≠ (∅ : TarskiSet.{u}))
    (hY : Y ≠ (∅ : TarskiSet.{u})) (hx : x ∈ ZFMISC_1.product X Y) :
    x ≠ XTUPLE_0.fst x ∧ x ≠ XTUPLE_0.snd x :=
  th20 ⟨XTUPLE_0.fst x, XTUPLE_0.snd x, th22 hX hY hx⟩

/-- `MCART_1:26` (`Th26`). `MCART_1:25` is canceled. -/
theorem th26 {X : TarskiSet.{u}} (hX : X ≠ (∅ : TarskiSet.{u})) :
    ∃ v, v ∈ X ∧
      ¬ ∃ x y z, (x ∈ X ∨ y ∈ X) ∧ v = XTUPLE_0.triple x y z := by
  obtain ⟨v, hvX, hall⟩ := XREGULAR.th4 (nonempty_of_ne hX)
  refine ⟨v, hvX, ?_⟩
  intro ⟨x, y, z, hxy, heq⟩
  let Y1 := TARSKI.upair x y
  let Y2 := TARSKI.pair x y
  let Y3 := TARSKI.upair Y2 z
  have hY2 : Y2 = TARSKI.upair Y1 (TARSKI.singleton x) := rfl
  have hY3v : Y3 ∈ v :=
    Eq.subst (motive := fun s => Y3 ∈ s) heq.symm
      ((TARSKI.def2 (TARSKI.upair (TARSKI.pair x y) z)
        (TARSKI.singleton (TARSKI.pair x y)) Y3).mpr (Or.inl rfl))
  have hY1Y2 : Y1 ∈ Y2 :=
    (TARSKI.def2 Y1 (TARSKI.singleton x) Y1).mpr (Or.inl rfl)
  have hY2Y3 : Y2 ∈ Y3 :=
    (TARSKI.upair_iff Y2 z Y2).mpr (Or.inl rfl)
  have hmeet : XBOOLE_0.meets Y1 X :=
    (XBOOLE_0.th3 Y1 X).mpr
      (Or.elim hxy
        (fun hx => ⟨x, (TARSKI.upair_iff x y x).mpr (Or.inl rfl), hx⟩)
        (fun hy => ⟨y, (TARSKI.upair_iff x y y).mpr (Or.inr rfl), hy⟩))
  exact hmeet (hall Y1 Y2 Y3 hY1Y2 hY2Y3 hY3v)

/-- `MCART_1:30` (`Th30`). `MCART_1:27`–`29` are canceled. -/
theorem th30 {X : TarskiSet.{u}} (hX : X ≠ (∅ : TarskiSet.{u})) :
    ∃ v, v ∈ X ∧
      ¬ ∃ x1 x2 x3 x4, (x1 ∈ X ∨ x2 ∈ X) ∧
        v = XTUPLE_0.quadruple x1 x2 x3 x4 := by
  obtain ⟨v, hvX, hall⟩ := XREGULAR.th6 (nonempty_of_ne hX)
  refine ⟨v, hvX, ?_⟩
  intro ⟨x1, x2, x3, x4, hxy, heq⟩
  let Y1 := TARSKI.upair x1 x2
  let Y2 := TARSKI.pair x1 x2
  let Y3 := TARSKI.upair Y2 x3
  let Y4 := TARSKI.pair Y2 x3
  let Y5 := TARSKI.upair Y4 x4
  have hY5v : Y5 ∈ v :=
    Eq.subst (motive := fun s => Y5 ∈ s) heq.symm
      ((TARSKI.def2 (TARSKI.upair Y4 x4) (TARSKI.singleton Y4) Y5).mpr
        (Or.inl rfl))
  have hY1Y2 : Y1 ∈ Y2 :=
    (TARSKI.def2 Y1 (TARSKI.singleton x1) Y1).mpr (Or.inl rfl)
  have hY2Y3 : Y2 ∈ Y3 :=
    (TARSKI.upair_iff Y2 x3 Y2).mpr (Or.inl rfl)
  have hY3Y4 : Y3 ∈ Y4 :=
    (TARSKI.def2 Y3 (TARSKI.singleton Y2) Y3).mpr (Or.inl rfl)
  have hY4Y5 : Y4 ∈ Y5 :=
    (TARSKI.upair_iff Y4 x4 Y4).mpr (Or.inl rfl)
  have hmeet : XBOOLE_0.meets Y1 X :=
    (XBOOLE_0.th3 Y1 X).mpr
      (Or.elim hxy
        (fun hx => ⟨x1, (TARSKI.upair_iff x1 x2 x1).mpr (Or.inl rfl), hx⟩)
        (fun hx => ⟨x2, (TARSKI.upair_iff x1 x2 x2).mpr (Or.inr rfl), hx⟩))
  exact hmeet (hall Y1 Y2 Y3 Y4 Y5 hY1Y2 hY2Y3 hY3Y4 hY4Y5 hY5v)

/-- `MCART_1:31` (`Th31`) -/
theorem th31 (X1 X2 X3 : TarskiSet.{u}) :
    (X1 ≠ (∅ : TarskiSet.{u}) ∧ X2 ≠ (∅ : TarskiSet.{u}) ∧
      X3 ≠ (∅ : TarskiSet.{u})) ↔
      ZFMISC_1.product3 X1 X2 X3 ≠ (∅ : TarskiSet.{u}) := by
  have h12 : ZFMISC_1.product X1 X2 = (∅ : TarskiSet.{u}) ↔
      X1 = (∅ : TarskiSet.{u}) ∨ X2 = (∅ : TarskiSet.{u}) :=
    ZFMISC_1.th90 (X := X1) (Y := X2)
  have h3 : ZFMISC_1.product3 X1 X2 X3 = (∅ : TarskiSet.{u}) ↔
      ZFMISC_1.product X1 X2 = (∅ : TarskiSet.{u}) ∨
        X3 = (∅ : TarskiSet.{u}) :=
    ZFMISC_1.th90 (X := ZFMISC_1.product X1 X2) (Y := X3)
  constructor
  · intro ⟨h1, h2, h3ne⟩
    intro hempty
    exact Or.elim (h3.mp hempty)
      (fun h12e => Or.elim (h12.mp h12e) (fun h => h1 h) (fun h => h2 h))
      (fun h => h3ne h)
  · intro hne
    refine Classical.byContradiction fun hnot => ?_
    have h12e : X1 = (∅ : TarskiSet.{u}) ∨ X2 = (∅ : TarskiSet.{u}) ∨
        X3 = (∅ : TarskiSet.{u}) := by
      refine Or.elim (Classical.em (X1 = (∅ : TarskiSet.{u})))
        (fun h => Or.inl h) (fun hn1 =>
          Or.elim (Classical.em (X2 = (∅ : TarskiSet.{u})))
            (fun h => Or.inr (Or.inl h)) (fun hn2 =>
              Or.inr (Or.inr (Classical.byContradiction fun hn3 =>
                hnot ⟨hn1, hn2, hn3⟩))))
    have hempty : ZFMISC_1.product3 X1 X2 X3 = (∅ : TarskiSet.{u}) :=
      h3.mpr (Or.elim h12e
        (fun h1 => Or.inl (h12.mpr (Or.inl h1)))
        (fun h23 => Or.elim h23
          (fun h2 => Or.inl (h12.mpr (Or.inr h2)))
          (fun h3e => Or.inr h3e)))
    exact hne hempty

/-- `MCART_1:32` (`Th32`) -/
theorem th32 {X1 X2 X3 Y1 Y2 Y3 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (heq : ZFMISC_1.product3 X1 X2 X3 = ZFMISC_1.product3 Y1 Y2 Y3) :
    X1 = Y1 ∧ X2 = Y2 ∧ X3 = Y3 := by
  have h12 : ZFMISC_1.product X1 X2 ≠ (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := X1) (Y := X2)).mp hempty)
        (fun h => h1 h) (fun h => h2 h)
  have hprod :
      ZFMISC_1.product (ZFMISC_1.product X1 X2) X3 =
        ZFMISC_1.product (ZFMISC_1.product Y1 Y2) Y3 :=
    heq
  have ⟨hXY, h3eq⟩ :=
    ZFMISC_1.th110 (X1 := ZFMISC_1.product X1 X2) (Y1 := X3)
      (X2 := ZFMISC_1.product Y1 Y2) (Y2 := Y3) h12 h3 hprod
  have ⟨h1eq, h2eq⟩ :=
    ZFMISC_1.th110 (X1 := X1) (Y1 := X2) (X2 := Y1) (Y2 := Y2) h1 h2 hXY
  exact ⟨h1eq, h2eq, h3eq⟩

/-- Unlabeled `MCART_1` (`L319`). -/
theorem th33 {X1 X2 X3 Y1 Y2 Y3 : TarskiSet.{u}}
    (hne : ZFMISC_1.product3 X1 X2 X3 ≠ (∅ : TarskiSet.{u}))
    (heq : ZFMISC_1.product3 X1 X2 X3 = ZFMISC_1.product3 Y1 Y2 Y3) :
    X1 = Y1 ∧ X2 = Y2 ∧ X3 = Y3 :=
  let ⟨h1, h23⟩ := (th31 X1 X2 X3).mpr hne
  let ⟨h2, h3⟩ := h23
  th32 h1 h2 h3 heq

/-- Unlabeled `MCART_1` (`L331`). -/
theorem th34 {X Y : TarskiSet.{u}}
    (heq : ZFMISC_1.product3 X X X = ZFMISC_1.product3 Y Y Y) : X = Y :=
  Or.elim (Classical.em (X = (∅ : TarskiSet.{u})))
    (fun hXe => by
      have hemptyX : ZFMISC_1.product3 X X X = (∅ : TarskiSet.{u}) :=
        Classical.byContradiction fun hne =>
          ((th31 X X X).mpr hne).1 hXe
      have hemptyY : ZFMISC_1.product3 Y Y Y = (∅ : TarskiSet.{u}) :=
        heq.symm.trans hemptyX
      have hYe : Y = (∅ : TarskiSet.{u}) :=
        Classical.byContradiction fun hYne =>
          (th31 Y Y Y).mp ⟨hYne, hYne, hYne⟩ hemptyY
      exact hXe.trans hYe.symm)
    (fun hXne => (th32 hXne hXne hXne heq).1)

/-- `MCART_1:lm 2` -/
theorem lm2 {X1 X2 X3 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product3 X1 X2 X3) :
    ∃ xx1 xx2 xx3, xx1 ∈ X1 ∧ xx2 ∈ X2 ∧ xx3 ∈ X3 ∧
      x = XTUPLE_0.triple xx1 xx2 xx3 := by
  have h12 : ZFMISC_1.product X1 X2 ≠ (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := X1) (Y := X2)).mp hempty)
        (fun h => h1 h) (fun h => h2 h)
  obtain ⟨x12, xx3, hx12, hx3, heq⟩ := lm1 h12 h3 hx
  obtain ⟨xx1, xx2, hx1, hx2, heq12⟩ := lm1 h1 h2 hx12
  refine ⟨xx1, xx2, xx3, hx1, hx2, hx3, ?_⟩
  exact heq.trans (congrArg (fun s => TARSKI.pair s xx3) heq12)

/-- `MCART_1:35` (`Th35`) -/
theorem th35 (x1 x2 x3 : TarskiSet.{u}) :
    ZFMISC_1.product3 (TARSKI.singleton x1) (TARSKI.singleton x2)
      (TARSKI.singleton x3) =
      TARSKI.singleton (XTUPLE_0.triple x1 x2 x3) := by
  have h1 : ZFMISC_1.product (TARSKI.singleton x1) (TARSKI.singleton x2) =
      TARSKI.singleton (TARSKI.pair x1 x2) :=
    ZFMISC_1.th29 (x := x1) (y := x2)
  have h2 :
      ZFMISC_1.product (ZFMISC_1.product (TARSKI.singleton x1)
        (TARSKI.singleton x2)) (TARSKI.singleton x3) =
      ZFMISC_1.product (TARSKI.singleton (TARSKI.pair x1 x2))
        (TARSKI.singleton x3) :=
    congrArg (fun s => ZFMISC_1.product s (TARSKI.singleton x3)) h1
  exact h2.trans (ZFMISC_1.th29 (x := TARSKI.pair x1 x2) (y := x3))

/-- Unlabeled `MCART_1` (`L365`). -/
theorem th36 (x1 y1 x2 x3 : TarskiSet.{u}) :
    ZFMISC_1.product3 (TARSKI.upair x1 y1) (TARSKI.singleton x2)
      (TARSKI.singleton x3) =
      TARSKI.upair (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple y1 x2 x3) := by
  have h1 : ZFMISC_1.product (TARSKI.upair x1 y1) (TARSKI.singleton x2) =
      TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair y1 x2) :=
    (ZFMISC_1.th30 (x := x1) (y := y1) (z := x2)).2
  have h2 :
      ZFMISC_1.product (ZFMISC_1.product (TARSKI.upair x1 y1)
        (TARSKI.singleton x2)) (TARSKI.singleton x3) =
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair y1 x2))
        (TARSKI.singleton x3) :=
    congrArg (fun s => ZFMISC_1.product s (TARSKI.singleton x3)) h1
  exact h2.trans (ZFMISC_1.th30 (x := TARSKI.pair x1 x2)
    (y := TARSKI.pair y1 x2) (z := x3)).2

/-- Unlabeled `MCART_1` (`L373`). -/
theorem th37 (x1 x2 y2 x3 : TarskiSet.{u}) :
    ZFMISC_1.product3 (TARSKI.singleton x1) (TARSKI.upair x2 y2)
      (TARSKI.singleton x3) =
      TARSKI.upair (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3) := by
  have h1 : ZFMISC_1.product (TARSKI.singleton x1) (TARSKI.upair x2 y2) =
      TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2) :=
    (ZFMISC_1.th30 (x := x1) (y := x2) (z := y2)).1
  have h2 :
      ZFMISC_1.product (ZFMISC_1.product (TARSKI.singleton x1)
        (TARSKI.upair x2 y2)) (TARSKI.singleton x3) =
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2))
        (TARSKI.singleton x3) :=
    congrArg (fun s => ZFMISC_1.product s (TARSKI.singleton x3)) h1
  exact h2.trans (ZFMISC_1.th30 (x := TARSKI.pair x1 x2)
    (y := TARSKI.pair x1 y2) (z := x3)).2

/-- Unlabeled `MCART_1` (`L381`). -/
theorem th38 (x1 x2 x3 y3 : TarskiSet.{u}) :
    ZFMISC_1.product3 (TARSKI.singleton x1) (TARSKI.singleton x2)
      (TARSKI.upair x3 y3) =
      TARSKI.upair (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 x2 y3) := by
  have h1 : ZFMISC_1.product (TARSKI.singleton x1) (TARSKI.singleton x2) =
      TARSKI.singleton (TARSKI.pair x1 x2) :=
    ZFMISC_1.th29 (x := x1) (y := x2)
  have h2 :
      ZFMISC_1.product (ZFMISC_1.product (TARSKI.singleton x1)
        (TARSKI.singleton x2)) (TARSKI.upair x3 y3) =
      ZFMISC_1.product (TARSKI.singleton (TARSKI.pair x1 x2))
        (TARSKI.upair x3 y3) :=
    congrArg (fun s => ZFMISC_1.product s (TARSKI.upair x3 y3)) h1
  exact h2.trans (ZFMISC_1.th30 (x := TARSKI.pair x1 x2)
    (y := x3) (z := y3)).1

/-- Unlabeled `MCART_1` (`L389`). -/
theorem th39 (x1 y1 x2 y2 x3 : TarskiSet.{u}) :
    ZFMISC_1.product3 (TARSKI.upair x1 y1) (TARSKI.upair x2 y2)
      (TARSKI.singleton x3) =
      ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple y1 x2 x3)
        (XTUPLE_0.triple x1 y2 x3) (XTUPLE_0.triple y1 y2 x3) := by
  have h0 : ZFMISC_1.product (TARSKI.upair x1 y1) (TARSKI.upair x2 y2) =
      ENUMSET1.enumset4 (TARSKI.pair x1 x2) (TARSKI.pair x1 y2)
        (TARSKI.pair y1 x2) (TARSKI.pair y1 y2) :=
    th23 x1 y1 x2 y2
  have h1 :
      ENUMSET1.enumset4 (TARSKI.pair x1 x2) (TARSKI.pair x1 y2)
        (TARSKI.pair y1 x2) (TARSKI.pair y1 y2) =
      TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2) ∪
        TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2) :=
    ENUMSET1.th5 (x1 := TARSKI.pair x1 x2) (x2 := TARSKI.pair x1 y2)
      (x3 := TARSKI.pair y1 x2) (x4 := TARSKI.pair y1 y2)
  have h2 :
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2) ∪
        TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.singleton x3) =
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2))
        (TARSKI.singleton x3) ∪
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.singleton x3) :=
    (ZFMISC_1.th97 (X := TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2))
      (Y := TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
      (Z := TARSKI.singleton x3)).1
  have h3 :
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2))
        (TARSKI.singleton x3) =
      TARSKI.upair (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3) :=
    (ZFMISC_1.th30 (x := TARSKI.pair x1 x2) (y := TARSKI.pair x1 y2)
      (z := x3)).2
  have h4 :
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.singleton x3) =
      TARSKI.upair (XTUPLE_0.triple y1 x2 x3) (XTUPLE_0.triple y1 y2 x3) :=
    (ZFMISC_1.th30 (x := TARSKI.pair y1 x2) (y := TARSKI.pair y1 y2)
      (z := x3)).2
  have h5 :
      TARSKI.upair (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3) ∪
        TARSKI.upair (XTUPLE_0.triple y1 x2 x3) (XTUPLE_0.triple y1 y2 x3) =
      ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3)
        (XTUPLE_0.triple y1 x2 x3) (XTUPLE_0.triple y1 y2 x3) :=
    (ENUMSET1.th5 (x1 := XTUPLE_0.triple x1 x2 x3)
      (x2 := XTUPLE_0.triple x1 y2 x3)
      (x3 := XTUPLE_0.triple y1 x2 x3)
      (x4 := XTUPLE_0.triple y1 y2 x3)).symm
  have h6 :
      ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3)
        (XTUPLE_0.triple y1 x2 x3) (XTUPLE_0.triple y1 y2 x3) =
      ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple y1 x2 x3)
        (XTUPLE_0.triple x1 y2 x3) (XTUPLE_0.triple y1 y2 x3) :=
    ENUMSET1.th62 (x1 := XTUPLE_0.triple x1 x2 x3)
      (x2 := XTUPLE_0.triple x1 y2 x3)
      (x3 := XTUPLE_0.triple y1 x2 x3)
      (x4 := XTUPLE_0.triple y1 y2 x3)
  have hprod :
      ZFMISC_1.product3 (TARSKI.upair x1 y1) (TARSKI.upair x2 y2)
        (TARSKI.singleton x3) =
      ZFMISC_1.product (ENUMSET1.enumset4 (TARSKI.pair x1 x2)
        (TARSKI.pair x1 y2) (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.singleton x3) :=
    congrArg (fun s => ZFMISC_1.product s (TARSKI.singleton x3)) h0
  have hunion :
      ZFMISC_1.product (ENUMSET1.enumset4 (TARSKI.pair x1 x2)
        (TARSKI.pair x1 y2) (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.singleton x3) =
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2) ∪
        TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.singleton x3) :=
    congrArg (fun s => ZFMISC_1.product s (TARSKI.singleton x3)) h1
  have h34 :
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2))
        (TARSKI.singleton x3) ∪
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.singleton x3) =
      TARSKI.upair (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3) ∪
        TARSKI.upair (XTUPLE_0.triple y1 x2 x3) (XTUPLE_0.triple y1 y2 x3) :=
    Eq.subst (motive := fun s =>
        s ∪ ZFMISC_1.product (TARSKI.upair (TARSKI.pair y1 x2)
          (TARSKI.pair y1 y2)) (TARSKI.singleton x3) =
        TARSKI.upair (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3) ∪
          TARSKI.upair (XTUPLE_0.triple y1 x2 x3) (XTUPLE_0.triple y1 y2 x3))
      h3.symm
      (Eq.subst (motive := fun s =>
          TARSKI.upair (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3) ∪
            s =
          TARSKI.upair (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3) ∪
            TARSKI.upair (XTUPLE_0.triple y1 x2 x3)
              (XTUPLE_0.triple y1 y2 x3))
        h4.symm rfl)
  exact hprod.trans (hunion.trans (h2.trans (h34.trans (h5.trans h6))))

/-- Unlabeled `MCART_1` (`L406`). -/
theorem th40 (x1 y1 x2 x3 y3 : TarskiSet.{u}) :
    ZFMISC_1.product3 (TARSKI.upair x1 y1) (TARSKI.singleton x2)
      (TARSKI.upair x3 y3) =
      ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple y1 x2 x3)
        (XTUPLE_0.triple x1 x2 y3) (XTUPLE_0.triple y1 x2 y3) := by
  have h1 : ZFMISC_1.product (TARSKI.upair x1 y1) (TARSKI.singleton x2) =
      TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair y1 x2) :=
    (ZFMISC_1.th30 (x := x1) (y := y1) (z := x2)).2
  have h2 :
      ZFMISC_1.product (ZFMISC_1.product (TARSKI.upair x1 y1)
        (TARSKI.singleton x2)) (TARSKI.upair x3 y3) =
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair y1 x2))
        (TARSKI.upair x3 y3) :=
    congrArg (fun s => ZFMISC_1.product s (TARSKI.upair x3 y3)) h1
  have h3 :
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair y1 x2))
        (TARSKI.upair x3 y3) =
      ENUMSET1.enumset4 (TARSKI.pair (TARSKI.pair x1 x2) x3)
        (TARSKI.pair (TARSKI.pair x1 x2) y3)
        (TARSKI.pair (TARSKI.pair y1 x2) x3)
        (TARSKI.pair (TARSKI.pair y1 x2) y3) :=
    th23 (TARSKI.pair x1 x2) (TARSKI.pair y1 x2) x3 y3
  have h4 :
      ENUMSET1.enumset4 (TARSKI.pair (TARSKI.pair x1 x2) x3)
        (TARSKI.pair (TARSKI.pair x1 x2) y3)
        (TARSKI.pair (TARSKI.pair y1 x2) x3)
        (TARSKI.pair (TARSKI.pair y1 x2) y3) =
      ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 x2 y3)
        (XTUPLE_0.triple y1 x2 x3) (XTUPLE_0.triple y1 x2 y3) :=
    rfl
  have h5 :
      ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 x2 y3)
        (XTUPLE_0.triple y1 x2 x3) (XTUPLE_0.triple y1 x2 y3) =
      ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple y1 x2 x3)
        (XTUPLE_0.triple x1 x2 y3) (XTUPLE_0.triple y1 x2 y3) :=
    ENUMSET1.th62 (x1 := XTUPLE_0.triple x1 x2 x3)
      (x2 := XTUPLE_0.triple x1 x2 y3)
      (x3 := XTUPLE_0.triple y1 x2 x3)
      (x4 := XTUPLE_0.triple y1 x2 y3)
  exact h2.trans (h3.trans (h4.trans h5))

/-- Unlabeled `MCART_1` (`L417`). -/
theorem th41 (x1 x2 y2 x3 y3 : TarskiSet.{u}) :
    ZFMISC_1.product3 (TARSKI.singleton x1) (TARSKI.upair x2 y2)
      (TARSKI.upair x3 y3) =
      ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3)
        (XTUPLE_0.triple x1 x2 y3) (XTUPLE_0.triple x1 y2 y3) := by
  have h1 : ZFMISC_1.product (TARSKI.singleton x1) (TARSKI.upair x2 y2) =
      TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2) :=
    (ZFMISC_1.th30 (x := x1) (y := x2) (z := y2)).1
  have h2 :
      ZFMISC_1.product (ZFMISC_1.product (TARSKI.singleton x1)
        (TARSKI.upair x2 y2)) (TARSKI.upair x3 y3) =
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2))
        (TARSKI.upair x3 y3) :=
    congrArg (fun s => ZFMISC_1.product s (TARSKI.upair x3 y3)) h1
  have h3 :
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2))
        (TARSKI.upair x3 y3) =
      ENUMSET1.enumset4 (TARSKI.pair (TARSKI.pair x1 x2) x3)
        (TARSKI.pair (TARSKI.pair x1 x2) y3)
        (TARSKI.pair (TARSKI.pair x1 y2) x3)
        (TARSKI.pair (TARSKI.pair x1 y2) y3) :=
    th23 (TARSKI.pair x1 x2) (TARSKI.pair x1 y2) x3 y3
  have h5 :
      ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 x2 y3)
        (XTUPLE_0.triple x1 y2 x3) (XTUPLE_0.triple x1 y2 y3) =
      ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3)
        (XTUPLE_0.triple x1 x2 y3) (XTUPLE_0.triple x1 y2 y3) :=
    ENUMSET1.th62 (x1 := XTUPLE_0.triple x1 x2 x3)
      (x2 := XTUPLE_0.triple x1 x2 y3)
      (x3 := XTUPLE_0.triple x1 y2 x3)
      (x4 := XTUPLE_0.triple x1 y2 y3)
  exact h2.trans (h3.trans h5)

/-- Unlabeled `MCART_1` (`L428`). -/
theorem th42 (x1 y1 x2 y2 x3 y3 : TarskiSet.{u}) :
    ZFMISC_1.product3 (TARSKI.upair x1 y1) (TARSKI.upair x2 y2)
      (TARSKI.upair x3 y3) =
      ENUMSET1.enumset8 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3)
        (XTUPLE_0.triple x1 x2 y3) (XTUPLE_0.triple x1 y2 y3)
        (XTUPLE_0.triple y1 x2 x3) (XTUPLE_0.triple y1 y2 x3)
        (XTUPLE_0.triple y1 x2 y3) (XTUPLE_0.triple y1 y2 y3) := by
  have a1' :
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2))
        (TARSKI.upair x3 y3) =
      ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3)
        (XTUPLE_0.triple x1 x2 y3) (XTUPLE_0.triple x1 y2 y3) := by
    have h := th23 (TARSKI.pair x1 x2) (TARSKI.pair x1 y2) x3 y3
    exact h.trans (ENUMSET1.th62 (x1 := XTUPLE_0.triple x1 x2 x3)
      (x2 := XTUPLE_0.triple x1 x2 y3)
      (x3 := XTUPLE_0.triple x1 y2 x3)
      (x4 := XTUPLE_0.triple x1 y2 y3))
  have a2' :
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.upair x3 y3) =
      ENUMSET1.enumset4 (XTUPLE_0.triple y1 x2 x3) (XTUPLE_0.triple y1 y2 x3)
        (XTUPLE_0.triple y1 x2 y3) (XTUPLE_0.triple y1 y2 y3) := by
    have h := th23 (TARSKI.pair y1 x2) (TARSKI.pair y1 y2) x3 y3
    exact h.trans (ENUMSET1.th62 (x1 := XTUPLE_0.triple y1 x2 x3)
      (x2 := XTUPLE_0.triple y1 x2 y3)
      (x3 := XTUPLE_0.triple y1 y2 x3)
      (x4 := XTUPLE_0.triple y1 y2 y3))
  have h0 : ZFMISC_1.product (TARSKI.upair x1 y1) (TARSKI.upair x2 y2) =
      ENUMSET1.enumset4 (TARSKI.pair x1 x2) (TARSKI.pair x1 y2)
        (TARSKI.pair y1 x2) (TARSKI.pair y1 y2) :=
    th23 x1 y1 x2 y2
  have h1 :
      ENUMSET1.enumset4 (TARSKI.pair x1 x2) (TARSKI.pair x1 y2)
        (TARSKI.pair y1 x2) (TARSKI.pair y1 y2) =
      TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2) ∪
        TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2) :=
    ENUMSET1.th5 (x1 := TARSKI.pair x1 x2) (x2 := TARSKI.pair x1 y2)
      (x3 := TARSKI.pair y1 x2) (x4 := TARSKI.pair y1 y2)
  have h2 :
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2) ∪
        TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.upair x3 y3) =
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2))
        (TARSKI.upair x3 y3) ∪
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.upair x3 y3) :=
    (ZFMISC_1.th97 (X := TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2))
      (Y := TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
      (Z := TARSKI.upair x3 y3)).1
  have hprod :
      ZFMISC_1.product3 (TARSKI.upair x1 y1) (TARSKI.upair x2 y2)
        (TARSKI.upair x3 y3) =
      ZFMISC_1.product (ENUMSET1.enumset4 (TARSKI.pair x1 x2)
        (TARSKI.pair x1 y2) (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.upair x3 y3) :=
    congrArg (fun s => ZFMISC_1.product s (TARSKI.upair x3 y3)) h0
  have hunion :
      ZFMISC_1.product (ENUMSET1.enumset4 (TARSKI.pair x1 x2)
        (TARSKI.pair x1 y2) (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.upair x3 y3) =
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2) ∪
        TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.upair x3 y3) :=
    congrArg (fun s => ZFMISC_1.product s (TARSKI.upair x3 y3)) h1
  have h34 :
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair x1 y2))
        (TARSKI.upair x3 y3) ∪
      ZFMISC_1.product (TARSKI.upair (TARSKI.pair y1 x2) (TARSKI.pair y1 y2))
        (TARSKI.upair x3 y3) =
      ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple x1 y2 x3)
        (XTUPLE_0.triple x1 x2 y3) (XTUPLE_0.triple x1 y2 y3) ∪
      ENUMSET1.enumset4 (XTUPLE_0.triple y1 x2 x3) (XTUPLE_0.triple y1 y2 x3)
        (XTUPLE_0.triple y1 x2 y3) (XTUPLE_0.triple y1 y2 y3) :=
    Eq.subst (motive := fun s =>
        s ∪ ZFMISC_1.product (TARSKI.upair (TARSKI.pair y1 x2)
          (TARSKI.pair y1 y2)) (TARSKI.upair x3 y3) =
        ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3)
          (XTUPLE_0.triple x1 y2 x3) (XTUPLE_0.triple x1 x2 y3)
          (XTUPLE_0.triple x1 y2 y3) ∪
        ENUMSET1.enumset4 (XTUPLE_0.triple y1 x2 x3)
          (XTUPLE_0.triple y1 y2 x3) (XTUPLE_0.triple y1 x2 y3)
          (XTUPLE_0.triple y1 y2 y3))
      a1'.symm
      (Eq.subst (motive := fun s =>
          ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3)
            (XTUPLE_0.triple x1 y2 x3) (XTUPLE_0.triple x1 x2 y3)
            (XTUPLE_0.triple x1 y2 y3) ∪ s =
          ENUMSET1.enumset4 (XTUPLE_0.triple x1 x2 x3)
            (XTUPLE_0.triple x1 y2 x3) (XTUPLE_0.triple x1 x2 y3)
            (XTUPLE_0.triple x1 y2 y3) ∪
          ENUMSET1.enumset4 (XTUPLE_0.triple y1 x2 x3)
            (XTUPLE_0.triple y1 y2 x3) (XTUPLE_0.triple y1 x2 y3)
            (XTUPLE_0.triple y1 y2 y3))
        a2'.symm rfl)
  exact hprod.trans (hunion.trans (h2.trans (h34.trans
    (ENUMSET1.th25 (x1 := XTUPLE_0.triple x1 x2 x3)
      (x2 := XTUPLE_0.triple x1 y2 x3)
      (x3 := XTUPLE_0.triple x1 x2 y3)
      (x4 := XTUPLE_0.triple x1 y2 y3)
      (x5 := XTUPLE_0.triple y1 x2 x3)
      (x6 := XTUPLE_0.triple y1 y2 x3)
      (x7 := XTUPLE_0.triple y1 x2 y3)
      (x8 := XTUPLE_0.triple y1 y2 y3)).symm)))

/-- `MCART_1:def 5`. `MCART_1:def 1`–`4` are canceled. -/
theorem def5 {X1 X2 X3 x x1 x2 x3 : TarskiSet.{u}}
    (_h1 : X1 ≠ (∅ : TarskiSet.{u})) (_h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (_h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (_hx : x ∈ ZFMISC_1.product3 X1 X2 X3)
    (heq : x = XTUPLE_0.triple x1 x2 x3) :
    XTUPLE_0.fst3 x = x1 :=
  Eq.subst (motive := fun s => XTUPLE_0.fst3 s = x1) heq.symm
    (XTUPLE_0.fst3_triple x1 x2 x3)

/-- `MCART_1:def 6` -/
theorem def6 {X1 X2 X3 x x1 x2 x3 : TarskiSet.{u}}
    (_h1 : X1 ≠ (∅ : TarskiSet.{u})) (_h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (_h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (_hx : x ∈ ZFMISC_1.product3 X1 X2 X3)
    (heq : x = XTUPLE_0.triple x1 x2 x3) :
    XTUPLE_0.snd3 x = x2 :=
  Eq.subst (motive := fun s => XTUPLE_0.snd3 s = x2) heq.symm
    (XTUPLE_0.snd3_triple x1 x2 x3)

/-- `MCART_1:def 7` -/
theorem def7 {X1 X2 X3 x x1 x2 x3 : TarskiSet.{u}}
    (_h1 : X1 ≠ (∅ : TarskiSet.{u})) (_h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (_h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (_hx : x ∈ ZFMISC_1.product3 X1 X2 X3)
    (heq : x = XTUPLE_0.triple x1 x2 x3) :
    XTUPLE_0.thd3 x = x3 :=
  Eq.subst (motive := fun s => XTUPLE_0.thd3 s = x3) heq.symm
    (XTUPLE_0.thd3_triple x1 x2 x3)

/-- Unlabeled `MCART_1` (`L554`). `MCART_1:44` is canceled. -/
theorem th43 {X1 X2 X3 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product3 X1 X2 X3) :
    x = XTUPLE_0.triple (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x)
      (XTUPLE_0.thd3 x) := by
  obtain ⟨xx1, xx2, xx3, _, _, _, heq⟩ := lm2 h1 h2 h3 hx
  exact (XTUPLE_0.triple_eta ⟨xx1, xx2, xx3, heq⟩).symm


/-- `MCART_1:45` (`Th45`) -/
theorem th45 {X Y Z : TarskiSet.{u}}
    (h : X ⊆ ZFMISC_1.product3 X Y Z ∨
      X ⊆ ZFMISC_1.product3 Y Z X ∨
      X ⊆ ZFMISC_1.product3 Z X Y) :
    X = (∅ : TarskiSet.{u}) := by
  refine Classical.byContradiction fun hne => ?_
  have hneX : X ≠ (∅ : TarskiSet.{u}) := hne
  exact Or.elim h
    (fun hXY =>
      let ⟨w, hw⟩ := XBOOLE_0.th7 hneX
      let hwP : w ∈ ZFMISC_1.product3 X Y Z := hXY w hw
      let hPne : ZFMISC_1.product3 X Y Z ≠ (∅ : TarskiSet.{u}) :=
        fun hempty => (XBOOLE_0.empty_iff w).mp
          (Eq.subst (motive := fun s => w ∈ s) hempty hwP)
      let ⟨hXne, hYZ⟩ := (th31 X Y Z).mpr hPne
      let ⟨hYne, hZne⟩ := hYZ
      let ⟨v, hvX, hnot⟩ := th26 hneX
      let hvP : v ∈ ZFMISC_1.product3 X Y Z := hXY v hvX
      let ⟨xx1, xx2, xx3, hx1, _, _, heq⟩ := lm2 hXne hYne hZne hvP
      hnot ⟨xx1, xx2, xx3, Or.inl hx1, heq⟩)
    (fun hrest =>
      Or.elim hrest
        (fun hYX =>
          hneX (ZFMISC_1.th111 (X := X) (Y := ZFMISC_1.product Y Z)
            (Or.inr hYX)))
        (fun hZX =>
          let ⟨v, hvX, hnot⟩ := th26 hneX
          let hvP : v ∈ ZFMISC_1.product3 Z X Y := hZX v hvX
          let hPne : ZFMISC_1.product3 Z X Y ≠ (∅ : TarskiSet.{u}) :=
            fun hempty => (XBOOLE_0.empty_iff v).mp
              (Eq.subst (motive := fun s => v ∈ s) hempty hvP)
          let ⟨hZne, hXY⟩ := (th31 Z X Y).mpr hPne
          let ⟨hXne2, hYne⟩ := hXY
          let ⟨xx1, xx2, xx3, _, hx2, _, heq⟩ := lm2 hZne hXne2 hYne hvP
          hnot ⟨xx1, xx2, xx3, Or.inr hx2, heq⟩))

/-- `MCART_1:47` (`Th47`). `MCART_1:46` is canceled. -/
theorem th47 {X1 X2 X3 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product3 X1 X2 X3) :
    x ≠ XTUPLE_0.fst3 x ∧ x ≠ XTUPLE_0.snd3 x ∧ x ≠ XTUPLE_0.thd3 x := by
  have heta := th43 h1 h2 h3 hx
  have ⟨xx1, xx2, xx3, _, _, _, heq⟩ := lm2 h1 h2 h3 hx
  have ha : XTUPLE_0.fst3 x = xx1 := def5 h1 h2 h3 hx heq
  have hb : XTUPLE_0.snd3 x = xx2 := def6 h1 h2 h3 hx heq
  have hc : XTUPLE_0.thd3 x = xx3 := def7 h1 h2 h3 hx heq
  have hp : XTUPLE_0.isPair x := ⟨TARSKI.pair xx1 xx2, xx3, heq⟩
  constructor
  · intro hxf
    let Y9 := TARSKI.upair (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x)
    let Y := TARSKI.pair (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x)
    let X9 := TARSKI.upair Y (XTUPLE_0.thd3 x)
    have hX : TARSKI.pair Y (XTUPLE_0.thd3 x) = x := heta.symm
    have h1m : XTUPLE_0.fst3 x ∈ Y9 :=
      (TARSKI.upair_iff (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x)
        (XTUPLE_0.fst3 x)).mpr (Or.inl rfl)
    have h2m : Y9 ∈ Y :=
      (TARSKI.def2 Y9 (TARSKI.singleton (XTUPLE_0.fst3 x)) Y9).mpr (Or.inl rfl)
    have h3m : Y ∈ X9 :=
      (TARSKI.upair_iff Y (XTUPLE_0.thd3 x) Y).mpr (Or.inl rfl)
    have h4m : X9 ∈ x :=
      Eq.subst (motive := fun s => X9 ∈ s) hX
        ((TARSKI.def2 X9 (TARSKI.singleton Y) X9).mpr (Or.inl rfl))
    have h4f : X9 ∈ XTUPLE_0.fst3 x :=
      Eq.subst (motive := fun s => X9 ∈ s) hxf h4m
    exact XREGULAR.th8 ⟨h1m, h2m, h3m, h4f⟩
  constructor
  · intro hxs
    let Y9 := TARSKI.upair (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x)
    let Y := TARSKI.pair (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x)
    let X9 := TARSKI.upair Y (XTUPLE_0.thd3 x)
    have hX : TARSKI.pair Y (XTUPLE_0.thd3 x) = x := heta.symm
    have h1m : XTUPLE_0.snd3 x ∈ Y9 :=
      (TARSKI.upair_iff (XTUPLE_0.fst3 x) (XTUPLE_0.snd3 x)
        (XTUPLE_0.snd3 x)).mpr (Or.inr rfl)
    have h2m : Y9 ∈ Y :=
      (TARSKI.def2 Y9 (TARSKI.singleton (XTUPLE_0.fst3 x)) Y9).mpr (Or.inl rfl)
    have h3m : Y ∈ X9 :=
      (TARSKI.upair_iff Y (XTUPLE_0.thd3 x) Y).mpr (Or.inl rfl)
    have h4m : X9 ∈ x :=
      Eq.subst (motive := fun s => X9 ∈ s) hX
        ((TARSKI.def2 X9 (TARSKI.singleton Y) X9).mpr (Or.inl rfl))
    have h4s : X9 ∈ XTUPLE_0.snd3 x :=
      Eq.subst (motive := fun s => X9 ∈ s) hxs h4m
    exact XREGULAR.th8 ⟨h1m, h2m, h3m, h4s⟩
  · intro hxt
    have hpair : x = TARSKI.pair (TARSKI.pair xx1 xx2) xx3 := heq
    have hsnd : XTUPLE_0.snd x = xx3 :=
      XTUPLE_0.def2 hpair
    have hxx : xx3 = x := (hxt.trans hc).symm
    have hsndx : XTUPLE_0.snd x = x := hsnd.trans hxx
    exact (th20 hp).2 hsndx.symm

/-- Unlabeled `MCART_1` (`L612`). -/
theorem th48 {X1 X2 X3 Y1 Y2 Y3 : TarskiSet.{u}}
    (h : XBOOLE_0.meets (ZFMISC_1.product3 X1 X2 X3)
      (ZFMISC_1.product3 Y1 Y2 Y3)) :
    XBOOLE_0.meets X1 Y1 ∧ XBOOLE_0.meets X2 Y2 ∧ XBOOLE_0.meets X3 Y3 := by
  have h12 : XBOOLE_0.meets (ZFMISC_1.product X1 X2) (ZFMISC_1.product Y1 Y2) :=
    fun hmiss =>
      h (ZFMISC_1.th104 (X1 := ZFMISC_1.product X1 X2)
        (X2 := ZFMISC_1.product Y1 Y2) (Y1 := X3) (Y2 := Y3)
        (Or.inl hmiss))
  constructor
  · exact fun hmiss =>
      h12 (ZFMISC_1.th104 (X1 := X1) (X2 := Y1) (Y1 := X2) (Y2 := Y2)
        (Or.inl hmiss))
  constructor
  · exact fun hmiss =>
      h12 (ZFMISC_1.th104 (X1 := X1) (X2 := Y1) (Y1 := X2) (Y2 := Y2)
        (Or.inr hmiss))
  · exact fun hmiss =>
      h (ZFMISC_1.th104 (X1 := ZFMISC_1.product X1 X2)
        (X2 := ZFMISC_1.product Y1 Y2) (Y1 := X3) (Y2 := Y3)
        (Or.inr hmiss))

/-- `MCART_1:49` (`Th49`) -/
theorem th49 (X1 X2 X3 X4 : TarskiSet.{u}) :
    ZFMISC_1.product4 X1 X2 X3 X4 =
      ZFMISC_1.product (ZFMISC_1.product (ZFMISC_1.product X1 X2) X3) X4 :=
  rfl

/-- `MCART_1:50` (`Th50`) -/
theorem th50 (X1 X2 X3 X4 : TarskiSet.{u}) :
    ZFMISC_1.product3 (ZFMISC_1.product X1 X2) X3 X4 =
      ZFMISC_1.product4 X1 X2 X3 X4 :=
  rfl

/-- `MCART_1:51` (`Th51`) -/
theorem th51 (X1 X2 X3 X4 : TarskiSet.{u}) :
    (X1 ≠ (∅ : TarskiSet.{u}) ∧ X2 ≠ (∅ : TarskiSet.{u}) ∧
      X3 ≠ (∅ : TarskiSet.{u}) ∧ X4 ≠ (∅ : TarskiSet.{u})) ↔
      ZFMISC_1.product4 X1 X2 X3 X4 ≠ (∅ : TarskiSet.{u}) := by
  have h3 : (X1 ≠ (∅ : TarskiSet.{u}) ∧ X2 ≠ (∅ : TarskiSet.{u}) ∧
      X3 ≠ (∅ : TarskiSet.{u})) ↔
      ZFMISC_1.product3 X1 X2 X3 ≠ (∅ : TarskiSet.{u}) :=
    th31 X1 X2 X3
  have h4 : ZFMISC_1.product4 X1 X2 X3 X4 = (∅ : TarskiSet.{u}) ↔
      ZFMISC_1.product3 X1 X2 X3 = (∅ : TarskiSet.{u}) ∨
        X4 = (∅ : TarskiSet.{u}) :=
    ZFMISC_1.th90 (X := ZFMISC_1.product3 X1 X2 X3) (Y := X4)
  constructor
  · intro ⟨h1, h2, h3ne, h4ne⟩
    intro hempty
    exact Or.elim (h4.mp hempty)
      (fun h3e => (h3.mp ⟨h1, h2, h3ne⟩) h3e)
      (fun h => h4ne h)
  · intro hne
    refine Classical.byContradiction fun hnot => ?_
    have hempty : ZFMISC_1.product4 X1 X2 X3 X4 = (∅ : TarskiSet.{u}) :=
      h4.mpr
        (Or.elim (Classical.em (X4 = (∅ : TarskiSet.{u})))
          (fun h => Or.inr h)
          (fun hn4 =>
            Or.inl (Classical.byContradiction fun hn3 =>
              have ⟨a, b⟩ : X1 ≠ (∅ : TarskiSet.{u}) ∧
                  X2 ≠ (∅ : TarskiSet.{u}) ∧ X3 ≠ (∅ : TarskiSet.{u}) :=
                (th31 X1 X2 X3).mpr hn3
              hnot ⟨a, b.1, b.2, hn4⟩)))
    exact hne hempty

/-- `MCART_1:52` (`Th52`) -/
theorem th52 {X1 X2 X3 X4 Y1 Y2 Y3 Y4 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (heq : ZFMISC_1.product4 X1 X2 X3 X4 = ZFMISC_1.product4 Y1 Y2 Y3 Y4) :
    X1 = Y1 ∧ X2 = Y2 ∧ X3 = Y3 ∧ X4 = Y4 := by
  have h123 : ZFMISC_1.product3 X1 X2 X3 ≠ (∅ : TarskiSet.{u}) :=
    (th31 X1 X2 X3).mp ⟨h1, h2, h3⟩
  have ⟨hXY, h4eq⟩ :=
    ZFMISC_1.th110 (X1 := ZFMISC_1.product3 X1 X2 X3) (Y1 := X4)
      (X2 := ZFMISC_1.product3 Y1 Y2 Y3) (Y2 := Y4) h123 h4 heq
  have ⟨h1eq, h23⟩ := th32 h1 h2 h3 hXY
  exact ⟨h1eq, h23.1, h23.2, h4eq⟩

/-- Unlabeled `MCART_1` (`L667`). -/
theorem th53 {X1 X2 X3 X4 Y1 Y2 Y3 Y4 : TarskiSet.{u}}
    (hne : ZFMISC_1.product4 X1 X2 X3 X4 ≠ (∅ : TarskiSet.{u}))
    (heq : ZFMISC_1.product4 X1 X2 X3 X4 = ZFMISC_1.product4 Y1 Y2 Y3 Y4) :
    X1 = Y1 ∧ X2 = Y2 ∧ X3 = Y3 ∧ X4 = Y4 :=
  let ⟨h1, hrest⟩ := (th51 X1 X2 X3 X4).mpr hne
  let ⟨h2, h34⟩ := hrest
  let ⟨h3, h4⟩ := h34
  th52 h1 h2 h3 h4 heq

/-- Unlabeled `MCART_1` (`L679`). -/
theorem th54 {X Y : TarskiSet.{u}}
    (heq : ZFMISC_1.product4 X X X X = ZFMISC_1.product4 Y Y Y Y) : X = Y :=
  Or.elim (Classical.em (X = (∅ : TarskiSet.{u})))
    (fun hXe => by
      have hemptyX : ZFMISC_1.product4 X X X X = (∅ : TarskiSet.{u}) :=
        Classical.byContradiction fun hne =>
          ((th51 X X X X).mpr hne).1 hXe
      have hemptyY : ZFMISC_1.product4 Y Y Y Y = (∅ : TarskiSet.{u}) :=
        heq.symm.trans hemptyX
      have hYe : Y = (∅ : TarskiSet.{u}) :=
        Classical.byContradiction fun hYne =>
          (th51 Y Y Y Y).mp ⟨hYne, hYne, hYne, hYne⟩ hemptyY
      exact hXe.trans hYe.symm)
    (fun hXne => (th52 hXne hXne hXne hXne heq).1)

/-- `MCART_1:lm 3` -/
theorem lm3 {X1 X2 X3 X4 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product4 X1 X2 X3 X4) :
    ∃ xx1 xx2 xx3 xx4, xx1 ∈ X1 ∧ xx2 ∈ X2 ∧ xx3 ∈ X3 ∧ xx4 ∈ X4 ∧
      x = XTUPLE_0.quadruple xx1 xx2 xx3 xx4 := by
  have h123 : ZFMISC_1.product3 X1 X2 X3 ≠ (∅ : TarskiSet.{u}) :=
    (th31 X1 X2 X3).mp ⟨h1, h2, h3⟩
  obtain ⟨x123, xx4, hx123, hx4, heq⟩ := lm1 h123 h4 hx
  obtain ⟨xx1, xx2, xx3, hx1, hx2, hx3, heq123⟩ := lm2 h1 h2 h3 hx123
  refine ⟨xx1, xx2, xx3, xx4, hx1, hx2, hx3, hx4, ?_⟩
  exact heq.trans (congrArg (fun s => TARSKI.pair s xx4) heq123)

/-- `MCART_1:def 8` -/
theorem def8 {X1 X2 X3 X4 x x1 x2 x3 x4 : TarskiSet.{u}}
    (_h1 : X1 ≠ (∅ : TarskiSet.{u})) (_h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (_h3 : X3 ≠ (∅ : TarskiSet.{u})) (_h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (_hx : x ∈ ZFMISC_1.product4 X1 X2 X3 X4)
    (heq : x = XTUPLE_0.quadruple x1 x2 x3 x4) :
    XTUPLE_0.fst4 x = x1 :=
  Eq.subst (motive := fun s => XTUPLE_0.fst4 s = x1) heq.symm
    (XTUPLE_0.fst4_quadruple x1 x2 x3 x4)

/-- `MCART_1:def 9` -/
theorem def9 {X1 X2 X3 X4 x x1 x2 x3 x4 : TarskiSet.{u}}
    (_h1 : X1 ≠ (∅ : TarskiSet.{u})) (_h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (_h3 : X3 ≠ (∅ : TarskiSet.{u})) (_h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (_hx : x ∈ ZFMISC_1.product4 X1 X2 X3 X4)
    (heq : x = XTUPLE_0.quadruple x1 x2 x3 x4) :
    XTUPLE_0.snd4 x = x2 :=
  Eq.subst (motive := fun s => XTUPLE_0.snd4 s = x2) heq.symm
    (XTUPLE_0.snd4_quadruple x1 x2 x3 x4)

/-- `MCART_1:def 10` -/
theorem def10 {X1 X2 X3 X4 x x1 x2 x3 x4 : TarskiSet.{u}}
    (_h1 : X1 ≠ (∅ : TarskiSet.{u})) (_h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (_h3 : X3 ≠ (∅ : TarskiSet.{u})) (_h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (_hx : x ∈ ZFMISC_1.product4 X1 X2 X3 X4)
    (heq : x = XTUPLE_0.quadruple x1 x2 x3 x4) :
    XTUPLE_0.thd4 x = x3 :=
  Eq.subst (motive := fun s => XTUPLE_0.thd4 s = x3) heq.symm
    (XTUPLE_0.thd4_quadruple x1 x2 x3 x4)

/-- `MCART_1:def 11` -/
theorem def11 {X1 X2 X3 X4 x x1 x2 x3 x4 : TarskiSet.{u}}
    (_h1 : X1 ≠ (∅ : TarskiSet.{u})) (_h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (_h3 : X3 ≠ (∅ : TarskiSet.{u})) (_h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (_hx : x ∈ ZFMISC_1.product4 X1 X2 X3 X4)
    (heq : x = XTUPLE_0.quadruple x1 x2 x3 x4) :
    XTUPLE_0.fth4 x = x4 :=
  Eq.subst (motive := fun s => XTUPLE_0.fth4 s = x4) heq.symm
    (XTUPLE_0.fth4_quadruple x1 x2 x3 x4)

/-- Unlabeled `MCART_1` (`L845`). -/
theorem th55 {X1 X2 X3 X4 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product4 X1 X2 X3 X4) :
    x = XTUPLE_0.quadruple (XTUPLE_0.fst4 x) (XTUPLE_0.snd4 x)
      (XTUPLE_0.thd4 x) (XTUPLE_0.fth4 x) := by
  obtain ⟨xx1, xx2, xx3, xx4, _, _, _, _, heq⟩ := lm3 h1 h2 h3 h4 hx
  exact (XTUPLE_0.quadruple_eta ⟨xx1, xx2, xx3, xx4, heq⟩).symm

/-- Unlabeled `MCART_1` (`L852`). -/
theorem th56 {X1 X2 X3 X4 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product4 X1 X2 X3 X4) :
    x ≠ XTUPLE_0.fst4 x ∧ x ≠ XTUPLE_0.snd4 x ∧
      x ≠ XTUPLE_0.thd4 x ∧ x ≠ XTUPLE_0.fth4 x := by
  have hY : ZFMISC_1.product X1 X2 ≠ (∅ : TarskiSet.{u}) :=
    fun hempty =>
      Or.elim ((ZFMISC_1.th90 (X := X1) (Y := X2)).mp hempty)
        (fun h => h1 h) (fun h => h2 h)
  have hx3 : x ∈ ZFMISC_1.product3 (ZFMISC_1.product X1 X2) X3 X4 := hx
  have ⟨_, hne2, hne3⟩ := th47 hY h3 h4 hx3
  have heta := th55 h1 h2 h3 h4 hx
  constructor
  · intro hxf
    let Z9 := TARSKI.upair (XTUPLE_0.fst4 x) (XTUPLE_0.snd4 x)
    let Z := TARSKI.pair (XTUPLE_0.fst4 x) (XTUPLE_0.snd4 x)
    let Y9 := TARSKI.upair Z (XTUPLE_0.thd4 x)
    let Y := TARSKI.pair Z (XTUPLE_0.thd4 x)
    let X9 := TARSKI.upair Y (XTUPLE_0.fth4 x)
    have hX : TARSKI.pair Y (XTUPLE_0.fth4 x) = x := heta.symm
    have c1 : XTUPLE_0.fst4 x ∈ Z9 :=
      (TARSKI.upair_iff _ _ _).mpr (Or.inl rfl)
    have c2 : Z9 ∈ Z :=
      (TARSKI.def2 Z9 (TARSKI.singleton (XTUPLE_0.fst4 x)) Z9).mpr (Or.inl rfl)
    have c3 : Z ∈ Y9 := (TARSKI.upair_iff Z _ Z).mpr (Or.inl rfl)
    have c4 : Y9 ∈ Y :=
      (TARSKI.def2 Y9 (TARSKI.singleton Z) Y9).mpr (Or.inl rfl)
    have c5 : Y ∈ X9 := (TARSKI.upair_iff Y _ Y).mpr (Or.inl rfl)
    have c6 : X9 ∈ x :=
      Eq.subst (motive := fun s => X9 ∈ s) hX
        ((TARSKI.def2 X9 (TARSKI.singleton Y) X9).mpr (Or.inl rfl))
    exact XREGULAR.th10 ⟨c1, c2, c3, c4, c5,
      Eq.subst (motive := fun s => X9 ∈ s) hxf c6⟩
  constructor
  · intro hxs
    let Z9 := TARSKI.upair (XTUPLE_0.fst4 x) (XTUPLE_0.snd4 x)
    let Z := TARSKI.pair (XTUPLE_0.fst4 x) (XTUPLE_0.snd4 x)
    let Y9 := TARSKI.upair Z (XTUPLE_0.thd4 x)
    let Y := TARSKI.pair Z (XTUPLE_0.thd4 x)
    let X9 := TARSKI.upair Y (XTUPLE_0.fth4 x)
    have hX : TARSKI.pair Y (XTUPLE_0.fth4 x) = x := heta.symm
    have c1 : XTUPLE_0.snd4 x ∈ Z9 :=
      (TARSKI.upair_iff _ _ _).mpr (Or.inr rfl)
    have c2 : Z9 ∈ Z :=
      (TARSKI.def2 Z9 (TARSKI.singleton (XTUPLE_0.fst4 x)) Z9).mpr (Or.inl rfl)
    have c3 : Z ∈ Y9 := (TARSKI.upair_iff Z _ Z).mpr (Or.inl rfl)
    have c4 : Y9 ∈ Y :=
      (TARSKI.def2 Y9 (TARSKI.singleton Z) Y9).mpr (Or.inl rfl)
    have c5 : Y ∈ X9 := (TARSKI.upair_iff Y _ Y).mpr (Or.inl rfl)
    have c6 : X9 ∈ x :=
      Eq.subst (motive := fun s => X9 ∈ s) hX
        ((TARSKI.def2 X9 (TARSKI.singleton Y) X9).mpr (Or.inl rfl))
    exact XREGULAR.th10 ⟨c1, c2, c3, c4, c5,
      Eq.subst (motive := fun s => X9 ∈ s) hxs c6⟩
  exact ⟨hne2, hne3⟩

/-- Unlabeled `MCART_1` (`L875`). -/
theorem th57 {X1 X2 X3 X4 : TarskiSet.{u}}
    (h : X1 ⊆ ZFMISC_1.product4 X1 X2 X3 X4 ∨
      X1 ⊆ ZFMISC_1.product4 X2 X3 X4 X1 ∨
      X1 ⊆ ZFMISC_1.product4 X3 X4 X1 X2 ∨
      X1 ⊆ ZFMISC_1.product4 X4 X1 X2 X3) :
    X1 = (∅ : TarskiSet.{u}) := by
  refine Classical.byContradiction fun hne => ?_
  exact Or.elim h
    (fun h1 =>
      let ⟨v, hv, hnot⟩ := th30 hne
      let hvP : v ∈ ZFMISC_1.product4 X1 X2 X3 X4 := h1 v hv
      let hPne : ZFMISC_1.product4 X1 X2 X3 X4 ≠ (∅ : TarskiSet.{u}) :=
        fun hempty => (XBOOLE_0.empty_iff v).mp
          (Eq.subst (motive := fun s => v ∈ s) hempty hvP)
      let ⟨a, rest⟩ := (th51 X1 X2 X3 X4).mpr hPne
      let ⟨b, rest2⟩ := rest
      let ⟨c, d⟩ := rest2
      let ⟨xx1, xx2, xx3, xx4, hx1, _, _, _, heq⟩ := lm3 a b c d hvP
      hnot ⟨xx1, xx2, xx3, xx4, Or.inl hx1, heq⟩)
    (fun hrest =>
      Or.elim hrest
        (fun h2 =>
          hne (th45 (X := X1) (Y := ZFMISC_1.product X2 X3) (Z := X4)
            (Or.inr (Or.inl h2))))
        (fun hrest2 =>
          Or.elim hrest2
            (fun h3 =>
              hne (th45 (X := X1) (Y := X2) (Z := ZFMISC_1.product X3 X4)
                (Or.inr (Or.inr h3))))
            (fun h4 =>
              let ⟨v, hv, hnot⟩ := th30 hne
              let hvP : v ∈ ZFMISC_1.product4 X4 X1 X2 X3 := h4 v hv
              let hPne : ZFMISC_1.product4 X4 X1 X2 X3 ≠ (∅ : TarskiSet.{u}) :=
                fun hempty => (XBOOLE_0.empty_iff v).mp
                  (Eq.subst (motive := fun s => v ∈ s) hempty hvP)
              let ⟨a, rest⟩ := (th51 X4 X1 X2 X3).mpr hPne
              let ⟨b, rest2⟩ := rest
              let ⟨c, d⟩ := rest2
              let ⟨xx1, xx2, xx3, xx4, _, hx2, _, _, heq⟩ := lm3 a b c d hvP
              hnot ⟨xx1, xx2, xx3, xx4, Or.inr hx2, heq⟩)))

/-- Unlabeled `MCART_1` (`L919`). -/
theorem th58 {X1 X2 X3 X4 Y1 Y2 Y3 Y4 : TarskiSet.{u}}
    (h : XBOOLE_0.meets (ZFMISC_1.product4 X1 X2 X3 X4)
      (ZFMISC_1.product4 Y1 Y2 Y3 Y4)) :
    XBOOLE_0.meets X1 Y1 ∧ XBOOLE_0.meets X2 Y2 ∧
      XBOOLE_0.meets X3 Y3 ∧ XBOOLE_0.meets X4 Y4 := by
  have h3 : XBOOLE_0.meets (ZFMISC_1.product3 X1 X2 X3)
      (ZFMISC_1.product3 Y1 Y2 Y3) :=
    fun hmiss =>
      h (ZFMISC_1.th104 (X1 := ZFMISC_1.product3 X1 X2 X3)
        (X2 := ZFMISC_1.product3 Y1 Y2 Y3) (Y1 := X4) (Y2 := Y4)
        (Or.inl hmiss))
  have ⟨hm1, hm2, hm3⟩ := th48 h3
  have hm4 : XBOOLE_0.meets X4 Y4 :=
    fun hmiss =>
      h (ZFMISC_1.th104 (X1 := ZFMISC_1.product3 X1 X2 X3)
        (X2 := ZFMISC_1.product3 Y1 Y2 Y3) (Y1 := X4) (Y2 := Y4)
        (Or.inr hmiss))
  exact ⟨hm1, hm2, hm3, hm4⟩

/-- Unlabeled `MCART_1` (`L933`). -/
theorem th59 (x1 x2 x3 x4 : TarskiSet.{u}) :
    ZFMISC_1.product4 (TARSKI.singleton x1) (TARSKI.singleton x2)
      (TARSKI.singleton x3) (TARSKI.singleton x4) =
      TARSKI.singleton (XTUPLE_0.quadruple x1 x2 x3 x4) := by
  have h := th35 (TARSKI.pair x1 x2) x3 x4
  have h29 : ZFMISC_1.product (TARSKI.singleton x1) (TARSKI.singleton x2) =
      TARSKI.singleton (TARSKI.pair x1 x2) :=
    ZFMISC_1.th29 (x := x1) (y := x2)
  have h3 :
      ZFMISC_1.product3 (ZFMISC_1.product (TARSKI.singleton x1)
        (TARSKI.singleton x2)) (TARSKI.singleton x3) (TARSKI.singleton x4) =
      ZFMISC_1.product3 (TARSKI.singleton (TARSKI.pair x1 x2))
        (TARSKI.singleton x3) (TARSKI.singleton x4) :=
    congrArg (fun s => ZFMISC_1.product3 s (TARSKI.singleton x3)
      (TARSKI.singleton x4)) h29
  exact h3.trans (h.trans rfl)

/-- `MCART_1:62` (`Th62`). -/
theorem th62 {X Y x : TarskiSet.{u}}
    (hne : ZFMISC_1.product X Y ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product X Y) :
    x ≠ XTUPLE_0.fst x ∧ x ≠ XTUPLE_0.snd x :=
  Or.elim (Classical.em (X = (∅ : TarskiSet.{u})))
    (fun hX => (hne ((ZFMISC_1.th90 (X := X) (Y := Y)).mpr (Or.inl hX))).elim)
    (fun hX =>
      Or.elim (Classical.em (Y = (∅ : TarskiSet.{u})))
        (fun hY => (hne ((ZFMISC_1.th90 (X := X) (Y := Y)).mpr (Or.inr hY))).elim)
        (fun hY => th24 hX hY hx))

/-- Unlabeled `MCART_1` (`L953`). -/
theorem th63 {X Y x : TarskiSet.{u}} (hx : x ∈ ZFMISC_1.product X Y) :
    x ≠ XTUPLE_0.fst x ∧ x ≠ XTUPLE_0.snd x :=
  th62 (fun hempty =>
    (XBOOLE_0.empty_iff x).mp
      (Eq.subst (motive := fun s => x ∈ s) hempty hx)) hx

/-- Unlabeled `MCART_1` (`L965`). -/
theorem th64 {X1 X2 X3 x x1 x2 x3 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product3 X1 X2 X3)
    (heq : x = XTUPLE_0.triple x1 x2 x3) :
    XTUPLE_0.fst3 x = x1 ∧ XTUPLE_0.snd3 x = x2 ∧ XTUPLE_0.thd3 x = x3 :=
  ⟨def5 h1 h2 h3 hx heq, def6 h1 h2 h3 hx heq, def7 h1 h2 h3 hx heq⟩

/-- Unlabeled `MCART_1` (`L971`). -/
theorem th65 {X1 X2 X3 x y1 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product3 X1 X2 X3)
    (hy : ∀ xx1 xx2 xx3, xx1 ∈ X1 → xx2 ∈ X2 → xx3 ∈ X3 →
      x = XTUPLE_0.triple xx1 xx2 xx3 → y1 = xx1) :
    y1 = XTUPLE_0.fst3 x :=
  let ⟨xx1, xx2, xx3, hx1, hx2, hx3, heq⟩ := lm2 h1 h2 h3 hx
  (hy xx1 xx2 xx3 hx1 hx2 hx3 heq).trans (def5 h1 h2 h3 hx heq).symm

/-- Unlabeled `MCART_1` (`L986`). -/
theorem th66 {X1 X2 X3 x y2 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product3 X1 X2 X3)
    (hy : ∀ xx1 xx2 xx3, xx1 ∈ X1 → xx2 ∈ X2 → xx3 ∈ X3 →
      x = XTUPLE_0.triple xx1 xx2 xx3 → y2 = xx2) :
    y2 = XTUPLE_0.snd3 x :=
  let ⟨xx1, xx2, xx3, hx1, hx2, hx3, heq⟩ := lm2 h1 h2 h3 hx
  (hy xx1 xx2 xx3 hx1 hx2 hx3 heq).trans (def6 h1 h2 h3 hx heq).symm

/-- Unlabeled `MCART_1` (`L1001`). -/
theorem th67 {X1 X2 X3 x y3 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product3 X1 X2 X3)
    (hy : ∀ xx1 xx2 xx3, xx1 ∈ X1 → xx2 ∈ X2 → xx3 ∈ X3 →
      x = XTUPLE_0.triple xx1 xx2 xx3 → y3 = xx3) :
    y3 = XTUPLE_0.thd3 x :=
  let ⟨xx1, xx2, xx3, hx1, hx2, hx3, heq⟩ := lm2 h1 h2 h3 hx
  (hy xx1 xx2 xx3 hx1 hx2 hx3 heq).trans (def7 h1 h2 h3 hx heq).symm

/-- `MCART_1:68` (`Th68`) -/
theorem th68 {z X1 X2 X3 : TarskiSet.{u}}
    (hz : z ∈ ZFMISC_1.product3 X1 X2 X3) :
    ∃ x1 x2 x3, x1 ∈ X1 ∧ x2 ∈ X2 ∧ x3 ∈ X3 ∧ z = XTUPLE_0.triple x1 x2 x3 := by
  obtain ⟨x12, x3, hx12, hx3, heq⟩ := (ZFMISC_1.def2 (ZFMISC_1.product X1 X2) X3 z).mp hz
  obtain ⟨x1, x2, hx1, hx2, heq12⟩ := (ZFMISC_1.def2 X1 X2 x12).mp hx12
  exact ⟨x1, x2, x3, hx1, hx2, hx3,
    heq.trans (congrArg (fun s => TARSKI.pair s x3) heq12)⟩

/-- `MCART_1:69` (`Th69`) -/
theorem th69 (x1 x2 x3 X1 X2 X3 : TarskiSet.{u}) :
    XTUPLE_0.triple x1 x2 x3 ∈ ZFMISC_1.product3 X1 X2 X3 ↔
      x1 ∈ X1 ∧ x2 ∈ X2 ∧ x3 ∈ X3 := by
  have h12 : TARSKI.pair x1 x2 ∈ ZFMISC_1.product X1 X2 ↔
      x1 ∈ X1 ∧ x2 ∈ X2 :=
    ZFMISC_1.th87 (x := x1) (y := x2) (X := X1) (Y := X2)
  have h3 : TARSKI.pair (TARSKI.pair x1 x2) x3 ∈
      ZFMISC_1.product (ZFMISC_1.product X1 X2) X3 ↔
      TARSKI.pair x1 x2 ∈ ZFMISC_1.product X1 X2 ∧ x3 ∈ X3 :=
    ZFMISC_1.th87 (x := TARSKI.pair x1 x2) (y := x3)
      (X := ZFMISC_1.product X1 X2) (Y := X3)
  constructor
  · intro hz
    have ⟨hp, hx3⟩ := h3.mp hz
    have ⟨hx1, hx2⟩ := h12.mp hp
    exact ⟨hx1, hx2, hx3⟩
  · intro ⟨hx1, hx2, hx3⟩
    exact h3.mpr ⟨h12.mpr ⟨hx1, hx2⟩, hx3⟩

/-- Unlabeled `MCART_1` (`L1042`). -/
theorem th70 {Z X1 X2 X3 : TarskiSet.{u}}
    (h : ∀ z, z ∈ Z ↔ ∃ x1 x2 x3, x1 ∈ X1 ∧ x2 ∈ X2 ∧ x3 ∈ X3 ∧
      z = XTUPLE_0.triple x1 x2 x3) :
    Z = ZFMISC_1.product3 X1 X2 X3 := by
  apply TARSKI.extensionality
  intro z
  constructor
  · intro hz
    obtain ⟨x1, x2, x3, hx1, hx2, hx3, heq⟩ := (h z).mp hz
    exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product3 X1 X2 X3)
      heq.symm ((th69 x1 x2 x3 X1 X2 X3).mpr ⟨hx1, hx2, hx3⟩)
  · intro hz
    obtain ⟨x1, x2, x3, hx1, hx2, hx3, heq⟩ := th68 hz
    exact (h z).mpr ⟨x1, x2, x3, hx1, hx2, hx3, heq⟩

/-- Unlabeled `MCART_1` (`L1077`). `MCART_1:71` is canceled. -/
theorem th72 {X1 X2 X3 A1 A2 A3 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u}))
    (_hA1 : A1 ≠ (∅ : TarskiSet.{u})) (_hA2 : A2 ≠ (∅ : TarskiSet.{u}))
    (_hA3 : A3 ≠ (∅ : TarskiSet.{u}))
    (_hA1s : A1 ⊆ X1) (_hA2s : A2 ⊆ X2) (_hA3s : A3 ⊆ X3)
    (hx : x ∈ ZFMISC_1.product3 X1 X2 X3)
    (hin : x ∈ ZFMISC_1.product3 A1 A2 A3) :
    XTUPLE_0.fst3 x ∈ A1 ∧ XTUPLE_0.snd3 x ∈ A2 ∧ XTUPLE_0.thd3 x ∈ A3 := by
  obtain ⟨x1, x2, x3, hx1, hx2, hx3, heq⟩ := th68 hin
  exact ⟨
    Eq.subst (motive := fun s => s ∈ A1) (def5 h1 h2 h3 hx heq).symm hx1,
    Eq.subst (motive := fun s => s ∈ A2) (def6 h1 h2 h3 hx heq).symm hx2,
    Eq.subst (motive := fun s => s ∈ A3) (def7 h1 h2 h3 hx heq).symm hx3⟩

/-- `MCART_1:73` (`Th73`) -/
theorem th73 {X1 X2 X3 Y1 Y2 Y3 : TarskiSet.{u}}
    (h1 : X1 ⊆ Y1) (h2 : X2 ⊆ Y2) (h3 : X3 ⊆ Y3) :
    ZFMISC_1.product3 X1 X2 X3 ⊆ ZFMISC_1.product3 Y1 Y2 Y3 :=
  ZFMISC_1.th96 (X1 := ZFMISC_1.product X1 X2) (X2 := X3)
    (Y1 := ZFMISC_1.product Y1 Y2) (Y2 := Y3)
    (ZFMISC_1.th96 h1 h2) h3

/-- Unlabeled `MCART_1` (`L1114`). -/
theorem th74 {X1 X2 X3 X4 x x1 x2 x3 x4 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product4 X1 X2 X3 X4)
    (heq : x = XTUPLE_0.quadruple x1 x2 x3 x4) :
    XTUPLE_0.fst4 x = x1 ∧ XTUPLE_0.snd4 x = x2 ∧
      XTUPLE_0.thd4 x = x3 ∧ XTUPLE_0.fth4 x = x4 :=
  ⟨def8 h1 h2 h3 h4 hx heq, def9 h1 h2 h3 h4 hx heq,
    def10 h1 h2 h3 h4 hx heq, def11 h1 h2 h3 h4 hx heq⟩

/-- Unlabeled `MCART_1` (`L1121`). -/
theorem th75 {X1 X2 X3 X4 x y1 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product4 X1 X2 X3 X4)
    (hy : ∀ xx1 xx2 xx3 xx4, xx1 ∈ X1 → xx2 ∈ X2 → xx3 ∈ X3 → xx4 ∈ X4 →
      x = XTUPLE_0.quadruple xx1 xx2 xx3 xx4 → y1 = xx1) :
    y1 = XTUPLE_0.fst4 x :=
  let ⟨xx1, xx2, xx3, xx4, hx1, hx2, hx3, hx4, heq⟩ := lm3 h1 h2 h3 h4 hx
  (hy xx1 xx2 xx3 xx4 hx1 hx2 hx3 hx4 heq).trans
    (def8 h1 h2 h3 h4 hx heq).symm

/-- Unlabeled `MCART_1` (`L1141`). -/
theorem th76 {X1 X2 X3 X4 x y2 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product4 X1 X2 X3 X4)
    (hy : ∀ xx1 xx2 xx3 xx4, xx1 ∈ X1 → xx2 ∈ X2 → xx3 ∈ X3 → xx4 ∈ X4 →
      x = XTUPLE_0.quadruple xx1 xx2 xx3 xx4 → y2 = xx2) :
    y2 = XTUPLE_0.snd4 x :=
  let ⟨xx1, xx2, xx3, xx4, hx1, hx2, hx3, hx4, heq⟩ := lm3 h1 h2 h3 h4 hx
  (hy xx1 xx2 xx3 xx4 hx1 hx2 hx3 hx4 heq).trans
    (def9 h1 h2 h3 h4 hx heq).symm

/-- Unlabeled `MCART_1` (`L1162`). -/
theorem th77 {X1 X2 X3 X4 x y3 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product4 X1 X2 X3 X4)
    (hy : ∀ xx1 xx2 xx3 xx4, xx1 ∈ X1 → xx2 ∈ X2 → xx3 ∈ X3 → xx4 ∈ X4 →
      x = XTUPLE_0.quadruple xx1 xx2 xx3 xx4 → y3 = xx3) :
    y3 = XTUPLE_0.thd4 x :=
  let ⟨xx1, xx2, xx3, xx4, hx1, hx2, hx3, hx4, heq⟩ := lm3 h1 h2 h3 h4 hx
  (hy xx1 xx2 xx3 xx4 hx1 hx2 hx3 hx4 heq).trans
    (def10 h1 h2 h3 h4 hx heq).symm

/-- Unlabeled `MCART_1` (`L1183`). -/
theorem th78 {X1 X2 X3 X4 x y4 : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product4 X1 X2 X3 X4)
    (hy : ∀ xx1 xx2 xx3 xx4, xx1 ∈ X1 → xx2 ∈ X2 → xx3 ∈ X3 → xx4 ∈ X4 →
      x = XTUPLE_0.quadruple xx1 xx2 xx3 xx4 → y4 = xx4) :
    y4 = XTUPLE_0.fth4 x :=
  let ⟨xx1, xx2, xx3, xx4, hx1, hx2, hx3, hx4, heq⟩ := lm3 h1 h2 h3 h4 hx
  (hy xx1 xx2 xx3 xx4 hx1 hx2 hx3 hx4 heq).trans
    (def11 h1 h2 h3 h4 hx heq).symm

/-- Unlabeled `MCART_1` (`L1204`). -/
theorem th79 {z X1 X2 X3 X4 : TarskiSet.{u}}
    (hz : z ∈ ZFMISC_1.product4 X1 X2 X3 X4) :
    ∃ x1 x2 x3 x4, x1 ∈ X1 ∧ x2 ∈ X2 ∧ x3 ∈ X3 ∧ x4 ∈ X4 ∧
      z = XTUPLE_0.quadruple x1 x2 x3 x4 := by
  obtain ⟨x123, x4, hx123, hx4, heq⟩ :=
    (ZFMISC_1.def2 (ZFMISC_1.product3 X1 X2 X3) X4 z).mp hz
  obtain ⟨x1, x2, x3, hx1, hx2, hx3, heq123⟩ := th68 hx123
  exact ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4,
    heq.trans (congrArg (fun s => TARSKI.pair s x4) heq123)⟩

/-- Unlabeled `MCART_1` (`L1221`). -/
theorem th80 (x1 x2 x3 x4 X1 X2 X3 X4 : TarskiSet.{u}) :
    XTUPLE_0.quadruple x1 x2 x3 x4 ∈ ZFMISC_1.product4 X1 X2 X3 X4 ↔
      x1 ∈ X1 ∧ x2 ∈ X2 ∧ x3 ∈ X3 ∧ x4 ∈ X4 := by
  have h3 : XTUPLE_0.triple x1 x2 x3 ∈ ZFMISC_1.product3 X1 X2 X3 ↔
      x1 ∈ X1 ∧ x2 ∈ X2 ∧ x3 ∈ X3 :=
    th69 x1 x2 x3 X1 X2 X3
  have h4 : TARSKI.pair (XTUPLE_0.triple x1 x2 x3) x4 ∈
      ZFMISC_1.product (ZFMISC_1.product3 X1 X2 X3) X4 ↔
      XTUPLE_0.triple x1 x2 x3 ∈ ZFMISC_1.product3 X1 X2 X3 ∧ x4 ∈ X4 :=
    ZFMISC_1.th87 (x := XTUPLE_0.triple x1 x2 x3) (y := x4)
      (X := ZFMISC_1.product3 X1 X2 X3) (Y := X4)
  constructor
  · intro hz
    have ⟨hp, hx4⟩ := h4.mp hz
    have ⟨hx1, hx2, hx3⟩ := h3.mp hp
    exact ⟨hx1, hx2, hx3, hx4⟩
  · intro ⟨hx1, hx2, hx3, hx4⟩
    exact h4.mpr ⟨h3.mpr ⟨hx1, hx2, hx3⟩, hx4⟩

/-- Unlabeled `MCART_1` (`L1231`). -/
theorem th81 {Z X1 X2 X3 X4 : TarskiSet.{u}}
    (h : ∀ z, z ∈ Z ↔ ∃ x1 x2 x3 x4, x1 ∈ X1 ∧ x2 ∈ X2 ∧ x3 ∈ X3 ∧
      x4 ∈ X4 ∧ z = XTUPLE_0.quadruple x1 x2 x3 x4) :
    Z = ZFMISC_1.product4 X1 X2 X3 X4 := by
  apply TARSKI.extensionality
  intro z
  constructor
  · intro hz
    obtain ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, heq⟩ := (h z).mp hz
    exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product4 X1 X2 X3 X4)
      heq.symm ((th80 x1 x2 x3 x4 X1 X2 X3 X4).mpr ⟨hx1, hx2, hx3, hx4⟩)
  · intro hz
    obtain ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, heq⟩ := th79 hz
    exact (h z).mpr ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, heq⟩

/-- Unlabeled `MCART_1` (`L1266`). `MCART_1:82` is canceled. -/
theorem th83 {X1 X2 X3 X4 A1 A2 A3 A4 x : TarskiSet.{u}}
    (h1 : X1 ≠ (∅ : TarskiSet.{u})) (h2 : X2 ≠ (∅ : TarskiSet.{u}))
    (h3 : X3 ≠ (∅ : TarskiSet.{u})) (h4 : X4 ≠ (∅ : TarskiSet.{u}))
    (_hA1 : A1 ≠ (∅ : TarskiSet.{u})) (_hA2 : A2 ≠ (∅ : TarskiSet.{u}))
    (_hA3 : A3 ≠ (∅ : TarskiSet.{u})) (_hA4 : A4 ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ ZFMISC_1.product4 X1 X2 X3 X4)
    (hin : x ∈ ZFMISC_1.product4 A1 A2 A3 A4) :
    XTUPLE_0.fst4 x ∈ A1 ∧ XTUPLE_0.snd4 x ∈ A2 ∧
      XTUPLE_0.thd4 x ∈ A3 ∧ XTUPLE_0.fth4 x ∈ A4 := by
  obtain ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, heq⟩ := th79 hin
  exact ⟨
    Eq.subst (motive := fun s => s ∈ A1) (def8 h1 h2 h3 h4 hx heq).symm hx1,
    Eq.subst (motive := fun s => s ∈ A2) (def9 h1 h2 h3 h4 hx heq).symm hx2,
    Eq.subst (motive := fun s => s ∈ A3) (def10 h1 h2 h3 h4 hx heq).symm hx3,
    Eq.subst (motive := fun s => s ∈ A4) (def11 h1 h2 h3 h4 hx heq).symm hx4⟩

/-- `MCART_1:84` (`Th84`) -/
theorem th84 {X1 X2 X3 X4 Y1 Y2 Y3 Y4 : TarskiSet.{u}}
    (h1 : X1 ⊆ Y1) (h2 : X2 ⊆ Y2) (h3 : X3 ⊆ Y3) (h4 : X4 ⊆ Y4) :
    ZFMISC_1.product4 X1 X2 X3 X4 ⊆ ZFMISC_1.product4 Y1 Y2 Y3 Y4 :=
  ZFMISC_1.th96 (X1 := ZFMISC_1.product3 X1 X2 X3) (X2 := X4)
    (Y1 := ZFMISC_1.product3 Y1 Y2 Y3) (Y2 := Y4) (th73 h1 h2 h3) h4

theorem product_subset {X1 X2 A1 A2 : TarskiSet.{u}}
    (h1 : A1 ⊆ X1) (h2 : A2 ⊆ X2) :
    ZFMISC_1.product A1 A2 ⊆ ZFMISC_1.product X1 X2 :=
  ZFMISC_1.th96 h1 h2

/-- Mizar `pr1 f`. -/
noncomputable def pr1 (f : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (FUNCT_1.sch_Lambda (RELAT_1.dom f)
      (fun x => XTUPLE_0.fst (FUNCT_1.apply f x)))

theorem pr1_spec (f : TarskiSet.{u}) :
    FUNCT_1.isFunction (pr1 f) ∧ RELAT_1.dom (pr1 f) = RELAT_1.dom f ∧
      ∀ x, x ∈ RELAT_1.dom f →
        FUNCT_1.apply (pr1 f) x = XTUPLE_0.fst (FUNCT_1.apply f x) :=
  Classical.choose_spec
    (FUNCT_1.sch_Lambda (RELAT_1.dom f)
      (fun x => XTUPLE_0.fst (FUNCT_1.apply f x)))

/-- Mizar `pr2 f`. -/
noncomputable def pr2 (f : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (FUNCT_1.sch_Lambda (RELAT_1.dom f)
      (fun x => XTUPLE_0.snd (FUNCT_1.apply f x)))

theorem pr2_spec (f : TarskiSet.{u}) :
    FUNCT_1.isFunction (pr2 f) ∧ RELAT_1.dom (pr2 f) = RELAT_1.dom f ∧
      ∀ x, x ∈ RELAT_1.dom f →
        FUNCT_1.apply (pr2 f) x = XTUPLE_0.snd (FUNCT_1.apply f x) :=
  Classical.choose_spec
    (FUNCT_1.sch_Lambda (RELAT_1.dom f)
      (fun x => XTUPLE_0.snd (FUNCT_1.apply f x)))

noncomputable def fst11 (x : TarskiSet.{u}) : TarskiSet.{u} :=
  XTUPLE_0.fst (XTUPLE_0.fst x)
noncomputable def fst12 (x : TarskiSet.{u}) : TarskiSet.{u} :=
  XTUPLE_0.snd (XTUPLE_0.fst x)
noncomputable def snd21 (x : TarskiSet.{u}) : TarskiSet.{u} :=
  XTUPLE_0.fst (XTUPLE_0.snd x)
noncomputable def snd22 (x : TarskiSet.{u}) : TarskiSet.{u} :=
  XTUPLE_0.snd (XTUPLE_0.snd x)

/-- Unlabeled `MCART_1` (`L1396`). -/
theorem th85 (x1 x2 y y1 y2 x : TarskiSet.{u}) :
    fst11 (TARSKI.pair (TARSKI.pair x1 x2) y) = x1 ∧
      fst12 (TARSKI.pair (TARSKI.pair x1 x2) y) = x2 ∧
      snd21 (TARSKI.pair x (TARSKI.pair y1 y2)) = y1 ∧
      snd22 (TARSKI.pair x (TARSKI.pair y1 y2)) = y2 := by
  have hfst : XTUPLE_0.fst (TARSKI.pair (TARSKI.pair x1 x2) y) =
      TARSKI.pair x1 x2 :=
    XTUPLE_0.fst_pair (TARSKI.pair x1 x2) y
  have hsnd : XTUPLE_0.snd (TARSKI.pair x (TARSKI.pair y1 y2)) =
      TARSKI.pair y1 y2 :=
    XTUPLE_0.snd_pair x (TARSKI.pair y1 y2)
  exact ⟨
    Eq.subst (motive := fun s => XTUPLE_0.fst s = x1) hfst.symm
      (XTUPLE_0.fst_pair x1 x2),
    Eq.subst (motive := fun s => XTUPLE_0.snd s = x2) hfst.symm
      (XTUPLE_0.snd_pair x1 x2),
    Eq.subst (motive := fun s => XTUPLE_0.fst s = y1) hsnd.symm
      (XTUPLE_0.fst_pair y1 y2),
    Eq.subst (motive := fun s => XTUPLE_0.snd s = y2) hsnd.symm
      (XTUPLE_0.snd_pair y1 y2)⟩

/-- Unlabeled `MCART_1` (`L1402`). -/
theorem th86 {x R : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hx : x ∈ R) :
    XTUPLE_0.fst x ∈ RELAT_1.dom R ∧ XTUPLE_0.snd x ∈ RELAT_1.rng R := by
  have heq : x = TARSKI.pair (XTUPLE_0.fst x) (XTUPLE_0.snd x) := th21 hR hx
  have hp : TARSKI.pair (XTUPLE_0.fst x) (XTUPLE_0.snd x) ∈ R :=
    Eq.subst (motive := fun s => s ∈ R) heq hx
  exact ⟨RELAT_1.pair_mem_dom hp, RELAT_1.pair_mem_rng hp⟩

/-- `MCART_1:87` (`Th87`) -/
theorem th87 {R x z : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (_hne : R ≠ (∅ : TarskiSet.{u})) :
    z ∈ RELAT_1.Im R x ↔
      ∃ I, I ∈ R ∧ XTUPLE_0.snd I = z ∧ XTUPLE_0.fst I = x := by
  constructor
  · intro hz
    obtain ⟨y, hp, hy⟩ := (RELAT_1.def13 R (TARSKI.singleton x) z).mp hz
    have hyx : y = x := (singleton_iff x y).mp hy
    have hp' : TARSKI.pair x z ∈ R :=
      Eq.subst (motive := fun s => TARSKI.pair s z ∈ R) hyx hp
    exact ⟨TARSKI.pair x z, hp', XTUPLE_0.snd_pair x z, XTUPLE_0.fst_pair x z⟩
  · intro ⟨I, hI, hs, hf⟩
    have heq : I = TARSKI.pair (XTUPLE_0.fst I) (XTUPLE_0.snd I) :=
      th21 hR hI
    have hfst : TARSKI.pair (XTUPLE_0.fst I) (XTUPLE_0.snd I) =
        TARSKI.pair x (XTUPLE_0.snd I) :=
      Eq.subst (motive := fun s =>
          TARSKI.pair (XTUPLE_0.fst I) (XTUPLE_0.snd I) =
            TARSKI.pair s (XTUPLE_0.snd I)) hf rfl
    have hsnd : TARSKI.pair x (XTUPLE_0.snd I) = TARSKI.pair x z :=
      Eq.subst (motive := fun s =>
          TARSKI.pair x (XTUPLE_0.snd I) = TARSKI.pair x s) hs rfl
    have hpair : I = TARSKI.pair x z := heq.trans (hfst.trans hsnd)
    have hp : TARSKI.pair x z ∈ R :=
      Eq.subst (motive := fun s => s ∈ R) hpair hI
    exact (RELAT_1.def13 R (TARSKI.singleton x) z).mpr
      ⟨x, hp, (singleton_iff x x).mpr rfl⟩

/-- Unlabeled `MCART_1` (`L1438`). -/
theorem th88 {x R : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hx : x ∈ R) :
    XTUPLE_0.snd x ∈ RELAT_1.Im R (XTUPLE_0.fst x) :=
  (RELAT_1.def13 R (TARSKI.singleton (XTUPLE_0.fst x)) (XTUPLE_0.snd x)).mpr
    ⟨XTUPLE_0.fst x,
      Eq.subst (motive := fun s => s ∈ R) (th21 hR hx) hx,
      (singleton_iff (XTUPLE_0.fst x) (XTUPLE_0.fst x)).mpr rfl⟩

/-- `MCART_1:89` (`Th89`) -/
theorem th89 {x y R : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hx : x ∈ R) (hy : y ∈ R)
    (h1 : XTUPLE_0.fst x = XTUPLE_0.fst y)
    (h2 : XTUPLE_0.snd x = XTUPLE_0.snd y) : x = y := by
  have hxeq : x = TARSKI.pair (XTUPLE_0.fst x) (XTUPLE_0.snd x) :=
    th21 hR hx
  have hyeq : y = TARSKI.pair (XTUPLE_0.fst y) (XTUPLE_0.snd y) :=
    th21 hR hy
  have hfst : TARSKI.pair (XTUPLE_0.fst x) (XTUPLE_0.snd x) =
      TARSKI.pair (XTUPLE_0.fst y) (XTUPLE_0.snd x) :=
    Eq.subst (motive := fun s =>
        TARSKI.pair (XTUPLE_0.fst x) (XTUPLE_0.snd x) =
          TARSKI.pair s (XTUPLE_0.snd x)) h1 rfl
  have hsnd : TARSKI.pair (XTUPLE_0.fst y) (XTUPLE_0.snd x) =
      TARSKI.pair (XTUPLE_0.fst y) (XTUPLE_0.snd y) :=
    Eq.subst (motive := fun s =>
        TARSKI.pair (XTUPLE_0.fst y) (XTUPLE_0.snd x) =
          TARSKI.pair (XTUPLE_0.fst y) s) h2 rfl
  exact hxeq.trans (hfst.trans (hsnd.trans hyeq.symm))

/-- Unlabeled `MCART_1` (`L1454`). -/
theorem th90 {R x y : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (_hne : R ≠ (∅ : TarskiSet.{u})) (hx : x ∈ R) (hy : y ∈ R)
    (h1 : XTUPLE_0.fst x = XTUPLE_0.fst y)
    (h2 : XTUPLE_0.snd x = XTUPLE_0.snd y) : x = y :=
  th89 hR hx hy h1 h2

/-- Unlabeled `MCART_1` (`L1461`). -/
theorem th91 (x1 x2 x3 y1 y2 y3 : TarskiSet.{u}) :
    XTUPLE_0.proj1 (XTUPLE_0.proj1
      (TARSKI.upair (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple y1 y2 y3))) =
      TARSKI.upair x1 y1 := by
  have h1 : XTUPLE_0.proj1
      (TARSKI.upair (XTUPLE_0.triple x1 x2 x3) (XTUPLE_0.triple y1 y2 y3)) =
      TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair y1 y2) :=
    (RELAT_1.th10 (R := TARSKI.upair (XTUPLE_0.triple x1 x2 x3)
      (XTUPLE_0.triple y1 y2 y3)) (a := TARSKI.pair x1 x2) (b := x3)
      (x := TARSKI.pair y1 y2) (y := y3) rfl).1
  have h2 : XTUPLE_0.proj1
      (TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair y1 y2)) =
      TARSKI.upair x1 y1 :=
    (RELAT_1.th10 (R := TARSKI.upair (TARSKI.pair x1 x2) (TARSKI.pair y1 y2))
      (a := x1) (b := x2) (x := y1) (y := y2) rfl).1
  exact Eq.subst (motive := fun s => XTUPLE_0.proj1 s = TARSKI.upair x1 y1)
    h1.symm h2

/-- Unlabeled `MCART_1` (`L1469`). -/
theorem th92 (x1 x2 x3 : TarskiSet.{u}) :
    XTUPLE_0.proj1 (XTUPLE_0.proj1
      (TARSKI.singleton (XTUPLE_0.triple x1 x2 x3))) =
      TARSKI.singleton x1 := by
  have h1 : XTUPLE_0.proj1 (TARSKI.singleton (XTUPLE_0.triple x1 x2 x3)) =
      TARSKI.singleton (TARSKI.pair x1 x2) :=
    (RELAT_1.th9 (R := TARSKI.singleton (XTUPLE_0.triple x1 x2 x3))
      (x := TARSKI.pair x1 x2) (y := x3) rfl).1
  have h2 : XTUPLE_0.proj1 (TARSKI.singleton (TARSKI.pair x1 x2)) =
      TARSKI.singleton x1 :=
    (RELAT_1.th9 (R := TARSKI.singleton (TARSKI.pair x1 x2))
      (x := x1) (y := x2) rfl).1
  exact Eq.subst (motive := fun s => XTUPLE_0.proj1 s = TARSKI.singleton x1)
    h1.symm h2

/-- `MCART_1:sch BiFuncEx` -/
theorem sch_BiFuncEx (A B C : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hP : ∀ x, x ∈ A → ∃ y z, y ∈ B ∧ z ∈ C ∧ P x y z) :
    ∃ f g, FUNCT_1.isFunction f ∧ FUNCT_1.isFunction g ∧
      RELAT_1.dom f = A ∧ RELAT_1.dom g = A ∧
      ∀ x, x ∈ A → P x (FUNCT_1.apply f x) (FUNCT_1.apply g x) := by
  have hP2 : ∀ x, x ∈ A → ∃ p, p ∈ ZFMISC_1.product B C ∧
      P x (XTUPLE_0.fst p) (XTUPLE_0.snd p) := by
    intro x hx
    obtain ⟨y, z, hy, hz, hPx⟩ := hP x hx
    refine ⟨TARSKI.pair y z,
      (ZFMISC_1.th87 (x := y) (y := z) (X := B) (Y := C)).mpr ⟨hy, hz⟩, ?_⟩
    have hfst : XTUPLE_0.fst (TARSKI.pair y z) = y := XTUPLE_0.fst_pair y z
    have hsnd : XTUPLE_0.snd (TARSKI.pair y z) = z := XTUPLE_0.snd_pair y z
    have hPz : P x y (XTUPLE_0.snd (TARSKI.pair y z)) :=
      Eq.subst (motive := fun s => P x y s) hsnd.symm hPx
    exact Eq.subst (motive := fun s =>
        P x s (XTUPLE_0.snd (TARSKI.pair y z))) hfst.symm hPz
  obtain ⟨h, hh, hd, _, hv⟩ :=
    FUNCT_1.sch_NonUniqBoundFuncEx A (ZFMISC_1.product B C)
      (fun x p => P x (XTUPLE_0.fst p) (XTUPLE_0.snd p)) hP2
  obtain ⟨f, hf, hdf, hvf⟩ :=
    FUNCT_1.sch_Lambda A (fun x => XTUPLE_0.fst (FUNCT_1.apply h x))
  obtain ⟨g, hg, hdg, hvg⟩ :=
    FUNCT_1.sch_Lambda A (fun x => XTUPLE_0.snd (FUNCT_1.apply h x))
  refine ⟨f, g, hf, hg, hdf, hdg, fun x hx => ?_⟩
  have hPx : P x (XTUPLE_0.fst (FUNCT_1.apply h x))
      (XTUPLE_0.snd (FUNCT_1.apply h x)) :=
    hv x hx
  have hfval : FUNCT_1.apply f x = XTUPLE_0.fst (FUNCT_1.apply h x) :=
    hvf x hx
  have hgval : FUNCT_1.apply g x = XTUPLE_0.snd (FUNCT_1.apply h x) :=
    hvg x hx
  have hP2 : P x (FUNCT_1.apply f x) (XTUPLE_0.snd (FUNCT_1.apply h x)) :=
    Eq.subst (motive := fun s =>
        P x s (XTUPLE_0.snd (FUNCT_1.apply h x))) hfval.symm hPx
  exact Eq.subst (motive := fun s => P x (FUNCT_1.apply f x) s)
    hgval.symm hP2

end MCART_1


