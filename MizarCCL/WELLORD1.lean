import MizarCCL.FUNCT_1
import MizarCCL.RELAT_2

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/wellord1.miz`.
Authors: Grzegorz Bancerek (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# The Well Ordering Relations

1–1 Lean rendering of Mizar article `WELLORD1`
(`vendor/mml/wellord1.miz`). Import is `FUNCT_1` and `RELAT_2`.
-/

universe u

open TarskiSet TARSKI

namespace WELLORD1

/-- `WELLORD1:lm 1` -/
theorem lm1 (R : TarskiSet.{u}) :
    RELAT_2.isReflexive R ↔
      ∀ x, x ∈ RELAT_1.field R → TARSKI.pair x x ∈ R :=
  Iff.trans (RELAT_2.def9 R) (RELAT_2.def1 R (RELAT_1.field R))

/-- `WELLORD1:lm 2` -/
theorem lm2 (R : TarskiSet.{u}) :
    RELAT_2.isTransitive R ↔
      ∀ x y z, TARSKI.pair x y ∈ R → TARSKI.pair y z ∈ R →
        TARSKI.pair x z ∈ R := by
  constructor
  · intro hT x y z hxy hyz
    have hf := (RELAT_2.def16 R).mp hT
    have hz : z ∈ RELAT_1.field R := (RELAT_1.th15 hyz).2
    have hx : x ∈ RELAT_1.field R := (RELAT_1.th15 hxy).1
    have hy : y ∈ RELAT_1.field R := (RELAT_1.th15 hxy).2
    exact (RELAT_2.def8 R (RELAT_1.field R)).mp hf x y z hx hy hz hxy hyz
  · intro h
    exact (RELAT_2.def16 R).mpr
      ((RELAT_2.def8 R (RELAT_1.field R)).mpr
        fun x y z _ _ _ hxy hyz => h x y z hxy hyz)

/-- `WELLORD1:lm 3` -/
theorem lm3 (R : TarskiSet.{u}) :
    RELAT_2.isAntisymmetric R ↔
      ∀ x y, TARSKI.pair x y ∈ R → TARSKI.pair y x ∈ R → x = y := by
  constructor
  · intro hA x y hxy hyx
    have hf := (RELAT_2.def12 R).mp hA
    have hx : x ∈ RELAT_1.field R := (RELAT_1.th15 hxy).1
    have hy : y ∈ RELAT_1.field R := (RELAT_1.th15 hxy).2
    exact (RELAT_2.def4 R (RELAT_1.field R)).mp hf x y hx hy hxy hyx
  · intro h
    exact (RELAT_2.def12 R).mpr
      ((RELAT_2.def4 R (RELAT_1.field R)).mpr
        fun x y _ _ hxy hyx => h x y hxy hyx)

/-- `WELLORD1:lm 4` -/
theorem lm4 (R : TarskiSet.{u}) :
    RELAT_2.isConnected R ↔
      ∀ x y, x ∈ RELAT_1.field R → y ∈ RELAT_1.field R → x ≠ y →
        TARSKI.pair x y ∈ R ∨ TARSKI.pair y x ∈ R :=
  Iff.trans (RELAT_2.def14 R) (RELAT_2.def6 R (RELAT_1.field R))

/-- Initial segment `R-Seg(a) = Coim(R,a) \ {a}`. -/
noncomputable def seg (R a : TarskiSet.{u}) : TarskiSet.{u} :=
  RELAT_1.Coim R a \ TARSKI.singleton a

/-- `WELLORD1:1` (`Th1`) -/
theorem th1 (R a x : TarskiSet.{u}) :
    x ∈ seg R a ↔ x ≠ a ∧ TARSKI.pair x a ∈ R := by
  constructor
  · intro hx
    have ⟨hCoim, hns⟩ :=
      (ZFMISC_1.th56 (X := RELAT_1.Coim R a) (x := a) (z := x)).mp hx
    have ⟨y, hp, hy⟩ := (RELAT_1.def14 R (TARSKI.singleton a) x).mp hCoim
    exact ⟨(ZFMISC_1.th56 (X := RELAT_1.Coim R a) (x := a) (z := x)).mp hx
      |>.2, (singleton_iff a y).mp hy ▸ hp⟩
  · intro ⟨hne, hp⟩
    exact (ZFMISC_1.th56 (X := RELAT_1.Coim R a) (x := a) (z := x)).mpr
      ⟨(RELAT_1.def14 R (TARSKI.singleton a) x).mpr
        ⟨a, hp, (singleton_iff a a).mpr rfl⟩, hne⟩

/-- `WELLORD1:2` (`Th2`) -/
theorem th2 (R x : TarskiSet.{u}) :
    x ∈ RELAT_1.field R ∨ seg R x = (∅ : TarskiSet.{u}) :=
  Or.elim (Classical.em (x ∈ RELAT_1.field R)) Or.inl fun hnf =>
    Or.inr (Classical.byContradiction fun hne =>
      (XBOOLE_0.th7 hne).elim fun y hy =>
        hnf (RELAT_1.th15 ((th1 R x y).mp hy).2).2)

/-- `WELLORD1:def 2` -/
def isWellFounded (R : TarskiSet.{u}) : Prop :=
  ∀ Y, Y ⊆ RELAT_1.field R → Y ≠ (∅ : TarskiSet.{u}) →
    ∃ a, a ∈ Y ∧ XBOOLE_0.misses (seg R a) Y

theorem def2 (R : TarskiSet.{u}) :
    isWellFounded R ↔
      ∀ Y, Y ⊆ RELAT_1.field R → Y ≠ (∅ : TarskiSet.{u}) →
        ∃ a, a ∈ Y ∧ XBOOLE_0.misses (seg R a) Y :=
  Iff.rfl

/-- `WELLORD1:def 3` -/
def isWellFoundedIn (R X : TarskiSet.{u}) : Prop :=
  ∀ Y, Y ⊆ X → Y ≠ (∅ : TarskiSet.{u}) →
    ∃ a, a ∈ Y ∧ XBOOLE_0.misses (seg R a) Y

theorem def3 (R X : TarskiSet.{u}) :
    isWellFoundedIn R X ↔
      ∀ Y, Y ⊆ X → Y ≠ (∅ : TarskiSet.{u}) →
        ∃ a, a ∈ Y ∧ XBOOLE_0.misses (seg R a) Y :=
  Iff.rfl

/-- `WELLORD1:3` (`Th3`) -/
theorem th3 (R : TarskiSet.{u}) :
    isWellFounded R ↔ isWellFoundedIn R (RELAT_1.field R) :=
  Iff.rfl

/-- `WELLORD1:def 4` -/
def isWellOrdering (R : TarskiSet.{u}) : Prop :=
  RELAT_2.isReflexive R ∧ RELAT_2.isTransitive R ∧
    RELAT_2.isAntisymmetric R ∧ RELAT_2.isConnected R ∧ isWellFounded R

theorem def4 (R : TarskiSet.{u}) :
    isWellOrdering R ↔
      RELAT_2.isReflexive R ∧ RELAT_2.isTransitive R ∧
        RELAT_2.isAntisymmetric R ∧ RELAT_2.isConnected R ∧
          isWellFounded R :=
  Iff.rfl

/-- `WELLORD1:def 5` -/
def wellOrders (R X : TarskiSet.{u}) : Prop :=
  RELAT_2.isReflexiveIn R X ∧ RELAT_2.isTransitiveIn R X ∧
    RELAT_2.isAntisymmetricIn R X ∧ RELAT_2.isConnectedIn R X ∧
      isWellFoundedIn R X

theorem def5 (R X : TarskiSet.{u}) :
    wellOrders R X ↔
      RELAT_2.isReflexiveIn R X ∧ RELAT_2.isTransitiveIn R X ∧
        RELAT_2.isAntisymmetricIn R X ∧ RELAT_2.isConnectedIn R X ∧
          isWellFoundedIn R X :=
  Iff.rfl

/-- Unlabeled `WELLORD1` after `Def5` (`L174`). -/
theorem th4 (R : TarskiSet.{u}) :
    wellOrders R (RELAT_1.field R) ↔ isWellOrdering R := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, (th3 R).mpr h.2.2.2.2⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, (th3 R).mp h.2.2.2.2⟩

private theorem misses_not_mem {A B x : TarskiSet.{u}}
    (h : XBOOLE_0.misses A B) (hx : x ∈ B) : x ∉ A :=
  fun ha =>
    (XBOOLE_0.empty_iff x).mp
      (Eq.subst (motive := fun s => x ∈ s) h
        ((XBOOLE_0.def4 A B x).mpr ⟨ha, hx⟩))

/-- Unlabeled `WELLORD1` (`L192`). -/
theorem th5 {R X : TarskiSet.{u}} (h : wellOrders R X)
    {Y : TarskiSet.{u}} (hY : Y ⊆ X) (hne : Y ≠ (∅ : TarskiSet.{u})) :
    ∃ a, a ∈ Y ∧ ∀ b, b ∈ Y → TARSKI.pair a b ∈ R := by
  obtain ⟨a, ha, hmiss⟩ := h.2.2.2.2 Y hY hne
  refine ⟨a, ha, ?_⟩
  intro b hb
  have hnseg : b ∉ seg R a := misses_not_mem hmiss hb
  have hcases : a = b ∨ TARSKI.pair b a ∉ R :=
    Classical.or_iff_not_imp_left.mpr fun hne' hp =>
      hnseg ((th1 R a b).mpr ⟨fun (heq : b = a) => hne' heq.symm, hp⟩)
  exact Or.elim hcases
    (fun heq =>
      Eq.subst (motive := fun s => TARSKI.pair a s ∈ R) heq
        (h.1 a (hY a ha)))
    (fun hnba =>
      Or.elim (h.2.2.2.1 a b (hY a ha) (hY b hb)
          (fun heq => hnba (heq ▸ h.1 a (hY a ha))))
        (fun hab => hab)
        (fun hba => (hnba hba).elim))

/-- `WELLORD1:6` (`Th6`) -/
theorem th6 {R : TarskiSet.{u}} (h : isWellOrdering R)
    {Y : TarskiSet.{u}} (hY : Y ⊆ RELAT_1.field R)
    (hne : Y ≠ (∅ : TarskiSet.{u})) :
    ∃ a, a ∈ Y ∧ ∀ b, b ∈ Y → TARSKI.pair a b ∈ R :=
  th5 ((th4 R).mpr h) hY hne

/-- Unlabeled `WELLORD1` (`L244`). -/
theorem th7 {R : TarskiSet.{u}} (h : isWellOrdering R)
    (hne : RELAT_1.field R ≠ (∅ : TarskiSet.{u})) :
    ∃ a, a ∈ RELAT_1.field R ∧
      ∀ b, b ∈ RELAT_1.field R → TARSKI.pair a b ∈ R :=
  th6 h (fun _ hx => hx) hne

/-- Unlabeled `WELLORD1` (`L248`). -/
theorem th8 {R : TarskiSet.{u}} (h : isWellOrdering R)
    {a : TarskiSet.{u}} (ha : a ∈ RELAT_1.field R) :
    (∀ b, b ∈ RELAT_1.field R → TARSKI.pair b a ∈ R) ∨
      ∃ b, b ∈ RELAT_1.field R ∧ TARSKI.pair a b ∈ R ∧
        ∀ c, c ∈ RELAT_1.field R → TARSKI.pair a c ∈ R →
          c = a ∨ TARSKI.pair b c ∈ R := by
  apply Classical.or_iff_not_imp_left.mpr
  intro hn
  have hex : ∃ b, b ∈ RELAT_1.field R ∧ TARSKI.pair b a ∉ R :=
    Classical.byContradiction fun hne =>
      hn fun b hb =>
        Classical.not_not.mp (fun hnba => hne ⟨b, hb, hnba⟩)
  obtain ⟨b0, hb0, hnba0⟩ := hex
  obtain ⟨Z, hZ⟩ :=
    XBOOLE_0.sch_separation (RELAT_1.field R)
      (fun c => TARSKI.pair c a ∉ R)
  have hZsub : Z ⊆ RELAT_1.field R := fun c hc => ((hZ c).mp hc).1
  have hZne : Z ≠ (∅ : TarskiSet.{u}) := fun hempty =>
    (XBOOLE_0.empty_iff b0).mp
      (Eq.subst (motive := fun s => b0 ∈ s) hempty
        ((hZ b0).mpr ⟨hb0, hnba0⟩))
  obtain ⟨d, hdZ, hleast⟩ := th6 h hZsub hZne
  have hd : d ∈ RELAT_1.field R := ((hZ d).mp hdZ).1
  have hnda : TARSKI.pair d a ∉ R := ((hZ d).mp hdZ).2
  have hnead : a ≠ d := fun heq =>
    hnda (Eq.subst (motive := fun s => TARSKI.pair s a ∈ R) heq
      ((lm1 R).mp h.1 a ha))
  have had : TARSKI.pair a d ∈ R :=
    Or.elim ((lm4 R).mp h.2.2.2.1 a d ha hd hnead)
      (fun h => h)
      (fun hda => (hnda hda).elim)
  refine ⟨d, hd, had, ?_⟩
  intro c hc hac
  apply Classical.or_iff_not_imp_left.mpr
  intro hneca
  have hnca : TARSKI.pair c a ∉ R := fun hca =>
    hneca ((lm3 R).mp h.2.2.1 c a hca hac)
  have hcZ : c ∈ Z := (hZ c).mpr ⟨hc, hnca⟩
  exact hleast c hcZ

/-- `WELLORD1:9` (`Th9`) -/
theorem th9 (R a : TarskiSet.{u}) : seg R a ⊆ RELAT_1.field R :=
  fun b hb => (RELAT_1.th15 ((th1 R a b).mp hb).2).1

/-- `WELLORD1:def 6` — `R |_2 Y = R ∩ [:Y,Y:]`. -/
noncomputable def restrict2 (R Y : TarskiSet.{u}) : TarskiSet.{u} :=
  R ∩ ZFMISC_1.product Y Y

theorem restrict2_iff (R Y x y : TarskiSet.{u}) :
    TARSKI.pair x y ∈ restrict2 R Y ↔
      TARSKI.pair x y ∈ R ∧ x ∈ Y ∧ y ∈ Y :=
  Iff.trans (XBOOLE_0.def4 R (ZFMISC_1.product Y Y) (TARSKI.pair x y))
    (and_congr_right fun _ => ZFMISC_1.th87)

private theorem restrict2_isRelation (R Y : TarskiSet.{u}) :
    RELAT_1.isRelation (restrict2 R Y) :=
  RELAT_1.subset_isRelation (RELAT_1.product_isRelation Y Y)
    (fun z hz => ((XBOOLE_0.def4 R (ZFMISC_1.product Y Y) z).mp hz).2)

/-- `WELLORD1:10` (`Th10`) -/
theorem th10 (R X : TarskiSet.{u}) :
    restrict2 R X = RELAT_1.restrict (RELAT_1.restrictRng X R) X :=
  RELAT_1.rel_eq (restrict2_isRelation R X)
    (RELAT_1.restrict_isRelation _ _) fun x y =>
      (restrict2_iff R X x y).trans
        ⟨fun ⟨hp, hx, hy⟩ =>
          (RELAT_1.def11 (RELAT_1.restrictRng X R) X x y).mpr
            ⟨hx, (RELAT_1.def12 X R x y).mpr ⟨hy, hp⟩⟩,
          fun h =>
            let ⟨hx, hpY⟩ :=
              (RELAT_1.def11 (RELAT_1.restrictRng X R) X x y).mp h
            let ⟨hy, hp⟩ := (RELAT_1.def12 X R x y).mp hpY
            ⟨hp, hx, hy⟩⟩

/-- `WELLORD1:11` (`Th11`) -/
theorem th11 (R X : TarskiSet.{u}) :
    restrict2 R X = RELAT_1.restrictRng X (RELAT_1.restrict R X) :=
  (th10 R X).trans RELAT_1.th109

/-- `WELLORD1:lm 5` -/
theorem lm5 (X R : TarskiSet.{u}) :
    RELAT_1.dom (RELAT_1.restrictRng X R) ⊆ RELAT_1.dom R :=
  fun x hx =>
    let ⟨y, hp⟩ := (RELAT_1.dom_iff (RELAT_1.restrictRng X R) x).mp hx
    RELAT_1.pair_mem_dom ((RELAT_1.def12 X R x y).mp hp).2

/-- `WELLORD1:12` (`Th12`) -/
theorem th12 {R X x : TarskiSet.{u}}
    (hx : x ∈ RELAT_1.field (restrict2 R X)) :
    x ∈ RELAT_1.field R ∧ x ∈ X := by
  rcases (XBOOLE_0.def3 (RELAT_1.dom (restrict2 R X))
      (RELAT_1.rng (restrict2 R X)) x).mp hx with hd | hr
  · obtain ⟨y, hp⟩ := (RELAT_1.dom_iff (restrict2 R X) x).mp hd
    have ⟨hpR, hxX, _⟩ := (restrict2_iff R X x y).mp hp
    exact ⟨(RELAT_1.th15 hpR).1, hxX⟩
  · obtain ⟨y, hp⟩ := (RELAT_1.rng_iff (restrict2 R X) x).mp hr
    have ⟨hpR, _, hxX⟩ := (restrict2_iff R X y x).mp hp
    exact ⟨(RELAT_1.th15 hpR).2, hxX⟩

/-- `WELLORD1:13` (`Th13`) -/
theorem th13 (R X : TarskiSet.{u}) :
    RELAT_1.field (restrict2 R X) ⊆ RELAT_1.field R ∧
      RELAT_1.field (restrict2 R X) ⊆ X :=
  ⟨fun x hx => (th12 hx).1, fun x hx => (th12 hx).2⟩

/-- `WELLORD1:14` (`Th14`) -/
theorem th14 (R X a : TarskiSet.{u}) :
    seg (restrict2 R X) a ⊆ seg R a :=
  fun x hx =>
    let ⟨hne, hp⟩ := (th1 (restrict2 R X) a x).mp hx
    (th1 R a x).mpr ⟨hne, ((restrict2_iff R X x a).mp hp).1⟩

/-- `WELLORD1:15` (`Th15`) -/
theorem th15 {R : TarskiSet.{u}} (h : RELAT_2.isReflexive R)
    (X : TarskiSet.{u}) : RELAT_2.isReflexive (restrict2 R X) :=
  (lm1 (restrict2 R X)).mpr fun a ha =>
    let ⟨haR, haX⟩ := th12 ha
    (restrict2_iff R X a a).mpr ⟨(lm1 R).mp h a haR, haX, haX⟩

/-- `WELLORD1:16` (`Th16`) -/
theorem th16 {R : TarskiSet.{u}} (h : RELAT_2.isConnected R)
    (Y : TarskiSet.{u}) : RELAT_2.isConnected (restrict2 R Y) :=
  (lm4 (restrict2 R Y)).mpr fun a b ha hb hne =>
    let ⟨haR, haY⟩ := th12 ha
    let ⟨hbR, hbY⟩ := th12 hb
    Or.elim ((lm4 R).mp h a b haR hbR hne)
      (fun hab => Or.inl ((restrict2_iff R Y a b).mpr ⟨hab, haY, hbY⟩))
      (fun hba => Or.inr ((restrict2_iff R Y b a).mpr ⟨hba, hbY, haY⟩))

/-- `WELLORD1:17` (`Th17`) -/
theorem th17 {R : TarskiSet.{u}} (h : RELAT_2.isTransitive R)
    (Y : TarskiSet.{u}) : RELAT_2.isTransitive (restrict2 R Y) :=
  (lm2 (restrict2 R Y)).mpr fun a b c hab hbc =>
    let ⟨hpab, haY, hbY⟩ := (restrict2_iff R Y a b).mp hab
    let ⟨hpbc, _, hcY⟩ := (restrict2_iff R Y b c).mp hbc
    (restrict2_iff R Y a c).mpr
      ⟨(lm2 R).mp h a b c hpab hpbc, haY, hcY⟩

/-- `WELLORD1:18` (`Th18`) -/
theorem th18 {R : TarskiSet.{u}} (h : RELAT_2.isAntisymmetric R)
    (Y : TarskiSet.{u}) : RELAT_2.isAntisymmetric (restrict2 R Y) :=
  (lm3 (restrict2 R Y)).mpr fun x y hxy hyx =>
    (lm3 R).mp h x y ((restrict2_iff R Y x y).mp hxy).1
      ((restrict2_iff R Y y x).mp hyx).1

/-- `WELLORD1:19` (`Th19`) -/
theorem th19 (R X Y : TarskiSet.{u}) :
    restrict2 (restrict2 R X) Y = restrict2 R (X ∩ Y) :=
  RELAT_1.rel_eq (restrict2_isRelation _ _) (restrict2_isRelation _ _)
    fun x y =>
      (restrict2_iff (restrict2 R X) Y x y).trans <|
        Iff.trans
          ⟨fun ⟨hp, hyX, hyY⟩ =>
            let ⟨hpR, hxX, hyX0⟩ := (restrict2_iff R X x y).mp hp
            ⟨hpR, (XBOOLE_0.def4 X Y x).mpr ⟨hxX, hyX⟩,
              (XBOOLE_0.def4 X Y y).mpr ⟨hyX0, hyY⟩⟩,
            fun ⟨hpR, hxI, hyI⟩ =>
              let ⟨hxX, hxY⟩ := (XBOOLE_0.def4 X Y x).mp hxI
              let ⟨hyX, hyY⟩ := (XBOOLE_0.def4 X Y y).mp hyI
              ⟨(restrict2_iff R X x y).mpr ⟨hpR, hxX, hyX⟩, hxY, hyY⟩⟩
          (restrict2_iff R (X ∩ Y) x y).symm

/-- Unlabeled `WELLORD1` (`L470`). -/
theorem th20 (R X Y : TarskiSet.{u}) :
    restrict2 (restrict2 R X) Y = restrict2 (restrict2 R Y) X :=
  (th19 R X Y).trans <|
    Eq.subst (motive := fun s => restrict2 R s = restrict2 (restrict2 R Y) X)
      (XBOOLE_0.inter_comm X Y).symm (th19 R Y X).symm

/-- Unlabeled `WELLORD1` (`L477`). -/
theorem th21 (R Y : TarskiSet.{u}) :
    restrict2 (restrict2 R Y) Y = restrict2 R Y :=
  (th19 R Y Y).trans
    (Eq.subst (motive := fun s => restrict2 R s = restrict2 R Y)
      (XBOOLE_0.inter_idem Y).symm rfl)

/-- `WELLORD1:22` (`Th22`) -/
theorem th22 {Z Y : TarskiSet.{u}} (h : Z ⊆ Y) (R : TarskiSet.{u}) :
    restrict2 (restrict2 R Y) Z = restrict2 R Z := by
  have hIZ : Y ∩ Z = Z :=
    (XBOOLE_0.inter_comm Y Z).trans (XBOOLE_1.th28 (X := Z) (Y := Y) h)
  exact (th19 R Y Z).trans
    (Eq.subst (motive := fun s => restrict2 R s = restrict2 R Z) hIZ.symm rfl)

/-- `WELLORD1:23` (`Th23`) -/
theorem th23 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    restrict2 R (RELAT_1.field R) = R :=
  RELAT_1.rel_eq (restrict2_isRelation _ _) hR fun x y =>
    (restrict2_iff R (RELAT_1.field R) x y).trans
      ⟨And.left, fun hp =>
        let ⟨hx, hy⟩ := RELAT_1.th15 hp
        ⟨hp, hx, hy⟩⟩

/-- `WELLORD1:24` (`Th24`) -/
theorem th24 {R : TarskiSet.{u}} (h : isWellFounded R)
    (X : TarskiSet.{u}) : isWellFounded (restrict2 R X) := by
  intro Y hY hne
  have hYf : Y ⊆ RELAT_1.field R := XBOOLE_1.th1 hY (th13 R X).1
  obtain ⟨a, ha, hmiss⟩ := h Y hYf hne
  refine ⟨a, ha, ?_⟩
  apply Classical.byContradiction
  intro hnmiss
  have ⟨b, hbs, hbY⟩ :=
    (XBOOLE_0.th3 (seg (restrict2 R X) a) Y).mp hnmiss
  exact misses_not_mem hmiss hbY (th14 R X a b hbs)

/-- `WELLORD1:25` (`Th25`) -/
theorem th25 {R : TarskiSet.{u}} (h : isWellOrdering R)
    (Y : TarskiSet.{u}) : isWellOrdering (restrict2 R Y) :=
  ⟨th15 h.1 Y, th17 h.2.1 Y, th18 h.2.2.1 Y, th16 h.2.2.2.1 Y,
    th24 h.2.2.2.2 Y⟩

/-- `WELLORD1:26` (`Th26`) -/
theorem th26 {R : TarskiSet.{u}} (h : isWellOrdering R) (a b : TarskiSet.{u}) :
    XBOOLE_0.are_ccomparable (seg R a) (seg R b) := by
  have hempty :
      seg R a = (∅ : TarskiSet.{u}) ∨ seg R b = (∅ : TarskiSet.{u}) →
        XBOOLE_0.are_ccomparable (seg R a) (seg R b) :=
    fun o => Or.elim o
      (fun ha => Or.inl (Eq.subst (motive := fun s => s ⊆ seg R b) ha.symm
        XBOOLE_1.th2))
      (fun hb => Or.inr (Eq.subst (motive := fun s => s ⊆ seg R a) hb.symm
        XBOOLE_1.th2))
  refine Or.elim (th2 R a) (fun ha => ?_) (fun hae => hempty (Or.inl hae))
  refine Or.elim (th2 R b) (fun hb => ?_) (fun hbe => hempty (Or.inr hbe))
  exact Or.elim (Classical.em (a = b))
    (fun heq => Or.inl (Eq.subst (motive := fun s => seg R a ⊆ seg R s)
      heq (fun _ hx => hx)))
    (fun hne =>
      Or.elim ((lm4 R).mp h.2.2.2.1 a b ha hb hne)
        (fun hab => Or.inl fun c hc =>
          let ⟨hnc, hca⟩ := (th1 R a c).mp hc
          (th1 R b c).mpr ⟨fun heq =>
            hnc (heq.trans ((lm3 R).mp h.2.2.1 a b hab
              (Eq.subst (motive := fun s => TARSKI.pair s a ∈ R) heq hca)).symm),
            (lm2 R).mp h.2.1 c a b hca hab⟩)
        (fun hba => Or.inr fun c hc =>
          let ⟨hnc, hcb⟩ := (th1 R b c).mp hc
          (th1 R a c).mpr ⟨fun heq =>
            hnc (heq.trans ((lm3 R).mp h.2.2.1 b a hba
              (Eq.subst (motive := fun s => TARSKI.pair s b ∈ R) heq hcb)).symm),
            (lm2 R).mp h.2.1 c b a hcb hba⟩))

/-- `WELLORD1:27` (`Th27`) -/
theorem th27 {R : TarskiSet.{u}} (h : isWellOrdering R)
    {a b : TarskiSet.{u}} (hb : b ∈ seg R a) :
    seg (restrict2 R (seg R a)) b = seg R b := by
  apply (XBOOLE_0.def10 (X := seg (restrict2 R (seg R a)) b)
      (Y := seg R b)).mpr
  constructor
  · exact th14 R (seg R a) b
  · intro c hc
    have ⟨hnc, hcb⟩ := (th1 R b c).mp hc
    have ⟨hnb, hba⟩ := (th1 R a b).mp hb
    have hca : TARSKI.pair c a ∈ R := (lm2 R).mp h.2.1 c b a hcb hba
    have hncA : c ≠ a := fun heq =>
      hnc (heq.trans ((lm3 R).mp h.2.2.1 a b
        (Eq.subst (motive := fun s => TARSKI.pair s b ∈ R) heq hcb)
        hba))
    have hcA : c ∈ seg R a := (th1 R a c).mpr ⟨hncA, hca⟩
    exact (th1 (restrict2 R (seg R a)) b c).mpr
      ⟨hnc, (restrict2_iff R (seg R a) c b).mpr ⟨hcb, hcA, hb⟩⟩

/-- `WELLORD1:28` (`Th28`) -/
theorem th28 {R Y : TarskiSet.{u}} (h : isWellOrdering R)
    (hY : Y ⊆ RELAT_1.field R) :
    (Y = RELAT_1.field R ∨
        ∃ a, a ∈ RELAT_1.field R ∧ Y = seg R a) ↔
      ∀ a, a ∈ Y → ∀ b, TARSKI.pair b a ∈ R → b ∈ Y := by
  constructor
  · intro hcases a ha b hba
    exact Or.elim hcases
      (fun heq =>
        Eq.subst (motive := fun s => b ∈ s) heq.symm (RELAT_1.th15 hba).1)
      (fun ⟨c, _, hYseg⟩ => by
        have haS : a ∈ seg R c :=
          Eq.subst (motive := fun s => a ∈ s) hYseg ha
        have ⟨hne, hac⟩ := (th1 R c a).mp haS
        have hbc : TARSKI.pair b c ∈ R :=
          (lm2 R).mp h.2.1 b a c hba hac
        have hnb : b ≠ c := fun heq =>
          hne ((lm3 R).mp h.2.2.1 a c hac
            (Eq.subst (motive := fun s => TARSKI.pair s a ∈ R) heq hba))
        exact Eq.subst (motive := fun s => b ∈ s) hYseg.symm
          ((th1 R c b).mpr ⟨hnb, hbc⟩))
  · intro hcl
    apply Classical.or_iff_not_imp_left.mpr
    intro hne
    have hdiff : RELAT_1.field R \ Y ≠ (∅ : TarskiSet.{u}) := fun heq =>
      hne ((XBOOLE_0.def10 (X := Y) (Y := RELAT_1.field R)).mpr
        ⟨hY, (XBOOLE_1.th37 (X := RELAT_1.field R) (Y := Y)).mp heq⟩)
    obtain ⟨a, haD, hleast⟩ := th6 h
      (fun x hx => ((XBOOLE_0.def5 (RELAT_1.field R) Y x).mp hx).1) hdiff
    have haF : a ∈ RELAT_1.field R :=
      ((XBOOLE_0.def5 (RELAT_1.field R) Y a).mp haD).1
    have hanY : a ∉ Y :=
      ((XBOOLE_0.def5 (RELAT_1.field R) Y a).mp haD).2
    refine ⟨a, haF, ?_⟩
    apply TARSKI.extensionality
    intro b
    constructor
    · intro hbY
      apply Classical.byContradiction
      intro hnseg
      have hneab : a ≠ b := fun heq => hanY (heq ▸ hbY)
      have hnba : TARSKI.pair b a ∉ R := fun hp =>
        hnseg ((th1 R a b).mpr ⟨fun heq => hneab heq.symm, hp⟩)
      have hab : TARSKI.pair a b ∈ R :=
        Or.elim ((lm4 R).mp h.2.2.2.1 a b haF (hY b hbY) hneab)
          (fun h => h) (fun hba => (hnba hba).elim)
      exact hanY (hcl b hbY a hab)
    · intro hbS
      have ⟨hnb, hba⟩ := (th1 R a b).mp hbS
      apply Classical.byContradiction
      intro hbnY
      have hbD : b ∈ RELAT_1.field R \ Y :=
        (XBOOLE_0.def5 (RELAT_1.field R) Y b).mpr
          ⟨(RELAT_1.th15 hba).1, hbnY⟩
      have hab : TARSKI.pair a b ∈ R := hleast b hbD
      exact hnb ((lm3 R).mp h.2.2.1 a b hab hba).symm

/-- `WELLORD1:29` (`Th29`) -/
theorem th29 {R : TarskiSet.{u}} (h : isWellOrdering R)
    {a b : TarskiSet.{u}} (ha : a ∈ RELAT_1.field R)
    (hb : b ∈ RELAT_1.field R) :
    TARSKI.pair a b ∈ R ↔ seg R a ⊆ seg R b := by
  constructor
  · intro hab c hc
    have ⟨hnc, hca⟩ := (th1 R a c).mp hc
    have hnc2 : c ≠ b := fun heq =>
      hnc (heq.trans ((lm3 R).mp h.2.2.1 a b hab
        (Eq.subst (motive := fun s => TARSKI.pair s a ∈ R) heq hca)).symm)
    exact (th1 R b c).mpr ⟨hnc2, (lm2 R).mp h.2.1 c a b hca hab⟩
  · intro hsub
    exact Or.elim (Classical.em (a = b))
      (fun heq => Eq.subst (motive := fun s => TARSKI.pair a s ∈ R) heq
        ((lm1 R).mp h.1 a ha))
      (fun hne =>
        Classical.byContradiction fun hnab =>
          have hba : TARSKI.pair b a ∈ R :=
            Or.elim ((lm4 R).mp h.2.2.2.1 a b ha hb hne)
              (fun hab => (hnab hab).elim) (fun hba => hba)
          have hbSeg : b ∈ seg R a :=
            (th1 R a b).mpr ⟨fun heq => hne heq.symm, hba⟩
          have hbSelf : b ∈ seg R b := hsub b hbSeg
          ((th1 R b b).mp hbSelf).1 rfl)

/-- `WELLORD1:30` (`Th30`) -/
theorem th30 {R : TarskiSet.{u}} (h : isWellOrdering R)
    {a b : TarskiSet.{u}} (ha : a ∈ RELAT_1.field R)
    (hb : b ∈ RELAT_1.field R) :
    seg R a ⊆ seg R b ↔ a = b ∨ a ∈ seg R b := by
  constructor
  · intro hsub
    have hab : TARSKI.pair a b ∈ R := (th29 h ha hb).mpr hsub
    exact Or.elim (Classical.em (a = b)) Or.inl
      (fun hne => Or.inr ((th1 R b a).mpr ⟨hne, hab⟩))
  · intro hcases
    exact Or.elim hcases
      (fun heq => Eq.subst (motive := fun s => seg R s ⊆ seg R b) heq.symm
        (fun _ hx => hx))
      (fun haS => (th29 h ha hb).mp ((th1 R b a).mp haS).2)

/-- `WELLORD1:31` (`Th31`) -/
theorem th31 {R X : TarskiSet.{u}} (h : isWellOrdering R)
    (hX : X ⊆ RELAT_1.field R) :
    RELAT_1.field (restrict2 R X) = X := by
  apply (XBOOLE_0.def10 (X := RELAT_1.field (restrict2 R X)) (Y := X)).mpr
  constructor
  · exact (th13 R X).2
  · intro x hx
    have hxx : TARSKI.pair x x ∈ R :=
      (lm1 R).mp h.1 x (hX x hx)
    have hxx2 : TARSKI.pair x x ∈ restrict2 R X :=
      (restrict2_iff R X x x).mpr
        ⟨hxx, hx, hx⟩
    exact (RELAT_1.th15 hxx2).1

/-- `WELLORD1:32` (`Th32`) -/
theorem th32 {R : TarskiSet.{u}} (h : isWellOrdering R) (a : TarskiSet.{u}) :
    RELAT_1.field (restrict2 R (seg R a)) = seg R a :=
  th31 h (th9 R a)

/-- `WELLORD1:33` (`Th33`) -/
theorem th33 {R Z : TarskiSet.{u}} (h : isWellOrdering R)
    (hZ : ∀ a, a ∈ RELAT_1.field R → seg R a ⊆ Z → a ∈ Z) :
    RELAT_1.field R ⊆ Z := by
  intro a0 ha0
  apply Classical.byContradiction
  intro hnZ0
  have hsub : RELAT_1.field R \ Z ⊆ RELAT_1.field R :=
    fun x hx => ((XBOOLE_0.def5 (RELAT_1.field R) Z x).mp hx).1
  have ha0D : a0 ∈ RELAT_1.field R \ Z :=
    (XBOOLE_0.def5 (RELAT_1.field R) Z a0).mpr ⟨ha0, hnZ0⟩
  have hne : RELAT_1.field R \ Z ≠ (∅ : TarskiSet.{u}) :=
    fun he => (XBOOLE_0.empty_iff a0).mp
      (Eq.subst (motive := fun s => a0 ∈ s) he ha0D)
  obtain ⟨a, haD, hleast⟩ := th6 h hsub hne
  have ha : a ∈ RELAT_1.field R := hsub a haD
  have hnZ : a ∉ Z := ((XBOOLE_0.def5 (RELAT_1.field R) Z a).mp haD).2
  have hex : ∃ b, TARSKI.pair b a ∈ R ∧ b ≠ a ∧ b ∉ Z :=
    Classical.byContradiction fun hne =>
      hnZ (hZ a ha (fun b hb =>
        let ⟨hnba, hba⟩ := (th1 R a b).mp hb
        Classical.not_not.mp (fun hnbZ =>
          hne ⟨b, hba, hnba, hnbZ⟩)))
  obtain ⟨b, hba, hnba, hnbZ⟩ := hex
  have hbF : b ∈ RELAT_1.field R := (RELAT_1.th15 hba).1
  have hbD : b ∈ RELAT_1.field R \ Z :=
    (XBOOLE_0.def5 (RELAT_1.field R) Z b).mpr ⟨hbF, hnbZ⟩
  have hab : TARSKI.pair a b ∈ R := hleast b hbD
  exact hnba ((lm3 R).mp h.2.2.1 b a hba hab)

/-- `WELLORD1:34` (`Th34`) -/
theorem th34 {R : TarskiSet.{u}} (h : isWellOrdering R)
    {a b : TarskiSet.{u}} (ha : a ∈ RELAT_1.field R)
    (hb : b ∈ RELAT_1.field R)
    (hseg : ∀ c, c ∈ seg R a → TARSKI.pair c b ∈ R ∧ c ≠ b) :
    TARSKI.pair a b ∈ R := by
  apply Classical.byContradiction
  intro hnab
  have hne : a ≠ b := fun heq =>
    hnab (Eq.subst (motive := fun s => TARSKI.pair a s ∈ R) heq
      ((lm1 R).mp h.1 a ha))
  have hba : TARSKI.pair b a ∈ R :=
    Or.elim ((lm4 R).mp h.2.2.2.1 a b ha hb hne)
      (fun hab => (hnab hab).elim) (fun hba => hba)
  have hbS : b ∈ seg R a := (th1 R a b).mpr ⟨fun heq => hne heq.symm, hba⟩
  exact (hseg b hbS).2 rfl

/-- `WELLORD1:35` (`Th35`) -/
theorem th35 {R F : TarskiSet.{u}} (h : isWellOrdering R)
    (hF : FUNCT_1.isFunction F)
    (hd : RELAT_1.dom F = RELAT_1.field R)
    (hr : RELAT_1.rng F ⊆ RELAT_1.field R)
    (hmono : ∀ a b, TARSKI.pair a b ∈ R → a ≠ b →
      TARSKI.pair (FUNCT_1.apply F a) (FUNCT_1.apply F b) ∈ R ∧
        FUNCT_1.apply F a ≠ FUNCT_1.apply F b)
    {a : TarskiSet.{u}} (ha : a ∈ RELAT_1.field R) :
    TARSKI.pair a (FUNCT_1.apply F a) ∈ R := by
  obtain ⟨Z, hZ⟩ :=
    XBOOLE_0.sch_separation (RELAT_1.field R)
      (fun x => TARSKI.pair x (FUNCT_1.apply F x) ∈ R)
  have hind : ∀ x, x ∈ RELAT_1.field R → seg R x ⊆ Z → x ∈ Z := by
    intro x hx hseg
    have hxD : x ∈ RELAT_1.dom F :=
      Eq.subst (motive := fun s => x ∈ s) hd.symm hx
    have hFa : FUNCT_1.apply F x ∈ RELAT_1.field R :=
      hr _ ((FUNCT_1.def3 hF.2).mpr ⟨x, hxD, rfl⟩)
    have hpair : TARSKI.pair x (FUNCT_1.apply F x) ∈ R :=
      th34 h hx hFa fun b hb => by
        have hbZ : b ∈ Z := hseg b hb
        have hbF : TARSKI.pair b (FUNCT_1.apply F b) ∈ R :=
          ((hZ b).mp hbZ).2
        have ⟨hnbx, hbx⟩ := (th1 R x b).mp hb
        have ⟨hFba, hFne⟩ := hmono b x hbx hnbx
        have hbFa : TARSKI.pair b (FUNCT_1.apply F x) ∈ R :=
          (lm2 R).mp h.2.1 b (FUNCT_1.apply F b) (FUNCT_1.apply F x) hbF hFba
        refine ⟨hbFa, fun heq => ?_⟩
        have heq2 : FUNCT_1.apply F b = b :=
          ((lm3 R).mp h.2.2.1 b (FUNCT_1.apply F b) hbF
            (Eq.subst (motive := fun s =>
                TARSKI.pair (FUNCT_1.apply F b) s ∈ R) heq.symm hFba)).symm
        exact hFne (heq2.trans heq)
    exact (hZ x).mpr ⟨hx, hpair⟩
  exact ((hZ a).mp (th33 h hind a ha)).2

/-- `WELLORD1:def 7` -/
def isIsomorphismOf (F R S : TarskiSet.{u}) : Prop :=
  FUNCT_1.isFunction F ∧
    RELAT_1.dom F = RELAT_1.field R ∧
    RELAT_1.rng F = RELAT_1.field S ∧
    FUNCT_1.isOneToOne F ∧
    ∀ a b, TARSKI.pair a b ∈ R ↔
      a ∈ RELAT_1.field R ∧ b ∈ RELAT_1.field R ∧
        TARSKI.pair (FUNCT_1.apply F a) (FUNCT_1.apply F b) ∈ S

theorem def7 (F R S : TarskiSet.{u}) :
    isIsomorphismOf F R S ↔
      FUNCT_1.isFunction F ∧
        RELAT_1.dom F = RELAT_1.field R ∧
        RELAT_1.rng F = RELAT_1.field S ∧
        FUNCT_1.isOneToOne F ∧
        ∀ a b, TARSKI.pair a b ∈ R ↔
          a ∈ RELAT_1.field R ∧ b ∈ RELAT_1.field R ∧
            TARSKI.pair (FUNCT_1.apply F a) (FUNCT_1.apply F b) ∈ S :=
  Iff.rfl

/-- `WELLORD1:36` (`Th36`) -/
theorem th36 {F R S : TarskiSet.{u}} (h : isIsomorphismOf F R S)
    {a b : TarskiSet.{u}} (hab : TARSKI.pair a b ∈ R) (hne : a ≠ b) :
    TARSKI.pair (FUNCT_1.apply F a) (FUNCT_1.apply F b) ∈ S ∧
      FUNCT_1.apply F a ≠ FUNCT_1.apply F b := by
  have ⟨ha, hb, hFab⟩ := (h.2.2.2.2 a b).mp hab
  have haD : a ∈ RELAT_1.dom F :=
    Eq.subst (motive := fun s => a ∈ s) h.2.1.symm ha
  have hbD : b ∈ RELAT_1.dom F :=
    Eq.subst (motive := fun s => b ∈ s) h.2.1.symm hb
  exact ⟨hFab, fun heq => hne (h.2.2.2.1 a b haD hbD heq)⟩

/-- `WELLORD1:def 8` -/
def areIsomorphic (R S : TarskiSet.{u}) : Prop :=
  ∃ F, isIsomorphismOf F R S

theorem def8 (R S : TarskiSet.{u}) :
    areIsomorphic R S ↔ ∃ F, isIsomorphismOf F R S :=
  Iff.rfl

/-- `WELLORD1:37` (`Th37`) -/
theorem th37 (R : TarskiSet.{u}) :
    isIsomorphismOf (RELAT_1.id (RELAT_1.field R)) R R := by
  refine ⟨FUNCT_1.id_isFunction (RELAT_1.field R),
    (RELAT_1.th45 (X := RELAT_1.field R)).1,
    (RELAT_1.th45 (X := RELAT_1.field R)).2,
    FUNCT_1.id_isOneToOne (RELAT_1.field R), ?_⟩
  intro a b
  constructor
  · intro hab
    have ⟨ha, hb⟩ := RELAT_1.th15 hab
    have haid := FUNCT_1.th18 (X := RELAT_1.field R) ha
    have hbid := FUNCT_1.th18 (X := RELAT_1.field R) hb
    exact ⟨ha, hb,
      Eq.subst (motive := fun s =>
          TARSKI.pair s (FUNCT_1.apply (RELAT_1.id (RELAT_1.field R)) b) ∈ R)
        haid.symm
        (Eq.subst (motive := fun s => TARSKI.pair a s ∈ R) hbid.symm hab)⟩
  · intro ⟨ha, hb, hid⟩
    have haid := FUNCT_1.th18 (X := RELAT_1.field R) ha
    have hbid := FUNCT_1.th18 (X := RELAT_1.field R) hb
    exact Eq.subst (motive := fun s => TARSKI.pair s b ∈ R) haid
      (Eq.subst (motive := fun s =>
          TARSKI.pair (FUNCT_1.apply (RELAT_1.id (RELAT_1.field R)) a) s ∈ R)
        hbid hid)

/-- Unlabeled `WELLORD1` after `Th37` (`L947`). -/
theorem th38 (R : TarskiSet.{u}) : areIsomorphic R R :=
  ⟨RELAT_1.id (RELAT_1.field R), th37 R⟩



/-- `WELLORD1:39` (`Th39`) -/
theorem th39 {F R S : TarskiSet.{u}} (h : isIsomorphismOf F R S) :
    isIsomorphismOf (FUNCT_1.inv F) S R := by
  have hF := h.1
  have h1 := h.2.2.2.1
  have hd := h.2.1
  have hr := h.2.2.1
  have hinv := FUNCT_1.inv_isFunction hF h1
  refine ⟨hinv,
    (FUNCT_1.th33 h1).1.symm.trans hr,
    (FUNCT_1.th33 h1).2.symm.trans hd, ?oto, ?pairs⟩
  case oto =>
    intro y1 y2 hy1 hy2 heq
    have hy1R : y1 ∈ RELAT_1.rng F :=
      Eq.subst (motive := fun s => y1 ∈ s) (FUNCT_1.th33 h1).1.symm hy1
    have hy2R : y2 ∈ RELAT_1.rng F :=
      Eq.subst (motive := fun s => y2 ∈ s) (FUNCT_1.th33 h1).1.symm hy2
    have h1y : FUNCT_1.apply F (FUNCT_1.apply (FUNCT_1.inv F) y1) = y1 :=
      (FUNCT_1.th35 hF h1 hy1R).1
    have h2y : FUNCT_1.apply F (FUNCT_1.apply (FUNCT_1.inv F) y2) = y2 :=
      (FUNCT_1.th35 hF h1 hy2R).1
    exact h1y.symm.trans ((congrArg (FUNCT_1.apply F) heq).trans h2y)
  case pairs =>
    intro a b
    constructor
    · intro hab
      have ⟨ha, hb⟩ := RELAT_1.th15 hab
      have haR : a ∈ RELAT_1.rng F :=
        Eq.subst (motive := fun s => a ∈ s) hr.symm ha
      have hbR : b ∈ RELAT_1.rng F :=
        Eq.subst (motive := fun s => b ∈ s) hr.symm hb
      have haeq : a = FUNCT_1.apply F (FUNCT_1.apply (FUNCT_1.inv F) a) :=
        (FUNCT_1.th35 hF h1 haR).1.symm
      have hbeq : b = FUNCT_1.apply F (FUNCT_1.apply (FUNCT_1.inv F) b) :=
        (FUNCT_1.th35 hF h1 hbR).1.symm
      have hFa : FUNCT_1.apply (FUNCT_1.inv F) a ∈ RELAT_1.field R :=
        Eq.subst (motive := fun s => FUNCT_1.apply (FUNCT_1.inv F) a ∈ s) hd
          (Eq.subst (motive := fun s => FUNCT_1.apply (FUNCT_1.inv F) a ∈ s)
            (FUNCT_1.th33 h1).2.symm
            (FUNCT_1.th3 (FUNCT_1.converse_isFunctionLike_of_inj hF.2 h1)
              (Eq.subst (motive := fun s => a ∈ s) (FUNCT_1.th33 h1).1 haR)))
      have hFb : FUNCT_1.apply (FUNCT_1.inv F) b ∈ RELAT_1.field R :=
        Eq.subst (motive := fun s => FUNCT_1.apply (FUNCT_1.inv F) b ∈ s) hd
          (Eq.subst (motive := fun s => FUNCT_1.apply (FUNCT_1.inv F) b ∈ s)
            (FUNCT_1.th33 h1).2.symm
            (FUNCT_1.th3 (FUNCT_1.converse_isFunctionLike_of_inj hF.2 h1)
              (Eq.subst (motive := fun s => b ∈ s) (FUNCT_1.th33 h1).1 hbR)))
      have hab1 : TARSKI.pair a
          (FUNCT_1.apply F (FUNCT_1.apply (FUNCT_1.inv F) b)) ∈ S :=
        Eq.subst (motive := fun s => TARSKI.pair a s ∈ S) hbeq hab
      have habF : TARSKI.pair
          (FUNCT_1.apply F (FUNCT_1.apply (FUNCT_1.inv F) a))
          (FUNCT_1.apply F (FUNCT_1.apply (FUNCT_1.inv F) b)) ∈ S :=
        Eq.subst (motive := fun s => TARSKI.pair s
            (FUNCT_1.apply F (FUNCT_1.apply (FUNCT_1.inv F) b)) ∈ S) haeq hab1
      exact ⟨ha, hb,
        (h.2.2.2.2 (FUNCT_1.apply (FUNCT_1.inv F) a)
          (FUNCT_1.apply (FUNCT_1.inv F) b)).mpr ⟨hFa, hFb, habF⟩⟩
    · intro ⟨ha, hb, hp⟩
      have haR : a ∈ RELAT_1.rng F :=
        Eq.subst (motive := fun s => a ∈ s) hr.symm ha
      have hbR : b ∈ RELAT_1.rng F :=
        Eq.subst (motive := fun s => b ∈ s) hr.symm hb
      have haeq : FUNCT_1.apply F (FUNCT_1.apply (FUNCT_1.inv F) a) = a :=
        (FUNCT_1.th35 hF h1 haR).1
      have hbeq : FUNCT_1.apply F (FUNCT_1.apply (FUNCT_1.inv F) b) = b :=
        (FUNCT_1.th35 hF h1 hbR).1
      have hFab := ((h.2.2.2.2 (FUNCT_1.apply (FUNCT_1.inv F) a)
        (FUNCT_1.apply (FUNCT_1.inv F) b)).mp hp).2.2
      have hFab1 : TARSKI.pair a
          (FUNCT_1.apply F (FUNCT_1.apply (FUNCT_1.inv F) b)) ∈ S :=
        Eq.subst (motive := fun s => TARSKI.pair s
            (FUNCT_1.apply F (FUNCT_1.apply (FUNCT_1.inv F) b)) ∈ S) haeq hFab
      exact Eq.subst (motive := fun s => TARSKI.pair a s ∈ S) hbeq hFab1

/-- `WELLORD1:40` (`Th40`) -/
theorem th40 {R S : TarskiSet.{u}} (h : areIsomorphic R S) :
    areIsomorphic S R :=
  let ⟨F, hF⟩ := h
  ⟨FUNCT_1.inv F, th39 hF⟩

private theorem iso_inv_apply_field {F R S a : TarskiSet.{u}}
    (h : isIsomorphismOf F R S) (ha : a ∈ RELAT_1.field S) :
    FUNCT_1.apply (FUNCT_1.inv F) a ∈ RELAT_1.field R := by
  have h39 := th39 h
  have haD : a ∈ RELAT_1.dom (FUNCT_1.inv F) :=
    Eq.subst (motive := fun s => a ∈ s) h39.2.1.symm ha
  exact Eq.subst (motive := fun s => FUNCT_1.apply (FUNCT_1.inv F) a ∈ s) h39.2.2.1
    (FUNCT_1.th3 h39.1.2 haD)

private theorem iso_apply_inv {F R S a : TarskiSet.{u}}
    (h : isIsomorphismOf F R S) (ha : a ∈ RELAT_1.field S) :
    FUNCT_1.apply F (FUNCT_1.apply (FUNCT_1.inv F) a) = a :=
  (FUNCT_1.th35 h.1 h.2.2.2.1
    (Eq.subst (motive := fun s => a ∈ s) h.2.2.1.symm ha)).1

/-- `WELLORD1:41` (`Th41`) -/
theorem th41 {F G R S T : TarskiSet.{u}}
    (hF : isIsomorphismOf F R S) (hG : isIsomorphismOf G S T) :
    isIsomorphismOf (RELAT_1.comp F G) R T := by
  have hdF := hF.2.1
  have hrF := hF.2.2.1
  have hdG := hG.2.1
  have hrG := hG.2.2.1
  have hrng_sub : RELAT_1.rng F ⊆ RELAT_1.dom G :=
    fun x hx =>
      Eq.subst (motive := fun s => x ∈ s) hdG.symm
        (Eq.subst (motive := fun s => x ∈ s) hrF hx)
  have hdom_sub : RELAT_1.dom G ⊆ RELAT_1.rng F :=
    fun x hx =>
      Eq.subst (motive := fun s => x ∈ s) hrF.symm
        (Eq.subst (motive := fun s => x ∈ s) hdG hx)
  have hdom : RELAT_1.dom (RELAT_1.comp F G) = RELAT_1.field R :=
    (RELAT_1.th27 (R := F) (P := G) hrng_sub).trans hdF
  have hrng : RELAT_1.rng (RELAT_1.comp F G) = RELAT_1.field T :=
    (RELAT_1.th28 (P := G) (R := F) hdom_sub).trans hrG
  refine ⟨FUNCT_1.comp_isFunction hF.1 hG.1, hdom, hrng,
    FUNCT_1.th24 hF.1.2 hG.1.2 hF.2.2.2.1 hG.2.2.2.1, ?_⟩
  intro a b
  constructor
  · intro hab
    have ⟨ha, hb, hFab⟩ := (hF.2.2.2.2 a b).mp hab
    have haD : a ∈ RELAT_1.dom F :=
      Eq.subst (motive := fun s => a ∈ s) hdF.symm ha
    have hbD : b ∈ RELAT_1.dom F :=
      Eq.subst (motive := fun s => b ∈ s) hdF.symm hb
    have hFa : FUNCT_1.apply F a ∈ RELAT_1.field S :=
      Eq.subst (motive := fun s => FUNCT_1.apply F a ∈ s) hrF
        (FUNCT_1.th3 hF.1.2 haD)
    have hFb : FUNCT_1.apply F b ∈ RELAT_1.field S :=
      Eq.subst (motive := fun s => FUNCT_1.apply F b ∈ s) hrF
        (FUNCT_1.th3 hF.1.2 hbD)
    have hGab := ((hG.2.2.2.2 (FUNCT_1.apply F a) (FUNCT_1.apply F b)).mp hFab).2.2
    have haeq : FUNCT_1.apply (RELAT_1.comp F G) a =
        FUNCT_1.apply G (FUNCT_1.apply F a) :=
      FUNCT_1.th13 hF.1.2 hG.1.2 haD
    have hbeq : FUNCT_1.apply (RELAT_1.comp F G) b =
        FUNCT_1.apply G (FUNCT_1.apply F b) :=
      FUNCT_1.th13 hF.1.2 hG.1.2 hbD
    have hcomp1 : TARSKI.pair (FUNCT_1.apply (RELAT_1.comp F G) a)
        (FUNCT_1.apply G (FUNCT_1.apply F b)) ∈ T :=
      Eq.subst (motive := fun s => TARSKI.pair s
          (FUNCT_1.apply G (FUNCT_1.apply F b)) ∈ T) haeq.symm hGab
    have hcomp2 : TARSKI.pair (FUNCT_1.apply (RELAT_1.comp F G) a)
        (FUNCT_1.apply (RELAT_1.comp F G) b) ∈ T :=
      Eq.subst (motive := fun s =>
          TARSKI.pair (FUNCT_1.apply (RELAT_1.comp F G) a) s ∈ T)
        hbeq.symm hcomp1
    exact ⟨ha, hb, hcomp2⟩
  · intro ⟨ha, hb, hcomp⟩
    have haD : a ∈ RELAT_1.dom F :=
      Eq.subst (motive := fun s => a ∈ s) hdF.symm ha
    have hbD : b ∈ RELAT_1.dom F :=
      Eq.subst (motive := fun s => b ∈ s) hdF.symm hb
    have haeq : FUNCT_1.apply (RELAT_1.comp F G) a =
        FUNCT_1.apply G (FUNCT_1.apply F a) :=
      FUNCT_1.th13 hF.1.2 hG.1.2 haD
    have hbeq : FUNCT_1.apply (RELAT_1.comp F G) b =
        FUNCT_1.apply G (FUNCT_1.apply F b) :=
      FUNCT_1.th13 hF.1.2 hG.1.2 hbD
    have hGab1 : TARSKI.pair (FUNCT_1.apply G (FUNCT_1.apply F a))
        (FUNCT_1.apply (RELAT_1.comp F G) b) ∈ T :=
      Eq.subst (motive := fun s => TARSKI.pair s
          (FUNCT_1.apply (RELAT_1.comp F G) b) ∈ T) haeq hcomp
    have hGab : TARSKI.pair (FUNCT_1.apply G (FUNCT_1.apply F a))
        (FUNCT_1.apply G (FUNCT_1.apply F b)) ∈ T :=
      Eq.subst (motive := fun s =>
          TARSKI.pair (FUNCT_1.apply G (FUNCT_1.apply F a)) s ∈ T) hbeq hGab1
    have hFa : FUNCT_1.apply F a ∈ RELAT_1.field S :=
      Eq.subst (motive := fun s => FUNCT_1.apply F a ∈ s) hrF
        (FUNCT_1.th3 hF.1.2 haD)
    have hFb : FUNCT_1.apply F b ∈ RELAT_1.field S :=
      Eq.subst (motive := fun s => FUNCT_1.apply F b ∈ s) hrF
        (FUNCT_1.th3 hF.1.2 hbD)
    have hFab : TARSKI.pair (FUNCT_1.apply F a) (FUNCT_1.apply F b) ∈ S :=
      (hG.2.2.2.2 (FUNCT_1.apply F a) (FUNCT_1.apply F b)).mpr
        ⟨hFa, hFb, hGab⟩
    exact (hF.2.2.2.2 a b).mpr ⟨ha, hb, hFab⟩

/-- `WELLORD1:42` (`Th42`) -/
theorem th42 {R S T : TarskiSet.{u}}
    (h1 : areIsomorphic R S) (h2 : areIsomorphic S T) :
    areIsomorphic R T :=
  let ⟨F, hF⟩ := h1
  let ⟨G, hG⟩ := h2
  ⟨RELAT_1.comp F G, th41 hF hG⟩

/-- `WELLORD1:43` (`Th43`) -/
theorem th43 {F R S : TarskiSet.{u}} (hF : isIsomorphismOf F R S) :
    (RELAT_2.isReflexive R → RELAT_2.isReflexive S) ∧
    (RELAT_2.isTransitive R → RELAT_2.isTransitive S) ∧
    (RELAT_2.isConnected R → RELAT_2.isConnected S) ∧
    (RELAT_2.isAntisymmetric R → RELAT_2.isAntisymmetric S) ∧
    (isWellFounded R → isWellFounded S) := by
  have h39 := th39 hF
  refine ⟨?refl, ?trans, ?conn, ?anti, ?wf⟩
  case refl =>
    intro hR
    exact (lm1 S).mpr fun a ha =>
      (h39.2.2.2.2 a a).mpr ⟨ha, ha,
        (lm1 R).mp hR _ (iso_inv_apply_field hF ha)⟩
  case trans =>
    intro hT
    exact (lm2 S).mpr fun a b c hab hbc =>
      (h39.2.2.2.2 a c).mpr ⟨(RELAT_1.th15 hab).1, (RELAT_1.th15 hbc).2,
        (lm2 R).mp hT _ _ _
          ((h39.2.2.2.2 a b).mp hab).2.2
          ((h39.2.2.2.2 b c).mp hbc).2.2⟩
  case conn =>
    intro hC
    exact (lm4 S).mpr fun a b ha hb hne =>
      let hneinv : FUNCT_1.apply (FUNCT_1.inv F) a ≠
          FUNCT_1.apply (FUNCT_1.inv F) b :=
        fun heq => hne
          ((iso_apply_inv hF ha).symm.trans
            ((congrArg (FUNCT_1.apply F) heq).trans (iso_apply_inv hF hb)))
      Or.elim ((lm4 R).mp hC _ _
          (iso_inv_apply_field hF ha) (iso_inv_apply_field hF hb) hneinv)
        (fun habR => Or.inl ((h39.2.2.2.2 a b).mpr
          ⟨ha, hb, habR⟩))
        (fun hbaR => Or.inr ((h39.2.2.2.2 b a).mpr
          ⟨hb, ha, hbaR⟩))
  case anti =>
    intro hA
    exact (lm3 S).mpr fun a b hab hba =>
      (iso_apply_inv hF (RELAT_1.th15 hab).1).symm.trans
        ((congrArg (FUNCT_1.apply F)
          ((lm3 R).mp hA _ _
            ((h39.2.2.2.2 a b).mp hab).2.2
            ((h39.2.2.2.2 b a).mp hba).2.2)).trans
          (iso_apply_inv hF (RELAT_1.th15 hab).2))
  case wf =>
    intro hWF Z hZ hne
    have hZrng : Z ⊆ RELAT_1.rng F :=
      fun z hz => Eq.subst (motive := fun s => z ∈ s) hF.2.2.1.symm (hZ z hz)
    have hinvY : RELAT_1.invimage F Z ⊆ RELAT_1.field R :=
      fun x hx => Eq.subst (motive := fun s => x ∈ s) hF.2.1
        (RELAT_1.th132 x hx)
    have hinvNe : RELAT_1.invimage F Z ≠ (∅ : TarskiSet.{u}) :=
      RELAT_1.th139 hne hZrng
    obtain ⟨x, hxY, hmiss⟩ := hWF _ hinvY hinvNe
    have hxD : x ∈ RELAT_1.dom F :=
      Eq.subst (motive := fun s => x ∈ s) hF.2.1.symm (hinvY x hxY)
    have hFxZ : FUNCT_1.apply F x ∈ Z :=
      ((FUNCT_1.def7 hF.1.2 (Y := Z) (x := x)).mp hxY).2
    refine ⟨FUNCT_1.apply F x, hFxZ, ?_⟩
    apply Classical.byContradiction
    intro hnm
    have ⟨y, hyS, hyZ⟩ := (XBOOLE_0.th3 (seg S (FUNCT_1.apply F x)) Z).mp
      (fun hm : XBOOLE_0.misses (seg S (FUNCT_1.apply F x)) Z => hnm hm)
    have ⟨hny, hyFx⟩ := (th1 S (FUNCT_1.apply F x) y).mp hyS
    have hySfield := (RELAT_1.th15 hyFx).1
    have hyinv := iso_inv_apply_field hF hySfield
    have hyeq := iso_apply_inv hF hySfield
    have hyinvD : FUNCT_1.apply (FUNCT_1.inv F) y ∈ RELAT_1.dom F :=
      Eq.subst (motive := fun s => FUNCT_1.apply (FUNCT_1.inv F) y ∈ s)
        hF.2.1.symm hyinv
    have hyinvY : FUNCT_1.apply (FUNCT_1.inv F) y ∈ RELAT_1.invimage F Z :=
      (FUNCT_1.def7 hF.1.2).mpr
        ⟨hyinvD, Eq.subst (motive := fun s => s ∈ Z) hyeq.symm hyZ⟩
    have hnseg : FUNCT_1.apply (FUNCT_1.inv F) y ∉ seg R x :=
      misses_not_mem hmiss hyinvY
    have hyxR : TARSKI.pair (FUNCT_1.apply (FUNCT_1.inv F) y) x ∈ R :=
      (hF.2.2.2.2 (FUNCT_1.apply (FUNCT_1.inv F) y) x).mpr
        ⟨hyinv, hinvY x hxY,
          Eq.subst (motive := fun s => TARSKI.pair s (FUNCT_1.apply F x) ∈ S)
            hyeq.symm hyFx⟩
    have hne2 : FUNCT_1.apply (FUNCT_1.inv F) y ≠ x :=
      fun heq => hny (hyeq.symm.trans (congrArg (FUNCT_1.apply F) heq))
    exact hnseg ((th1 R x (FUNCT_1.apply (FUNCT_1.inv F) y)).mpr ⟨hne2, hyxR⟩)

/-- `WELLORD1:44` (`Th44`) -/
theorem th44 {R S F : TarskiSet.{u}} (hR : isWellOrdering R)
    (hF : isIsomorphismOf F R S) : isWellOrdering S :=
  let h := th43 hF
  ⟨h.1 hR.1, h.2.1 hR.2.1, h.2.2.2.1 hR.2.2.1, h.2.2.1 hR.2.2.2.1,
    h.2.2.2.2 hR.2.2.2.2⟩

/-- `WELLORD1:45` (`Th45`) -/
theorem th45 {R S F G : TarskiSet.{u}} (hR : isWellOrdering R)
    (hF : isIsomorphismOf F R S) (hG : isIsomorphismOf G R S) : F = G := by
  have hS : isWellOrdering S := th44 hR hF
  have hdF := hF.2.1
  have hrF := hF.2.2.1
  have hdG := hG.2.1
  have hrG := hG.2.2.1
  have h1F := hF.2.2.2.1
  have h1G := hG.2.2.2.1
  have hFinv := th39 hF
  have hGinv := th39 hG
  have hFG : isIsomorphismOf (RELAT_1.comp G (FUNCT_1.inv F)) R R :=
    th41 hG hFinv
  have hGF : isIsomorphismOf (RELAT_1.comp F (FUNCT_1.inv G)) R R :=
    th41 hF hGinv
  have hpoint : ∀ a, a ∈ RELAT_1.field R →
      FUNCT_1.apply F a = FUNCT_1.apply G a := by
    intro a ha
    have haDF : a ∈ RELAT_1.dom F :=
      Eq.subst (motive := fun s => a ∈ s) hdF.symm ha
    have haDG : a ∈ RELAT_1.dom G :=
      Eq.subst (motive := fun s => a ∈ s) hdG.symm ha
    have hGa : FUNCT_1.apply G a ∈ RELAT_1.field S :=
      Eq.subst (motive := fun s => FUNCT_1.apply G a ∈ s) hrG
        (FUNCT_1.th3 hG.1.2 haDG)
    have hFa : FUNCT_1.apply F a ∈ RELAT_1.field S :=
      Eq.subst (motive := fun s => FUNCT_1.apply F a ∈ s) hrF
        (FUNCT_1.th3 hF.1.2 haDF)
    have hmonoFG : ∀ x y, TARSKI.pair x y ∈ R → x ≠ y →
        TARSKI.pair (FUNCT_1.apply (RELAT_1.comp G (FUNCT_1.inv F)) x)
          (FUNCT_1.apply (RELAT_1.comp G (FUNCT_1.inv F)) y) ∈ R ∧
        FUNCT_1.apply (RELAT_1.comp G (FUNCT_1.inv F)) x ≠
          FUNCT_1.apply (RELAT_1.comp G (FUNCT_1.inv F)) y :=
      fun x y hxy hne => th36 hFG hxy hne
    have hmonoGF : ∀ x y, TARSKI.pair x y ∈ R → x ≠ y →
        TARSKI.pair (FUNCT_1.apply (RELAT_1.comp F (FUNCT_1.inv G)) x)
          (FUNCT_1.apply (RELAT_1.comp F (FUNCT_1.inv G)) y) ∈ R ∧
        FUNCT_1.apply (RELAT_1.comp F (FUNCT_1.inv G)) x ≠
          FUNCT_1.apply (RELAT_1.comp F (FUNCT_1.inv G)) y :=
      fun x y hxy hne => th36 hGF hxy hne
    have hFGa : TARSKI.pair a
        (FUNCT_1.apply (RELAT_1.comp G (FUNCT_1.inv F)) a) ∈ R :=
      th35 hR hFG.1 hFG.2.1
        (fun x hx => Eq.subst (motive := fun s => x ∈ s) hFG.2.2.1 hx)
        hmonoFG ha
    have hGFa : TARSKI.pair a
        (FUNCT_1.apply (RELAT_1.comp F (FUNCT_1.inv G)) a) ∈ R :=
      th35 hR hGF.1 hGF.2.1
        (fun x hx => Eq.subst (motive := fun s => x ∈ s) hGF.2.2.1 hx)
        hmonoGF ha
    have haGeq : FUNCT_1.apply (RELAT_1.comp G (FUNCT_1.inv F)) a =
        FUNCT_1.apply (FUNCT_1.inv F) (FUNCT_1.apply G a) :=
      FUNCT_1.th13 hG.1.2 (FUNCT_1.converse_isFunctionLike_of_inj hF.1.2 h1F) haDG
    have haFeq : FUNCT_1.apply (RELAT_1.comp F (FUNCT_1.inv G)) a =
        FUNCT_1.apply (FUNCT_1.inv G) (FUNCT_1.apply F a) :=
      FUNCT_1.th13 hF.1.2 (FUNCT_1.converse_isFunctionLike_of_inj hG.1.2 h1G) haDF
    have hGaR : FUNCT_1.apply G a ∈ RELAT_1.rng F :=
      Eq.subst (motive := fun s => FUNCT_1.apply G a ∈ s) hrF.symm hGa
    have hFaR : FUNCT_1.apply F a ∈ RELAT_1.rng G :=
      Eq.subst (motive := fun s => FUNCT_1.apply F a ∈ s) hrG.symm hFa
    have hFinvGa : FUNCT_1.apply F
        (FUNCT_1.apply (FUNCT_1.inv F) (FUNCT_1.apply G a)) =
        FUNCT_1.apply G a :=
      (FUNCT_1.th35 hF.1 h1F hGaR).1
    have hGinvFa : FUNCT_1.apply G
        (FUNCT_1.apply (FUNCT_1.inv G) (FUNCT_1.apply F a)) =
        FUNCT_1.apply F a :=
      (FUNCT_1.th35 hG.1 h1G hFaR).1
    have hFGmid : TARSKI.pair (FUNCT_1.apply F a)
        (FUNCT_1.apply F (FUNCT_1.apply (RELAT_1.comp G (FUNCT_1.inv F)) a)) ∈ S :=
      ((hF.2.2.2.2 a (FUNCT_1.apply (RELAT_1.comp G (FUNCT_1.inv F)) a)).mp
        hFGa).2.2
    have hFGval : FUNCT_1.apply F
        (FUNCT_1.apply (RELAT_1.comp G (FUNCT_1.inv F)) a) =
        FUNCT_1.apply G a :=
      (congrArg (FUNCT_1.apply F) haGeq).trans hFinvGa
    have hFGpair : TARSKI.pair (FUNCT_1.apply F a) (FUNCT_1.apply G a) ∈ S :=
      Eq.subst (motive := fun s => TARSKI.pair (FUNCT_1.apply F a) s ∈ S)
        hFGval hFGmid
    have hGFmid : TARSKI.pair (FUNCT_1.apply G a)
        (FUNCT_1.apply G (FUNCT_1.apply (RELAT_1.comp F (FUNCT_1.inv G)) a)) ∈ S :=
      ((hG.2.2.2.2 a (FUNCT_1.apply (RELAT_1.comp F (FUNCT_1.inv G)) a)).mp
        hGFa).2.2
    have hGFval : FUNCT_1.apply G
        (FUNCT_1.apply (RELAT_1.comp F (FUNCT_1.inv G)) a) =
        FUNCT_1.apply F a :=
      (congrArg (FUNCT_1.apply G) haFeq).trans hGinvFa
    have hGFpair : TARSKI.pair (FUNCT_1.apply G a) (FUNCT_1.apply F a) ∈ S :=
      Eq.subst (motive := fun s => TARSKI.pair (FUNCT_1.apply G a) s ∈ S)
        hGFval hGFmid
    exact (lm3 S).mp hS.2.2.1 _ _ hFGpair hGFpair
  exact FUNCT_1.th2 hF.1 hG.1 (hdF.trans hdG.symm) fun x hx =>
    hpoint x (Eq.subst (motive := fun s => x ∈ s) hdF hx)

/-- `WELLORD1:def 9` -/
noncomputable def canonical_isomorphism_of {R S : TarskiSet.{u}}
    (_hR : isWellOrdering R) (hiso : areIsomorphic R S) : TarskiSet.{u} :=
  Classical.choose hiso

theorem def9 {R S : TarskiSet.{u}} (hR : isWellOrdering R)
    (hiso : areIsomorphic R S) :
    isIsomorphismOf (canonical_isomorphism_of hR hiso) R S :=
  Classical.choose_spec hiso

/-- `WELLORD1:46` (`Th46`) -/
theorem th46 {R : TarskiSet.{u}} (h : isWellOrdering R)
    {a : TarskiSet.{u}} (ha : a ∈ RELAT_1.field R) :
    ¬ areIsomorphic R (restrict2 R (seg R a)) := by
  intro hiso
  let F := canonical_isomorphism_of h hiso
  have hF : isIsomorphismOf F R (restrict2 R (seg R a)) := def9 h hiso
  have haD : a ∈ RELAT_1.dom F :=
    Eq.subst (motive := fun s => a ∈ s) hF.2.1.symm ha
  have hFaS : FUNCT_1.apply F a ∈ seg R a :=
    Eq.subst (motive := fun s => FUNCT_1.apply F a ∈ s) (th32 h a)
      (Eq.subst (motive := fun s => FUNCT_1.apply F a ∈ s) hF.2.2.1
        (FUNCT_1.th3 hF.1.2 haD))
  have ⟨hnea, hFaa⟩ := (th1 R a (FUNCT_1.apply F a)).mp hFaS
  have hmono : ∀ x y, TARSKI.pair x y ∈ R → x ≠ y →
      TARSKI.pair (FUNCT_1.apply F x) (FUNCT_1.apply F y) ∈ R ∧
        FUNCT_1.apply F x ≠ FUNCT_1.apply F y := by
    intro x y hxy hne
    have ⟨hpS, hFne⟩ := th36 hF hxy hne
    exact ⟨((restrict2_iff R (seg R a) (FUNCT_1.apply F x)
      (FUNCT_1.apply F y)).mp hpS).1, hFne⟩
  have hrng : RELAT_1.rng F ⊆ RELAT_1.field R :=
    fun z hz => (th13 R (seg R a)).1 z
      (Eq.subst (motive := fun s => z ∈ s) hF.2.2.1 hz)
  have hab : TARSKI.pair a (FUNCT_1.apply F a) ∈ R :=
    th35 h hF.1 hF.2.1 hrng hmono ha
  exact hnea ((lm3 R).mp h.2.2.1 a (FUNCT_1.apply F a) hab hFaa).symm

/-- `WELLORD1:47` (`Th47`) -/
theorem th47 {R : TarskiSet.{u}} (h : isWellOrdering R)
    {a b : TarskiSet.{u}} (ha : a ∈ RELAT_1.field R)
    (hb : b ∈ RELAT_1.field R) (hne : a ≠ b) :
    ¬ areIsomorphic (restrict2 R (seg R a)) (restrict2 R (seg R b)) := by
  have hcmp := (XBOOLE_0.def9 (seg R a) (seg R b)).mp (th26 h a b)
  exact Or.elim hcmp
    (fun hab : seg R a ⊆ seg R b => by
      intro hiso
      have haSeg : a ∈ seg R b := by
        apply Classical.byContradiction
        intro hna
        have hnab : TARSKI.pair a b ∉ R := fun hp =>
          hna ((th1 R b a).mpr ⟨hne, hp⟩)
        have hbaR : TARSKI.pair b a ∈ R :=
          Or.elim ((lm4 R).mp h.2.2.2.1 a b ha hb hne)
            (fun hp => (hnab hp).elim) (fun hp => hp)
        have hbSeg : b ∈ seg R a :=
          (th1 R a b).mpr ⟨fun heq => hne heq.symm, hbaR⟩
        exact ((th1 R b b).mp (hab b hbSeg)).1 rfl
      have hS : isWellOrdering (restrict2 R (seg R b)) := th25 h (seg R b)
      have haF : a ∈ RELAT_1.field (restrict2 R (seg R b)) :=
        Eq.subst (motive := fun s => a ∈ s) (th32 h b).symm haSeg
      have hseg : seg (restrict2 R (seg R b)) a = seg R a := th27 h haSeg
      have hrest : restrict2 (restrict2 R (seg R b)) (seg R a) =
          restrict2 R (seg R a) := th22 hab (R := R)
      have hnot := th46 hS haF
      have hisoS : areIsomorphic (restrict2 R (seg R b)) (restrict2 R (seg R a)) :=
        th40 hiso
      have hiso2 : areIsomorphic (restrict2 R (seg R b))
          (restrict2 (restrict2 R (seg R b)) (seg (restrict2 R (seg R b)) a)) :=
        Eq.subst (motive := fun s => areIsomorphic (restrict2 R (seg R b))
            (restrict2 (restrict2 R (seg R b)) s)) hseg.symm
          (Eq.subst (motive := fun s =>
              areIsomorphic (restrict2 R (seg R b)) s) hrest.symm hisoS)
      exact hnot hiso2)
    (fun hba : seg R b ⊆ seg R a => by
      intro hiso
      have hbSeg : b ∈ seg R a := by
        apply Classical.byContradiction
        intro hnb
        have hnba : TARSKI.pair b a ∉ R := fun hp =>
          hnb ((th1 R a b).mpr ⟨fun heq => hne heq.symm, hp⟩)
        have habR : TARSKI.pair a b ∈ R :=
          Or.elim ((lm4 R).mp h.2.2.2.1 a b ha hb hne)
            (fun hp => hp) (fun hp => (hnba hp).elim)
        have haSeg : a ∈ seg R b := (th1 R b a).mpr ⟨hne, habR⟩
        exact ((th1 R a a).mp (hba a haSeg)).1 rfl
      have hS : isWellOrdering (restrict2 R (seg R a)) := th25 h (seg R a)
      have hbF : b ∈ RELAT_1.field (restrict2 R (seg R a)) :=
        Eq.subst (motive := fun s => b ∈ s) (th32 h a).symm hbSeg
      have hseg : seg (restrict2 R (seg R a)) b = seg R b := th27 h hbSeg
      have hrest : restrict2 (restrict2 R (seg R a)) (seg R b) =
          restrict2 R (seg R b) := th22 hba (R := R)
      have hnot := th46 hS hbF
      have hiso2 : areIsomorphic (restrict2 R (seg R a))
          (restrict2 (restrict2 R (seg R a)) (seg (restrict2 R (seg R a)) b)) :=
        Eq.subst (motive := fun s => areIsomorphic (restrict2 R (seg R a))
            (restrict2 (restrict2 R (seg R a)) s)) hseg.symm
          (Eq.subst (motive := fun s =>
              areIsomorphic (restrict2 R (seg R a)) s) hrest.symm hiso)
      exact hnot hiso2)

/-- `WELLORD1:48` (`Th48`) -/
theorem th48 {R S F Z : TarskiSet.{u}} (hR : isWellOrdering R)
    (hZ : Z ⊆ RELAT_1.field R) (hF : isIsomorphismOf F R S) :
    isIsomorphismOf (RELAT_1.restrict F Z) (restrict2 R Z)
      (restrict2 S (RELAT_1.image F Z)) ∧
    areIsomorphic (restrict2 R Z) (restrict2 S (RELAT_1.image F Z)) := by
  have hS : isWellOrdering S := th44 hR hF
  have himg : RELAT_1.image F Z ⊆ RELAT_1.field S :=
    fun y hy =>
      Eq.subst (motive := fun s => y ∈ s) hF.2.2.1
        (RELAT_1.th111 (R := F) (X := Z) y hy)
  have hfieldR : RELAT_1.field (restrict2 R Z) = Z := th31 hR hZ
  have hfieldS : RELAT_1.field (restrict2 S (RELAT_1.image F Z)) =
      RELAT_1.image F Z := th31 hS himg
  have hZdom : Z ⊆ RELAT_1.dom F :=
    fun x hx => Eq.subst (motive := fun s => x ∈ s) hF.2.1.symm (hZ x hx)
  have hdom : RELAT_1.dom (RELAT_1.restrict F Z) =
      RELAT_1.field (restrict2 R Z) :=
    (RELAT_1.th62 (R := F) (X := Z) hZdom).trans hfieldR.symm
  have hrng : RELAT_1.rng (RELAT_1.restrict F Z) =
      RELAT_1.field (restrict2 S (RELAT_1.image F Z)) :=
    RELAT_1.th115.trans hfieldS.symm
  have hresF : FUNCT_1.isFunction (RELAT_1.restrict F Z) :=
    FUNCT_1.restrict_isFunction hF.1
  have h1 : FUNCT_1.isOneToOne (RELAT_1.restrict F Z) :=
    FUNCT_1.th52 hF.1.2 hF.2.2.2.1
  have hiso : isIsomorphismOf (RELAT_1.restrict F Z) (restrict2 R Z)
      (restrict2 S (RELAT_1.image F Z)) := by
    refine ⟨hresF, hdom, hrng, h1, ?_⟩
    intro a b
    constructor
    · intro hab
      have ⟨hpR, haZ, hbZ⟩ := (restrict2_iff R Z a b).mp hab
      have ⟨haF, hbF, hFab⟩ := (hF.2.2.2.2 a b).mp hpR
      have haD : a ∈ RELAT_1.dom (RELAT_1.restrict F Z) :=
        Eq.subst (motive := fun s => a ∈ s) hdom.symm
          (Eq.subst (motive := fun s => a ∈ s) hfieldR.symm haZ)
      have hbD : b ∈ RELAT_1.dom (RELAT_1.restrict F Z) :=
        Eq.subst (motive := fun s => b ∈ s) hdom.symm
          (Eq.subst (motive := fun s => b ∈ s) hfieldR.symm hbZ)
      have haeq : FUNCT_1.apply (RELAT_1.restrict F Z) a = FUNCT_1.apply F a :=
        FUNCT_1.th47 hF.1.2 haD
      have hbeq : FUNCT_1.apply (RELAT_1.restrict F Z) b = FUNCT_1.apply F b :=
        FUNCT_1.th47 hF.1.2 hbD
      have hFaI : FUNCT_1.apply (RELAT_1.restrict F Z) a ∈ RELAT_1.image F Z :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.image F Z) haeq.symm
          ((FUNCT_1.def6 hF.1.2).mpr ⟨a,
            Eq.subst (motive := fun s => a ∈ s) hF.2.1.symm haF, haZ, rfl⟩)
      have hFbI : FUNCT_1.apply (RELAT_1.restrict F Z) b ∈ RELAT_1.image F Z :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.image F Z) hbeq.symm
          ((FUNCT_1.def6 hF.1.2).mpr ⟨b,
            Eq.subst (motive := fun s => b ∈ s) hF.2.1.symm hbF, hbZ, rfl⟩)
      have hFab1 : TARSKI.pair (FUNCT_1.apply (RELAT_1.restrict F Z) a)
          (FUNCT_1.apply F b) ∈ S :=
        Eq.subst (motive := fun s => TARSKI.pair s (FUNCT_1.apply F b) ∈ S)
          haeq.symm hFab
      have hFab2 : TARSKI.pair (FUNCT_1.apply (RELAT_1.restrict F Z) a)
          (FUNCT_1.apply (RELAT_1.restrict F Z) b) ∈ S :=
        Eq.subst (motive := fun s =>
            TARSKI.pair (FUNCT_1.apply (RELAT_1.restrict F Z) a) s ∈ S)
          hbeq.symm hFab1
      exact ⟨Eq.subst (motive := fun s => a ∈ s) hfieldR.symm haZ,
        Eq.subst (motive := fun s => b ∈ s) hfieldR.symm hbZ,
        (restrict2_iff S (RELAT_1.image F Z)
          (FUNCT_1.apply (RELAT_1.restrict F Z) a)
          (FUNCT_1.apply (RELAT_1.restrict F Z) b)).mpr
          ⟨hFab2, hFaI, hFbI⟩⟩
    · intro ⟨haFr, hbFr, hpS2⟩
      have ⟨hpS, haI, hbI⟩ := (restrict2_iff S (RELAT_1.image F Z)
        (FUNCT_1.apply (RELAT_1.restrict F Z) a)
        (FUNCT_1.apply (RELAT_1.restrict F Z) b)).mp hpS2
      have haZ : a ∈ Z :=
        Eq.subst (motive := fun s => a ∈ s) hfieldR haFr
      have hbZ : b ∈ Z :=
        Eq.subst (motive := fun s => b ∈ s) hfieldR hbFr
      have haD : a ∈ RELAT_1.dom (RELAT_1.restrict F Z) :=
        Eq.subst (motive := fun s => a ∈ s) hdom.symm haFr
      have hbD : b ∈ RELAT_1.dom (RELAT_1.restrict F Z) :=
        Eq.subst (motive := fun s => b ∈ s) hdom.symm hbFr
      have haeq : FUNCT_1.apply (RELAT_1.restrict F Z) a = FUNCT_1.apply F a :=
        FUNCT_1.th47 hF.1.2 haD
      have hbeq : FUNCT_1.apply (RELAT_1.restrict F Z) b = FUNCT_1.apply F b :=
        FUNCT_1.th47 hF.1.2 hbD
      have hFab0 : TARSKI.pair (FUNCT_1.apply F a)
          (FUNCT_1.apply (RELAT_1.restrict F Z) b) ∈ S :=
        Eq.subst (motive := fun s => TARSKI.pair s
            (FUNCT_1.apply (RELAT_1.restrict F Z) b) ∈ S) haeq hpS
      have hFab : TARSKI.pair (FUNCT_1.apply F a) (FUNCT_1.apply F b) ∈ S :=
        Eq.subst (motive := fun s => TARSKI.pair (FUNCT_1.apply F a) s ∈ S)
          hbeq hFab0
      have haR : a ∈ RELAT_1.field R := hZ a haZ
      have hbR : b ∈ RELAT_1.field R := hZ b hbZ
      have hpR : TARSKI.pair a b ∈ R :=
        (hF.2.2.2.2 a b).mpr ⟨haR, hbR, hFab⟩
      exact (restrict2_iff R Z a b).mpr ⟨hpR, haZ, hbZ⟩
  exact ⟨hiso, ⟨RELAT_1.restrict F Z, hiso⟩⟩

/-- `WELLORD1:49` (`Th49`) -/
theorem th49 {F R S : TarskiSet.{u}} (hF : isIsomorphismOf F R S)
    {a : TarskiSet.{u}} (ha : a ∈ RELAT_1.field R) :
    ∃ b, b ∈ RELAT_1.field S ∧ RELAT_1.image F (seg R a) = seg S b := by
  refine ⟨FUNCT_1.apply F a, ?bS, ?eq⟩
  case bS =>
    have haD : a ∈ RELAT_1.dom F :=
      Eq.subst (motive := fun s => a ∈ s) hF.2.1.symm ha
    exact Eq.subst (motive := fun s => FUNCT_1.apply F a ∈ s) hF.2.2.1
      (FUNCT_1.th3 hF.1.2 haD)
  case eq =>
    apply (XBOOLE_0.def10 (X := RELAT_1.image F (seg R a))
      (Y := seg S (FUNCT_1.apply F a))).mpr
    constructor
    · intro c hc
      obtain ⟨d, hd, hdS, heq⟩ := (FUNCT_1.def6 hF.1.2).mp hc
      have ⟨hnd, hda⟩ := (th1 R a d).mp hdS
      have hFab := ((hF.2.2.2.2 d a).mp hda).2.2
      have hne : FUNCT_1.apply F d ≠ FUNCT_1.apply F a :=
        fun heqFa =>
          hnd (hF.2.2.2.1 d a hd
            (Eq.subst (motive := fun s => a ∈ s) hF.2.1.symm ha) heqFa)
      have hcS : c ∈ seg S (FUNCT_1.apply F a) :=
        (th1 S (FUNCT_1.apply F a) c).mpr
          ⟨fun heqc => hne (heq.symm.trans heqc),
            Eq.subst (motive := fun s => TARSKI.pair s (FUNCT_1.apply F a) ∈ S)
              heq.symm hFab⟩
      exact hcS
    · intro c hc
      have ⟨hnc, hcFa⟩ := (th1 S (FUNCT_1.apply F a) c).mp hc
      have hcS := (RELAT_1.th15 hcFa).1
      have hcR : c ∈ RELAT_1.rng F :=
        Eq.subst (motive := fun s => c ∈ s) hF.2.2.1.symm hcS
      have hceq := iso_apply_inv hF hcS
      have hd : FUNCT_1.apply (FUNCT_1.inv F) c ∈ RELAT_1.field R :=
        iso_inv_apply_field hF hcS
      have hda : TARSKI.pair (FUNCT_1.apply (FUNCT_1.inv F) c) a ∈ R :=
        (hF.2.2.2.2 (FUNCT_1.apply (FUNCT_1.inv F) c) a).mpr
          ⟨hd, ha,
            Eq.subst (motive := fun s => TARSKI.pair s (FUNCT_1.apply F a) ∈ S)
              hceq.symm hcFa⟩
      have hnd : FUNCT_1.apply (FUNCT_1.inv F) c ≠ a :=
        fun heq => hnc (hceq.symm.trans (congrArg (FUNCT_1.apply F) heq))
      have hdSeg : FUNCT_1.apply (FUNCT_1.inv F) c ∈ seg R a :=
        (th1 R a (FUNCT_1.apply (FUNCT_1.inv F) c)).mpr ⟨hnd, hda⟩
      have hdD : FUNCT_1.apply (FUNCT_1.inv F) c ∈ RELAT_1.dom F :=
        Eq.subst (motive := fun s => FUNCT_1.apply (FUNCT_1.inv F) c ∈ s)
          hF.2.1.symm hd
      exact (FUNCT_1.def6 hF.1.2).mpr
        ⟨FUNCT_1.apply (FUNCT_1.inv F) c, hdD, hdSeg, hceq.symm⟩

/-- `WELLORD1:50` (`Th50`) -/
theorem th50 {R S F : TarskiSet.{u}} (hR : isWellOrdering R)
    (hF : isIsomorphismOf F R S) {a : TarskiSet.{u}}
    (ha : a ∈ RELAT_1.field R) :
    ∃ b, b ∈ RELAT_1.field S ∧
      areIsomorphic (restrict2 R (seg R a)) (restrict2 S (seg S b)) := by
  obtain ⟨b, hb, himg⟩ := th49 hF ha
  refine ⟨b, hb, ?_⟩
  have hiso := (th48 hR (th9 R a) hF).2
  exact Eq.subst (motive := fun s =>
      areIsomorphic (restrict2 R (seg R a)) (restrict2 S s)) himg hiso

/-- `WELLORD1:51` (`Th51`) -/
theorem th51 {R S : TarskiSet.{u}} (hR : isWellOrdering R)
    (hS : isWellOrdering S) {a b c : TarskiSet.{u}}
    (ha : a ∈ RELAT_1.field R) (_hb : b ∈ RELAT_1.field S)
    (hc : c ∈ RELAT_1.field S)
    (hRb : areIsomorphic R (restrict2 S (seg S b)))
    (hRac : areIsomorphic (restrict2 R (seg R a))
      (restrict2 S (seg S c))) :
    seg S c ⊆ seg S b ∧ TARSKI.pair c b ∈ S := by
  have hF := def9 hR hRb
  obtain ⟨d, hdQ, himg⟩ := th49 hF ha
  have hfieldQ : RELAT_1.field (restrict2 S (seg S b)) = seg S b :=
    th32 hS b
  have hdSeg : d ∈ seg S b :=
    Eq.subst (motive := fun s => d ∈ s) hfieldQ hdQ
  have hdS : d ∈ RELAT_1.field S := th9 S b d hdSeg
  have hQseg : seg (restrict2 S (seg S b)) d = seg S d := th27 hS hdSeg
  have hTP : areIsomorphic (restrict2 S (seg S c))
      (restrict2 R (seg R a)) := th40 hRac
  have hPimg : areIsomorphic (restrict2 R (seg R a))
      (restrict2 (restrict2 S (seg S b))
        (RELAT_1.image (canonical_isomorphism_of hR hRb) (seg R a))) :=
    (th48 hR (th9 R a) hF).2
  have hTQd : areIsomorphic (restrict2 S (seg S c))
      (restrict2 (restrict2 S (seg S b))
        (seg (restrict2 S (seg S b)) d)) :=
    th42 hTP
      (Eq.subst (motive := fun s =>
          areIsomorphic (restrict2 R (seg R a))
            (restrict2 (restrict2 S (seg S b)) s)) himg hPimg)
  have hrng : RELAT_1.rng (canonical_isomorphism_of hR hRb) = seg S b :=
    hF.2.2.1.trans hfieldQ
  have himg_sub :
      RELAT_1.image (canonical_isomorphism_of hR hRb) (seg R a) ⊆
        RELAT_1.rng (canonical_isomorphism_of hR hRb) :=
    RELAT_1.th111 (R := canonical_isomorphism_of hR hRb) (X := seg R a)
  have hQd_sub : seg (restrict2 S (seg S b)) d ⊆ seg S b :=
    fun z hz =>
      Eq.subst (motive := fun s => z ∈ s) hrng
        (himg_sub z (Eq.subst (motive := fun s => z ∈ s) himg.symm hz))
  have hrest : restrict2 (restrict2 S (seg S b))
      (seg (restrict2 S (seg S b)) d) = restrict2 S (seg S d) :=
    (th22 hQd_sub (R := S)).trans (congrArg (restrict2 S) hQseg)
  have hTSd : areIsomorphic (restrict2 S (seg S c))
      (restrict2 S (seg S d)) :=
    Eq.subst (motive := fun s =>
        areIsomorphic (restrict2 S (seg S c)) s) hrest hTQd
  have heqcd : c = d :=
    Classical.byContradiction fun hne => th47 hS hc hdS hne hTSd
  have hsub : seg S c ⊆ seg S b :=
    Eq.subst (motive := fun s => seg S s ⊆ seg S b) heqcd.symm
      (fun z hz =>
        hQd_sub z (Eq.subst (motive := fun s => z ∈ s) hQseg.symm hz))
  exact ⟨hsub, (th29 hS hc _hb).mpr hsub⟩

/-- Identity on `field R` is an isomorphism of `R |_2 field R` with `R`. -/
private theorem restrict2_field_iso {R : TarskiSet.{u}}
    (h : isWellOrdering R) :
    areIsomorphic (restrict2 R (RELAT_1.field R)) R := by
  refine ⟨RELAT_1.id (RELAT_1.field R), ?_⟩
  have hfield : RELAT_1.field (restrict2 R (RELAT_1.field R)) =
      RELAT_1.field R := th31 h (fun _ hx => hx)
  refine ⟨FUNCT_1.id_isFunction (RELAT_1.field R),
    (RELAT_1.th45 (X := RELAT_1.field R)).1.trans hfield.symm,
    (RELAT_1.th45 (X := RELAT_1.field R)).2,
    FUNCT_1.id_isOneToOne (RELAT_1.field R), ?_⟩
  intro a b
  constructor
  · intro hab
    have ⟨hpR, haY, hbY⟩ :=
      (restrict2_iff R (RELAT_1.field R) a b).mp hab
    have haid := FUNCT_1.th18 (X := RELAT_1.field R) haY
    have hbid := FUNCT_1.th18 (X := RELAT_1.field R) hbY
    have haF : a ∈ RELAT_1.field (restrict2 R (RELAT_1.field R)) :=
      Eq.subst (motive := fun s => a ∈ s) hfield.symm haY
    have hbF : b ∈ RELAT_1.field (restrict2 R (RELAT_1.field R)) :=
      Eq.subst (motive := fun s => b ∈ s) hfield.symm hbY
    exact ⟨haF, hbF,
      Eq.subst (motive := fun s => TARSKI.pair s
          (FUNCT_1.apply (RELAT_1.id (RELAT_1.field R)) b) ∈ R)
        haid.symm
        (Eq.subst (motive := fun s => TARSKI.pair a s ∈ R)
          hbid.symm hpR)⟩
  · intro ⟨ha, hb, hid⟩
    have haY : a ∈ RELAT_1.field R :=
      Eq.subst (motive := fun s => a ∈ s) hfield ha
    have hbY : b ∈ RELAT_1.field R :=
      Eq.subst (motive := fun s => b ∈ s) hfield hb
    have haid := FUNCT_1.th18 (X := RELAT_1.field R) haY
    have hbid := FUNCT_1.th18 (X := RELAT_1.field R) hbY
    have hpR : TARSKI.pair a b ∈ R :=
      Eq.subst (motive := fun s => TARSKI.pair s b ∈ R) haid
        (Eq.subst (motive := fun s => TARSKI.pair
            (FUNCT_1.apply (RELAT_1.id (RELAT_1.field R)) a) s ∈ R)
          hbid hid)
    exact (restrict2_iff R (RELAT_1.field R) a b).mpr ⟨hpR, haY, hbY⟩

/-- `WELLORD1:52` (`Th52`) -/
theorem th52 {R S : TarskiSet.{u}} (hR : isWellOrdering R)
    (hS : isWellOrdering S) :
    areIsomorphic R S ∨
      (∃ a, a ∈ RELAT_1.field R ∧
        areIsomorphic (restrict2 R (seg R a)) S) ∨
      ∃ a, a ∈ RELAT_1.field S ∧
        areIsomorphic R (restrict2 S (seg S a)) := by
  obtain ⟨Z, hZmem⟩ :=
    XBOOLE_0.sch_separation (RELAT_1.field R)
      (fun a => ∃ b, b ∈ RELAT_1.field S ∧
        areIsomorphic (restrict2 R (seg R a)) (restrict2 S (seg S b)))
  have hZsub : Z ⊆ RELAT_1.field R :=
    fun x hx => ((hZmem x).mp hx).1
  have huniq : ∀ (x y1 y2 : TarskiSet.{u}),
      (y1 ∈ RELAT_1.field S ∧
        areIsomorphic (restrict2 R (seg R x)) (restrict2 S (seg S y1))) →
      (y2 ∈ RELAT_1.field S ∧
        areIsomorphic (restrict2 R (seg R x)) (restrict2 S (seg S y2))) →
      y1 = y2 := by
    intro x y1 y2 ⟨hy1, h1⟩ ⟨hy2, h2⟩
    exact Classical.byContradiction fun hne =>
      th47 hS hy1 hy2 hne (th42 (th40 h1) h2)
  obtain ⟨F, hFfun, hFchar⟩ :=
    FUNCT_1.sch_GraphFunc (RELAT_1.field R)
      (fun a b => b ∈ RELAT_1.field S ∧
        areIsomorphic (restrict2 R (seg R a)) (restrict2 S (seg S b)))
      huniq
  have hZeqD : Z = RELAT_1.dom F := by
    apply (XBOOLE_0.def10 (X := Z) (Y := RELAT_1.dom F)).mpr
    constructor
    · intro a haZ
      obtain ⟨b, hbS, hiso⟩ := ((hZmem a).mp haZ).2
      have haR : a ∈ RELAT_1.field R := ((hZmem a).mp haZ).1
      have hp : TARSKI.pair a b ∈ F :=
        (hFchar a b).mpr ⟨haR, ⟨hbS, hiso⟩⟩
      exact (RELAT_1.dom_iff F a).mpr ⟨b, hp⟩
    · intro a haD
      obtain ⟨b, hp⟩ := (RELAT_1.dom_iff F a).mp haD
      have ⟨haR, hbS, hiso⟩ := (hFchar a b).mp hp
      exact (hZmem a).mpr ⟨haR, ⟨b, hbS, hiso⟩⟩
  have hrngS : RELAT_1.rng F ⊆ RELAT_1.field S := by
    intro a haR
    obtain ⟨b, hbD, haeq⟩ := (FUNCT_1.def3 hFfun.2).mp haR
    have hp : TARSKI.pair b a ∈ F :=
      (FUNCT_1.th1 hFfun.2 (x := b) (y := a)).mpr ⟨hbD, haeq⟩
    exact ((hFchar b a).mp hp).2.1
  have hfieldRZ : RELAT_1.field (restrict2 R Z) = Z := th31 hR hZsub
  have hfieldRD : RELAT_1.field (restrict2 R (RELAT_1.dom F)) =
      RELAT_1.dom F :=
    Eq.subst (motive := fun s => RELAT_1.field (restrict2 R s) = s)
      hZeqD hfieldRZ
  have hfieldSR : RELAT_1.field (restrict2 S (RELAT_1.rng F)) =
      RELAT_1.rng F := th31 hS hrngS
  have h1to1 : FUNCT_1.isOneToOne F := by
    intro a b haD hbD heq
    have hpa : TARSKI.pair a (FUNCT_1.apply F a) ∈ F :=
      FUNCT_1.apply_spec haD
    have hpb : TARSKI.pair b (FUNCT_1.apply F b) ∈ F :=
      FUNCT_1.apply_spec hbD
    have ⟨haR, hFaS, hisoA⟩ := (hFchar a (FUNCT_1.apply F a)).mp hpa
    have ⟨hbR, _, hisoB0⟩ := (hFchar b (FUNCT_1.apply F b)).mp hpb
    have hisoB : areIsomorphic (restrict2 R (seg R b))
        (restrict2 S (seg S (FUNCT_1.apply F a))) :=
      Eq.subst (motive := fun s =>
          areIsomorphic (restrict2 R (seg R b)) (restrict2 S (seg S s)))
        heq.symm hisoB0
    exact Classical.byContradiction fun hne =>
      th47 hR haR hbR hne (th42 hisoA (th40 hisoB))
  have hFiso : isIsomorphismOf F (restrict2 R (RELAT_1.dom F))
      (restrict2 S (RELAT_1.rng F)) := by
    refine ⟨hFfun, hfieldRD.symm, hfieldSR.symm, h1to1, ?_⟩
    intro a b
    constructor
    · intro hab
      have haFld : a ∈ RELAT_1.field (restrict2 R (RELAT_1.dom F)) :=
        (RELAT_1.th15 hab).1
      have hbFld : b ∈ RELAT_1.field (restrict2 R (RELAT_1.dom F)) :=
        (RELAT_1.th15 hab).2
      have haD : a ∈ RELAT_1.dom F :=
        Eq.subst (motive := fun s => a ∈ s) hfieldRD haFld
      have hbD : b ∈ RELAT_1.dom F :=
        Eq.subst (motive := fun s => b ∈ s) hfieldRD hbFld
      have ⟨hpR, _, _⟩ :=
        (restrict2_iff R (RELAT_1.dom F) a b).mp hab
      have hpa : TARSKI.pair a (FUNCT_1.apply F a) ∈ F :=
        FUNCT_1.apply_spec haD
      have hpb : TARSKI.pair b (FUNCT_1.apply F b) ∈ F :=
        FUNCT_1.apply_spec hbD
      have ⟨haR, hFaS, hisoA⟩ := (hFchar a (FUNCT_1.apply F a)).mp hpa
      have ⟨hbR, hFbS, hisoB⟩ := (hFchar b (FUNCT_1.apply F b)).mp hpb
      have hFaR : FUNCT_1.apply F a ∈ RELAT_1.rng F :=
        FUNCT_1.th3 hFfun.2 haD
      have hFbR : FUNCT_1.apply F b ∈ RELAT_1.rng F :=
        FUNCT_1.th3 hFfun.2 hbD
      have hFabS : TARSKI.pair (FUNCT_1.apply F a) (FUNCT_1.apply F b) ∈ S :=
        Or.elim (Classical.em (a = b))
          (fun heq =>
            Eq.subst (motive := fun s =>
                TARSKI.pair (FUNCT_1.apply F a) (FUNCT_1.apply F s) ∈ S)
              heq ((lm1 S).mp hS.1 (FUNCT_1.apply F a) hFaS))
          (fun hne => by
            have haSeg : a ∈ seg R b :=
              (th1 R b a).mpr ⟨hne, hpR⟩
            let P := restrict2 R (seg R b)
            have hPwo : isWellOrdering P := th25 hR (seg R b)
            have hfieldP : RELAT_1.field P = seg R b := th32 hR b
            have haP : a ∈ RELAT_1.field P :=
              Eq.subst (motive := fun s => a ∈ s) hfieldP.symm haSeg
            have hPseg : seg P a = seg R a := th27 hR haSeg
            have hsubab : seg R a ⊆ seg R b :=
              (th29 hR haR hbR).mp hpR
            have hrest1 : restrict2 P (seg P a) = restrict2 P (seg R a) :=
              congrArg (restrict2 P) hPseg
            have hrest : restrict2 P (seg P a) = restrict2 R (seg R a) :=
              hrest1.trans (th22 hsubab (R := R))
            have hisoP : areIsomorphic (restrict2 P (seg P a))
                (restrict2 S (seg S (FUNCT_1.apply F a))) :=
              Eq.subst (motive := fun s =>
                  areIsomorphic s
                    (restrict2 S (seg S (FUNCT_1.apply F a))))
                hrest.symm hisoA
            exact (th51 hPwo hS haP hFbS hFaS hisoB hisoP).2)
      exact ⟨haFld, hbFld,
        (restrict2_iff S (RELAT_1.rng F)
          (FUNCT_1.apply F a) (FUNCT_1.apply F b)).mpr
          ⟨hFabS, hFaR, hFbR⟩⟩
    · intro ⟨haFld, hbFld, hFabS2⟩
      have haD : a ∈ RELAT_1.dom F :=
        Eq.subst (motive := fun s => a ∈ s) hfieldRD haFld
      have hbD : b ∈ RELAT_1.dom F :=
        Eq.subst (motive := fun s => b ∈ s) hfieldRD hbFld
      have haR : a ∈ RELAT_1.field R := (th12 haFld).1
      have hbR : b ∈ RELAT_1.field R := (th12 hbFld).1
      have ⟨hFabS, _, _⟩ :=
        (restrict2_iff S (RELAT_1.rng F)
          (FUNCT_1.apply F a) (FUNCT_1.apply F b)).mp hFabS2
      apply Classical.byContradiction
      intro hnab2
      have hnabR : TARSKI.pair a b ∉ R :=
        fun hp => hnab2
          ((restrict2_iff R (RELAT_1.dom F) a b).mpr ⟨hp, haD, hbD⟩)
      have hne : a ≠ b :=
        fun heq => hnabR
          (Eq.subst (motive := fun s => TARSKI.pair a s ∈ R) heq
            ((lm1 R).mp hR.1 a haR))
      have hba : TARSKI.pair b a ∈ R :=
        Or.elim ((lm4 R).mp hR.2.2.2.1 a b haR hbR hne)
          (fun hab => (hnabR hab).elim) (fun hba => hba)
      have hbSeg : b ∈ seg R a :=
        (th1 R a b).mpr ⟨fun heq => hne heq.symm, hba⟩
      let P := restrict2 R (seg R a)
      have hPwo : isWellOrdering P := th25 hR (seg R a)
      have hfieldP : RELAT_1.field P = seg R a := th32 hR a
      have hbP : b ∈ RELAT_1.field P :=
        Eq.subst (motive := fun s => b ∈ s) hfieldP.symm hbSeg
      have hPseg : seg P b = seg R b := th27 hR hbSeg
      have hsubba : seg R b ⊆ seg R a :=
        (th29 hR hbR haR).mp hba
      have hrest1 : restrict2 P (seg P b) = restrict2 P (seg R b) :=
        congrArg (restrict2 P) hPseg
      have hrest : restrict2 P (seg P b) = restrict2 R (seg R b) :=
        hrest1.trans (th22 hsubba (R := R))
      have hpa : TARSKI.pair a (FUNCT_1.apply F a) ∈ F :=
        FUNCT_1.apply_spec haD
      have hpb : TARSKI.pair b (FUNCT_1.apply F b) ∈ F :=
        FUNCT_1.apply_spec hbD
      have ⟨_, hFaS, hisoA⟩ := (hFchar a (FUNCT_1.apply F a)).mp hpa
      have ⟨_, hFbS, hisoB⟩ := (hFchar b (FUNCT_1.apply F b)).mp hpb
      have hisoP : areIsomorphic (restrict2 P (seg P b))
          (restrict2 S (seg S (FUNCT_1.apply F b))) :=
        Eq.subst (motive := fun s =>
            areIsomorphic s (restrict2 S (seg S (FUNCT_1.apply F b))))
          hrest.symm hisoB
      have hFba : TARSKI.pair (FUNCT_1.apply F b) (FUNCT_1.apply F a) ∈ S :=
        (th51 hPwo hS hbP hFaS hFbS hisoA hisoP).2
      have heqF : FUNCT_1.apply F a = FUNCT_1.apply F b :=
        (lm3 S).mp hS.2.2.1 (FUNCT_1.apply F a) (FUNCT_1.apply F b)
          hFabS hFba
      exact hne (h1to1 a b haD hbD heqF)
  have hFiso2 : areIsomorphic (restrict2 R (RELAT_1.dom F))
      (restrict2 S (RELAT_1.rng F)) := ⟨F, hFiso⟩
  have hZR : areIsomorphic (restrict2 R Z)
      (restrict2 S (RELAT_1.rng F)) :=
    Eq.subst (motive := fun s =>
        areIsomorphic (restrict2 R s) (restrict2 S (RELAT_1.rng F)))
      hZeqD.symm hFiso2
  have hZclosed : ∀ a, a ∈ Z → ∀ b, TARSKI.pair b a ∈ R → b ∈ Z := by
    intro a haZ b hba
    exact Or.elim (Classical.em (a = b))
      (fun heq => Eq.subst (motive := fun s => s ∈ Z) heq haZ)
      (fun hne => by
        obtain ⟨c, hcS, hiso⟩ := ((hZmem a).mp haZ).2
        have haR : a ∈ RELAT_1.field R := ((hZmem a).mp haZ).1
        let P := restrict2 R (seg R a)
        let Q := restrict2 S (seg S c)
        have hPwo : isWellOrdering P := th25 hR (seg R a)
        have hFcan := def9 hPwo hiso
        have hbSeg : b ∈ seg R a :=
          (th1 R a b).mpr ⟨fun heq => hne heq.symm, hba⟩
        have hPseg : seg P b = seg R b := th27 hR hbSeg
        have hbR : b ∈ RELAT_1.field R := (RELAT_1.th15 hba).1
        have hsub : seg R b ⊆ seg R a :=
          (th29 hR hbR haR).mp hba
        have hfieldP : RELAT_1.field P = seg R a := th32 hR a
        have hbP : b ∈ RELAT_1.field P :=
          Eq.subst (motive := fun s => b ∈ s) hfieldP.symm hbSeg
        obtain ⟨d, hdQ, hisoSeg⟩ := th50 hPwo hFcan hbP
        have hfieldQ : RELAT_1.field Q = seg S c := th32 hS c
        have hdSeg : d ∈ seg S c :=
          Eq.subst (motive := fun s => d ∈ s) hfieldQ hdQ
        have hQseg : seg Q d = seg S d := th27 hS hdSeg
        have hdc : TARSKI.pair d c ∈ S := ((th1 S c d).mp hdSeg).2
        have hdS : d ∈ RELAT_1.field S := (RELAT_1.th15 hdc).1
        have hrestP : restrict2 P (seg P b) = restrict2 R (seg R b) :=
          (congrArg (restrict2 P) hPseg).trans (th22 hsub (R := R))
        have hrestQ : restrict2 Q (seg Q d) = restrict2 S (seg S d) :=
          (congrArg (restrict2 Q) hQseg).trans
            (th22 ((th29 hS hdS hcS).mp hdc) (R := S))
        have hiso1 : areIsomorphic (restrict2 P (seg P b))
            (restrict2 S (seg S d)) :=
          Eq.subst (motive := fun s =>
              areIsomorphic (restrict2 P (seg P b)) s) hrestQ hisoSeg
        have hisoB : areIsomorphic (restrict2 R (seg R b))
            (restrict2 S (seg S d)) :=
          Eq.subst (motive := fun s =>
              areIsomorphic s (restrict2 S (seg S d))) hrestP hiso1
        exact (hZmem b).mpr ⟨hbR, ⟨d, hdS, hisoB⟩⟩)
  have hRclosed : ∀ a, a ∈ RELAT_1.rng F → ∀ b, TARSKI.pair b a ∈ S →
      b ∈ RELAT_1.rng F := by
    intro a haR b hba
    exact Or.elim (Classical.em (a = b))
      (fun heq => Eq.subst (motive := fun s => s ∈ RELAT_1.rng F) heq haR)
      (fun hne => by
        obtain ⟨c, hcD, haeq⟩ := (FUNCT_1.def3 hFfun.2).mp haR
        have hpair : TARSKI.pair c a ∈ F :=
          (FUNCT_1.th1 hFfun.2 (x := c) (y := a)).mpr ⟨hcD, haeq⟩
        have ⟨hcR, haS, hiso⟩ := (hFchar c a).mp hpair
        let Q := restrict2 S (seg S a)
        let P := restrict2 R (seg R c)
        have hQwo : isWellOrdering Q := th25 hS (seg S a)
        have hisoQP : areIsomorphic Q P := th40 hiso
        have hFcan := def9 hQwo hisoQP
        have hbSeg : b ∈ seg S a :=
          (th1 S a b).mpr ⟨fun heq => hne heq.symm, hba⟩
        have hQseg : seg Q b = seg S b := th27 hS hbSeg
        have hbS : b ∈ RELAT_1.field S := (RELAT_1.th15 hba).1
        have hsub : seg S b ⊆ seg S a :=
          (th29 hS hbS haS).mp hba
        have hfieldQ : RELAT_1.field Q = seg S a := th32 hS a
        have hbQ : b ∈ RELAT_1.field Q :=
          Eq.subst (motive := fun s => b ∈ s) hfieldQ.symm hbSeg
        obtain ⟨d, hdP, hisoSeg⟩ := th50 hQwo hFcan hbQ
        have hfieldP : RELAT_1.field P = seg R c := th32 hR c
        have hdSeg : d ∈ seg R c :=
          Eq.subst (motive := fun s => d ∈ s) hfieldP hdP
        have hPseg : seg P d = seg R d := th27 hR hdSeg
        have hdc : TARSKI.pair d c ∈ R := ((th1 R c d).mp hdSeg).2
        have hdR : d ∈ RELAT_1.field R := (RELAT_1.th15 hdc).1
        have hrestQ : restrict2 Q (seg Q b) = restrict2 S (seg S b) :=
          (congrArg (restrict2 Q) hQseg).trans (th22 hsub (R := S))
        have hrestP : restrict2 P (seg P d) = restrict2 R (seg R d) :=
          (congrArg (restrict2 P) hPseg).trans
            (th22 ((th29 hR hdR hcR).mp hdc) (R := R))
        have hiso1 : areIsomorphic (restrict2 Q (seg Q b))
            (restrict2 R (seg R d)) :=
          Eq.subst (motive := fun s =>
              areIsomorphic (restrict2 Q (seg Q b)) s) hrestP hisoSeg
        have hisoS : areIsomorphic (restrict2 S (seg S b))
            (restrict2 R (seg R d)) :=
          Eq.subst (motive := fun s =>
              areIsomorphic s (restrict2 R (seg R d))) hrestQ hiso1
        have hisoR : areIsomorphic (restrict2 R (seg R d))
            (restrict2 S (seg S b)) := th40 hisoS
        have hpF : TARSKI.pair d b ∈ F :=
          (hFchar d b).mpr ⟨hdR, ⟨hbS, hisoR⟩⟩
        have hdD : d ∈ RELAT_1.dom F :=
          (RELAT_1.dom_iff F d).mpr ⟨b, hpF⟩
        have hbF : b = FUNCT_1.apply F d :=
          (FUNCT_1.apply_of_mem hFfun.2 hpF).symm
        exact (FUNCT_1.def3 hFfun.2).mpr ⟨d, hdD, hbF⟩)
  have hZcases := (th28 hR hZsub).mpr hZclosed
  have hRcases := (th28 hS hrngS).mpr hRclosed
  have hboth :
      Z = RELAT_1.field R → RELAT_1.rng F = RELAT_1.field S →
        areIsomorphic R S := by
    intro hZeq hReq
    have hisoRS : areIsomorphic
        (restrict2 R (RELAT_1.field R))
        (restrict2 S (RELAT_1.field S)) :=
      Eq.subst (motive := fun s =>
          areIsomorphic (restrict2 R (RELAT_1.field R))
            (restrict2 S s)) hReq
        (Eq.subst (motive := fun s =>
            areIsomorphic (restrict2 R s)
              (restrict2 S (RELAT_1.rng F))) hZeq hZR)
    exact th42 (th40 (restrict2_field_iso hR))
      (th42 hisoRS (restrict2_field_iso hS))
  have hRseg : Z = RELAT_1.field R →
      (∃ a, a ∈ RELAT_1.field S ∧ RELAT_1.rng F = seg S a) →
        ∃ a, a ∈ RELAT_1.field S ∧
          areIsomorphic R (restrict2 S (seg S a)) := by
    intro hZeq ⟨a, haS, hseg⟩
    refine ⟨a, haS, ?_⟩
    have hiso : areIsomorphic (restrict2 R (RELAT_1.field R))
        (restrict2 S (seg S a)) :=
      Eq.subst (motive := fun s =>
          areIsomorphic (restrict2 R (RELAT_1.field R))
            (restrict2 S s)) hseg
        (Eq.subst (motive := fun s =>
            areIsomorphic (restrict2 R s)
              (restrict2 S (RELAT_1.rng F))) hZeq hZR)
    exact th42 (th40 (restrict2_field_iso hR)) hiso
  have hSfield : RELAT_1.rng F = RELAT_1.field S →
      (∃ a, a ∈ RELAT_1.field R ∧ Z = seg R a) →
        ∃ a, a ∈ RELAT_1.field R ∧
          areIsomorphic (restrict2 R (seg R a)) S := by
    intro hReq ⟨a, haR, hseg⟩
    refine ⟨a, haR, ?_⟩
    have hiso : areIsomorphic (restrict2 R (seg R a))
        (restrict2 S (RELAT_1.field S)) :=
      Eq.subst (motive := fun s =>
          areIsomorphic (restrict2 R (seg R a)) (restrict2 S s)) hReq
        (Eq.subst (motive := fun s =>
            areIsomorphic (restrict2 R s)
              (restrict2 S (RELAT_1.rng F))) hseg hZR)
    exact th42 hiso (restrict2_field_iso hS)
  have hcontra :
      (∃ a, a ∈ RELAT_1.field R ∧ Z = seg R a) →
        (∃ b, b ∈ RELAT_1.field S ∧ RELAT_1.rng F = seg S b) →
          False := by
    intro ⟨a, haR, hZseg⟩ ⟨b, hbS, hrngseg⟩
    have hiso : areIsomorphic (restrict2 R (seg R a))
        (restrict2 S (seg S b)) :=
      Eq.subst (motive := fun s =>
          areIsomorphic (restrict2 R (seg R a)) (restrict2 S s))
        hrngseg
        (Eq.subst (motive := fun s =>
            areIsomorphic (restrict2 R s)
              (restrict2 S (RELAT_1.rng F))) hZseg hZR)
    have haZ : a ∈ Z := (hZmem a).mpr ⟨haR, ⟨b, hbS, hiso⟩⟩
    have haSeg : a ∈ seg R a :=
      Eq.subst (motive := fun s => a ∈ s) hZseg haZ
    exact ((th1 R a a).mp haSeg).1 rfl
  exact Or.elim hZcases
    (fun hZeq =>
      Or.elim hRcases
        (fun hReq => Or.inl (hboth hZeq hReq))
        (fun hseg => Or.inr (Or.inr (hRseg hZeq hseg))))
    (fun hZseg =>
      Or.elim hRcases
        (fun hReq => Or.inr (Or.inl (hSfield hReq hZseg)))
        (fun hseg => (hcontra hZseg hseg).elim))

/-- Unlabeled `WELLORD1` after `Th52` (`L1809`). -/
theorem th53 {R Y : TarskiSet.{u}} (hY : Y ⊆ RELAT_1.field R)
    (hR : isWellOrdering R) :
    areIsomorphic R (restrict2 R Y) ∨
      ∃ a, a ∈ RELAT_1.field R ∧
        areIsomorphic (restrict2 R (seg R a)) (restrict2 R Y) := by
  have hYwo : isWellOrdering (restrict2 R Y) := th25 hR Y
  have hfieldY : RELAT_1.field (restrict2 R Y) = Y := th31 hR hY
  have hnseg : ¬ ∃ a, a ∈ RELAT_1.field (restrict2 R Y) ∧
      areIsomorphic R (restrict2 (restrict2 R Y)
        (seg (restrict2 R Y) a)) := by
    intro ⟨a, haY, hiso⟩
    obtain ⟨F, hF⟩ := hiso
    have hfieldSeg : RELAT_1.field
        (restrict2 (restrict2 R Y) (seg (restrict2 R Y) a)) =
        seg (restrict2 R Y) a := th32 hYwo a
    have hrng : RELAT_1.rng F = seg (restrict2 R Y) a :=
      hF.2.2.1.trans hfieldSeg
    have hdom : RELAT_1.dom F = RELAT_1.field R := hF.2.1
    have haY2 : a ∈ Y :=
      Eq.subst (motive := fun s => a ∈ s) hfieldY haY
    have haR : a ∈ RELAT_1.field R := hY a haY2
    have haD : a ∈ RELAT_1.dom F :=
      Eq.subst (motive := fun s => a ∈ s) hdom.symm haR
    have hFaR : FUNCT_1.apply F a ∈ RELAT_1.rng F :=
      FUNCT_1.th3 hF.1.2 haD
    have hFaSeg : FUNCT_1.apply F a ∈ seg (restrict2 R Y) a :=
      Eq.subst (motive := fun s => FUNCT_1.apply F a ∈ s) hrng hFaR
    have ⟨hnea, hFaa2⟩ :=
      (th1 (restrict2 R Y) a (FUNCT_1.apply F a)).mp hFaSeg
    have hFaa : TARSKI.pair (FUNCT_1.apply F a) a ∈ R :=
      ((restrict2_iff R Y (FUNCT_1.apply F a) a).mp hFaa2).1
    have hmono : ∀ x y, TARSKI.pair x y ∈ R → x ≠ y →
        TARSKI.pair (FUNCT_1.apply F x) (FUNCT_1.apply F y) ∈ R ∧
          FUNCT_1.apply F x ≠ FUNCT_1.apply F y := by
      intro x y hxy hne
      have ⟨hpS, hFne⟩ := th36 hF hxy hne
      have hpY : TARSKI.pair (FUNCT_1.apply F x) (FUNCT_1.apply F y) ∈
          restrict2 R Y :=
        ((restrict2_iff (restrict2 R Y) (seg (restrict2 R Y) a)
          (FUNCT_1.apply F x) (FUNCT_1.apply F y)).mp hpS).1
      exact ⟨((restrict2_iff R Y (FUNCT_1.apply F x)
        (FUNCT_1.apply F y)).mp hpY).1, hFne⟩
    have hsegY : seg (restrict2 R Y) a ⊆ Y :=
      fun z hz =>
        Eq.subst (motive := fun s => z ∈ s) hfieldY
          (th9 (restrict2 R Y) a z hz)
    have hrngR : RELAT_1.rng F ⊆ RELAT_1.field R :=
      fun z hz => hY z
        (hsegY z (Eq.subst (motive := fun s => z ∈ s) hrng hz))
    have hab : TARSKI.pair a (FUNCT_1.apply F a) ∈ R :=
      th35 hR hF.1 hdom hrngR hmono haR
    exact hnea ((lm3 R).mp hR.2.2.1 a (FUNCT_1.apply F a) hab hFaa).symm
  exact Or.elim (th52 hR hYwo)
    (fun hiso => Or.inl hiso)
    (fun hrest =>
      Or.elim hrest
        (fun hex => Or.inr hex)
        (fun hex => (hnseg hex).elim))

/-- Unlabeled `WELLORD1` after `L1809` (`L1853`). -/
theorem th54 {R S : TarskiSet.{u}} (hiso : areIsomorphic R S)
    (hR : isWellOrdering R) : isWellOrdering S :=
  hiso.elim fun _ hF => th44 hR hF

end WELLORD1
