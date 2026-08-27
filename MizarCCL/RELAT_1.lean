import MizarCCL.SUBSET_1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/relat_1.miz`.
Authors: Edmund Woronowicz (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Relations and Their Basic Properties

1–1 Lean rendering of Mizar article `RELAT_1`
(`vendor/mml/relat_1.miz`). A relation is a set of Kuratowski pairs.
`dom` / `rng` are `XTUPLE_0.proj1` / `proj2`. Mizar `RELAT_1:4`–`6`,
`116`–`117`, and `136`–`137` are canceled and omitted. Import is
`SUBSET_1` only (`XTUPLE_0` arrives via `ZFMISC_1`).
-/

universe u

open TarskiSet TARSKI

namespace RELAT_1

variable {A X X1 X2 Y Y1 Y2 a b c d x y z P P1 P2 Q R S : TarskiSet.{u}}

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

/-! ## Relation-like (`RELAT_1:def 1`) -/

def isRelation (IT : TarskiSet.{u}) : Prop :=
  ∀ x, x ∈ IT → ∃ y z, x = TARSKI.pair y z

theorem def1 (IT : TarskiSet.{u}) :
    isRelation IT ↔ ∀ x, x ∈ IT → ∃ y z, x = TARSKI.pair y z :=
  Iff.rfl

theorem empty_isRelation : isRelation (∅ : TarskiSet.{u}) :=
  fun x hx => ((XBOOLE_0.empty_iff x).mp hx).elim

theorem subset_isRelation {A R : TarskiSet.{u}} (hR : isRelation R)
    (hA : A ⊆ R) : isRelation A :=
  fun x hx => hR x (hA x hx)

theorem inter_isRelation {P X : TarskiSet.{u}} (hP : isRelation P) :
    isRelation (P ∩ X) :=
  subset_isRelation hP XBOOLE_1.th17

theorem diff_isRelation {P X : TarskiSet.{u}} (hP : isRelation P) :
    isRelation (P \ X) :=
  subset_isRelation hP XBOOLE_1.th36

theorem union_isRelation {P R : TarskiSet.{u}} (hP : isRelation P)
    (hR : isRelation R) : isRelation (P ∪ R) :=
  fun x hx => ((XBOOLE_0.def3 P R x).mp hx).elim (hP x) (hR x)

theorem singleton_pair_isRelation (a b : TarskiSet.{u}) :
    isRelation (TARSKI.singleton (TARSKI.pair a b)) :=
  fun x hx => ⟨a, b, (singleton_iff (TARSKI.pair a b) x).mp hx⟩

theorem product_isRelation (a b : TarskiSet.{u}) :
    isRelation (ZFMISC_1.product a b) :=
  fun z hz =>
    let ⟨x, y, _, _, heq⟩ := (ZFMISC_1.def2 a b z).mp hz
    ⟨x, y, heq⟩

/-! ## `RELAT_1:sch RelExistence` -/

theorem sch_RelExistence (A B : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop) :
    ∃ R, isRelation R ∧
      ∀ x y, TARSKI.pair x y ∈ R ↔ x ∈ A ∧ y ∈ B ∧ P x y := by
  obtain ⟨R, hR⟩ :=
    XBOOLE_0.sch_separation (ZFMISC_1.product A B)
      (fun p => ∃ x y, p = TARSKI.pair x y ∧ P x y)
  refine ⟨R, ?rel, ?char⟩
  · intro p hp
    obtain ⟨hpP, x, y, heq, _⟩ := (hR p).mp hp
    exact ⟨x, y, heq⟩
  · intro x y
    constructor
    · intro hp
      have ⟨hpP, x', y', heq, hP⟩ := (hR _).mp hp
      have ⟨hx, hy⟩ := TARSKI.pair_inj.mp heq
      have ⟨hxA, hyB⟩ := (ZFMISC_1.th87 (x := x') (y := y') (X := A) (Y := B)).mp
        (heq ▸ hpP)
      exact ⟨hx ▸ hxA, hy ▸ hyB, hx ▸ hy ▸ hP⟩
    · intro ⟨hxA, hyB, hP⟩
      exact (hR _).mpr
        ⟨(ZFMISC_1.th87 (x := x) (y := y) (X := A) (Y := B)).mpr ⟨hxA, hyB⟩,
          ⟨x, y, rfl, hP⟩⟩

theorem rel_eq {P R : TarskiSet.{u}} (hP : isRelation P) (hR : isRelation R)
    (h : ∀ a b, TARSKI.pair a b ∈ P ↔ TARSKI.pair a b ∈ R) : P = R := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    obtain ⟨a, b, heq⟩ := hP x hx
    exact heq ▸ (h a b).mp (heq ▸ hx)
  · intro hx
    obtain ⟨a, b, heq⟩ := hR x hx
    exact heq ▸ (h a b).mpr (heq ▸ hx)

theorem rel_subset {P A : TarskiSet.{u}} (hP : isRelation P)
    (h : ∀ a b, TARSKI.pair a b ∈ P → TARSKI.pair a b ∈ A) : P ⊆ A :=
  fun x hx =>
    let ⟨a, b, heq⟩ := hP x hx
    heq ▸ h a b (heq ▸ hx)

/-! ## Domain, range, field -/

noncomputable def dom (R : TarskiSet.{u}) : TarskiSet.{u} := XTUPLE_0.proj1 R
noncomputable def rng (R : TarskiSet.{u}) : TarskiSet.{u} := XTUPLE_0.proj2 R

theorem dom_iff (R x : TarskiSet.{u}) :
    x ∈ dom R ↔ ∃ y, TARSKI.pair x y ∈ R :=
  XTUPLE_0.def4 R x

theorem rng_iff (R y : TarskiSet.{u}) :
    y ∈ rng R ↔ ∃ x, TARSKI.pair x y ∈ R :=
  XTUPLE_0.def5 R y

theorem pair_mem_dom {R x y : TarskiSet.{u}} (h : TARSKI.pair x y ∈ R) :
    x ∈ dom R :=
  (dom_iff R x).mpr ⟨y, h⟩

theorem pair_mem_rng {R x y : TarskiSet.{u}} (h : TARSKI.pair x y ∈ R) :
    y ∈ rng R :=
  (rng_iff R y).mpr ⟨x, h⟩

/-- `RELAT_1:1` (`Th1`) -/
theorem th1 : dom (P ∪ R) = dom P ∪ dom R :=
  XTUPLE_0.th22 P R

/-- `RELAT_1:2` (`Th2`) -/
theorem th2 : dom (P ∩ R) ⊆ dom P ∩ dom R :=
  XTUPLE_0.th23 P R

/-- `RELAT_1:3` -/
theorem th3 : dom P \ dom R ⊆ dom (P \ R) :=
  XTUPLE_0.th24 P R

/-- `RELAT_1:7` (`Th7`) -/
theorem th7 {R : TarskiSet.{u}} (hR : isRelation R) :
    R ⊆ ZFMISC_1.product (dom R) (rng R) :=
  rel_subset hR fun a b hp =>
    (ZFMISC_1.th87 (x := a) (y := b) (X := dom R) (Y := rng R)).mpr
      ⟨pair_mem_dom hp, pair_mem_rng hp⟩

/-- `RELAT_1:8` -/
theorem th8 {R : TarskiSet.{u}} (hR : isRelation R) :
    R ∩ ZFMISC_1.product (dom R) (rng R) = R :=
  XBOOLE_1.th28 (th7 hR)

/-- `RELAT_1:9` (`Th9`) -/
theorem th9 (hR : R = TARSKI.singleton (TARSKI.pair x y)) :
    dom R = TARSKI.singleton x ∧ rng R = TARSKI.singleton y := by
  constructor
  · apply eq_of_mem
    intro z
    constructor
    · intro hz
      obtain ⟨b, hp⟩ := (dom_iff R z).mp hz
      have : TARSKI.pair z b = TARSKI.pair x y :=
        (singleton_iff (TARSKI.pair x y) _).mp (hR ▸ hp)
      exact (singleton_iff x z).mpr (TARSKI.pair_inj.mp this).1
    · intro hz
      have hzx : z = x := (singleton_iff x z).mp hz
      exact (dom_iff R z).mpr ⟨y, hR ▸ (singleton_iff _ _).mpr
        (congrArg (fun w => TARSKI.pair w y) hzx)⟩
  · apply eq_of_mem
    intro z
    constructor
    · intro hz
      obtain ⟨a, hp⟩ := (rng_iff R z).mp hz
      have : TARSKI.pair a z = TARSKI.pair x y :=
        (singleton_iff (TARSKI.pair x y) _).mp (hR ▸ hp)
      exact (singleton_iff y z).mpr (TARSKI.pair_inj.mp this).2
    · intro hz
      have hzy : z = y := (singleton_iff y z).mp hz
      exact (rng_iff R z).mpr ⟨x, hR ▸ (singleton_iff _ _).mpr
        (congrArg (TARSKI.pair x) hzy)⟩

/-- `RELAT_1:10` -/
theorem th10 (hR : R = upair (TARSKI.pair a b) (TARSKI.pair x y)) :
    dom R = upair a x ∧ rng R = upair b y := by
  constructor
  · apply eq_of_mem
    intro z
    constructor
    · intro hz
      obtain ⟨c, hp⟩ := (dom_iff R z).mp hz
      have hpair := (upair_iff (TARSKI.pair a b) (TARSKI.pair x y)
        (TARSKI.pair z c)).mp (hR ▸ hp)
      exact (upair_iff a x z).mpr <|
        hpair.elim (fun h => Or.inl (TARSKI.pair_inj.mp h).1)
          (fun h => Or.inr (TARSKI.pair_inj.mp h).1)
    · intro hz
      rcases (upair_iff a x z).mp hz with hza | hzx
      · exact (dom_iff R z).mpr ⟨b, hR ▸ (upair_iff _ _ _).mpr
          (Or.inl (congrArg (fun w => TARSKI.pair w b) hza))⟩
      · exact (dom_iff R z).mpr ⟨y, hR ▸ (upair_iff _ _ _).mpr
          (Or.inr (congrArg (fun w => TARSKI.pair w y) hzx))⟩
  · apply eq_of_mem
    intro z
    constructor
    · intro hz
      obtain ⟨d, hp⟩ := (rng_iff R z).mp hz
      have hpair := (upair_iff (TARSKI.pair a b) (TARSKI.pair x y)
        (TARSKI.pair d z)).mp (hR ▸ hp)
      exact (upair_iff b y z).mpr <|
        hpair.elim (fun h => Or.inl (TARSKI.pair_inj.mp h).2)
          (fun h => Or.inr (TARSKI.pair_inj.mp h).2)
    · intro hz
      rcases (upair_iff b y z).mp hz with hzb | hzy
      · exact (rng_iff R z).mpr ⟨a, hR ▸ (upair_iff _ _ _).mpr
          (Or.inl (congrArg (TARSKI.pair a) hzb))⟩
      · exact (rng_iff R z).mpr ⟨x, hR ▸ (upair_iff _ _ _).mpr
          (Or.inr (congrArg (TARSKI.pair x) hzy))⟩

/-- `RELAT_1:11` (`Th11`) -/
theorem th11 (h : P ⊆ R) : dom P ⊆ dom R ∧ rng P ⊆ rng R :=
  ⟨XTUPLE_0.th10 h, XTUPLE_0.th11 h⟩

/-- `RELAT_1:12` (`Th12`) -/
theorem th12 : rng (P ∪ R) = rng P ∪ rng R :=
  XTUPLE_0.th26 P R

/-- `RELAT_1:13` (`Th13`) -/
theorem th13 : rng (P ∩ R) ⊆ rng P ∩ rng R :=
  XTUPLE_0.th27 P R

/-- `RELAT_1:14` -/
theorem th14 : rng P \ rng R ⊆ rng (P \ R) :=
  XTUPLE_0.th28 P R

noncomputable def field (R : TarskiSet.{u}) : TarskiSet.{u} :=
  dom R ∪ rng R

/-- `RELAT_1:15` -/
theorem th15 (h : TARSKI.pair a b ∈ R) : a ∈ field R ∧ b ∈ field R :=
  ⟨(XBOOLE_0.def3 (dom R) (rng R) a).mpr (Or.inl (pair_mem_dom h)),
    (XBOOLE_0.def3 (dom R) (rng R) b).mpr (Or.inr (pair_mem_rng h))⟩

/-- `RELAT_1:16` -/
theorem th16 (h : P ⊆ R) : field P ⊆ field R :=
  XBOOLE_1.th13 (th11 h).1 (th11 h).2

/-- `RELAT_1:17` (`Th17`) -/
theorem th17 :
    field (TARSKI.singleton (TARSKI.pair x y)) = upair x y := by
  have ⟨hd, hr⟩ := th9 (R := TARSKI.singleton (TARSKI.pair x y)) rfl
  exact (hd ▸ hr ▸ rfl : field (TARSKI.singleton (TARSKI.pair x y)) = TARSKI.singleton x ∪ TARSKI.singleton y).trans
    ENUMSET1.th1.symm

/-- `RELAT_1:18` -/
theorem th18 : field (P ∪ R) = field P ∪ field R := by
  have h1 : field (P ∪ R) = (dom P ∪ dom R) ∪ rng (P ∪ R) :=
    congrArg (fun s => s ∪ rng (P ∪ R)) (th1 (P := P) (R := R))
  have h2 : (dom P ∪ dom R) ∪ rng (P ∪ R) =
      (dom P ∪ dom R) ∪ (rng P ∪ rng R) :=
    congrArg (fun s => (dom P ∪ dom R) ∪ s) (th12 (P := P) (R := R))
  have h3 : (dom P ∪ dom R) ∪ (rng P ∪ rng R) =
      ((dom P ∪ rng P) ∪ (dom R ∪ rng R)) := by
    have u1 := XBOOLE_1.th4 (X := dom P ∪ dom R) (Y := rng P) (Z := rng R)
    have u2 := XBOOLE_1.th4 (X := dom P) (Y := dom R) (Z := rng P)
    -- ((dom P ∪ dom R) ∪ rng P) ∪ rng R
    -- rearrange to (dom P ∪ rng P) ∪ (dom R ∪ rng R)
    apply eq_of_mem
    intro w
    constructor
    · intro hw
      have hw1 := (XBOOLE_0.def3 (dom P ∪ dom R) (rng P ∪ rng R) w).mp hw
      rcases hw1 with hdom | hrng
      · rcases (XBOOLE_0.def3 (dom P) (dom R) w).mp hdom with hp | hr
        · exact (XBOOLE_0.def3 (field P) (field R) w).mpr
            (Or.inl ((XBOOLE_0.def3 (dom P) (rng P) w).mpr (Or.inl hp)))
        · exact (XBOOLE_0.def3 (field P) (field R) w).mpr
            (Or.inr ((XBOOLE_0.def3 (dom R) (rng R) w).mpr (Or.inl hr)))
      · rcases (XBOOLE_0.def3 (rng P) (rng R) w).mp hrng with hp | hr
        · exact (XBOOLE_0.def3 (field P) (field R) w).mpr
            (Or.inl ((XBOOLE_0.def3 (dom P) (rng P) w).mpr (Or.inr hp)))
        · exact (XBOOLE_0.def3 (field P) (field R) w).mpr
            (Or.inr ((XBOOLE_0.def3 (dom R) (rng R) w).mpr (Or.inr hr)))
    · intro hw
      rcases (XBOOLE_0.def3 (field P) (field R) w).mp hw with hp | hr
      · rcases (XBOOLE_0.def3 (dom P) (rng P) w).mp hp with hd | hrng
        · exact (XBOOLE_0.def3 (dom P ∪ dom R) (rng P ∪ rng R) w).mpr
            (Or.inl ((XBOOLE_0.def3 (dom P) (dom R) w).mpr (Or.inl hd)))
        · exact (XBOOLE_0.def3 (dom P ∪ dom R) (rng P ∪ rng R) w).mpr
            (Or.inr ((XBOOLE_0.def3 (rng P) (rng R) w).mpr (Or.inl hrng)))
      · rcases (XBOOLE_0.def3 (dom R) (rng R) w).mp hr with hd | hrng
        · exact (XBOOLE_0.def3 (dom P ∪ dom R) (rng P ∪ rng R) w).mpr
            (Or.inl ((XBOOLE_0.def3 (dom P) (dom R) w).mpr (Or.inr hd)))
        · exact (XBOOLE_0.def3 (dom P ∪ dom R) (rng P ∪ rng R) w).mpr
            (Or.inr ((XBOOLE_0.def3 (rng P) (rng R) w).mpr (Or.inr hrng)))
  exact (h1.trans h2).trans h3

/-- `RELAT_1:19` -/
theorem th19 : field (P ∩ R) ⊆ field P ∩ field R := by
  intro x hx
  have hx1 := (XBOOLE_0.def3 (dom (P ∩ R)) (rng (P ∩ R)) x).mp hx
  have hdom := th2 (P := P) (R := R)
  have hrng := th13 (P := P) (R := R)
  have : x ∈ dom P ∩ dom R ∨ x ∈ rng P ∩ rng R :=
    hx1.elim (fun h => Or.inl (hdom x h)) (fun h => Or.inr (hrng x h))
  have hP : x ∈ field P :=
    this.elim
      (fun h => (XBOOLE_0.def3 (dom P) (rng P) x).mpr
        (Or.inl ((XBOOLE_0.def4 (dom P) (dom R) x).mp h).1))
      (fun h => (XBOOLE_0.def3 (dom P) (rng P) x).mpr
        (Or.inr ((XBOOLE_0.def4 (rng P) (rng R) x).mp h).1))
  have hR : x ∈ field R :=
    this.elim
      (fun h => (XBOOLE_0.def3 (dom R) (rng R) x).mpr
        (Or.inl ((XBOOLE_0.def4 (dom P) (dom R) x).mp h).2))
      (fun h => (XBOOLE_0.def3 (dom R) (rng R) x).mpr
        (Or.inr ((XBOOLE_0.def4 (rng P) (rng R) x).mp h).2))
  exact (XBOOLE_0.def4 (field P) (field R) x).mpr ⟨hP, hR⟩

/-! ## Converse `R~` (`RELAT_1:def 7`) -/

noncomputable def converse (R : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (sch_RelExistence (rng R) (dom R) (fun x y => TARSKI.pair y x ∈ R))

theorem converse_isRelation (R : TarskiSet.{u}) : isRelation (converse R) :=
  (Classical.choose_spec
    (sch_RelExistence (rng R) (dom R) (fun x y => TARSKI.pair y x ∈ R))).1

theorem converse_char (R : TarskiSet.{u}) :
    ∀ x y, TARSKI.pair x y ∈ converse R ↔
      x ∈ rng R ∧ y ∈ dom R ∧ TARSKI.pair y x ∈ R :=
  (Classical.choose_spec
    (sch_RelExistence (rng R) (dom R) (fun x y => TARSKI.pair y x ∈ R))).2

theorem def7 (R x y : TarskiSet.{u}) :
    TARSKI.pair x y ∈ converse R ↔ TARSKI.pair y x ∈ R := by
  constructor
  · intro h
    exact (converse_char R x y).mp h |>.2.2
  · intro h
    exact (converse_char R x y).mpr ⟨pair_mem_rng h, pair_mem_dom h, h⟩

/-- `RELAT_1:20` (`Th20`) -/
theorem th20 : rng R = dom (converse R) ∧ dom R = rng (converse R) := by
  constructor
  · apply eq_of_mem
    intro u
    constructor
    · intro hu
      obtain ⟨x, hp⟩ := (rng_iff R u).mp hu
      exact (dom_iff (converse R) u).mpr ⟨x, (def7 R u x).mpr hp⟩
    · intro hu
      obtain ⟨x, hp⟩ := (dom_iff (converse R) u).mp hu
      exact (rng_iff R u).mpr ⟨x, (def7 R u x).mp hp⟩
  · apply eq_of_mem
    intro u
    constructor
    · intro hu
      obtain ⟨x, hp⟩ := (dom_iff R u).mp hu
      exact (rng_iff (converse R) u).mpr ⟨x, (def7 R x u).mpr hp⟩
    · intro hu
      obtain ⟨x, hp⟩ := (rng_iff (converse R) u).mp hu
      exact (dom_iff R u).mpr ⟨x, (def7 R x u).mp hp⟩

/-- `RELAT_1:21` -/
theorem th21 : field R = field (converse R) := by
  have ⟨h1, h2⟩ := th20 (R := R)
  exact (h2.symm ▸ h1 ▸ rfl : field R = rng (converse R) ∪ dom (converse R)).trans
    (XBOOLE_0.union_comm (rng (converse R)) (dom (converse R)))

theorem converse_involutive {R : TarskiSet.{u}} (hR : isRelation R) :
    converse (converse R) = R :=
  rel_eq (converse_isRelation _) hR fun x y =>
    (def7 (converse R) x y).trans (def7 R y x)

/-! ## Composition `P * R` (`RELAT_1:def 8`) -/

noncomputable def comp (P R : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (sch_RelExistence (XTUPLE_0.proj1 P) (XTUPLE_0.proj2 R)
      (fun x y => ∃ z, TARSKI.pair x z ∈ P ∧ TARSKI.pair z y ∈ R))

theorem comp_isRelation (P R : TarskiSet.{u}) : isRelation (comp P R) :=
  (Classical.choose_spec
    (sch_RelExistence (XTUPLE_0.proj1 P) (XTUPLE_0.proj2 R)
      (fun x y => ∃ z, TARSKI.pair x z ∈ P ∧ TARSKI.pair z y ∈ R))).1

theorem def8 (P R x y : TarskiSet.{u}) :
    TARSKI.pair x y ∈ comp P R ↔
      ∃ z, TARSKI.pair x z ∈ P ∧ TARSKI.pair z y ∈ R := by
  have h := (Classical.choose_spec
    (sch_RelExistence (XTUPLE_0.proj1 P) (XTUPLE_0.proj2 R)
      (fun x y => ∃ z, TARSKI.pair x z ∈ P ∧ TARSKI.pair z y ∈ R))).2 x y
  constructor
  · intro hp
    exact (h.mp hp).2.2
  · intro ⟨z, hzP, hzR⟩
    exact h.mpr ⟨pair_mem_dom hzP, pair_mem_rng hzR, ⟨z, hzP, hzR⟩⟩

/-- `RELAT_1:25` (`Th25`) -/
theorem th25 : dom (comp P R) ⊆ dom P := by
  intro x hx
  obtain ⟨y, hp⟩ := (dom_iff (comp P R) x).mp hx
  obtain ⟨z, hzP, _⟩ := (def8 P R x y).mp hp
  exact pair_mem_dom hzP

/-- `RELAT_1:26` (`Th26`) -/
theorem th26 : rng (comp P R) ⊆ rng R := by
  intro y hy
  obtain ⟨x, hp⟩ := (rng_iff (comp P R) y).mp hy
  obtain ⟨z, _, hzR⟩ := (def8 P R x y).mp hp
  exact pair_mem_rng hzR

/-- `RELAT_1:36` (`Th36`) -/
theorem th36 {P R Q : TarskiSet.{u}} :
    comp (comp P R) Q = comp P (comp R Q) :=
  rel_eq (comp_isRelation _ _) (comp_isRelation _ _) fun a b => by
    constructor
    · intro h
      obtain ⟨y, hPR, hQ⟩ := (def8 (comp P R) Q a b).mp h
      obtain ⟨x, hP, hR⟩ := (def8 P R a y).mp hPR
      exact (def8 P (comp R Q) a b).mpr
        ⟨x, hP, (def8 R Q x b).mpr ⟨y, hR, hQ⟩⟩
    · intro h
      obtain ⟨y, hP, hRQ⟩ := (def8 P (comp R Q) a b).mp h
      obtain ⟨x, hR, hQ⟩ := (def8 R Q y b).mp hRQ
      exact (def8 (comp P R) Q a b).mpr
        ⟨x, (def8 P R a x).mpr ⟨y, hP, hR⟩, hQ⟩

/-- `RELAT_1:37` (`Th37`) -/
theorem th37 {R : TarskiSet.{u}} (hR : isRelation R)
    (h : ∀ x y, TARSKI.pair x y ∉ R) : R = (∅ : TarskiSet.{u}) :=
  eq_of_mem fun p =>
    ⟨fun hp =>
      let ⟨x, y, heq⟩ := hR p hp
      (h x y (heq ▸ hp)).elim,
      fun hp => ((XBOOLE_0.empty_iff p).mp hp).elim⟩

/-- `RELAT_1:38` (`Th38`) -/
theorem th38 : dom (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) ∧
    rng (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) :=
  ⟨XBOOLE_0.empty_eq (XTUPLE_0.proj1_empty XBOOLE_0.emptySet_isEmpty),
    XBOOLE_0.empty_eq (XTUPLE_0.proj2_empty XBOOLE_0.emptySet_isEmpty)⟩

/-! ## Identity `id X` (`RELAT_1:def 10`) -/

noncomputable def id (X : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (sch_RelExistence X X (fun x y => x = y))

theorem id_isRelation (X : TarskiSet.{u}) : isRelation (id X) :=
  (Classical.choose_spec (sch_RelExistence X X (fun x y => x = y))).1

theorem def10 (X x y : TarskiSet.{u}) :
    TARSKI.pair x y ∈ id X ↔ x ∈ X ∧ x = y := by
  have h := (Classical.choose_spec
    (sch_RelExistence X X (fun x y => x = y))).2 x y
  constructor
  · intro hp
    have ⟨hx, _, heq⟩ := h.mp hp
    exact ⟨hx, heq⟩
  · intro ⟨hx, heq⟩
    exact h.mpr ⟨hx, heq ▸ hx, heq⟩

theorem id_dom (X : TarskiSet.{u}) : dom (id X) = X := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    obtain ⟨y, hp⟩ := (dom_iff (id X) x).mp hx
    exact (def10 X x y).mp hp |>.1
  · intro hx
    exact (dom_iff (id X) x).mpr ⟨x, (def10 X x x).mpr ⟨hx, rfl⟩⟩

theorem id_rng (X : TarskiSet.{u}) : rng (id X) = X := by
  apply eq_of_mem
  intro y
  constructor
  · intro hy
    obtain ⟨x, hp⟩ := (rng_iff (id X) y).mp hy
    have ⟨hx, heq⟩ := (def10 X x y).mp hp
    exact heq ▸ hx
  · intro hy
    exact (rng_iff (id X) y).mpr ⟨y, (def10 X y y).mpr ⟨hy, rfl⟩⟩

/-! ## Restriction `R|X` (`RELAT_1:def 11`) -/

noncomputable def restrict (R X : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (sch_RelExistence (dom R) (rng R)
      (fun x y => x ∈ X ∧ TARSKI.pair x y ∈ R))

theorem restrict_isRelation (R X : TarskiSet.{u}) : isRelation (restrict R X) :=
  (Classical.choose_spec
    (sch_RelExistence (dom R) (rng R)
      (fun x y => x ∈ X ∧ TARSKI.pair x y ∈ R))).1

theorem def11 (R X x y : TarskiSet.{u}) :
    TARSKI.pair x y ∈ restrict R X ↔ x ∈ X ∧ TARSKI.pair x y ∈ R := by
  have h := (Classical.choose_spec
    (sch_RelExistence (dom R) (rng R)
      (fun x y => x ∈ X ∧ TARSKI.pair x y ∈ R))).2 x y
  constructor
  · intro hp
    exact (h.mp hp).2.2
  · intro ⟨hx, hp⟩
    exact h.mpr ⟨pair_mem_dom hp, pair_mem_rng hp, ⟨hx, hp⟩⟩

/-- `RELAT_1:57` (`Th57`) -/
theorem th57 : x ∈ dom (restrict R X) ↔ x ∈ X ∧ x ∈ dom R := by
  constructor
  · intro hx
    obtain ⟨y, hp⟩ := (dom_iff (restrict R X) x).mp hx
    have ⟨hxX, hpR⟩ := (def11 R X x y).mp hp
    exact ⟨hxX, pair_mem_dom hpR⟩
  · intro ⟨hxX, hxD⟩
    obtain ⟨y, hp⟩ := (dom_iff R x).mp hxD
    exact (dom_iff (restrict R X) x).mpr ⟨y, (def11 R X x y).mpr ⟨hxX, hp⟩⟩

/-! ## Range restriction `Y|`R` (`RELAT_1:def 12`) -/

noncomputable def restrictRng (Y R : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (sch_RelExistence (dom R) (rng R)
      (fun x y => y ∈ Y ∧ TARSKI.pair x y ∈ R))

theorem restrictRng_isRelation (Y R : TarskiSet.{u}) :
    isRelation (restrictRng Y R) :=
  (Classical.choose_spec
    (sch_RelExistence (dom R) (rng R)
      (fun x y => y ∈ Y ∧ TARSKI.pair x y ∈ R))).1

theorem def12 (Y R x y : TarskiSet.{u}) :
    TARSKI.pair x y ∈ restrictRng Y R ↔ y ∈ Y ∧ TARSKI.pair x y ∈ R := by
  have h := (Classical.choose_spec
    (sch_RelExistence (dom R) (rng R)
      (fun x y => y ∈ Y ∧ TARSKI.pair x y ∈ R))).2 x y
  constructor
  · intro hp
    exact (h.mp hp).2.2
  · intro ⟨hy, hp⟩
    exact h.mpr ⟨pair_mem_dom hp, pair_mem_rng hp, ⟨hy, hp⟩⟩

/-! ## Image `R.:X` (`RELAT_1:def 13`) -/

noncomputable def image (R X : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (XBOOLE_0.sch_separation (rng R)
      (fun y => ∃ x, TARSKI.pair x y ∈ R ∧ x ∈ X))

theorem def13 (R X y : TarskiSet.{u}) :
    y ∈ image R X ↔ ∃ x, TARSKI.pair x y ∈ R ∧ x ∈ X := by
  have h := Classical.choose_spec
    (XBOOLE_0.sch_separation (rng R)
      (fun y => ∃ x, TARSKI.pair x y ∈ R ∧ x ∈ X)) y
  constructor
  · intro hy
    exact (h.mp hy).2
  · intro ⟨x, hp, hx⟩
    exact h.mpr ⟨pair_mem_rng hp, ⟨x, hp, hx⟩⟩

/-- `RELAT_1:110` (`Th110`) -/
theorem th110 : y ∈ image R X ↔
    ∃ x, x ∈ dom R ∧ TARSKI.pair x y ∈ R ∧ x ∈ X :=
  (def13 R X y).trans
    ⟨fun ⟨x, hp, hx⟩ => ⟨x, pair_mem_dom hp, hp, hx⟩,
      fun ⟨x, _, hp, hx⟩ => ⟨x, hp, hx⟩⟩

/-! ## Inverse image `R"Y` (`RELAT_1:def 14`) -/

noncomputable def invimage (R Y : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (XBOOLE_0.sch_separation (dom R)
      (fun x => ∃ y, TARSKI.pair x y ∈ R ∧ y ∈ Y))

theorem def14 (R Y x : TarskiSet.{u}) :
    x ∈ invimage R Y ↔ ∃ y, TARSKI.pair x y ∈ R ∧ y ∈ Y := by
  have h := Classical.choose_spec
    (XBOOLE_0.sch_separation (dom R)
      (fun x => ∃ y, TARSKI.pair x y ∈ R ∧ y ∈ Y)) x
  constructor
  · intro hx
    exact (h.mp hx).2
  · intro ⟨y, hp, hy⟩
    exact h.mpr ⟨pair_mem_dom hp, ⟨y, hp, hy⟩⟩

/-- `RELAT_1:131` (`Th131`) -/
theorem th131 : x ∈ invimage R Y ↔
    ∃ y, y ∈ rng R ∧ TARSKI.pair x y ∈ R ∧ y ∈ Y :=
  (def14 R Y x).trans
    ⟨fun ⟨y, hp, hy⟩ => ⟨y, pair_mem_rng hp, hp, hy⟩,
      fun ⟨y, _, hp, hy⟩ => ⟨y, hp, hy⟩⟩

/-- `Im(R,x)` is `R.:{x}`. -/
noncomputable def Im (R x : TarskiSet.{u}) : TarskiSet.{u} :=
  image R (TARSKI.singleton x)

/-- `Coim(R,x)` is `R"{x}`. -/
noncomputable def Coim (R x : TarskiSet.{u}) : TarskiSet.{u} :=
  invimage R (TARSKI.singleton x)

def isNonEmptyRel (R : TarskiSet.{u}) : Prop :=
  ¬ XBOOLE_0.isEmpty R

def isEmptyYielding (R : TarskiSet.{u}) : Prop :=
  (∅ : TarskiSet.{u}) ∉ rng R

theorem def9 (R : TarskiSet.{u}) :
    isEmptyYielding R ↔ (∅ : TarskiSet.{u}) ∉ rng R := Iff.rfl

def isXdefined (R X : TarskiSet.{u}) : Prop := dom R ⊆ X
def isXvalued (R X : TarskiSet.{u}) : Prop := rng R ⊆ X

theorem def18 (R X : TarskiSet.{u}) : isXdefined R X ↔ dom R ⊆ X := Iff.rfl
theorem def19 (R X : TarskiSet.{u}) : isXvalued R X ↔ rng R ⊆ X := Iff.rfl

/-- `Lm1`. -/
theorem lm1 {R X : TarskiSet.{u}} (h : isXdefined R X) : dom R ⊆ X := h

/-- `RELAT_1:22` -/
theorem th22 : converse (P ∩ R) = converse P ∩ converse R :=
  rel_eq (converse_isRelation _)
    (inter_isRelation (converse_isRelation P)) fun x y =>
    (def7 (P ∩ R) x y).trans <|
      (XBOOLE_0.def4 P R (TARSKI.pair y x)).trans <|
        Iff.trans
          (and_congr (def7 P x y).symm (def7 R x y).symm)
          (XBOOLE_0.def4 (converse P) (converse R) (TARSKI.pair x y)).symm

/-- `RELAT_1:23` -/
theorem th23 : converse (P ∪ R) = converse P ∪ converse R :=
  rel_eq (converse_isRelation _)
    (union_isRelation (converse_isRelation P) (converse_isRelation R))
    fun x y =>
    (def7 (P ∪ R) x y).trans <|
      (XBOOLE_0.def3 P R (TARSKI.pair y x)).trans <|
        Iff.trans
          (or_congr (def7 P x y).symm (def7 R x y).symm)
          (XBOOLE_0.def3 (converse P) (converse R) (TARSKI.pair x y)).symm

/-- `RELAT_1:24` -/
theorem th24 : converse (P \ R) = converse P \ converse R :=
  rel_eq (converse_isRelation _)
    (diff_isRelation (converse_isRelation P)) fun x y =>
    (def7 (P \ R) x y).trans <|
      (XBOOLE_0.def5 P R (TARSKI.pair y x)).trans <|
        Iff.trans
          (and_congr (def7 P x y).symm (not_congr (def7 R x y).symm))
          (XBOOLE_0.def5 (converse P) (converse R) (TARSKI.pair x y)).symm

/-- `RELAT_1:27` -/
theorem th27 (h : rng R ⊆ dom P) : dom (comp R P) = dom R := by
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · exact th25 (P := R) (R := P)
  · intro x hx
    obtain ⟨y, hp⟩ := (dom_iff R x).mp hx
    have hy : y ∈ dom P := h y (pair_mem_rng hp)
    obtain ⟨z, hz⟩ := (dom_iff P y).mp hy
    exact (dom_iff (comp R P) x).mpr
      ⟨z, (def8 R P x z).mpr ⟨y, hp, hz⟩⟩

/-- `RELAT_1:28` -/
theorem th28 (h : dom P ⊆ rng R) : rng (comp R P) = rng P := by
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · exact th26 (P := R) (R := P)
  · intro z hz
    obtain ⟨y, hp⟩ := (rng_iff P z).mp hz
    have hy : y ∈ rng R := h y (pair_mem_dom hp)
    obtain ⟨x, hx⟩ := (rng_iff R y).mp hy
    exact (rng_iff (comp R P) z).mpr
      ⟨x, (def8 R P x z).mpr ⟨y, hx, hp⟩⟩

/-- `RELAT_1:45` -/
theorem th45 : dom (id X) = X ∧ rng (id X) = X :=
  ⟨id_dom X, id_rng X⟩

/-- `RELAT_1:46` -/
theorem th46 : converse (id X) = id X :=
  rel_eq (converse_isRelation _) (id_isRelation X) fun x y =>
    (def7 (id X) x y).trans <|
      (def10 X y x).trans <|
        ⟨fun ⟨hy, heq⟩ => (def10 X x y).mpr ⟨heq ▸ hy, heq.symm⟩,
          fun hp =>
            let ⟨hx, heq⟩ := (def10 X x y).mp hp
            ⟨heq ▸ hx, heq.symm⟩⟩

/-- `RELAT_1:47` -/
theorem th47 (h : ∀ x, x ∈ X → TARSKI.pair x x ∈ R) : id X ⊆ R :=
  rel_subset (id_isRelation X) fun x y hp =>
    let ⟨hx, heq⟩ := (def10 X x y).mp hp
    heq ▸ h x hx

/-- `RELAT_1:48` (`Th48`) -/
theorem th48 : TARSKI.pair x y ∈ comp (id X) R ↔ x ∈ X ∧ TARSKI.pair x y ∈ R := by
  constructor
  · intro hp
    obtain ⟨z, hid, hR⟩ := (def8 (id X) R x y).mp hp
    have ⟨hx, heq⟩ := (def10 X x z).mp hid
    exact ⟨hx, heq ▸ hR⟩
  · intro ⟨hx, hR⟩
    exact (def8 (id X) R x y).mpr ⟨x, (def10 X x x).mpr ⟨hx, rfl⟩, hR⟩

/-- `RELAT_1:49` (`Th49`) -/
theorem th49 : TARSKI.pair x y ∈ comp R (id Y) ↔ y ∈ Y ∧ TARSKI.pair x y ∈ R := by
  constructor
  · intro hp
    obtain ⟨z, hR, hid⟩ := (def8 R (id Y) x y).mp hp
    have ⟨hy, heq⟩ := (def10 Y z y).mp hid
    exact ⟨heq ▸ hy, heq ▸ hR⟩
  · intro ⟨hy, hR⟩
    exact (def8 R (id Y) x y).mpr ⟨y, hR, (def10 Y y y).mpr ⟨hy, rfl⟩⟩

/-- `RELAT_1:50` (`Th50`) -/
theorem th50 : comp R (id X) ⊆ R ∧ comp (id X) R ⊆ R :=
  ⟨rel_subset (comp_isRelation R (id X)) fun x y hp => (th49 (R := R) (Y := X) (x := x) (y := y)).mp hp |>.2,
    rel_subset (comp_isRelation (id X) R) fun x y hp => (th48 (X := X) (R := R) (x := x) (y := y)).mp hp |>.2⟩

/-- `RELAT_1:51` (`Th51`) -/
theorem th51 {R X : TarskiSet.{u}} (hR : isRelation R) (h : dom R ⊆ X) :
    comp (id X) R = R :=
  XBOOLE_0.eq_iff_subset.mpr
    ⟨th50.2,
      rel_subset hR fun x y hp =>
        (th48 (X := X) (R := R) (x := x) (y := y)).mpr ⟨h x (pair_mem_dom hp), hp⟩⟩

/-- `RELAT_1:52` -/
theorem th52 {R : TarskiSet.{u}} (hR : isRelation R) :
    comp (id (dom R)) R = R :=
  th51 hR (subset_refl _)

/-- `RELAT_1:53` (`Th53`) -/
theorem th53 {R Y : TarskiSet.{u}} (hR : isRelation R) (h : rng R ⊆ Y) :
    comp R (id Y) = R :=
  XBOOLE_0.eq_iff_subset.mpr
    ⟨th50.1,
      rel_subset hR fun x y hp =>
        (th49 (R := R) (Y := Y) (x := x) (y := y)).mpr ⟨h y (pair_mem_rng hp), hp⟩⟩

/-- `RELAT_1:54` -/
theorem th54 {R : TarskiSet.{u}} (hR : isRelation R) :
    comp R (id (rng R)) = R :=
  th53 hR (subset_refl _)

/-- `RELAT_1:55` -/
theorem th55 : id (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) :=
  th37 (id_isRelation ∅) fun x y hp =>
    (XBOOLE_0.empty_iff x).mp ((def10 ∅ x y).mp hp |>.1)

/-- `RELAT_1:29` (`Th29`) -/
theorem th29 (h : P ⊆ R) : comp Q P ⊆ comp Q R :=
  rel_subset (comp_isRelation Q P) fun x y hp =>
    let ⟨z, hQ, hP⟩ := (def8 Q P x y).mp hp
    (def8 Q R x y).mpr ⟨z, hQ, h _ hP⟩

/-- `RELAT_1:30` (`Th30`) -/
theorem th30 (h : P ⊆ Q) : comp P R ⊆ comp Q R :=
  rel_subset (comp_isRelation P R) fun x y hp =>
    let ⟨z, hP, hR⟩ := (def8 P R x y).mp hp
    (def8 Q R x y).mpr ⟨z, h _ hP, hR⟩

/-- `RELAT_1:31` -/
theorem th31 (hPR : P ⊆ R) (hQS : Q ⊆ S) : comp P Q ⊆ comp R S :=
  XBOOLE_1.th1 (th30 (R := Q) hPR) (th29 (P := Q) (R := S) (Q := R) hQS)

/-- `RELAT_1:32` -/
theorem th32 : comp P (R ∪ Q) = comp P R ∪ comp P Q :=
  rel_eq (comp_isRelation P (R ∪ Q))
    (union_isRelation (comp_isRelation P R) (comp_isRelation P Q))
    fun x y => by
      constructor
      · intro hp
        obtain ⟨z, hP, hRQ⟩ := (def8 P (R ∪ Q) x y).mp hp
        rcases (XBOOLE_0.def3 R Q (TARSKI.pair z y)).mp hRQ with hR | hQ
        · exact (XBOOLE_0.def3 (comp P R) (comp P Q) (TARSKI.pair x y)).mpr
            (Or.inl ((def8 P R x y).mpr ⟨z, hP, hR⟩))
        · exact (XBOOLE_0.def3 (comp P R) (comp P Q) (TARSKI.pair x y)).mpr
            (Or.inr ((def8 P Q x y).mpr ⟨z, hP, hQ⟩))
      · intro hp
        rcases (XBOOLE_0.def3 (comp P R) (comp P Q) (TARSKI.pair x y)).mp hp
          with hPR | hPQ
        · obtain ⟨z, hP, hR⟩ := (def8 P R x y).mp hPR
          exact (def8 P (R ∪ Q) x y).mpr
            ⟨z, hP, (XBOOLE_0.def3 R Q (TARSKI.pair z y)).mpr (Or.inl hR)⟩
        · obtain ⟨z, hP, hQ⟩ := (def8 P Q x y).mp hPQ
          exact (def8 P (R ∪ Q) x y).mpr
            ⟨z, hP, (XBOOLE_0.def3 R Q (TARSKI.pair z y)).mpr (Or.inr hQ)⟩

/-- `RELAT_1:33` -/
theorem th33 : comp P (R ∩ Q) ⊆ comp P R ∩ comp P Q :=
  rel_subset (comp_isRelation P (R ∩ Q)) fun x y hp =>
    let ⟨z, hP, hRQ⟩ := (def8 P (R ∩ Q) x y).mp hp
    let ⟨hR, hQ⟩ := (XBOOLE_0.def4 R Q (TARSKI.pair z y)).mp hRQ
    (XBOOLE_0.def4 (comp P R) (comp P Q) (TARSKI.pair x y)).mpr
      ⟨(def8 P R x y).mpr ⟨z, hP, hR⟩, (def8 P Q x y).mpr ⟨z, hP, hQ⟩⟩

/-- `RELAT_1:34` -/
theorem th34 : comp P R \ comp P Q ⊆ comp P (R \ Q) :=
  rel_subset (diff_isRelation (comp_isRelation P R)) fun a b hp =>
    let ⟨hPR, hnPQ⟩ := (XBOOLE_0.def5 (comp P R) (comp P Q) (TARSKI.pair a b)).mp hp
    let ⟨y, hP, hR⟩ := (def8 P R a b).mp hPR
    have hnQ : TARSKI.pair y b ∉ Q := fun hQ =>
      hnPQ ((def8 P Q a b).mpr ⟨y, hP, hQ⟩)
    (def8 P (R \ Q) a b).mpr
      ⟨y, hP, (XBOOLE_0.def5 R Q (TARSKI.pair y b)).mpr ⟨hR, hnQ⟩⟩

/-- `RELAT_1:35` -/
theorem th35 : converse (comp P R) = comp (converse R) (converse P) :=
  rel_eq (converse_isRelation _) (comp_isRelation _ _) fun a b => by
    constructor
    · intro hp
      obtain ⟨y, hP, hR⟩ := (def8 P R b a).mp ((def7 (comp P R) a b).mp hp)
      exact (def8 (converse R) (converse P) a b).mpr
        ⟨y, (def7 R a y).mpr hR, (def7 P y b).mpr hP⟩
    · intro hp
      obtain ⟨y, hR, hP⟩ := (def8 (converse R) (converse P) a b).mp hp
      exact (def7 (comp P R) a b).mpr
        ((def8 P R b a).mpr ⟨y, (def7 P y b).mp hP, (def7 R a y).mp hR⟩)

/-- `RELAT_1:39` (`Th39`) -/
theorem th39 : comp (∅ : TarskiSet.{u}) R = (∅ : TarskiSet.{u}) ∧
    comp R (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) :=
  ⟨th37 (comp_isRelation ∅ R) fun x y hp =>
      let ⟨_, hz, _⟩ := (def8 ∅ R x y).mp hp
      (XBOOLE_0.empty_iff _).mp hz,
    th37 (comp_isRelation R ∅) fun x y hp =>
      let ⟨_, _, hz⟩ := (def8 R ∅ x y).mp hp
      (XBOOLE_0.empty_iff _).mp hz⟩

/-- `RELAT_1:40` -/
theorem th40 : field (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    rcases (XBOOLE_0.def3 (dom (∅ : TarskiSet.{u})) (rng (∅ : TarskiSet.{u})) x).mp hx
      with hd | hr
    · exact th38.1 ▸ hd
    · exact th38.2 ▸ hr
  · intro hx
    exact ((XBOOLE_0.empty_iff x).mp hx).elim

/-- `RELAT_1:41` (`Th41`) -/
theorem th41 {R : TarskiSet.{u}} (hR : isRelation R)
    (h : dom R = (∅ : TarskiSet.{u}) ∨ rng R = (∅ : TarskiSet.{u})) :
    R = (∅ : TarskiSet.{u}) :=
  h.elim
    (fun hd => th37 hR fun x _ hp =>
      (XBOOLE_0.empty_iff x).mp (hd ▸ pair_mem_dom hp))
    (fun hr => th37 hR fun _ y hp =>
      (XBOOLE_0.empty_iff y).mp (hr ▸ pair_mem_rng hp))

/-- `RELAT_1:42` -/
theorem th42 {R : TarskiSet.{u}} (hR : isRelation R) :
    dom R = (∅ : TarskiSet.{u}) ↔ rng R = (∅ : TarskiSet.{u}) :=
  ⟨fun h => (th41 hR (Or.inl h)) ▸ th38.2,
    fun h => (th41 hR (Or.inr h)) ▸ th38.1⟩

/-- `RELAT_1:43` -/
theorem th43 : converse (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) :=
  th37 (converse_isRelation ∅) fun x y hp =>
    (XBOOLE_0.empty_iff _).mp ((def7 ∅ x y).mp hp)

/-- `RELAT_1:44` -/
theorem th44 (h : XBOOLE_0.misses (rng R) (dom P)) :
    comp R P = (∅ : TarskiSet.{u}) :=
  th37 (comp_isRelation R P) fun x z hp =>
    let ⟨y, hR, hP⟩ := (def8 R P x z).mp hp
    (XBOOLE_0.empty_iff y).mp
      (h ▸ (XBOOLE_0.def4 (rng R) (dom P) y).mpr
        ⟨pair_mem_rng hR, pair_mem_dom hP⟩)

/-- `RELAT_1:56` -/
theorem th56 {P1 P2 R X : TarskiSet.{u}}
    (hP1 : isRelation P1) (hP2 : isRelation P2)
    (h : rng P2 ⊆ X)
    (h1 : comp P2 R = id (dom P1))
    (h2 : comp R P1 = id X) : P1 = P2 :=
  (((th52 hP1).symm.trans
      (congrArg (fun s => comp s P1) h1.symm)).trans th36).trans
    ((congrArg (fun s => comp P2 s) h2).trans (th53 hP2 h))

/-- `RELAT_1:58` (`Th58`) -/
theorem th58 : dom (restrict R X) ⊆ X :=
  fun x hx => (th57 (R := R) (X := X) (x := x)).mp hx |>.1

/-- `RELAT_1:59` (`Th59`) -/
theorem th59 : restrict R X ⊆ R :=
  rel_subset (restrict_isRelation R X) fun x y hp =>
    (def11 R X x y).mp hp |>.2

/-- `RELAT_1:60` (`Th60`) -/
theorem th60 : dom (restrict R X) ⊆ dom R :=
  fun x hx => (th57 (R := R) (X := X) (x := x)).mp hx |>.2

/-- `RELAT_1:61` (`Th61`) -/
theorem th61 : dom (restrict R X) = dom R ∩ X := by
  apply eq_of_mem
  intro x
  exact (th57 (R := R) (X := X) (x := x)).trans
    ⟨fun ⟨hx, hd⟩ => (XBOOLE_0.def4 (dom R) X x).mpr ⟨hd, hx⟩,
      fun hxI =>
        let ⟨hd, hx⟩ := (XBOOLE_0.def4 (dom R) X x).mp hxI
        ⟨hx, hd⟩⟩

/-- `RELAT_1:62` -/
theorem th62 (h : X ⊆ dom R) : dom (restrict R X) = X :=
  ((th61 (R := R) (X := X)).trans (XBOOLE_0.inter_comm (dom R) X)).trans
    (XBOOLE_1.th28 h)

/-- `RELAT_1:63` -/
theorem th63 : comp (restrict R X) P ⊆ comp R P :=
  th30 (th59 (R := R) (X := X))

/-- `RELAT_1:64` -/
theorem th64 : comp P (restrict R X) ⊆ comp P R :=
  th29 (th59 (R := R) (X := X))

/-- `RELAT_1:65` -/
theorem th65 : restrict R X = comp (id X) R :=
  rel_eq (restrict_isRelation R X) (comp_isRelation (id X) R) fun x y =>
    (def11 R X x y).trans (th48 (X := X) (R := R) (x := x) (y := y)).symm

/-- `RELAT_1:66` -/
theorem th66 : restrict R X = (∅ : TarskiSet.{u}) ↔
    XBOOLE_0.misses (dom R) X := by
  constructor
  · intro h
    apply eq_of_mem
    intro x
    constructor
    · intro hx
      have ⟨hd, hxX⟩ := (XBOOLE_0.def4 (dom R) X x).mp hx
      obtain ⟨y, hp⟩ := (dom_iff R x).mp hd
      exact ((XBOOLE_0.empty_iff (TARSKI.pair x y)).mp
        (h ▸ (def11 R X x y).mpr ⟨hxX, hp⟩)).elim
    · intro hx
      exact ((XBOOLE_0.empty_iff x).mp hx).elim
  · intro hmiss
    exact th37 (restrict_isRelation R X) fun x y hp =>
      let ⟨hx, hpR⟩ := (def11 R X x y).mp hp
      (XBOOLE_0.empty_iff x).mp
        (hmiss ▸ (XBOOLE_0.def4 (dom R) X x).mpr ⟨pair_mem_dom hpR, hx⟩)

/-- `RELAT_1:67` (`Th67`) -/
theorem th67 {R X : TarskiSet.{u}} (hR : isRelation R) :
    restrict R X = R ∩ ZFMISC_1.product X (rng R) :=
  rel_eq (restrict_isRelation R X) (inter_isRelation hR) fun x y =>
    (def11 R X x y).trans <|
      Iff.trans
        ⟨fun ⟨hx, hp⟩ =>
          ⟨hp, (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := rng R)).mpr
            ⟨hx, pair_mem_rng hp⟩⟩,
          fun ⟨hp, hprod⟩ =>
            ⟨(ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := rng R)).mp hprod |>.1,
              hp⟩⟩
        (XBOOLE_0.def4 R (ZFMISC_1.product X (rng R)) (TARSKI.pair x y)).symm

/-- `RELAT_1:68` (`Th68`) -/
theorem th68 {R X : TarskiSet.{u}} (hR : isRelation R) (h : dom R ⊆ X) :
    restrict R X = R :=
  (th67 hR).trans
    (XBOOLE_1.th28 (XBOOLE_1.th1 (th7 hR) (ZFMISC_1.th95 h).1))

/-- `RELAT_1:69` -/
theorem th69 {R : TarskiSet.{u}} (hR : isRelation R) :
    restrict R (dom R) = R :=
  th68 hR (subset_refl _)

/-- `RELAT_1:70` (`Th70`) -/
theorem th70 : rng (restrict R X) ⊆ rng R :=
  (th11 (th59 (R := R) (X := X))).2

/-- `RELAT_1:71` (`Th71`) -/
theorem th71 : restrict (restrict R X) Y = restrict R (X ∩ Y) :=
  rel_eq (restrict_isRelation _ _) (restrict_isRelation _ _) fun x y =>
    (def11 (restrict R X) Y x y).trans <|
      Iff.trans
        (and_congr_right fun _ => def11 R X x y)
        (Iff.trans
          ⟨fun ⟨hy, hx, hp⟩ =>
            ⟨(XBOOLE_0.def4 X Y x).mpr ⟨hx, hy⟩, hp⟩,
            fun ⟨hxy, hp⟩ =>
              let ⟨hx, hy⟩ := (XBOOLE_0.def4 X Y x).mp hxy
              ⟨hy, hx, hp⟩⟩
          (def11 R (X ∩ Y) x y).symm)

/-- `RELAT_1:72` -/
theorem th72 : restrict (restrict R X) X = restrict R X :=
  (th71 (R := R) (X := X) (Y := X)).trans
    (congrArg (restrict R) (XBOOLE_0.inter_idem X))

/-- `RELAT_1:73` -/
theorem th73 (h : X ⊆ Y) : restrict (restrict R X) Y = restrict R X :=
  (th71 (R := R) (X := X) (Y := Y)).trans
    (congrArg (restrict R) (XBOOLE_1.th28 h))

/-- `RELAT_1:74` -/
theorem th74 (h : Y ⊆ X) : restrict (restrict R X) Y = restrict R Y :=
  (th71 (R := R) (X := X) (Y := Y)).trans
    (congrArg (restrict R)
      (Eq.trans (XBOOLE_0.inter_comm X Y) (XBOOLE_1.th28 h)))

/-- `RELAT_1:75` (`Th75`) -/
theorem th75 (h : X ⊆ Y) : restrict R X ⊆ restrict R Y :=
  rel_subset (restrict_isRelation R X) fun x y hp =>
    let ⟨hx, hpR⟩ := (def11 R X x y).mp hp
    (def11 R Y x y).mpr ⟨h x hx, hpR⟩

/-- `RELAT_1:76` (`Th76`) -/
theorem th76 (h : P ⊆ R) : restrict P X ⊆ restrict R X :=
  rel_subset (restrict_isRelation P X) fun x y hp =>
    let ⟨hx, hpP⟩ := (def11 P X x y).mp hp
    (def11 R X x y).mpr ⟨hx, h _ hpP⟩

/-- `RELAT_1:77` (`Th77`) -/
theorem th77 (hPR : P ⊆ R) (hXY : X ⊆ Y) :
    restrict P X ⊆ restrict R Y :=
  XBOOLE_1.th1 (th76 (X := X) hPR) (th75 (R := R) hXY)

/-- `RELAT_1:78` (`Th78`) -/
theorem th78 : restrict R (X ∪ Y) = restrict R X ∪ restrict R Y :=
  rel_eq (restrict_isRelation R (X ∪ Y))
    (union_isRelation (restrict_isRelation R X) (restrict_isRelation R Y))
    fun x y => by
      constructor
      · intro hp
        have ⟨hxy, hpR⟩ := (def11 R (X ∪ Y) x y).mp hp
        rcases (XBOOLE_0.def3 X Y x).mp hxy with hx | hy
        · exact (XBOOLE_0.def3 (restrict R X) (restrict R Y)
            (TARSKI.pair x y)).mpr (Or.inl ((def11 R X x y).mpr ⟨hx, hpR⟩))
        · exact (XBOOLE_0.def3 (restrict R X) (restrict R Y)
            (TARSKI.pair x y)).mpr (Or.inr ((def11 R Y x y).mpr ⟨hy, hpR⟩))
      · intro hp
        rcases (XBOOLE_0.def3 (restrict R X) (restrict R Y)
            (TARSKI.pair x y)).mp hp with hX | hY
        · have ⟨hx, hpR⟩ := (def11 R X x y).mp hX
          exact (def11 R (X ∪ Y) x y).mpr
            ⟨(XBOOLE_0.def3 X Y x).mpr (Or.inl hx), hpR⟩
        · have ⟨hy, hpR⟩ := (def11 R Y x y).mp hY
          exact (def11 R (X ∪ Y) x y).mpr
            ⟨(XBOOLE_0.def3 X Y x).mpr (Or.inr hy), hpR⟩

/-- `RELAT_1:79` -/
theorem th79 : restrict R (X ∩ Y) = restrict R X ∩ restrict R Y :=
  rel_eq (restrict_isRelation R (X ∩ Y))
    (inter_isRelation (restrict_isRelation R X)) fun x y => by
      constructor
      · intro hp
        have ⟨hxy, hpR⟩ := (def11 R (X ∩ Y) x y).mp hp
        have ⟨hx, hy⟩ := (XBOOLE_0.def4 X Y x).mp hxy
        exact (XBOOLE_0.def4 (restrict R X) (restrict R Y)
            (TARSKI.pair x y)).mpr
          ⟨(def11 R X x y).mpr ⟨hx, hpR⟩, (def11 R Y x y).mpr ⟨hy, hpR⟩⟩
      · intro hp
        have ⟨hX, hY⟩ := (XBOOLE_0.def4 (restrict R X) (restrict R Y)
            (TARSKI.pair x y)).mp hp
        have ⟨hx, hpR⟩ := (def11 R X x y).mp hX
        have ⟨hy, _⟩ := (def11 R Y x y).mp hY
        exact (def11 R (X ∩ Y) x y).mpr
          ⟨(XBOOLE_0.def4 X Y x).mpr ⟨hx, hy⟩, hpR⟩

/-- `RELAT_1:80` (`Th80`) -/
theorem th80 : restrict R (X \ Y) = restrict R X \ restrict R Y :=
  rel_eq (restrict_isRelation R (X \ Y))
    (diff_isRelation (restrict_isRelation R X)) fun x y => by
      constructor
      · intro hp
        have ⟨hxy, hpR⟩ := (def11 R (X \ Y) x y).mp hp
        have ⟨hx, hny⟩ := (XBOOLE_0.def5 X Y x).mp hxy
        exact (XBOOLE_0.def5 (restrict R X) (restrict R Y)
            (TARSKI.pair x y)).mpr
          ⟨(def11 R X x y).mpr ⟨hx, hpR⟩,
            fun hY => hny ((def11 R Y x y).mp hY |>.1)⟩
      · intro hp
        have ⟨hX, hnY⟩ := (XBOOLE_0.def5 (restrict R X) (restrict R Y)
            (TARSKI.pair x y)).mp hp
        have ⟨hx, hpR⟩ := (def11 R X x y).mp hX
        have hny : x ∉ Y := fun hy => hnY ((def11 R Y x y).mpr ⟨hy, hpR⟩)
        exact (def11 R (X \ Y) x y).mpr
          ⟨(XBOOLE_0.def5 X Y x).mpr ⟨hx, hny⟩, hpR⟩

/-- `RELAT_1:81` -/
theorem th81 : restrict R (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) :=
  th37 (restrict_isRelation R ∅) fun x y hp =>
    (XBOOLE_0.empty_iff x).mp ((def11 R ∅ x y).mp hp |>.1)

/-- `RELAT_1:82` -/
theorem th82 : restrict (∅ : TarskiSet.{u}) X = (∅ : TarskiSet.{u}) :=
  th37 (restrict_isRelation ∅ X) fun x y hp =>
    (XBOOLE_0.empty_iff _).mp ((def11 ∅ X x y).mp hp |>.2)

/-- `RELAT_1:83` -/
theorem th83 : restrict (comp P R) X = comp (restrict P X) R :=
  rel_eq (restrict_isRelation (comp P R) X) (comp_isRelation _ _) fun x y => by
    constructor
    · intro hp
      have ⟨hx, hPR⟩ := (def11 (comp P R) X x y).mp hp
      obtain ⟨a, hP, hR⟩ := (def8 P R x y).mp hPR
      exact (def8 (restrict P X) R x y).mpr
        ⟨a, (def11 P X x a).mpr ⟨hx, hP⟩, hR⟩
    · intro hp
      obtain ⟨a, hPX, hR⟩ := (def8 (restrict P X) R x y).mp hp
      have ⟨hx, hP⟩ := (def11 P X x a).mp hPX
      exact (def11 (comp P R) X x y).mpr
        ⟨hx, (def8 P R x y).mpr ⟨a, hP, hR⟩⟩

/-- `RELAT_1:84` (`Th84`) -/
theorem th84 : y ∈ rng (restrictRng Y R) ↔ y ∈ Y ∧ y ∈ rng R := by
  constructor
  · intro hy
    obtain ⟨x, hp⟩ := (rng_iff (restrictRng Y R) y).mp hy
    have ⟨hY, hpR⟩ := (def12 Y R x y).mp hp
    exact ⟨hY, pair_mem_rng hpR⟩
  · intro ⟨hY, hr⟩
    obtain ⟨x, hp⟩ := (rng_iff R y).mp hr
    exact (rng_iff (restrictRng Y R) y).mpr ⟨x, (def12 Y R x y).mpr ⟨hY, hp⟩⟩

/-- `RELAT_1:85` (`Th85`) -/
theorem th85 : rng (restrictRng Y R) ⊆ Y :=
  fun y hy => (th84 (Y := Y) (R := R) (y := y)).mp hy |>.1

/-- `RELAT_1:86` (`Th86`) -/
theorem th86 : restrictRng Y R ⊆ R :=
  rel_subset (restrictRng_isRelation Y R) fun x y hp =>
    (def12 Y R x y).mp hp |>.2

/-- `RELAT_1:87` (`Th87`) -/
theorem th87 : rng (restrictRng Y R) ⊆ rng R :=
  (th11 (th86 (Y := Y) (R := R))).2

/-- `RELAT_1:88` (`Th88`) -/
theorem th88 : rng (restrictRng Y R) = rng R ∩ Y := by
  apply eq_of_mem
  intro y
  exact (th84 (Y := Y) (R := R) (y := y)).trans
    ⟨fun ⟨hY, hr⟩ => (XBOOLE_0.def4 (rng R) Y y).mpr ⟨hr, hY⟩,
      fun hy =>
        let ⟨hr, hY⟩ := (XBOOLE_0.def4 (rng R) Y y).mp hy
        ⟨hY, hr⟩⟩

/-- `RELAT_1:89` -/
theorem th89 (h : Y ⊆ rng R) : rng (restrictRng Y R) = Y :=
  ((th88 (Y := Y) (R := R)).trans (XBOOLE_0.inter_comm (rng R) Y)).trans
    (XBOOLE_1.th28 h)

/-- `RELAT_1:90` -/
theorem th90 : comp (restrictRng Y R) P ⊆ comp R P :=
  th30 (th86 (Y := Y) (R := R))

/-- `RELAT_1:91` -/
theorem th91 : comp P (restrictRng Y R) ⊆ comp P R :=
  th29 (th86 (Y := Y) (R := R))

/-- `RELAT_1:92` -/
theorem th92 : restrictRng Y R = comp R (id Y) :=
  rel_eq (restrictRng_isRelation Y R) (comp_isRelation R (id Y)) fun x y =>
    (def12 Y R x y).trans (th49 (R := R) (Y := Y) (x := x) (y := y)).symm

/-- `RELAT_1:93` (`Th93`) -/
theorem th93 {Y R : TarskiSet.{u}} (hR : isRelation R) :
    restrictRng Y R = R ∩ ZFMISC_1.product (dom R) Y :=
  rel_eq (restrictRng_isRelation Y R) (inter_isRelation hR) fun x y =>
    (def12 Y R x y).trans <|
      Iff.trans
        ⟨fun ⟨hY, hp⟩ =>
          ⟨hp, (ZFMISC_1.th87 (x := x) (y := y) (X := dom R) (Y := Y)).mpr
            ⟨pair_mem_dom hp, hY⟩⟩,
          fun ⟨hp, hprod⟩ =>
            ⟨(ZFMISC_1.th87 (x := x) (y := y) (X := dom R) (Y := Y)).mp hprod |>.2,
              hp⟩⟩
        (XBOOLE_0.def4 R (ZFMISC_1.product (dom R) Y) (TARSKI.pair x y)).symm

/-- `RELAT_1:94` (`Th94`) -/
theorem th94 {Y R : TarskiSet.{u}} (hR : isRelation R) (h : rng R ⊆ Y) :
    restrictRng Y R = R :=
  (th93 hR).trans
    (XBOOLE_1.th28 (XBOOLE_1.th1 (th7 hR) (ZFMISC_1.th95 h).2))

/-- `RELAT_1:95` -/
theorem th95 {R : TarskiSet.{u}} (hR : isRelation R) :
    restrictRng (rng R) R = R :=
  th94 hR (subset_refl _)

/-- `RELAT_1:96` (`Th96`) -/
theorem th96 : restrictRng Y (restrictRng X R) = restrictRng (Y ∩ X) R :=
  rel_eq (restrictRng_isRelation _ _) (restrictRng_isRelation _ _) fun x y =>
    (def12 Y (restrictRng X R) x y).trans <|
      Iff.trans
        (and_congr_right fun _ => def12 X R x y)
        (Iff.trans
          ⟨fun ⟨hY, hX, hp⟩ =>
            ⟨(XBOOLE_0.def4 Y X y).mpr ⟨hY, hX⟩, hp⟩,
            fun ⟨hYX, hp⟩ =>
              let ⟨hY, hX⟩ := (XBOOLE_0.def4 Y X y).mp hYX
              ⟨hY, hX, hp⟩⟩
          (def12 (Y ∩ X) R x y).symm)

/-- `RELAT_1:97` -/
theorem th97 : restrictRng Y (restrictRng Y R) = restrictRng Y R :=
  (th96 (Y := Y) (X := Y) (R := R)).trans
    (congrArg (fun s => restrictRng s R) (XBOOLE_0.inter_idem Y))

/-- `RELAT_1:98` -/
theorem th98 (h : X ⊆ Y) : restrictRng Y (restrictRng X R) = restrictRng X R :=
  (th96 (Y := Y) (X := X) (R := R)).trans
    (congrArg (fun s => restrictRng s R)
      (Eq.trans (XBOOLE_0.inter_comm Y X) (XBOOLE_1.th28 h)))

/-- `RELAT_1:99` -/
theorem th99 (h : Y ⊆ X) : restrictRng Y (restrictRng X R) = restrictRng Y R :=
  (th96 (Y := Y) (X := X) (R := R)).trans
    (congrArg (fun s => restrictRng s R) (XBOOLE_1.th28 h))

/-- `RELAT_1:100` (`Th100`) -/
theorem th100 (h : X ⊆ Y) : restrictRng X R ⊆ restrictRng Y R :=
  rel_subset (restrictRng_isRelation X R) fun x y hp =>
    let ⟨hX, hpR⟩ := (def12 X R x y).mp hp
    (def12 Y R x y).mpr ⟨h y hX, hpR⟩

/-- `RELAT_1:101` (`Th101`) -/
theorem th101 (h : P1 ⊆ P2) : restrictRng Y P1 ⊆ restrictRng Y P2 :=
  rel_subset (restrictRng_isRelation Y P1) fun x y hp =>
    let ⟨hY, hp1⟩ := (def12 Y P1 x y).mp hp
    (def12 Y P2 x y).mpr ⟨hY, h _ hp1⟩

/-- `RELAT_1:102` -/
theorem th102 (hP : P1 ⊆ P2) (hY : Y1 ⊆ Y2) :
    restrictRng Y1 P1 ⊆ restrictRng Y2 P2 :=
  XBOOLE_1.th1 (th101 (Y := Y1) hP) (th100 (R := P2) hY)

/-- `RELAT_1:103` -/
theorem th103 : restrictRng (X ∪ Y) R = restrictRng X R ∪ restrictRng Y R :=
  rel_eq (restrictRng_isRelation (X ∪ Y) R)
    (union_isRelation (restrictRng_isRelation X R) (restrictRng_isRelation Y R))
    fun x y => by
      constructor
      · intro hp
        have ⟨hxy, hpR⟩ := (def12 (X ∪ Y) R x y).mp hp
        rcases (XBOOLE_0.def3 X Y y).mp hxy with hx | hy
        · exact (XBOOLE_0.def3 (restrictRng X R) (restrictRng Y R)
            (TARSKI.pair x y)).mpr (Or.inl ((def12 X R x y).mpr ⟨hx, hpR⟩))
        · exact (XBOOLE_0.def3 (restrictRng X R) (restrictRng Y R)
            (TARSKI.pair x y)).mpr (Or.inr ((def12 Y R x y).mpr ⟨hy, hpR⟩))
      · intro hp
        rcases (XBOOLE_0.def3 (restrictRng X R) (restrictRng Y R)
            (TARSKI.pair x y)).mp hp with hX | hY
        · have ⟨hx, hpR⟩ := (def12 X R x y).mp hX
          exact (def12 (X ∪ Y) R x y).mpr
            ⟨(XBOOLE_0.def3 X Y y).mpr (Or.inl hx), hpR⟩
        · have ⟨hy, hpR⟩ := (def12 Y R x y).mp hY
          exact (def12 (X ∪ Y) R x y).mpr
            ⟨(XBOOLE_0.def3 X Y y).mpr (Or.inr hy), hpR⟩

/-- `RELAT_1:104` -/
theorem th104 : restrictRng (X ∩ Y) R = restrictRng X R ∩ restrictRng Y R :=
  rel_eq (restrictRng_isRelation (X ∩ Y) R)
    (inter_isRelation (restrictRng_isRelation X R)) fun x y => by
      constructor
      · intro hp
        have ⟨hxy, hpR⟩ := (def12 (X ∩ Y) R x y).mp hp
        have ⟨hx, hy⟩ := (XBOOLE_0.def4 X Y y).mp hxy
        exact (XBOOLE_0.def4 (restrictRng X R) (restrictRng Y R)
            (TARSKI.pair x y)).mpr
          ⟨(def12 X R x y).mpr ⟨hx, hpR⟩, (def12 Y R x y).mpr ⟨hy, hpR⟩⟩
      · intro hp
        have ⟨hX, hY⟩ := (XBOOLE_0.def4 (restrictRng X R) (restrictRng Y R)
            (TARSKI.pair x y)).mp hp
        have ⟨hx, hpR⟩ := (def12 X R x y).mp hX
        have ⟨hy, _⟩ := (def12 Y R x y).mp hY
        exact (def12 (X ∩ Y) R x y).mpr
          ⟨(XBOOLE_0.def4 X Y y).mpr ⟨hx, hy⟩, hpR⟩

/-- `RELAT_1:105` -/
theorem th105 : restrictRng (X \ Y) R = restrictRng X R \ restrictRng Y R :=
  rel_eq (restrictRng_isRelation (X \ Y) R)
    (diff_isRelation (restrictRng_isRelation X R)) fun x y => by
      constructor
      · intro hp
        have ⟨hxy, hpR⟩ := (def12 (X \ Y) R x y).mp hp
        have ⟨hx, hny⟩ := (XBOOLE_0.def5 X Y y).mp hxy
        exact (XBOOLE_0.def5 (restrictRng X R) (restrictRng Y R)
            (TARSKI.pair x y)).mpr
          ⟨(def12 X R x y).mpr ⟨hx, hpR⟩,
            fun hY => hny ((def12 Y R x y).mp hY |>.1)⟩
      · intro hp
        have ⟨hX, hnY⟩ := (XBOOLE_0.def5 (restrictRng X R) (restrictRng Y R)
            (TARSKI.pair x y)).mp hp
        have ⟨hx, hpR⟩ := (def12 X R x y).mp hX
        have hny : y ∉ Y := fun hy => hnY ((def12 Y R x y).mpr ⟨hy, hpR⟩)
        exact (def12 (X \ Y) R x y).mpr
          ⟨(XBOOLE_0.def5 X Y y).mpr ⟨hx, hny⟩, hpR⟩

/-- `RELAT_1:106` -/
theorem th106 : restrictRng (∅ : TarskiSet.{u}) R = (∅ : TarskiSet.{u}) :=
  th37 (restrictRng_isRelation ∅ R) fun _ y hp =>
    (XBOOLE_0.empty_iff y).mp ((def12 ∅ R _ y).mp hp |>.1)

/-- `RELAT_1:107` -/
theorem th107 : restrictRng Y (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) :=
  th37 (restrictRng_isRelation Y ∅) fun x y hp =>
    (XBOOLE_0.empty_iff _).mp ((def12 Y ∅ x y).mp hp |>.2)

/-- `RELAT_1:108` -/
theorem th108 : restrictRng Y (comp P R) = comp P (restrictRng Y R) :=
  rel_eq (restrictRng_isRelation Y (comp P R)) (comp_isRelation _ _)
    fun x y => by
      constructor
      · intro hp
        have ⟨hY, hPR⟩ := (def12 Y (comp P R) x y).mp hp
        obtain ⟨a, hP, hR⟩ := (def8 P R x y).mp hPR
        exact (def8 P (restrictRng Y R) x y).mpr
          ⟨a, hP, (def12 Y R a y).mpr ⟨hY, hR⟩⟩
      · intro hp
        obtain ⟨a, hP, hYR⟩ := (def8 P (restrictRng Y R) x y).mp hp
        have ⟨hY, hR⟩ := (def12 Y R a y).mp hYR
        exact (def12 Y (comp P R) x y).mpr
          ⟨hY, (def8 P R x y).mpr ⟨a, hP, hR⟩⟩

/-- `RELAT_1:109` -/
theorem th109 : restrict (restrictRng Y R) X =
    restrictRng Y (restrict R X) :=
  rel_eq (restrict_isRelation _ _) (restrictRng_isRelation _ _) fun x y =>
    (def11 (restrictRng Y R) X x y).trans <|
      Iff.trans
        (and_congr_right fun _ => def12 Y R x y)
        (Iff.trans
          ⟨fun ⟨hx, hY, hp⟩ => ⟨hY, (def11 R X x y).mpr ⟨hx, hp⟩⟩,
            fun ⟨hY, hRX⟩ =>
              let ⟨hx, hp⟩ := (def11 R X x y).mp hRX
              ⟨hx, hY, hp⟩⟩
          (def12 Y (restrict R X) x y).symm)

/-- `RELAT_1:111` (`Th111`) -/
theorem th111 : image R X ⊆ rng R :=
  fun y hy =>
    let ⟨_, hp, _⟩ := (def13 R X y).mp hy
    pair_mem_rng hp

/-- `RELAT_1:112` -/
theorem th112 : image R X = image R (dom R ∩ X) := by
  apply eq_of_mem
  intro y
  constructor
  · intro hy
    obtain ⟨x, hp, hx⟩ := (def13 R X y).mp hy
    exact (def13 R (dom R ∩ X) y).mpr
      ⟨x, hp, (XBOOLE_0.def4 (dom R) X x).mpr ⟨pair_mem_dom hp, hx⟩⟩
  · intro hy
    obtain ⟨x, hp, hxI⟩ := (def13 R (dom R ∩ X) y).mp hy
    exact (def13 R X y).mpr ⟨x, hp, (XBOOLE_0.def4 (dom R) X x).mp hxI |>.2⟩

/-- `RELAT_1:113` (`Th113`) -/
theorem th113 : image R (dom R) = rng R := by
  apply eq_of_mem
  intro y
  constructor
  · intro hy
    exact th111 (R := R) (X := dom R) y hy
  · intro hy
    obtain ⟨x, hp⟩ := (rng_iff R y).mp hy
    exact (def13 R (dom R) y).mpr ⟨x, hp, pair_mem_dom hp⟩

/-- `RELAT_1:114` -/
theorem th114 : image R X ⊆ image R (dom R) := by
  intro y hy
  obtain ⟨x, hp, hx⟩ := (def13 R X y).mp hy
  exact (def13 R (dom R) y).mpr ⟨x, hp, pair_mem_dom hp⟩

/-- `RELAT_1:115` -/
theorem th115 : rng (restrict R X) = image R X := by
  apply eq_of_mem
  intro y
  constructor
  · intro hy
    obtain ⟨x, hp⟩ := (rng_iff (restrict R X) y).mp hy
    have ⟨hx, hpR⟩ := (def11 R X x y).mp hp
    exact (def13 R X y).mpr ⟨x, hpR, hx⟩
  · intro hy
    obtain ⟨x, hpR, hx⟩ := (def13 R X y).mp hy
    exact (rng_iff (restrict R X) y).mpr ⟨x, (def11 R X x y).mpr ⟨hx, hpR⟩⟩

/-- `RELAT_1:118` -/
theorem th118 : image R X = (∅ : TarskiSet.{u}) ↔
    XBOOLE_0.misses (dom R) X := by
  constructor
  · intro h
    apply eq_of_mem
    intro x
    constructor
    · intro hx
      have ⟨hd, hxX⟩ := (XBOOLE_0.def4 (dom R) X x).mp hx
      obtain ⟨y, hp⟩ := (dom_iff R x).mp hd
      exact ((XBOOLE_0.empty_iff y).mp
        (h ▸ (def13 R X y).mpr ⟨x, hp, hxX⟩)).elim
    · intro hx
      exact ((XBOOLE_0.empty_iff x).mp hx).elim
  · intro hmiss
    apply XBOOLE_1.th3
    intro y hy
    obtain ⟨x, hp, hx⟩ := (def13 R X y).mp hy
    exact ((XBOOLE_0.empty_iff x).mp
      (hmiss ▸ (XBOOLE_0.def4 (dom R) X x).mpr ⟨pair_mem_dom hp, hx⟩)).elim

/-- `RELAT_1:119` -/
theorem th119 (hne : X ≠ (∅ : TarskiSet.{u})) (h : X ⊆ dom R) :
    image R X ≠ (∅ : TarskiSet.{u}) :=
  fun him =>
    hne (XBOOLE_1.th3 (fun x hx =>
      ((XBOOLE_0.empty_iff x).mp
        ((th118 (R := R) (X := X)).mp him ▸
          (XBOOLE_0.def4 (dom R) X x).mpr ⟨h x hx, hx⟩)).elim))

/-- `RELAT_1:120` -/
theorem th120 : image R (X ∪ Y) = image R X ∪ image R Y := by
  apply eq_of_mem
  intro z
  constructor
  · intro hz
    obtain ⟨x, hp, hxy⟩ := (def13 R (X ∪ Y) z).mp hz
    rcases (XBOOLE_0.def3 X Y x).mp hxy with hx | hy
    · exact (XBOOLE_0.def3 (image R X) (image R Y) z).mpr
        (Or.inl ((def13 R X z).mpr ⟨x, hp, hx⟩))
    · exact (XBOOLE_0.def3 (image R X) (image R Y) z).mpr
        (Or.inr ((def13 R Y z).mpr ⟨x, hp, hy⟩))
  · intro hz
    rcases (XBOOLE_0.def3 (image R X) (image R Y) z).mp hz with hX | hY
    · obtain ⟨x, hp, hx⟩ := (def13 R X z).mp hX
      exact (def13 R (X ∪ Y) z).mpr
        ⟨x, hp, (XBOOLE_0.def3 X Y x).mpr (Or.inl hx)⟩
    · obtain ⟨x, hp, hy⟩ := (def13 R Y z).mp hY
      exact (def13 R (X ∪ Y) z).mpr
        ⟨x, hp, (XBOOLE_0.def3 X Y x).mpr (Or.inr hy)⟩

/-- `RELAT_1:121` -/
theorem th121 : image R (X ∩ Y) ⊆ image R X ∩ image R Y :=
  fun z hz =>
    let ⟨x, hp, hxy⟩ := (def13 R (X ∩ Y) z).mp hz
    let ⟨hx, hy⟩ := (XBOOLE_0.def4 X Y x).mp hxy
    (XBOOLE_0.def4 (image R X) (image R Y) z).mpr
      ⟨(def13 R X z).mpr ⟨x, hp, hx⟩, (def13 R Y z).mpr ⟨x, hp, hy⟩⟩

/-- `RELAT_1:122` -/
theorem th122 : image R X \ image R Y ⊆ image R (X \ Y) :=
  fun z hz =>
    let ⟨hX, hnY⟩ := (XBOOLE_0.def5 (image R X) (image R Y) z).mp hz
    let ⟨x, hp, hx⟩ := (def13 R X z).mp hX
    have hnx : x ∉ Y := fun hy => hnY ((def13 R Y z).mpr ⟨x, hp, hy⟩)
    (def13 R (X \ Y) z).mpr
      ⟨x, hp, (XBOOLE_0.def5 X Y x).mpr ⟨hx, hnx⟩⟩

/-- `RELAT_1:123` (`Th123`) -/
theorem th123 (h : X ⊆ Y) : image R X ⊆ image R Y :=
  fun z hz =>
    let ⟨x, hp, hx⟩ := (def13 R X z).mp hz
    (def13 R Y z).mpr ⟨x, hp, h x hx⟩

/-- `RELAT_1:124` (`Th124`) -/
theorem th124 (h : P ⊆ R) : image P X ⊆ image R X :=
  fun z hz =>
    let ⟨x, hp, hx⟩ := (def13 P X z).mp hz
    (def13 R X z).mpr ⟨x, h _ hp, hx⟩

/-- `RELAT_1:125` -/
theorem th125 (hPR : P ⊆ R) (hXY : X ⊆ Y) : image P X ⊆ image R Y :=
  XBOOLE_1.th1 (th124 (X := X) hPR) (th123 (R := R) hXY)

/-- `RELAT_1:126` -/
theorem th126 : image (comp P R) X = image R (image P X) := by
  apply eq_of_mem
  intro z
  constructor
  · intro hz
    obtain ⟨x, hp, hx⟩ := (def13 (comp P R) X z).mp hz
    obtain ⟨y, hP, hR⟩ := (def8 P R x z).mp hp
    exact (def13 R (image P X) z).mpr
      ⟨y, hR, (def13 P X y).mpr ⟨x, hP, hx⟩⟩
  · intro hz
    obtain ⟨y, hR, hy⟩ := (def13 R (image P X) z).mp hz
    obtain ⟨x, hP, hx⟩ := (def13 P X y).mp hy
    exact (def13 (comp P R) X z).mpr
      ⟨x, (def8 P R x z).mpr ⟨y, hP, hR⟩, hx⟩

/-- `RELAT_1:127` (`Th127`) -/
theorem th127 : rng (comp P R) = image R (rng P) := by
  apply eq_of_mem
  intro z
  constructor
  · intro hz
    obtain ⟨x, hp⟩ := (rng_iff (comp P R) z).mp hz
    obtain ⟨y, hP, hR⟩ := (def8 P R x z).mp hp
    exact (def13 R (rng P) z).mpr ⟨y, hR, pair_mem_rng hP⟩
  · intro hz
    obtain ⟨y, hR, hy⟩ := (def13 R (rng P) z).mp hz
    obtain ⟨x, hP⟩ := (rng_iff P y).mp hy
    exact (rng_iff (comp P R) z).mpr ⟨x, (def8 P R x z).mpr ⟨y, hP, hR⟩⟩

/-- `RELAT_1:128` -/
theorem th128 : image (restrict R X) Y ⊆ image R Y :=
  th124 (th59 (R := R) (X := X))

/-- `RELAT_1:129` (`Th129`) -/
theorem th129 (h : X ⊆ Y) : image (restrict R Y) X = image R X := by
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · exact th128 (R := R) (X := Y) (Y := X)
  · intro z hz
    obtain ⟨x, hp, hx⟩ := (def13 R X z).mp hz
    exact (def13 (restrict R Y) X z).mpr
      ⟨x, (def11 R Y x z).mpr ⟨h x hx, hp⟩, hx⟩

/-- `RELAT_1:130` -/
theorem th130 : dom R ∩ X ⊆ image (converse R) (image R X) :=
  fun x hx =>
    let ⟨hd, hxX⟩ := (XBOOLE_0.def4 (dom R) X x).mp hx
    let ⟨y, hp⟩ := (dom_iff R x).mp hd
    (def13 (converse R) (image R X) x).mpr
      ⟨y, (def7 R y x).mpr hp, (def13 R X y).mpr ⟨x, hp, hxX⟩⟩

private theorem exists_mem_of_ne {A : TarskiSet.{u}}
    (h : A ≠ (∅ : TarskiSet.{u})) : ∃ x, x ∈ A :=
  Classical.byContradiction fun hne =>
    h (XBOOLE_0.empty_eq (fun hex => hne hex))

/-- `RELAT_1:132` (`Th132`) -/
theorem th132 : invimage R Y ⊆ dom R :=
  fun x hx =>
    let ⟨_, hp, _⟩ := (def14 R Y x).mp hx
    pair_mem_dom hp

/-- `RELAT_1:133` -/
theorem th133 : invimage R Y = invimage R (rng R ∩ Y) := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    obtain ⟨y, hr, hp, hy⟩ := (th131 (R := R) (Y := Y) (x := x)).mp hx
    exact (def14 R (rng R ∩ Y) x).mpr
      ⟨y, hp, (XBOOLE_0.def4 (rng R) Y y).mpr ⟨hr, hy⟩⟩
  · intro hx
    obtain ⟨y, hp, hyI⟩ := (def14 R (rng R ∩ Y) x).mp hx
    exact (def14 R Y x).mpr ⟨y, hp, (XBOOLE_0.def4 (rng R) Y y).mp hyI |>.2⟩

/-- `RELAT_1:134` (`Th134`) -/
theorem th134 : invimage R (rng R) = dom R := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    exact th132 (R := R) (Y := rng R) x hx
  · intro hx
    obtain ⟨y, hp⟩ := (dom_iff R x).mp hx
    exact (def14 R (rng R) x).mpr ⟨y, hp, pair_mem_rng hp⟩

/-- `RELAT_1:135` -/
theorem th135 : invimage R Y ⊆ invimage R (rng R) :=
  th134 (R := R) ▸ th132 (R := R) (Y := Y)

/-- `RELAT_1:138` -/
theorem th138 : invimage R Y = (∅ : TarskiSet.{u}) ↔
    XBOOLE_0.misses (rng R) Y := by
  constructor
  · intro h
    apply eq_of_mem
    intro y
    constructor
    · intro hy
      have ⟨hr, hyY⟩ := (XBOOLE_0.def4 (rng R) Y y).mp hy
      obtain ⟨x, hp⟩ := (rng_iff R y).mp hr
      exact ((XBOOLE_0.empty_iff x).mp
        (h ▸ (def14 R Y x).mpr ⟨y, hp, hyY⟩)).elim
    · intro hy
      exact ((XBOOLE_0.empty_iff y).mp hy).elim
  · intro hmiss
    apply XBOOLE_1.th3
    intro x hx
    obtain ⟨y, hp, hy⟩ := (def14 R Y x).mp hx
    exact ((XBOOLE_0.empty_iff y).mp
      (hmiss ▸ (XBOOLE_0.def4 (rng R) Y y).mpr ⟨pair_mem_rng hp, hy⟩)).elim

/-- `RELAT_1:139` -/
theorem th139 (hne : Y ≠ (∅ : TarskiSet.{u})) (h : Y ⊆ rng R) :
    invimage R Y ≠ (∅ : TarskiSet.{u}) :=
  fun him =>
    hne (XBOOLE_1.th3 (fun y hy =>
      ((XBOOLE_0.empty_iff y).mp
        ((th138 (R := R) (Y := Y)).mp him ▸
          (XBOOLE_0.def4 (rng R) Y y).mpr ⟨h y hy, hy⟩)).elim))

/-- `RELAT_1:140` -/
theorem th140 : invimage R (X ∪ Y) = invimage R X ∪ invimage R Y := by
  apply eq_of_mem
  intro z
  constructor
  · intro hz
    obtain ⟨y, hp, hxy⟩ := (def14 R (X ∪ Y) z).mp hz
    rcases (XBOOLE_0.def3 X Y y).mp hxy with hx | hy
    · exact (XBOOLE_0.def3 (invimage R X) (invimage R Y) z).mpr
        (Or.inl ((def14 R X z).mpr ⟨y, hp, hx⟩))
    · exact (XBOOLE_0.def3 (invimage R X) (invimage R Y) z).mpr
        (Or.inr ((def14 R Y z).mpr ⟨y, hp, hy⟩))
  · intro hz
    rcases (XBOOLE_0.def3 (invimage R X) (invimage R Y) z).mp hz with hX | hY
    · obtain ⟨y, hp, hx⟩ := (def14 R X z).mp hX
      exact (def14 R (X ∪ Y) z).mpr
        ⟨y, hp, (XBOOLE_0.def3 X Y y).mpr (Or.inl hx)⟩
    · obtain ⟨y, hp, hy⟩ := (def14 R Y z).mp hY
      exact (def14 R (X ∪ Y) z).mpr
        ⟨y, hp, (XBOOLE_0.def3 X Y y).mpr (Or.inr hy)⟩

/-- `RELAT_1:141` -/
theorem th141 : invimage R (X ∩ Y) ⊆ invimage R X ∩ invimage R Y :=
  fun z hz =>
    let ⟨y, hp, hxy⟩ := (def14 R (X ∩ Y) z).mp hz
    let ⟨hx, hy⟩ := (XBOOLE_0.def4 X Y y).mp hxy
    (XBOOLE_0.def4 (invimage R X) (invimage R Y) z).mpr
      ⟨(def14 R X z).mpr ⟨y, hp, hx⟩, (def14 R Y z).mpr ⟨y, hp, hy⟩⟩

/-- `RELAT_1:142` -/
theorem th142 : invimage R X \ invimage R Y ⊆ invimage R (X \ Y) :=
  fun z hz =>
    let ⟨hX, hnY⟩ := (XBOOLE_0.def5 (invimage R X) (invimage R Y) z).mp hz
    let ⟨y, hp, hx⟩ := (def14 R X z).mp hX
    have hny : y ∉ Y := fun hy => hnY ((def14 R Y z).mpr ⟨y, hp, hy⟩)
    (def14 R (X \ Y) z).mpr
      ⟨y, hp, (XBOOLE_0.def5 X Y y).mpr ⟨hx, hny⟩⟩

/-- `RELAT_1:143` (`Th143`) -/
theorem th143 (h : X ⊆ Y) : invimage R X ⊆ invimage R Y :=
  fun z hz =>
    let ⟨y, hp, hx⟩ := (def14 R X z).mp hz
    (def14 R Y z).mpr ⟨y, hp, h y hx⟩

/-- `RELAT_1:144` (`Th144`) -/
theorem th144 (h : P ⊆ R) : invimage P Y ⊆ invimage R Y :=
  fun z hz =>
    let ⟨y, hp, hy⟩ := (def14 P Y z).mp hz
    (def14 R Y z).mpr ⟨y, h _ hp, hy⟩

/-- `RELAT_1:145` -/
theorem th145 (hPR : P ⊆ R) (hXY : X ⊆ Y) : invimage P X ⊆ invimage R Y :=
  XBOOLE_1.th1 (th144 (Y := X) hPR) (th143 (R := R) hXY)

/-- `RELAT_1:146` -/
theorem th146 : invimage (comp P R) Y = invimage P (invimage R Y) := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    obtain ⟨y, hp, hy⟩ := (def14 (comp P R) Y x).mp hx
    obtain ⟨z, hP, hR⟩ := (def8 P R x y).mp hp
    exact (def14 P (invimage R Y) x).mpr
      ⟨z, hP, (def14 R Y z).mpr ⟨y, hR, hy⟩⟩
  · intro hx
    obtain ⟨z, hP, hz⟩ := (def14 P (invimage R Y) x).mp hx
    obtain ⟨y, hR, hy⟩ := (def14 R Y z).mp hz
    exact (def14 (comp P R) Y x).mpr
      ⟨y, (def8 P R x y).mpr ⟨z, hP, hR⟩, hy⟩

/-- `RELAT_1:147` (`Th147`) -/
theorem th147 : dom (comp P R) = invimage P (dom R) := by
  apply eq_of_mem
  intro z
  constructor
  · intro hz
    obtain ⟨x, hp⟩ := (dom_iff (comp P R) z).mp hz
    obtain ⟨y, hP, hR⟩ := (def8 P R z x).mp hp
    exact (def14 P (dom R) z).mpr ⟨y, hP, pair_mem_dom hR⟩
  · intro hz
    obtain ⟨y, hP, hy⟩ := (def14 P (dom R) z).mp hz
    obtain ⟨x, hR⟩ := (dom_iff R y).mp hy
    exact (dom_iff (comp P R) z).mpr ⟨x, (def8 P R z x).mpr ⟨y, hP, hR⟩⟩

/-- `RELAT_1:148` -/
theorem th148 : rng R ∩ Y ⊆ invimage (converse R) (invimage R Y) :=
  fun y hy =>
    let ⟨hr, hyY⟩ := (XBOOLE_0.def4 (rng R) Y y).mp hy
    let ⟨x, hp⟩ := (rng_iff R y).mp hr
    (def14 (converse R) (invimage R Y) y).mpr
      ⟨x, (def7 R y x).mpr hp, (def14 R Y x).mpr ⟨y, hp, hyY⟩⟩

/-- `RELAT_1:def 15` — empty-yielding. -/
def isEmptyYieldingSet (R : TarskiSet.{u}) : Prop :=
  rng R ⊆ TARSKI.singleton (∅ : TarskiSet.{u})

theorem def15 (R : TarskiSet.{u}) :
    isEmptyYieldingSet R ↔ rng R ⊆ TARSKI.singleton (∅ : TarskiSet.{u}) :=
  Iff.rfl

/-- `RELAT_1:149` -/
theorem th149 : isEmptyYieldingSet R ↔
    ∀ X, X ∈ rng R → X = (∅ : TarskiSet.{u}) :=
  ⟨fun h X hx => (singleton_iff _ X).mp (h X hx),
    fun h X hx => (singleton_iff (∅ : TarskiSet.{u}) X).mpr (h X hx)⟩

/-- `RELAT_1:sch ExtensionalityR` -/
theorem sch_ExtensionalityR {A B : TarskiSet.{u}}
    (hA : isRelation A) (hB : isRelation B)
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (h1 : ∀ a b, TARSKI.pair a b ∈ A ↔ P a b)
    (h2 : ∀ a b, TARSKI.pair a b ∈ B ↔ P a b) : A = B :=
  rel_eq hA hB fun a b => (h1 a b).trans (h2 a b).symm

/-- `RELAT_1:150` -/
theorem th150 (hA : restrict f A = restrict g A)
    (hB : restrict f B = restrict g B) :
    restrict f (A ∪ B) = restrict g (A ∪ B) :=
  (((th78 (R := f) (X := A) (Y := B)).trans
      (congrArg (fun s => s ∪ restrict f B) hA)).trans
      (congrArg (fun s => restrict g A ∪ s) hB)).trans
    (th78 (R := g) (X := A) (Y := B)).symm

/-- `RELAT_1:151` -/
theorem th151 {f g X : TarskiSet.{u}} (hg : isRelation g)
    (hdom : dom g ⊆ X) (hsub : g ⊆ f) : g ⊆ restrict f X :=
  th69 hg ▸ th77 hsub hdom

/-- `RELAT_1:152` -/
theorem th152 (h : XBOOLE_0.misses X (dom f)) :
    restrict f X = (∅ : TarskiSet.{u}) :=
  (th66 (R := f) (X := X)).mpr (XBOOLE_0.misses_symm h)

/-- `RELAT_1:153` -/
theorem th153 (hAB : A ⊆ B) (h : restrict f B = restrict g B) :
    restrict f A = restrict g A := by
  have hAeq : B ∩ A = A :=
    (XBOOLE_0.inter_comm B A).trans (XBOOLE_1.th28 hAB)
  exact
    (((congrArg (restrict f) hAeq.symm).trans
        (th71 (R := f) (X := B) (Y := A)).symm).trans
        (congrArg (fun s => restrict s A) h)).trans
      ((th71 (R := g) (X := B) (Y := A)).trans
        (congrArg (restrict g) hAeq))

/-- `RELAT_1:154` -/
theorem th154 : restrict R (dom S) =
    restrict R (dom (restrict S (dom R))) :=
  rel_eq (restrict_isRelation R (dom S))
    (restrict_isRelation R (dom (restrict S (dom R)))) fun x y => by
      constructor
      · intro hp
        have ⟨hS, hpR⟩ := (def11 R (dom S) x y).mp hp
        have hxI : x ∈ dom S ∩ dom R :=
          (XBOOLE_0.def4 (dom S) (dom R) x).mpr ⟨hS, pair_mem_dom hpR⟩
        have hx : x ∈ dom (restrict S (dom R)) :=
          (th61 (R := S) (X := dom R)).symm ▸ hxI
        exact (def11 R (dom (restrict S (dom R))) x y).mpr ⟨hx, hpR⟩
      · intro hp
        have ⟨hx, hpR⟩ := (def11 R (dom (restrict S (dom R))) x y).mp hp
        have hxI : x ∈ dom S ∩ dom R :=
          (th61 (R := S) (X := dom R)) ▸ hx
        exact (def11 R (dom S) x y).mpr
          ⟨(XBOOLE_0.def4 (dom S) (dom R) x).mp hxI |>.1, hpR⟩

/-- `RELAT_1:155` -/
theorem th155 (h : ¬ isEmptyYieldingSet (restrict R X)) :
    ¬ isEmptyYieldingSet R :=
  fun hR => h (XBOOLE_1.th1 (th70 (R := R) (X := X)) hR)

/-- `RELAT_1:156` -/
theorem th156 : dom (restrict R (dom R \ X)) = dom R \ X :=
  (th61 (R := R) (X := dom R \ X)).trans <|
    (XBOOLE_1.th49 (X := dom R) (Y := dom R) (Z := X)).trans
      (congrArg (fun s => s \ X) (XBOOLE_0.inter_idem (dom R)))

/-- `RELAT_1:157` -/
theorem th157 : restrict R X = restrict R (dom R ∩ X) :=
  rel_eq (restrict_isRelation R X) (restrict_isRelation R (dom R ∩ X))
    fun x y => by
      constructor
      · intro hp
        have ⟨hx, hpR⟩ := (def11 R X x y).mp hp
        exact (def11 R (dom R ∩ X) x y).mpr
          ⟨(XBOOLE_0.def4 (dom R) X x).mpr ⟨pair_mem_dom hpR, hx⟩, hpR⟩
      · intro hp
        have ⟨hxI, hpR⟩ := (def11 R (dom R ∩ X) x y).mp hp
        exact (def11 R X x y).mpr
          ⟨(XBOOLE_0.def4 (dom R) X x).mp hxI |>.2, hpR⟩

/-- `RELAT_1:158` -/
theorem th158 : dom (ZFMISC_1.product X Y) ⊆ X :=
  fun x hx =>
    let ⟨y, hp⟩ := (dom_iff (ZFMISC_1.product X Y) x).mp hx
    (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp hp |>.1

/-- `RELAT_1:159` -/
theorem th159 : rng (ZFMISC_1.product X Y) ⊆ Y :=
  fun y hy =>
    let ⟨x, hp⟩ := (rng_iff (ZFMISC_1.product X Y) y).mp hy
    (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp hp |>.2

/-- `RELAT_1:160` -/
theorem th160 (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u})) :
    dom (ZFMISC_1.product X Y) = X ∧ rng (ZFMISC_1.product X Y) = Y := by
  obtain ⟨a, ha⟩ := exists_mem_of_ne hX
  obtain ⟨b, hb⟩ := exists_mem_of_ne hY
  constructor
  · apply eq_of_mem
    intro x
    constructor
    · intro hx
      exact th158 (X := X) (Y := Y) x hx
    · intro hx
      exact (dom_iff (ZFMISC_1.product X Y) x).mpr
        ⟨b, (ZFMISC_1.th87 (x := x) (y := b) (X := X) (Y := Y)).mpr ⟨hx, hb⟩⟩
  · apply eq_of_mem
    intro y
    constructor
    · intro hy
      exact th159 (X := X) (Y := Y) y hy
    · intro hy
      exact (rng_iff (ZFMISC_1.product X Y) y).mpr
        ⟨a, (ZFMISC_1.th87 (x := a) (y := y) (X := X) (Y := Y)).mpr ⟨ha, hy⟩⟩

/-- `RELAT_1:161` -/
theorem th161 {R Q : TarskiSet.{u}} (hR : isRelation R) (hQ : isRelation Q)
    (hR' : dom R = (∅ : TarskiSet.{u}))
    (hQ' : dom Q = (∅ : TarskiSet.{u})) : R = Q :=
  (th41 hR (Or.inl hR')).trans (th41 hQ (Or.inl hQ')).symm

/-- `RELAT_1:162` -/
theorem th162 {R Q : TarskiSet.{u}} (hR : isRelation R) (hQ : isRelation Q)
    (hR' : rng R = (∅ : TarskiSet.{u}))
    (hQ' : rng Q = (∅ : TarskiSet.{u})) : R = Q :=
  (th41 hR (Or.inr hR')).trans (th41 hQ (Or.inr hQ')).symm

/-- `RELAT_1:163` -/
theorem th163 (h : dom R = dom Q) : dom (comp S R) = dom (comp S Q) :=
  (th147 (P := S) (R := R)).trans
    ((congrArg (invimage S) h).trans (th147 (P := S) (R := Q)).symm)

/-- `RELAT_1:164` -/
theorem th164 (h : rng R = rng Q) : rng (comp R S) = rng (comp Q S) :=
  (th127 (P := R) (R := S)).trans
    ((congrArg (image S) h).trans (th127 (P := Q) (R := S)).symm)

/-- `RELAT_1:165` -/
theorem th165 (h : rng R ⊆ dom (restrict S X)) :
    comp R (restrict S X) = comp R S :=
  XBOOLE_0.eq_iff_subset.mpr
    ⟨th29 (th59 (R := S) (X := X)),
      rel_subset (comp_isRelation R S) fun a b hp =>
        let ⟨c, hR, hS⟩ := (def8 R S a b).mp hp
        have hc : c ∈ X :=
          (th57 (R := S) (X := X) (x := c)).mp (h c (pair_mem_rng hR)) |>.1
        (def8 R (restrict S X) a b).mpr
          ⟨c, hR, (def11 S X c b).mpr ⟨hc, hS⟩⟩⟩

/-- `RELAT_1:166` -/
theorem th166 (h : restrict Q A = restrict R A) :
    image Q A = image R A :=
  ((th129 (R := Q) (X := A) (Y := A) (subset_refl A)).symm.trans
      (congrArg (fun s => image s A) h)).trans
    (th129 (R := R) (X := A) (Y := A) (subset_refl A))

/-- `RELAT_1:167` -/
theorem th167 (h : isXvalued R D) (hy : y ∈ rng R) : y ∈ D :=
  h y hy

/-- `RELAT_1:168` -/
theorem th168 (hx : x ∈ X) : Im (ZFMISC_1.product X Y) x = Y := by
  apply eq_of_mem
  intro y
  constructor
  · intro hy
    obtain ⟨z, hp, hz⟩ := (def13 (ZFMISC_1.product X Y) (TARSKI.singleton x) y).mp hy
    exact (ZFMISC_1.th87 (x := z) (y := y) (X := X) (Y := Y)).mp hp |>.2
  · intro hy
    exact (def13 (ZFMISC_1.product X Y) (TARSKI.singleton x) y).mpr
      ⟨x, (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mpr ⟨hx, hy⟩,
        (singleton_iff x x).mpr rfl⟩

/-- `RELAT_1:169` (`Th169`) -/
theorem th169 : TARSKI.pair x y ∈ R ↔ y ∈ Im R x :=
  ⟨fun hp => (def13 R (TARSKI.singleton x) y).mpr
      ⟨x, hp, (singleton_iff x x).mpr rfl⟩,
    fun hy =>
      let ⟨z, hp, hz⟩ := (def13 R (TARSKI.singleton x) y).mp hy
      (singleton_iff x z).mp hz ▸ hp⟩

/-- `RELAT_1:170` -/
theorem th170 : x ∈ dom R ↔ Im R x ≠ (∅ : TarskiSet.{u}) := by
  constructor
  · intro hx
    obtain ⟨y, hp⟩ := (dom_iff R x).mp hx
    exact fun him =>
      (XBOOLE_0.empty_iff y).mp (him ▸ (th169 (R := R) (x := x) (y := y)).mp hp)
  · intro hne
    obtain ⟨y, hy⟩ := exists_mem_of_ne hne
    exact pair_mem_dom ((th169 (R := R) (x := x) (y := y)).mpr hy)

/-- `RELAT_1:171` -/
theorem th171 : isXdefined (∅ : TarskiSet.{u}) X ∧
    isXvalued (∅ : TarskiSet.{u}) Y :=
  ⟨fun x hx => ((XBOOLE_0.empty_iff x).mp (th38.1 ▸ hx)).elim,
    fun y hy => ((XBOOLE_0.empty_iff y).mp (th38.2 ▸ hy)).elim⟩

/-- `RELAT_1:172` -/
theorem th172 (h : XBOOLE_0.misses X Y) :
    restrict (restrict R X) Y = (∅ : TarskiSet.{u}) :=
  (th71 (R := R) (X := X) (Y := Y)).trans
    ((congrArg (restrict R) h).trans (th81 (R := R)))

/-- `RELAT_1:173` -/
theorem th173 :
    field (TARSKI.singleton (TARSKI.pair x x)) = TARSKI.singleton x :=
  (th17 (x := x) (y := x)).trans ENUMSET1.th29

/-- `RELAT_1:174` -/
theorem th174 {R X : TarskiSet.{u}} (hR : isRelation R)
    (h : isXdefined R X) : R = restrict R X :=
  (th68 hR h).symm

/-- `RELAT_1:175` -/
theorem th175 {S R X : TarskiSet.{u}} (hR : isRelation R)
    (h : isXdefined R X) (hsub : R ⊆ S) : R ⊆ restrict S X :=
  th174 hR h ▸ th76 hsub

/-- `RELAT_1:176` (`Th176`) -/
theorem th176 {R X A : TarskiSet.{u}} (hR : isRelation R) (h : dom R ⊆ X) :
    R \ restrict R A = restrict R (X \ A) :=
  ((congrArg (fun s => s \ restrict R A) (th68 hR h).symm).trans
      (th80 (R := R) (X := X) (Y := A)).symm)

/-- `RELAT_1:177` (`Th177`) -/
theorem th177 {R A : TarskiSet.{u}} (hR : isRelation R) :
    dom (R \ restrict R A) = dom R \ A :=
  (congrArg dom (th176 hR (subset_refl (dom R)))).trans
    (th61 (R := R) (X := dom R \ A)) |>.trans
      ((XBOOLE_1.th49 (X := dom R) (Y := dom R) (Z := A)).trans
        (congrArg (fun s => s \ A) (XBOOLE_0.inter_idem (dom R))))

/-- `RELAT_1:178` -/
theorem th178 {R A : TarskiSet.{u}} (hR : isRelation R) :
    dom R \ dom (restrict R A) = dom (R \ restrict R A) :=
  (congrArg (fun s => dom R \ s) (th61 (R := R) (X := A))).trans <|
    (XBOOLE_1.th47 (X := dom R) (Y := A)).trans
      (th177 hR).symm

/-- `RELAT_1:179` -/
theorem th179 {R S : TarskiSet.{u}} (hR : isRelation R)
    (h : XBOOLE_0.misses (dom R) (dom S)) : XBOOLE_0.misses R S := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    have ⟨hxR, hxS⟩ := (XBOOLE_0.def4 R S x).mp hx
    obtain ⟨y, _, heq⟩ := hR x hxR
    exact ((XBOOLE_0.empty_iff y).mp
      (h ▸ (XBOOLE_0.def4 (dom R) (dom S) y).mpr
        ⟨pair_mem_dom (heq ▸ hxR), pair_mem_dom (heq ▸ hxS)⟩)).elim
  · intro hx
    exact ((XBOOLE_0.empty_iff x).mp hx).elim

/-- `RELAT_1:180` -/
theorem th180 {R S : TarskiSet.{u}} (hR : isRelation R)
    (h : XBOOLE_0.misses (rng R) (rng S)) : XBOOLE_0.misses R S := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    have ⟨hxR, hxS⟩ := (XBOOLE_0.def4 R S x).mp hx
    obtain ⟨_, z, heq⟩ := hR x hxR
    exact ((XBOOLE_0.empty_iff z).mp
      (h ▸ (XBOOLE_0.def4 (rng R) (rng S) z).mpr
        ⟨pair_mem_rng (heq ▸ hxR), pair_mem_rng (heq ▸ hxS)⟩)).elim
  · intro hx
    exact ((XBOOLE_0.empty_iff x).mp hx).elim

/-- `RELAT_1:181` -/
theorem th181 {R X Y : TarskiSet.{u}} (hR : isRelation R) (h : X ⊆ Y) :
    restrict (R \ restrict R Y) X = (∅ : TarskiSet.{u}) := by
  have hsub : dom R ∩ X ⊆ Y :=
    fun z hz => h z ((XBOOLE_0.def4 (dom R) X z).mp hz).2
  have hdom : dom (restrict (R \ restrict R Y) X) = (∅ : TarskiSet.{u}) :=
    (th61 (R := R \ restrict R Y) (X := X)).trans <|
      (congrArg (fun s => s ∩ X) (th177 hR)).trans <|
        (XBOOLE_0.inter_comm (dom R \ Y) X).trans <|
          (XBOOLE_1.th49 (X := X) (Y := dom R) (Z := Y)).trans <|
            ((XBOOLE_0.inter_comm X (dom R)).symm ▸
              (XBOOLE_1.th37 (X := dom R ∩ X) (Y := Y)).mpr hsub)
  exact th41 (restrict_isRelation _ _) (Or.inl hdom)

/-- `RELAT_1:182` -/
theorem th182 (h : X ⊆ Y) (hR : isXdefined R X) : isXdefined R Y :=
  XBOOLE_1.th1 hR h

/-- `RELAT_1:183` -/
theorem th183 (h : X ⊆ Y) (hR : isXvalued R X) : isXvalued R Y :=
  XBOOLE_1.th1 hR h

/-- `RELAT_1:184` -/
theorem th184 {R S : TarskiSet.{u}} (hR : isRelation R) :
    R ⊆ S ↔ R ⊆ restrict S (dom R) :=
  ⟨fun hsub =>
      rel_subset hR fun a b hp =>
        (def11 S (dom R) a b).mpr ⟨pair_mem_dom hp, hsub _ hp⟩,
    fun hsub => XBOOLE_1.th1 hsub (th59 (R := S) (X := dom R))⟩

/-- `RELAT_1:185` -/
theorem th185 {R X Y : TarskiSet.{u}} (hR : isRelation R)
    (hd : isXdefined R X) (hv : isXvalued R Y) :
    R ⊆ ZFMISC_1.product X Y :=
  XBOOLE_1.th1 (th7 hR) (ZFMISC_1.th96 hd hv)

/-- `RELAT_1:186` (`Th186`) -/
theorem th186 : dom (restrictRng X R) ⊆ dom R :=
  (th11 (th86 (Y := X) (R := R))).1

end RELAT_1







