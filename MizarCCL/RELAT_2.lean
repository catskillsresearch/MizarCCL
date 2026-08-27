import MizarCCL.RELAT_1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/relat_2.miz`.
Authors: Edmund Woronowicz and Anna Zalewska (Mizar),
  Lars Warren Ericson (Lean 4).
-/

/-!
# Properties of Binary Relations

1–1 Lean rendering of Mizar article `RELAT_2`
(`vendor/mml/relat_2.miz`). Reflexive, symmetric, transitive, and
related attributes of a relation, on a set and on the field.
Import is `RELAT_1` only. Canceled: `th5`–`th11`, `th14`–`th21`,
`th23`–`th26`, `th29`.
-/

universe u

open TarskiSet TARSKI

namespace RELAT_2

def isReflexiveIn (R X : TarskiSet.{u}) : Prop :=
  ∀ x, x ∈ X → TARSKI.pair x x ∈ R

theorem def1 (R X : TarskiSet.{u}) :
    isReflexiveIn R X ↔ ∀ x, x ∈ X → TARSKI.pair x x ∈ R :=
  Iff.rfl

def isIrreflexiveIn (R X : TarskiSet.{u}) : Prop :=
  ∀ x, x ∈ X → TARSKI.pair x x ∉ R

theorem def2 (R X : TarskiSet.{u}) :
    isIrreflexiveIn R X ↔ ∀ x, x ∈ X → TARSKI.pair x x ∉ R :=
  Iff.rfl

def isSymmetricIn (R X : TarskiSet.{u}) : Prop :=
  ∀ x y, x ∈ X → y ∈ X → TARSKI.pair x y ∈ R → TARSKI.pair y x ∈ R

theorem def3 (R X : TarskiSet.{u}) :
    isSymmetricIn R X ↔
      ∀ x y, x ∈ X → y ∈ X → TARSKI.pair x y ∈ R → TARSKI.pair y x ∈ R :=
  Iff.rfl

def isAntisymmetricIn (R X : TarskiSet.{u}) : Prop :=
  ∀ x y, x ∈ X → y ∈ X → TARSKI.pair x y ∈ R → TARSKI.pair y x ∈ R → x = y

theorem def4 (R X : TarskiSet.{u}) :
    isAntisymmetricIn R X ↔
      ∀ x y, x ∈ X → y ∈ X → TARSKI.pair x y ∈ R → TARSKI.pair y x ∈ R →
        x = y :=
  Iff.rfl

def isAsymmetricIn (R X : TarskiSet.{u}) : Prop :=
  ∀ x y, x ∈ X → y ∈ X → TARSKI.pair x y ∈ R → TARSKI.pair y x ∉ R

theorem def5 (R X : TarskiSet.{u}) :
    isAsymmetricIn R X ↔
      ∀ x y, x ∈ X → y ∈ X → TARSKI.pair x y ∈ R → TARSKI.pair y x ∉ R :=
  Iff.rfl

def isConnectedIn (R X : TarskiSet.{u}) : Prop :=
  ∀ x y, x ∈ X → y ∈ X → x ≠ y →
    TARSKI.pair x y ∈ R ∨ TARSKI.pair y x ∈ R

theorem def6 (R X : TarskiSet.{u}) :
    isConnectedIn R X ↔
      ∀ x y, x ∈ X → y ∈ X → x ≠ y →
        TARSKI.pair x y ∈ R ∨ TARSKI.pair y x ∈ R :=
  Iff.rfl

def isStronglyConnectedIn (R X : TarskiSet.{u}) : Prop :=
  ∀ x y, x ∈ X → y ∈ X → TARSKI.pair x y ∈ R ∨ TARSKI.pair y x ∈ R

theorem def7 (R X : TarskiSet.{u}) :
    isStronglyConnectedIn R X ↔
      ∀ x y, x ∈ X → y ∈ X → TARSKI.pair x y ∈ R ∨ TARSKI.pair y x ∈ R :=
  Iff.rfl

def isTransitiveIn (R X : TarskiSet.{u}) : Prop :=
  ∀ x y z, x ∈ X → y ∈ X → z ∈ X →
    TARSKI.pair x y ∈ R → TARSKI.pair y z ∈ R → TARSKI.pair x z ∈ R

theorem def8 (R X : TarskiSet.{u}) :
    isTransitiveIn R X ↔
      ∀ x y z, x ∈ X → y ∈ X → z ∈ X →
        TARSKI.pair x y ∈ R → TARSKI.pair y z ∈ R → TARSKI.pair x z ∈ R :=
  Iff.rfl

def isReflexive (R : TarskiSet.{u}) : Prop := isReflexiveIn R (RELAT_1.field R)
def isIrreflexive (R : TarskiSet.{u}) : Prop := isIrreflexiveIn R (RELAT_1.field R)
def isSymmetric (R : TarskiSet.{u}) : Prop := isSymmetricIn R (RELAT_1.field R)
def isAntisymmetric (R : TarskiSet.{u}) : Prop :=
  isAntisymmetricIn R (RELAT_1.field R)
def isAsymmetric (R : TarskiSet.{u}) : Prop := isAsymmetricIn R (RELAT_1.field R)
def isConnected (R : TarskiSet.{u}) : Prop := isConnectedIn R (RELAT_1.field R)
def isStronglyConnected (R : TarskiSet.{u}) : Prop :=
  isStronglyConnectedIn R (RELAT_1.field R)
def isTransitive (R : TarskiSet.{u}) : Prop := isTransitiveIn R (RELAT_1.field R)

theorem def9 (R : TarskiSet.{u}) : isReflexive R ↔ isReflexiveIn R (RELAT_1.field R) := Iff.rfl
theorem def10 (R : TarskiSet.{u}) : isIrreflexive R ↔ isIrreflexiveIn R (RELAT_1.field R) := Iff.rfl
theorem def11 (R : TarskiSet.{u}) : isSymmetric R ↔ isSymmetricIn R (RELAT_1.field R) := Iff.rfl
theorem def12 (R : TarskiSet.{u}) : isAntisymmetric R ↔ isAntisymmetricIn R (RELAT_1.field R) := Iff.rfl
theorem def13 (R : TarskiSet.{u}) : isAsymmetric R ↔ isAsymmetricIn R (RELAT_1.field R) := Iff.rfl
theorem def14 (R : TarskiSet.{u}) : isConnected R ↔ isConnectedIn R (RELAT_1.field R) := Iff.rfl
theorem def15 (R : TarskiSet.{u}) : isStronglyConnected R ↔ isStronglyConnectedIn R (RELAT_1.field R) := Iff.rfl
theorem def16 (R : TarskiSet.{u}) : isTransitive R ↔ isTransitiveIn R (RELAT_1.field R) := Iff.rfl

theorem empty_field_vacuous {P : TarskiSet.{u} → Prop} :
    ∀ x, x ∈ RELAT_1.field (∅ : TarskiSet.{u}) → P x :=
  fun x hx =>
    ((XBOOLE_0.empty_iff x).mp (RELAT_1.th40 ▸ hx)).elim

theorem empty_isReflexive : isReflexive (∅ : TarskiSet.{u}) :=
  empty_field_vacuous

theorem empty_isIrreflexive : isIrreflexive (∅ : TarskiSet.{u}) :=
  empty_field_vacuous

theorem empty_isSymmetric : isSymmetric (∅ : TarskiSet.{u}) :=
  fun x _ hx _ _ => (empty_field_vacuous (P := fun _ => False) x hx).elim

theorem empty_isAntisymmetric : isAntisymmetric (∅ : TarskiSet.{u}) :=
  fun x _ hx _ _ => (empty_field_vacuous (P := fun _ => False) x hx).elim

theorem empty_isAsymmetric : isAsymmetric (∅ : TarskiSet.{u}) :=
  fun x _ hx _ => (empty_field_vacuous (P := fun _ => False) x hx).elim

theorem empty_isConnected : isConnected (∅ : TarskiSet.{u}) :=
  fun x _ hx _ _ => (empty_field_vacuous (P := fun _ => False) x hx).elim

theorem empty_isStronglyConnected : isStronglyConnected (∅ : TarskiSet.{u}) :=
  fun x _ hx _ => (empty_field_vacuous (P := fun _ => False) x hx).elim

theorem empty_isTransitive : isTransitive (∅ : TarskiSet.{u}) :=
  fun x _ _ hx _ _ => (empty_field_vacuous (P := fun _ => False) x hx).elim

/-- `RELAT_2:1` -/
theorem th1 {R : TarskiSet.{u}} (_hR : RELAT_1.isRelation R) :
    isReflexive R ↔ RELAT_1.id (RELAT_1.field R) ⊆ R := by
  constructor
  · intro href
    exact RELAT_1.rel_subset (RELAT_1.id_isRelation (RELAT_1.field R))
      fun a b hp =>
        let ⟨ha, heq⟩ := (RELAT_1.def10 (RELAT_1.field R) a b).mp hp
        heq ▸ href a ha
  · intro hid a ha
    exact hid _ ((RELAT_1.def10 (RELAT_1.field R) a a).mpr ⟨ha, rfl⟩)

/-- `RELAT_2:2` -/
theorem th2 {R : TarskiSet.{u}} (_hR : RELAT_1.isRelation R) :
    isIrreflexive R ↔
      XBOOLE_0.misses (RELAT_1.id (RELAT_1.field R)) R := by
  constructor
  · intro hir
    have hnone : ∀ a b, TARSKI.pair a b ∉
        RELAT_1.id (RELAT_1.field R) ∩ R := fun a b hp =>
      let ⟨hid, hRpair⟩ :=
        (XBOOLE_0.def4 (RELAT_1.id (RELAT_1.field R)) R (TARSKI.pair a b)).mp hp
      let ⟨ha, heq⟩ := (RELAT_1.def10 (RELAT_1.field R) a b).mp hid
      hir a ha (heq ▸ hRpair)
    exact (XBOOLE_0.def7 (RELAT_1.id (RELAT_1.field R)) R).mpr
      (RELAT_1.th37 (RELAT_1.inter_isRelation (RELAT_1.id_isRelation _) (X := R))
        hnone)
  · intro hmiss a ha hp
    exact (XBOOLE_0.empty_iff (TARSKI.pair a a)).mp
      (Eq.subst (motive := fun s => TARSKI.pair a a ∈ s)
        ((XBOOLE_0.def7 (RELAT_1.id (RELAT_1.field R)) R).mp hmiss)
        ((XBOOLE_0.def4 (RELAT_1.id (RELAT_1.field R)) R
          (TARSKI.pair a a)).mpr
          ⟨(RELAT_1.def10 (RELAT_1.field R) a a).mpr ⟨ha, rfl⟩, hp⟩))

/-- `RELAT_2:3` -/
theorem th3 {R X : TarskiSet.{u}} :
    isAntisymmetricIn R X ↔ isAsymmetricIn (R \ RELAT_1.id X) X := by
  constructor
  · intro hanti x y hx hy hp
    have ⟨hpR, hnid⟩ := (XBOOLE_0.def5 R (RELAT_1.id X) (TARSKI.pair x y)).mp hp
    have hne : x ≠ y := fun heq =>
      hnid ((RELAT_1.def10 X x y).mpr ⟨hx, heq⟩)
    intro hp2
    have hp2R := ((XBOOLE_0.def5 R (RELAT_1.id X) (TARSKI.pair y x)).mp hp2).1
    exact hne (hanti x y hx hy hpR hp2R)
  · intro hasym x y hx hy hxy hyx
    refine Classical.byContradiction fun hne => ?_
    have hnid1 : TARSKI.pair x y ∉ RELAT_1.id X := fun hid =>
      hne ((RELAT_1.def10 X x y).mp hid).2
    have hnid2 : TARSKI.pair y x ∉ RELAT_1.id X := fun hid =>
      hne ((RELAT_1.def10 X y x).mp hid).2.symm
    exact hasym x y hx hy
      ((XBOOLE_0.def5 R (RELAT_1.id X) (TARSKI.pair x y)).mpr ⟨hxy, hnid1⟩)
      ((XBOOLE_0.def5 R (RELAT_1.id X) (TARSKI.pair y x)).mpr ⟨hyx, hnid2⟩)

/-- `RELAT_2:4` -/
theorem th4 {R X : TarskiSet.{u}} (h : isAsymmetricIn R X) :
    isAntisymmetricIn (R ∪ RELAT_1.id X) X :=
  fun x y hx hy hxy hyx =>
    Classical.byContradiction fun hne =>
      let hnid1 : TARSKI.pair x y ∉ RELAT_1.id X := fun hid =>
        hne ((RELAT_1.def10 X x y).mp hid).2
      let hnid2 : TARSKI.pair y x ∉ RELAT_1.id X := fun hid =>
        hne ((RELAT_1.def10 X y x).mp hid).2.symm
      let hpR : TARSKI.pair x y ∈ R :=
        ((XBOOLE_0.def3 R (RELAT_1.id X) (TARSKI.pair x y)).mp hxy).elim
          (fun hpR => hpR) fun hid => (hnid1 hid).elim
      let hqR : TARSKI.pair y x ∈ R :=
        ((XBOOLE_0.def3 R (RELAT_1.id X) (TARSKI.pair y x)).mp hyx).elim
          (fun hpR => hpR) fun hid => (hnid2 hid).elim
      h x y hx hy hpR hqR


theorem field_mem_of_pair {R a b : TarskiSet.{u}}
    (h : TARSKI.pair a b ∈ R) : a ∈ RELAT_1.field R ∧ b ∈ RELAT_1.field R :=
  RELAT_1.th15 (R := R) (a := a) (b := b) h

theorem symmetric_transitive_isReflexive {R : TarskiSet.{u}}
    (hsym : isSymmetric R) (htr : isTransitive R) : isReflexive R := by
  intro a ha
  have o := (XBOOLE_0.def3 (RELAT_1.dom R) (RELAT_1.rng R) a).mp ha
  exact Or.elim o
    (fun hd =>
      let ⟨ y, hp ⟩ := (RELAT_1.dom_iff R a).mp hd
      let ⟨ ha', hb ⟩ := field_mem_of_pair hp
      htr a y a ha' hb ha' hp (hsym a y ha' hb hp))
    (fun hr =>
      let ⟨ y, hp ⟩ := (RELAT_1.rng_iff R a).mp hr
      let ⟨ hy, ha' ⟩ := field_mem_of_pair hp
      htr a y a ha' hy ha' (hsym y a hy ha' hp) hp)

theorem id_isSymmetric (X : TarskiSet.{u}) : isSymmetric (RELAT_1.id X) :=
  fun a b _ _ hp =>
    let ⟨ _ha, heq ⟩ := (RELAT_1.def10 X a b).mp hp
    heq ▸ (heq.symm ▸ hp)

theorem id_isTransitive (X : TarskiSet.{u}) : isTransitive (RELAT_1.id X) :=
  fun a b c _ _ _ hab hbc =>
    let ⟨ ha, heq1 ⟩ := (RELAT_1.def10 X a b).mp hab
    let ⟨ _hb, heq2 ⟩ := (RELAT_1.def10 X b c).mp hbc
    (RELAT_1.def10 X a c).mpr ⟨ ha, heq1.trans heq2 ⟩

theorem id_isAntisymmetric (X : TarskiSet.{u}) : isAntisymmetric (RELAT_1.id X) :=
  fun a b _ _ hp _ => ((RELAT_1.def10 X a b).mp hp).2

theorem irreflexive_transitive_isAsymmetric {R : TarskiSet.{u}}
    (hir : isIrreflexive R) (htr : isTransitive R) : isAsymmetric R :=
  fun a b ha hb hab hba => hir a ha (htr a b a ha hb ha hab hba)

theorem asymmetric_isIrreflexive {R : TarskiSet.{u}} (h : isAsymmetric R) :
    isIrreflexive R :=
  fun x hx hp => h x x hx hx hp hp

theorem asymmetric_isAntisymmetric {R : TarskiSet.{u}} (h : isAsymmetric R) :
    isAntisymmetric R :=
  fun x y hx hy hxy hyx => (h x y hx hy hxy hyx).elim

theorem converse_isReflexive {R : TarskiSet.{u}} (h : isReflexive R) :
    isReflexive (RELAT_1.converse R) :=
  fun x hx =>
    (RELAT_1.def7 R x x).mpr
      (h x (Eq.subst (motive := fun d => x ∈ d) (RELAT_1.th21 (R := R)).symm hx))

theorem converse_isIrreflexive {R : TarskiSet.{u}} (h : isIrreflexive R) :
    isIrreflexive (RELAT_1.converse R) :=
  fun x hx hp =>
    h x (Eq.subst (motive := fun d => x ∈ d) (RELAT_1.th21 (R := R)).symm hx)
      ((RELAT_1.def7 R x x).mp hp)

/-- `RELAT_2:12` -/
theorem th12 {R : TarskiSet.{u}} (h : isReflexive R) :
    RELAT_1.dom R = RELAT_1.dom (RELAT_1.converse R) ∧
      RELAT_1.rng R = RELAT_1.rng (RELAT_1.converse R) := by
  have hc := converse_isReflexive h
  have hfield := RELAT_1.th21 (R := R)
  constructor
  · apply TARSKI.extensionality
    intro x
    constructor
    · intro hx
      have hf : x ∈ RELAT_1.field R :=
        (XBOOLE_0.def3 (RELAT_1.dom R) (RELAT_1.rng R) x).mpr (Or.inl hx)
      exact RELAT_1.pair_mem_dom ((RELAT_1.def7 R x x).mpr (h x hf))
    · intro hx
      have hf : x ∈ RELAT_1.field (RELAT_1.converse R) :=
        (XBOOLE_0.def3 (RELAT_1.dom (RELAT_1.converse R))
          (RELAT_1.rng (RELAT_1.converse R)) x).mpr (Or.inl hx)
      exact RELAT_1.pair_mem_dom ((RELAT_1.def7 R x x).mp (hc x hf))
  · apply TARSKI.extensionality
    intro x
    constructor
    · intro hx
      have hf : x ∈ RELAT_1.field R :=
        (XBOOLE_0.def3 (RELAT_1.dom R) (RELAT_1.rng R) x).mpr (Or.inr hx)
      exact RELAT_1.pair_mem_rng ((RELAT_1.def7 R x x).mpr (h x hf))
    · intro hx
      have hf : x ∈ RELAT_1.field (RELAT_1.converse R) :=
        (XBOOLE_0.def3 (RELAT_1.dom (RELAT_1.converse R))
          (RELAT_1.rng (RELAT_1.converse R)) x).mpr (Or.inr hx)
      exact RELAT_1.pair_mem_rng ((RELAT_1.def7 R x x).mp (hc x hf))

/-- `RELAT_2:13` (`Th13`) -/
theorem th13 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    isSymmetric R ↔ R = RELAT_1.converse R := by
  constructor
  · intro hsym
    exact RELAT_1.rel_eq hR (RELAT_1.converse_isRelation R) fun a b =>
      ⟨ fun hp =>
        let ⟨ ha, hb ⟩ := field_mem_of_pair hp
        (RELAT_1.def7 R a b).mpr (hsym a b ha hb hp),
      fun hp =>
        let hba := (RELAT_1.def7 R a b).mp hp
        let ⟨ hb, ha ⟩ := field_mem_of_pair hba
        hsym b a hb ha hba ⟩
  · intro heq a b _ _ hp
    exact (RELAT_1.def7 R a b).mp
      (Eq.subst (motive := fun s => TARSKI.pair a b ∈ s) heq hp)

theorem union_isReflexive {P R : TarskiSet.{u}}
    (hP : isReflexive P) (hR : isReflexive R) : isReflexive (P ∪ R) := by
  intro a ha
  have hf := Eq.subst (motive := fun d => a ∈ d)
    (RELAT_1.th18 (P := P) (R := R)) ha
  exact Or.elim ((XBOOLE_0.def3 (RELAT_1.field P) (RELAT_1.field R) a).mp hf)
    (fun hfp => (XBOOLE_0.def3 P R (TARSKI.pair a a)).mpr (Or.inl (hP a hfp)))
    (fun hfr => (XBOOLE_0.def3 P R (TARSKI.pair a a)).mpr (Or.inr (hR a hfr)))

theorem inter_isReflexive {P R : TarskiSet.{u}}
    (hP : isReflexive P) (hR : isReflexive R) : isReflexive (P ∩ R) := by
  intro a ha
  have hsub := RELAT_1.th19 (P := P) (R := R) a ha
  have ⟨ hfp, hfr ⟩ := (XBOOLE_0.def4 (RELAT_1.field P) (RELAT_1.field R) a).mp hsub
  exact (XBOOLE_0.def4 P R (TARSKI.pair a a)).mpr ⟨ hP a hfp, hR a hfr ⟩

theorem pair_not_mem_of_not_field {R a : TarskiSet.{u}}
    (h : a ∉ RELAT_1.field R) : TARSKI.pair a a ∉ R :=
  fun hp => h (field_mem_of_pair hp).1

theorem union_isIrreflexive {P R : TarskiSet.{u}}
    (hP : isIrreflexive P) (hR : isIrreflexive R) : isIrreflexive (P ∪ R) := by
  intro a ha hp
  have hf := Eq.subst (motive := fun d => a ∈ d)
    (RELAT_1.th18 (P := P) (R := R)) ha
  have o := (XBOOLE_0.def3 P R (TARSKI.pair a a)).mp hp
  exact Or.elim ((XBOOLE_0.def3 (RELAT_1.field P) (RELAT_1.field R) a).mp hf)
    (fun hfp => Or.elim o (hP a hfp) fun hRaa =>
      hR a (field_mem_of_pair hRaa).1 hRaa)
    (fun hfr => Or.elim o (fun hPaa =>
      hP a (field_mem_of_pair hPaa).1 hPaa) (hR a hfr))

theorem inter_isIrreflexive {P R : TarskiSet.{u}}
    (hP : isIrreflexive P) : isIrreflexive (P ∩ R) :=
  fun a ha hp =>
    hP a ((XBOOLE_0.def4 (RELAT_1.field P) (RELAT_1.field R) a).mp
        (RELAT_1.th19 (P := P) (R := R) a ha)).1
      ((XBOOLE_0.def4 P R (TARSKI.pair a a)).mp hp).1

theorem diff_isIrreflexive {P R : TarskiSet.{u}}
    (hP : isIrreflexive P) : isIrreflexive (P \ R) :=
  fun a _ha hp =>
    let hpP := ((XBOOLE_0.def5 P R (TARSKI.pair a a)).mp hp).1
    -- a in field (P \ R) implies a in field P via the pair in P
    hP a (field_mem_of_pair hpP).1 hpP

/-- `RELAT_2:13` also gives converse of a symmetric relation. -/
theorem converse_isSymmetric {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (h : isSymmetric R) : isSymmetric (RELAT_1.converse R) :=
  (th13 (RELAT_1.converse_isRelation R)).mpr
    (((th13 hR).mp h).symm.trans (RELAT_1.converse_involutive hR).symm)

theorem union_isSymmetric {P R : TarskiSet.{u}}
    (hP : isSymmetric P) (hR : isSymmetric R) : isSymmetric (P ∪ R) :=
  fun a b _ _ hp =>
    Or.elim ((XBOOLE_0.def3 P R (TARSKI.pair a b)).mp hp)
      (fun hPab =>
        let ⟨ ha, hb ⟩ := field_mem_of_pair hPab
        (XBOOLE_0.def3 P R (TARSKI.pair b a)).mpr (Or.inl (hP a b ha hb hPab)))
      (fun hRab =>
        let ⟨ ha, hb ⟩ := field_mem_of_pair hRab
        (XBOOLE_0.def3 P R (TARSKI.pair b a)).mpr (Or.inr (hR a b ha hb hRab)))

theorem inter_isSymmetric {P R : TarskiSet.{u}}
    (hP : isSymmetric P) (hR : isSymmetric R) : isSymmetric (P ∩ R) :=
  fun a b _ _ hp =>
    let ⟨ hPab, hRab ⟩ := (XBOOLE_0.def4 P R (TARSKI.pair a b)).mp hp
    let ⟨ haP, hbP ⟩ := field_mem_of_pair hPab
    let ⟨ haR, hbR ⟩ := field_mem_of_pair hRab
    (XBOOLE_0.def4 P R (TARSKI.pair b a)).mpr
      ⟨ hP a b haP hbP hPab, hR a b haR hbR hRab ⟩

theorem diff_isSymmetric {P R : TarskiSet.{u}}
    (hP : isSymmetric P) (hR : isSymmetric R) : isSymmetric (P \ R) :=
  fun a b _ _ hp =>
    let ⟨ hPab, hnR ⟩ := (XBOOLE_0.def5 P R (TARSKI.pair a b)).mp hp
    let ⟨ ha, hb ⟩ := field_mem_of_pair hPab
    have hPba := hP a b ha hb hPab
    have hnRba : TARSKI.pair b a ∉ R := fun hba =>
      Or.elim (Classical.em (a ∈ RELAT_1.field R))
        (fun haR =>
          Or.elim (Classical.em (b ∈ RELAT_1.field R))
            (fun hbR => hnR (hR b a hbR haR hba))
            (fun nfb => nfb (field_mem_of_pair hba).1))
        (fun nfa => nfa (field_mem_of_pair hba).2)
    (XBOOLE_0.def5 P R (TARSKI.pair b a)).mpr ⟨ hPba, hnRba ⟩

theorem converse_isAsymmetric {R : TarskiSet.{u}} (h : isAsymmetric R) :
    isAsymmetric (RELAT_1.converse R) :=
  fun x y hx hy hp hq =>
    h y x
      (Eq.subst (motive := fun d => y ∈ d) (RELAT_1.th21 (R := R)).symm hy)
      (Eq.subst (motive := fun d => x ∈ d) (RELAT_1.th21 (R := R)).symm hx)
      ((RELAT_1.def7 R x y).mp hp) ((RELAT_1.def7 R y x).mp hq)

theorem inter_isAsymmetric {P R : TarskiSet.{u}} (hR : isAsymmetric R) :
    isAsymmetric (P ∩ R) :=
  fun a b _ _ hp hq =>
    let hRab := ((XBOOLE_0.def4 P R (TARSKI.pair a b)).mp hp).2
    let ⟨ ha, hb ⟩ := field_mem_of_pair hRab
    hR a b ha hb hRab ((XBOOLE_0.def4 P R (TARSKI.pair b a)).mp hq).2

theorem diff_isAsymmetric {P R : TarskiSet.{u}} (hP : isAsymmetric P) :
    isAsymmetric (P \ R) :=
  fun a b _ _ hp hq =>
    let hPab := ((XBOOLE_0.def5 P R (TARSKI.pair a b)).mp hp).1
    let ⟨ ha, hb ⟩ := field_mem_of_pair hPab
    hP a b ha hb hPab ((XBOOLE_0.def5 P R (TARSKI.pair b a)).mp hq).1

/-- `RELAT_2:22` -/
theorem th22 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    isAntisymmetric R ↔
      R ∩ RELAT_1.converse R ⊆ RELAT_1.id (RELAT_1.dom R) := by
  constructor
  · intro hanti
    exact RELAT_1.rel_subset
      (RELAT_1.inter_isRelation hR (X := RELAT_1.converse R)) fun a b hp =>
      let ⟨ hRab, hC ⟩ :=
        (XBOOLE_0.def4 R (RELAT_1.converse R) (TARSKI.pair a b)).mp hp
      let hba := (RELAT_1.def7 R a b).mp hC
      let ⟨ ha, hb ⟩ := field_mem_of_pair hRab
      let heq := hanti a b ha hb hRab hba
      (RELAT_1.def10 (RELAT_1.dom R) a b).mpr
        ⟨RELAT_1.pair_mem_dom hRab, heq⟩
  · intro hsub a b _ _ hab hba
    have hp := (XBOOLE_0.def4 R (RELAT_1.converse R) (TARSKI.pair a b)).mpr
      ⟨ hab, (RELAT_1.def7 R a b).mpr hba ⟩
    exact ((RELAT_1.def10 (RELAT_1.dom R) a b).mp (hsub _ hp)).2

theorem converse_isAntisymmetric {R : TarskiSet.{u}} (h : isAntisymmetric R) :
    isAntisymmetric (RELAT_1.converse R) :=
  fun x y hx hy hxy hyx =>
    (h y x
      (Eq.subst (motive := fun d => y ∈ d) (RELAT_1.th21 (R := R)).symm hy)
      (Eq.subst (motive := fun d => x ∈ d) (RELAT_1.th21 (R := R)).symm hx)
      ((RELAT_1.def7 R x y).mp hxy) ((RELAT_1.def7 R y x).mp hyx)).symm

theorem inter_isAntisymmetric {P R : TarskiSet.{u}} (hP : isAntisymmetric P) :
    isAntisymmetric (P ∩ R) :=
  fun a b _ _ hab hba =>
    let hPab := ((XBOOLE_0.def4 P R (TARSKI.pair a b)).mp hab).1
    let ⟨ ha, hb ⟩ := field_mem_of_pair hPab
    hP a b ha hb hPab ((XBOOLE_0.def4 P R (TARSKI.pair b a)).mp hba).1

theorem diff_isAntisymmetric {P R : TarskiSet.{u}} (hP : isAntisymmetric P) :
    isAntisymmetric (P \ R) :=
  fun a b _ _ hab hba =>
    let hPab := ((XBOOLE_0.def5 P R (TARSKI.pair a b)).mp hab).1
    let ⟨ ha, hb ⟩ := field_mem_of_pair hPab
    hP a b ha hb hPab ((XBOOLE_0.def5 P R (TARSKI.pair b a)).mp hba).1

theorem converse_isTransitive {R : TarskiSet.{u}} (h : isTransitive R) :
    isTransitive (RELAT_1.converse R) :=
  fun x y z hx hy hz hxy hyz =>
    (RELAT_1.def7 R x z).mpr
      (h z y x
        (Eq.subst (motive := fun d => z ∈ d) (RELAT_1.th21 (R := R)).symm hz)
        (Eq.subst (motive := fun d => y ∈ d) (RELAT_1.th21 (R := R)).symm hy)
        (Eq.subst (motive := fun d => x ∈ d) (RELAT_1.th21 (R := R)).symm hx)
        ((RELAT_1.def7 R y z).mp hyz) ((RELAT_1.def7 R x y).mp hxy))

theorem inter_isTransitive {P R : TarskiSet.{u}}
    (hP : isTransitive P) (hR : isTransitive R) : isTransitive (P ∩ R) :=
  fun a b c _ _ _ hab hbc =>
    let ⟨ hPab, hRab ⟩ := (XBOOLE_0.def4 P R (TARSKI.pair a b)).mp hab
    let ⟨ hPbc, hRbc ⟩ := (XBOOLE_0.def4 P R (TARSKI.pair b c)).mp hbc
    let ⟨ haP, hbP ⟩ := field_mem_of_pair hPab
    let hcP := (field_mem_of_pair hPbc).2
    let ⟨ haR, hbR ⟩ := field_mem_of_pair hRab
    let hcR := (field_mem_of_pair hRbc).2
    (XBOOLE_0.def4 P R (TARSKI.pair a c)).mpr
      ⟨ hP a b c haP hbP hcP hPab hPbc, hR a b c haR hbR hcR hRab hRbc ⟩

/-- `RELAT_2:27` -/
theorem th27 {R : TarskiSet.{u}} (_hR : RELAT_1.isRelation R) :
    isTransitive R ↔ RELAT_1.comp R R ⊆ R := by
  constructor
  · intro htr
    exact RELAT_1.rel_subset (RELAT_1.comp_isRelation R R) fun a b hp =>
      let ⟨ c, hac, hcb ⟩ := (RELAT_1.def8 R R a b).mp hp
      let ⟨ ha, hc ⟩ := field_mem_of_pair hac
      let hb := (field_mem_of_pair hcb).2
      htr a c b ha hc hb hac hcb
  · intro hsub a b c _ _ _ hab hbc
    exact hsub _ ((RELAT_1.def8 R R a c).mpr ⟨ b, hab, hbc ⟩)

/-- `RELAT_2:28` -/
theorem th28 {R : TarskiSet.{u}} :
    isConnected R ↔
      ZFMISC_1.product (RELAT_1.field R) (RELAT_1.field R) \
        RELAT_1.id (RELAT_1.field R) ⊆ R ∪ RELAT_1.converse R := by
  constructor
  · intro hcon p hp
    have ⟨ hpP, hnid ⟩ :=
      (XBOOLE_0.def5 (ZFMISC_1.product (RELAT_1.field R) (RELAT_1.field R))
        (RELAT_1.id (RELAT_1.field R)) p).mp hp
    have ⟨ y, z, hy, hz, heq ⟩ :=
      (ZFMISC_1.def2 (RELAT_1.field R) (RELAT_1.field R) p).mp hpP
    have hne : y ≠ z := fun heqyz =>
      hnid (heq ▸ (RELAT_1.def10 (RELAT_1.field R) y z).mpr ⟨ hy, heqyz ⟩)
    exact heq ▸
      Or.elim (hcon y z hy hz hne)
        (fun hRyz => (XBOOLE_0.def3 R (RELAT_1.converse R) (TARSKI.pair y z)).mpr
          (Or.inl hRyz))
        (fun hRzy => (XBOOLE_0.def3 R (RELAT_1.converse R) (TARSKI.pair y z)).mpr
          (Or.inr ((RELAT_1.def7 R y z).mpr hRzy)))
  · intro hsub a b ha hb hne
    have hprod : TARSKI.pair a b ∈
        ZFMISC_1.product (RELAT_1.field R) (RELAT_1.field R) :=
      (ZFMISC_1.th87 (x := a) (y := b) (X := RELAT_1.field R)
        (Y := RELAT_1.field R)).mpr ⟨ ha, hb ⟩
    have hnid : TARSKI.pair a b ∉ RELAT_1.id (RELAT_1.field R) := fun hid =>
      hne ((RELAT_1.def10 (RELAT_1.field R) a b).mp hid).2
    have hp := hsub (TARSKI.pair a b)
      ((XBOOLE_0.def5 (ZFMISC_1.product (RELAT_1.field R) (RELAT_1.field R))
        (RELAT_1.id (RELAT_1.field R)) (TARSKI.pair a b)).mpr ⟨ hprod, hnid ⟩)
    exact Or.elim ((XBOOLE_0.def3 R (RELAT_1.converse R) (TARSKI.pair a b)).mp hp)
      Or.inl fun hc => Or.inr ((RELAT_1.def7 R a b).mp hc)

theorem strongly_connected_isConnected {R : TarskiSet.{u}}
    (h : isStronglyConnected R) : isConnected R :=
  fun x y hx hy _ => h x y hx hy

theorem strongly_connected_isReflexive {R : TarskiSet.{u}}
    (h : isStronglyConnected R) : isReflexive R :=
  fun x hx => (h x x hx hx).elim (fun hp => hp) (fun hp => hp)

/-- `RELAT_2:30` -/
theorem th30 {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R) :
    isStronglyConnected R ↔
      ZFMISC_1.product (RELAT_1.field R) (RELAT_1.field R) =
        R ∪ RELAT_1.converse R := by
  constructor
  · intro hsc
    apply TARSKI.extensionality
    intro p
    constructor
    · intro hp
      have ⟨ y, z, hy, hz, heq ⟩ :=
        (ZFMISC_1.def2 (RELAT_1.field R) (RELAT_1.field R) p).mp hp
      exact heq ▸
        Or.elim (hsc y z hy hz)
          (fun hRyz => (XBOOLE_0.def3 R (RELAT_1.converse R)
            (TARSKI.pair y z)).mpr (Or.inl hRyz))
          (fun hRzy => (XBOOLE_0.def3 R (RELAT_1.converse R)
            (TARSKI.pair y z)).mpr (Or.inr ((RELAT_1.def7 R y z).mpr hRzy)))
    · intro hp
      exact Or.elim ((XBOOLE_0.def3 R (RELAT_1.converse R) p).mp hp)
        (fun hRp =>
          let ⟨y, z, heq⟩ := hR p hRp
          Eq.subst
            (motive := fun q =>
              q ∈ ZFMISC_1.product (RELAT_1.field R) (RELAT_1.field R))
            heq.symm
            ((ZFMISC_1.th87 (x := y) (y := z) (X := RELAT_1.field R)
              (Y := RELAT_1.field R)).mpr
              (field_mem_of_pair (Eq.subst
                (motive := fun q => q ∈ R) heq hRp))))
        (fun hCp =>
          let ⟨y, z, heq⟩ := RELAT_1.converse_isRelation R p hCp
          let hzy := (RELAT_1.def7 R y z).mp
            (Eq.subst (motive := fun q => q ∈ RELAT_1.converse R) heq hCp)
          let ⟨hz, hy⟩ := field_mem_of_pair hzy
          Eq.subst
            (motive := fun q =>
              q ∈ ZFMISC_1.product (RELAT_1.field R) (RELAT_1.field R))
            heq.symm
            ((ZFMISC_1.th87 (x := y) (y := z) (X := RELAT_1.field R)
              (Y := RELAT_1.field R)).mpr ⟨hy, hz⟩))
  · intro heq a b ha hb
    have hp : TARSKI.pair a b ∈ R ∪ RELAT_1.converse R :=
      heq.symm ▸
        (ZFMISC_1.th87 (x := a) (y := b) (X := RELAT_1.field R)
          (Y := RELAT_1.field R)).mpr ⟨ ha, hb ⟩
    exact Or.elim ((XBOOLE_0.def3 R (RELAT_1.converse R) (TARSKI.pair a b)).mp hp)
      Or.inl fun hc => Or.inr ((RELAT_1.def7 R a b).mp hc)

/-- `RELAT_2:31` -/
theorem th31 {R : TarskiSet.{u}} :
    isTransitive R ↔
      ∀ x y z, TARSKI.pair x y ∈ R → TARSKI.pair y z ∈ R →
        TARSKI.pair x z ∈ R := by
  constructor
  · intro htr x y z hxy hyz
    let ⟨ hx, hy ⟩ := field_mem_of_pair hxy
    let hz := (field_mem_of_pair hyz).2
    exact htr x y z hx hy hz hxy hyz
  · intro h x y z _ _ _ hxy hyz
    exact h x y z hxy hyz

end RELAT_2
