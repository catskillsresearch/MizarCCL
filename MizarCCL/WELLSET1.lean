import MizarCCL.WELLORD1
import MizarCCL.WELLORD2

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/wellset1.miz`.
Authors: Bogdan Nowak, Sławomir Białecki (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Zermelo's Theorem

1–1 Lean rendering of Mizar article `WELLSET1`
(`vendor/mml/wellset1.miz`). Import is `WELLORD1` and `WELLORD2`
(the latter only for the Zermelo theorem proof variation).
-/

universe u

open TarskiSet TARSKI

namespace WELLSET1

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  TARSKI.extensionality h

private theorem exists_mem_of_ne {A : TarskiSet.{u}}
    (h : A ≠ (∅ : TarskiSet.{u})) : ∃ x, x ∈ A :=
  Classical.byContradiction fun hne =>
    h (XBOOLE_0.empty_eq (fun hex => hne hex))

/-- `WELLSET1:1` (`Th1`) -/
theorem th1 (R x : TarskiSet.{u}) :
    x ∈ RELAT_1.field R ↔
      ∃ y, TARSKI.pair x y ∈ R ∨ TARSKI.pair y x ∈ R := by
  constructor
  · intro hx
    have h := (XBOOLE_0.def3 (RELAT_1.dom R) (RELAT_1.rng R) x).mp hx
    exact Or.elim h
      (fun hd =>
        let ⟨y, hp⟩ := (RELAT_1.dom_iff R x).mp hd
        ⟨y, Or.inl hp⟩)
      (fun hr =>
        let ⟨y, hp⟩ := (RELAT_1.rng_iff R x).mp hr
        ⟨y, Or.inr hp⟩)
  · intro ⟨y, h⟩
    exact Or.elim h
      (fun hp => (RELAT_1.th15 hp).1)
      (fun hp => (RELAT_1.th15 hp).2)

/-- `WELLSET1:2` (`Th2`) -/
theorem th2 {X Y W : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hW : W = ZFMISC_1.product X Y) :
    RELAT_1.field W = X ∪ Y := by
  obtain ⟨a, ha⟩ := exists_mem_of_ne hX
  obtain ⟨b, hb⟩ := exists_mem_of_ne hY
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    obtain ⟨y, hor⟩ := (th1 W x).mp hx
    exact Or.elim hor
      (fun hp =>
        have hxX : x ∈ X :=
          ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp
            (hW ▸ hp)).1
        (XBOOLE_0.def3 X Y x).mpr (Or.inl hxX))
      (fun hp =>
        have hxY : x ∈ Y :=
          ((ZFMISC_1.th87 (x := y) (y := x) (X := X) (Y := Y)).mp
            (hW ▸ hp)).2
        (XBOOLE_0.def3 X Y x).mpr (Or.inr hxY))
  · intro hx
    exact Or.elim ((XBOOLE_0.def3 X Y x).mp hx)
      (fun hxX =>
        (th1 W x).mpr ⟨b,
          Or.inl (hW ▸ (ZFMISC_1.th87 (x := x) (y := b) (X := X) (Y := Y)).mpr
            ⟨hxX, hb⟩)⟩)
      (fun hxY =>
        (th1 W x).mpr ⟨a,
          Or.inr (hW ▸ (ZFMISC_1.th87 (x := a) (y := x) (X := X) (Y := Y)).mpr
            ⟨ha, hxY⟩)⟩)

/-- `WELLSET1:sch RSeparation` -/
theorem sch_RSeparation (A : TarskiSet.{u})
    (P : TarskiSet.{u} → Prop) :
    ∃ B : TarskiSet.{u},
      ∀ R : TarskiSet.{u}, R ∈ B ↔ R ∈ A ∧ P R := by
  obtain ⟨B, hB⟩ :=
    TARSKI.sch1 A (fun y t => y = t ∧ ∃ S : TarskiSet.{u}, S = t ∧ P S)
      (fun y t v ⟨ht, _⟩ ⟨hv, _⟩ => ht.symm.trans hv)
  refine ⟨B, fun R => ?_⟩
  constructor
  · intro hR
    have ⟨y, hyA, hyeq, ⟨S, hS, hP⟩⟩ := (hB R).mp hR
    exact ⟨Eq.subst (motive := fun s => s ∈ A) hyeq hyA,
      Eq.subst (motive := P) hS hP⟩
  · intro ⟨hRA, hP⟩
    exact (hB R).mpr ⟨R, hRA, rfl, ⟨R, rfl, hP⟩⟩

/-- `WELLSET1:3` (`Th3`) -/
theorem th3 {x y W : TarskiSet.{u}}
    (hx : x ∈ RELAT_1.field W) (hy : y ∈ RELAT_1.field W)
    (hW : WELLORD1.isWellOrdering W) (hnseg : x ∉ WELLORD1.seg W y) :
    TARSKI.pair y x ∈ W := by
  have hconnF := (RELAT_2.def14 W).mp hW.2.2.2.1
  have hrefIn :=
    (RELAT_2.def1 W (RELAT_1.field W)).mp ((RELAT_2.def9 W).mp hW.1)
  apply Classical.byContradiction
  intro hnyx
  have hne : x ≠ y := fun heq =>
    hnyx (Eq.subst (motive := fun s => TARSKI.pair y s ∈ W) heq.symm
      (hrefIn y hy))
  have hxyW : TARSKI.pair x y ∈ W :=
    Or.elim ((RELAT_2.def6 W (RELAT_1.field W)).mp hconnF x y hx hy hne)
      id fun hyx => (hnyx hyx).elim
  exact hnseg ((WELLORD1.th1 W y x).mpr ⟨hne, hxyW⟩)

/-- `WELLSET1:4` (`Th4`) -/
theorem th4 {x y W : TarskiSet.{u}}
    (hx : x ∈ RELAT_1.field W) (hy : y ∈ RELAT_1.field W)
    (hW : WELLORD1.isWellOrdering W) (hseg : x ∈ WELLORD1.seg W y) :
    TARSKI.pair y x ∉ W := by
  have hantiF := (RELAT_2.def12 W).mp hW.2.2.1
  have ⟨hne, hxy⟩ := (WELLORD1.th1 W y x).mp hseg
  intro hyx
  exact hne ((RELAT_2.def4 W (RELAT_1.field W)).mp hantiF x y hx hy hxy hyx)

/-- Approximation predicate used by `Th5`. -/
private def isApprox (F D W : TarskiSet.{u}) : Prop :=
  WELLORD1.isWellOrdering W ∧
    ∀ y, y ∈ RELAT_1.field W →
      WELLORD1.seg W y ∈ D ∧ FUNCT_1.apply F (WELLORD1.seg W y) = y

private theorem field_empty :
    RELAT_1.field (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) := by
  apply eq_of_mem
  intro z
  constructor
  · intro hz
    obtain ⟨y, hor⟩ := (th1 (∅ : TarskiSet.{u}) z).mp hz
    exact Or.elim hor
      (fun hp => ((XBOOLE_0.empty_iff _).mp hp).elim)
      (fun hp => ((XBOOLE_0.empty_iff _).mp hp).elim)
  · intro hz
    exact ((XBOOLE_0.empty_iff z).mp hz).elim

private theorem empty_well_ordering :
    WELLORD1.isWellOrdering (∅ : TarskiSet.{u}) := by
  have hf := field_empty
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (RELAT_2.def9 (∅ : TarskiSet.{u})).mpr fun a ha =>
      ((XBOOLE_0.empty_iff a).mp
        (Eq.subst (motive := fun s => a ∈ s) hf ha)).elim
  · exact (RELAT_2.def16 (∅ : TarskiSet.{u})).mpr
      ((RELAT_2.def8 (∅ : TarskiSet.{u})
          (RELAT_1.field (∅ : TarskiSet.{u}))).mpr
        fun _ _ _ ha =>
          ((XBOOLE_0.empty_iff _).mp
            (Eq.subst (motive := fun s => _ ∈ s) hf ha)).elim)
  · exact (RELAT_2.def12 (∅ : TarskiSet.{u})).mpr
      ((RELAT_2.def4 (∅ : TarskiSet.{u})
          (RELAT_1.field (∅ : TarskiSet.{u}))).mpr
        fun _ _ ha =>
          ((XBOOLE_0.empty_iff _).mp
            (Eq.subst (motive := fun s => _ ∈ s) hf ha)).elim)
  · exact (RELAT_2.def14 (∅ : TarskiSet.{u})).mpr
      ((RELAT_2.def6 (∅ : TarskiSet.{u})
          (RELAT_1.field (∅ : TarskiSet.{u}))).mpr
        fun _ _ ha =>
          ((XBOOLE_0.empty_iff _).mp
            (Eq.subst (motive := fun s => _ ∈ s) hf ha)).elim)
  · intro Y hY hne
    exact False.elim (hne (XBOOLE_1.th3 fun y hy =>
      ((XBOOLE_0.empty_iff y).mp
        (Eq.subst (motive := fun s => y ∈ s) hf (hY y hy))).elim))

private theorem empty_isApprox (F D : TarskiSet.{u}) :
    isApprox F D (∅ : TarskiSet.{u}) :=
  ⟨empty_well_ordering, fun y hy =>
    ((XBOOLE_0.empty_iff y).mp
      (Eq.subst (motive := fun s => y ∈ s) field_empty hy)).elim⟩

private theorem restrict2_isRelation (R Y : TarskiSet.{u}) :
    RELAT_1.isRelation (WELLORD1.restrict2 R Y) :=
  RELAT_1.subset_isRelation (RELAT_1.product_isRelation Y Y)
    (fun z hz => ((XBOOLE_0.def4 R (ZFMISC_1.product Y Y) z).mp hz).2)

private theorem wellOrders_restrict2 {R X : TarskiSet.{u}}
    (h : WELLORD1.wellOrders R X) :
    WELLORD1.wellOrders (WELLORD1.restrict2 R X) X ∧
      RELAT_1.field (WELLORD1.restrict2 R X) = X := by
  have hrefl : RELAT_2.isReflexiveIn (WELLORD1.restrict2 R X) X :=
    (RELAT_2.def1 (WELLORD1.restrict2 R X) X).mpr fun x hx =>
      (WELLORD1.restrict2_iff R X x x).mpr ⟨h.1 x hx, hx, hx⟩
  have hNfield : X ⊆ RELAT_1.field (WELLORD1.restrict2 R X) :=
    fun x hx =>
      (RELAT_1.th15
        ((RELAT_2.def1 (WELLORD1.restrict2 R X) X).mp hrefl x hx)).1
  have hfieldN : RELAT_1.field (WELLORD1.restrict2 R X) ⊆ X :=
    (WELLORD1.th13 R X).2
  have hfield : RELAT_1.field (WELLORD1.restrict2 R X) = X :=
    (XBOOLE_0.def10
      (X := RELAT_1.field (WELLORD1.restrict2 R X)) (Y := X)).mpr
      ⟨hfieldN, hNfield⟩
  have htr : RELAT_2.isTransitiveIn (WELLORD1.restrict2 R X) X :=
    (RELAT_2.def8 (WELLORD1.restrict2 R X) X).mpr
      fun a b c ha hb hc hab hbc =>
        let ⟨hpab, _, _⟩ := (WELLORD1.restrict2_iff R X a b).mp hab
        let ⟨hpbc, _, _⟩ := (WELLORD1.restrict2_iff R X b c).mp hbc
        (WELLORD1.restrict2_iff R X a c).mpr
          ⟨(RELAT_2.def8 R X).mp h.2.1 a b c ha hb hc hpab hpbc, ha, hc⟩
  have hanti : RELAT_2.isAntisymmetricIn (WELLORD1.restrict2 R X) X :=
    (RELAT_2.def4 (WELLORD1.restrict2 R X) X).mpr fun a b ha hb hab hba =>
      let ⟨hpab, _, _⟩ := (WELLORD1.restrict2_iff R X a b).mp hab
      let ⟨hpba, _, _⟩ := (WELLORD1.restrict2_iff R X b a).mp hba
      (RELAT_2.def4 R X).mp h.2.2.1 a b ha hb hpab hpba
  have hconn : RELAT_2.isConnectedIn (WELLORD1.restrict2 R X) X :=
    (RELAT_2.def6 (WELLORD1.restrict2 R X) X).mpr fun a b ha hb hne =>
      Or.elim ((RELAT_2.def6 R X).mp h.2.2.2.1 a b ha hb hne)
        (fun hab => Or.inl ((WELLORD1.restrict2_iff R X a b).mpr
          ⟨hab, ha, hb⟩))
        (fun hba => Or.inr ((WELLORD1.restrict2_iff R X b a).mpr
          ⟨hba, hb, ha⟩))
  have hwf : WELLORD1.isWellFoundedIn (WELLORD1.restrict2 R X) X := by
    intro Y hY hne
    obtain ⟨a, ha, hmiss⟩ := h.2.2.2.2 Y hY hne
    refine ⟨a, ha, ?_⟩
    apply (XBOOLE_0.def7
      (WELLORD1.seg (WELLORD1.restrict2 R X) a) Y).mpr
    apply eq_of_mem
    intro x
    constructor
    · intro hx
      have ⟨hxS, hxY⟩ :=
        (XBOOLE_0.def4
          (WELLORD1.seg (WELLORD1.restrict2 R X) a) Y x).mp hx
      have ⟨hne', hp⟩ :=
        (WELLORD1.th1 (WELLORD1.restrict2 R X) a x).mp hxS
      have hpR := ((WELLORD1.restrict2_iff R X x a).mp hp).1
      have hxSeg : x ∈ WELLORD1.seg R a :=
        (WELLORD1.th1 R a x).mpr ⟨hne', hpR⟩
      exact ((XBOOLE_0.empty_iff x).mp
        (Eq.subst (motive := fun s => x ∈ s)
          ((XBOOLE_0.def7 (WELLORD1.seg R a) Y).mp hmiss)
          ((XBOOLE_0.def4 (WELLORD1.seg R a) Y x).mpr ⟨hxSeg, hxY⟩))).elim
    · intro hx
      exact ((XBOOLE_0.empty_iff x).mp hx).elim
  exact ⟨⟨hrefl, htr, hanti, hconn, hwf⟩, hfield⟩

private theorem pair_of_seg_or_eq {W z1 z2 : TarskiSet.{u}}
    (hwo : WELLORD1.isWellOrdering W)
    (_hz1F : z1 ∈ RELAT_1.field W) (hz2F : z2 ∈ RELAT_1.field W)
    (hcases : z1 ∈ WELLORD1.seg W z2 ∨ z1 = z2) :
    TARSKI.pair z1 z2 ∈ W :=
  Or.elim hcases
    (fun hs => ((WELLORD1.th1 W z2 z1).mp hs).2)
    (fun heq =>
      Eq.subst (motive := fun s => TARSKI.pair s z2 ∈ W) heq.symm
        ((WELLORD1.lm1 W).mp hwo.1 z2 hz2F))

private theorem seg_or_eq_of_pair {W z1 z2 : TarskiSet.{u}}
    (hp : TARSKI.pair z1 z2 ∈ W) :
    z1 ∈ WELLORD1.seg W z2 ∨ z1 = z2 :=
  Or.elim (Classical.em (z1 = z2)) Or.inr
    (fun hne => Or.inl ((WELLORD1.th1 W z2 z1).mpr ⟨hne, hp⟩))
/-- Comparability of approximations (`Th5`/`A7`). -/
private theorem approx_comparable {F D W1 W2 : TarskiSet.{u}}
    (hRel1 : RELAT_1.isRelation W1) (hRel2 : RELAT_1.isRelation W2)
    (hW1 : isApprox F D W1) (hW2 : isApprox F D W2) :
    (W1 ⊆ W2 ∧ ∀ x, x ∈ RELAT_1.field W1 →
        WELLORD1.seg W1 x = WELLORD1.seg W2 x) ∨
      (W2 ⊆ W1 ∧ ∀ x, x ∈ RELAT_1.field W2 →
        WELLORD1.seg W2 x = WELLORD1.seg W1 x) := by
  obtain ⟨hwo1, happ1⟩ := hW1
  obtain ⟨hwo2, happ2⟩ := hW2
  obtain ⟨C, hC⟩ :=
    XBOOLE_0.sch_separation (RELAT_1.field W1)
      (fun x => x ∈ RELAT_1.field W2 ∧
        WELLORD1.restrict2 W1 (WELLORD1.seg W1 x) =
          WELLORD1.restrict2 W2 (WELLORD1.seg W2 x))
  have hC' (x : TarskiSet.{u}) : x ∈ C ↔
      x ∈ RELAT_1.field W1 ∧ x ∈ RELAT_1.field W2 ∧
        WELLORD1.restrict2 W1 (WELLORD1.seg W1 x) =
          WELLORD1.restrict2 W2 (WELLORD1.seg W2 x) := by
    constructor
    · intro hx
      obtain ⟨hx1, hx2, heq⟩ := (hC x).mp hx
      exact ⟨hx1, hx2, heq⟩
    · intro ⟨hx1, hx2, heq⟩
      exact (hC x).mpr ⟨hx1, hx2, heq⟩
  have A13 (x : TarskiSet.{u}) (hxC : x ∈ C) :
      WELLORD1.seg W1 x = WELLORD1.seg W2 x := by
    obtain ⟨_, _, heqR⟩ := (hC' x).mp hxC
    apply eq_of_mem
    intro y
    have hf1 := WELLORD1.th32 hwo1 x
    have hf2 := WELLORD1.th32 hwo2 x
    constructor
    · intro hy
      have hyF :
          y ∈ RELAT_1.field (WELLORD1.restrict2 W1 (WELLORD1.seg W1 x)) :=
        Eq.subst (motive := fun s => y ∈ s) hf1.symm hy
      exact Eq.subst (motive := fun s => y ∈ s) hf2
        (Eq.subst (motive := fun s => y ∈ RELAT_1.field s) heqR hyF)
    · intro hy
      have hyF :
          y ∈ RELAT_1.field (WELLORD1.restrict2 W2 (WELLORD1.seg W2 x)) :=
        Eq.subst (motive := fun s => y ∈ s) hf2.symm hy
      exact Eq.subst (motive := fun s => y ∈ s) hf1
        (Eq.subst (motive := fun s => y ∈ RELAT_1.field s) heqR.symm hyF)
  have restrict_agree_of_seg_sub {W X Y : TarskiSet.{u}}
      (hsub : Y ⊆ X) :
      WELLORD1.restrict2 W Y =
        WELLORD1.restrict2 (WELLORD1.restrict2 W X) Y :=
    (WELLORD1.th22 hsub W).symm
  have A15 (x : TarskiSet.{u}) (hxC : x ∈ C) :
      WELLORD1.seg W1 x ⊆ C := by
    intro y hy
    obtain ⟨hxF1, hxF2, heqR⟩ := (hC' x).mp hxC
    have hy2 : y ∈ WELLORD1.seg W2 x :=
      Eq.subst (motive := fun s => y ∈ s) (A13 x hxC) hy
    have hyF2 : y ∈ RELAT_1.field W2 :=
      (RELAT_1.th15 ((WELLORD1.th1 W2 x y).mp hy2).2).1
    have hpyx1 : TARSKI.pair y x ∈ W1 := ((WELLORD1.th1 W1 x y).mp hy).2
    have hyF1 : y ∈ RELAT_1.field W1 := (RELAT_1.th15 hpyx1).1
    have hsegEq : WELLORD1.seg W1 y = WELLORD1.seg W2 y := by
      have h1 := WELLORD1.th27 hwo1 hy
      have h2 :
          WELLORD1.seg (WELLORD1.restrict2 W2 (WELLORD1.seg W2 x)) y =
            WELLORD1.seg W1 y :=
        Eq.subst (motive := fun s =>
            WELLORD1.seg s y = WELLORD1.seg W1 y) heqR h1
      exact h2.symm.trans (WELLORD1.th27 hwo2 hy2)
    have hsub1 : WELLORD1.seg W1 y ⊆ WELLORD1.seg W1 x :=
      (WELLORD1.th30 hwo1 hyF1 hxF1).mpr (Or.inr hy)
    have hsub2 : WELLORD1.seg W2 y ⊆ WELLORD1.seg W2 x :=
      (WELLORD1.th30 hwo2 hyF2 hxF2).mpr (Or.inr hy2)
    have heqR' :
        WELLORD1.restrict2 W1 (WELLORD1.seg W1 y) =
          WELLORD1.restrict2 W2 (WELLORD1.seg W2 y) := by
      have e1 := restrict_agree_of_seg_sub (W := W1) hsub1
      have e2 :
          WELLORD1.restrict2
              (WELLORD1.restrict2 W1 (WELLORD1.seg W1 x))
              (WELLORD1.seg W1 y) =
            WELLORD1.restrict2
              (WELLORD1.restrict2 W2 (WELLORD1.seg W2 x))
              (WELLORD1.seg W1 y) :=
        Eq.subst (motive := fun s =>
            WELLORD1.restrict2
                (WELLORD1.restrict2 W1 (WELLORD1.seg W1 x))
                (WELLORD1.seg W1 y) =
              WELLORD1.restrict2 s (WELLORD1.seg W1 y)) heqR rfl
      have e3 :
          WELLORD1.restrict2
              (WELLORD1.restrict2 W2 (WELLORD1.seg W2 x))
              (WELLORD1.seg W1 y) =
            WELLORD1.restrict2
              (WELLORD1.restrict2 W2 (WELLORD1.seg W2 x))
              (WELLORD1.seg W2 y) :=
        Eq.subst (motive := fun s =>
            WELLORD1.restrict2
                (WELLORD1.restrict2 W2 (WELLORD1.seg W2 x)) s =
              WELLORD1.restrict2
                (WELLORD1.restrict2 W2 (WELLORD1.seg W2 x))
                (WELLORD1.seg W2 y)) hsegEq.symm rfl
      exact ((e1.trans e2).trans e3).trans (WELLORD1.th22 hsub2 W2)
    exact (hC' y).mpr ⟨hyF1, hyF2, heqR'⟩
  have least_missing_W1 (y1 : TarskiSet.{u})
      (hy1F : y1 ∈ RELAT_1.field W1) (hnC : y1 ∉ C) :
      ∃ y3, y3 ∈ RELAT_1.field W1 ∧ C = WELLORD1.seg W1 y3 ∧ y3 ∉ C := by
    let Y := RELAT_1.field W1 \ C
    have hy1Y : y1 ∈ Y :=
      (XBOOLE_0.def5 (RELAT_1.field W1) C y1).mpr ⟨hy1F, hnC⟩
    have hYne : Y ≠ (∅ : TarskiSet.{u}) := fun hempty =>
      ((XBOOLE_0.empty_iff y1).mp
        (Eq.subst (motive := fun s => y1 ∈ s) hempty hy1Y)).elim
    have hYsub : Y ⊆ RELAT_1.field W1 := fun b hb =>
      ((XBOOLE_0.def5 (RELAT_1.field W1) C b).mp hb).1
    obtain ⟨a, haY, hleast⟩ := WELLORD1.th6 hwo1 hYsub hYne
    have haF := ((XBOOLE_0.def5 (RELAT_1.field W1) C a).mp haY).1
    have hanC := ((XBOOLE_0.def5 (RELAT_1.field W1) C a).mp haY).2
    refine ⟨a, haF, ?_, hanC⟩
    apply eq_of_mem
    intro x
    constructor
    · intro hxC
      apply Classical.byContradiction
      intro hnseg
      have hxF1 : x ∈ RELAT_1.field W1 := ((hC' x).mp hxC).1
      have hax : TARSKI.pair a x ∈ W1 := th3 hxF1 haF hwo1 hnseg
      have hne : a ≠ x := fun heq =>
        hanC (Eq.subst (motive := fun s => s ∈ C) heq.symm hxC)
      exact hanC (A15 x hxC a ((WELLORD1.th1 W1 x a).mpr ⟨hne, hax⟩))
    · intro hxseg
      apply Classical.byContradiction
      intro hnC'
      have hxy : TARSKI.pair x a ∈ W1 := ((WELLORD1.th1 W1 a x).mp hxseg).2
      have hxF1 : x ∈ RELAT_1.field W1 := (RELAT_1.th15 hxy).1
      exact th4 hxF1 haF hwo1 hxseg
        (hleast x ((XBOOLE_0.def5 (RELAT_1.field W1) C x).mpr
          ⟨hxF1, hnC'⟩))
  have A35 (x : TarskiSet.{u}) (hxC : x ∈ C) :
      WELLORD1.seg W2 x ⊆ C := by
    intro y hy
    obtain ⟨hxF1, hxF2, heqR⟩ := (hC' x).mp hxC
    have hy1 : y ∈ WELLORD1.seg W1 x :=
      Eq.subst (motive := fun s => y ∈ s) (A13 x hxC).symm hy
    have hyF1 : y ∈ RELAT_1.field W1 :=
      (RELAT_1.th15 ((WELLORD1.th1 W1 x y).mp hy1).2).1
    have hyF2 : y ∈ RELAT_1.field W2 :=
      (RELAT_1.th15 ((WELLORD1.th1 W2 x y).mp hy).2).1
    have hsegEq : WELLORD1.seg W2 y = WELLORD1.seg W1 y := by
      have h1 := WELLORD1.th27 hwo2 hy
      have h2 :
          WELLORD1.seg (WELLORD1.restrict2 W1 (WELLORD1.seg W1 x)) y =
            WELLORD1.seg W2 y :=
        Eq.subst (motive := fun s =>
            WELLORD1.seg s y = WELLORD1.seg W2 y) heqR.symm h1
      exact h2.symm.trans (WELLORD1.th27 hwo1 hy1)
    have hsub1 : WELLORD1.seg W1 y ⊆ WELLORD1.seg W1 x :=
      (WELLORD1.th30 hwo1 hyF1 hxF1).mpr (Or.inr hy1)
    have hsub2 : WELLORD1.seg W2 y ⊆ WELLORD1.seg W2 x :=
      (WELLORD1.th30 hwo2 hyF2 hxF2).mpr (Or.inr hy)
    have heqR' :
        WELLORD1.restrict2 W1 (WELLORD1.seg W1 y) =
          WELLORD1.restrict2 W2 (WELLORD1.seg W2 y) := by
      have e1 := restrict_agree_of_seg_sub (W := W2) hsub2
      have e2 :
          WELLORD1.restrict2
              (WELLORD1.restrict2 W2 (WELLORD1.seg W2 x))
              (WELLORD1.seg W2 y) =
            WELLORD1.restrict2
              (WELLORD1.restrict2 W1 (WELLORD1.seg W1 x))
              (WELLORD1.seg W2 y) :=
        Eq.subst (motive := fun s =>
            WELLORD1.restrict2
                (WELLORD1.restrict2 W2 (WELLORD1.seg W2 x))
                (WELLORD1.seg W2 y) =
              WELLORD1.restrict2 s (WELLORD1.seg W2 y)) heqR.symm rfl
      have e3 :
          WELLORD1.restrict2
              (WELLORD1.restrict2 W1 (WELLORD1.seg W1 x))
              (WELLORD1.seg W2 y) =
            WELLORD1.restrict2
              (WELLORD1.restrict2 W1 (WELLORD1.seg W1 x))
              (WELLORD1.seg W1 y) :=
        Eq.subst (motive := fun s =>
            WELLORD1.restrict2
                (WELLORD1.restrict2 W1 (WELLORD1.seg W1 x)) s =
              WELLORD1.restrict2
                (WELLORD1.restrict2 W1 (WELLORD1.seg W1 x))
                (WELLORD1.seg W1 y)) hsegEq.symm rfl
      have e4 := WELLORD1.th22 hsub1 W1
      exact (((e4.symm.trans e3.symm).trans e2.symm).trans e1.symm)
    exact (hC' y).mpr ⟨hyF1, hyF2, heqR'⟩
  have least_missing_W2 (y1 : TarskiSet.{u})
      (hy1F : y1 ∈ RELAT_1.field W2) (hnC : y1 ∉ C) :
      ∃ y3, y3 ∈ RELAT_1.field W2 ∧ C = WELLORD1.seg W2 y3 ∧ y3 ∉ C := by
    let Y := RELAT_1.field W2 \ C
    have hy1Y : y1 ∈ Y :=
      (XBOOLE_0.def5 (RELAT_1.field W2) C y1).mpr ⟨hy1F, hnC⟩
    have hYne : Y ≠ (∅ : TarskiSet.{u}) := fun hempty =>
      ((XBOOLE_0.empty_iff y1).mp
        (Eq.subst (motive := fun s => y1 ∈ s) hempty hy1Y)).elim
    have hYsub : Y ⊆ RELAT_1.field W2 := fun b hb =>
      ((XBOOLE_0.def5 (RELAT_1.field W2) C b).mp hb).1
    obtain ⟨a, haY, hleast⟩ := WELLORD1.th6 hwo2 hYsub hYne
    have haF := ((XBOOLE_0.def5 (RELAT_1.field W2) C a).mp haY).1
    have hanC := ((XBOOLE_0.def5 (RELAT_1.field W2) C a).mp haY).2
    refine ⟨a, haF, ?_, hanC⟩
    apply eq_of_mem
    intro x
    constructor
    · intro hxC
      apply Classical.byContradiction
      intro hnseg
      have hxF2 : x ∈ RELAT_1.field W2 := ((hC' x).mp hxC).2.1
      have hax : TARSKI.pair a x ∈ W2 := th3 hxF2 haF hwo2 hnseg
      have hne : a ≠ x := fun heq =>
        hanC (Eq.subst (motive := fun s => s ∈ C) heq.symm hxC)
      exact hanC (A35 x hxC a ((WELLORD1.th1 W2 x a).mpr ⟨hne, hax⟩))
    · intro hxseg
      apply Classical.byContradiction
      intro hnC'
      have hxy : TARSKI.pair x a ∈ W2 := ((WELLORD1.th1 W2 a x).mp hxseg).2
      have hxF2 : x ∈ RELAT_1.field W2 := (RELAT_1.th15 hxy).1
      exact th4 hxF2 haF hwo2 hxseg
        (hleast x ((XBOOLE_0.def5 (RELAT_1.field W2) C x).mpr
          ⟨hxF2, hnC'⟩))
  have mem_restrict2_iff (W Y z : TarskiSet.{u}) :
      z ∈ WELLORD1.restrict2 W Y ↔
        z ∈ W ∧ z ∈ ZFMISC_1.product Y Y :=
    XBOOLE_0.def4 W (ZFMISC_1.product Y Y) z
  have A55 : C = RELAT_1.field W1 ∨ C = RELAT_1.field W2 := by
    apply Classical.or_iff_not_imp_left.mpr
    intro hnEq1
    obtain ⟨y1, hy1iff⟩ : ∃ y1, ¬(y1 ∈ C ↔ y1 ∈ RELAT_1.field W1) :=
      Classical.byContradiction fun hall =>
        hnEq1 (eq_of_mem fun x =>
          Classical.not_not.mp fun hiff => hall ⟨x, hiff⟩)
    have hy1F : y1 ∈ RELAT_1.field W1 := Classical.byContradiction fun hnF =>
      have hnC : y1 ∉ C := fun hCx => hnF ((hC' y1).mp hCx).1
      hy1iff ⟨fun hCx => (hnC hCx).elim, fun hF => (hnF hF).elim⟩
    have hy1nC : y1 ∉ C := fun hCx =>
      hy1iff ⟨fun _ => hy1F, fun _ => hCx⟩
    obtain ⟨y3, hy3F, hCseg1, hy3nC⟩ := least_missing_W1 y1 hy1F hy1nC
    apply Classical.byContradiction
    intro hnEq2
    obtain ⟨y2, hy2iff⟩ : ∃ y2, ¬(y2 ∈ C ↔ y2 ∈ RELAT_1.field W2) :=
      Classical.byContradiction fun hall =>
        hnEq2 (eq_of_mem fun x =>
          Classical.not_not.mp fun hiff => hall ⟨x, hiff⟩)
    have hy2F : y2 ∈ RELAT_1.field W2 := Classical.byContradiction fun hnF =>
      have hnC : y2 ∉ C := fun hCx => hnF ((hC' y2).mp hCx).2.1
      hy2iff ⟨fun hCx => (hnC hCx).elim, fun hF => (hnF hF).elim⟩
    have hy2nC : y2 ∉ C := fun hCx =>
      hy2iff ⟨fun _ => hy2F, fun _ => hCx⟩
    obtain ⟨y4, hy4F, hCseg2, hy4nC⟩ := least_missing_W2 y2 hy2F hy2nC
    have hy3eq : y3 = y4 := by
      have hseg : WELLORD1.seg W1 y3 = WELLORD1.seg W2 y4 :=
        hCseg1.symm.trans hCseg2
      have hF :=
        Eq.subst (motive := fun s => FUNCT_1.apply F s = y3) hseg
          (happ1 y3 hy3F).2
      exact hF.symm.trans (happ2 y4 hy4F).2
    have hCseg2y3 : C = WELLORD1.seg W2 y3 :=
      Eq.subst (motive := fun s => C = WELLORD1.seg W2 s) hy3eq.symm hCseg2
    have heqR :
        WELLORD1.restrict2 W1 (WELLORD1.seg W1 y3) =
          WELLORD1.restrict2 W2 (WELLORD1.seg W2 y3) := by
      apply eq_of_mem
      intro z
      constructor
      · intro hz
        obtain ⟨hzW, hzP⟩ := (mem_restrict2_iff W1 (WELLORD1.seg W1 y3) z).mp hz
        obtain ⟨z1, z2, hz1, hz2, heqz⟩ :=
          (ZFMISC_1.def2 (WELLORD1.seg W1 y3) (WELLORD1.seg W1 y3) z).mp hzP
        have hz1C : z1 ∈ C :=
          Eq.subst (motive := fun s => z1 ∈ s) hCseg1.symm hz1
        have hz2C : z2 ∈ C :=
          Eq.subst (motive := fun s => z2 ∈ s) hCseg1.symm hz2
        have hz1F2 : z1 ∈ RELAT_1.field W2 := ((hC' z1).mp hz1C).2.1
        have hz2F2 : z2 ∈ RELAT_1.field W2 := ((hC' z2).mp hz2C).2.1
        have hpW1 : TARSKI.pair z1 z2 ∈ W1 :=
          Eq.subst (motive := fun s => s ∈ W1) heqz hzW
        have hcases2 : z1 ∈ WELLORD1.seg W2 z2 ∨ z1 = z2 :=
          Or.elim (seg_or_eq_of_pair hpW1)
            (fun hs => Or.inl (Eq.subst (motive := fun s => z1 ∈ s)
              (A13 z2 hz2C) hs))
            Or.inr
        have hpW2 := pair_of_seg_or_eq hwo2 hz1F2 hz2F2 hcases2
        have hz1s : z1 ∈ WELLORD1.seg W2 y3 :=
          Eq.subst (motive := fun s => z1 ∈ s) hCseg2y3 hz1C
        have hz2s : z2 ∈ WELLORD1.seg W2 y3 :=
          Eq.subst (motive := fun s => z2 ∈ s) hCseg2y3 hz2C
        exact (mem_restrict2_iff W2 (WELLORD1.seg W2 y3) z).mpr
          ⟨Eq.subst (motive := fun s => s ∈ W2) heqz.symm hpW2,
            Eq.subst (motive := fun s => s ∈
                ZFMISC_1.product (WELLORD1.seg W2 y3) (WELLORD1.seg W2 y3))
              heqz.symm ((ZFMISC_1.th87 (x := z1) (y := z2)
                (X := WELLORD1.seg W2 y3) (Y := WELLORD1.seg W2 y3)).mpr
                ⟨hz1s, hz2s⟩)⟩
      · intro hz
        obtain ⟨hzW, hzP⟩ := (mem_restrict2_iff W2 (WELLORD1.seg W2 y3) z).mp hz
        obtain ⟨z1, z2, hz1, hz2, heqz⟩ :=
          (ZFMISC_1.def2 (WELLORD1.seg W2 y3) (WELLORD1.seg W2 y3) z).mp hzP
        have hz1C : z1 ∈ C :=
          Eq.subst (motive := fun s => z1 ∈ s) hCseg2y3.symm hz1
        have hz2C : z2 ∈ C :=
          Eq.subst (motive := fun s => z2 ∈ s) hCseg2y3.symm hz2
        have hz1F1 : z1 ∈ RELAT_1.field W1 := ((hC' z1).mp hz1C).1
        have hz2F1 : z2 ∈ RELAT_1.field W1 := ((hC' z2).mp hz2C).1
        have hpW2 : TARSKI.pair z1 z2 ∈ W2 :=
          Eq.subst (motive := fun s => s ∈ W2) heqz hzW
        have hcases1 : z1 ∈ WELLORD1.seg W1 z2 ∨ z1 = z2 :=
          Or.elim (seg_or_eq_of_pair hpW2)
            (fun hs => Or.inl (Eq.subst (motive := fun s => z1 ∈ s)
              (A13 z2 hz2C).symm hs))
            Or.inr
        have hpW1 := pair_of_seg_or_eq hwo1 hz1F1 hz2F1 hcases1
        have hz1s : z1 ∈ WELLORD1.seg W1 y3 :=
          Eq.subst (motive := fun s => z1 ∈ s) hCseg1 hz1C
        have hz2s : z2 ∈ WELLORD1.seg W1 y3 :=
          Eq.subst (motive := fun s => z2 ∈ s) hCseg1 hz2C
        exact (mem_restrict2_iff W1 (WELLORD1.seg W1 y3) z).mpr
          ⟨Eq.subst (motive := fun s => s ∈ W1) heqz.symm hpW1,
            Eq.subst (motive := fun s => s ∈
                ZFMISC_1.product (WELLORD1.seg W1 y3) (WELLORD1.seg W1 y3))
              heqz.symm ((ZFMISC_1.th87 (x := z1) (y := z2)
                (X := WELLORD1.seg W1 y3) (Y := WELLORD1.seg W1 y3)).mpr
                ⟨hz1s, hz2s⟩)⟩
    have hy3F2 : y3 ∈ RELAT_1.field W2 :=
      Eq.subst (motive := fun s => s ∈ RELAT_1.field W2) hy3eq.symm hy4F
    exact hy3nC ((hC' y3).mpr ⟨hy3F, hy3F2, heqR⟩)
  have nest_of_C_eq_field2 (hCeq : C = RELAT_1.field W2) :
      W2 ⊆ W1 ∧ ∀ x, x ∈ RELAT_1.field W2 →
        WELLORD1.seg W2 x = WELLORD1.seg W1 x := by
    have hsub : W2 ⊆ W1 :=
      RELAT_1.rel_subset hRel2 fun z1 z2 hp => by
        have hz1C : z1 ∈ C :=
          Eq.subst (motive := fun s => z1 ∈ s) hCeq.symm
            (RELAT_1.th15 hp).1
        have hz2C : z2 ∈ C :=
          Eq.subst (motive := fun s => z2 ∈ s) hCeq.symm
            (RELAT_1.th15 hp).2
        have hz1F1 : z1 ∈ RELAT_1.field W1 := ((hC' z1).mp hz1C).1
        have hz2F1 : z2 ∈ RELAT_1.field W1 := ((hC' z2).mp hz2C).1
        have hcases : z1 ∈ WELLORD1.seg W1 z2 ∨ z1 = z2 :=
          Or.elim (seg_or_eq_of_pair hp)
            (fun hs => Or.inl (Eq.subst (motive := fun s => z1 ∈ s)
              (A13 z2 hz2C).symm hs))
            Or.inr
        exact pair_of_seg_or_eq hwo1 hz1F1 hz2F1 hcases
    refine ⟨hsub, fun x hx => ?_⟩
    have hxC : x ∈ C :=
      Eq.subst (motive := fun s => x ∈ s) hCeq.symm hx
    exact (A13 x hxC).symm
  have nest_of_C_eq_field1 (hCeq : C = RELAT_1.field W1) :
      W1 ⊆ W2 ∧ ∀ x, x ∈ RELAT_1.field W1 →
        WELLORD1.seg W1 x = WELLORD1.seg W2 x := by
    have hsub : W1 ⊆ W2 :=
      RELAT_1.rel_subset hRel1 fun z1 z2 hp => by
        have hz1C : z1 ∈ C :=
          Eq.subst (motive := fun s => z1 ∈ s) hCeq.symm
            (RELAT_1.th15 hp).1
        have hz2C : z2 ∈ C :=
          Eq.subst (motive := fun s => z2 ∈ s) hCeq.symm
            (RELAT_1.th15 hp).2
        have hz1F2 : z1 ∈ RELAT_1.field W2 := ((hC' z1).mp hz1C).2.1
        have hz2F2 : z2 ∈ RELAT_1.field W2 := ((hC' z2).mp hz2C).2.1
        have hcases : z1 ∈ WELLORD1.seg W2 z2 ∨ z1 = z2 :=
          Or.elim (seg_or_eq_of_pair hp)
            (fun hs => Or.inl (Eq.subst (motive := fun s => z1 ∈ s)
              (A13 z2 hz2C) hs))
            Or.inr
        exact pair_of_seg_or_eq hwo2 hz1F2 hz2F2 hcases
    exact ⟨hsub, fun x hx => A13 x
      (Eq.subst (motive := fun s => x ∈ s) hCeq.symm hx)⟩
  exact Or.elim A55
    (fun h => Or.inl (nest_of_C_eq_field1 h))
    (fun h => Or.inr (nest_of_C_eq_field2 h))

/-- `WELLSET1:5` (`Th5`) — full Mizar statement (no extra `∅ ∉ D`). -/
theorem th5 {F D : TarskiSet.{u}}
    (hF : ∀ X, X ∈ D →
      FUNCT_1.apply F X ∉ X ∧ FUNCT_1.apply F X ∈ TARSKI.union D) :
    ∃ R, RELAT_1.field R ⊆ TARSKI.union D ∧
      WELLORD1.isWellOrdering R ∧ RELAT_1.field R ∉ D ∧
      ∀ y, y ∈ RELAT_1.field R →
        WELLORD1.seg R y ∈ D ∧ FUNCT_1.apply F (WELLORD1.seg R y) = y := by
  let U := TARSKI.union D
  let W0 := ZFMISC_1.bool (ZFMISC_1.product U U)
  obtain ⟨G, hG⟩ := sch_RSeparation W0 (isApprox F D)
  obtain ⟨S, hSrel, hS⟩ :=
    RELAT_1.sch_RelExistence U U
      (fun x y => ∃ W, TARSKI.pair x y ∈ W ∧ W ∈ G)
  have memG_rel {W : TarskiSet.{u}} (hW : W ∈ G) :
      RELAT_1.isRelation W :=
    RELAT_1.subset_isRelation (RELAT_1.product_isRelation U U)
      ((ZFMISC_1.def1 (ZFMISC_1.product U U) W).mp ((hG W).mp hW).1)
  have memG_approx {W : TarskiSet.{u}} (hW : W ∈ G) :
      isApprox F D W := ((hG W).mp hW).2
  have memG_sub {W : TarskiSet.{u}} (hW : W ∈ G) :
      W ⊆ ZFMISC_1.product U U :=
    (ZFMISC_1.def1 (ZFMISC_1.product U U) W).mp ((hG W).mp hW).1
  have A4 (x : TarskiSet.{u}) (hx : x ∈ RELAT_1.field S) :
      x ∈ U ∧ ∃ W, x ∈ RELAT_1.field W ∧ W ∈ G := by
    obtain ⟨y, hor⟩ := (th1 S x).mp hx
    exact Or.elim hor
      (fun hp =>
        let ⟨hxU, _, ⟨W, hpW, hWG⟩⟩ := (hS x y).mp hp
        ⟨hxU, ⟨W, (RELAT_1.th15 hpW).1, hWG⟩⟩)
      (fun hp =>
        let ⟨_, hxU, ⟨W, hpW, hWG⟩⟩ := (hS y x).mp hp
        ⟨hxU, ⟨W, (RELAT_1.th15 hpW).2, hWG⟩⟩)
  have hfield_sub : RELAT_1.field S ⊆ U := fun x hx => (A4 x hx).1
  have A7 {W1 W2 : TarskiSet.{u}} (h1 : W1 ∈ G) (h2 : W2 ∈ G) :
      (W1 ⊆ W2 ∧ ∀ x, x ∈ RELAT_1.field W1 →
          WELLORD1.seg W1 x = WELLORD1.seg W2 x) ∨
        (W2 ⊆ W1 ∧ ∀ x, x ∈ RELAT_1.field W2 →
          WELLORD1.seg W2 x = WELLORD1.seg W1 x) :=
    approx_comparable (memG_rel h1) (memG_rel h2)
      (memG_approx h1) (memG_approx h2)
  have pair_in_S_of_G {W x y : TarskiSet.{u}} (hW : W ∈ G)
      (hp : TARSKI.pair x y ∈ W) : TARSKI.pair x y ∈ S := by
    obtain ⟨z1, z2, hz1, hz2, heq⟩ := ZFMISC_1.th84 (memG_sub hW) hp
    have ⟨heqx, heqy⟩ := TARSKI.pair_inj.mp heq
    exact (hS x y).mpr
      ⟨Eq.subst (motive := fun s => s ∈ U) heqx.symm hz1,
        Eq.subst (motive := fun s => s ∈ U) heqy.symm hz2,
        ⟨W, hp, hW⟩⟩
  have A97 {W : TarskiSet.{u}} (hW : W ∈ G) :
      RELAT_1.field W ⊆ RELAT_1.field S := by
    intro x hx
    obtain ⟨y, hor⟩ := (th1 W x).mp hx
    exact Or.elim hor
      (fun hp => (th1 S x).mpr ⟨y, Or.inl (pair_in_S_of_G hW hp)⟩)
      (fun hp => (th1 S x).mpr ⟨y, Or.inr (pair_in_S_of_G hW hp)⟩)
  have seg_agree_of_both_fields {W1 W2 y : TarskiSet.{u}}
      (h1 : W1 ∈ G) (h2 : W2 ∈ G)
      (hy1 : y ∈ RELAT_1.field W1) (hy2 : y ∈ RELAT_1.field W2) :
      WELLORD1.seg W1 y = WELLORD1.seg W2 y :=
    Or.elim (A7 h1 h2)
      (fun ⟨_, hseg⟩ => hseg y hy1)
      (fun ⟨_, hseg⟩ => (hseg y hy2).symm)
  have A103 (y : TarskiSet.{u}) (hy : y ∈ RELAT_1.field S) :
      WELLORD1.seg S y ∈ D ∧ FUNCT_1.apply F (WELLORD1.seg S y) = y := by
    obtain ⟨hyU, ⟨W, hyW, hWG⟩⟩ := A4 y hy
    have hsegEq : WELLORD1.seg W y = WELLORD1.seg S y := by
      apply eq_of_mem
      intro x
      constructor
      · intro hx
        have ⟨hne, hp⟩ := (WELLORD1.th1 W y x).mp hx
        have hxU : x ∈ U :=
          hfield_sub x (A97 hWG x (RELAT_1.th15 hp).1)
        exact (WELLORD1.th1 S y x).mpr
          ⟨hne, (hS x y).mpr ⟨hxU, hyU, ⟨W, hp, hWG⟩⟩⟩
      · intro hx
        have ⟨hne, hpS⟩ := (WELLORD1.th1 S y x).mp hx
        obtain ⟨_, _, ⟨W1, hpW1, hW1G⟩⟩ := (hS x y).mp hpS
        have hyW1 : y ∈ RELAT_1.field W1 := (RELAT_1.th15 hpW1).2
        exact Eq.subst (motive := fun s => x ∈ s)
          (seg_agree_of_both_fields hW1G hWG hyW1 hyW)
          ((WELLORD1.th1 W1 y x).mpr ⟨hne, hpW1⟩)
    have happ := (memG_approx hWG).2 y hyW
    exact ⟨Eq.subst (motive := fun s => s ∈ D) hsegEq happ.1,
      Eq.subst (motive := fun s => FUNCT_1.apply F s = y) hsegEq happ.2⟩
  have A84 {x y : TarskiSet.{u}}
      (_hx : x ∈ RELAT_1.field S) (_hy : y ∈ RELAT_1.field S)
      (hxy : TARSKI.pair x y ∈ S) (hyx : TARSKI.pair y x ∈ S) : x = y := by
    obtain ⟨_, _, ⟨W1, hp1, h1⟩⟩ := (hS x y).mp hxy
    obtain ⟨_, _, ⟨W2, hp2, h2⟩⟩ := (hS y x).mp hyx
    exact Or.elim (A7 h1 h2)
      (fun ⟨hsub, _⟩ =>
        ((RELAT_2.def4 W2 (RELAT_1.field W2)).mp
          ((WELLORD1.th4 W2).mpr (memG_approx h2).1).2.2.1)
          x y (RELAT_1.th15 (hsub (TARSKI.pair x y) hp1)).1
          (RELAT_1.th15 (hsub (TARSKI.pair x y) hp1)).2
          (hsub (TARSKI.pair x y) hp1) hp2)
      (fun ⟨hsub, _⟩ =>
        ((RELAT_2.def4 W1 (RELAT_1.field W1)).mp
          ((WELLORD1.th4 W1).mpr (memG_approx h1).1).2.2.1)
          x y (RELAT_1.th15 hp1).1 (RELAT_1.th15 hp1).2 hp1
          (hsub (TARSKI.pair y x) hp2))
  have A96 : RELAT_2.isAntisymmetricIn S (RELAT_1.field S) :=
    (RELAT_2.def4 S (RELAT_1.field S)).mpr fun x y hx hy hxy hyx =>
      A84 hx hy hxy hyx
  have A117 {x y : TarskiSet.{u}}
      (hx : x ∈ RELAT_1.field S) (hy : y ∈ RELAT_1.field S) (hne : x ≠ y) :
      TARSKI.pair x y ∈ S ∨ TARSKI.pair y x ∈ S := by
    obtain ⟨_, ⟨W1, hxW1, h1⟩⟩ := A4 x hx
    obtain ⟨_, ⟨W2, hyW2, h2⟩⟩ := A4 y hy
    exact Or.elim (A7 h1 h2)
      (fun ⟨hsub, _⟩ =>
        Or.elim (((RELAT_2.def6 W2 (RELAT_1.field W2)).mp
            ((WELLORD1.th4 W2).mpr (memG_approx h2).1).2.2.2.1)
            x y (RELAT_1.th16 hsub x hxW1) hyW2 hne)
          (fun hp => Or.inl (pair_in_S_of_G h2 hp))
          (fun hp => Or.inr (pair_in_S_of_G h2 hp)))
      (fun ⟨hsub, _⟩ =>
        Or.elim (((RELAT_2.def6 W1 (RELAT_1.field W1)).mp
            ((WELLORD1.th4 W1).mpr (memG_approx h1).1).2.2.2.1)
            x y hxW1 (RELAT_1.th16 hsub y hyW2) hne)
          (fun hp => Or.inl (pair_in_S_of_G h1 hp))
          (fun hp => Or.inr (pair_in_S_of_G h1 hp)))
  have A129 : RELAT_2.isConnectedIn S (RELAT_1.field S) :=
    (RELAT_2.def6 S (RELAT_1.field S)).mpr fun x y hx hy hne =>
      A117 hx hy hne
  have A130 : WELLORD1.isWellFoundedIn S (RELAT_1.field S) := by
    intro Y hY hne
    obtain ⟨y, hyY⟩ := exists_mem_of_ne hne
    obtain ⟨_, ⟨W, hyW, hWG⟩⟩ := A4 y (hY y hyY)
    have hwf := ((WELLORD1.th4 W).mpr (memG_approx hWG).1).2.2.2.2
    let A := Y ∩ RELAT_1.field W
    have hAsub : A ⊆ RELAT_1.field W := fun z hz =>
      ((XBOOLE_0.def4 Y (RELAT_1.field W) z).mp hz).2
    have hAne : A ≠ (∅ : TarskiSet.{u}) := fun hempty =>
      ((XBOOLE_0.empty_iff y).mp
        (Eq.subst (motive := fun s => y ∈ s) hempty
          ((XBOOLE_0.def4 Y (RELAT_1.field W) y).mpr ⟨hyY, hyW⟩))).elim
    obtain ⟨a, haA, hmiss⟩ := hwf A hAsub hAne
    have haY : a ∈ Y := ((XBOOLE_0.def4 Y (RELAT_1.field W) a).mp haA).1
    refine ⟨a, haY, ?_⟩
    apply Classical.byContradiction
    intro hnmiss
    obtain ⟨x, hxSeg, hxY⟩ :=
      (XBOOLE_0.th3 (WELLORD1.seg S a) Y).mp hnmiss
    have ⟨hne', hpS⟩ := (WELLORD1.th1 S a x).mp hxSeg
    obtain ⟨_, _, ⟨W1, hpW1, hW1G⟩⟩ := (hS x a).mp hpS
    have haW1 : a ∈ RELAT_1.field W1 := (RELAT_1.th15 hpW1).2
    have haW : a ∈ RELAT_1.field W :=
      ((XBOOLE_0.def4 Y (RELAT_1.field W) a).mp haA).2
    have hxWseg : x ∈ WELLORD1.seg W a :=
      Eq.subst (motive := fun s => x ∈ s)
        (seg_agree_of_both_fields hW1G hWG haW1 haW)
        ((WELLORD1.th1 W1 a x).mpr ⟨hne', hpW1⟩)
    have hxA : x ∈ A :=
      (XBOOLE_0.def4 Y (RELAT_1.field W) x).mpr
        ⟨hxY, (RELAT_1.th15 ((WELLORD1.th1 W a x).mp hxWseg).2).1⟩
    exact ((XBOOLE_0.empty_iff x).mp
      (Eq.subst (motive := fun s => x ∈ s)
        ((XBOOLE_0.def7 (WELLORD1.seg W a) A).mp hmiss)
        ((XBOOLE_0.def4 (WELLORD1.seg W a) A x).mpr
          ⟨hxWseg, hxA⟩))).elim
  have A145 {x y z : TarskiSet.{u}}
      (_hx : x ∈ RELAT_1.field S) (_hy : y ∈ RELAT_1.field S)
      (_hz : z ∈ RELAT_1.field S)
      (hxy : TARSKI.pair x y ∈ S) (hyz : TARSKI.pair y z ∈ S) :
      TARSKI.pair x z ∈ S := by
    obtain ⟨_, _, ⟨W1, hp1, h1⟩⟩ := (hS x y).mp hxy
    obtain ⟨_, _, ⟨W2, hp2, h2⟩⟩ := (hS y z).mp hyz
    have hyW1 : y ∈ RELAT_1.field W1 := (RELAT_1.th15 hp1).2
    have hyW2 : y ∈ RELAT_1.field W2 := (RELAT_1.th15 hp2).1
    have hsegEq : WELLORD1.seg W1 y = WELLORD1.seg W2 y :=
      seg_agree_of_both_fields h1 h2 hyW1 hyW2
    have hpxyW2 : TARSKI.pair x y ∈ W2 := by
      apply Classical.byCases (p := x ∈ WELLORD1.seg W1 y)
      · intro hxseg
        exact ((WELLORD1.th1 W2 y x).mp
          (Eq.subst (motive := fun s => x ∈ s) hsegEq hxseg)).2
      · intro hnseg
        have hxF1 : x ∈ RELAT_1.field W1 := (RELAT_1.th15 hp1).1
        have hyx : TARSKI.pair y x ∈ W1 :=
          th3 hxF1 hyW1 (memG_approx h1).1 hnseg
        have heq : x = y :=
          ((RELAT_2.def4 W1 (RELAT_1.field W1)).mp
            ((WELLORD1.th4 W1).mpr (memG_approx h1).1).2.2.1)
            x y hxF1 hyW1 hp1 hyx
        exact Eq.subst (motive := fun s => TARSKI.pair s y ∈ W2) heq.symm
          (((RELAT_2.def1 W2 (RELAT_1.field W2)).mp
            ((WELLORD1.th4 W2).mpr (memG_approx h2).1).1) y hyW2)
    have hzW2 : z ∈ RELAT_1.field W2 := (RELAT_1.th15 hp2).2
    have hxW2 : x ∈ RELAT_1.field W2 := (RELAT_1.th15 hpxyW2).1
    exact pair_in_S_of_G h2
      (((RELAT_2.def8 W2 (RELAT_1.field W2)).mp
        ((WELLORD1.th4 W2).mpr (memG_approx h2).1).2.1)
        x y z hxW2 hyW2 hzW2 hpxyW2 hp2)
  have A164 : RELAT_2.isTransitiveIn S (RELAT_1.field S) :=
    (RELAT_2.def8 S (RELAT_1.field S)).mpr fun x y z hx hy hz hxy hyz =>
      A145 hx hy hz hxy hyz
  have A165 {x : TarskiSet.{u}} (hx : x ∈ RELAT_1.field S) :
      TARSKI.pair x x ∈ S := by
    obtain ⟨_, ⟨W, hxW, hWG⟩⟩ := A4 x hx
    exact pair_in_S_of_G hWG
      (((RELAT_2.def1 W (RELAT_1.field W)).mp
        ((WELLORD1.th4 W).mpr (memG_approx hWG).1).1) x hxW)
  have A165' : RELAT_2.isReflexiveIn S (RELAT_1.field S) :=
    (RELAT_2.def1 S (RELAT_1.field S)).mpr fun x hx => A165 hx
  have hS_wo : WELLORD1.isWellOrdering S :=
    (WELLORD1.th4 S).mp ⟨A165', A164, A96, A129, A130⟩
  have A170 : RELAT_1.field S ∉ D := by
    intro hfieldD
    let a0 := FUNCT_1.apply F (RELAT_1.field S)
    have ha0nF : a0 ∉ RELAT_1.field S := (hF (RELAT_1.field S) hfieldD).1
    have ha0U : a0 ∈ U := (hF (RELAT_1.field S) hfieldD).2
    let W3 := ZFMISC_1.product (RELAT_1.field S) (TARSKI.singleton a0)
    let W4 := TARSKI.singleton (TARSKI.pair a0 a0)
    let W1 := (S ∪ W3) ∪ W4
    have hW1mem {x y : TarskiSet.{u}} :
        TARSKI.pair x y ∈ W1 ↔
          TARSKI.pair x y ∈ S ∨ TARSKI.pair x y ∈ W3 ∨
            TARSKI.pair x y ∈ W4 := by
      constructor
      · intro hp
        exact Or.elim ((XBOOLE_0.def3 (S ∪ W3) W4 (TARSKI.pair x y)).mp hp)
          (fun h => Or.elim ((XBOOLE_0.def3 S W3 (TARSKI.pair x y)).mp h)
            Or.inl (fun hw => Or.inr (Or.inl hw)))
          (fun hw => Or.inr (Or.inr hw))
      · intro hor
        exact Or.elim hor
          (fun hs => (XBOOLE_0.def3 (S ∪ W3) W4 (TARSKI.pair x y)).mpr
            (Or.inl ((XBOOLE_0.def3 S W3 (TARSKI.pair x y)).mpr (Or.inl hs))))
          (fun hor' => Or.elim hor'
            (fun hw => (XBOOLE_0.def3 (S ∪ W3) W4 (TARSKI.pair x y)).mpr
              (Or.inl ((XBOOLE_0.def3 S W3 (TARSKI.pair x y)).mpr
                (Or.inr hw))))
            (fun hw => (XBOOLE_0.def3 (S ∪ W3) W4 (TARSKI.pair x y)).mpr
              (Or.inr hw)))
    have ha0W1 : a0 ∈ RELAT_1.field W1 :=
      (RELAT_1.th15 ((hW1mem (x := a0) (y := a0)).mpr
        (Or.inr (Or.inr ((TARSKI.def1 (TARSKI.pair a0 a0)
          (TARSKI.pair a0 a0)).mpr rfl))))).1
    have field_cases {x : TarskiSet.{u}} (hx : x ∈ RELAT_1.field W1) :
        x ∈ RELAT_1.field S ∨ x = a0 := by
      obtain ⟨y, hor⟩ := (th1 W1 x).mp hx
      have fromPair (p q : TarskiSet.{u}) (hp : TARSKI.pair p q ∈ W1) :
          (p ∈ RELAT_1.field S ∨ p = a0) ∧
            (q ∈ RELAT_1.field S ∨ q = a0) :=
        Or.elim ((hW1mem (x := p) (y := q)).mp hp)
          (fun hs => ⟨Or.inl (RELAT_1.th15 hs).1, Or.inl (RELAT_1.th15 hs).2⟩)
          (fun hor' => Or.elim hor'
            (fun hw3 =>
              let ⟨hpF, hqeq⟩ :=
                (ZFMISC_1.th106 (x := p) (y := q)
                  (X := RELAT_1.field S) (z := a0)).mp hw3
              ⟨Or.inl hpF, Or.inr hqeq⟩)
            (fun hw4 =>
              let ⟨hpeq, hqeq⟩ := TARSKI.pair_inj.mp
                ((TARSKI.def1 (TARSKI.pair a0 a0) (TARSKI.pair p q)).mp hw4)
              ⟨Or.inr hpeq, Or.inr hqeq⟩))
      exact Or.elim hor
        (fun hp => (fromPair x y hp).1)
        (fun hp => (fromPair y x hp).2)
    have hfieldW1 : RELAT_1.field W1 =
        RELAT_1.field S ∪ TARSKI.singleton a0 := by
      apply eq_of_mem
      intro x
      constructor
      · intro hx
        exact Or.elim (field_cases hx)
          (fun h => (XBOOLE_0.def3 (RELAT_1.field S) (TARSKI.singleton a0) x).mpr
            (Or.inl h))
          (fun heq => (XBOOLE_0.def3 (RELAT_1.field S) (TARSKI.singleton a0) x).mpr
            (Or.inr ((TARSKI.def1 a0 x).mpr heq)))
      · intro hx
        exact Or.elim
          ((XBOOLE_0.def3 (RELAT_1.field S) (TARSKI.singleton a0) x).mp hx)
          (fun hxS => (th1 W1 x).mpr
            ⟨x, Or.inl ((hW1mem (x := x) (y := x)).mpr (Or.inl (A165 hxS)))⟩)
          (fun hxA =>
            Eq.subst (motive := fun s => s ∈ RELAT_1.field W1)
              ((TARSKI.def1 a0 x).mp hxA).symm ha0W1)
    have pair_to_S {x y : TarskiSet.{u}}
        (hp : TARSKI.pair x y ∈ W1) (hy : y ∈ RELAT_1.field S) :
        TARSKI.pair x y ∈ S ∧ x ∈ RELAT_1.field S := by
      have hnW4 : TARSKI.pair x y ∉ W4 := fun hw4 =>
        ha0nF (Eq.subst (motive := fun s => s ∈ RELAT_1.field S)
          (TARSKI.pair_inj.mp
            ((TARSKI.def1 (TARSKI.pair a0 a0) (TARSKI.pair x y)).mp hw4)).2
          hy)
      have hnW3 : TARSKI.pair x y ∉ W3 := fun hw3 =>
        ha0nF (Eq.subst (motive := fun s => s ∈ RELAT_1.field S)
          ((ZFMISC_1.th106 (x := x) (y := y)
            (X := RELAT_1.field S) (z := a0)).mp hw3).2 hy)
      have hs : TARSKI.pair x y ∈ S :=
        Or.elim ((hW1mem (x := x) (y := y)).mp hp) id
          (fun hor => Or.elim hor (fun h => (hnW3 h).elim)
            (fun h => (hnW4 h).elim))
      exact ⟨hs, (RELAT_1.th15 hs).1⟩
    have seg_eq_S {y : TarskiSet.{u}} (hy : y ∈ RELAT_1.field S) :
        WELLORD1.seg W1 y = WELLORD1.seg S y := by
      apply eq_of_mem
      intro x
      constructor
      · intro hx
        have ⟨hne, hp⟩ := (WELLORD1.th1 W1 y x).mp hx
        exact (WELLORD1.th1 S y x).mpr ⟨hne, (pair_to_S hp hy).1⟩
      · intro hx
        have ⟨hne, hs⟩ := (WELLORD1.th1 S y x).mp hx
        exact (WELLORD1.th1 W1 y x).mpr
          ⟨hne, (hW1mem (x := x) (y := y)).mpr (Or.inl hs)⟩
    have seg_a0 : WELLORD1.seg W1 a0 = RELAT_1.field S := by
      apply eq_of_mem
      intro x
      constructor
      · intro hx
        have ⟨hne, hp⟩ := (WELLORD1.th1 W1 a0 x).mp hx
        exact Or.elim (field_cases (RELAT_1.th15 hp).1) id
          (fun heq => (hne heq).elim)
      · intro hx
        exact (WELLORD1.th1 W1 a0 x).mpr
          ⟨fun heq => ha0nF (Eq.subst (motive := fun s => s ∈ RELAT_1.field S)
              heq hx),
            (hW1mem (x := x) (y := a0)).mpr (Or.inr (Or.inl
              ((ZFMISC_1.th106 (x := x) (y := a0)
                (X := RELAT_1.field S) (z := a0)).mpr ⟨hx, rfl⟩)))⟩
    have hW1rel : RELAT_1.isRelation W1 :=
      RELAT_1.union_isRelation
        (RELAT_1.union_isRelation hSrel
          (RELAT_1.product_isRelation _ _))
        (RELAT_1.singleton_pair_isRelation _ _)
    have hW1sub : W1 ⊆ ZFMISC_1.product U U :=
      RELAT_1.rel_subset hW1rel fun x y hp =>
        Or.elim ((hW1mem (x := x) (y := y)).mp hp)
          (fun hs =>
            let ⟨hxU, hyU, _⟩ := (hS x y).mp hs
            (ZFMISC_1.th87 (x := x) (y := y) (X := U) (Y := U)).mpr
              ⟨hxU, hyU⟩)
          (fun hor => Or.elim hor
            (fun hw3 =>
              let ⟨hxF, hyeq⟩ :=
                (ZFMISC_1.th106 (x := x) (y := y)
                  (X := RELAT_1.field S) (z := a0)).mp hw3
              (ZFMISC_1.th87 (x := x) (y := y) (X := U) (Y := U)).mpr
                ⟨hfield_sub x hxF,
                  Eq.subst (motive := fun s => s ∈ U) hyeq.symm ha0U⟩)
            (fun hw4 =>
              let ⟨hxeq, hyeq⟩ := TARSKI.pair_inj.mp
                ((TARSKI.def1 (TARSKI.pair a0 a0) (TARSKI.pair x y)).mp hw4)
              (ZFMISC_1.th87 (x := x) (y := y) (X := U) (Y := U)).mpr
                ⟨Eq.subst (motive := fun s => s ∈ U) hxeq.symm ha0U,
                  Eq.subst (motive := fun s => s ∈ U) hyeq.symm ha0U⟩))
    have hconn : RELAT_2.isConnectedIn W1 (RELAT_1.field W1) :=
      (RELAT_2.def6 W1 (RELAT_1.field W1)).mpr fun x y hx hy hne => by
        have hx' := field_cases hx
        have hy' := field_cases hy
        exact Or.elim hx'
          (fun hxS => Or.elim hy'
            (fun hyS => Or.elim (A117 hxS hyS hne)
              (fun hp => Or.inl ((hW1mem (x := x) (y := y)).mpr (Or.inl hp)))
              (fun hp => Or.inr ((hW1mem (x := y) (y := x)).mpr (Or.inl hp))))
            (fun hyeq => Or.inl ((hW1mem (x := x) (y := y)).mpr
              (Or.inr (Or.inl ((ZFMISC_1.th106 (x := x) (y := y)
                (X := RELAT_1.field S) (z := a0)).mpr
                ⟨hxS, hyeq⟩))))))
          (fun hxeq => Or.elim hy'
            (fun hyS => Or.inr ((hW1mem (x := y) (y := x)).mpr
              (Or.inr (Or.inl ((ZFMISC_1.th106 (x := y) (y := x)
                (X := RELAT_1.field S) (z := a0)).mpr
                ⟨hyS, hxeq⟩)))))
            (fun hyeq => (hne (hxeq.trans hyeq.symm)).elim))
    have hanti : RELAT_2.isAntisymmetricIn W1 (RELAT_1.field W1) :=
      (RELAT_2.def4 W1 (RELAT_1.field W1)).mpr fun x y hx hy hxy hyx => by
        exact Or.elim (field_cases hx)
          (fun hxS =>
            have ⟨hsyx, hyS⟩ := pair_to_S hyx hxS
            have ⟨hsxy, _⟩ := pair_to_S hxy hyS
            A84 hxS hyS hsxy hsyx)
          (fun hxeq => Or.elim (field_cases hy)
            (fun hyS =>
              have ⟨_, hxS⟩ := pair_to_S hxy hyS
              (ha0nF (Eq.subst (motive := fun s => s ∈ RELAT_1.field S)
                hxeq hxS)).elim)
            (fun hyeq => hxeq.trans hyeq.symm))
    have hwf : WELLORD1.isWellFoundedIn W1 (RELAT_1.field W1) := by
      intro Y hY hne
      apply Classical.byCases (p := Y ⊆ RELAT_1.field S)
      · intro hYS
        obtain ⟨a, haY, hmiss⟩ := A130 Y hYS hne
        refine ⟨a, haY, ?_⟩
        apply (XBOOLE_0.def7 (WELLORD1.seg W1 a) Y).mpr
        have hseg : WELLORD1.seg W1 a = WELLORD1.seg S a :=
          seg_eq_S (hYS a haY)
        exact Eq.subst (motive := fun s => s ∩ Y = (∅ : TarskiSet.{u}))
          hseg.symm ((XBOOLE_0.def7 (WELLORD1.seg S a) Y).mp hmiss)
      · intro hnYS
        apply Classical.byCases
          (p := RELAT_1.field S ∩ Y = (∅ : TarskiSet.{u}))
        · intro hempty
          obtain ⟨y, hyY⟩ := exists_mem_of_ne hne
          have hyW1 : y ∈ RELAT_1.field W1 := hY y hyY
          have hyA0 : y = a0 :=
            Or.elim (field_cases hyW1) (fun hyS =>
              ((XBOOLE_0.empty_iff y).mp
                (Eq.subst (motive := fun s => y ∈ s) hempty
                  ((XBOOLE_0.def4 (RELAT_1.field S) Y y).mpr
                    ⟨hyS, hyY⟩))).elim) id
          refine ⟨y, hyY, ?_⟩
          apply (XBOOLE_0.def7 (WELLORD1.seg W1 y) Y).mpr
          apply eq_of_mem
          intro z
          constructor
          · intro hz
            have ⟨hzSeg, hzY⟩ :=
              (XBOOLE_0.def4 (WELLORD1.seg W1 y) Y z).mp hz
            have hzSeg' : z ∈ WELLORD1.seg W1 a0 :=
              Eq.subst (motive := fun s => z ∈ WELLORD1.seg W1 s) hyA0 hzSeg
            have hzF : z ∈ RELAT_1.field S :=
              Eq.subst (motive := fun s => z ∈ s) seg_a0 hzSeg'
            exact ((XBOOLE_0.empty_iff z).mp
              (Eq.subst (motive := fun s => z ∈ s) hempty
                ((XBOOLE_0.def4 (RELAT_1.field S) Y z).mpr
                  ⟨hzF, hzY⟩))).elim
          · intro hz
            exact ((XBOOLE_0.empty_iff z).mp hz).elim
        · intro hneInter
          let X := RELAT_1.field S ∩ Y
          have hXsub : X ⊆ RELAT_1.field S := fun z hz =>
            ((XBOOLE_0.def4 (RELAT_1.field S) Y z).mp hz).1
          obtain ⟨a, haX, hmiss⟩ := A130 X hXsub hneInter
          have haY : a ∈ Y :=
            ((XBOOLE_0.def4 (RELAT_1.field S) Y a).mp haX).2
          refine ⟨a, haY, ?_⟩
          apply (XBOOLE_0.def7 (WELLORD1.seg W1 a) Y).mpr
          have hseg : WELLORD1.seg W1 a = WELLORD1.seg S a :=
            seg_eq_S ((XBOOLE_0.def4 (RELAT_1.field S) Y a).mp haX).1
          apply eq_of_mem
          intro z
          constructor
          · intro hz
            have ⟨hzSeg, hzY⟩ :=
              (XBOOLE_0.def4 (WELLORD1.seg W1 a) Y z).mp hz
            have hzSseg : z ∈ WELLORD1.seg S a :=
              Eq.subst (motive := fun s => z ∈ s) hseg hzSeg
            have hzF : z ∈ RELAT_1.field S :=
              (RELAT_1.th15 ((WELLORD1.th1 S a z).mp hzSseg).2).1
            have hzX : z ∈ X :=
              (XBOOLE_0.def4 (RELAT_1.field S) Y z).mpr ⟨hzF, hzY⟩
            exact ((XBOOLE_0.empty_iff z).mp
              (Eq.subst (motive := fun s => z ∈ s)
                ((XBOOLE_0.def7 (WELLORD1.seg S a) X).mp hmiss)
                ((XBOOLE_0.def4 (WELLORD1.seg S a) X z).mpr
                  ⟨hzSseg, hzX⟩))).elim
          · intro hz
            exact ((XBOOLE_0.empty_iff z).mp hz).elim
    have htr : RELAT_2.isTransitiveIn W1 (RELAT_1.field W1) :=
      (RELAT_2.def8 W1 (RELAT_1.field W1)).mpr fun x y z hx _hy hz hxy hyz =>
        Or.elim (field_cases hz)
          (fun hzS =>
            have ⟨hsyz, hyS⟩ := pair_to_S hyz hzS
            have ⟨hsxy, hxS⟩ := pair_to_S hxy hyS
            (hW1mem (x := x) (y := z)).mpr
              (Or.inl (A145 hxS hyS hzS hsxy hsyz)))
          (fun hzeq => Or.elim (field_cases hx)
            (fun hxS => (hW1mem (x := x) (y := z)).mpr
              (Or.inr (Or.inl ((ZFMISC_1.th106 (x := x) (y := z)
                (X := RELAT_1.field S) (z := a0)).mpr ⟨hxS, hzeq⟩))))
            (fun hxeq => (hW1mem (x := x) (y := z)).mpr
              (Or.inr (Or.inr ((TARSKI.def1 (TARSKI.pair a0 a0)
                (TARSKI.pair x z)).mpr
                (by cases hxeq; cases hzeq; rfl))))))
    have href : RELAT_2.isReflexiveIn W1 (RELAT_1.field W1) :=
      (RELAT_2.def1 W1 (RELAT_1.field W1)).mpr fun x hx =>
        Or.elim (field_cases hx)
          (fun hxS => (hW1mem (x := x) (y := x)).mpr (Or.inl (A165 hxS)))
          (fun hxeq => (hW1mem (x := x) (y := x)).mpr
            (Or.inr (Or.inr ((TARSKI.def1 (TARSKI.pair a0 a0)
              (TARSKI.pair x x)).mpr
              (by cases hxeq; rfl)))))
    have hwo1 : WELLORD1.isWellOrdering W1 :=
      (WELLORD1.th4 W1).mp ⟨href, htr, hanti, hconn, hwf⟩
    have happ1 : ∀ y, y ∈ RELAT_1.field W1 →
        WELLORD1.seg W1 y ∈ D ∧
          FUNCT_1.apply F (WELLORD1.seg W1 y) = y := by
      intro y hy
      exact Or.elim (field_cases hy)
        (fun hyS =>
          have hseg := seg_eq_S hyS
          have happ := A103 y hyS
          ⟨Eq.subst (motive := fun s => s ∈ D) hseg.symm happ.1,
            Eq.subst (motive := fun s => FUNCT_1.apply F s = y)
              hseg.symm happ.2⟩)
        (fun hyeq =>
          have hseg : WELLORD1.seg W1 y = RELAT_1.field S :=
            Eq.subst (motive := fun s => WELLORD1.seg W1 s = RELAT_1.field S)
              hyeq.symm seg_a0
          ⟨Eq.subst (motive := fun s => s ∈ D) hseg.symm hfieldD,
            Eq.subst (motive := fun s => FUNCT_1.apply F s = y) hseg.symm
              (Eq.subst (motive := fun s => FUNCT_1.apply F (RELAT_1.field S) = s)
                hyeq.symm rfl)⟩)
    have hW1G : W1 ∈ G :=
      (hG W1).mpr ⟨(ZFMISC_1.def1 (ZFMISC_1.product U U) W1).mpr hW1sub,
        ⟨hwo1, happ1⟩⟩
    have ha0S : a0 ∈ RELAT_1.field S := A97 hW1G a0 ha0W1
    exact ha0nF ha0S
  exact ⟨S, hfield_sub, hS_wo, A170, A103⟩

/-- `WELLSET1:lm 1` (`Lm1`) -/
theorem lm1 (X M : TarskiSet.{u}) :
    TARSKI.are_equipotent X M ↔
      ∃ Z : TarskiSet.{u},
        (∀ x, x ∈ X → ∃ y, y ∈ M ∧ TARSKI.pair x y ∈ Z) ∧
        (∀ y, y ∈ M → ∃ x, x ∈ X ∧ TARSKI.pair x y ∈ Z) ∧
        ∀ x z1 y z2, TARSKI.pair x z1 ∈ Z → TARSKI.pair y z2 ∈ Z →
          (x = y ↔ z1 = z2) :=
  TARSKI.are_equipotent_iff X M

/-- `WELLSET1:6` (unlabeled final theorem): Zermelo's theorem.

**Proof variation (TARSKI axiom-free discipline).** Same statement as
Mizar; different proof because `ZFMISC_1.th112` omits Mizar
`TARSKI:3`(iii)–(iv). Lean reuses `WELLORD2.th17` and restricts
the witnessing relation to `N`. -/
theorem th6 (N : TarskiSet.{u}) :
    ∃ R, WELLORD1.isWellOrdering R ∧ RELAT_1.field R = N := by
  obtain ⟨R0, hwo⟩ := WELLORD2.th17 N
  obtain ⟨hwo', hfield⟩ := wellOrders_restrict2 hwo
  exact ⟨WELLORD1.restrict2 R0 N,
    (WELLORD1.th4 (WELLORD1.restrict2 R0 N)).mp
      (Eq.subst (motive := fun s =>
          WELLORD1.wellOrders (WELLORD1.restrict2 R0 N) s)
        hfield.symm hwo'),
    hfield⟩

end WELLSET1
