import MizarCCL.WELLORD1
import MizarCCL.MCART_1
import MizarCCL.ORDINAL1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/wellord2.miz`.
Authors: Grzegorz Bancerek (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Zermelo Theorem and the Axiom of Choice

1–1 Lean rendering of Mizar article `WELLORD2`
(`vendor/mml/wellord2.miz`). Import is `WELLORD1`, `MCART_1`, and
`ORDINAL1`. This file is in progress.
-/

universe u

open TarskiSet TARSKI

namespace WELLORD2

private theorem exists_mem_of_ne {A : TarskiSet.{u}}
    (h : A ≠ (∅ : TarskiSet.{u})) : ∃ x, x ∈ A :=
  Classical.byContradiction fun hne =>
    h (XBOOLE_0.empty_eq (fun hex => hne hex))

private theorem restrict2_isRelation (R Y : TarskiSet.{u}) :
    RELAT_1.isRelation (WELLORD1.restrict2 R Y) :=
  RELAT_1.subset_isRelation (RELAT_1.product_isRelation Y Y)
    (fun z hz =>
      ((XBOOLE_0.def4 R (ZFMISC_1.product Y Y) z).mp hz).2)

/-- Inclusion relation on `X`. `WELLORD2:def 1`. -/
noncomputable def RelIncl (X : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (RELAT_1.sch_RelExistence X X (fun Y Z => Y ⊆ Z))

theorem RelIncl_isRelation (X : TarskiSet.{u}) :
    RELAT_1.isRelation (RelIncl X) :=
  (Classical.choose_spec
    (RELAT_1.sch_RelExistence X X (fun Y Z => Y ⊆ Z))).1

theorem RelIncl_char (X Y Z : TarskiSet.{u}) :
    TARSKI.pair Y Z ∈ RelIncl X ↔ Y ∈ X ∧ Z ∈ X ∧ Y ⊆ Z :=
  (Classical.choose_spec
    (RELAT_1.sch_RelExistence X X (fun Y Z => Y ⊆ Z))).2 Y Z

/-- `WELLORD2:def 1` (`Def1`). `WELLORD2:1`–`6` are canceled. -/
theorem def1 (X : TarskiSet.{u}) :
    RELAT_1.field (RelIncl X) = X ∧
      ∀ Y Z, Y ∈ X → Z ∈ X → (TARSKI.pair Y Z ∈ RelIncl X ↔ Y ⊆ Z) := by
  constructor
  · apply TARSKI.extensionality
    intro x
    constructor
    · intro hx
      have hdomrng := (XBOOLE_0.def3 (RELAT_1.dom (RelIncl X))
        (RELAT_1.rng (RelIncl X)) x).mp hx
      exact Or.elim hdomrng
        (fun hd =>
          let ⟨y, hp⟩ := (RELAT_1.dom_iff (RelIncl X) x).mp hd
          ((RelIncl_char X x y).mp hp).1)
        (fun hr =>
          let ⟨y, hp⟩ := (RELAT_1.rng_iff (RelIncl X) x).mp hr
          ((RelIncl_char X y x).mp hp).2.1)
    · intro hx
      have hp : TARSKI.pair x x ∈ RelIncl X :=
        (RelIncl_char X x x).mpr ⟨hx, hx, fun _ ha => ha⟩
      exact (RELAT_1.th15 (a := x) (b := x) (R := RelIncl X) hp).1
  · intro Y Z hY hZ
    constructor
    · intro hp
      exact ((RelIncl_char X Y Z).mp hp).2.2
    · intro hsub
      exact (RelIncl_char X Y Z).mpr ⟨hY, hZ, hsub⟩

theorem RelIncl_field (X : TarskiSet.{u}) :
    RELAT_1.field (RelIncl X) = X :=
  (def1 X).1

theorem RelIncl_reflexive (X : TarskiSet.{u}) :
    RELAT_2.isReflexive (RelIncl X) :=
  (RELAT_2.def9 (RelIncl X)).mpr fun a ha =>
    let haX : a ∈ X :=
      Eq.subst (motive := fun s => a ∈ s) (RelIncl_field X) ha
    (RelIncl_char X a a).mpr ⟨haX, haX, fun _ hx => hx⟩

theorem RelIncl_transitive (X : TarskiSet.{u}) :
    RELAT_2.isTransitive (RelIncl X) :=
  (RELAT_2.def16 (RelIncl X)).mpr
    ((RELAT_2.def8 (RelIncl X) (RELAT_1.field (RelIncl X))).mpr
      fun a b c ha _hb hc hab hbc =>
        let haX : a ∈ X :=
          Eq.subst (motive := fun s => a ∈ s) (RelIncl_field X) ha
        let hcX : c ∈ X :=
          Eq.subst (motive := fun s => c ∈ s) (RelIncl_field X) hc
        let habs : a ⊆ b := ((RelIncl_char X a b).mp hab).2.2
        let hbcs : b ⊆ c := ((RelIncl_char X b c).mp hbc).2.2
        (RelIncl_char X a c).mpr ⟨haX, hcX, XBOOLE_1.th1 habs hbcs⟩)

theorem RelIncl_antisymmetric (X : TarskiSet.{u}) :
    RELAT_2.isAntisymmetric (RelIncl X) :=
  (RELAT_2.def12 (RelIncl X)).mpr
    ((RELAT_2.def4 (RelIncl X) (RELAT_1.field (RelIncl X))).mpr
      fun a b _ _ hab hba =>
        XBOOLE_0.def10.mpr
          ⟨((RelIncl_char X a b).mp hab).2.2,
            ((RelIncl_char X b a).mp hba).2.2⟩)

theorem RelIncl_connected {A : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) :
    RELAT_2.isConnected (RelIncl A) :=
  (RELAT_2.def14 (RelIncl A)).mpr
    ((RELAT_2.def6 (RelIncl A) (RELAT_1.field (RelIncl A))).mpr
      fun a b ha hb _hne =>
        let haA : a ∈ A :=
          Eq.subst (motive := fun s => a ∈ s) (RelIncl_field A) ha
        let hbA : b ∈ A :=
          Eq.subst (motive := fun s => b ∈ s) (RelIncl_field A) hb
        let haOrd : ORDINAL1.isOrdinal a := ORDINAL1.th13 hA haA
        let hbOrd : ORDINAL1.isOrdinal b := ORDINAL1.th13 hA hbA
        Or.elim (ORDINAL1.th15 haOrd hbOrd)
          (fun hab => Or.inl ((RelIncl_char A a b).mpr ⟨haA, hbA, hab⟩))
          (fun hba => Or.inr ((RelIncl_char A b a).mpr ⟨hbA, haA, hba⟩)))

theorem RelIncl_wellFounded {A : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) :
    WELLORD1.isWellFounded (RelIncl A) := by
  intro Y hYf hYne
  have hYsub : Y ⊆ A :=
    fun y hy =>
      Eq.subst (motive := fun s => y ∈ s) (RelIncl_field A) (hYf y hy)
  obtain ⟨x0, hx0⟩ := exists_mem_of_ne hYne
  have hx0A : x0 ∈ A := hYsub x0 hx0
  have hx0Ord : ORDINAL1.isOrdinal x0 := ORDINAL1.th13 hA hx0A
  obtain ⟨B, hBord, hBinY, hmin⟩ :=
    ORDINAL1.sch_OrdinalMin (fun s => s ∈ Y) ⟨x0, hx0Ord, hx0⟩
  refine ⟨B, hBinY, ?_⟩
  apply Classical.byContradiction
  intro hmeet
  have ⟨y, hys, hyY⟩ :=
    (XBOOLE_0.th3 (WELLORD1.seg (RelIncl A) B) Y).mp hmeet
  have ⟨hyne, hyp⟩ := (WELLORD1.th1 (RelIncl A) B y).mp hys
  have hyA : y ∈ A := ((RelIncl_char A y B).mp hyp).1
  have hyOrd : ORDINAL1.isOrdinal y := ORDINAL1.th13 hA hyA
  have hysub : y ⊆ B := ((RelIncl_char A y B).mp hyp).2.2
  have hBsub : B ⊆ y := hmin y hyOrd hyY
  exact hyne (XBOOLE_0.def10.mpr ⟨hysub, hBsub⟩)

theorem RelIncl_wellOrdering {A : TarskiSet.{u}}
    (hA : ORDINAL1.isOrdinal A) :
    WELLORD1.isWellOrdering (RelIncl A) :=
  ⟨RelIncl_reflexive A, RelIncl_transitive A, RelIncl_antisymmetric A,
    RelIncl_connected hA, RelIncl_wellFounded hA⟩

/-- `WELLORD2:7` (`Th7`) -/
theorem th7 {X Y : TarskiSet.{u}} (hY : Y ⊆ X) :
    WELLORD1.restrict2 (RelIncl X) Y = RelIncl Y :=
  RELAT_1.rel_eq (restrict2_isRelation (RelIncl X) Y)
    (RelIncl_isRelation Y) fun a b =>
      (WELLORD1.restrict2_iff (RelIncl X) Y a b).trans
        ⟨fun ⟨hp, ha, hb⟩ =>
          (RelIncl_char Y a b).mpr
            ⟨ha, hb, ((RelIncl_char X a b).mp hp).2.2⟩,
          fun hp =>
            let ⟨ha, hb, hsub⟩ := (RelIncl_char Y a b).mp hp
            ⟨(RelIncl_char X a b).mpr ⟨hY a ha, hY b hb, hsub⟩, ha, hb⟩⟩

/-- `WELLORD2:8` (`Th8`) -/
theorem th8 {A X : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hX : X ⊆ A) : WELLORD1.isWellOrdering (RelIncl X) :=
  Eq.subst (motive := WELLORD1.isWellOrdering) (th7 hX)
    (WELLORD1.th25 (RelIncl_wellOrdering hA) X)

/-- `WELLORD2:9` (`Th9`) -/
theorem th9 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B) (hAB : A ∈ B) :
    A = WELLORD1.seg (RelIncl B) A := by
  apply TARSKI.extensionality
  intro a
  constructor
  · intro ha
    have haOrd : ORDINAL1.isOrdinal a := ORDINAL1.th13 hA ha
    have hAsub : A ⊆ B := hB.1 A hAB
    have hasub : a ⊆ A := hA.1 a ha
    have hane : a ≠ A := fun heq =>
      ORDINAL1.not_mem_self A (Eq.subst (motive := fun s => s ∈ A) heq ha)
    exact (WELLORD1.th1 (RelIncl B) A a).mpr
      ⟨hane, (RelIncl_char B a A).mpr ⟨hAsub a ha, hAB, hasub⟩⟩
  · intro ha
    have ⟨hane, hp⟩ := (WELLORD1.th1 (RelIncl B) A a).mp ha
    have haB : a ∈ B := ((RelIncl_char B a A).mp hp).1
    have haOrd : ORDINAL1.isOrdinal a := ORDINAL1.th13 hB haB
    have hasub : a ⊆ A := ((RelIncl_char B a A).mp hp).2.2
    exact ORDINAL1.th11 haOrd.1 hA ⟨hasub, hane⟩

/-- `WELLORD2:10` (`Th10`) -/
theorem th10 {A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B)
    (hiso : WELLORD1.areIsomorphic (RelIncl A) (RelIncl B)) : A = B := by
  have hfA : RELAT_1.field (RelIncl A) = A := RelIncl_field A
  have hfB : RELAT_1.field (RelIncl B) = B := RelIncl_field B
  have hnAB : ¬ A ∈ B := by
    intro hAB
    have hseg : A = WELLORD1.seg (RelIncl B) A := th9 hA hB hAB
    have hsegsub : WELLORD1.seg (RelIncl B) A ⊆ B :=
      fun x hx =>
        Eq.subst (motive := fun s => x ∈ s) hfB
          (WELLORD1.th9 (RelIncl B) A x hx)
    have heq : RelIncl A = WELLORD1.restrict2 (RelIncl B)
        (WELLORD1.seg (RelIncl B) A) := by
      have h1 : WELLORD1.restrict2 (RelIncl B)
          (WELLORD1.seg (RelIncl B) A) =
          RelIncl (WELLORD1.seg (RelIncl B) A) := th7 hsegsub
      exact Eq.subst (motive := fun s => RelIncl s =
          WELLORD1.restrict2 (RelIncl B) (WELLORD1.seg (RelIncl B) A))
        hseg.symm h1.symm
    have hiso' : WELLORD1.areIsomorphic (RelIncl B)
        (WELLORD1.restrict2 (RelIncl B) (WELLORD1.seg (RelIncl B) A)) :=
      Eq.subst (motive := fun s => WELLORD1.areIsomorphic (RelIncl B) s)
        heq (WELLORD1.th40 hiso)
    have hAfield : A ∈ RELAT_1.field (RelIncl B) :=
      Eq.subst (motive := fun s => A ∈ s) hfB.symm hAB
    exact WELLORD1.th46 (RelIncl_wellOrdering hB) hAfield hiso'
  apply Classical.byContradiction
  intro hne
  have htri : A ∈ B ∨ A = B ∨ B ∈ A := ORDINAL1.th14 hA hB
  have hBA : B ∈ A :=
    htri.elim (fun hAB => (hnAB hAB).elim)
      (fun h => h.elim (fun heq => (hne heq).elim) id)
  have hseg : B = WELLORD1.seg (RelIncl A) B := th9 hB hA hBA
  have hsegsub : WELLORD1.seg (RelIncl A) B ⊆ A :=
    fun x hx =>
      Eq.subst (motive := fun s => x ∈ s) hfA
        (WELLORD1.th9 (RelIncl A) B x hx)
  have heq : RelIncl B = WELLORD1.restrict2 (RelIncl A)
      (WELLORD1.seg (RelIncl A) B) := by
    have h1 : WELLORD1.restrict2 (RelIncl A)
        (WELLORD1.seg (RelIncl A) B) =
        RelIncl (WELLORD1.seg (RelIncl A) B) := th7 hsegsub
    exact Eq.subst (motive := fun s => RelIncl s =
        WELLORD1.restrict2 (RelIncl A) (WELLORD1.seg (RelIncl A) B))
      hseg.symm h1.symm
  have hiso' : WELLORD1.areIsomorphic (RelIncl A)
      (WELLORD1.restrict2 (RelIncl A) (WELLORD1.seg (RelIncl A) B)) :=
    Eq.subst (motive := fun s => WELLORD1.areIsomorphic (RelIncl A) s)
      heq hiso
  have hBfield : B ∈ RELAT_1.field (RelIncl A) :=
    Eq.subst (motive := fun s => B ∈ s) hfA.symm hBA
  exact WELLORD1.th46 (RelIncl_wellOrdering hA) hBfield hiso'

/-- `WELLORD2:11` (`Th11`) -/
theorem th11 {R A B : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hB : ORDINAL1.isOrdinal B)
    (hRA : WELLORD1.areIsomorphic R (RelIncl A))
    (hRB : WELLORD1.areIsomorphic R (RelIncl B)) : A = B :=
  th10 hA hB (WELLORD1.th42 (WELLORD1.th40 hRA) hRB)

/-- `WELLORD2:12` (`Th12`) -/
theorem th12 {R : TarskiSet.{u}} (hR : WELLORD1.isWellOrdering R)
    (hseg : ∀ a, a ∈ RELAT_1.field R →
      ∃ A, ORDINAL1.isOrdinal A ∧
        WELLORD1.areIsomorphic
          (WELLORD1.restrict2 R (WELLORD1.seg R a)) (RelIncl A)) :
    ∃ A, ORDINAL1.isOrdinal A ∧
      WELLORD1.areIsomorphic R (RelIncl A) := by
  have hex : ∀ a, a ∈ RELAT_1.field R →
      ∃ b, ORDINAL1.isOrdinal b ∧
        WELLORD1.areIsomorphic
          (WELLORD1.restrict2 R (WELLORD1.seg R a)) (RelIncl b) :=
    hseg
  have hfun : ∀ a y1 y2, a ∈ RELAT_1.field R →
      (ORDINAL1.isOrdinal y1 ∧
        WELLORD1.areIsomorphic
          (WELLORD1.restrict2 R (WELLORD1.seg R a)) (RelIncl y1)) →
      (ORDINAL1.isOrdinal y2 ∧
        WELLORD1.areIsomorphic
          (WELLORD1.restrict2 R (WELLORD1.seg R a)) (RelIncl y2)) →
      y1 = y2 :=
    fun _ _ _ _ ⟨h1, i1⟩ ⟨h2, i2⟩ => th11 h1 h2 i1 i2
  obtain ⟨H, hH, hdH, hvH⟩ :=
    FUNCT_1.sch_FuncEx (RELAT_1.field R)
      (fun a b => ORDINAL1.isOrdinal b ∧
        WELLORD1.areIsomorphic
          (WELLORD1.restrict2 R (WELLORD1.seg R a)) (RelIncl b))
      hfun hex
  have hrngOrd : ∀ a, a ∈ RELAT_1.rng H → ORDINAL1.isOrdinal a := by
    intro b hb
    obtain ⟨c, hc, heq⟩ := (FUNCT_1.def3 hH.2).mp hb
    have hcF : c ∈ RELAT_1.field R :=
      Eq.subst (motive := fun s => c ∈ s) hdH hc
    exact Eq.subst (motive := ORDINAL1.isOrdinal) heq.symm (hvH c hcF).1
  obtain ⟨C, hC, hCsub⟩ := ORDINAL1.th24 hrngOrd
  have hfC : RELAT_1.field (RelIncl C) = C := RelIncl_field C
  have hcl : ∀ a, a ∈ RELAT_1.rng H → ∀ c,
      TARSKI.pair c a ∈ RelIncl C → c ∈ RELAT_1.rng H := by
    intro b hb c hp
    have ⟨cC, bC, hsub⟩ := (RelIncl_char C c b).mp hp
    obtain ⟨b9, hb9d, hbeq⟩ := (FUNCT_1.def3 hH.2).mp hb
    have hb9 : b9 ∈ RELAT_1.field R :=
      Eq.subst (motive := fun s => b9 ∈ s) hdH hb9d
    have ⟨hAord, hAiso⟩ := hvH b9 hb9
    have hAeq : FUNCT_1.apply H b9 = b := hbeq.symm
    have hBord : ORDINAL1.isOrdinal b :=
      Eq.subst (motive := ORDINAL1.isOrdinal) hAeq hAord
    have hcOrd : ORDINAL1.isOrdinal c := ORDINAL1.th13 hC cC
    exact Or.elim (Classical.em (c = b))
      (fun heq => Eq.subst (motive := fun s => s ∈ RELAT_1.rng H) heq.symm hb)
      (fun hne => by
        have hss : c ⊂ b := ⟨hsub, hne⟩
        have hcin : c ∈ b := ORDINAL1.th11 hcOrd.1 hBord hss
        have hBseg : c = WELLORD1.seg (RelIncl b) c :=
          th9 hcOrd hBord hcin
        have hcrestr : WELLORD1.restrict2 (RelIncl b) c = RelIncl c :=
          th7 (hBord.1 c hcin)
        have hP : WELLORD1.restrict2 R (WELLORD1.seg R b9) =
            WELLORD1.restrict2 R (WELLORD1.seg R b9) := rfl
        have hPwo : WELLORD1.isWellOrdering
            (WELLORD1.restrict2 R (WELLORD1.seg R b9)) :=
          WELLORD1.th25 hR (WELLORD1.seg R b9)
        have hisoBA : WELLORD1.areIsomorphic (RelIncl b)
            (WELLORD1.restrict2 R (WELLORD1.seg R b9)) :=
          WELLORD1.th40
            (Eq.subst (motive := fun s => WELLORD1.areIsomorphic
                (WELLORD1.restrict2 R (WELLORD1.seg R b9)) (RelIncl s))
              hAeq hAiso)
        have hcan := WELLORD1.def9 (RelIncl_wellOrdering hBord) hisoBA
        have hcinA : c ∈ RELAT_1.field (RelIncl b) :=
          Eq.subst (motive := fun s => c ∈ s) (RelIncl_field b).symm hcin
        obtain ⟨d, hdP, hisoSeg⟩ :=
          WELLORD1.th50 (RelIncl_wellOrdering hBord) hcan hcinA
        have hdR : d ∈ RELAT_1.field R := (WELLORD1.th12 hdP).1
        have hdV : d ∈ WELLORD1.seg R b9 := (WELLORD1.th12 hdP).2
        have hdpair : TARSKI.pair d b9 ∈ R :=
          ((WELLORD1.th1 R b9 d).mp hdV).2
        have hsegsub : WELLORD1.seg R d ⊆ WELLORD1.seg R b9 :=
          (WELLORD1.th29 hR hdR hb9).mp hdpair
        have hPseg : WELLORD1.seg
            (WELLORD1.restrict2 R (WELLORD1.seg R b9)) d =
            WELLORD1.seg R d :=
          WELLORD1.th27 hR hdV
        have hrest : WELLORD1.restrict2
            (WELLORD1.restrict2 R (WELLORD1.seg R b9))
            (WELLORD1.seg R d) =
            WELLORD1.restrict2 R (WELLORD1.seg R d) :=
          WELLORD1.th22 hsegsub (R := R)
        have hisoC : WELLORD1.areIsomorphic (RelIncl c)
            (WELLORD1.restrict2 R (WELLORD1.seg R d)) := by
          have h1 : WELLORD1.restrict2 (RelIncl b) c = RelIncl c :=
            hcrestr
          have h2 : c = WELLORD1.seg (RelIncl b) c := hBseg
          have hL : WELLORD1.restrict2 (RelIncl b)
              (WELLORD1.seg (RelIncl b) c) = RelIncl c :=
            Eq.subst (motive := fun s =>
                WELLORD1.restrict2 (RelIncl b) s = RelIncl c)
              h2 h1
          have hR' : WELLORD1.restrict2
              (WELLORD1.restrict2 R (WELLORD1.seg R b9))
              (WELLORD1.seg
                (WELLORD1.restrict2 R (WELLORD1.seg R b9)) d) =
              WELLORD1.restrict2 R (WELLORD1.seg R d) :=
            Eq.subst (motive := fun s =>
                WELLORD1.restrict2
                  (WELLORD1.restrict2 R (WELLORD1.seg R b9)) s =
                  WELLORD1.restrict2 R (WELLORD1.seg R d))
              hPseg.symm hrest
          exact Eq.subst (motive := fun s =>
              WELLORD1.areIsomorphic s
                (WELLORD1.restrict2 R (WELLORD1.seg R d)))
            hL
            (Eq.subst (motive := fun s =>
                WELLORD1.areIsomorphic
                  (WELLORD1.restrict2 (RelIncl b)
                    (WELLORD1.seg (RelIncl b) c)) s)
              hR' hisoSeg)
        have hisoD : WELLORD1.areIsomorphic
            (WELLORD1.restrict2 R (WELLORD1.seg R d)) (RelIncl c) :=
          WELLORD1.th40 hisoC
        have hcH : FUNCT_1.apply H d = c :=
          (hfun d (FUNCT_1.apply H d) c hdR (hvH d hdR)
            ⟨hcOrd, hisoD⟩)
        have hdHmem : d ∈ RELAT_1.dom H :=
          Eq.subst (motive := fun s => d ∈ s) hdH.symm hdR
        exact (FUNCT_1.def3 hH.2).mpr ⟨d, hdHmem, hcH.symm⟩)
  have hYsub : RELAT_1.rng H ⊆ RELAT_1.field (RelIncl C) :=
    fun x hx =>
      Eq.subst (motive := fun s => x ∈ s) hfC.symm (hCsub x hx)
  have h28 :=
    (WELLORD1.th28 (RelIncl_wellOrdering hC) hYsub).mpr
      fun a ha c hca => hcl a ha c hca
  have hAord : ORDINAL1.isOrdinal (RELAT_1.rng H) :=
    Or.elim h28
      (fun heq =>
        Eq.subst (motive := ORDINAL1.isOrdinal) heq.symm
          (Eq.subst (motive := ORDINAL1.isOrdinal) hfC.symm hC))
      (fun ⟨a, ha, hsegY⟩ =>
        let haC : a ∈ C :=
          Eq.subst (motive := fun s => a ∈ s) hfC ha
        let haOrd : ORDINAL1.isOrdinal a := ORDINAL1.th13 hC haC
        let hseq : a = WELLORD1.seg (RelIncl C) a :=
          th9 haOrd hC haC
        Eq.subst (motive := ORDINAL1.isOrdinal) hsegY.symm
          (Eq.subst (motive := ORDINAL1.isOrdinal) hseq haOrd))
  refine ⟨RELAT_1.rng H, hAord, ⟨H, ?_⟩⟩
  have hfA : RELAT_1.field (RelIncl (RELAT_1.rng H)) = RELAT_1.rng H :=
    RelIncl_field (RELAT_1.rng H)
  have h1 : FUNCT_1.isOneToOne H := by
    intro a b ha hb heq
    have haF : a ∈ RELAT_1.field R :=
      Eq.subst (motive := fun s => a ∈ s) hdH ha
    have hbF : b ∈ RELAT_1.field R :=
      Eq.subst (motive := fun s => b ∈ s) hdH hb
    apply Classical.byContradiction
    intro hne
    have ⟨hAord', hAiso⟩ := hvH a haF
    have ⟨hBord, hBiso⟩ := hvH b hbF
    have hBeq : FUNCT_1.apply H a = FUNCT_1.apply H b := heq
    have hisoAB : WELLORD1.areIsomorphic
        (WELLORD1.restrict2 R (WELLORD1.seg R a))
        (WELLORD1.restrict2 R (WELLORD1.seg R b)) :=
      WELLORD1.th42 hAiso
        (WELLORD1.th40
          (Eq.subst (motive := fun s => WELLORD1.areIsomorphic
              (WELLORD1.restrict2 R (WELLORD1.seg R b)) (RelIncl s))
            hBeq.symm hBiso))
    exact WELLORD1.th47 hR haF hbF hne hisoAB
  refine ⟨hH, hdH, hfA.symm, h1, ?pairs⟩
  intro a b
  constructor
  · intro hab
    have haF : a ∈ RELAT_1.field R := (RELAT_1.th15 hab).1
    have hbF : b ∈ RELAT_1.field R := (RELAT_1.th15 hab).2
    have haD : a ∈ RELAT_1.dom H :=
      Eq.subst (motive := fun s => a ∈ s) hdH.symm haF
    have hbD : b ∈ RELAT_1.dom H :=
      Eq.subst (motive := fun s => b ∈ s) hdH.symm hbF
    have hAin : FUNCT_1.apply H a ∈ RELAT_1.rng H :=
      FUNCT_1.th3 hH.2 haD
    have hBin : FUNCT_1.apply H b ∈ RELAT_1.rng H :=
      FUNCT_1.th3 hH.2 hbD
    have ⟨hAord', hAiso⟩ := hvH a haF
    have ⟨hBord, hBiso⟩ := hvH b hbF
    refine ⟨haF, hbF, ?_⟩
    exact Or.elim (Classical.em (a = b))
      (fun heq =>
        (RelIncl_char (RELAT_1.rng H)
            (FUNCT_1.apply H a) (FUNCT_1.apply H b)).mpr
          ⟨hAin,
            Eq.subst (motive := fun s => FUNCT_1.apply H s ∈ RELAT_1.rng H)
              heq hAin,
            Eq.subst (motive := fun s =>
                FUNCT_1.apply H a ⊆ FUNCT_1.apply H s) heq
              (fun _ hx => hx)⟩)
      (fun hne => by
        have haZ : a ∈ WELLORD1.seg R b :=
          (WELLORD1.th1 R b a).mpr ⟨hne, hab⟩
        have hPwo : WELLORD1.isWellOrdering
            (WELLORD1.restrict2 R (WELLORD1.seg R b)) :=
          WELLORD1.th25 hR (WELLORD1.seg R b)
        have hPseg : WELLORD1.seg
            (WELLORD1.restrict2 R (WELLORD1.seg R b)) a =
            WELLORD1.seg R a :=
          WELLORD1.th27 hR haZ
        have hsegsub : WELLORD1.seg R a ⊆ WELLORD1.seg R b :=
          (WELLORD1.th29 hR haF hbF).mp hab
        have haP : a ∈ RELAT_1.field
            (WELLORD1.restrict2 R (WELLORD1.seg R b)) :=
          Eq.subst (motive := fun s => a ∈ s)
            (WELLORD1.th32 hR b).symm haZ
        have hA9sub : FUNCT_1.apply H a ⊆ RELAT_1.rng H :=
          hAord.1 (FUNCT_1.apply H a) hAin
        have hrestrA : WELLORD1.restrict2
            (RelIncl (RELAT_1.rng H)) (FUNCT_1.apply H a) =
            RelIncl (FUNCT_1.apply H a) :=
          th7 hA9sub
        have hA9in : FUNCT_1.apply H a ∈ RELAT_1.rng H := hAin
        have hA9seg : FUNCT_1.apply H a =
            WELLORD1.seg (RelIncl (RELAT_1.rng H)) (FUNCT_1.apply H a) :=
          th9 hAord' hAord hA9in
        have hB9seg : FUNCT_1.apply H b =
            WELLORD1.seg (RelIncl (RELAT_1.rng H)) (FUNCT_1.apply H b) :=
          th9 hBord hAord hBin
        have hrestrB : WELLORD1.restrict2
            (RelIncl (RELAT_1.rng H)) (FUNCT_1.apply H b) =
            RelIncl (FUNCT_1.apply H b) :=
          th7 (hAord.1 (FUNCT_1.apply H b) hBin)
        have hrestP : WELLORD1.restrict2
            (WELLORD1.restrict2 R (WELLORD1.seg R b))
            (WELLORD1.seg R a) =
            WELLORD1.restrict2 R (WELLORD1.seg R a) :=
          WELLORD1.th22 hsegsub (R := R)
        have hisoPseg : WELLORD1.areIsomorphic
            (WELLORD1.restrict2
              (WELLORD1.restrict2 R (WELLORD1.seg R b))
              (WELLORD1.seg
                (WELLORD1.restrict2 R (WELLORD1.seg R b)) a))
            (WELLORD1.restrict2 (RelIncl (RELAT_1.rng H))
              (WELLORD1.seg (RelIncl (RELAT_1.rng H))
                (FUNCT_1.apply H a))) := by
          have hL : WELLORD1.restrict2
              (WELLORD1.restrict2 R (WELLORD1.seg R b))
              (WELLORD1.seg
                (WELLORD1.restrict2 R (WELLORD1.seg R b)) a) =
              WELLORD1.restrict2 R (WELLORD1.seg R a) :=
            Eq.subst (motive := fun s =>
                WELLORD1.restrict2
                  (WELLORD1.restrict2 R (WELLORD1.seg R b)) s =
                  WELLORD1.restrict2 R (WELLORD1.seg R a))
              hPseg.symm hrestP
          have hR' : WELLORD1.restrict2 (RelIncl (RELAT_1.rng H))
              (WELLORD1.seg (RelIncl (RELAT_1.rng H))
                (FUNCT_1.apply H a)) =
              RelIncl (FUNCT_1.apply H a) :=
            Eq.subst (motive := fun s =>
                WELLORD1.restrict2 (RelIncl (RELAT_1.rng H)) s =
                  RelIncl (FUNCT_1.apply H a))
              hA9seg hrestrA
          exact Eq.subst (motive := fun s =>
              WELLORD1.areIsomorphic s
                (WELLORD1.restrict2 (RelIncl (RELAT_1.rng H))
                  (WELLORD1.seg (RelIncl (RELAT_1.rng H))
                    (FUNCT_1.apply H a))))
            hL.symm
            (Eq.subst (motive := fun s =>
                WELLORD1.areIsomorphic
                  (WELLORD1.restrict2 R (WELLORD1.seg R a)) s)
              hR'.symm hAiso)
        have hisoP : WELLORD1.areIsomorphic
            (WELLORD1.restrict2 R (WELLORD1.seg R b))
            (WELLORD1.restrict2 (RelIncl (RELAT_1.rng H))
              (WELLORD1.seg (RelIncl (RELAT_1.rng H))
                (FUNCT_1.apply H b))) := by
          have hR' : WELLORD1.restrict2 (RelIncl (RELAT_1.rng H))
              (WELLORD1.seg (RelIncl (RELAT_1.rng H))
                (FUNCT_1.apply H b)) =
              RelIncl (FUNCT_1.apply H b) :=
            Eq.subst (motive := fun s =>
                WELLORD1.restrict2 (RelIncl (RELAT_1.rng H)) s =
                  RelIncl (FUNCT_1.apply H b))
              hB9seg hrestrB
          exact Eq.subst (motive := fun s =>
              WELLORD1.areIsomorphic
                (WELLORD1.restrict2 R (WELLORD1.seg R b)) s)
            hR'.symm hBiso
        have hA9F : FUNCT_1.apply H a ∈
            RELAT_1.field (RelIncl (RELAT_1.rng H)) :=
          Eq.subst (motive := fun s => FUNCT_1.apply H a ∈ s) hfA.symm hAin
        have hB9F : FUNCT_1.apply H b ∈
            RELAT_1.field (RelIncl (RELAT_1.rng H)) :=
          Eq.subst (motive := fun s => FUNCT_1.apply H b ∈ s) hfA.symm hBin
        exact (WELLORD1.th51 hPwo (RelIncl_wellOrdering hAord)
          haP hB9F hA9F hisoP hisoPseg).2)
  · intro ⟨haF, hbF, hpH⟩
    apply Classical.byContradiction
    intro hnab
    have hrefl : RELAT_2.isReflexiveIn R (RELAT_1.field R) :=
      (RELAT_2.def9 R).mp hR.1
    have hne : a ≠ b := fun heq =>
      hnab (Eq.subst (motive := fun s => TARSKI.pair a s ∈ R) heq
        (hrefl a haF))
    have hconn : RELAT_2.isConnectedIn R (RELAT_1.field R) :=
      (RELAT_2.def14 R).mp hR.2.2.2.1
    have hba : TARSKI.pair b a ∈ R :=
      Or.elim (hconn a b haF hbF hne)
        (fun hab => (hnab hab).elim) (fun hba => hba)
    have hbZ : b ∈ WELLORD1.seg R a :=
      (WELLORD1.th1 R a b).mpr ⟨fun heq => hne heq.symm, hba⟩
    have hPwo : WELLORD1.isWellOrdering
        (WELLORD1.restrict2 R (WELLORD1.seg R a)) :=
      WELLORD1.th25 hR (WELLORD1.seg R a)
    have ⟨hAord', hAiso⟩ := hvH a haF
    have ⟨hBord, hBiso⟩ := hvH b hbF
    have haD : a ∈ RELAT_1.dom H :=
      Eq.subst (motive := fun s => a ∈ s) hdH.symm haF
    have hbD : b ∈ RELAT_1.dom H :=
      Eq.subst (motive := fun s => b ∈ s) hdH.symm hbF
    have hAin : FUNCT_1.apply H a ∈ RELAT_1.rng H :=
      FUNCT_1.th3 hH.2 haD
    have hBin : FUNCT_1.apply H b ∈ RELAT_1.rng H :=
      FUNCT_1.th3 hH.2 hbD
    have hPseg : WELLORD1.seg
        (WELLORD1.restrict2 R (WELLORD1.seg R a)) b =
        WELLORD1.seg R b :=
      WELLORD1.th27 hR hbZ
    have hsegsub : WELLORD1.seg R b ⊆ WELLORD1.seg R a :=
      (WELLORD1.th29 hR hbF haF).mp hba
    have hbP : b ∈ RELAT_1.field
        (WELLORD1.restrict2 R (WELLORD1.seg R a)) :=
      Eq.subst (motive := fun s => b ∈ s)
        (WELLORD1.th32 hR a).symm hbZ
    have hA9seg : FUNCT_1.apply H a =
        WELLORD1.seg (RelIncl (RELAT_1.rng H)) (FUNCT_1.apply H a) :=
      th9 hAord' hAord hAin
    have hB9seg : FUNCT_1.apply H b =
        WELLORD1.seg (RelIncl (RELAT_1.rng H)) (FUNCT_1.apply H b) :=
      th9 hBord hAord hBin
    have hrestrA : WELLORD1.restrict2
        (RelIncl (RELAT_1.rng H)) (FUNCT_1.apply H a) =
        RelIncl (FUNCT_1.apply H a) :=
      th7 (hAord.1 (FUNCT_1.apply H a) hAin)
    have hrestrB : WELLORD1.restrict2
        (RelIncl (RELAT_1.rng H)) (FUNCT_1.apply H b) =
        RelIncl (FUNCT_1.apply H b) :=
      th7 (hAord.1 (FUNCT_1.apply H b) hBin)
    have hrestP : WELLORD1.restrict2
        (WELLORD1.restrict2 R (WELLORD1.seg R a))
        (WELLORD1.seg R b) =
        WELLORD1.restrict2 R (WELLORD1.seg R b) :=
      WELLORD1.th22 hsegsub (R := R)
    have hisoP : WELLORD1.areIsomorphic
        (WELLORD1.restrict2 R (WELLORD1.seg R a))
        (WELLORD1.restrict2 (RelIncl (RELAT_1.rng H))
          (WELLORD1.seg (RelIncl (RELAT_1.rng H))
            (FUNCT_1.apply H a))) := by
      have hR' : WELLORD1.restrict2 (RelIncl (RELAT_1.rng H))
          (WELLORD1.seg (RelIncl (RELAT_1.rng H))
            (FUNCT_1.apply H a)) =
          RelIncl (FUNCT_1.apply H a) :=
        Eq.subst (motive := fun s =>
            WELLORD1.restrict2 (RelIncl (RELAT_1.rng H)) s =
              RelIncl (FUNCT_1.apply H a))
          hA9seg hrestrA
      exact Eq.subst (motive := fun s =>
          WELLORD1.areIsomorphic
            (WELLORD1.restrict2 R (WELLORD1.seg R a)) s)
        hR'.symm hAiso
    have hisoPseg : WELLORD1.areIsomorphic
        (WELLORD1.restrict2
          (WELLORD1.restrict2 R (WELLORD1.seg R a))
          (WELLORD1.seg
            (WELLORD1.restrict2 R (WELLORD1.seg R a)) b))
        (WELLORD1.restrict2 (RelIncl (RELAT_1.rng H))
          (WELLORD1.seg (RelIncl (RELAT_1.rng H))
            (FUNCT_1.apply H b))) := by
      have hL : WELLORD1.restrict2
          (WELLORD1.restrict2 R (WELLORD1.seg R a))
          (WELLORD1.seg
            (WELLORD1.restrict2 R (WELLORD1.seg R a)) b) =
          WELLORD1.restrict2 R (WELLORD1.seg R b) :=
        Eq.subst (motive := fun s =>
            WELLORD1.restrict2
              (WELLORD1.restrict2 R (WELLORD1.seg R a)) s =
              WELLORD1.restrict2 R (WELLORD1.seg R b))
          hPseg.symm hrestP
      have hR' : WELLORD1.restrict2 (RelIncl (RELAT_1.rng H))
          (WELLORD1.seg (RelIncl (RELAT_1.rng H))
            (FUNCT_1.apply H b)) =
          RelIncl (FUNCT_1.apply H b) :=
        Eq.subst (motive := fun s =>
            WELLORD1.restrict2 (RelIncl (RELAT_1.rng H)) s =
              RelIncl (FUNCT_1.apply H b))
          hB9seg hrestrB
      exact Eq.subst (motive := fun s =>
          WELLORD1.areIsomorphic s
            (WELLORD1.restrict2 (RelIncl (RELAT_1.rng H))
              (WELLORD1.seg (RelIncl (RELAT_1.rng H))
                (FUNCT_1.apply H b))))
        hL.symm
        (Eq.subst (motive := fun s =>
            WELLORD1.areIsomorphic
              (WELLORD1.restrict2 R (WELLORD1.seg R b)) s)
          hR'.symm hBiso)
    have hA9F : FUNCT_1.apply H a ∈
        RELAT_1.field (RelIncl (RELAT_1.rng H)) :=
      Eq.subst (motive := fun s => FUNCT_1.apply H a ∈ s) hfA.symm hAin
    have hB9F : FUNCT_1.apply H b ∈
        RELAT_1.field (RelIncl (RELAT_1.rng H)) :=
      Eq.subst (motive := fun s => FUNCT_1.apply H b ∈ s) hfA.symm hBin
    have hpBA : TARSKI.pair (FUNCT_1.apply H b) (FUNCT_1.apply H a) ∈
        RelIncl (RELAT_1.rng H) :=
      (WELLORD1.th51 hPwo (RelIncl_wellOrdering hAord)
        hbP hA9F hB9F hisoP hisoPseg).2
    have hanti : RELAT_2.isAntisymmetricIn
        (RelIncl (RELAT_1.rng H))
        (RELAT_1.field (RelIncl (RELAT_1.rng H))) :=
      (RELAT_2.def12 (RelIncl (RELAT_1.rng H))).mp
        (RelIncl_antisymmetric (RELAT_1.rng H))
    have heqH : FUNCT_1.apply H a = FUNCT_1.apply H b :=
      hanti (FUNCT_1.apply H a) (FUNCT_1.apply H b) hA9F hB9F hpH hpBA
    exact hne (h1 a b haD hbD heqH)

/-- `WELLORD2:13` (`Th13`) -/
theorem th13 {R : TarskiSet.{u}} (hR : WELLORD1.isWellOrdering R) :
    ∃ A, ORDINAL1.isOrdinal A ∧
      WELLORD1.areIsomorphic R (RelIncl A) := by
  obtain ⟨Z, hZ⟩ :=
    XBOOLE_0.sch_separation (RELAT_1.field R)
      (fun a => ∃ A, ORDINAL1.isOrdinal A ∧
        WELLORD1.areIsomorphic
          (WELLORD1.restrict2 R (WELLORD1.seg R a)) (RelIncl A))
  have hclosed : ∀ a, a ∈ RELAT_1.field R →
      WELLORD1.seg R a ⊆ Z → a ∈ Z := by
    intro a ha hsegZ
    have hPwo : WELLORD1.isWellOrdering
        (WELLORD1.restrict2 R (WELLORD1.seg R a)) :=
      WELLORD1.th25 hR (WELLORD1.seg R a)
    have hPseg : ∀ b, b ∈ RELAT_1.field
        (WELLORD1.restrict2 R (WELLORD1.seg R a)) →
        ∃ A, ORDINAL1.isOrdinal A ∧
          WELLORD1.areIsomorphic
            (WELLORD1.restrict2
              (WELLORD1.restrict2 R (WELLORD1.seg R a))
              (WELLORD1.seg
                (WELLORD1.restrict2 R (WELLORD1.seg R a)) b))
            (RelIncl A) := by
      intro b hb
      have hbV : b ∈ WELLORD1.seg R a := (WELLORD1.th12 hb).2
      have hbR : b ∈ RELAT_1.field R := (WELLORD1.th12 hb).1
      have hpair : TARSKI.pair b a ∈ R :=
        ((WELLORD1.th1 R a b).mp hbV).2
      have hsub : WELLORD1.seg R b ⊆ WELLORD1.seg R a :=
        (WELLORD1.th29 hR hbR ha).mp hpair
      have hbZ : b ∈ Z := hsegZ b hbV
      obtain ⟨_, ⟨A, hA, hiso⟩⟩ := (hZ b).mp hbZ
      have hPeq : WELLORD1.seg
          (WELLORD1.restrict2 R (WELLORD1.seg R a)) b =
          WELLORD1.seg R b :=
        WELLORD1.th27 hR hbV
      have hrest : WELLORD1.restrict2
          (WELLORD1.restrict2 R (WELLORD1.seg R a))
          (WELLORD1.seg R b) =
          WELLORD1.restrict2 R (WELLORD1.seg R b) :=
        WELLORD1.th22 hsub (R := R)
      refine ⟨A, hA, ?_⟩
      exact Eq.subst (motive := fun s =>
          WELLORD1.areIsomorphic
            (WELLORD1.restrict2
              (WELLORD1.restrict2 R (WELLORD1.seg R a)) s)
            (RelIncl A))
        hPeq.symm
        (Eq.subst (motive := fun s =>
            WELLORD1.areIsomorphic s (RelIncl A)) hrest.symm hiso)
    obtain ⟨A, hA, hiso⟩ := th12 hPwo hPseg
    exact (hZ a).mpr ⟨ha, A, hA, hiso⟩
  have hsub : RELAT_1.field R ⊆ Z := WELLORD1.th33 hR hclosed
  exact th12 hR fun a ha =>
    let ⟨_, hP⟩ := (hZ a).mp (hsub a ha)
    hP

/-- `WELLORD2:def 2` — order type of a well-ordering. -/
noncomputable def order_type_of {R : TarskiSet.{u}}
    (hR : WELLORD1.isWellOrdering R) : TarskiSet.{u} :=
  Classical.choose (th13 hR)

theorem order_type_of_ordinal {R : TarskiSet.{u}}
    (hR : WELLORD1.isWellOrdering R) :
    ORDINAL1.isOrdinal (order_type_of hR) :=
  (Classical.choose_spec (th13 hR)).1

theorem def2 {R : TarskiSet.{u}} (hR : WELLORD1.isWellOrdering R) :
    WELLORD1.areIsomorphic R (RelIncl (order_type_of hR)) :=
  (Classical.choose_spec (th13 hR)).2

def is_order_type_of (A R : TarskiSet.{u})
    (hR : WELLORD1.isWellOrdering R) : Prop :=
  A = order_type_of hR

theorem order_type_unique {R A : TarskiSet.{u}}
    (hR : WELLORD1.isWellOrdering R) (hA : ORDINAL1.isOrdinal A)
    (hiso : WELLORD1.areIsomorphic R (RelIncl A)) :
    order_type_of hR = A :=
  th11 (order_type_of_ordinal hR) hA (def2 hR) hiso

/-- Unlabeled `WELLORD2` after `Def2` (`L561`). -/
theorem th14 {A X : TarskiSet.{u}} (hA : ORDINAL1.isOrdinal A)
    (hX : X ⊆ A) :
    order_type_of (th8 hA hX) ⊆ A := by
  have hwoX : WELLORD1.isWellOrdering (RelIncl X) := th8 hA hX
  have heq : WELLORD1.restrict2 (RelIncl A) X = RelIncl X := th7 hX
  have hfA : RELAT_1.field (RelIncl A) = A := RelIncl_field A
  have hXfield : X ⊆ RELAT_1.field (RelIncl A) :=
    fun y hy => Eq.subst (motive := fun s => y ∈ s) hfA.symm (hX y hy)
  have h53 := WELLORD1.th53 hXfield (RelIncl_wellOrdering hA)
  exact Or.elim h53
    (fun hiso =>
      let hiso' : WELLORD1.areIsomorphic (RelIncl X) (RelIncl A) :=
        WELLORD1.th40
          (Eq.subst (motive := fun s =>
              WELLORD1.areIsomorphic (RelIncl A) s) heq hiso)
      let heqot : order_type_of hwoX = A :=
        order_type_unique hwoX hA hiso'
      Eq.subst (motive := fun s => s ⊆ A) heqot.symm
        (fun _ hx => hx))
    (fun ⟨a, ha, hiso⟩ =>
      let haA : a ∈ A :=
        Eq.subst (motive := fun s => a ∈ s) hfA ha
      let haOrd : ORDINAL1.isOrdinal a := ORDINAL1.th13 hA haA
      let hseg : a = WELLORD1.seg (RelIncl A) a := th9 haOrd hA haA
      let hresta : WELLORD1.restrict2 (RelIncl A) a = RelIncl a :=
        th7 (hA.1 a haA)
      let hL : WELLORD1.restrict2 (RelIncl A)
          (WELLORD1.seg (RelIncl A) a) = RelIncl a :=
        Eq.subst (motive := fun s =>
            WELLORD1.restrict2 (RelIncl A) s = RelIncl a) hseg hresta
      let hiso1 : WELLORD1.areIsomorphic (RelIncl a)
          (WELLORD1.restrict2 (RelIncl A) X) :=
        Eq.subst (motive := fun s =>
            WELLORD1.areIsomorphic s (WELLORD1.restrict2 (RelIncl A) X))
          hL hiso
      let hiso2 : WELLORD1.areIsomorphic (RelIncl a) (RelIncl X) :=
        Eq.subst (motive := fun s =>
            WELLORD1.areIsomorphic (RelIncl a) s) heq hiso1
      let hiso' : WELLORD1.areIsomorphic (RelIncl X) (RelIncl a) :=
        WELLORD1.th40 hiso2
      let heqot : order_type_of hwoX = a :=
        order_type_unique hwoX haOrd hiso'
      Eq.subst (motive := fun s => s ⊆ A) heqot.symm (hA.1 a haA))

/-- Compatibility of the `are_equipotent` redefine (`WELLORD2` after `L591`). -/
theorem are_equipotent_fun (X Y : TarskiSet.{u}) :
    TARSKI.are_equipotent X Y ↔
      ∃ f, FUNCT_1.isFunction f ∧ FUNCT_1.isOneToOne f ∧
        RELAT_1.dom f = X ∧ RELAT_1.rng f = Y := by
  constructor
  · intro ⟨Z, hXY, hYX, hbij⟩
    let F := Z ∩ ZFMISC_1.product X Y
    have hFrel : RELAT_1.isRelation F :=
      RELAT_1.subset_isRelation (RELAT_1.product_isRelation X Y)
        (fun z hz =>
          ((XBOOLE_0.def4 Z (ZFMISC_1.product X Y) z).mp hz).2)
    have hFlike : FUNCT_1.isFunctionLike F := by
      intro x y1 y2 h1 h2
      have hp1 := (XBOOLE_0.def4 Z (ZFMISC_1.product X Y)
        (TARSKI.pair x y1)).mp h1
      have hp2 := (XBOOLE_0.def4 Z (ZFMISC_1.product X Y)
        (TARSKI.pair x y2)).mp h2
      exact (hbij x y1 x y2 hp1.1 hp2.1).mp rfl
    have hF : FUNCT_1.isFunction F := ⟨hFrel, hFlike⟩
    have h1 : FUNCT_1.isOneToOne F := by
      intro x y hx hy heq
      have hpx : TARSKI.pair x (FUNCT_1.apply F x) ∈ F :=
        (FUNCT_1.th1 hFlike (x := x) (y := FUNCT_1.apply F x)).mpr
          ⟨hx, rfl⟩
      have hpy : TARSKI.pair y (FUNCT_1.apply F y) ∈ F :=
        (FUNCT_1.th1 hFlike (x := y) (y := FUNCT_1.apply F y)).mpr
          ⟨hy, rfl⟩
      have hz1 := (XBOOLE_0.def4 Z (ZFMISC_1.product X Y)
        (TARSKI.pair x (FUNCT_1.apply F x))).mp hpx
      have hz2 := (XBOOLE_0.def4 Z (ZFMISC_1.product X Y)
        (TARSKI.pair y (FUNCT_1.apply F y))).mp hpy
      exact (hbij x (FUNCT_1.apply F x) y (FUNCT_1.apply F y)
        hz1.1 hz2.1).mpr heq
    have hdom : RELAT_1.dom F = X := by
      apply TARSKI.extensionality
      intro x
      constructor
      · intro hx
        obtain ⟨y, hp⟩ := (RELAT_1.dom_iff F x).mp hx
        have hpP := (XBOOLE_0.def4 Z (ZFMISC_1.product X Y)
          (TARSKI.pair x y)).mp hp
        exact ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp
          hpP.2).1
      · intro hx
        obtain ⟨y, hy, hpZ⟩ := hXY x hx
        have hpP : TARSKI.pair x y ∈ ZFMISC_1.product X Y :=
          (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mpr
            ⟨hx, hy⟩
        have hpF : TARSKI.pair x y ∈ F :=
          (XBOOLE_0.def4 Z (ZFMISC_1.product X Y)
            (TARSKI.pair x y)).mpr ⟨hpZ, hpP⟩
        exact (RELAT_1.dom_iff F x).mpr ⟨y, hpF⟩
    have hrng : RELAT_1.rng F = Y := by
      apply TARSKI.extensionality
      intro y
      constructor
      · intro hy
        obtain ⟨x, hx, heq⟩ := (FUNCT_1.def3 hFlike).mp hy
        have hp : TARSKI.pair x y ∈ F :=
          (FUNCT_1.th1 hFlike (x := x) (y := y)).mpr ⟨hx, heq⟩
        have hpP := (XBOOLE_0.def4 Z (ZFMISC_1.product X Y)
          (TARSKI.pair x y)).mp hp
        exact ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp
          hpP.2).2
      · intro hy
        obtain ⟨x, hx, hpZ⟩ := hYX y hy
        have hpP : TARSKI.pair x y ∈ ZFMISC_1.product X Y :=
          (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mpr
            ⟨hx, hy⟩
        have hpF : TARSKI.pair x y ∈ F :=
          (XBOOLE_0.def4 Z (ZFMISC_1.product X Y)
            (TARSKI.pair x y)).mpr ⟨hpZ, hpP⟩
        have hxD : x ∈ RELAT_1.dom F :=
          (RELAT_1.dom_iff F x).mpr ⟨y, hpF⟩
        have heq : y = FUNCT_1.apply F x :=
          ((FUNCT_1.th1 hFlike (x := x) (y := y)).mp hpF).2
        exact (FUNCT_1.def3 hFlike).mpr ⟨x, hxD, heq⟩
    exact ⟨F, hF, h1, hdom, hrng⟩
  · intro ⟨f, hf, h1, hd, hr⟩
    refine ⟨f, ?fwd, ?bwd, ?bij⟩
    · intro x hx
      have hxD : x ∈ RELAT_1.dom f :=
        Eq.subst (motive := fun s => x ∈ s) hd.symm hx
      exact ⟨FUNCT_1.apply f x,
        Eq.subst (motive := fun s => FUNCT_1.apply f x ∈ s) hr
          (FUNCT_1.th3 hf.2 hxD),
        (FUNCT_1.th1 hf.2 (x := x) (y := FUNCT_1.apply f x)).mpr
          ⟨hxD, rfl⟩⟩
    · intro y hy
      have hyR : y ∈ RELAT_1.rng f :=
        Eq.subst (motive := fun s => y ∈ s) hr.symm hy
      have hyD : y ∈ RELAT_1.dom (FUNCT_1.inv f) :=
        Eq.subst (motive := fun s => y ∈ s) (FUNCT_1.th33 h1).1 hyR
      have hx : FUNCT_1.apply (FUNCT_1.inv f) y ∈ RELAT_1.rng (FUNCT_1.inv f) :=
        FUNCT_1.th3 (FUNCT_1.inv_isFunction hf h1).2 hyD
      have hxX : FUNCT_1.apply (FUNCT_1.inv f) y ∈ X :=
        Eq.subst (motive := fun s =>
            FUNCT_1.apply (FUNCT_1.inv f) y ∈ s)
          ((FUNCT_1.th33 h1).2.symm.trans hd) hx
      have hyeq : y = FUNCT_1.apply f (FUNCT_1.apply (FUNCT_1.inv f) y) :=
        (FUNCT_1.th35 hf h1 hyR).1.symm
      have hxin : FUNCT_1.apply (FUNCT_1.inv f) y ∈ RELAT_1.dom f :=
        Eq.subst (motive := fun s =>
            FUNCT_1.apply (FUNCT_1.inv f) y ∈ s)
          (FUNCT_1.th33 h1).2.symm hx
      exact ⟨FUNCT_1.apply (FUNCT_1.inv f) y, hxX,
        (FUNCT_1.th1 hf.2 (x := FUNCT_1.apply (FUNCT_1.inv f) y)
          (y := y)).mpr ⟨hxin, hyeq⟩⟩
    · intro x y z u hp1 hp2
      have hx := (FUNCT_1.th1 hf.2 (x := x) (y := y)).mp hp1
      have hz := (FUNCT_1.th1 hf.2 (x := z) (y := u)).mp hp2
      constructor
      · intro heq
        have happ : FUNCT_1.apply f z = u := hz.2.symm
        have happx : FUNCT_1.apply f x = u :=
          Eq.subst (motive := fun s => FUNCT_1.apply f s = u) heq.symm happ
        exact hx.2.trans happx
      · intro heq
        have happ : FUNCT_1.apply f x = FUNCT_1.apply f z :=
          hx.2.symm.trans (heq.trans hz.2)
        exact h1 x z hx.1 hz.1 happ

theorem are_equipotent_refl (X : TarskiSet.{u}) :
    TARSKI.are_equipotent X X :=
  (are_equipotent_fun X X).mpr
    ⟨RELAT_1.id X, FUNCT_1.id_isFunction X, FUNCT_1.id_isOneToOne X,
      RELAT_1.id_dom X, RELAT_1.id_rng X⟩

theorem are_equipotent_symm {X Y : TarskiSet.{u}}
    (h : TARSKI.are_equipotent X Y) : TARSKI.are_equipotent Y X := by
  obtain ⟨f, hf, h1, hd, hr⟩ := (are_equipotent_fun X Y).mp h
  exact (are_equipotent_fun Y X).mpr
    ⟨FUNCT_1.inv f, FUNCT_1.inv_isFunction hf h1, FUNCT_1.th40 hf h1,
      (FUNCT_1.th33 h1).1.symm.trans hr,
      (FUNCT_1.th33 h1).2.symm.trans hd⟩

/-- Unlabeled `WELLORD2` (`L730`). -/
theorem th15 {X Y Z : TarskiSet.{u}}
    (hXY : TARSKI.are_equipotent X Y) (hYZ : TARSKI.are_equipotent Y Z) :
    TARSKI.are_equipotent X Z := by
  obtain ⟨f, hf, h1f, hdf, hrf⟩ := (are_equipotent_fun X Y).mp hXY
  obtain ⟨g, hg, h1g, hdg, hrg⟩ := (are_equipotent_fun Y Z).mp hYZ
  have hsub : RELAT_1.rng f ⊆ RELAT_1.dom g :=
    fun y hy =>
      Eq.subst (motive := fun s => y ∈ s) hdg.symm
        (Eq.subst (motive := fun s => y ∈ s) hrf hy)
  have hsub2 : RELAT_1.dom g ⊆ RELAT_1.rng f :=
    fun y hy =>
      Eq.subst (motive := fun s => y ∈ s) hrf.symm
        (Eq.subst (motive := fun s => y ∈ s) hdg hy)
  exact (are_equipotent_fun X Z).mpr
    ⟨RELAT_1.comp f g, FUNCT_1.comp_isFunction hf hg,
      FUNCT_1.th24 hf.2 hg.2 h1f h1g,
      (RELAT_1.th27 (P := g) (R := f) hsub).trans hdf,
      (RELAT_1.th28 (P := g) (R := f) hsub2).trans hrg⟩

/-- `WELLORD2:16` (`Th16`) -/
theorem th16 {R X : TarskiSet.{u}} (h : WELLORD1.wellOrders R X) :
    RELAT_1.field (WELLORD1.restrict2 R X) = X ∧
      WELLORD1.isWellOrdering (WELLORD1.restrict2 R X) := by
  have hrefl : RELAT_2.isReflexiveIn R X := h.1
  have htrans : RELAT_2.isTransitiveIn R X := h.2.1
  have hanti : RELAT_2.isAntisymmetricIn R X := h.2.2.1
  have hconn : RELAT_2.isConnectedIn R X := h.2.2.2.1
  have hwf : WELLORD1.isWellFoundedIn R X := h.2.2.2.2
  have hanti2 : RELAT_2.isAntisymmetricIn (WELLORD1.restrict2 R X) X := by
    intro x y hx hy hxy hyx
    exact hanti x y hx hy
      ((WELLORD1.restrict2_iff R X x y).mp hxy).1
      ((WELLORD1.restrict2_iff R X y x).mp hyx).1
  have hwf2 : WELLORD1.isWellFoundedIn (WELLORD1.restrict2 R X) X := by
    intro Y hY hYne
    obtain ⟨a, ha, hmiss⟩ := hwf Y hY hYne
    refine ⟨a, ha, ?_⟩
    apply Classical.byContradiction
    intro hmeet
    have ⟨x, hxs, hxY⟩ :=
      (XBOOLE_0.th3 (WELLORD1.seg (WELLORD1.restrict2 R X) a) Y).mp hmeet
    have ⟨hne, hp⟩ :=
      (WELLORD1.th1 (WELLORD1.restrict2 R X) a x).mp hxs
    have hpR : TARSKI.pair x a ∈ R :=
      ((WELLORD1.restrict2_iff R X x a).mp hp).1
    have hxseg : x ∈ WELLORD1.seg R a :=
      (WELLORD1.th1 R a x).mpr ⟨hne, hpR⟩
    have hmeet2 : XBOOLE_0.meets (WELLORD1.seg R a) Y :=
      (XBOOLE_0.th3 (WELLORD1.seg R a) Y).mpr ⟨x, hxseg, hxY⟩
    exact hmeet2 hmiss
  have htrans2 : RELAT_2.isTransitiveIn (WELLORD1.restrict2 R X) X := by
    intro x y z hx hy hz hxy hyz
    have hp1 := ((WELLORD1.restrict2_iff R X x y).mp hxy).1
    have hp2 := ((WELLORD1.restrict2_iff R X y z).mp hyz).1
    have hp3 : TARSKI.pair x z ∈ R := htrans x y z hx hy hz hp1 hp2
    exact (WELLORD1.restrict2_iff R X x z).mpr
      ⟨hp3, hx, hz⟩
  have hconn2 : RELAT_2.isConnectedIn (WELLORD1.restrict2 R X) X := by
    intro x y hx hy hne
    have hpP : TARSKI.pair x y ∈ ZFMISC_1.product X X :=
      (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := X)).mpr ⟨hx, hy⟩
    have hqP : TARSKI.pair y x ∈ ZFMISC_1.product X X :=
      (ZFMISC_1.th87 (x := y) (y := x) (X := X) (Y := X)).mpr ⟨hy, hx⟩
    exact Or.elim (hconn x y hx hy hne)
      (fun hxy => Or.inl ((WELLORD1.restrict2_iff R X x y).mpr
        ⟨hxy, hx, hy⟩))
      (fun hyx => Or.inr ((WELLORD1.restrict2_iff R X y x).mpr
        ⟨hyx, hy, hx⟩))
  have hfield : RELAT_1.field (WELLORD1.restrict2 R X) = X := by
    apply TARSKI.extensionality
    intro x
    constructor
    · intro hx
      exact (WELLORD1.th13 R X).2 x hx
    · intro hx
      have hxx : TARSKI.pair x x ∈ R := hrefl x hx
      have hxx2 : TARSKI.pair x x ∈ WELLORD1.restrict2 R X :=
        (WELLORD1.restrict2_iff R X x x).mpr ⟨hxx, hx, hx⟩
      exact (RELAT_1.th15 hxx2).1
  have hrefl2 : RELAT_2.isReflexiveIn (WELLORD1.restrict2 R X) X := by
    intro x hx
    exact (WELLORD1.restrict2_iff R X x x).mpr ⟨hrefl x hx, hx, hx⟩
  have hwoX : WELLORD1.wellOrders (WELLORD1.restrict2 R X) X :=
    ⟨hrefl2, htrans2, hanti2, hconn2, hwf2⟩
  have hfield' : RELAT_1.field (WELLORD1.restrict2 R X) =
      RELAT_1.field (WELLORD1.restrict2 R X) := rfl
  exact ⟨hfield,
    (WELLORD1.th4 (WELLORD1.restrict2 R X)).mp
      (Eq.subst (motive := fun s =>
          WELLORD1.wellOrders (WELLORD1.restrict2 R X) s)
        hfield.symm hwoX)⟩

/-- `WELLORD2:lm 1` -/
theorem lm1 {R X : TarskiSet.{u}} (hR : WELLORD1.isWellOrdering R)
    (heq : TARSKI.are_equipotent X (RELAT_1.field R)) :
    ∃ Q, WELLORD1.wellOrders Q X := by
  obtain ⟨f, hf, h1, hd, hr⟩ := (are_equipotent_fun X (RELAT_1.field R)).mp heq
  obtain ⟨Q, hQrel, hQchar⟩ :=
    RELAT_1.sch_RelExistence X X
      (fun x y => TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply f y) ∈ R)
  refine ⟨Q, ?_⟩
  have hfQ : RELAT_1.field Q = X := by
    apply TARSKI.extensionality
    intro x
    constructor
    · intro hx
      have hdomrng := (XBOOLE_0.def3 (RELAT_1.dom Q) (RELAT_1.rng Q) x).mp hx
      exact Or.elim hdomrng
        (fun hdQ =>
          let ⟨y, hp⟩ := (RELAT_1.dom_iff Q x).mp hdQ
          ((hQchar x y).mp hp).1)
        (fun hrQ =>
          let ⟨y, hp⟩ := (RELAT_1.rng_iff Q x).mp hrQ
          ((hQchar y x).mp hp).2.1)
    · intro hx
      have hxD : x ∈ RELAT_1.dom f :=
        Eq.subst (motive := fun s => x ∈ s) hd.symm hx
      have hfx : FUNCT_1.apply f x ∈ RELAT_1.field R :=
        Eq.subst (motive := fun s => FUNCT_1.apply f x ∈ s) hr
          (FUNCT_1.th3 hf.2 hxD)
      have hxxR : TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply f x) ∈ R :=
        ((WELLORD1.lm1 R).mp hR.1) (FUNCT_1.apply f x) hfx
      have hxxQ : TARSKI.pair x x ∈ Q :=
        (hQchar x x).mpr ⟨hx, hx, hxxR⟩
      exact (RELAT_1.th15 hxxQ).1
  have hFiso : WELLORD1.isIsomorphismOf f Q R := by
    refine ⟨hf, hd.trans hfQ.symm, hr, h1, ?_⟩
    intro x y
    constructor
    · intro hp
      have ⟨hx, hy, hpR⟩ := (hQchar x y).mp hp
      exact ⟨Eq.subst (motive := fun s => x ∈ s) hfQ.symm hx,
        Eq.subst (motive := fun s => y ∈ s) hfQ.symm hy, hpR⟩
    · intro ⟨hx, hy, hpR⟩
      have hxX : x ∈ X :=
        Eq.subst (motive := fun s => x ∈ s) hfQ hx
      have hyX : y ∈ X :=
        Eq.subst (motive := fun s => y ∈ s) hfQ hy
      exact (hQchar x y).mpr ⟨hxX, hyX, hpR⟩
  have hQwo : WELLORD1.isWellOrdering Q :=
    WELLORD1.th44 hR (WELLORD1.th39 hFiso)
  exact Eq.subst (motive := fun s => WELLORD1.wellOrders Q s) hfQ
    ((WELLORD1.th4 Q).mp hQwo)

/-- `$N` Zermelo Theorem. `WELLORD2:17` (`Th17`).
Mizar uses `ZFMISC_1:112` inaccessibility of a TG class; this model
does not prove that clause, so the argument is Hartogs plus a
choice-driven transfinite enumeration, then `lm1`. -/
theorem th17 (X : TarskiSet.{u}) :
    ∃ R, WELLORD1.wellOrders R X := by
  obtain ⟨W, hW⟩ :=
    XBOOLE_0.sch_separation (ZFMISC_1.bool (ZFMISC_1.product X X))
      (fun R => WELLORD1.wellOrders R (RELAT_1.field R) ∧
        RELAT_1.field R ⊆ X)
  obtain ⟨ot, hot, hdot, hvot⟩ :=
    FUNCT_1.sch_Lambda W (fun R =>
      have := Classical.propDecidable (R ∈ W)
      if h : R ∈ W then
        order_type_of ((WELLORD1.th4 R).mp ((hW R).mp h).2.1)
      else (∅ : TarskiSet.{u}))
  have hrngOrd : ∀ a, a ∈ RELAT_1.rng ot → ORDINAL1.isOrdinal a := by
    intro a ha
    obtain ⟨R, hRd, heq⟩ := (FUNCT_1.def3 hot.2).mp ha
    have hRW : R ∈ W :=
      Eq.subst (motive := fun s => R ∈ s) hdot hRd
    have hwo : WELLORD1.wellOrders R (RELAT_1.field R) :=
      ((hW R).mp hRW).2.1
    have hRwo : WELLORD1.isWellOrdering R := (WELLORD1.th4 R).mp hwo
    have hval : FUNCT_1.apply ot R = order_type_of hRwo := by
      have hif := hvot R hRW
      have := Classical.propDecidable (R ∈ W)
      exact hif.trans (dif_pos hRW)
    exact Eq.subst (motive := ORDINAL1.isOrdinal) heq.symm
      (Eq.subst (motive := ORDINAL1.isOrdinal) hval.symm
        (order_type_of_ordinal hRwo))
  have hU : ORDINAL1.isOrdinal (TARSKI.union (RELAT_1.rng ot)) :=
    ORDINAL1.th23 hrngOrd
  have hα : ORDINAL1.isOrdinal
      (ORDINAL1.succ (TARSKI.union (RELAT_1.rng ot))) :=
    ORDINAL1.th17 hU
  let α := ORDINAL1.succ (TARSKI.union (RELAT_1.rng ot))
  let H : TarskiSet.{u} → TarskiSet.{u} := fun L =>
    let rest := X \ RELAT_1.rng L
    have := Classical.propDecidable (rest = (∅ : TarskiSet.{u}))
    if h : rest = (∅ : TarskiSet.{u}) then X
    else Classical.choose (exists_mem_of_ne h)
  obtain ⟨L, hLTS, hLdom, hLrec⟩ := ORDINAL1.sch_TSExist H hα
  obtain ⟨S, hS⟩ :=
    XBOOLE_0.sch_separation α (fun β => FUNCT_1.apply L β = X)
  have hSsub : S ⊆ α := fun x hx => ((hS x).mp hx).1
  have := Classical.propDecidable (S = (∅ : TarskiSet.{u}))
  cases Classical.em (S = (∅ : TarskiSet.{u})) with
  | inl hSempty =>
    have hnever : ∀ β, β ∈ α → FUNCT_1.apply L β ≠ X := by
      intro β hβ hX
      exact (XBOOLE_0.empty_iff β).mp
        (Eq.subst (motive := fun s => β ∈ s) hSempty
          ((hS β).mpr ⟨hβ, hX⟩))
    have h1 : FUNCT_1.isOneToOne L := by
      intro β1 β2 hβ1 hβ2 heq
      have hβ1α : β1 ∈ α :=
        Eq.subst (motive := fun s => β1 ∈ s) hLdom hβ1
      have hβ2α : β2 ∈ α :=
        Eq.subst (motive := fun s => β2 ∈ s) hLdom hβ2
      apply Classical.byContradiction
      intro hne
      have htri : β1 ∈ β2 ∨ β1 = β2 ∨ β2 ∈ β1 :=
        ORDINAL1.th14 (ORDINAL1.th13 hα hβ1α) (ORDINAL1.th13 hα hβ2α)
      have hrest : ∀ β γ, β ∈ α → γ ∈ α → β ∈ γ →
          FUNCT_1.apply L β ∈ RELAT_1.rng (RELAT_1.restrict L γ) ∧
            FUNCT_1.apply L γ ∉ RELAT_1.rng (RELAT_1.restrict L γ) := by
        intro β γ hβα hγα hβγ
        have hγsub : γ ⊆ α := hα.1 γ hγα
        have hdγ : RELAT_1.dom (RELAT_1.restrict L γ) = γ :=
          RELAT_1.th62 (R := L) (X := γ)
            (Eq.subst (motive := fun s => γ ⊆ s) hLdom.symm hγsub)
        have hβd : β ∈ RELAT_1.dom (RELAT_1.restrict L γ) :=
          Eq.subst (motive := fun s => β ∈ s) hdγ.symm hβγ
        have happβ : FUNCT_1.apply (RELAT_1.restrict L γ) β =
            FUNCT_1.apply L β :=
          FUNCT_1.th47 hLTS.1.2 hβd
        have hin : FUNCT_1.apply L β ∈
            RELAT_1.rng (RELAT_1.restrict L γ) :=
          Eq.subst (motive := fun s => s ∈
              RELAT_1.rng (RELAT_1.restrict L γ)) happβ
            (FUNCT_1.th3 (FUNCT_1.restrict_isFunctionLike hLTS.1.2) hβd)
        have hLγ : FUNCT_1.apply L γ = H (RELAT_1.restrict L γ) :=
          hLrec γ (RELAT_1.restrict L γ) hγα rfl
        have hneX : FUNCT_1.apply L γ ≠ X := hnever γ hγα
        have hrestne : X \ RELAT_1.rng (RELAT_1.restrict L γ) ≠
            (∅ : TarskiSet.{u}) := by
          intro hempty
          have := Classical.propDecidable
            (X \ RELAT_1.rng (RELAT_1.restrict L γ) =
              (∅ : TarskiSet.{u}))
          exact hneX (hLγ.trans (dif_pos hempty))
        have hpick : H (RELAT_1.restrict L γ) ∈
            X \ RELAT_1.rng (RELAT_1.restrict L γ) := by
          have := Classical.propDecidable
            (X \ RELAT_1.rng (RELAT_1.restrict L γ) =
              (∅ : TarskiSet.{u}))
          exact Eq.subst (motive := fun s => s ∈
              X \ RELAT_1.rng (RELAT_1.restrict L γ))
            (dif_neg hrestne).symm
            (Classical.choose_spec (exists_mem_of_ne hrestne))
        have hnotin : H (RELAT_1.restrict L γ) ∉
            RELAT_1.rng (RELAT_1.restrict L γ) :=
          ((XBOOLE_0.def5 X (RELAT_1.rng (RELAT_1.restrict L γ))
            (H (RELAT_1.restrict L γ))).mp hpick).2
        exact ⟨hin,
          Eq.subst (motive := fun s => s ∉
              RELAT_1.rng (RELAT_1.restrict L γ)) hLγ.symm hnotin⟩
      exact Or.elim htri
        (fun h12 => (hrest β1 β2 hβ1α hβ2α h12).2
          (Eq.subst (motive := fun s => s ∈
              RELAT_1.rng (RELAT_1.restrict L β2)) heq
            (hrest β1 β2 hβ1α hβ2α h12).1))
        (fun h => h.elim (fun he => hne he)
          (fun h21 => (hrest β2 β1 hβ2α hβ1α h21).2
            (Eq.subst (motive := fun s => s ∈
                RELAT_1.rng (RELAT_1.restrict L β1)) heq.symm
              (hrest β2 β1 hβ2α hβ1α h21).1)))
    have hrngX : RELAT_1.rng L ⊆ X := by
      intro y hy
      obtain ⟨β, hβd, heq⟩ := (FUNCT_1.def3 hLTS.1.2).mp hy
      have hβα : β ∈ α :=
        Eq.subst (motive := fun s => β ∈ s) hLdom hβd
      have hLβ : FUNCT_1.apply L β = H (RELAT_1.restrict L β) :=
        hLrec β (RELAT_1.restrict L β) hβα rfl
      have hneX : FUNCT_1.apply L β ≠ X := hnever β hβα
      have hrestne : X \ RELAT_1.rng (RELAT_1.restrict L β) ≠
          (∅ : TarskiSet.{u}) := by
        intro hempty
        have := Classical.propDecidable
          (X \ RELAT_1.rng (RELAT_1.restrict L β) =
            (∅ : TarskiSet.{u}))
        exact hneX (hLβ.trans (dif_pos hempty))
      have hpick : H (RELAT_1.restrict L β) ∈ X :=
        ((XBOOLE_0.def5 X (RELAT_1.rng (RELAT_1.restrict L β))
          (H (RELAT_1.restrict L β))).mp
          (by
            have := Classical.propDecidable
              (X \ RELAT_1.rng (RELAT_1.restrict L β) =
                (∅ : TarskiSet.{u}))
            exact Eq.subst (motive := fun s => s ∈
                X \ RELAT_1.rng (RELAT_1.restrict L β))
              (dif_neg hrestne).symm
              (Classical.choose_spec (exists_mem_of_ne hrestne)))).1
      exact Eq.subst (motive := fun s => s ∈ X) (heq.trans hLβ).symm
        hpick
    have hLinv : FUNCT_1.isFunction (FUNCT_1.inv L) :=
      FUNCT_1.inv_isFunction hLTS.1 h1
    obtain ⟨Q, hQrel, hQchar⟩ :=
      RELAT_1.sch_RelExistence (RELAT_1.rng L) (RELAT_1.rng L)
        (fun x y =>
          TARSKI.pair (FUNCT_1.apply (FUNCT_1.inv L) x)
            (FUNCT_1.apply (FUNCT_1.inv L) y) ∈ RelIncl α)
    have hfQ : RELAT_1.field Q = RELAT_1.rng L := by
      apply TARSKI.extensionality
      intro x
      constructor
      · intro hx
        have hd := (XBOOLE_0.def3 (RELAT_1.dom Q) (RELAT_1.rng Q) x).mp hx
        exact Or.elim hd
          (fun hxd =>
            let ⟨y, hp⟩ := (RELAT_1.dom_iff Q x).mp hxd
            ((hQchar x y).mp hp).1)
          (fun hxr =>
            let ⟨y, hp⟩ := (RELAT_1.rng_iff Q x).mp hxr
            ((hQchar y x).mp hp).2.1)
      · intro hx
        have hxD : x ∈ RELAT_1.dom (FUNCT_1.inv L) :=
          Eq.subst (motive := fun s => x ∈ s) (FUNCT_1.th33 h1).1 hx
        have hxx : TARSKI.pair
            (FUNCT_1.apply (FUNCT_1.inv L) x)
            (FUNCT_1.apply (FUNCT_1.inv L) x) ∈ RelIncl α :=
          (RelIncl_char α _ _).mpr
            ⟨Eq.subst (motive := fun s =>
                FUNCT_1.apply (FUNCT_1.inv L) x ∈ s)
              ((FUNCT_1.th33 h1).2.symm.trans hLdom)
              (FUNCT_1.th3 hLinv.2 hxD),
              Eq.subst (motive := fun s =>
                FUNCT_1.apply (FUNCT_1.inv L) x ∈ s)
              ((FUNCT_1.th33 h1).2.symm.trans hLdom)
              (FUNCT_1.th3 hLinv.2 hxD),
              fun _ ha => ha⟩
        exact (RELAT_1.th15 ((hQchar x x).mpr ⟨hx, hx, hxx⟩)).1
    have hFiso : WELLORD1.isIsomorphismOf (FUNCT_1.inv L) Q (RelIncl α) := by
      refine ⟨hLinv,
        (FUNCT_1.th33 h1).1.symm.trans hfQ.symm,
        (FUNCT_1.th33 h1).2.symm.trans
          (hLdom.trans (RelIncl_field α).symm),
        FUNCT_1.th40 hLTS.1 h1, ?_⟩
      intro x y
      constructor
      · intro hp
        have ⟨hx, hy, hpR⟩ := (hQchar x y).mp hp
        exact ⟨Eq.subst (motive := fun s => x ∈ s) hfQ.symm hx,
          Eq.subst (motive := fun s => y ∈ s) hfQ.symm hy, hpR⟩
      · intro ⟨hx, hy, hpR⟩
        have hxX : x ∈ RELAT_1.rng L :=
          Eq.subst (motive := fun s => x ∈ s) hfQ hx
        have hyX : y ∈ RELAT_1.rng L :=
          Eq.subst (motive := fun s => y ∈ s) hfQ hy
        exact (hQchar x y).mpr ⟨hxX, hyX, hpR⟩
    have hQwo : WELLORD1.isWellOrdering Q :=
      WELLORD1.th44 (RelIncl_wellOrdering hα) (WELLORD1.th39 hFiso)
    have hQwoF : WELLORD1.wellOrders Q (RELAT_1.field Q) :=
      (WELLORD1.th4 Q).mp hQwo
    have hQprod : Q ⊆ ZFMISC_1.product X X :=
      RELAT_1.rel_subset hQrel (fun a b hp =>
        (ZFMISC_1.th87 (x := a) (y := b) (X := X) (Y := X)).mpr
          ⟨hrngX a ((hQchar a b).mp hp).1,
            hrngX b ((hQchar a b).mp hp).2.1⟩)
    have hQW : Q ∈ W :=
      (hW Q).mpr
        ⟨(ZFMISC_1.def1 (ZFMISC_1.product X X) Q).mpr hQprod,
          ⟨hQwoF,
            fun z hz =>
              hrngX z (Eq.subst (motive := fun s => z ∈ s) hfQ hz)⟩⟩
    have hRwoW : WELLORD1.isWellOrdering Q :=
      (WELLORD1.th4 Q).mp ((hW Q).mp hQW).2.1
    have hval : FUNCT_1.apply ot Q = order_type_of hRwoW := by
      have hif := hvot Q hQW
      have := Classical.propDecidable (Q ∈ W)
      exact hif.trans (dif_pos hQW)
    have heqot : order_type_of hRwoW = α :=
      order_type_unique hRwoW hα
        ⟨FUNCT_1.inv L, hFiso⟩
    have hαrng : α ∈ RELAT_1.rng ot :=
      (FUNCT_1.def3 hot.2).mpr
        ⟨Q, Eq.subst (motive := fun s => Q ∈ s) hdot.symm hQW,
          (hval.trans heqot).symm⟩
    have hαα : α ∈ α :=
      (ORDINAL1.th22 hα hU).mpr
        (fun x hx =>
          (TARSKI.def4 (RELAT_1.rng ot) x).mpr ⟨α, hx, hαrng⟩)
    exact (ORDINAL1.not_mem_self α hαα).elim
  | inr hSne =>
    obtain ⟨β, hβS, hleast⟩ := ORDINAL1.th20 hα hSsub hSne
    have hβα : β ∈ α := ((hS β).mp hβS).1
    have hβX : FUNCT_1.apply L β = X := ((hS β).mp hβS).2
    have hLβ : FUNCT_1.apply L β = H (RELAT_1.restrict L β) :=
      hLrec β (RELAT_1.restrict L β) hβα rfl
    have hrest0 : X \ RELAT_1.rng (RELAT_1.restrict L β) =
        (∅ : TarskiSet.{u}) := by
      have := Classical.propDecidable
        (X \ RELAT_1.rng (RELAT_1.restrict L β) =
          (∅ : TarskiSet.{u}))
      apply Classical.byContradiction
      intro hne
      have hpick := Classical.choose_spec (exists_mem_of_ne hne)
      have hin : H (RELAT_1.restrict L β) ∈
          X \ RELAT_1.rng (RELAT_1.restrict L β) :=
        Eq.subst (motive := fun s => s ∈
            X \ RELAT_1.rng (RELAT_1.restrict L β))
          (dif_neg hne).symm hpick
      have hinX : H (RELAT_1.restrict L β) ∈ X :=
        ((XBOOLE_0.def5 X (RELAT_1.rng (RELAT_1.restrict L β))
          (H (RELAT_1.restrict L β))).mp hin).1
      exact ORDINAL1.not_mem_self X
        (Eq.subst (motive := fun s => s ∈ X)
          (hLβ.symm.trans hβX) hinX)
    have hXsub : X ⊆ RELAT_1.rng (RELAT_1.restrict L β) :=
      (XBOOLE_1.th37 (X := X)
        (Y := RELAT_1.rng (RELAT_1.restrict L β))).mp hrest0
    have hβsub : β ⊆ α := hα.1 β hβα
    have hdβ : RELAT_1.dom (RELAT_1.restrict L β) = β :=
      RELAT_1.th62 (R := L) (X := β)
        (Eq.subst (motive := fun s => β ⊆ s) hLdom.symm hβsub)
    have hrngXβ : RELAT_1.rng (RELAT_1.restrict L β) ⊆ X := by
      intro y hy
      obtain ⟨γ, hγd, heq⟩ :=
        (FUNCT_1.def3 (FUNCT_1.restrict_isFunctionLike hLTS.1.2)).mp hy
      have hγβ : γ ∈ β :=
        Eq.subst (motive := fun s => γ ∈ s) hdβ hγd
      have happ : FUNCT_1.apply (RELAT_1.restrict L β) γ =
          FUNCT_1.apply L γ :=
        FUNCT_1.th47 hLTS.1.2 hγd
      have hγα : γ ∈ α := hβsub γ hγβ
      have hneX : FUNCT_1.apply L γ ≠ X := fun hXeq =>
        ORDINAL1.not_mem_self γ
          ((hleast γ ((hS γ).mpr ⟨hγα, hXeq⟩)) γ hγβ)
      have hLγ : FUNCT_1.apply L γ = H (RELAT_1.restrict L γ) :=
        hLrec γ (RELAT_1.restrict L γ) hγα rfl
      have hrestne : X \ RELAT_1.rng (RELAT_1.restrict L γ) ≠
          (∅ : TarskiSet.{u}) := by
        intro hempty
        have := Classical.propDecidable
          (X \ RELAT_1.rng (RELAT_1.restrict L γ) =
            (∅ : TarskiSet.{u}))
        exact hneX (hLγ.trans (dif_pos hempty))
      have hpick : H (RELAT_1.restrict L γ) ∈ X :=
        ((XBOOLE_0.def5 X (RELAT_1.rng (RELAT_1.restrict L γ))
          (H (RELAT_1.restrict L γ))).mp
          (by
            have := Classical.propDecidable
              (X \ RELAT_1.rng (RELAT_1.restrict L γ) =
                (∅ : TarskiSet.{u}))
            exact Eq.subst (motive := fun s => s ∈
                X \ RELAT_1.rng (RELAT_1.restrict L γ))
              (dif_neg hrestne).symm
              (Classical.choose_spec (exists_mem_of_ne hrestne)))).1
      exact Eq.subst (motive := fun s => s ∈ X)
        (heq.trans (happ.trans hLγ)).symm hpick
    have hrngβ : RELAT_1.rng (RELAT_1.restrict L β) = X :=
      (XBOOLE_0.def10
        (X := RELAT_1.rng (RELAT_1.restrict L β)) (Y := X)).mpr
        ⟨hrngXβ, hXsub⟩
    have h1β : FUNCT_1.isOneToOne (RELAT_1.restrict L β) := by
      intro γ1 γ2 hγ1 hγ2 heq
      have hγ1β : γ1 ∈ β :=
        Eq.subst (motive := fun s => γ1 ∈ s) hdβ hγ1
      have hγ2β : γ2 ∈ β :=
        Eq.subst (motive := fun s => γ2 ∈ s) hdβ hγ2
      have happ1 : FUNCT_1.apply (RELAT_1.restrict L β) γ1 =
          FUNCT_1.apply L γ1 :=
        FUNCT_1.th47 hLTS.1.2 hγ1
      have happ2 : FUNCT_1.apply (RELAT_1.restrict L β) γ2 =
          FUNCT_1.apply L γ2 :=
        FUNCT_1.th47 hLTS.1.2 hγ2
      have hLeq : FUNCT_1.apply L γ1 = FUNCT_1.apply L γ2 :=
        happ1.symm.trans (heq.trans happ2)
      have hγ1α : γ1 ∈ α := hβsub γ1 hγ1β
      have hγ2α : γ2 ∈ α := hβsub γ2 hγ2β
      apply Classical.byContradiction
      intro hne
      have htri : γ1 ∈ γ2 ∨ γ1 = γ2 ∨ γ2 ∈ γ1 :=
        ORDINAL1.th14 (ORDINAL1.th13 hα hγ1α) (ORDINAL1.th13 hα hγ2α)
      have hrest : ∀ δ ε, δ ∈ α → ε ∈ α → δ ∈ ε → ε ∈ β →
          FUNCT_1.apply L δ ∈ RELAT_1.rng (RELAT_1.restrict L ε) ∧
            FUNCT_1.apply L ε ∉ RELAT_1.rng (RELAT_1.restrict L ε) := by
        intro δ ε hδα hεα hδε hεβ
        have hεsub : ε ⊆ α := hα.1 ε hεα
        have hdε : RELAT_1.dom (RELAT_1.restrict L ε) = ε :=
          RELAT_1.th62 (R := L) (X := ε)
            (Eq.subst (motive := fun s => ε ⊆ s) hLdom.symm hεsub)
        have hδd : δ ∈ RELAT_1.dom (RELAT_1.restrict L ε) :=
          Eq.subst (motive := fun s => δ ∈ s) hdε.symm hδε
        have happδ : FUNCT_1.apply (RELAT_1.restrict L ε) δ =
            FUNCT_1.apply L δ :=
          FUNCT_1.th47 hLTS.1.2 hδd
        have hin : FUNCT_1.apply L δ ∈
            RELAT_1.rng (RELAT_1.restrict L ε) :=
          Eq.subst (motive := fun s => s ∈
              RELAT_1.rng (RELAT_1.restrict L ε)) happδ
            (FUNCT_1.th3 (FUNCT_1.restrict_isFunctionLike hLTS.1.2) hδd)
        have hLε : FUNCT_1.apply L ε = H (RELAT_1.restrict L ε) :=
          hLrec ε (RELAT_1.restrict L ε) hεα rfl
        have hneX : FUNCT_1.apply L ε ≠ X := fun hXeq =>
          ORDINAL1.not_mem_self ε
            ((hleast ε ((hS ε).mpr ⟨hεα, hXeq⟩)) ε hεβ)
        have hrestne : X \ RELAT_1.rng (RELAT_1.restrict L ε) ≠
            (∅ : TarskiSet.{u}) := by
          intro hempty
          have := Classical.propDecidable
            (X \ RELAT_1.rng (RELAT_1.restrict L ε) =
              (∅ : TarskiSet.{u}))
          exact hneX (hLε.trans (dif_pos hempty))
        have hpick : H (RELAT_1.restrict L ε) ∈
            X \ RELAT_1.rng (RELAT_1.restrict L ε) := by
          have := Classical.propDecidable
            (X \ RELAT_1.rng (RELAT_1.restrict L ε) =
              (∅ : TarskiSet.{u}))
          exact Eq.subst (motive := fun s => s ∈
              X \ RELAT_1.rng (RELAT_1.restrict L ε))
            (dif_neg hrestne).symm
            (Classical.choose_spec (exists_mem_of_ne hrestne))
        have hnotin : H (RELAT_1.restrict L ε) ∉
            RELAT_1.rng (RELAT_1.restrict L ε) :=
          ((XBOOLE_0.def5 X (RELAT_1.rng (RELAT_1.restrict L ε))
            (H (RELAT_1.restrict L ε))).mp hpick).2
        exact ⟨hin,
          Eq.subst (motive := fun s => s ∉
              RELAT_1.rng (RELAT_1.restrict L ε)) hLε.symm hnotin⟩
      exact Or.elim htri
        (fun h12 => (hrest γ1 γ2 hγ1α hγ2α h12 hγ2β).2
          (Eq.subst (motive := fun s => s ∈
              RELAT_1.rng (RELAT_1.restrict L γ2)) hLeq
            (hrest γ1 γ2 hγ1α hγ2α h12 hγ2β).1))
        (fun h => h.elim (fun he => hne he)
          (fun h21 => (hrest γ2 γ1 hγ2α hγ1α h21 hγ1β).2
            (Eq.subst (motive := fun s => s ∈
                RELAT_1.rng (RELAT_1.restrict L γ1)) hLeq.symm
              (hrest γ2 γ1 hγ2α hγ1α h21 hγ1β).1)))
    have hfieldβ : RELAT_1.field (RelIncl β) = β := RelIncl_field β
    exact lm1 (RelIncl_wellOrdering (ORDINAL1.th13 hα hβα))
      (are_equipotent_symm
        (Eq.subst (motive := fun s => TARSKI.are_equipotent s X)
          hfieldβ.symm
          ((are_equipotent_fun β X).mpr
            ⟨RELAT_1.restrict L β,
              FUNCT_1.restrict_isFunction hLTS.1, h1β, hdβ, hrngβ⟩)))

end WELLORD2







