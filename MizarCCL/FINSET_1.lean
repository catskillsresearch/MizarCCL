import MizarCCL.ORDINAL3
import MizarCCL.FUNCT_4

/-
Copyright (c) 1990-2012 Association of Mizar Users.
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and `vendor/mml/finset_1.miz`.
Authors: Agata Darmochwał (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Finite Sets

Faithful 1–1 rendering of Mizar article `FINSET_1`: 15 absolute theorem
slots, six definition blocks (including two redefinitions), three lemmas,
two schemes, and all 54 claims in 50 registration blocks.  The source has
no canceled theorem slots.
-/

universe u

open TarskiSet TARSKI XBOOLE_0

namespace FINSET_1

local infixl:65 " +ᵒ " => ORDINAL2.ordinalAdd

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

private theorem subset_refl (A : TarskiSet.{u}) : A ⊆ A := fun _ h => h

/-- `FINSET_1:def 1`: Mizar's finite attribute. -/
def isFinite (A : TarskiSet.{u}) : Prop :=
  ∃ p, FUNCT_1.isFunction p ∧ RELAT_1.rng p = A ∧
    ORDINAL1.isNatural (RELAT_1.dom p)

theorem def1 (A : TarskiSet.{u}) :
    isFinite A ↔ ∃ p, FUNCT_1.isFunction p ∧ RELAT_1.rng p = A ∧
      ORDINAL1.isNatural (RELAT_1.dom p) :=
  Iff.rfl

/-- Mizar's antonym notation `infinite`. -/
def isInfinite (A : TarskiSet.{u}) : Prop := ¬ isFinite A

/-- `FINSET_1:Lm1`. -/
theorem lm1 (x : TarskiSet.{u}) : isFinite (TARSKI.singleton x) := by
  obtain ⟨p, hp, hd, hr⟩ :=
    FUNCT_1.sch_Lambda (TARSKI.singleton (∅ : TarskiSet.{u})) (fun _ => x)
  refine ⟨p, hp, ?_, ?_⟩
  · exact (FUNCT_1.th4 hp.2 hd).trans
      (congrArg TARSKI.singleton (hr (∅ : TarskiSet.{u})
        ((singleton_iff _ _).mpr rfl)))
  · rw [hd]
    rw [← ORDINAL3.th15, ORDINAL3.lm1]
    exact ORDINAL1.succ_isNatural ORDINAL1.empty_isNatural

/-- Registration: a nonempty finite set exists. -/
theorem exists_nonempty_finite :
    ∃ A : TarskiSet.{u}, A ≠ (∅ : TarskiSet.{u}) ∧ isFinite A :=
  ⟨TARSKI.singleton (∅ : TarskiSet.{u}),
    fun h => by
      have hm : (∅ : TarskiSet.{u}) ∈
          TARSKI.singleton (∅ : TarskiSet.{u}) :=
        (singleton_iff _ _).mpr rfl
      exact (XBOOLE_0.empty_iff (∅ : TarskiSet.{u})).mp
        (Eq.subst (motive := fun s => (∅ : TarskiSet.{u}) ∈ s) h hm),
    lm1 _⟩

/-- Registration: the empty set is finite. -/
theorem empty_isFinite : isFinite (∅ : TarskiSet.{u}) :=
  ⟨∅, FUNCT_1.empty_isFunction, RELAT_1.th38.2,
    Eq.subst (motive := ORDINAL1.isNatural) RELAT_1.th38.1.symm
      ORDINAL1.empty_isNatural⟩

/-- `FINSET_1:sch OLambdaC`. -/
theorem sch_OLambdaC (A : TarskiSet.{u}) (C : TarskiSet.{u} → Prop)
    (F G : TarskiSet.{u} → TarskiSet.{u}) :
    ∃ f, FUNCT_1.isFunction f ∧ RELAT_1.dom f = A ∧
      ∀ x, ORDINAL1.isOrdinal x → x ∈ A →
        (C x → FUNCT_1.apply f x = F x) ∧
        (¬ C x → FUNCT_1.apply f x = G x) := by
  classical
  obtain ⟨f, hf, hd, hv⟩ :=
    FUNCT_1.sch_Lambda A (fun x => if C x then F x else G x)
  refine ⟨f, hf, hd, ?_⟩
  intro x _ hx
  constructor
  · intro h; simpa [h] using hv x hx
  · intro h; simpa [h] using hv x hx

/-- `FINSET_1:Lm2`: a union of two finite sets is finite. -/
theorem lm2 {A B : TarskiSet.{u}} (hA : isFinite A) (hB : isFinite B) :
    isFinite (A ∪ B) := by
  classical
  obtain ⟨p, hp, hrp, hdp⟩ := hA
  obtain ⟨q, hq, hrq, hdq⟩ := hB
  let m := RELAT_1.dom p
  let n := RELAT_1.dom q
  let d := ORDINAL2.ordinalAdd m n
  obtain ⟨f, hf, hfd, hfv⟩ := FUNCT_1.sch_Lambda d
    (fun z => if z ∈ m then FUNCT_1.apply p z
      else FUNCT_1.apply q (ORDINAL3.ordinalSub z m))
  refine ⟨f, hf, ?_, ?_⟩
  · apply eq_of_mem
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz, hyz⟩ := (FUNCT_1.def3 hf.2).mp hy
      have hzd : z ∈ d := hfd ▸ hz
      by_cases hzm : z ∈ m
      · have hyp : FUNCT_1.apply p z ∈ RELAT_1.rng p :=
          FUNCT_1.th3 hp.2 hzm
        exact (XBOOLE_0.def3 A B y).mpr (Or.inl
          (hrp ▸ Eq.subst (motive := fun s => s ∈ RELAT_1.rng p)
            (hyz.trans (by simpa [hzm] using hfv z hzd)).symm hyp))
      · have hmz : m ⊆ z :=
          (ORDINAL1.th16 (ORDINAL1.natural_isOrdinal hdp)
            (ORDINAL1.th13 (ORDINAL2.ordinalAdd_isOrdinal m n) hzd))
            |>.resolve_right hzm
        have hsubmem : ORDINAL3.ordinalSub z m ∈ n := by
          have heq := (ORDINAL3.def5
            (ORDINAL1.th13 (ORDINAL2.ordinalAdd_isOrdinal m n) hzd)
            (ORDINAL1.natural_isOrdinal hdp)).1 hmz
          have hz' : z ∈ m +ᵒ n := hzd
          exact ORDINAL3.th22 (ORDINAL1.natural_isOrdinal hdp)
            (ORDINAL3.ordinalSub_isOrdinal z m)
            (ORDINAL1.natural_isOrdinal hdq)
            (Eq.subst (motive := fun s => s ∈ m +ᵒ n) heq hz')
        have hyq : FUNCT_1.apply q (ORDINAL3.ordinalSub z m) ∈ RELAT_1.rng q :=
          FUNCT_1.th3 hq.2 hsubmem
        exact (XBOOLE_0.def3 A B y).mpr (Or.inr
          (hrq ▸ Eq.subst (motive := fun s => s ∈ RELAT_1.rng q)
            (hyz.trans (by simpa [hzm] using hfv z hzd)).symm hyq))
    · intro hy
      rcases (XBOOLE_0.def3 A B y).mp hy with hyA | hyB
      · obtain ⟨z, hz, hyz⟩ := (FUNCT_1.def3 hp.2).mp (hrp ▸ hyA)
        have hzm : z ∈ m := hz
        have hzd : z ∈ d :=
          (ORDINAL3.th24 (ORDINAL1.natural_isOrdinal hdp)
            (ORDINAL1.natural_isOrdinal hdq)).1 z hz
        exact (FUNCT_1.def3 hf.2).mpr
          ⟨z, hfd.symm ▸ hzd,
            hyz.trans (by simpa [hzm] using (hfv z hzd).symm)⟩
      · obtain ⟨z, hz, hyz⟩ := (FUNCT_1.def3 hq.2).mp (hrq ▸ hyB)
        let w := ORDINAL2.ordinalAdd m z
        have hwd : w ∈ d := ORDINAL2.th32
          (ORDINAL1.th13 (ORDINAL1.natural_isOrdinal hdq) hz)
          (ORDINAL1.natural_isOrdinal hdq)
          (ORDINAL1.natural_isOrdinal hdp) hz
        have hwnm : w ∉ m := fun h =>
          ORDINAL1.th5 h ((ORDINAL3.th24 (ORDINAL1.natural_isOrdinal hdp)
            (ORDINAL1.th13 (ORDINAL1.natural_isOrdinal hdq) hz)).1)
        have hsub : ORDINAL3.ordinalSub w m = z :=
          ORDINAL3.th52 (ORDINAL1.natural_isOrdinal hdp)
            (ORDINAL1.th13 (ORDINAL1.natural_isOrdinal hdq) hz)
        exact (FUNCT_1.def3 hf.2).mpr
          ⟨w, hfd.symm ▸ hwd,
            hyz.trans (by simpa [hwnm, hsub] using (hfv w hwd).symm)⟩
  · rw [hfd]
    exact ORDINAL2.add_natural hdp hdq

/-- Registration: singletons are finite. -/
theorem singleton_isFinite (x : TarskiSet.{u}) : isFinite (TARSKI.singleton x) :=
  lm1 x

/-- Registration: unordered pairs are finite. -/
theorem upair_isFinite (x y : TarskiSet.{u}) : isFinite (TARSKI.upair x y) := by
  rw [ENUMSET1.th1 (x1 := x) (x2 := y)]
  exact lm2 (lm1 x) (lm1 y)

/-- Registration: three-element enumerations are finite. -/
theorem enumset3_isFinite (x y z : TarskiSet.{u}) :
    isFinite (ENUMSET1.enumset3 x y z) := by
  rw [ENUMSET1.th2 (x1 := x) (x2 := y) (x3 := z)]
  exact lm2 (lm1 x) (upair_isFinite y z)

/-- Registration: four-element enumerations are finite. -/
theorem enumset4_isFinite (a b c d : TarskiSet.{u}) :
    isFinite (ENUMSET1.enumset4 a b c d) := by
  rw [ENUMSET1.th6 (x1 := a) (x2 := b) (x3 := c) (x4 := d)]
  exact lm2 (enumset3_isFinite a b c) (lm1 d)

/-- Registration: five-element enumerations are finite. -/
theorem enumset5_isFinite (a b c d e : TarskiSet.{u}) :
    isFinite (ENUMSET1.enumset5 a b c d e) := by
  rw [ENUMSET1.th10 (x1 := a) (x2 := b) (x3 := c) (x4 := d) (x5 := e)]
  exact lm2 (enumset4_isFinite a b c d) (lm1 e)

/-- Registration: six-element enumerations are finite. -/
theorem enumset6_isFinite (a b c d e f : TarskiSet.{u}) :
    isFinite (ENUMSET1.enumset6 a b c d e f) := by
  rw [ENUMSET1.th15 (x1 := a) (x2 := b) (x3 := c) (x4 := d) (x5 := e)
    (x6 := f)]
  exact lm2 (enumset5_isFinite a b c d e) (lm1 f)

/-- Registration: seven-element enumerations are finite. -/
theorem enumset7_isFinite (a b c d e f g : TarskiSet.{u}) :
    isFinite (ENUMSET1.enumset7 a b c d e f g) := by
  rw [ENUMSET1.th21 (x1 := a) (x2 := b) (x3 := c) (x4 := d) (x5 := e)
    (x6 := f) (x7 := g)]
  exact lm2 (enumset6_isFinite a b c d e f) (lm1 g)

/-- Registration: eight-element enumerations are finite. -/
theorem enumset8_isFinite (a b c d e f g h : TarskiSet.{u}) :
    isFinite (ENUMSET1.enumset8 a b c d e f g h) := by
  rw [ENUMSET1.th28 (x1 := a) (x2 := b) (x3 := c) (x4 := d) (x5 := e)
    (x6 := f) (x7 := g) (x8 := h)]
  exact lm2 (enumset7_isFinite a b c d e f g) (lm1 h)

private theorem range_restrict_succ {p n : TarskiSet.{u}}
    (hp : FUNCT_1.isFunction p) (_hn : ORDINAL1.isNatural n)
    (hd : RELAT_1.dom p = ORDINAL1.succ n) :
    RELAT_1.rng p =
      RELAT_1.rng (RELAT_1.restrict p n) ∪
        TARSKI.singleton (FUNCT_1.apply p n) := by
  apply eq_of_mem
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, heq⟩ := (FUNCT_1.def3 hp.2).mp hy
    rcases (ORDINAL1.th8 x n).mp (hd ▸ hx) with hxn | hxn
    · exact (XBOOLE_0.def3 _ _ y).mpr (Or.inl
      ((FUNCT_1.def3 (FUNCT_1.restrict_isFunctionLike hp.2)).mpr
        ⟨x, (RELAT_1.th57).mpr ⟨hxn, hx⟩,
          heq.trans (FUNCT_1.th49 hp.2 hxn).symm⟩))
    · exact (XBOOLE_0.def3 _ _ y).mpr (Or.inr
        ((singleton_iff _ _).mpr
          (heq.trans (congrArg (FUNCT_1.apply p) hxn))))
  · intro hy
    rcases (XBOOLE_0.def3 _ _ y).mp hy with hy | hy
    · obtain ⟨x, hx, heq⟩ :=
        (FUNCT_1.def3 (FUNCT_1.restrict_isFunctionLike hp.2)).mp hy
      have hxp := (RELAT_1.th57).mp hx |>.2
      exact (FUNCT_1.def3 hp.2).mpr
        ⟨x, hxp, heq.trans (FUNCT_1.th47 hp.2 hx)⟩
    · have heq := (singleton_iff (FUNCT_1.apply p n) y).mp hy
      exact (FUNCT_1.def3 hp.2).mpr
        ⟨n, hd.symm ▸ ORDINAL1.th6 n, heq⟩

private theorem finite_induction_core
    (A : TarskiSet.{u}) (P : TarskiSet.{u} → Prop)
    (hA : isFinite A) (h0 : P (∅ : TarskiSet.{u}))
    (hs : ∀ x B, x ∈ A → B ⊆ A → P B → P (B ∪ TARSKI.singleton x)) :
    P A := by
  obtain ⟨p, hp, hr, hn⟩ := hA
  let Q := fun n : TarskiSet.{u} => ∀ q, FUNCT_1.isFunction q →
    RELAT_1.dom q = n → RELAT_1.rng q ⊆ A → P (RELAT_1.rng q)
  have q0 : Q (∅ : TarskiSet.{u}) := by
    intro q hq hd _
    have hre : RELAT_1.rng q = (∅ : TarskiSet.{u}) :=
      (RELAT_1.th42 hq.1).mp hd
    exact hre ▸ h0
  have qs : ∀ n, ORDINAL1.isNatural n → Q n → Q (ORDINAL1.succ n) := by
    intro n hn ih q hq hd hrq
    let r := RELAT_1.restrict q n
    have hdr : RELAT_1.dom r = n := by
      rw [RELAT_1.th61, hd]
      rw [XBOOLE_0.inter_comm]
      exact XBOOLE_1.th28 (ORDINAL3.th1 n)
    have hrr : RELAT_1.rng r ⊆ A :=
      XBOOLE_1.th1 (RELAT_1.th11 RELAT_1.th59).2 hrq
    have hi := ih r (FUNCT_1.restrict_isFunction hq) hdr hrr
    have hqn : FUNCT_1.apply q n ∈ A :=
      hrq _ (FUNCT_1.th3 hq.2 (hd.symm ▸ ORDINAL1.th6 n))
    rw [range_restrict_succ hq hn hd]
    exact hs _ _ hqn hrr hi
  have := ORDINAL2.sch_OmegaInd hn Q q0 qs p hp
    rfl
    (hr ▸ subset_refl A)
  exact hr ▸ this

/-- Registration: subsets of finite sets are finite. -/
theorem subset_isFinite {A B : TarskiSet.{u}} (hAB : A ⊆ B)
    (hB : isFinite B) : isFinite A := by
  have hres := finite_induction_core B (fun C => isFinite (C ∩ A)) hB
    (by
      have he : (∅ : TarskiSet.{u}) ∩ A = (∅ : TarskiSet.{u}) := by
        apply eq_of_mem
        intro x
        simp only [XBOOLE_0.def4, XBOOLE_0.empty_iff, false_and]
      rw [he]
      exact empty_isFinite) (by
    intro x C _ _ ih
    by_cases hx : x ∈ A
    · have heq : (C ∪ TARSKI.singleton x) ∩ A =
          (C ∩ A) ∪ TARSKI.singleton x := by
        apply eq_of_mem
        intro z
        simp only [XBOOLE_0.def3, XBOOLE_0.def4, singleton_iff]
        constructor
        · rintro ⟨h | h, hzA⟩
          · exact Or.inl ⟨h, hzA⟩
          · exact Or.inr h
        · rintro (⟨hC, hzA⟩ | hzx)
          · exact ⟨Or.inl hC, hzA⟩
          · exact ⟨Or.inr hzx, hzx ▸ hx⟩
      rw [heq]
      exact lm2 ih (lm1 x)
    · have heq : (C ∪ TARSKI.singleton x) ∩ A = C ∩ A := by
        apply eq_of_mem
        intro z
        simp only [XBOOLE_0.def3, XBOOLE_0.def4, singleton_iff]
        constructor
        · rintro ⟨h | h, hzA⟩
          · exact ⟨h, hzA⟩
          · exact (hx (h ▸ hzA)).elim
        · rintro ⟨h, hzA⟩; exact ⟨Or.inl h, hzA⟩
      rw [heq]; exact ih)
  rw [XBOOLE_0.inter_comm, XBOOLE_1.th28 hAB] at hres
  exact hres

/-- `FINSET_1:1` (unlabeled). -/
theorem th1 {A B : TarskiSet.{u}} (hAB : A ⊆ B) (hB : isFinite B) :
    isFinite A :=
  subset_isFinite hAB hB

/-- `FINSET_1:2` (unlabeled). -/
theorem th2 {A B : TarskiSet.{u}} (hA : isFinite A) (hB : isFinite B) :
    isFinite (A ∪ B) :=
  lm2 hA hB

/-- Registration: unions of finite sets are finite. -/
theorem union_isFinite {A B : TarskiSet.{u}}
    (hA : isFinite A) (hB : isFinite B) : isFinite (A ∪ B) :=
  lm2 hA hB

/-- Registration: intersection with a finite right operand is finite. -/
theorem inter_right_isFinite {A B : TarskiSet.{u}} (hB : isFinite B) :
    isFinite (A ∩ B) := by
  rw [XBOOLE_0.inter_comm]
  exact th1 XBOOLE_1.th17 hB

/-- Registration: intersection with, and difference from, a finite set. -/
theorem inter_left_isFinite {A B : TarskiSet.{u}} (hA : isFinite A) :
    isFinite (A ∩ B) :=
  th1 XBOOLE_1.th17 hA

theorem diff_isFinite {A B : TarskiSet.{u}} (hA : isFinite A) :
    isFinite (A \ B) :=
  th1 (fun x hx => (XBOOLE_0.def5 A B x).mp hx |>.1) hA

/-- `FINSET_1:3` (unlabeled). -/
theorem th3 {A B : TarskiSet.{u}} (hA : isFinite A) : isFinite (A ∩ B) :=
  inter_left_isFinite hA

/-- `FINSET_1:4` (unlabeled). -/
theorem th4 {A B : TarskiSet.{u}} (hA : isFinite A) : isFinite (A \ B) :=
  diff_isFinite hA

/-- Registration: the image of a finite set under a function is finite. -/
theorem image_isFinite {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hA : isFinite A) : isFinite (RELAT_1.image f A) := by
  have hB : isFinite (RELAT_1.dom f ∩ A) :=
    inter_right_isFinite hA
  obtain ⟨p, hp, hrp, hdp⟩ := hB
  let q := RELAT_1.comp p f
  have hdom : RELAT_1.dom q = RELAT_1.dom p :=
    RELAT_1.th27 (hrp ▸ XBOOLE_1.th17)
  refine ⟨q, FUNCT_1.comp_isFunction hp hf, ?_, hdom ▸ hdp⟩
  calc
    RELAT_1.rng q = RELAT_1.image f (RELAT_1.rng p) := RELAT_1.th127
    _ = RELAT_1.image f (RELAT_1.dom f ∩ A) := congrArg _ hrp
    _ = RELAT_1.image f A := RELAT_1.th112.symm

/-- `FINSET_1:5` (unlabeled). -/
theorem th5 {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hA : isFinite A) : isFinite (RELAT_1.image f A) :=
  image_isFinite hf hA

/-- `FINSET_1:sch Finite`: finite-set induction. -/
theorem sch_Finite {A : TarskiSet.{u}} (P : TarskiSet.{u} → Prop)
    (hA : isFinite A) (h0 : P (∅ : TarskiSet.{u}))
    (hs : ∀ x B, x ∈ A → B ⊆ A → P B →
      P (B ∪ TARSKI.singleton x)) : P A :=
  finite_induction_core A P hA h0 hs

/-- `FINSET_1:Lm3`. -/
theorem lm3 {A : TarskiSet.{u}} (hA : isFinite A)
    (hm : ∀ X, X ∈ A → isFinite X) : isFinite (TARSKI.union A) := by
  apply sch_Finite (A := A) (fun B => isFinite (TARSKI.union B)) hA
  · rw [ZFMISC_1.th2]; exact empty_isFinite
  · intro x B hx _ ih
    rw [ZFMISC_1.th78, ZFMISC_1.th25]
    exact lm2 ih (hm x hx)

private theorem product_singleton_right_isFinite {A : TarskiSet.{u}}
    (hA : isFinite A) (y : TarskiSet.{u}) :
    isFinite (ZFMISC_1.product A (TARSKI.singleton y)) := by
  obtain ⟨f, hf, hd, hv⟩ :=
    FUNCT_1.sch_Lambda A (fun x => TARSKI.pair x y)
  have himg : RELAT_1.image f A =
      ZFMISC_1.product A (TARSKI.singleton y) := by
    apply eq_of_mem
    intro z
    constructor
    · intro hz
      obtain ⟨x, _, hxA, heq⟩ := (FUNCT_1.def6 hf.2).mp hz
      exact Eq.subst (motive := fun s => s ∈
        ZFMISC_1.product A (TARSKI.singleton y))
        (heq.trans (hv x hxA)).symm
        ((ZFMISC_1.th87).mpr ⟨hxA, (singleton_iff _ _).mpr rfl⟩)
    · intro hz
      obtain ⟨x, z', hxA, hz', heq⟩ := (ZFMISC_1.def2 A
        (TARSKI.singleton y) z).mp hz
      have hz'y : z' = y := (singleton_iff y z').mp hz'
      refine (FUNCT_1.def6 hf.2).mpr
        ⟨x, hd.symm ▸ hxA, hxA, ?_⟩
      exact heq.trans (congrArg (TARSKI.pair x) hz'y) |>.trans
        (hv x hxA).symm
  rw [← himg]
  exact image_isFinite hf hA

/-- Registration: Cartesian products of finite sets are finite. -/
theorem product_isFinite {A B : TarskiSet.{u}}
    (hA : isFinite A) (hB : isFinite B) :
    isFinite (ZFMISC_1.product A B) := by
  apply sch_Finite (A := B)
    (fun C => isFinite (ZFMISC_1.product A C)) hB
  · have he : ZFMISC_1.product A (∅ : TarskiSet.{u}) =
        (∅ : TarskiSet.{u}) :=
      (ZFMISC_1.th90).2 (Or.inr rfl)
    rw [he]; exact empty_isFinite
  · intro x C _ _ ih
    rw [(ZFMISC_1.th97 (X := C) (Y := TARSKI.singleton x) (Z := A)).2]
    exact lm2 ih (product_singleton_right_isFinite hA x)

/-- Registration: triple Cartesian products of finite sets are finite. -/
theorem product3_isFinite {A B C : TarskiSet.{u}}
    (hA : isFinite A) (hB : isFinite B) (hC : isFinite C) :
    isFinite (ZFMISC_1.product3 A B C) := by
  unfold ZFMISC_1.product3
  exact product_isFinite (product_isFinite hA hB) hC

/-- Registration: quadruple Cartesian products of finite sets are finite. -/
theorem product4_isFinite {A B C D : TarskiSet.{u}}
    (hA : isFinite A) (hB : isFinite B) (hC : isFinite C)
    (hD : isFinite D) :
    isFinite (ZFMISC_1.product4 A B C D) := by
  unfold ZFMISC_1.product4
  exact product_isFinite (product3_isFinite hA hB hC) hD

/-- Registration: power sets of finite sets are finite. -/
theorem bool_isFinite {A : TarskiSet.{u}} (hA : isFinite A) :
    isFinite (ZFMISC_1.bool A) := by
  apply sch_Finite (A := A) (fun B => isFinite (ZFMISC_1.bool B)) hA
  · rw [ZFMISC_1.th1]; exact lm1 _
  · intro x B _ _ ih
    obtain ⟨f, hf, hd, hv⟩ :=
      FUNCT_1.sch_Lambda (ZFMISC_1.bool B)
        (fun Y => Y ∪ TARSKI.singleton x)
    have himg := image_isFinite hf ih
    apply th1 (B := ZFMISC_1.bool B ∪ RELAT_1.image f (ZFMISC_1.bool B))
      ?_ (lm2 ih himg)
    intro Y hY
    have hsub : Y ⊆ B ∪ TARSKI.singleton x :=
      (ZFMISC_1.def1 _ Y).mp hY
    by_cases hxY : x ∈ Y
    · apply (XBOOLE_0.def3 _ _ Y).mpr
      right
      let Z := Y \ TARSKI.singleton x
      have hZB : Z ⊆ B := by
        intro z hz
        have hzY := (XBOOLE_0.def5 Y (TARSKI.singleton x) z).mp hz |>.1
        have hzU := hsub z hzY
        rcases (XBOOLE_0.def3 B (TARSKI.singleton x) z).mp hzU with hzB | hzx
        · exact hzB
        · exact (((XBOOLE_0.def5 Y (TARSKI.singleton x) z).mp hz).2
            hzx).elim
      have hZd : Z ∈ RELAT_1.dom f :=
        hd.symm ▸ (ZFMISC_1.def1 B Z).mpr hZB
      refine (FUNCT_1.def6 hf.2).mpr
        ⟨Z, hZd, (ZFMISC_1.def1 B Z).mpr hZB, ?_⟩
      calc
        Y = TARSKI.singleton x ∪ (Y \ TARSKI.singleton x) :=
          XBOOLE_1.th45 ((ZFMISC_1.th31).2 hxY)
        _ = (Y \ TARSKI.singleton x) ∪ TARSKI.singleton x :=
          XBOOLE_0.union_comm _ _
        _ = FUNCT_1.apply f Z := (hv Z ((ZFMISC_1.def1 B Z).mpr hZB)).symm
    · apply (XBOOLE_0.def3 _ _ Y).mpr
      left
      exact (ZFMISC_1.def1 B Y).mpr (fun z hz =>
        (XBOOLE_0.def3 B (TARSKI.singleton x) z).mp (hsub z hz) |>.resolve_right
          (fun hzx => hxY ((singleton_iff x z).mp hzx ▸ hz)))

private theorem finite_has_maximal {S : TarskiSet.{u}} (hS : isFinite S)
    (hne : S ≠ (∅ : TarskiSet.{u})) :
    ∃ m, m ∈ S ∧ ∀ C, C ∈ S → m ⊆ C → C = m := by
  let P := fun T : TarskiSet.{u} => T ≠ (∅ : TarskiSet.{u}) →
    ∃ m, m ∈ T ∧ ∀ C, C ∈ T → m ⊆ C → C = m
  apply sch_Finite (A := S) P hS
  · intro h; exact (h rfl).elim
  · intro x B _ _ ih hneU
    by_cases hB0 : B = (∅ : TarskiSet.{u})
    · refine ⟨x, (XBOOLE_0.def3 _ _ _).mpr (Or.inr
        ((singleton_iff _ _).mpr rfl)), ?_⟩
      intro C hC _
      rcases (XBOOLE_0.def3 B (TARSKI.singleton x) C).mp hC with hCB | hCx
      · exact ((XBOOLE_0.empty_iff C).mp (hB0 ▸ hCB)).elim
      · exact (singleton_iff x C).mp hCx
    · obtain ⟨m, hmB, hm⟩ := ih hB0
      by_cases hmx : m ⊆ x
      · refine ⟨x, (XBOOLE_0.def3 _ _ _).mpr (Or.inr
          ((singleton_iff _ _).mpr rfl)), ?_⟩
        intro C hC hxC
        rcases (XBOOLE_0.def3 B (TARSKI.singleton x) C).mp hC with hCB | hCx
        · have hCm : C = m := hm C hCB (XBOOLE_1.th1 hmx hxC)
          have hxm : x = m := XBOOLE_0.def10.mpr
            ⟨Eq.subst (motive := fun s => x ⊆ s) hCm hxC, hmx⟩
          exact hCm.trans hxm.symm
        · exact (singleton_iff x C).mp hCx
      · refine ⟨m, (XBOOLE_0.def3 _ _ _).mpr (Or.inl hmB), ?_⟩
        intro C hC hmC
        rcases (XBOOLE_0.def3 B (TARSKI.singleton x) C).mp hC with hCB | hCx
        · exact hm C hCB hmC
        · exact (hmx (Eq.subst (motive := fun s => m ⊆ s)
            ((singleton_iff x C).mp hCx) hmC)).elim
  · exact hne

/-- `FINSET_1:6` (`Th6`). -/
theorem th6 {A X : TarskiSet.{u}} (hA : isFinite A)
    (hXA : X ⊆ ZFMISC_1.bool A) (hne : X ≠ (∅ : TarskiSet.{u})) :
    ∃ x, x ∈ X ∧ ∀ B, B ∈ X → x ⊆ B → B = x :=
  finite_has_maximal (th1 hXA (bool_isFinite hA)) hne

/-- `FINSET_1:7` (`Th7`). -/
theorem th7 {A : TarskiSet.{u}} :
    (isFinite A ∧ ∀ X, X ∈ A → isFinite X) ↔
      isFinite (TARSKI.union A) := by
  constructor
  · rintro ⟨hA, hm⟩; exact lm3 hA hm
  · intro hu
    constructor
    · exact th1 ZFMISC_1.th82 (bool_isFinite hu)
    · intro X hX
      exact th1 (ZFMISC_1.th74 hX) hu

/-- `FINSET_1:8` (`Th8`). -/
theorem th8 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hd : isFinite (RELAT_1.dom f)) : isFinite (RELAT_1.rng f) := by
  rw [← RELAT_1.th113 (R := f)]
  exact image_isFinite hf hd

/-- `FINSET_1:9` (unlabeled). -/
theorem th9 {f Y : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hY : Y ⊆ RELAT_1.rng f) (hpre : isFinite (RELAT_1.invimage f Y)) :
    isFinite Y := by
  have he := FUNCT_1.th77 hf.2 hY
  rw [← he]
  exact image_isFinite hf hpre

/-- Registration: symmetric differences of finite sets are finite. -/
theorem symmDiff_isFinite {X Y : TarskiSet.{u}} (hX : isFinite X)
    (hY : isFinite Y) : isFinite (X ∆ Y) := by
  rw [XBOOLE_0.def6]
  exact lm2 (diff_isFinite hX) (diff_isFinite hY)

/-- Registration: finite nonempty subsets of nonempty sets exist. -/
theorem exists_nonempty_finite_subset {X : TarskiSet.{u}}
    (hne : X ≠ (∅ : TarskiSet.{u})) :
    ∃ A, A ⊆ X ∧ A ≠ (∅ : TarskiSet.{u}) ∧ isFinite A := by
  obtain ⟨x, hx⟩ := XBOOLE_0.th7 hne
  refine ⟨TARSKI.singleton x, (ZFMISC_1.th31).2 hx, ?_, lm1 x⟩
  intro h
  exact (XBOOLE_0.empty_iff x).mp
    (Eq.subst (motive := fun s => x ∈ s) h ((singleton_iff x x).mpr rfl))

/-- `FINSET_1:10` (`Th10`). -/
theorem th10 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    isFinite (RELAT_1.dom f) ↔ isFinite f := by
  constructor
  · intro hd
    exact th1 (RELAT_1.th7 hf.1)
      (product_isFinite hd (th8 hf hd))
  · intro hfin
    rw [← FUNCT_3.th79 hf]
    exact image_isFinite (FUNCT_3.pr1_isFunction _ _) hfin

/-- `FINSET_1:11` (unlabeled): a finite inclusion-chain has a least member. -/
theorem th11 {F : TarskiSet.{u}} (hF : isFinite F)
    (hne : F ≠ (∅ : TarskiSet.{u}))
    (hlin : ∀ A, A ∈ F → ∀ B, B ∈ F → A ⊆ B ∨ B ⊆ A) :
    ∃ m, m ∈ F ∧ ∀ C, C ∈ F → m ⊆ C := by
  let P := fun S : TarskiSet.{u} => S ≠ (∅ : TarskiSet.{u}) →
    ∃ m, m ∈ S ∧ ∀ C, C ∈ S → m ⊆ C
  apply sch_Finite (A := F) P hF
  · intro h; exact (h rfl).elim
  · intro x B hxF hBF ih _
    by_cases hB0 : B = (∅ : TarskiSet.{u})
    · refine ⟨x, (XBOOLE_0.def3 _ _ _).mpr
        (Or.inr ((singleton_iff _ _).mpr rfl)), ?_⟩
      intro C hC
      rcases (XBOOLE_0.def3 B (TARSKI.singleton x) C).mp hC with h | h
      · exact ((XBOOLE_0.empty_iff C).mp (hB0 ▸ h)).elim
      · exact Eq.subst (motive := fun s => x ⊆ s)
          ((singleton_iff x C).mp h).symm (subset_refl x)
    · obtain ⟨m, hmB, hm⟩ := ih hB0
      rcases hlin m (hBF m hmB) x hxF with hmx | hxm
      · refine ⟨m, (XBOOLE_0.def3 _ _ _).mpr (Or.inl hmB), ?_⟩
        intro C hC
        rcases (XBOOLE_0.def3 B (TARSKI.singleton x) C).mp hC with h | h
        · exact hm C h
        · exact Eq.subst (motive := fun s => m ⊆ s)
            ((singleton_iff x C).mp h).symm hmx
      · refine ⟨x, (XBOOLE_0.def3 _ _ _).mpr
          (Or.inr ((singleton_iff _ _).mpr rfl)), ?_⟩
        intro C hC
        rcases (XBOOLE_0.def3 B (TARSKI.singleton x) C).mp hC with h | h
        · exact XBOOLE_1.th1 hxm (hm C h)
        · exact Eq.subst (motive := fun s => x ⊆ s)
            ((singleton_iff x C).mp h).symm (subset_refl x)
  · exact hne

/-- `FINSET_1:12` (unlabeled): a finite inclusion-chain has a greatest member. -/
theorem th12 {F : TarskiSet.{u}} (hF : isFinite F)
    (hne : F ≠ (∅ : TarskiSet.{u}))
    (hlin : ∀ A, A ∈ F → ∀ B, B ∈ F → A ⊆ B ∨ B ⊆ A) :
    ∃ m, m ∈ F ∧ ∀ C, C ∈ F → C ⊆ m := by
  obtain ⟨m, hm, hmax⟩ := finite_has_maximal hF hne
  refine ⟨m, hm, ?_⟩
  intro C hC
  rcases hlin C hC m hm with h | h
  · exact h
  · exact Eq.subst (motive := fun s => C ⊆ s) (hmax C hC h)
      (subset_refl C)

/-- `FINSET_1:def 2`: finite-yielding relations. -/
def isFiniteYielding (R : TarskiSet.{u}) : Prop :=
  ∀ x, x ∈ RELAT_1.rng R → isFinite x

theorem def2 (R : TarskiSet.{u}) :
    isFiniteYielding R ↔ ∀ x, x ∈ RELAT_1.rng R → isFinite x :=
  Iff.rfl

/-- `FINSET_1:13` (unlabeled). -/
theorem th13 {X Y Z : TarskiSet.{u}} (hX : isFinite X)
    (hsub : X ⊆ ZFMISC_1.product Y Z) :
    ∃ A B, isFinite A ∧ A ⊆ Y ∧ isFinite B ∧ B ⊆ Z ∧
      X ⊆ ZFMISC_1.product A B := by
  let A := RELAT_1.image (FUNCT_3.pr1 Y Z) X
  let B := RELAT_1.image (FUNCT_3.pr2 Y Z) X
  have hA : isFinite A := image_isFinite (FUNCT_3.pr1_isFunction Y Z) hX
  have hB : isFinite B := image_isFinite (FUNCT_3.pr2_isFunction Y Z) hX
  refine ⟨A, B, hA, ?_, hB, ?_, ?_⟩
  · intro a ha
    obtain ⟨p, _, hpX, heq⟩ :=
      (FUNCT_1.def6 (FUNCT_3.pr1_isFunction Y Z).2).mp ha
    obtain ⟨x, y, hxY, hyZ, hp⟩ := (ZFMISC_1.def2 Y Z p).mp (hsub p hpX)
    exact Eq.subst (motive := fun s => s ∈ Y)
      ((heq.trans (congrArg (FUNCT_1.apply (FUNCT_3.pr1 Y Z)) hp)).trans
        (FUNCT_3.def4 hxY hyZ)).symm hxY
  · intro b hb
    obtain ⟨p, _, hpX, heq⟩ :=
      (FUNCT_1.def6 (FUNCT_3.pr2_isFunction Y Z).2).mp hb
    obtain ⟨x, y, hxY, hyZ, hp⟩ := (ZFMISC_1.def2 Y Z p).mp (hsub p hpX)
    exact Eq.subst (motive := fun s => s ∈ Z)
      ((heq.trans (congrArg (FUNCT_1.apply (FUNCT_3.pr2 Y Z)) hp)).trans
        (FUNCT_3.def5 hxY hyZ)).symm hyZ
  · intro p hpX
    obtain ⟨x, y, hxY, hyZ, hp⟩ := (ZFMISC_1.def2 Y Z p).mp (hsub p hpX)
    apply (ZFMISC_1.def2 A B p).mpr
    refine ⟨x, y, ?_, ?_, hp⟩
    · exact (FUNCT_1.def6 (FUNCT_3.pr1_isFunction Y Z).2).mpr
        ⟨p, (FUNCT_3.pr1_dom Y Z).symm ▸ hsub p hpX, hpX,
          ((congrArg (FUNCT_1.apply (FUNCT_3.pr1 Y Z)) hp).trans
            (FUNCT_3.def4 hxY hyZ)).symm⟩
    · exact (FUNCT_1.def6 (FUNCT_3.pr2_isFunction Y Z).2).mpr
        ⟨p, (FUNCT_3.pr2_dom Y Z).symm ▸ hsub p hpX, hpX,
          ((congrArg (FUNCT_1.apply (FUNCT_3.pr2 Y Z)) hp).trans
            (FUNCT_3.def5 hxY hyZ)).symm⟩

/-- `FINSET_1:14` (unlabeled). -/
theorem th14 {X Y Z : TarskiSet.{u}} (hX : isFinite X)
    (hsub : X ⊆ ZFMISC_1.product Y Z) :
    ∃ A, isFinite A ∧ A ⊆ Y ∧ X ⊆ ZFMISC_1.product A Z := by
  obtain ⟨A, B, hA, hAY, _, hBZ, hXAB⟩ := th13 hX hsub
  exact ⟨A, hA, hAY, XBOOLE_1.th1 hXAB
    (ZFMISC_1.th96 (subset_refl A) hBZ)⟩

/-- `FINSET_1:def 3`: centered families. -/
def isCentered (F : TarskiSet.{u}) : Prop :=
  F ≠ (∅ : TarskiSet.{u}) ∧
    ∀ G, G ≠ (∅ : TarskiSet.{u}) → G ⊆ F → isFinite G →
      SETFAM_1.meet G ≠ (∅ : TarskiSet.{u})

theorem def3 (F : TarskiSet.{u}) :
    isCentered F ↔ F ≠ (∅ : TarskiSet.{u}) ∧
      ∀ G, G ≠ (∅ : TarskiSet.{u}) → G ⊆ F → isFinite G →
        SETFAM_1.meet G ≠ (∅ : TarskiSet.{u}) :=
  Iff.rfl

/-- `FINSET_1:def 4`: function form of finite-yielding. -/
theorem def4 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    isFiniteYielding f ↔
      ∀ i, i ∈ RELAT_1.dom f → isFinite (FUNCT_1.apply f i) := by
  constructor
  · intro h i hi
    exact h _ (FUNCT_1.th3 hf.2 hi)
  · intro h y hy
    obtain ⟨i, hi, heq⟩ := (FUNCT_1.def3 hf.2).mp hy
    exact heq ▸ h i hi

/-- `FINSET_1:def 5`: defined-function form of finite-yielding. -/
theorem def5 {I f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hdef : RELAT_1.dom f ⊆ I) :
    isFiniteYielding f ↔ ∀ i, i ∈ I → isFinite (FUNCT_1.apply f i) := by
  constructor
  · intro h i _
    by_cases hi : i ∈ RELAT_1.dom f
    · exact (def4 hf).mp h i hi
    · rw [FUNCT_1.apply_of_not_mem hi]
      exact empty_isFinite
  · intro h
    exact (def4 hf).mpr (fun i hi => h i (hdef i hi))

/-- `FINSET_1:15` (unlabeled). -/
theorem th15 {A B : TarskiSet.{u}} (hB : isInfinite B) :
    B ∉ ZFMISC_1.product A B := by
  intro h
  obtain ⟨x, hxA, hEq⟩ := ZFMISC_1.th129 h
  have hp : isFinite (TARSKI.pair x (TARSKI.singleton x)) := by
    rw [TARSKI.pair_eq]
    exact upair_isFinite (TARSKI.upair x (TARSKI.singleton x))
      (TARSKI.singleton x)
  exact hB (Eq.subst (motive := isFinite) hEq.symm hp)

/-- `FINSET_1:def 6`: finite-membered families. -/
def isFiniteMembered (A : TarskiSet.{u}) : Prop :=
  ∀ B, B ∈ A → isFinite B

theorem def6 (A : TarskiSet.{u}) :
    isFiniteMembered A ↔ ∀ B, B ∈ A → isFinite B :=
  Iff.rfl

/-! ## Registration claims and redefinitions -/

/-- Registration: a finite nonempty function exists. -/
theorem exists_nonempty_finite_function :
    ∃ f : TarskiSet.{u}, FUNCT_1.isFunction f ∧
      f ≠ (∅ : TarskiSet.{u}) ∧ isFinite f := by
  let f := FUNCOP_1.mapsTo (TARSKI.singleton (∅ : TarskiSet.{u}))
    (∅ : TarskiSet.{u})
  refine ⟨f, FUNCOP_1.mapsTo_isFunction _ _, ?_, ?_⟩
  · intro he
    have hd := FUNCOP_1.mapsTo_dom
      (TARSKI.singleton (∅ : TarskiSet.{u})) (∅ : TarskiSet.{u})
    change RELAT_1.dom f = TARSKI.singleton (∅ : TarskiSet.{u}) at hd
    rw [he, RELAT_1.th38.1] at hd
    have hm : (∅ : TarskiSet.{u}) ∈ TARSKI.singleton (∅ : TarskiSet.{u}) :=
      (singleton_iff _ _).mpr rfl
    exact (XBOOLE_0.empty_iff (∅ : TarskiSet.{u})).mp
      (Eq.subst (motive := fun s => (∅ : TarskiSet.{u}) ∈ s) hd.symm hm)
  · apply (th10 (FUNCOP_1.mapsTo_isFunction _ _)).mp
    rw [FUNCOP_1.mapsTo_dom]
    exact lm1 _

private theorem finite_relation_projections {R : TarskiSet.{u}}
    (hR : RELAT_1.isRelation R) (hfin : isFinite R) :
    isFinite (RELAT_1.dom R) ∧ isFinite (RELAT_1.rng R) := by
  obtain ⟨A, B, hA, _, hB, _, hRAB⟩ := th13 hfin (RELAT_1.th7 hR)
  constructor
  · exact th1 (fun x hx =>
      let ⟨y, hp⟩ := (RELAT_1.dom_iff R x).mp hx
      (ZFMISC_1.th87).mp (hRAB _ hp) |>.1) hA
  · exact th1 (fun y hy =>
      let ⟨x, hp⟩ := (RELAT_1.rng_iff R y).mp hy
      (ZFMISC_1.th87).mp (hRAB _ hp) |>.2) hB

/-- Registration: the domain of a finite relation is finite. -/
theorem finite_relation_dom {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hfin : isFinite R) : isFinite (RELAT_1.dom R) :=
  (finite_relation_projections hR hfin).1

/-- Registration: the range of a finite relation is finite. -/
theorem finite_relation_rng {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hfin : isFinite R) : isFinite (RELAT_1.rng R) :=
  (finite_relation_projections hR hfin).2

/-- Registration: composition with a finite function is finite. -/
theorem comp_finite {f g : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) (hgfin : isFinite g) :
    isFinite (RELAT_1.comp g f) := by
  apply (th10 (FUNCT_1.comp_isFunction hg hf)).mp
  exact th1 RELAT_1.th25 ((th10 hg).mpr hgfin)

/-- Registration: every function with finite prescribed domain is finite. -/
theorem functionOf_finite {A B f : TarskiSet.{u}} (hA : isFinite A)
    (hf : FUNCT_2.isFunctionOf f A B)
    (hB : B ≠ (∅ : TarskiSet.{u})) : isFinite f := by
  apply (th10 (FUNCT_2.functionOf_isFunction hf)).mp
  rw [FUNCT_2.functionOf_dom_eq hf hB]
  exact hA

/-- Registration: a constant map on a finite set is finite. -/
theorem mapsTo_finite {A x : TarskiSet.{u}} (hA : isFinite A) :
    isFinite (FUNCOP_1.mapsTo A x) := by
  apply (th10 (FUNCOP_1.mapsTo_isFunction A x)).mp
  rw [FUNCOP_1.mapsTo_dom]
  exact hA

/-- Registration: inverse images of singleton values under finite functions
are finite. -/
theorem singleton_invimage_finite {f x : TarskiSet.{u}}
    (hf : FUNCT_1.isFunction f) (hfin : isFinite f) :
    isFinite (RELAT_1.invimage f (TARSKI.singleton x)) :=
  th1 RELAT_1.th132 ((th10 hf).mpr hfin)

/-- Registration: overriding finite functions preserves finiteness. -/
theorem override_finite {f g : TarskiSet.{u}}
    (hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (hff : isFinite f) (hgf : isFinite g) :
    isFinite (FUNCT_4.override f g) := by
  apply (th10 (FUNCT_4.override_isFunction f g)).mp
  rw [FUNCT_4.override_dom]
  exact lm2 ((th10 hf).mpr hff) ((th10 hg).mpr hgf)

/-- Registration: the two-point map is finite. -/
theorem pairMapsTo_finite (x y a b : TarskiSet.{u}) :
    isFinite (FUNCT_4.pairMapsTo x y a b) := by
  apply (th10 (FUNCT_4.pairMapsTo_isFunction x y a b)).mp
  rw [(FUNCT_4.th62 x y a b).1]
  exact upair_isFinite x y

/-- Registration: range restriction of a finite relation is finite. -/
theorem restrictRng_finite {A R : TarskiSet.{u}}
    (hfin : isFinite R) : isFinite (RELAT_1.restrictRng A R) :=
  th1 RELAT_1.th86 hfin

/-- Registration: domain restriction of a finite relation is finite. -/
theorem restrict_finite_relation {A R : TarskiSet.{u}}
    (hfin : isFinite R) : isFinite (RELAT_1.restrict R A) :=
  th1 RELAT_1.th59 hfin

/-- Registration: restriction to a finite set is a finite function. -/
theorem restrict_finite_domain {A f : TarskiSet.{u}}
    (hf : FUNCT_1.isFunction f) (hA : isFinite A) :
    isFinite (RELAT_1.restrict f A) := by
  apply (th10 (FUNCT_1.restrict_isFunction hf)).mp
  exact th1 RELAT_1.th58 hA

/-- Registration: the field of a finite relation is finite. -/
theorem field_finite {R : TarskiSet.{u}} (hR : RELAT_1.isRelation R)
    (hfin : isFinite R) : isFinite (RELAT_1.field R) := by
  unfold RELAT_1.field
  exact lm2 (finite_relation_dom hR hfin) (finite_relation_rng hR hfin)

/-- Registration: every trivial set is finite. -/
theorem trivial_isFinite {S : TarskiSet.{u}} (htr : ZFMISC_1.isTrivial S) :
    isFinite S := by
  by_cases he : S = (∅ : TarskiSet.{u})
  · rw [he]; exact empty_isFinite
  · obtain ⟨x, hx⟩ := XBOOLE_0.th7 he
    have hs : S = TARSKI.singleton x := by
      apply eq_of_mem
      intro y
      constructor
      · intro hy; exact (singleton_iff x y).mpr (htr y x hy hx)
      · intro hy; exact (singleton_iff x y).mp hy ▸ hx
    rw [hs]; exact lm1 x

/-- Registration: infinite sets are nontrivial. -/
theorem infinite_nontrivial {S : TarskiSet.{u}} (hinf : isInfinite S) :
    ¬ ZFMISC_1.isTrivial S :=
  fun h => hinf (trivial_isFinite h)

/-- Registration: a nontrivial set has a finite nontrivial subset. -/
theorem exists_finite_nontrivial_subset {X : TarskiSet.{u}}
    (hX : ¬ ZFMISC_1.isTrivial X) :
    ∃ A, A ⊆ X ∧ isFinite A ∧ ¬ ZFMISC_1.isTrivial A := by
  have hex : ∃ a b, a ∈ X ∧ b ∈ X ∧ a ≠ b := by
    apply Classical.byContradiction
    intro hn
    apply hX
    intro a b ha hb
    exact Classical.byContradiction (fun hab =>
      hn ⟨a, b, ha, hb, hab⟩)
  obtain ⟨a, b, ha, hb, hab⟩ := hex
  refine ⟨TARSKI.upair a b, (ZFMISC_1.th32).2 ⟨ha, hb⟩,
    upair_isFinite a b, ?_⟩
  intro htr
  exact hab (htr a b ((upair_iff _ _ _).mpr (Or.inl rfl))
    ((upair_iff _ _ _).mpr (Or.inr rfl)))

/-- Registration: the empty set is finite-membered. -/
theorem empty_finiteMembered :
    isFiniteMembered (∅ : TarskiSet.{u}) :=
  fun B h => ((XBOOLE_0.empty_iff B).mp h).elim

/-- Registration: members of finite-membered families are finite. -/
theorem member_of_finiteMembered {A B : TarskiSet.{u}}
    (hA : isFiniteMembered A) (hB : B ∈ A) : isFinite B :=
  hA B hB

/-- Registration: a nonempty finite finite-membered set exists. -/
theorem exists_nonempty_finite_finiteMembered :
    ∃ A : TarskiSet.{u}, A ≠ (∅ : TarskiSet.{u}) ∧
      isFinite A ∧ isFiniteMembered A := by
  refine ⟨TARSKI.singleton (TARSKI.singleton (∅ : TarskiSet.{u})),
    ?_, lm1 _, ?_⟩
  · intro h
    have hm : TARSKI.singleton (∅ : TarskiSet.{u}) ∈
        TARSKI.singleton (TARSKI.singleton (∅ : TarskiSet.{u})) :=
      (singleton_iff _ _).mpr rfl
    exact (XBOOLE_0.empty_iff _).mp
      (Eq.subst (motive := fun s =>
        TARSKI.singleton (∅ : TarskiSet.{u}) ∈ s) h hm)
  · intro B hB
    exact Eq.subst (motive := isFinite) ((singleton_iff _ B).mp hB).symm
      (lm1 _)

/-- Registration: singleton families of finite sets are finite-membered. -/
theorem singleton_finiteMembered {X : TarskiSet.{u}} (hX : isFinite X) :
    isFiniteMembered (TARSKI.singleton X) :=
  fun Y hY => Eq.subst (motive := isFinite) ((singleton_iff X Y).mp hY).symm hX

/-- Registration: the power set of a finite set is finite-membered. -/
theorem bool_finiteMembered {X : TarskiSet.{u}} (hX : isFinite X) :
    isFiniteMembered (ZFMISC_1.bool X) :=
  fun Y hY => th1 ((ZFMISC_1.def1 X Y).mp hY) hX

/-- Registration: unordered pairs of finite sets are finite-membered. -/
theorem upair_finiteMembered {X Y : TarskiSet.{u}}
    (hX : isFinite X) (hY : isFinite Y) :
    isFiniteMembered (TARSKI.upair X Y) := by
  intro Z hZ
  rcases (upair_iff X Y Z).mp hZ with h | h
  · exact h ▸ hX
  · exact h ▸ hY

/-- Registration: subsets preserve finite-memberedness. -/
theorem subset_finiteMembered {S X : TarskiSet.{u}} (hSX : S ⊆ X)
    (hX : isFiniteMembered X) : isFiniteMembered S :=
  fun z hz => hX z (hSX z hz)

/-- Registration: unions preserve finite-memberedness. -/
theorem union_finiteMembered {X Y : TarskiSet.{u}}
    (hX : isFiniteMembered X) (hY : isFiniteMembered Y) :
    isFiniteMembered (X ∪ Y) := by
  intro z hz
  rcases (XBOOLE_0.def3 X Y z).mp hz with h | h
  · exact hX z h
  · exact hY z h

/-- Registration: union of a finite finite-membered family is finite. -/
theorem union_finite_finiteMembered {X : TarskiSet.{u}}
    (hX : isFinite X) (hm : isFiniteMembered X) :
    isFinite (TARSKI.union X) :=
  lm3 hX hm

/-- Registration: a nonempty finite-yielding function exists. -/
theorem exists_nonempty_finiteYielding_function :
    ∃ f : TarskiSet.{u}, FUNCT_1.isFunction f ∧
      f ≠ (∅ : TarskiSet.{u}) ∧ isFiniteYielding f := by
  let f := FUNCOP_1.mapsTo (TARSKI.singleton (∅ : TarskiSet.{u}))
    (TARSKI.singleton (∅ : TarskiSet.{u}))
  refine ⟨f, FUNCOP_1.mapsTo_isFunction _ _, ?_, (def4
    (FUNCOP_1.mapsTo_isFunction _ _)).mpr ?_⟩
  · intro he
    have hd := FUNCOP_1.mapsTo_dom
      (TARSKI.singleton (∅ : TarskiSet.{u}))
      (TARSKI.singleton (∅ : TarskiSet.{u}))
    change RELAT_1.dom f = TARSKI.singleton (∅ : TarskiSet.{u}) at hd
    rw [he, RELAT_1.th38.1] at hd
    have hm : (∅ : TarskiSet.{u}) ∈ TARSKI.singleton (∅ : TarskiSet.{u}) :=
      (singleton_iff _ _).mpr rfl
    exact (XBOOLE_0.empty_iff (∅ : TarskiSet.{u})).mp
      (Eq.subst (motive := fun s => (∅ : TarskiSet.{u}) ∈ s) hd.symm hm)
  · intro i hi
    rw [FUNCOP_1.th7 (Eq.subst (motive := fun s => i ∈ s)
      (FUNCOP_1.mapsTo_dom _ _)
      hi)]
    exact lm1 _

/-- Registration: empty relations are finite-yielding. -/
theorem empty_relation_finiteYielding {R : TarskiSet.{u}}
    (hR : R = (∅ : TarskiSet.{u})) : isFiniteYielding R := by
  intro x hx
  exact ((XBOOLE_0.empty_iff x).mp
    (Eq.subst (motive := fun s => x ∈ s)
      (hR ▸ RELAT_1.th38.2) hx)).elim

/-- Registration: every value of a finite-yielding function is finite. -/
theorem apply_finiteYielding {F x : TarskiSet.{u}}
    (hF : FUNCT_1.isFunction F) (hy : isFiniteYielding F) :
    isFinite (FUNCT_1.apply F x) := by
  by_cases hx : x ∈ RELAT_1.dom F
  · exact (def4 hF).mp hy x hx
  · rw [FUNCT_1.apply_of_not_mem hx]
    exact empty_isFinite

/-- Registration: the range of a finite-yielding relation is
finite-membered. -/
theorem range_finiteMembered {F : TarskiSet.{u}}
    (hF : isFiniteYielding F) :
    isFiniteMembered (RELAT_1.rng F) :=
  hF

/-- Registration: a finite `I`-defined function compatible with a given
function exists. -/
theorem exists_finite_defined_compatible (I f : TarskiSet.{u}) :
    ∃ g, FUNCT_1.isFunction g ∧ isFinite g ∧
      RELAT_1.isXdefined g I ∧ FUNCT_1.isCompatible g f :=
  ⟨∅, FUNCT_1.empty_isFunction, empty_isFinite,
    (RELAT_1.th171 (X := I) (Y := I)).1, FUNCT_1.th104 f⟩

/-- Registration: a finite `X`-defined, `Y`-valued function exists. -/
theorem exists_finite_defined_valued (X Y : TarskiSet.{u}) :
    ∃ f, FUNCT_1.isFunction f ∧ isFinite f ∧
      RELAT_1.isXdefined f X ∧ RELAT_1.isXvalued f Y :=
  ⟨∅, FUNCT_1.empty_isFunction, empty_isFinite,
    (RELAT_1.th171 (X := X) (Y := Y)).1,
    (RELAT_1.th171 (X := X) (Y := Y)).2⟩

/-- Registration: for nonempty `X,Y`, a nonempty finite `X`-defined,
`Y`-valued function exists. -/
theorem exists_nonempty_finite_defined_valued {X Y : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u})) :
    ∃ f, FUNCT_1.isFunction f ∧ f ≠ (∅ : TarskiSet.{u}) ∧ isFinite f ∧
      RELAT_1.isXdefined f X ∧ RELAT_1.isXvalued f Y := by
  obtain ⟨x, hx⟩ := XBOOLE_0.th7 hX
  obtain ⟨y, hy⟩ := XBOOLE_0.th7 hY
  let f := FUNCOP_1.dotArrow x y
  refine ⟨f, FUNCOP_1.dotArrow_isFunction x y, ?_,
    mapsTo_finite (lm1 x), ?_, ?_⟩
  · intro he
    have hd := FUNCOP_1.mapsTo_dom (TARSKI.singleton x) y
    change RELAT_1.dom f = TARSKI.singleton x at hd
    rw [he, RELAT_1.th38.1] at hd
    have hm : x ∈ TARSKI.singleton x := (singleton_iff x x).mpr rfl
    exact (XBOOLE_0.empty_iff x).mp
      (Eq.subst (motive := fun s => x ∈ s) hd.symm hm)
  · exact XBOOLE_1.th1 (FUNCOP_1.dotArrow_isXdefined x y)
      ((ZFMISC_1.th31).2 hx)
  · have hr : RELAT_1.rng f = TARSKI.singleton y := FUNCOP_1.th88 x y
    exact Eq.subst (motive := fun s => s ⊆ Y) hr.symm
      ((ZFMISC_1.th31).2 hy)

end FINSET_1


