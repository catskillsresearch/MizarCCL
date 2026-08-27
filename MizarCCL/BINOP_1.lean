import MizarCCL.FUNCT_2

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/binop_1.miz`.
Authors: Czesław Byliński (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Binary Operations

1–1 Lean rendering of Mizar article `BINOP_1`
(`vendor/mml/binop_1.miz`). Import is `FUNCT_2` only. Canceled
redefines of commutative / associative / idempotent (3) are omitted.
-/

universe u

open TarskiSet TARSKI

namespace BINOP_1

/-! ## `f.(a,b)` (`BINOP_1:def 1`) -/

/-- `BINOP_1:def 1` — binary application `f.(a,b) = f.[a,b]`. -/
noncomputable def apply2 (f a b : TarskiSet.{u}) : TarskiSet.{u} :=
  FUNCT_1.apply f (TARSKI.pair a b)

theorem def1 (f a b : TarskiSet.{u}) :
    apply2 f a b = FUNCT_1.apply f (TARSKI.pair a b) :=
  rfl

private theorem apply2_of_empty_fun {f a b : TarskiSet.{u}}
    (hf : f = (∅ : TarskiSet.{u})) : apply2 f a b = (∅ : TarskiSet.{u}) := by
  have hdom : TARSKI.pair a b ∉ RELAT_1.dom f := by
    intro hx
    have hx' : TARSKI.pair a b ∈ RELAT_1.dom (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => TARSKI.pair a b ∈ RELAT_1.dom s) hf hx
    have hx'' : TARSKI.pair a b ∈ (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => TARSKI.pair a b ∈ s) RELAT_1.th38.1 hx'
    exact (XBOOLE_0.empty_iff _).mp hx''
  exact FUNCT_1.apply_of_not_mem hdom

private theorem ne_imp_not_empty {A : TarskiSet.{u}}
    (h : A ≠ (∅ : TarskiSet.{u})) : ¬ XBOOLE_0.isEmpty A :=
  fun he => h (XBOOLE_0.empty_eq he)

private theorem apply2_congr {o x1 x2 y1 y2 : TarskiSet.{u}}
    (hx : x1 = x2) (hy : y1 = y2) :
    apply2 o x1 y1 = apply2 o x2 y2 :=
  Eq.subst (motive := fun s => apply2 o x1 y1 = apply2 o s y2) hx
    (Eq.subst (motive := fun s => apply2 o x1 y1 = apply2 o x1 s) hy rfl)

/-- Coherence: `Function of [:A,B:],C` with nonempty `A`,`B` yields
`Element of C`. -/
theorem apply2_isElement {A B C f a b : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u})) (hB : B ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f (ZFMISC_1.product A B) C)
    (ha : SUBSET_1.isElement a A) (hb : SUBSET_1.isElement b B) :
    SUBSET_1.isElement (apply2 f a b) C := by
  have ha' : a ∈ A := SUBSET_1.isElement_mem (ne_imp_not_empty hA) ha
  have hb' : b ∈ B := SUBSET_1.isElement_mem (ne_imp_not_empty hB) hb
  have hab : TARSKI.pair a b ∈ ZFMISC_1.product A B :=
    (ZFMISC_1.th87 (x := a) (y := b) (X := A) (Y := B)).mpr ⟨ha', hb'⟩
  have := Classical.propDecidable (C = (∅ : TarskiSet.{u}))
  by_cases hC : C = (∅ : TarskiSet.{u})
  · have hempty : f = (∅ : TarskiSet.{u}) := FUNCT_2.functionOf_empty_cod hf hC
    exact Eq.subst (motive := fun s => SUBSET_1.isElement s C)
      (apply2_of_empty_fun hempty).symm
      ((SUBSET_1.isElement_iff_empty (x := ∅) (X := C)
        (hC ▸ XBOOLE_0.emptySet_isEmpty)).mpr XBOOLE_0.emptySet_isEmpty)
  · exact SUBSET_1.isElement_of (FUNCT_2.th5 hf hC hab)

/-! ## Equality of binary functions -/

/-- `BINOP_1:1` (`Th1`) -/
theorem th1 {X Y Z f1 f2 : TarskiSet.{u}}
    (h1 : FUNCT_2.isFunctionOf f1 (ZFMISC_1.product X Y) Z)
    (h2 : FUNCT_2.isFunctionOf f2 (ZFMISC_1.product X Y) Z)
    (hv : ∀ x y, x ∈ X → y ∈ Y → apply2 f1 x y = apply2 f2 x y) :
    f1 = f2 := by
  refine FUNCT_2.th12 h1 h2 ?_
  intro z hz
  obtain ⟨x, y, hx, hy, heq⟩ := (ZFMISC_1.def2 X Y z).mp hz
  exact Eq.subst (motive := fun s =>
      FUNCT_1.apply f1 s = FUNCT_1.apply f2 s) heq.symm (hv x y hx hy)

/-- Unlabeled `BINOP_1` after `Th1` -/
theorem th2 {X Y Z f1 f2 : TarskiSet.{u}}
    (h1 : FUNCT_2.isFunctionOf f1 (ZFMISC_1.product X Y) Z)
    (h2 : FUNCT_2.isFunctionOf f2 (ZFMISC_1.product X Y) Z)
    (hv : ∀ a b, SUBSET_1.isElement a X → SUBSET_1.isElement b Y →
      apply2 f1 a b = apply2 f2 a b) :
    f1 = f2 :=
  th1 h1 h2 fun x y hx hy =>
    hv x y (SUBSET_1.isElement_of hx) (SUBSET_1.isElement_of hy)

/-! ## Modes `UnOp of A`, `BinOp of A` -/

/-- Mode `UnOp of A` — `Function of A,A`. -/
def isUnOp (f A : TarskiSet.{u}) : Prop :=
  FUNCT_2.isFunctionOf f A A

/-- Mode `BinOp of A` — `Function of [:A,A:],A`. -/
def isBinOp (f A : TarskiSet.{u}) : Prop :=
  FUNCT_2.isFunctionOf f (ZFMISC_1.product A A) A

/-- Coherence: `BinOp of A` yields `Element of A` under `f.(a,b)`. -/
theorem apply2_binop_isElement {A f a b : TarskiSet.{u}}
    (hf : isBinOp f A)
    (ha : SUBSET_1.isElement a A) (hb : SUBSET_1.isElement b A) :
    SUBSET_1.isElement (apply2 f a b) A := by
  have := Classical.propDecidable (A = (∅ : TarskiSet.{u}))
  by_cases hA : A = (∅ : TarskiSet.{u})
  · have hempty : f = (∅ : TarskiSet.{u}) :=
      FUNCT_2.functionOf_empty_cod hf hA
    exact Eq.subst (motive := fun s => SUBSET_1.isElement s A)
      (apply2_of_empty_fun hempty).symm
      ((SUBSET_1.isElement_iff_empty (x := ∅) (X := A)
        (hA ▸ XBOOLE_0.emptySet_isEmpty)).mpr XBOOLE_0.emptySet_isEmpty)
  · exact apply2_isElement hA hA hf ha hb

/-! ## Schemes `FuncEx2`, `Lambda2`, `FuncEx2D`, `Lambda2D` -/

/-- `BINOP_1:sch FuncEx2` -/
theorem sch_FuncEx2 (X Y Z : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hP : ∀ x y, x ∈ X → y ∈ Y → ∃ z, z ∈ Z ∧ P x y z) :
    ∃ f, FUNCT_2.isFunctionOf f (ZFMISC_1.product X Y) Z ∧
      ∀ x y, x ∈ X → y ∈ Y → P x y (apply2 f x y) := by
  let R : TarskiSet.{u} → TarskiSet.{u} → Prop :=
    fun p w => ∀ x1 y1, p = TARSKI.pair x1 y1 → P x1 y1 w
  have hR : ∀ p, p ∈ ZFMISC_1.product X Y → ∃ z, z ∈ Z ∧ R p z := by
    intro p hp
    obtain ⟨x1, y1, hx, hy, heq⟩ := (ZFMISC_1.def2 X Y p).mp hp
    obtain ⟨z, hz, hPz⟩ := hP x1 y1 hx hy
    refine ⟨z, hz, ?_⟩
    intro x2 y2 heq2
    have ⟨hxeq, hyeq⟩ := XTUPLE_0.th1 (heq.symm.trans heq2)
    exact Eq.subst (motive := fun s => P s y2 z) hxeq
      (Eq.subst (motive := fun s => P x1 s z) hyeq hPz)
  obtain ⟨f, hf, hv⟩ := FUNCT_2.sch_FuncEx1 (ZFMISC_1.product X Y) Z R hR
  refine ⟨f, hf, ?_⟩
  intro x y hx hy
  have hp : TARSKI.pair x y ∈ ZFMISC_1.product X Y :=
    (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mpr ⟨hx, hy⟩
  exact hv (TARSKI.pair x y) hp x y rfl

/-- `BINOP_1:sch Lambda2` -/
theorem sch_Lambda2 (X Y Z : TarskiSet.{u})
    (F : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ x y, x ∈ X → y ∈ Y → F x y ∈ Z) :
    ∃ f, FUNCT_2.isFunctionOf f (ZFMISC_1.product X Y) Z ∧
      ∀ x y, x ∈ X → y ∈ Y → apply2 f x y = F x y :=
  sch_FuncEx2 X Y Z (fun x y z => z = F x y)
    (fun x y hx hy => ⟨F x y, hF x y hx hy, rfl⟩)

/-- `BINOP_1:sch FuncEx2D` -/
theorem sch_FuncEx2D (X Y Z : TarskiSet.{u})
    (_hX : X ≠ (∅ : TarskiSet.{u})) (_hY : Y ≠ (∅ : TarskiSet.{u}))
    (_hZ : Z ≠ (∅ : TarskiSet.{u}))
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hP : ∀ x y, x ∈ X → y ∈ Y → ∃ z, z ∈ Z ∧ P x y z) :
    ∃ f, FUNCT_2.isFunctionOf f (ZFMISC_1.product X Y) Z ∧
      ∀ x y, x ∈ X → y ∈ Y → P x y (apply2 f x y) :=
  sch_FuncEx2 X Y Z P hP

/-- `BINOP_1:sch Lambda2D` -/
theorem sch_Lambda2D (X Y Z : TarskiSet.{u})
    (_hX : X ≠ (∅ : TarskiSet.{u})) (_hY : Y ≠ (∅ : TarskiSet.{u}))
    (_hZ : Z ≠ (∅ : TarskiSet.{u}))
    (F : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ x y, x ∈ X → y ∈ Y → F x y ∈ Z) :
    ∃ f, FUNCT_2.isFunctionOf f (ZFMISC_1.product X Y) Z ∧
      ∀ x y, x ∈ X → y ∈ Y → apply2 f x y = F x y :=
  sch_Lambda2 X Y Z F hF

/-! ## Attributes commutative / associative / idempotent -/

/-- `BINOP_1:def 2` -/
def isCommutative (o A : TarskiSet.{u}) : Prop :=
  ∀ a b, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
    apply2 o a b = apply2 o b a

theorem def2 (o A : TarskiSet.{u}) :
    isCommutative o A ↔
      ∀ a b, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
        apply2 o a b = apply2 o b a :=
  Iff.rfl

/-- `BINOP_1:def 3` -/
def isAssociative (o A : TarskiSet.{u}) : Prop :=
  ∀ a b c, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
    SUBSET_1.isElement c A →
    apply2 o a (apply2 o b c) = apply2 o (apply2 o a b) c

theorem def3 (o A : TarskiSet.{u}) :
    isAssociative o A ↔
      ∀ a b c, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
        SUBSET_1.isElement c A →
        apply2 o a (apply2 o b c) = apply2 o (apply2 o a b) c :=
  Iff.rfl

/-- `BINOP_1:def 4` -/
def isIdempotent (o A : TarskiSet.{u}) : Prop :=
  ∀ a, SUBSET_1.isElement a A → apply2 o a a = a

theorem def4 (o A : TarskiSet.{u}) :
    isIdempotent o A ↔
      ∀ a, SUBSET_1.isElement a A → apply2 o a a = a :=
  Iff.rfl

/-- Registration: `BinOp of {}` is empty, associative, commutative. -/
theorem empty_binop_cluster {f : TarskiSet.{u}}
    (hf : isBinOp f (∅ : TarskiSet.{u})) :
    XBOOLE_0.isEmpty f ∧
      isAssociative f (∅ : TarskiSet.{u}) ∧
      isCommutative f (∅ : TarskiSet.{u}) := by
  have hempty : f = (∅ : TarskiSet.{u}) :=
    FUNCT_2.functionOf_empty_cod hf rfl
  refine ⟨Eq.subst (motive := fun s => XBOOLE_0.isEmpty s) hempty.symm
      XBOOLE_0.emptySet_isEmpty, ?_, ?_⟩
  · intro a b c _ _ _
    exact (apply2_of_empty_fun hempty (a := a) (b := apply2 f b c)).trans
      (apply2_of_empty_fun hempty (a := apply2 f a b) (b := c)).symm
  · intro a b _ _
    exact (apply2_of_empty_fun hempty (a := a) (b := b)).trans
      (apply2_of_empty_fun hempty (a := b) (b := a)).symm

/-! ## Unity predicates -/

/-- `BINOP_1:def 5` -/
def is_a_left_unity_wrt (e o A : TarskiSet.{u}) : Prop :=
  ∀ a, SUBSET_1.isElement a A → apply2 o e a = a

theorem def5 (e o A : TarskiSet.{u}) :
    is_a_left_unity_wrt e o A ↔
      ∀ a, SUBSET_1.isElement a A → apply2 o e a = a :=
  Iff.rfl

/-- `BINOP_1:def 6` -/
def is_a_right_unity_wrt (e o A : TarskiSet.{u}) : Prop :=
  ∀ a, SUBSET_1.isElement a A → apply2 o a e = a

theorem def6 (e o A : TarskiSet.{u}) :
    is_a_right_unity_wrt e o A ↔
      ∀ a, SUBSET_1.isElement a A → apply2 o a e = a :=
  Iff.rfl

/-- `BINOP_1:def 7` -/
def is_a_unity_wrt (e o A : TarskiSet.{u}) : Prop :=
  is_a_left_unity_wrt e o A ∧ is_a_right_unity_wrt e o A

theorem def7 (e o A : TarskiSet.{u}) :
    is_a_unity_wrt e o A ↔
      is_a_left_unity_wrt e o A ∧ is_a_right_unity_wrt e o A :=
  Iff.rfl

/-- `BINOP_1:3` (`Th3`) -/
theorem th3 {A e o : TarskiSet.{u}} :
    is_a_unity_wrt e o A ↔
      ∀ a, SUBSET_1.isElement a A →
        apply2 o e a = a ∧ apply2 o a e = a := by
  constructor
  · intro ⟨hl, hr⟩ a ha
    exact ⟨hl a ha, hr a ha⟩
  · intro h
    exact ⟨fun a ha => (h a ha).1, fun a ha => (h a ha).2⟩

/-- `BINOP_1:4` (`Th4`) -/
theorem th4 {A e o : TarskiSet.{u}} (he : SUBSET_1.isElement e A)
    (hc : isCommutative o A) :
    is_a_unity_wrt e o A ↔
      ∀ a, SUBSET_1.isElement a A → apply2 o e a = a := by
  constructor
  · intro hu a ha
    exact (th3.mp hu a ha).1
  · intro hl
    refine th3.mpr fun a ha => ⟨hl a ha, ?_⟩
    exact (hc a e ha he).trans (hl a ha)

/-- `BINOP_1:5` (`Th5`) -/
theorem th5 {A e o : TarskiSet.{u}} (he : SUBSET_1.isElement e A)
    (hc : isCommutative o A) :
    is_a_unity_wrt e o A ↔
      ∀ a, SUBSET_1.isElement a A → apply2 o a e = a := by
  constructor
  · intro hu a ha
    exact (th3.mp hu a ha).2
  · intro hr
    refine th3.mpr fun a ha => ⟨?_, hr a ha⟩
    exact (hc e a he ha).trans (hr a ha)

/-- `BINOP_1:6` (`Th6`) -/
theorem th6 {A e o : TarskiSet.{u}} (he : SUBSET_1.isElement e A)
    (hc : isCommutative o A) :
    is_a_unity_wrt e o A ↔ is_a_left_unity_wrt e o A :=
  th4 he hc

/-- `BINOP_1:7` (`Th7`) -/
theorem th7 {A e o : TarskiSet.{u}} (he : SUBSET_1.isElement e A)
    (hc : isCommutative o A) :
    is_a_unity_wrt e o A ↔ is_a_right_unity_wrt e o A :=
  th5 he hc

/-- Unlabeled `BINOP_1` after `Th7` -/
theorem th8 {A e o : TarskiSet.{u}} (he : SUBSET_1.isElement e A)
    (hc : isCommutative o A) :
    is_a_left_unity_wrt e o A ↔ is_a_right_unity_wrt e o A :=
  Iff.trans (th6 he hc).symm (th7 he hc)

/-- `BINOP_1:9` (`Th9`) -/
theorem th9 {A e1 e2 o : TarskiSet.{u}}
    (he1 : SUBSET_1.isElement e1 A) (he2 : SUBSET_1.isElement e2 A)
    (hl : is_a_left_unity_wrt e1 o A)
    (hr : is_a_right_unity_wrt e2 o A) : e1 = e2 :=
  (hr e1 he1).symm.trans (hl e2 he2)

/-- `BINOP_1:10` (`Th10`) -/
theorem th10 {A e1 e2 o : TarskiSet.{u}}
    (he1 : SUBSET_1.isElement e1 A) (he2 : SUBSET_1.isElement e2 A)
    (h1 : is_a_unity_wrt e1 o A) (h2 : is_a_unity_wrt e2 o A) : e1 = e2 :=
  (th9 he2 he1 h2.1 h1.2).symm

/-- `BINOP_1:def 8` — conditional `the_unity_wrt`. -/
noncomputable def the_unity_wrt {A o : TarskiSet.{u}}
    (h : ∃ e, SUBSET_1.isElement e A ∧ is_a_unity_wrt e o A) :
    TarskiSet.{u} :=
  Classical.choose h

theorem the_unity_wrt_isElement {A o : TarskiSet.{u}}
    (h : ∃ e, SUBSET_1.isElement e A ∧ is_a_unity_wrt e o A) :
    SUBSET_1.isElement (the_unity_wrt h) A :=
  (Classical.choose_spec h).1

theorem def8 {A o : TarskiSet.{u}}
    (h : ∃ e, SUBSET_1.isElement e A ∧ is_a_unity_wrt e o A) :
    is_a_unity_wrt (the_unity_wrt h) o A :=
  (Classical.choose_spec h).2

/-! ## Distributivity -/

/-- `BINOP_1:def 9` -/
def is_left_distributive_wrt (o9 o A : TarskiSet.{u}) : Prop :=
  ∀ a b c, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
    SUBSET_1.isElement c A →
    apply2 o9 a (apply2 o b c) = apply2 o (apply2 o9 a b) (apply2 o9 a c)

theorem def9 (o9 o A : TarskiSet.{u}) :
    is_left_distributive_wrt o9 o A ↔
      ∀ a b c, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
        SUBSET_1.isElement c A →
        apply2 o9 a (apply2 o b c) =
          apply2 o (apply2 o9 a b) (apply2 o9 a c) :=
  Iff.rfl

/-- `BINOP_1:def 10` -/
def is_right_distributive_wrt (o9 o A : TarskiSet.{u}) : Prop :=
  ∀ a b c, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
    SUBSET_1.isElement c A →
    apply2 o9 (apply2 o a b) c = apply2 o (apply2 o9 a c) (apply2 o9 b c)

theorem def10 (o9 o A : TarskiSet.{u}) :
    is_right_distributive_wrt o9 o A ↔
      ∀ a b c, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
        SUBSET_1.isElement c A →
        apply2 o9 (apply2 o a b) c =
          apply2 o (apply2 o9 a c) (apply2 o9 b c) :=
  Iff.rfl

/-- `BINOP_1:def 11` -/
def is_distributive_wrt (o9 o A : TarskiSet.{u}) : Prop :=
  is_left_distributive_wrt o9 o A ∧ is_right_distributive_wrt o9 o A

theorem def11 (o9 o A : TarskiSet.{u}) :
    is_distributive_wrt o9 o A ↔
      is_left_distributive_wrt o9 o A ∧ is_right_distributive_wrt o9 o A :=
  Iff.rfl

/-- `BINOP_1:11` (`Th11`) -/
theorem th11 {A o9 o : TarskiSet.{u}} :
    is_distributive_wrt o9 o A ↔
      ∀ a b c, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
        SUBSET_1.isElement c A →
        apply2 o9 a (apply2 o b c) =
            apply2 o (apply2 o9 a b) (apply2 o9 a c) ∧
          apply2 o9 (apply2 o a b) c =
            apply2 o (apply2 o9 a c) (apply2 o9 b c) := by
  constructor
  · intro ⟨hl, hr⟩ a b c ha hb hc
    exact ⟨hl a b c ha hb hc, hr a b c ha hb hc⟩
  · intro h
    exact ⟨fun a b c ha hb hc => (h a b c ha hb hc).1,
      fun a b c ha hb hc => (h a b c ha hb hc).2⟩

/-- `BINOP_1:12` (`Th12`) -/
theorem th12 {A o o9 : TarskiSet.{u}} (hA : A ≠ (∅ : TarskiSet.{u}))
    (ho : isBinOp o A) (_ho9 : isBinOp o9 A)
    (hc : isCommutative o9 A) :
    is_distributive_wrt o9 o A ↔
      ∀ a b c, a ∈ A → b ∈ A → c ∈ A →
        apply2 o9 a (apply2 o b c) =
          apply2 o (apply2 o9 a b) (apply2 o9 a c) := by
  have hAne := ne_imp_not_empty hA
  have toEl : ∀ x, x ∈ A → SUBSET_1.isElement x A :=
    fun _ hx => SUBSET_1.isElement_of hx
  have toMem : ∀ x, SUBSET_1.isElement x A → x ∈ A :=
    fun _ hx => SUBSET_1.isElement_mem hAne hx
  refine Iff.trans th11 ?_
  constructor
  · intro h a b c ha hb hc'
    exact (h a b c (toEl a ha) (toEl b hb) (toEl c hc')).1
  · intro hL a b c ha hb hc'
    have ha' := toMem a ha
    have hb' := toMem b hb
    have hc'' := toMem c hc'
    refine ⟨hL a b c ha' hb' hc'', ?_⟩
    have hab : SUBSET_1.isElement (apply2 o a b) A :=
      apply2_binop_isElement ho ha hb
    have step1 : apply2 o9 (apply2 o a b) c = apply2 o9 c (apply2 o a b) :=
      hc (apply2 o a b) c hab hc'
    have step2 : apply2 o9 c (apply2 o a b) =
        apply2 o (apply2 o9 c a) (apply2 o9 c b) :=
      hL c a b hc'' ha' hb'
    have step3 : apply2 o (apply2 o9 c a) (apply2 o9 c b) =
        apply2 o (apply2 o9 a c) (apply2 o9 c b) :=
      apply2_congr (hc c a hc' ha) rfl
    have step4 : apply2 o (apply2 o9 a c) (apply2 o9 c b) =
        apply2 o (apply2 o9 a c) (apply2 o9 b c) :=
      apply2_congr rfl (hc c b hc' hb)
    exact step1.trans (step2.trans (step3.trans step4))

/-- `BINOP_1:13` (`Th13`) -/
theorem th13 {A o o9 : TarskiSet.{u}} (hA : A ≠ (∅ : TarskiSet.{u}))
    (ho : isBinOp o A) (_ho9 : isBinOp o9 A)
    (hc : isCommutative o9 A) :
    is_distributive_wrt o9 o A ↔
      ∀ a b c, a ∈ A → b ∈ A → c ∈ A →
        apply2 o9 (apply2 o a b) c =
          apply2 o (apply2 o9 a c) (apply2 o9 b c) := by
  have hAne := ne_imp_not_empty hA
  have toEl : ∀ x, x ∈ A → SUBSET_1.isElement x A :=
    fun _ hx => SUBSET_1.isElement_of hx
  have toMem : ∀ x, SUBSET_1.isElement x A → x ∈ A :=
    fun _ hx => SUBSET_1.isElement_mem hAne hx
  refine Iff.trans th11 ?_
  constructor
  · intro h a b c ha hb hc'
    exact (h a b c (toEl a ha) (toEl b hb) (toEl c hc')).2
  · intro hR a b c ha hb hc'
    have ha' := toMem a ha
    have hb' := toMem b hb
    have hc'' := toMem c hc'
    refine ⟨?_, hR a b c ha' hb' hc''⟩
    have hbc : SUBSET_1.isElement (apply2 o b c) A :=
      apply2_binop_isElement ho hb hc'
    have step1 : apply2 o9 a (apply2 o b c) = apply2 o9 (apply2 o b c) a :=
      hc a (apply2 o b c) ha hbc
    have step2 : apply2 o9 (apply2 o b c) a =
        apply2 o (apply2 o9 b a) (apply2 o9 c a) :=
      hR b c a hb' hc'' ha'
    have step3 : apply2 o (apply2 o9 b a) (apply2 o9 c a) =
        apply2 o (apply2 o9 a b) (apply2 o9 c a) :=
      apply2_congr (hc b a hb ha) rfl
    have step4 : apply2 o (apply2 o9 a b) (apply2 o9 c a) =
        apply2 o (apply2 o9 a b) (apply2 o9 a c) :=
      apply2_congr rfl (hc c a hc' ha)
    exact step1.trans (step2.trans (step3.trans step4))

/-- `BINOP_1:14` (`Th14`) -/
theorem th14 {A o o9 : TarskiSet.{u}} (hA : A ≠ (∅ : TarskiSet.{u}))
    (ho : isBinOp o A) (ho9 : isBinOp o9 A)
    (hc : isCommutative o9 A) :
    is_distributive_wrt o9 o A ↔ is_left_distributive_wrt o9 o A := by
  have hAne := ne_imp_not_empty hA
  have toEl : ∀ x, x ∈ A → SUBSET_1.isElement x A :=
    fun _ hx => SUBSET_1.isElement_of hx
  have toMem : ∀ x, SUBSET_1.isElement x A → x ∈ A :=
    fun _ hx => SUBSET_1.isElement_mem hAne hx
  have hiff := th12 hA ho ho9 hc
  refine Iff.trans hiff ?_
  constructor
  · intro h a b c ha hb hc'
    exact h a b c (toMem a ha) (toMem b hb) (toMem c hc')
  · intro h a b c ha hb hc'
    exact h a b c (toEl a ha) (toEl b hb) (toEl c hc')

/-- `BINOP_1:15` (`Th15`) -/
theorem th15 {A o o9 : TarskiSet.{u}} (hA : A ≠ (∅ : TarskiSet.{u}))
    (ho : isBinOp o A) (ho9 : isBinOp o9 A)
    (hc : isCommutative o9 A) :
    is_distributive_wrt o9 o A ↔ is_right_distributive_wrt o9 o A := by
  have hAne := ne_imp_not_empty hA
  have toEl : ∀ x, x ∈ A → SUBSET_1.isElement x A :=
    fun _ hx => SUBSET_1.isElement_of hx
  have toMem : ∀ x, SUBSET_1.isElement x A → x ∈ A :=
    fun _ hx => SUBSET_1.isElement_mem hAne hx
  have hiff := th13 hA ho ho9 hc
  refine Iff.trans hiff ?_
  constructor
  · intro h a b c ha hb hc'
    exact h a b c (toMem a ha) (toMem b hb) (toMem c hc')
  · intro h a b c ha hb hc'
    exact h a b c (toEl a ha) (toEl b hb) (toEl c hc')

/-- Unlabeled `BINOP_1` after `Th15` -/
theorem th16 {A o o9 : TarskiSet.{u}} (hA : A ≠ (∅ : TarskiSet.{u}))
    (ho : isBinOp o A) (ho9 : isBinOp o9 A)
    (hc : isCommutative o9 A) :
    is_right_distributive_wrt o9 o A ↔ is_left_distributive_wrt o9 o A :=
  Iff.trans (th15 hA ho ho9 hc).symm (th14 hA ho ho9 hc)

/-- `BINOP_1:def 12` — unary distributive wrt binary. -/
def is_unOp_distributive_wrt (u o A : TarskiSet.{u}) : Prop :=
  ∀ a b, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
    FUNCT_1.apply u (apply2 o a b) =
      apply2 o (FUNCT_1.apply u a) (FUNCT_1.apply u b)

theorem def12 (u o A : TarskiSet.{u}) :
    is_unOp_distributive_wrt u o A ↔
      ∀ a b, SUBSET_1.isElement a A → SUBSET_1.isElement b A →
        FUNCT_1.apply u (apply2 o a b) =
          apply2 o (FUNCT_1.apply u a) (FUNCT_1.apply u b) :=
  Iff.rfl

/-! ## Addenda theorems -/

/-- Unlabeled `BINOP_1` from FUNCT_2 (2005.12.13) -/
theorem th17 {X Y Z f x y : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f (ZFMISC_1.product X Y) Z)
    (hx : x ∈ X) (hy : y ∈ Y) (hZ : Z ≠ (∅ : TarskiSet.{u})) :
    apply2 f x y ∈ Z :=
  FUNCT_2.th5 hf hZ
    ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mpr ⟨hx, hy⟩)

/-- Unlabeled `BINOP_1` from TOPALG_3 (2005.12.14) -/
theorem th18 {x y X Y Z f g : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f (ZFMISC_1.product X Y) Z)
    (hg : FUNCT_1.isFunction g) (hZ : Z ≠ (∅ : TarskiSet.{u}))
    (hx : x ∈ X) (hy : y ∈ Y) :
    apply2 (RELAT_1.comp f g) x y = FUNCT_1.apply g (apply2 f x y) :=
  FUNCT_2.th15 hf hg hZ
    ((ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mpr ⟨hx, hy⟩)

/-- Unlabeled `BINOP_1` (2005.12.17) — constant characterization. -/
theorem th19 {f X Y : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f)
    (hd : RELAT_1.dom f = ZFMISC_1.product X Y) :
    FUNCT_1.isConstant f ↔
      ∀ x1 x2 y1 y2, x1 ∈ X → x2 ∈ X → y1 ∈ Y → y2 ∈ Y →
        apply2 f x1 y1 = apply2 f x2 y2 := by
  constructor
  · intro hc x1 x2 y1 y2 hx1 hx2 hy1 hy2
    have hp1 : TARSKI.pair x1 y1 ∈ RELAT_1.dom f :=
      Eq.subst (motive := fun s => TARSKI.pair x1 y1 ∈ s) hd.symm
        ((ZFMISC_1.th87 (x := x1) (y := y1) (X := X) (Y := Y)).mpr ⟨hx1, hy1⟩)
    have hp2 : TARSKI.pair x2 y2 ∈ RELAT_1.dom f :=
      Eq.subst (motive := fun s => TARSKI.pair x2 y2 ∈ s) hd.symm
        ((ZFMISC_1.th87 (x := x2) (y := y2) (X := X) (Y := Y)).mpr ⟨hx2, hy2⟩)
    exact hc (TARSKI.pair x1 y1) (TARSKI.pair x2 y2) hp1 hp2
  · intro h p q hp hq
    obtain ⟨x1, y1, hx1, hy1, heq1⟩ :=
      (ZFMISC_1.th84 (A := RELAT_1.dom f) (X := X) (Y := Y)
        (fun z hz => Eq.subst (motive := fun s => z ∈ s) hd hz) hp)
    obtain ⟨x2, y2, hx2, hy2, heq2⟩ :=
      (ZFMISC_1.th84 (A := RELAT_1.dom f) (X := X) (Y := Y)
        (fun z hz => Eq.subst (motive := fun s => z ∈ s) hd hz) hq)
    have hv : apply2 f x1 y1 = apply2 f x2 y2 := h x1 x2 y1 y2 hx1 hx2 hy1 hy2
    exact Eq.subst (motive := fun s => FUNCT_1.apply f s = FUNCT_1.apply f q)
      heq1.symm
      (Eq.subst (motive := fun s => apply2 f x1 y1 = FUNCT_1.apply f s)
        heq2.symm hv)

/-- Unlabeled `BINOP_1` from PARTFUN1 (2006.12.05) -/
theorem th20 {X Y Z f1 f2 : TarskiSet.{u}}
    (h1 : PARTFUN1.isPartFunc f1 (ZFMISC_1.product X Y) Z)
    (h2 : PARTFUN1.isPartFunc f2 (ZFMISC_1.product X Y) Z)
    (hd : RELAT_1.dom f1 = RELAT_1.dom f2)
    (hv : ∀ x y, TARSKI.pair x y ∈ RELAT_1.dom f1 →
      apply2 f1 x y = apply2 f2 x y) :
    f1 = f2 := by
  have hdom_sub : RELAT_1.dom f1 ⊆ ZFMISC_1.product X Y :=
    RELSET_1.relationOf_defined h1.2
  refine FUNCT_1.th2 h1.1 h2.1 hd ?_
  intro z hz
  obtain ⟨x, y, _, _, heq⟩ :=
    (ZFMISC_1.th84 (A := RELAT_1.dom f1) (X := X) (Y := Y) hdom_sub hz)
  have hp : TARSKI.pair x y ∈ RELAT_1.dom f1 :=
    Eq.subst (motive := fun s => s ∈ RELAT_1.dom f1) heq hz
  exact Eq.subst (motive := fun s =>
      FUNCT_1.apply f1 s = FUNCT_1.apply f2 s) heq.symm (hv x y hp)

/-! ## Schemes `PartFuncEx2`, `LambdaR2`, `PartLambda2`, `PartLambda2D` -/

/-- `BINOP_1:sch PartFuncEx2` -/
theorem sch_PartFuncEx2 (X Y Z : TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hY : ∀ x y z, x ∈ X → y ∈ Y → P x y z → z ∈ Z)
    (hfun : ∀ x y z1 z2, x ∈ X → y ∈ Y → P x y z1 → P x y z2 → z1 = z2) :
    ∃ f, PARTFUN1.isPartFunc f (ZFMISC_1.product X Y) Z ∧
      (∀ x y, TARSKI.pair x y ∈ RELAT_1.dom f ↔
        x ∈ X ∧ y ∈ Y ∧ ∃ z, P x y z) ∧
      ∀ x y, TARSKI.pair x y ∈ RELAT_1.dom f → P x y (apply2 f x y) := by
  let Q : TarskiSet.{u} → TarskiSet.{u} → Prop :=
    fun p w => ∀ x1 y1, p = TARSKI.pair x1 y1 → P x1 y1 w
  have hQY : ∀ p w, p ∈ ZFMISC_1.product X Y → Q p w → w ∈ Z := by
    intro p w hp hQ
    obtain ⟨x1, y1, hx, hy, heq⟩ := (ZFMISC_1.def2 X Y p).mp hp
    exact hY x1 y1 w hx hy (hQ x1 y1 heq)
  have hQfun : ∀ p w1 w2, p ∈ ZFMISC_1.product X Y → Q p w1 → Q p w2 →
      w1 = w2 := by
    intro p w1 w2 hp h1 h2
    obtain ⟨x1, y1, hx, hy, heq⟩ := (ZFMISC_1.def2 X Y p).mp hp
    exact hfun x1 y1 w1 w2 hx hy (h1 x1 y1 heq) (h2 x1 y1 heq)
  obtain ⟨f, hf, hdom, happ⟩ :=
    PARTFUN1.sch_PartFuncEx (ZFMISC_1.product X Y) Z Q hQY hQfun
  refine ⟨f, hf, ?_, ?_⟩
  · intro x y
    constructor
    · intro hp
      have ⟨hpXY, ⟨z, hQ⟩⟩ := (hdom (TARSKI.pair x y)).mp hp
      have ⟨hx, hy⟩ :=
        (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mp hpXY
      exact ⟨hx, hy, ⟨z, hQ x y rfl⟩⟩
    · intro ⟨hx, hy, ⟨z, hP⟩⟩
      have hpXY : TARSKI.pair x y ∈ ZFMISC_1.product X Y :=
        (ZFMISC_1.th87 (x := x) (y := y) (X := X) (Y := Y)).mpr ⟨hx, hy⟩
      refine (hdom (TARSKI.pair x y)).mpr ⟨hpXY, ⟨z, ?_⟩⟩
      intro x1 y1 heq
      have ⟨hxeq, hyeq⟩ := XTUPLE_0.th1 heq
      exact Eq.subst (motive := fun s => P s y1 z) hxeq
        (Eq.subst (motive := fun s => P x s z) hyeq hP)
  · intro x y hp
    exact happ (TARSKI.pair x y) hp x y rfl

/-- `BINOP_1:sch LambdaR2` -/
theorem sch_LambdaR2 (X Y Z : TarskiSet.{u})
    (F : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hF : ∀ x y, P x y → F x y ∈ Z) :
    ∃ f, PARTFUN1.isPartFunc f (ZFMISC_1.product X Y) Z ∧
      (∀ x y, TARSKI.pair x y ∈ RELAT_1.dom f ↔ x ∈ X ∧ y ∈ Y ∧ P x y) ∧
      ∀ x y, TARSKI.pair x y ∈ RELAT_1.dom f → apply2 f x y = F x y := by
  obtain ⟨f, hf, hdom, happ⟩ :=
    sch_PartFuncEx2 X Y Z (fun x y z => P x y ∧ z = F x y)
      (fun x y z _ _ ⟨hP, heq⟩ =>
        Eq.subst (motive := fun s => s ∈ Z) heq.symm (hF x y hP))
      (fun x y z1 z2 _ _ ⟨_, e1⟩ ⟨_, e2⟩ => e1.trans e2.symm)
  refine ⟨f, hf, ?_, ?_⟩
  · intro x y
    constructor
    · intro hp
      have ⟨hx, hy, ⟨_, hP, _⟩⟩ := (hdom x y).mp hp
      exact ⟨hx, hy, hP⟩
    · intro ⟨hx, hy, hP⟩
      exact (hdom x y).mpr ⟨hx, hy, ⟨F x y, hP, rfl⟩⟩
  · intro x y hp
    exact (happ x y hp).2

/-- `BINOP_1:sch PartLambda2` -/
theorem sch_PartLambda2 (X Y Z : TarskiSet.{u})
    (F : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hF : ∀ x y, x ∈ X → y ∈ Y → P x y → F x y ∈ Z) :
    ∃ f, PARTFUN1.isPartFunc f (ZFMISC_1.product X Y) Z ∧
      (∀ x y, TARSKI.pair x y ∈ RELAT_1.dom f ↔ x ∈ X ∧ y ∈ Y ∧ P x y) ∧
      ∀ x y, TARSKI.pair x y ∈ RELAT_1.dom f → apply2 f x y = F x y := by
  obtain ⟨f, hf, hdom, happ⟩ :=
    sch_LambdaR2 X Y Z F (fun x y => x ∈ X ∧ y ∈ Y ∧ P x y)
      (fun x y ⟨hx, hy, hP⟩ => hF x y hx hy hP)
  refine ⟨f, hf, ?_, happ⟩
  intro x y
  constructor
  · intro hp
    have ⟨hx, hy, ⟨hx', hy', hP⟩⟩ := (hdom x y).mp hp
    exact ⟨hx, hy, hP⟩
  · intro ⟨hx, hy, hP⟩
    exact (hdom x y).mpr ⟨hx, hy, ⟨hx, hy, hP⟩⟩

/-- Unnamed `BINOP_1` scheme (nonempty domain elements). -/
theorem sch_PartLambda2D (X Y Z : TarskiSet.{u})
    (_hX : X ≠ (∅ : TarskiSet.{u})) (_hY : Y ≠ (∅ : TarskiSet.{u}))
    (F : TarskiSet.{u} → TarskiSet.{u} → TarskiSet.{u})
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (hF : ∀ x y, x ∈ X → y ∈ Y → P x y → F x y ∈ Z) :
    ∃ f, PARTFUN1.isPartFunc f (ZFMISC_1.product X Y) Z ∧
      (∀ x y, x ∈ X → y ∈ Y →
        (TARSKI.pair x y ∈ RELAT_1.dom f ↔ P x y)) ∧
      ∀ x y, x ∈ X → y ∈ Y → TARSKI.pair x y ∈ RELAT_1.dom f →
        apply2 f x y = F x y := by
  obtain ⟨f, hf, hdom, happ⟩ := sch_PartLambda2 X Y Z F P hF
  refine ⟨f, hf, ?_, ?_⟩
  · intro x y hx hy
    constructor
    · intro hp
      exact ((hdom x y).mp hp).2.2
    · intro hP
      exact (hdom x y).mpr ⟨hx, hy, hP⟩
  · intro x y _ _ hp
    exact happ x y hp

/-- Equality redefine compatibility (`BINOP_1` final redefine). -/
theorem eq_iff_apply2 {X Y Z f1 f2 : TarskiSet.{u}}
    (h1 : FUNCT_2.isFunctionOf f1 (ZFMISC_1.product X Y) Z)
    (h2 : FUNCT_2.isFunctionOf f2 (ZFMISC_1.product X Y) Z) :
    f1 = f2 ↔
      ∀ x y, x ∈ X → y ∈ Y → apply2 f1 x y = apply2 f2 x y :=
  ⟨fun heq _ _ _ _ => heq ▸ rfl, th1 h1 h2⟩

end BINOP_1
