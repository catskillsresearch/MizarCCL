import MizarCCL.XBOOLE_1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/enumset1.miz`.
Authors: Andrzej Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Enumerated sets

1–1 Lean rendering of Mizar article `ENUMSET1`
(`vendor/mml/enumset1.miz`). Environ: `TARSKI`, `XBOOLE_0`, `XBOOLE_1`.
Finite enumerations are `union({{x1,…,x_{n-1}},{xn}})` as in the
article. Lean insert notation is not used.
-/

universe u

open TarskiSet TARSKI

namespace ENUMSET1

variable {x x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y : TarskiSet.{u}}

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

private theorem union_eq (A B C : TarskiSet.{u})
    (h : ∀ x, x ∈ C ↔ x ∈ A ∨ x ∈ B) : C = A ∪ B :=
  eq_of_mem fun x => (h x).trans (XBOOLE_0.def3 A B x).symm

/-- Lean 4.33 Init has no `Or.assoc`. `∨` is right-associated. -/
@[simp] private theorem or_assoc {p q r : Prop} : (p ∨ q) ∨ r ↔ p ∨ q ∨ r :=
  ⟨fun h => h.elim (fun h => h.elim Or.inl (fun hq => Or.inr (Or.inl hq)))
      (fun hr => Or.inr (Or.inr hr)),
    fun h => h.elim (fun hp => Or.inl (Or.inl hp))
      (fun h => h.elim (fun hq => Or.inl (Or.inr hq)) Or.inr)⟩

/-! ## Lm1 -/

theorem lm1 (X y x : TarskiSet.{u}) :
    x ∈ union (upair X (TARSKI.singleton y)) ↔ x ∈ X ∨ x = y := by
  constructor
  · intro h
    obtain ⟨Z, hxZ, hZ⟩ := (union_iff _ _).mp h
    rcases (upair_iff X (TARSKI.singleton y) Z).mp hZ with hZX | hZy
    · exact Or.inl (hZX ▸ hxZ)
    · exact Or.inr ((singleton_iff y x).mp (hZy ▸ hxZ))
  · intro h
    refine (union_iff _ _).mpr ?_
    cases h with
    | inl hX => exact ⟨X, hX, (upair_iff _ _ _).mpr (Or.inl rfl)⟩
    | inr hy =>
      exact ⟨TARSKI.singleton y, (singleton_iff y x).mpr hy,
        (upair_iff _ _ _).mpr (Or.inr rfl)⟩

/-! ## def 1–8 -/

def enumset3 (a b c : TarskiSet.{u}) : TarskiSet.{u} :=
  union (upair (upair a b) (TARSKI.singleton c))

@[simp] theorem enumset3_iff (a b c z : TarskiSet.{u}) :
    z ∈ enumset3 a b c ↔ z = a ∨ z = b ∨ z = c := by
  rw [enumset3, lm1, upair_iff, or_assoc]

theorem def1 (a b c z : TarskiSet.{u}) :
    z ∈ enumset3 a b c ↔ z = a ∨ z = b ∨ z = c :=
  enumset3_iff a b c z

def enumset4 (a b c d : TarskiSet.{u}) : TarskiSet.{u} :=
  union (upair (enumset3 a b c) (TARSKI.singleton d))

@[simp] theorem enumset4_iff (a b c d z : TarskiSet.{u}) :
    z ∈ enumset4 a b c d ↔ z = a ∨ z = b ∨ z = c ∨ z = d := by
  rw [enumset4, lm1, enumset3_iff]; repeat rw [or_assoc]

theorem def2 (a b c d z : TarskiSet.{u}) :
    z ∈ enumset4 a b c d ↔ z = a ∨ z = b ∨ z = c ∨ z = d :=
  enumset4_iff a b c d z

def enumset5 (a b c d e : TarskiSet.{u}) : TarskiSet.{u} :=
  union (upair (enumset4 a b c d) (TARSKI.singleton e))

@[simp] theorem enumset5_iff (a b c d e z : TarskiSet.{u}) :
    z ∈ enumset5 a b c d e ↔ z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e := by
  rw [enumset5, lm1, enumset4_iff]; repeat rw [or_assoc]

theorem def3 (a b c d e z : TarskiSet.{u}) :
    z ∈ enumset5 a b c d e ↔ z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e :=
  enumset5_iff a b c d e z

def enumset6 (a b c d e f : TarskiSet.{u}) : TarskiSet.{u} :=
  union (upair (enumset5 a b c d e) (TARSKI.singleton f))

@[simp] theorem enumset6_iff (a b c d e f z : TarskiSet.{u}) :
    z ∈ enumset6 a b c d e f ↔
      z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f := by
  rw [enumset6, lm1, enumset5_iff]; repeat rw [or_assoc]

theorem def4 (a b c d e f z : TarskiSet.{u}) :
    z ∈ enumset6 a b c d e f ↔
      z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f :=
  enumset6_iff a b c d e f z

def enumset7 (a b c d e f g : TarskiSet.{u}) : TarskiSet.{u} :=
  union (upair (enumset6 a b c d e f) (TARSKI.singleton g))

@[simp] theorem enumset7_iff (a b c d e f g z : TarskiSet.{u}) :
    z ∈ enumset7 a b c d e f g ↔
      z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f ∨ z = g := by
  rw [enumset7, lm1, enumset6_iff]; repeat rw [or_assoc]

theorem def5 (a b c d e f g z : TarskiSet.{u}) :
    z ∈ enumset7 a b c d e f g ↔
      z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f ∨ z = g :=
  enumset7_iff a b c d e f g z

def enumset8 (a b c d e f g h : TarskiSet.{u}) : TarskiSet.{u} :=
  union (upair (enumset7 a b c d e f g) (TARSKI.singleton h))

@[simp] theorem enumset8_iff (a b c d e f g h z : TarskiSet.{u}) :
    z ∈ enumset8 a b c d e f g h ↔
      z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f ∨ z = g ∨ z = h := by
  rw [enumset8, lm1, enumset7_iff]; repeat rw [or_assoc]

theorem def6 (a b c d e f g h z : TarskiSet.{u}) :
    z ∈ enumset8 a b c d e f g h ↔
      z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f ∨ z = g ∨ z = h :=
  enumset8_iff a b c d e f g h z

def enumset9 (a b c d e f g h i : TarskiSet.{u}) : TarskiSet.{u} :=
  union (upair (enumset8 a b c d e f g h) (TARSKI.singleton i))

@[simp] theorem enumset9_iff (a b c d e f g h i z : TarskiSet.{u}) :
    z ∈ enumset9 a b c d e f g h i ↔
      z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f ∨ z = g ∨ z = h ∨ z = i := by
  rw [enumset9, lm1, enumset8_iff]; repeat rw [or_assoc]

theorem def7 (a b c d e f g h i z : TarskiSet.{u}) :
    z ∈ enumset9 a b c d e f g h i ↔
      z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f ∨ z = g ∨ z = h ∨ z = i :=
  enumset9_iff a b c d e f g h i z

def enumset10 (a b c d e f g h i j : TarskiSet.{u}) : TarskiSet.{u} :=
  union (upair (enumset9 a b c d e f g h i) (TARSKI.singleton j))

@[simp] theorem enumset10_iff (a b c d e f g h i j z : TarskiSet.{u}) :
    z ∈ enumset10 a b c d e f g h i j ↔
      z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f ∨ z = g ∨ z = h ∨
        z = i ∨ z = j := by
  rw [enumset10, lm1, enumset9_iff]; repeat rw [or_assoc]

theorem def8 (a b c d e f g h i j z : TarskiSet.{u}) :
    z ∈ enumset10 a b c d e f g h i j ↔
      z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f ∨ z = g ∨ z = h ∨
        z = i ∨ z = j :=
  enumset10_iff a b c d e f g h i j z

/-! ## Union decompositions (membership, then TARSKI:1) -/

theorem th1 : upair x1 x2 = TARSKI.singleton x1 ∪ TARSKI.singleton x2 :=
  union_eq _ _ _ fun z =>
    (upair_iff x1 x2 z).trans
      (or_congr (singleton_iff x1 z).symm (singleton_iff x2 z).symm)

theorem th2 : enumset3 x1 x2 x3 = TARSKI.singleton x1 ∪ upair x2 x3 :=
  union_eq _ _ _ fun z =>
    (enumset3_iff x1 x2 x3 z).trans
      (or_congr (singleton_iff x1 z).symm (upair_iff x2 x3 z).symm)

theorem th3 : enumset3 x1 x2 x3 = upair x1 x2 ∪ TARSKI.singleton x3 :=
  union_eq _ _ _ fun z =>
    (enumset3_iff x1 x2 x3 z).trans <|
      or_assoc.symm.trans (or_congr (upair_iff x1 x2 z).symm (singleton_iff x3 z).symm)

theorem lm2 : enumset4 x1 x2 x3 x4 = upair x1 x2 ∪ upair x3 x4 :=
  union_eq _ _ _ fun z => by
    simp only [enumset4_iff, upair_iff]
    constructor
    · intro h; rcases h with h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h) | (h | h) <;> simp [h]

theorem th4 : enumset4 x1 x2 x3 x4 = TARSKI.singleton x1 ∪ enumset3 x2 x3 x4 :=
  union_eq _ _ _ fun z => by
    simp only [enumset4_iff, enumset3_iff, singleton_iff]

theorem th5 : enumset4 x1 x2 x3 x4 = upair x1 x2 ∪ upair x3 x4 :=
  lm2

theorem th6 : enumset4 x1 x2 x3 x4 = enumset3 x1 x2 x3 ∪ TARSKI.singleton x4 :=
  union_eq _ _ _ fun z => by
    simp only [enumset4_iff, enumset3_iff, singleton_iff]
    constructor
    · intro h; rcases h with h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h) | h <;> simp [h]

theorem lm3 : enumset5 x1 x2 x3 x4 x5 = enumset3 x1 x2 x3 ∪ upair x4 x5 :=
  union_eq _ _ _ fun z => by
    simp only [enumset5_iff, enumset3_iff, upair_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h) | (h | h) <;> simp [h]

theorem th7 : enumset5 x1 x2 x3 x4 x5 = TARSKI.singleton x1 ∪ enumset4 x2 x3 x4 x5 :=
  union_eq _ _ _ fun z => by
    simp only [enumset5_iff, enumset4_iff, singleton_iff]

theorem th8 : enumset5 x1 x2 x3 x4 x5 = upair x1 x2 ∪ enumset3 x3 x4 x5 :=
  union_eq _ _ _ fun z => by
    simp only [enumset5_iff, enumset3_iff, upair_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h) | (h | h | h) <;> simp [h]

theorem th9 : enumset5 x1 x2 x3 x4 x5 = enumset3 x1 x2 x3 ∪ upair x4 x5 :=
  lm3

theorem th10 : enumset5 x1 x2 x3 x4 x5 = enumset4 x1 x2 x3 x4 ∪ TARSKI.singleton x5 :=
  union_eq _ _ _ fun z => by
    simp only [enumset5_iff, enumset4_iff, singleton_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h) | h <;> simp [h]

theorem lm4 : enumset6 x1 x2 x3 x4 x5 x6 = enumset3 x1 x2 x3 ∪ enumset3 x4 x5 x6 :=
  union_eq _ _ _ fun z => by
    simp only [enumset6_iff, enumset3_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h) | (h | h | h) <;> simp [h]

theorem th11 : enumset6 x1 x2 x3 x4 x5 x6 = TARSKI.singleton x1 ∪ enumset5 x2 x3 x4 x5 x6 :=
  union_eq _ _ _ fun z => by
    simp only [enumset6_iff, enumset5_iff, singleton_iff]

theorem th12 : enumset6 x1 x2 x3 x4 x5 x6 = upair x1 x2 ∪ enumset4 x3 x4 x5 x6 :=
  union_eq _ _ _ fun z => by
    simp only [enumset6_iff, enumset4_iff, upair_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h) | (h | h | h | h) <;> simp [h]

theorem th13 : enumset6 x1 x2 x3 x4 x5 x6 = enumset3 x1 x2 x3 ∪ enumset3 x4 x5 x6 :=
  lm4

theorem th14 : enumset6 x1 x2 x3 x4 x5 x6 = enumset4 x1 x2 x3 x4 ∪ upair x5 x6 :=
  union_eq _ _ _ fun z => by
    simp only [enumset6_iff, enumset4_iff, upair_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h) | (h | h) <;> simp [h]

theorem th15 : enumset6 x1 x2 x3 x4 x5 x6 = enumset5 x1 x2 x3 x4 x5 ∪ TARSKI.singleton x6 :=
  union_eq _ _ _ fun z => by
    simp only [enumset6_iff, enumset5_iff, singleton_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h | h) | h <;> simp [h]

theorem lm5 : enumset7 x1 x2 x3 x4 x5 x6 x7 = enumset4 x1 x2 x3 x4 ∪ enumset3 x5 x6 x7 :=
  union_eq _ _ _ fun z => by
    simp only [enumset7_iff, enumset4_iff, enumset3_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h) | (h | h | h) <;> simp [h]

theorem th16 : enumset7 x1 x2 x3 x4 x5 x6 x7 = TARSKI.singleton x1 ∪ enumset6 x2 x3 x4 x5 x6 x7 :=
  union_eq _ _ _ fun z => by
    simp only [enumset7_iff, enumset6_iff, singleton_iff]

theorem th17 : enumset7 x1 x2 x3 x4 x5 x6 x7 = upair x1 x2 ∪ enumset5 x3 x4 x5 x6 x7 :=
  union_eq _ _ _ fun z => by
    simp only [enumset7_iff, enumset5_iff, upair_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h) | (h | h | h | h | h) <;> simp [h]

theorem th18 : enumset7 x1 x2 x3 x4 x5 x6 x7 = enumset3 x1 x2 x3 ∪ enumset4 x4 x5 x6 x7 :=
  union_eq _ _ _ fun z => by
    simp only [enumset7_iff, enumset3_iff, enumset4_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h) | (h | h | h | h) <;> simp [h]

theorem th19 : enumset7 x1 x2 x3 x4 x5 x6 x7 = enumset4 x1 x2 x3 x4 ∪ enumset3 x5 x6 x7 :=
  lm5

theorem th20 : enumset7 x1 x2 x3 x4 x5 x6 x7 = enumset5 x1 x2 x3 x4 x5 ∪ upair x6 x7 :=
  union_eq _ _ _ fun z => by
    simp only [enumset7_iff, enumset5_iff, upair_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h | h) | (h | h) <;> simp [h]

theorem th21 : enumset7 x1 x2 x3 x4 x5 x6 x7 = enumset6 x1 x2 x3 x4 x5 x6 ∪ TARSKI.singleton x7 :=
  union_eq _ _ _ fun z => by
    simp only [enumset7_iff, enumset6_iff, singleton_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h | h | h) | h <;> simp [h]

theorem lm6 : enumset8 x1 x2 x3 x4 x5 x6 x7 x8 = enumset4 x1 x2 x3 x4 ∪ enumset4 x5 x6 x7 x8 :=
  union_eq _ _ _ fun z => by
    simp only [enumset8_iff, enumset4_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h) | (h | h | h | h) <;> simp [h]

theorem th22 : enumset8 x1 x2 x3 x4 x5 x6 x7 x8 = TARSKI.singleton x1 ∪ enumset7 x2 x3 x4 x5 x6 x7 x8 :=
  union_eq _ _ _ fun z => by
    simp only [enumset8_iff, enumset7_iff, singleton_iff]

theorem th23 : enumset8 x1 x2 x3 x4 x5 x6 x7 x8 = upair x1 x2 ∪ enumset6 x3 x4 x5 x6 x7 x8 :=
  union_eq _ _ _ fun z => by
    simp only [enumset8_iff, enumset6_iff, upair_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h) | (h | h | h | h | h | h) <;> simp [h]

theorem th24 : enumset8 x1 x2 x3 x4 x5 x6 x7 x8 = enumset3 x1 x2 x3 ∪ enumset5 x4 x5 x6 x7 x8 :=
  union_eq _ _ _ fun z => by
    simp only [enumset8_iff, enumset3_iff, enumset5_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h) | (h | h | h | h | h) <;> simp [h]

theorem th25 : enumset8 x1 x2 x3 x4 x5 x6 x7 x8 = enumset4 x1 x2 x3 x4 ∪ enumset4 x5 x6 x7 x8 :=
  lm6

theorem th26 : enumset8 x1 x2 x3 x4 x5 x6 x7 x8 = enumset5 x1 x2 x3 x4 x5 ∪ enumset3 x6 x7 x8 :=
  union_eq _ _ _ fun z => by
    simp only [enumset8_iff, enumset5_iff, enumset3_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h | h) | (h | h | h) <;> simp [h]

theorem th27 : enumset8 x1 x2 x3 x4 x5 x6 x7 x8 = enumset6 x1 x2 x3 x4 x5 x6 ∪ upair x7 x8 :=
  union_eq _ _ _ fun z => by
    simp only [enumset8_iff, enumset6_iff, upair_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h | h | h) | (h | h) <;> simp [h]

theorem th28 : enumset8 x1 x2 x3 x4 x5 x6 x7 x8 = enumset7 x1 x2 x3 x4 x5 x6 x7 ∪ TARSKI.singleton x8 :=
  union_eq _ _ _ fun z => by
    simp only [enumset8_iff, enumset7_iff, singleton_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h | h | h | h) | h <;> simp [h]

/-! ## Duplicate collapse -/

theorem th29 : upair x1 x1 = TARSKI.singleton x1 :=
  eq_of_mem fun z =>
    (upair_iff x1 x1 z).trans ⟨Or.rec id id, Or.inl⟩ |>.trans (singleton_iff x1 z).symm

theorem th30 : enumset3 x1 x1 x2 = upair x1 x2 :=
  eq_of_mem fun z => by
    simp only [enumset3_iff, upair_iff]
    constructor
    · intro h; rcases h with h | h | h <;> simp [h]
    · intro h; rcases h with h | h <;> simp [h]

theorem th31 : enumset4 x1 x1 x2 x3 = enumset3 x1 x2 x3 :=
  eq_of_mem fun z => by
    simp only [enumset4_iff, enumset3_iff]
    constructor
    · intro h; rcases h with h | h | h | h <;> simp [h]
    · intro h; rcases h with h | h | h <;> simp [h]

theorem th32 : enumset5 x1 x1 x2 x3 x4 = enumset4 x1 x2 x3 x4 :=
  eq_of_mem fun z => by
    simp only [enumset5_iff, enumset4_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h <;> simp [h]
    · intro h; rcases h with h | h | h | h <;> simp [h]

theorem th33 : enumset6 x1 x1 x2 x3 x4 x5 = enumset5 x1 x2 x3 x4 x5 :=
  eq_of_mem fun z => by
    simp only [enumset6_iff, enumset5_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with h | h | h | h | h <;> simp [h]

theorem th34 : enumset7 x1 x1 x2 x3 x4 x5 x6 = enumset6 x1 x2 x3 x4 x5 x6 :=
  eq_of_mem fun z => by
    simp only [enumset7_iff, enumset6_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with h | h | h | h | h | h <;> simp [h]

theorem th35 : enumset8 x1 x1 x2 x3 x4 x5 x6 x7 = enumset7 x1 x2 x3 x4 x5 x6 x7 :=
  eq_of_mem fun z => by
    simp only [enumset8_iff, enumset7_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with h | h | h | h | h | h | h <;> simp [h]

theorem th36 : enumset3 x1 x1 x1 = TARSKI.singleton x1 :=
  (th30 (x2 := x1)).trans th29

theorem th37 : enumset4 x1 x1 x1 x2 = upair x1 x2 :=
  (th31 (x2 := x1) (x3 := x2)).trans th30

theorem th38 : enumset5 x1 x1 x1 x2 x3 = enumset3 x1 x2 x3 :=
  (th32 (x2 := x1) (x3 := x2) (x4 := x3)).trans th31

theorem th39 : enumset6 x1 x1 x1 x2 x3 x4 = enumset4 x1 x2 x3 x4 :=
  (th33 (x2 := x1) (x3 := x2) (x4 := x3) (x5 := x4)).trans th32

theorem th40 : enumset7 x1 x1 x1 x2 x3 x4 x5 = enumset5 x1 x2 x3 x4 x5 :=
  (th34 (x2 := x1) (x3 := x2) (x4 := x3) (x5 := x4) (x6 := x5)).trans th33

theorem th41 : enumset8 x1 x1 x1 x2 x3 x4 x5 x6 = enumset6 x1 x2 x3 x4 x5 x6 :=
  (th35 (x2 := x1) (x3 := x2) (x4 := x3) (x5 := x4) (x6 := x5) (x7 := x6)).trans th34

theorem th42 : enumset4 x1 x1 x1 x1 = TARSKI.singleton x1 :=
  (th37 (x2 := x1)).trans th29

theorem th43 : enumset5 x1 x1 x1 x1 x2 = upair x1 x2 :=
  (th38 (x2 := x1) (x3 := x2)).trans th30

theorem th44 : enumset6 x1 x1 x1 x1 x2 x3 = enumset3 x1 x2 x3 :=
  (th39 (x2 := x1) (x3 := x2) (x4 := x3)).trans th31

theorem th45 : enumset7 x1 x1 x1 x1 x2 x3 x4 = enumset4 x1 x2 x3 x4 :=
  (th40 (x2 := x1) (x3 := x2) (x4 := x3) (x5 := x4)).trans th32

theorem th46 : enumset8 x1 x1 x1 x1 x2 x3 x4 x5 = enumset5 x1 x2 x3 x4 x5 :=
  (th41 (x2 := x1) (x3 := x2) (x4 := x3) (x5 := x4) (x6 := x5)).trans th33

theorem th47 : enumset5 x1 x1 x1 x1 x1 = TARSKI.singleton x1 :=
  (th43 (x2 := x1)).trans th29

theorem th48 : enumset6 x1 x1 x1 x1 x1 x2 = upair x1 x2 :=
  (th44 (x2 := x1) (x3 := x2)).trans th30

theorem th49 : enumset7 x1 x1 x1 x1 x1 x2 x3 = enumset3 x1 x2 x3 :=
  (th45 (x2 := x1) (x3 := x2) (x4 := x3)).trans th31

theorem th50 : enumset8 x1 x1 x1 x1 x1 x2 x3 x4 = enumset4 x1 x2 x3 x4 :=
  (th46 (x2 := x1) (x3 := x2) (x4 := x3) (x5 := x4)).trans th32

theorem th51 : enumset6 x1 x1 x1 x1 x1 x1 = TARSKI.singleton x1 :=
  (th48 (x2 := x1)).trans th29

theorem th52 : enumset7 x1 x1 x1 x1 x1 x1 x2 = upair x1 x2 :=
  (th49 (x2 := x1) (x3 := x2)).trans th30

theorem th53 : enumset8 x1 x1 x1 x1 x1 x1 x2 x3 = enumset3 x1 x2 x3 :=
  (th50 (x2 := x1) (x3 := x2) (x4 := x3)).trans th31

theorem th54 : enumset7 x1 x1 x1 x1 x1 x1 x1 = TARSKI.singleton x1 :=
  (th52 (x2 := x1)).trans th29

theorem th55 : enumset8 x1 x1 x1 x1 x1 x1 x1 x2 = upair x1 x2 :=
  (th53 (x2 := x1) (x3 := x2)).trans th30

theorem th56 : enumset8 x1 x1 x1 x1 x1 x1 x1 x1 = TARSKI.singleton x1 :=
  (th55 (x2 := x1)).trans th29

/-! ## Permutations -/

private theorem enumset3_perm {a b c a' b' c' : TarskiSet.{u}}
    (h : ∀ z, z = a ∨ z = b ∨ z = c ↔ z = a' ∨ z = b' ∨ z = c') :
    enumset3 a b c = enumset3 a' b' c' :=
  eq_of_mem fun z => (enumset3_iff a b c z).trans ((h z).trans (enumset3_iff a' b' c' z).symm)

private theorem enumset4_perm {a b c d a' b' c' d' : TarskiSet.{u}}
    (h : ∀ z, z = a ∨ z = b ∨ z = c ∨ z = d ↔ z = a' ∨ z = b' ∨ z = c' ∨ z = d') :
    enumset4 a b c d = enumset4 a' b' c' d' :=
  eq_of_mem fun z => (enumset4_iff a b c d z).trans ((h z).trans (enumset4_iff a' b' c' d' z).symm)

theorem th57 : enumset3 x1 x2 x3 = enumset3 x1 x3 x2 :=
  enumset3_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h <;> simp [h]

theorem th58 : enumset3 x1 x2 x3 = enumset3 x2 x1 x3 :=
  enumset3_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h <;> simp [h]

theorem th59 : enumset3 x1 x2 x3 = enumset3 x2 x3 x1 :=
  enumset3_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h <;> simp [h]

theorem th60 : enumset3 x1 x2 x3 = enumset3 x3 x2 x1 :=
  enumset3_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h <;> simp [h]

theorem th61 : enumset4 x1 x2 x3 x4 = enumset4 x1 x2 x4 x3 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem th62 : enumset4 x1 x2 x3 x4 = enumset4 x1 x3 x2 x4 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem th63 : enumset4 x1 x2 x3 x4 = enumset4 x1 x3 x4 x2 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem th64 : enumset4 x1 x2 x3 x4 = enumset4 x1 x4 x3 x2 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem th65 : enumset4 x1 x2 x3 x4 = enumset4 x2 x1 x3 x4 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem lm7 : enumset4 x1 x2 x3 x4 = enumset4 x2 x3 x1 x4 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem th66 : enumset4 x1 x2 x3 x4 = enumset4 x2 x1 x4 x3 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem th67 : enumset4 x1 x2 x3 x4 = enumset4 x2 x3 x1 x4 :=
  lm7

theorem th68 : enumset4 x1 x2 x3 x4 = enumset4 x2 x3 x4 x1 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem th69 : enumset4 x1 x2 x3 x4 = enumset4 x2 x4 x1 x3 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem th70 : enumset4 x1 x2 x3 x4 = enumset4 x2 x4 x3 x1 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem lm8 : enumset4 x1 x2 x3 x4 = enumset4 x3 x2 x1 x4 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem th71 : enumset4 x1 x2 x3 x4 = enumset4 x3 x2 x1 x4 :=
  lm8

theorem th72 : enumset4 x1 x2 x3 x4 = enumset4 x3 x2 x4 x1 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem th73 : enumset4 x1 x2 x3 x4 = enumset4 x3 x4 x1 x2 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem th74 : enumset4 x1 x2 x3 x4 = enumset4 x3 x4 x2 x1 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem th75 : enumset4 x1 x2 x3 x4 = enumset4 x4 x2 x3 x1 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem th76 : enumset4 x1 x2 x3 x4 = enumset4 x4 x3 x2 x1 :=
  enumset4_perm fun z => by
    constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

theorem lm9 :
    enumset9 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
      enumset4 x1 x2 x3 x4 ∪ enumset5 x5 x6 x7 x8 x9 :=
  union_eq _ _ _ fun z => by
    simp only [enumset9_iff, enumset4_iff, enumset5_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h) | (h | h | h | h | h) <;> simp [h]

theorem th77 :
    enumset9 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
      TARSKI.singleton x1 ∪ enumset8 x2 x3 x4 x5 x6 x7 x8 x9 :=
  union_eq _ _ _ fun z => by
    simp only [enumset9_iff, enumset8_iff, singleton_iff]

theorem th78 :
    enumset9 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
      upair x1 x2 ∪ enumset7 x3 x4 x5 x6 x7 x8 x9 :=
  union_eq _ _ _ fun z => by
    simp only [enumset9_iff, enumset7_iff, upair_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h) | (h | h | h | h | h | h | h) <;> simp [h]

theorem th79 :
    enumset9 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
      enumset3 x1 x2 x3 ∪ enumset6 x4 x5 x6 x7 x8 x9 :=
  union_eq _ _ _ fun z => by
    simp only [enumset9_iff, enumset3_iff, enumset6_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h) | (h | h | h | h | h | h) <;> simp [h]

theorem th80 :
    enumset9 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
      enumset4 x1 x2 x3 x4 ∪ enumset5 x5 x6 x7 x8 x9 :=
  lm9

theorem th81 :
    enumset9 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
      enumset5 x1 x2 x3 x4 x5 ∪ enumset4 x6 x7 x8 x9 :=
  union_eq _ _ _ fun z => by
    simp only [enumset9_iff, enumset5_iff, enumset4_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h | h) | (h | h | h | h) <;> simp [h]

theorem th82 :
    enumset9 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
      enumset6 x1 x2 x3 x4 x5 x6 ∪ enumset3 x7 x8 x9 :=
  union_eq _ _ _ fun z => by
    simp only [enumset9_iff, enumset6_iff, enumset3_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h | h | h) | (h | h | h) <;> simp [h]

theorem th83 :
    enumset9 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
      enumset7 x1 x2 x3 x4 x5 x6 x7 ∪ upair x8 x9 :=
  union_eq _ _ _ fun z => by
    simp only [enumset9_iff, enumset7_iff, upair_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h | h | h | h) | (h | h) <;> simp [h]

theorem th84 :
    enumset9 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
      enumset8 x1 x2 x3 x4 x5 x6 x7 x8 ∪ TARSKI.singleton x9 :=
  union_eq _ _ _ fun z => by
    simp only [enumset9_iff, enumset8_iff, singleton_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h | h | h | h | h) | h <;> simp [h]

theorem th85 :
    enumset10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =
      enumset9 x1 x2 x3 x4 x5 x6 x7 x8 x9 ∪ TARSKI.singleton x10 :=
  union_eq _ _ _ fun z => by
    simp only [enumset10_iff, enumset9_iff, singleton_iff]
    constructor
    · intro h; rcases h with h | h | h | h | h | h | h | h | h | h <;> simp [h]
    · intro h; rcases h with (h | h | h | h | h | h | h | h | h) | h <;> simp [h]

/-! ## Addenda -/

theorem th86 (hneY : x ≠ y) (hneZ : x ≠ x3) :
    enumset3 x y x3 \ TARSKI.singleton x = upair y x3 := by
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    have ⟨h3, hn⟩ := (XBOOLE_0.def5 (enumset3 x y x3) (TARSKI.singleton x) a).mp ha
    have ha' := (enumset3_iff x y x3 a).mp h3
    have hne : a ≠ x := fun hx => hn ((singleton_iff x a).mpr hx)
    rcases ha' with h | h | h
    · exact (hne h).elim
    · exact (upair_iff y x3 a).mpr (Or.inl h)
    · exact (upair_iff y x3 a).mpr (Or.inr h)
  · intro ha
    have hyz : a = y ∨ a = x3 := (upair_iff y x3 a).mp ha
    have h3 : a ∈ enumset3 x y x3 :=
      (enumset3_iff x y x3 a).mpr (hyz.elim (fun h => Or.inr (Or.inl h))
        (fun h => Or.inr (Or.inr h)))
    have hn : a ∉ TARSKI.singleton x := fun hx =>
      let hx' := (singleton_iff x a).mp hx
      hyz.elim (fun hy => hneY (hx'.symm.trans hy)) (fun hz => hneZ (hx'.symm.trans hz))
    exact (XBOOLE_0.def5 (enumset3 x y x3) (TARSKI.singleton x) a).mpr ⟨h3, hn⟩

theorem th87 : upair x2 x1 ∪ upair x3 x1 = enumset3 x1 x2 x3 := by
  have h := lm2 (x1 := x2) (x2 := x1) (x3 := x3) (x4 := x1)
  exact h.symm.trans ((th69 (x1 := x2) (x2 := x1) (x3 := x3) (x4 := x1)).trans th31)

end ENUMSET1
