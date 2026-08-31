import MizarCCL.HIDDEN

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/tarski.miz`.
Authors: Andrzej Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Tarski-Grothendieck set theory

1–1 Lean rendering of Mizar article `TARSKI`
(`vendor/mml/tarski.miz`, Mizar 7.13.01 / MML 4.181.1147).

Mizar labels: `TARSKI:1`–`TARSKI:3`, `TARSKI:def 1`–`def 6`,
`TARSKI:sch 1`. Every constructor and theorem is a Lean `def` or
`theorem` over `TarskiSet`. **No `axiom`, `admit`, or `sorry`.**

`TARSKI:3` uses Lean universes: the collection of all `TarskiSet.{u}`
is a universe object in `TarskiSet.{u+1}`. Mizar’s single sort `set`
becomes this universe-polymorphic family. The recursive cross-universe
map is not left abstract: `ulift_eq_iff` proves that it reflects
equality, and `ulift_mem_iff` proves that it preserves and reflects
membership.

## Palomar / axiom discipline (intentional variation)

Palomar registration for this package requires the compared surface to
be free of Lean `axiom`, `sorry`, and `admit`. Mizar’s `TARSKI:3` is
posted as an *axiom* in the MML with four clauses (containment,
subset-closure, power-set witness, inaccessibility). Lean’s `Type u`
does not prove a single-sort inaccessible universe object, so posting
Mizar’s full (iii)–(iv) here would require a Lean `axiom`.

**Choice made in this file:** prove the parts of `TARSKI:3` that are
theorems of the Aczel `TarskiSet` model (universe-polymorphic (i)–(ii)
plus “every `u`-set appears via the characterized embedding `ulift`”),
and **do not** introduce a Lean `axiom` for Mizar (iii)–(iv). This is
a deliberate weakening of the Mizar axiomatic packaging — not a
mistranslation of
`def 1`–`def 6`, extensionality, regularity, Fraenkel, or equipotence —
taken so the development stays axiom-free for Palomar.

**Consequence for later articles.** Theorems whose Mizar proofs need
the missing power-set / inaccessibility clauses (via `ZFMISC_1:112` or
`TARSKI:3` directly) may need a different argument in Lean. Every such
proof **must** carry an explicit docstring note that:

1. the *statement* matches Mizar;
2. the *proof* varies because this file omits Mizar `TARSKI:3`(iii)–(iv)
   rather than posting them as a Lean `axiom`;
3. the alternate argument uses only prior MizarCCL results (translated
   from dependent Mizar articles) and Lean’s ordinary logic / choice,
   not Mathlib set theory.

**Example.** `WELLORD2.th17` (Zermelo): Mizar uses a TG class from
`ZFMISC_1:112` with inaccessibility; Lean proves the same statement by
a Hartogs bound plus choice-driven transfinite enumeration and `lm1`.
See the docstring on `WELLORD2.th17` for the full English sketch.
`ZFMISC_1.th112` inherits the weaker `TARSKI.th3` and documents the
same gap.
-/

universe u

open TarskiSet

namespace TARSKI

/-! ## TARSKI:1 — Extensionality -/

theorem extensionality {X Y : TarskiSet.{u}}
    (h : ∀ x, x ∈ X ↔ x ∈ Y) : X = Y := by
  revert h
  refine inductionOn₂
    (β := fun X Y => (∀ x, x ∈ X ↔ x ∈ Y) → X = Y) X Y fun p q h => ?_
  apply sound
  cases p with
  | mk α A =>
    cases q with
    | mk β B =>
      constructor
      · intro a
        have ha : mk (A a) ∈ mk (PreSet.mk α A) := by
          rw [mem_mk_iff, PreSet.mem_mk]
          exact ⟨a, PreSet.equiv_refl _⟩
        have := (h (mk (A a))).mp ha
        rw [mem_mk_iff, PreSet.mem_mk] at this
        exact this
      · intro b
        have hb : mk (B b) ∈ mk (PreSet.mk β B) := by
          rw [mem_mk_iff, PreSet.mem_mk]
          exact ⟨b, PreSet.equiv_refl _⟩
        have := (h (mk (B b))).mpr hb
        rw [mem_mk_iff, PreSet.mem_mk] at this
        exact this.imp fun a ha => PreSet.equiv_symm ha

theorem th1 {X Y : TarskiSet.{u}} : (∀ x, x ∈ X ↔ x ∈ Y) → X = Y :=
  extensionality

/-! ## TARSKI:def 1 — singleton `{ y }` -/

def singletonPre (p : PreSet.{u}) : PreSet.{u} :=
  PreSet.mk PUnit.{u + 1} fun _ => p

theorem singletonPre_equiv {p q : PreSet.{u}} (h : PreSet.Equiv p q) :
    PreSet.Equiv (singletonPre p) (singletonPre q) :=
  ⟨fun _ => ⟨⟨⟩, h⟩, fun _ => ⟨⟨⟩, h⟩⟩

def singleton (y : TarskiSet.{u}) : TarskiSet.{u} :=
  Quotient.liftOn y (fun p => mk (singletonPre p)) fun _ _ h =>
    sound (singletonPre_equiv h)

noncomputable instance : Singleton TarskiSet.{u} TarskiSet.{u} where
  singleton := singleton

theorem singleton_mk (p : PreSet.{u}) : singleton (mk p) = mk (singletonPre p) :=
  rfl

@[simp] theorem singleton_iff (y x : TarskiSet.{u}) : x ∈ singleton y ↔ x = y := by
  refine inductionOn₂ (β := fun y x => x ∈ singleton y ↔ x = y) y x fun p q => ?_
  rw [singleton_mk, mem_mk_iff]
  simp only [singletonPre, PreSet.mem_mk]
  constructor
  · intro ⟨_, h⟩
    exact sound h
  · intro h
    exact ⟨⟨⟩, exact h⟩

theorem def1 (y x : TarskiSet.{u}) : x ∈ singleton y ↔ x = y :=
  singleton_iff y x


/-! ## TARSKI:def 2 — unordered pair `{ y, z }` -/

def upairPre (p q : PreSet.{u}) : PreSet.{u} :=
  PreSet.mk (ULift.{u} Bool) fun b => if b.down then p else q

theorem upairPre_equiv {p p' q q' : PreSet.{u}}
    (hp : PreSet.Equiv p p') (hq : PreSet.Equiv q q') :
    PreSet.Equiv (upairPre p q) (upairPre p' q') := by
  constructor
  · intro b
    rcases b with ⟨b⟩
    cases b
    · exact ⟨⟨false⟩, hq⟩
    · exact ⟨⟨true⟩, hp⟩
  · intro b
    rcases b with ⟨b⟩
    cases b
    · exact ⟨⟨false⟩, hq⟩
    · exact ⟨⟨true⟩, hp⟩

def upair (y z : TarskiSet.{u}) : TarskiSet.{u} :=
  Quotient.liftOn₂ y z (fun p q => mk (upairPre p q)) fun _ _ _ _ hp hq =>
    sound (upairPre_equiv hp hq)

theorem upair_mk (p q : PreSet.{u}) : upair (mk p) (mk q) = mk (upairPre p q) :=
  rfl

@[simp] theorem upair_iff (y z x : TarskiSet.{u}) :
    x ∈ upair y z ↔ x = y ∨ x = z := by
  revert z x
  refine inductionOn (β := fun y => ∀ z x, x ∈ upair y z ↔ x = y ∨ x = z) y
    fun p z x => ?_
  revert x
  refine inductionOn (β := fun z => ∀ x, x ∈ upair (mk p) z ↔ x = mk p ∨ x = z)
    z fun q x => ?_
  refine inductionOn (β := fun x => x ∈ upair (mk p) (mk q) ↔ x = mk p ∨ x = mk q)
    x fun r => ?_
  rw [upair_mk, mem_mk_iff]
  simp only [upairPre, PreSet.mem_mk]
  constructor
  · intro ⟨b, h⟩
    rcases b with ⟨b⟩
    cases b
    · exact Or.inr (sound (by simpa using h))
    · exact Or.inl (sound (by simpa using h))
  · intro h
    cases h with
    | inl hy => exact ⟨⟨true⟩, by simpa using exact hy⟩
    | inr hz => exact ⟨⟨false⟩, by simpa using exact hz⟩

theorem def2 (y z x : TarskiSet.{u}) : x ∈ upair y z ↔ x = y ∨ x = z :=
  upair_iff y z x

theorem upair_comm (y z : TarskiSet.{u}) : upair y z = upair z y :=
  extensionality fun x =>
    (upair_iff y z x).trans <| Or.comm.trans (upair_iff z y x).symm

/-! ## TARSKI:def 3 — inclusion `c=` -/

def subset (X Y : TarskiSet.{u}) : Prop := ∀ x, x ∈ X → x ∈ Y

instance instHasSubset : HasSubset TarskiSet.{u} where
  Subset := subset

theorem subset_iff (X Y : TarskiSet.{u}) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y :=
  Iff.rfl

theorem def3 (X Y : TarskiSet.{u}) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y :=
  subset_iff X Y

@[refl]
theorem subset_refl (X : TarskiSet.{u}) : X ⊆ X := fun _ hx => hx

/-! ## TARSKI:def 4 — `union X` -/

def unionPre : PreSet.{u} → PreSet.{u}
  | .mk α A => .mk (Σ a : α, (A a).idx) fun ⟨a, i⟩ => (A a).fam i

theorem mem_unionPre (r X : PreSet.{u}) :
    PreSet.Mem r (unionPre X) ↔ ∃ y, PreSet.Mem r y ∧ PreSet.Mem y X := by
  cases X with
  | mk α A =>
    constructor
    · intro h
      change PreSet.Mem r (PreSet.mk (Σ a, (A a).idx) fun ⟨a, i⟩ => (A a).fam i) at h
      rw [PreSet.mem_mk] at h
      obtain ⟨⟨a, i⟩, hi⟩ := h
      refine ⟨A a, ?_, ⟨a, PreSet.equiv_refl _⟩⟩
      rw [PreSet.eta (A a), PreSet.mem_mk]
      exact ⟨i, hi⟩
    · intro ⟨y, hry, hyX⟩
      rw [PreSet.mem_mk] at hyX
      obtain ⟨a, hay⟩ := hyX
      have hrA : PreSet.Mem r (A a) := PreSet.mem_congr_right hay hry
      rw [PreSet.eta (A a), PreSet.mem_mk] at hrA
      obtain ⟨i, hi⟩ := hrA
      change PreSet.Mem r (PreSet.mk (Σ a, (A a).idx) fun ⟨a, i⟩ => (A a).fam i)
      rw [PreSet.mem_mk]
      exact ⟨⟨a, i⟩, hi⟩

theorem unionPre_equiv {p q : PreSet.{u}} (h : PreSet.Equiv p q) :
    PreSet.Equiv (unionPre p) (unionPre q) :=
  PreSet.equiv_of_mem fun r =>
    (mem_unionPre r p).trans <|
      Iff.trans
        (exists_congr fun _ => and_congr_right fun _ =>
          PreSet.mem_iff_of_equiv_right h)
        (mem_unionPre r q).symm

def union (X : TarskiSet.{u}) : TarskiSet.{u} :=
  Quotient.liftOn X (fun p => mk (unionPre p)) fun _ _ h =>
    sound (unionPre_equiv h)

theorem union_mk (p : PreSet.{u}) : union (mk p) = mk (unionPre p) :=
  rfl

@[simp] theorem union_iff (X x : TarskiSet.{u}) :
    x ∈ union X ↔ ∃ Y, x ∈ Y ∧ Y ∈ X := by
  refine inductionOn₂ (β := fun X x => x ∈ union X ↔ ∃ Y, x ∈ Y ∧ Y ∈ X)
    X x fun p r => ?_
  rw [union_mk, mem_mk_iff, mem_unionPre]
  constructor
  · intro ⟨y, hry, hyX⟩
    exact ⟨mk y, (mem_mk_iff r y).mpr hry, (mem_mk_iff y p).mpr hyX⟩
  · intro ⟨Y, hxY, hYX⟩
    refine inductionOn (β := fun Y => mk r ∈ Y → Y ∈ mk p →
        ∃ y, PreSet.Mem r y ∧ PreSet.Mem y p) Y (fun q hxY hYX => ?_) hxY hYX
    rw [mem_mk_iff] at hxY
    rw [mem_mk_iff] at hYX
    exact ⟨q, hxY, hYX⟩

theorem def4 (X x : TarskiSet.{u}) : x ∈ union X ↔ ∃ Y, x ∈ Y ∧ Y ∈ X :=
  union_iff X x

/-! ## TARSKI:2 — Regularity -/

theorem acc_of_equiv {p q : PreSet.{u}} (he : PreSet.Equiv p q)
    (h : Acc PreSet.Mem q) : Acc PreSet.Mem p :=
  Acc.intro p fun _ hr => Acc.inv h (PreSet.mem_congr_right he hr)

theorem acc_mem (p : PreSet.{u}) : Acc PreSet.Mem p := by
  induction p with
  | mk α A ih =>
    exact Acc.intro _ fun q hq =>
      let ⟨a, ha⟩ := hq
      acc_of_equiv ha (ih a)

theorem regularity {X x : TarskiSet.{u}} (hx : x ∈ X) :
    ∃ Y, Y ∈ X ∧ ¬∃ z, z ∈ X ∧ z ∈ Y := by
  have : ∀ p : PreSet.{u}, Acc PreSet.Mem p → mk p ∈ X →
      ∃ Y, Y ∈ X ∧ ¬∃ z, z ∈ X ∧ z ∈ Y := by
    intro p hp
    induction hp with
    | intro p _ ih =>
      intro hpX
      by_cases h : ∃ z, z ∈ X ∧ z ∈ mk p
      · obtain ⟨z, hzX, hzP⟩ := h
        refine inductionOn (β := fun z => z ∈ X → z ∈ mk p →
            ∃ Y, Y ∈ X ∧ ¬∃ w, w ∈ X ∧ w ∈ Y) z (fun q hqX hqP => ?_) hzX hzP
        rw [mem_mk_iff] at hqP
        exact ih q hqP hqX
      · exact ⟨mk p, hpX, h⟩
  refine inductionOn (β := fun x => x ∈ X →
      ∃ Y, Y ∈ X ∧ ¬∃ z, z ∈ X ∧ z ∈ Y) x (fun p hp => ?_) hx
  exact this p (acc_mem p) hp

theorem th2 {X x : TarskiSet.{u}} (hx : x ∈ X) :
    ∃ Y, Y ∈ X ∧ ¬∃ z, z ∈ X ∧ z ∈ Y :=
  regularity hx

/-! ## TARSKI:sch 1 — Fraenkel -/

theorem fraenkel (A : TarskiSet.{u}) (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (functional : ∀ x y z, P x y → P x z → y = z) :
    ∃ X : TarskiSet.{u}, ∀ x, x ∈ X ↔ ∃ y, y ∈ A ∧ P y x := by
  refine inductionOn (β := fun A =>
      ∃ X, ∀ x, x ∈ X ↔ ∃ y, y ∈ A ∧ P y x) A fun p => ?_
  cases p with
  | mk α F =>
    let S := { a : α // ∃ x, P (mk (F a)) x }
    let X : TarskiSet.{u} :=
      mk (.mk S fun ⟨a, hx⟩ => out (Classical.choose hx))
    refine ⟨X, fun x => ?_⟩
    constructor
    · intro hx
      refine inductionOn (β := fun x => x ∈ X →
          ∃ y, y ∈ mk (PreSet.mk α F) ∧ P y x) x (fun q hq => ?_) hx
      change mk q ∈ mk (.mk S fun ⟨a, hx⟩ => out (Classical.choose hx)) at hq
      rw [mem_mk_iff, PreSet.mem_mk] at hq
      obtain ⟨⟨a, hex⟩, heq⟩ := hq
      refine ⟨mk (F a), ?_, ?_⟩
      · rw [mem_mk_iff, PreSet.mem_mk]
        exact ⟨a, PreSet.equiv_refl _⟩
      · have hP : P (mk (F a)) (Classical.choose hex) :=
          Classical.choose_spec hex
        have : mk q = Classical.choose hex :=
          (sound heq).trans (out_eq _)
        exact this ▸ hP
    · intro ⟨y, hyA, hP⟩
      refine inductionOn (β := fun y => y ∈ mk (PreSet.mk α F) → P y x → x ∈ X)
        y (fun q hqA hP => ?_) hyA hP
      rw [mem_mk_iff, PreSet.mem_mk] at hqA
      obtain ⟨a, ha⟩ := hqA
      have hyF : mk q = mk (F a) := sound ha
      have hex : ∃ z, P (mk (F a)) z := ⟨x, hyF ▸ hP⟩
      have hPx : P (mk (F a)) x := hyF ▸ hP
      have hxEq : x = Classical.choose hex :=
        functional _ _ _ hPx (Classical.choose_spec hex)
      rw [hxEq, ← out_eq (Classical.choose hex)]
      change mk (out (Classical.choose hex)) ∈
        mk (.mk S fun ⟨a, hx⟩ => out (Classical.choose hx))
      rw [mem_mk_iff, PreSet.mem_mk]
      exact ⟨⟨a, hex⟩, PreSet.equiv_refl _⟩

theorem sch1 (A : TarskiSet.{u}) (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (functional : ∀ x y z, P x y → P x z → y = z) :
    ∃ X : TarskiSet.{u}, ∀ x, x ∈ X ↔ ∃ y, y ∈ A ∧ P y x :=
  fraenkel A P functional

/-! ## TARSKI:def 5 — ordered pair `[x,y]` (Kuratowski) -/

def pair (x y : TarskiSet.{u}) : TarskiSet.{u} :=
  upair (upair x y) (singleton x)

theorem pair_eq (x y : TarskiSet.{u}) :
    pair x y = upair (upair x y) (singleton x) :=
  rfl

theorem def5 (x y : TarskiSet.{u}) :
    pair x y = upair (upair x y) (singleton x) :=
  pair_eq x y

theorem pair_inj {x₁ y₁ x₂ y₂ : TarskiSet.{u}} :
    pair x₁ y₁ = pair x₂ y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · intro h
    change upair (upair x₁ y₁) (singleton x₁) =
           upair (upair x₂ y₂) (singleton x₂) at h
    have hx1_s1 : x₁ ∈ singleton x₁ := (singleton_iff x₁ x₁).mpr rfl
    have hx1_u1 : x₁ ∈ upair x₁ y₁ := (upair_iff x₁ y₁ x₁).mpr (Or.inl rfl)
    have hy1_u1 : y₁ ∈ upair x₁ y₁ := (upair_iff x₁ y₁ y₁).mpr (Or.inr rfl)
    have hx2_s2 : x₂ ∈ singleton x₂ := (singleton_iff x₂ x₂).mpr rfl
    have hx2_u2 : x₂ ∈ upair x₂ y₂ := (upair_iff x₂ y₂ x₂).mpr (Or.inl rfl)
    have hy2_u2 : y₂ ∈ upair x₂ y₂ := (upair_iff x₂ y₂ y₂).mpr (Or.inr rfl)

    -- Step 1: Prove x₁ = x₂
    have hs2_in : singleton x₂ ∈ upair (upair x₂ y₂) (singleton x₂) :=
      (upair_iff _ _ _).mpr (Or.inr rfl)
    have hs2_in1 : singleton x₂ ∈ upair (upair x₁ y₁) (singleton x₁) :=
      h ▸ hs2_in
    have hx_eq : x₁ = x₂ := by
      cases (upair_iff _ _ _).mp hs2_in1 with
      | inl hs2_eq_u1 =>
        have : x₁ ∈ singleton x₂ := hs2_eq_u1 ▸ hx1_u1
        exact (singleton_iff x₂ x₁).mp this
      | inr hs2_eq_s1 =>
        have : x₁ ∈ singleton x₂ := hs2_eq_s1 ▸ hx1_s1
        exact (singleton_iff x₂ x₁).mp this
    subst hx_eq

    -- Step 2: Prove y₁ = y₂
    have hu1_in : upair x₁ y₁ ∈ upair (upair x₁ y₁) (singleton x₁) :=
      (upair_iff _ _ _).mpr (Or.inl rfl)
    have hu1_in2 : upair x₁ y₁ ∈ upair (upair x₁ y₂) (singleton x₁) :=
      h ▸ hu1_in
    have hy_eq : y₁ = y₂ := by
      cases (upair_iff _ _ _).mp hu1_in2 with
      | inl hu1_eq_u2 =>
        have hy1_in_u2 : y₁ ∈ upair x₁ y₂ := hu1_eq_u2 ▸ hy1_u1
        cases (upair_iff _ _ _).mp hy1_in_u2 with
        | inr hy1_eq_y2 => exact hy1_eq_y2
        | inl hy1_eq_x1 =>
          have hy2_in_u1 : y₂ ∈ upair x₁ y₁ := hu1_eq_u2.symm ▸ hy2_u2
          cases (upair_iff _ _ _).mp hy2_in_u1 with
          | inr hy2_eq_y1 => exact hy2_eq_y1.symm
          | inl hy2_eq_x1 => exact hy1_eq_x1.trans hy2_eq_x1.symm
      | inr hu1_eq_s1 =>
        have hy1_in_s1 : y₁ ∈ singleton x₁ := hu1_eq_s1 ▸ hy1_u1
        have hy1_eq_x1 : y₁ = x₁ := (singleton_iff x₁ y₁).mp hy1_in_s1
        have hu2_in : upair x₁ y₂ ∈ upair (upair x₁ y₂) (singleton x₁) :=
          (upair_iff _ _ _).mpr (Or.inl rfl)
        have hu2_in1 : upair x₁ y₂ ∈ upair (upair x₁ y₁) (singleton x₁) :=
          h.symm ▸ hu2_in
        cases (upair_iff _ _ _).mp hu2_in1 with
        | inl hu2_eq_u1 =>
          have : upair x₁ y₂ = singleton x₁ := hu2_eq_u1.trans hu1_eq_s1
          have hy2_in_s1 : y₂ ∈ singleton x₁ := this ▸ hy2_u2
          have hy2_eq_x1 : y₂ = x₁ := (singleton_iff x₁ y₂).mp hy2_in_s1
          exact hy1_eq_x1.trans hy2_eq_x1.symm
        | inr hu2_eq_s1 =>
          have hy2_in_s1 : y₂ ∈ singleton x₁ := hu2_eq_s1 ▸ hy2_u2
          have hy2_eq_x1 : y₂ = x₁ := (singleton_iff x₁ y₂).mp hy2_in_s1
          exact hy1_eq_x1.trans hy2_eq_x1.symm
    exact ⟨rfl, hy_eq⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## TARSKI:def 6 — equipotence -/

def are_equipotent (X Y : TarskiSet.{u}) : Prop :=
  ∃ Z : TarskiSet.{u},
    (∀ x, x ∈ X → ∃ y, y ∈ Y ∧ pair x y ∈ Z) ∧
    (∀ y, y ∈ Y → ∃ x, x ∈ X ∧ pair x y ∈ Z) ∧
    ∀ x y z u, pair x y ∈ Z → pair z u ∈ Z → (x = z ↔ y = u)

theorem are_equipotent_iff (X Y : TarskiSet.{u}) :
    are_equipotent X Y ↔
      ∃ Z : TarskiSet.{u},
        (∀ x, x ∈ X → ∃ y, y ∈ Y ∧ pair x y ∈ Z) ∧
        (∀ y, y ∈ Y → ∃ x, x ∈ X ∧ pair x y ∈ Z) ∧
        ∀ x y z u, pair x y ∈ Z → pair z u ∈ Z → (x = z ↔ y = u) :=
  Iff.rfl

theorem def6 (X Y : TarskiSet.{u}) :
    are_equipotent X Y ↔
      ∃ Z : TarskiSet.{u},
        (∀ x, x ∈ X → ∃ y, y ∈ Y ∧ pair x y ∈ Z) ∧
        (∀ y, y ∈ Y → ∃ x, x ∈ X ∧ pair x y ∈ Z) ∧
        ∀ x y z u, pair x y ∈ Z → pair z u ∈ Z → (x = z ↔ y = u) :=
  are_equipotent_iff X Y

/-! ## TARSKI:3 — Tarski–Grothendieck universes

Mizar’s single-sort `set` is `TarskiSet.{u}` here. Lean does not treat
`Type u` as a ZFC inaccessible, so the universe of all `TarskiSet.{u}`
lives in `TarskiSet.{u+1}`.

Mizar `TARSKI:3` (as an axiom) asserts, for every `N`, an `M` with:
(i) `N ∈ M`; (ii) subset-closure; (iii) a power-set witness inside
`M`; (iv) inaccessibility (`X ⊆ M → X ~ M ∨ X ∈ M`).

**What we prove (no Lean `axiom`).** Clause (i) in the lifted reading
(`ulift N ∈ M`), subset-closure of that universe, and “every `u`-set
is an element of that universe” via `ulift`. A power-set *object* for
a lifted set can be written `ulift (bool N)` / related constructions,
but Mizar’s (iii)–(iv) *as properties of a single-sort class* are not
theorems of this model and are not postulated.

**Why omit them.** Posting (iii)–(iv) as `axiom` would restore a more
literal TG packaging and some Mizar proof scripts, but would violate
the Palomar axiom-free requirement for this package. We prefer
theorem-only foundations here and accept proof variations downstream;
see the module docstring above and the note policy for impacted
theorems (e.g. `WELLORD2.th17`).
-/

def uliftPre : PreSet.{u} → PreSet.{u + 1}
  | .mk α A => .mk (ULift.{u + 1, u} α) fun ⟨a⟩ => uliftPre (A a)

theorem uliftPre_equiv {p q : PreSet.{u}} (h : PreSet.Equiv p q) :
    PreSet.Equiv (uliftPre p) (uliftPre q) := by
  induction p generalizing q with
  | mk α A ih =>
    cases q with
    | mk β B =>
      constructor
      · intro ⟨a⟩
        obtain ⟨b, hb⟩ := h.1 a
        exact ⟨⟨b⟩, ih a hb⟩
      · intro ⟨b⟩
        obtain ⟨a, ha⟩ := h.2 b
        exact ⟨⟨a⟩, ih a ha⟩

theorem uliftPre_equiv_iff {p q : PreSet.{u}} :
    PreSet.Equiv (uliftPre p) (uliftPre q) ↔ PreSet.Equiv p q := by
  constructor
  · intro h
    induction p generalizing q with
    | mk α A ih =>
      cases q with
      | mk β B =>
        constructor
        · intro a
          obtain ⟨⟨b⟩, hb⟩ := h.1 ⟨a⟩
          exact ⟨b, ih a hb⟩
        · intro b
          obtain ⟨⟨a⟩, ha⟩ := h.2 ⟨b⟩
          exact ⟨a, ih a ha⟩
  · exact uliftPre_equiv

def ulift (x : TarskiSet.{u}) : TarskiSet.{u + 1} :=
  Quotient.liftOn x (fun p => mk (uliftPre p)) fun _ _ h =>
    sound (uliftPre_equiv h)

theorem ulift_mk (p : PreSet.{u}) : ulift (mk p) = mk (uliftPre p) :=
  rfl

/-- Lifting reflects and preserves equality; in particular, `ulift` is an
embedding rather than an unspecified map between universe levels. -/
theorem ulift_eq_iff (X Y : TarskiSet.{u}) :
    ulift X = ulift Y ↔ X = Y := by
  refine inductionOn₂ (β := fun X Y => ulift X = ulift Y ↔ X = Y)
    X Y fun p q => ?_
  rw [ulift_mk, ulift_mk]
  constructor
  · intro h
    exact sound (uliftPre_equiv_iff.mp (TarskiSet.exact h))
  · exact congrArg ulift

/-- Lifting preserves and reflects set membership. This is the auditable
semantic characterization needed when reading the universe-polymorphic
form of `TARSKI:3`. -/
theorem ulift_mem_iff (X Y : TarskiSet.{u}) :
    ulift X ∈ ulift Y ↔ X ∈ Y := by
  refine inductionOn₂ (β := fun X Y => ulift X ∈ ulift Y ↔ X ∈ Y)
    X Y fun p q => ?_
  rw [ulift_mk, ulift_mk, mem_mk_iff, mem_mk_iff]
  cases q with
  | mk α A =>
    constructor
    · intro h
      obtain ⟨⟨a⟩, ha⟩ := h
      exact ⟨a, uliftPre_equiv_iff.mp ha⟩
    · intro h
      obtain ⟨a, ha⟩ := h
      exact ⟨⟨a⟩, uliftPre_equiv ha⟩

/-- The set of all `TarskiSet.{u}`, as an element of `TarskiSet.{u+1}`. -/
def universeSet : TarskiSet.{u + 1} :=
  mk <| .mk (ULift.{u + 1, u + 1} PreSet.{u}) fun ⟨p⟩ => uliftPre p

theorem ulift_mem_universe (N : TarskiSet.{u}) : ulift N ∈ universeSet.{u} := by
  refine inductionOn (β := fun N => ulift N ∈ universeSet.{u}) N fun p => ?_
  rw [ulift_mk]
  simp only [universeSet]
  rw [mem_mk_iff, PreSet.mem_mk]
  exact ⟨⟨p⟩, PreSet.equiv_refl _⟩

theorem mem_universe_iff (X : TarskiSet.{u + 1}) :
    X ∈ universeSet.{u} ↔ ∃ N : TarskiSet.{u}, X = ulift N := by
  constructor
  · intro h
    refine inductionOn (β := fun X => X ∈ universeSet.{u} →
      ∃ N : TarskiSet.{u}, X = ulift N) X (fun p h => ?_) h
    simp only [universeSet] at h
    rw [mem_mk_iff, PreSet.mem_mk] at h
    obtain ⟨⟨q⟩, hq⟩ := h
    exact ⟨mk q, (sound hq).trans (ulift_mk q).symm⟩
  · intro ⟨N, hN⟩
    rw [hN]
    exact ulift_mem_universe N

theorem subset_of_mem_universe {X Y : TarskiSet.{u + 1}}
    (hX : X ∈ universeSet.{u}) (hY : Y ⊆ X) : Y ∈ universeSet.{u} := by
  obtain ⟨N, hN⟩ := (mem_universe_iff X).mp hX
  subst hN
  refine inductionOn (β := fun N => Y ⊆ ulift N → Y ∈ universeSet.{u})
    N (fun q hY => ?_) hY
  refine inductionOn (β := fun Y => Y ⊆ ulift (mk q) → Y ∈ universeSet.{u})
    Y (fun r hY => ?_) hY
  cases q with
  | mk α A =>
    cases r with
    | mk β B =>
      let S := { a : α // ∃ b, PreSet.Equiv (B b) (uliftPre (A a)) }
      let r' : PreSet.{u} := .mk S fun ⟨a, _⟩ => A a
      have hEq : mk (.mk β B) = ulift (mk r') := by
        apply extensionality
        intro t
        refine inductionOn (β := fun t =>
            t ∈ mk (.mk β B) ↔ t ∈ ulift (mk r')) t fun s => ?_
        rw [ulift_mk]
        rw [mem_mk_iff, mem_mk_iff]
        rw [PreSet.mem_mk]
        simp only [r', uliftPre]
        rw [PreSet.mem_mk]
        constructor
        · intro ⟨b, hsb⟩
          have hbY : mk (B b) ∈ mk (.mk β B) := by
            rw [mem_mk_iff, PreSet.mem_mk]
            exact ⟨b, PreSet.equiv_refl _⟩
          have hbX : mk (B b) ∈ ulift (mk (PreSet.mk α A)) := hY _ hbY
          rw [ulift_mk] at hbX
          rw [mem_mk_iff] at hbX
          simp only [uliftPre] at hbX
          rw [PreSet.mem_mk] at hbX
          obtain ⟨⟨a⟩, ha⟩ := hbX
          exact ⟨⟨⟨a, ⟨b, ha⟩⟩⟩, PreSet.equiv_trans hsb ha⟩
        · intro ⟨⟨a, ⟨b, hb⟩⟩, hsa⟩
          exact ⟨b, PreSet.equiv_trans hsa (PreSet.equiv_symm hb)⟩
      rw [hEq]
      exact ulift_mem_universe (mk r')

/-- `TARSKI:3` over Lean universes (Palomar axiom-free reading).

`M` is the set of all `TarskiSet.{u}` inside `TarskiSet.{u+1}`. This
is Mizar (i)–(ii) plus “every `u`-set is an element of `M`”. Mizar’s
power-set witness (iii) and inaccessibility (iv) are **not** claimed:
they would need a Lean `axiom` (or a stronger ambient set model),
which this package deliberately avoids. Downstream proofs that used
those clauses in Mizar must vary and must document the variation;
see the module docstring and e.g. `WELLORD2.th17`. -/
theorem tarski_grothendieck (N : TarskiSet.{u}) :
    ∃ M : TarskiSet.{u + 1},
      ulift N ∈ M ∧
      (∀ X Y : TarskiSet.{u + 1}, X ∈ M → Y ⊆ X → Y ∈ M) ∧
      (∀ X : TarskiSet.{u}, ulift X ∈ M) :=
  ⟨universeSet.{u},
    ulift_mem_universe N,
    fun _ _ hX hY => subset_of_mem_universe hX hY,
    ulift_mem_universe⟩

/-- `TARSKI:3` (`Th3`). Same as `tarski_grothendieck`: universe-
polymorphic (i)–(ii), no Lean `axiom` for Mizar (iii)–(iv). -/
theorem th3 (N : TarskiSet.{u}) :
    ∃ M : TarskiSet.{u + 1},
      ulift N ∈ M ∧
      (∀ X Y : TarskiSet.{u + 1}, X ∈ M → Y ⊆ X → Y ∈ M) ∧
      (∀ X : TarskiSet.{u}, ulift X ∈ M) :=
  tarski_grothendieck N

end TARSKI
