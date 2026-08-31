/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/tarski.miz`.
Authors: Andrzej Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Tarski–Grothendieck set theory (Mizar `TARSKI`)

Palomar **Challenge** module: statement-only surface for Andrzej
Trybulec, *Tarski Grothendieck Set Theory* (Mizar `TARSKI`).

This is an **interim development scaffold**, not the eventual Palomar
research-interest submission. Submission is deferred until all 368
YELLOW*/WAYBEL* dependency articles are translated; the final surface
will select one substantive capstone from each of the 58 seed files.
The present foundational surface is retained to exercise Comparator
discipline and incorporates the audit laws requested during review.

## Palomar import rule (critical)

`Challenge.lean` must **not** import project libraries (`MizarCCL.*`)
or any dependency outside Lean core / allowlisted Mathlib. Palomar
compiles this file with plain `lean` and rejects transitive imports that
leave Init.

This file therefore:

* has **no** `import` lines (Init-only, implicit);
* inlines the shared carriers (`PreSet`, `TarskiSet`, membership) so
  `#check` / `#print` constants match `Solution.lean` exactly;
* uses `sorry` only on compared `TARSKI.*` theorems and constructors.

Proofs live in `Solution.lean`, which **may** import `MizarCCL.TARSKI`.
See `comparator.json` for the compared declaration list.
-/

/-!
# HIDDEN

Mizar built-ins that every article sees: a type of sets and membership
`in`. Not an item of `mizarccl_translation_order.yaml`.

`TarskiSet` is a *defined* type (Aczel pre-sets, quotiented by
extensional equivalence). It is not a synonym for `Type` and is not
introduced with `axiom`. Lean notation `x ∈ X` is Mizar `x in X`.
-/

universe u v

/-- Aczel pre-set: a family of pre-sets indexed by a `Type u`. -/
inductive PreSet : Type (u + 1) where
  | mk : (α : Type u) → (α → PreSet) → PreSet

namespace PreSet

/-- Extensional equivalence of pre-sets. -/
def Equiv : PreSet.{u} → PreSet.{u} → Prop
  | mk _ A, mk _ B =>
    (∀ a, ∃ b, Equiv (A a) (B b)) ∧
    (∀ b, ∃ a, Equiv (A a) (B b))

theorem equiv_refl (x : PreSet.{u}) : Equiv x x := by
  induction x with
  | mk α A ih =>
    exact ⟨fun a => ⟨a, ih a⟩, fun a => ⟨a, ih a⟩⟩

theorem equiv_symm {x y : PreSet.{u}} (h : Equiv x y) : Equiv y x := by
  induction x generalizing y with
  | mk α A ih =>
    cases y with
    | mk β B =>
      exact ⟨fun b =>
        let ⟨a, ha⟩ := h.2 b
        ⟨a, ih a ha⟩,
        fun a =>
        let ⟨b, hb⟩ := h.1 a
        ⟨b, ih a hb⟩⟩

theorem equiv_trans {x y z : PreSet.{u}} (hxy : Equiv x y) (hyz : Equiv y z) :
    Equiv x z := by
  induction x generalizing y z with
  | mk α A ih =>
    cases y with
    | mk β B =>
      cases z with
      | mk γ C =>
        exact ⟨fun a =>
          let ⟨b, hab⟩ := hxy.1 a
          let ⟨c, hbc⟩ := hyz.1 b
          ⟨c, ih a hab hbc⟩,
          fun c =>
          let ⟨b, hcb⟩ := hyz.2 c
          let ⟨a, hba⟩ := hxy.2 b
          ⟨a, ih a hba hcb⟩⟩

theorem equiv_iff {α : Type u} {A : α → PreSet.{u}} {β : Type u}
    {B : β → PreSet.{u}} :
    Equiv (mk α A) (mk β B) ↔
      (∀ a, ∃ b, Equiv (A a) (B b)) ∧ (∀ b, ∃ a, Equiv (A a) (B b)) :=
  Iff.rfl

def instSetoid : Setoid PreSet.{u} where
  r := Equiv
  iseqv := ⟨equiv_refl, fun h => equiv_symm h, fun hxy hyz => equiv_trans hxy hyz⟩

def idx : PreSet.{u} → Type u
  | mk α _ => α

def fam : (s : PreSet.{u}) → (s.idx → PreSet.{u})
  | mk _ A => A

theorem eta (p : PreSet.{u}) : p = mk p.idx p.fam := by
  cases p
  rfl

/-- Membership of pre-sets. -/
def Mem (x y : PreSet.{u}) : Prop :=
  match y with
  | mk _ A => ∃ a, Equiv x (A a)

theorem mem_mk {x : PreSet.{u}} {α : Type u} {A : α → PreSet.{u}} :
    Mem x (mk α A) ↔ ∃ a, Equiv x (A a) :=
  Iff.rfl

theorem mem_congr_left {x x' y : PreSet.{u}} (hx : Equiv x x') (h : Mem x y) :
    Mem x' y := by
  cases y with
  | mk α A =>
    let ⟨a, ha⟩ := h
    exact ⟨a, equiv_trans (equiv_symm hx) ha⟩

theorem mem_congr_right {x y y' : PreSet.{u}} (hy : Equiv y y') (h : Mem x y) :
    Mem x y' := by
  cases y with
  | mk α A =>
    cases y' with
    | mk β B =>
      let ⟨a, ha⟩ := h
      let ⟨b, hb⟩ := hy.1 a
      exact ⟨b, equiv_trans ha hb⟩

theorem mem_congr {x x' y y' : PreSet.{u}}
    (hx : Equiv x x') (hy : Equiv y y') (h : Mem x y) : Mem x' y' :=
  mem_congr_right hy (mem_congr_left hx h)

theorem mem_iff_of_equiv_right {x y y' : PreSet.{u}} (hy : Equiv y y') :
    Mem x y ↔ Mem x y' :=
  ⟨mem_congr_right hy, mem_congr_right (equiv_symm hy)⟩

theorem mem_iff_of_equiv_left {x x' y : PreSet.{u}} (hx : Equiv x x') :
    Mem x y ↔ Mem x' y :=
  ⟨mem_congr_left hx, mem_congr_left (equiv_symm hx)⟩

theorem equiv_of_mem {p q : PreSet.{u}}
    (h : ∀ x, Mem x p ↔ Mem x q) : Equiv p q := by
  cases p with
  | mk α A =>
    cases q with
    | mk β B =>
      constructor
      · intro a
        have : Mem (A a) (mk α A) := ⟨a, equiv_refl _⟩
        exact (h (A a)).mp this
      · intro b
        have : Mem (B b) (mk β B) := ⟨b, equiv_refl _⟩
        exact (h (B b)).mpr this |>.imp fun a ha => equiv_symm ha

end PreSet

/-- Extensional sets: pre-sets modulo `PreSet.Equiv`. -/
def TarskiSet : Type (u + 1) :=
  Quotient PreSet.instSetoid.{u}

namespace TarskiSet

def mk (p : PreSet.{u}) : TarskiSet.{u} :=
  Quotient.mk PreSet.instSetoid p

theorem sound {p q : PreSet.{u}} (h : PreSet.Equiv p q) : mk p = mk q :=
  Quotient.sound h

theorem exact {p q : PreSet.{u}} (h : mk p = mk q) : PreSet.Equiv p q :=
  Quotient.exact h

theorem ind {β : TarskiSet.{u} → Prop} (h : ∀ p : PreSet.{u}, β (mk p))
    (x : TarskiSet.{u}) : β x :=
  Quotient.ind h x

theorem inductionOn {β : TarskiSet.{u} → Prop} (x : TarskiSet.{u})
    (h : ∀ p : PreSet.{u}, β (mk p)) : β x :=
  ind h x

theorem inductionOn₂ {β : TarskiSet.{u} → TarskiSet.{u} → Prop}
    (x y : TarskiSet.{u})
    (h : ∀ p q : PreSet.{u}, β (mk p) (mk q)) : β x y :=
  Quotient.inductionOn₂ x y h

noncomputable def out (x : TarskiSet.{u}) : PreSet.{u} :=
  Classical.choose (Quotient.exists_rep x)

theorem out_eq (x : TarskiSet.{u}) : mk (out x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

/-- Mizar `in`. Defined, not postulated. -/
def mem (x y : TarskiSet.{u}) : Prop :=
  ∃ p q : PreSet.{u}, mk p = x ∧ mk q = y ∧ PreSet.Mem p q

theorem mem_pre (p q : PreSet.{u}) : mem (mk p) (mk q) ↔ PreSet.Mem p q := by
  constructor
  · intro ⟨p', q', hp, hq, hmem⟩
    exact PreSet.mem_congr (exact hp) (exact hq) hmem
  · intro h
    exact ⟨p, q, rfl, rfl, h⟩

end TarskiSet

instance instMembership : Membership TarskiSet.{u} TarskiSet.{u} where
  mem X x := TarskiSet.mem x X

@[simp] theorem TarskiSet.mem_eq (x y : TarskiSet.{u}) :
    Membership.mem y x = TarskiSet.mem x y := rfl

namespace TarskiSet

@[simp] theorem mem_mk_iff (p q : PreSet.{u}) :
    mk p ∈ mk q ↔ PreSet.Mem p q :=
  mem_pre p q

end TarskiSet

namespace TARSKI

/-! ## Constructors (Mizar `func` / `pred`) -/

def singleton (y : TarskiSet.{u}) : TarskiSet.{u} :=
  sorry

def upair (y z : TarskiSet.{u}) : TarskiSet.{u} :=
  sorry

def subset (X Y : TarskiSet.{u}) : Prop := ∀ x, x ∈ X → x ∈ Y

instance instHasSubset : HasSubset TarskiSet.{u} where
  Subset := subset

def union (X : TarskiSet.{u}) : TarskiSet.{u} :=
  sorry

def pair (x y : TarskiSet.{u}) : TarskiSet.{u} :=
  sorry

def are_equipotent (X Y : TarskiSet.{u}) : Prop :=
  sorry

/-- Structural universe lift for Aczel sets. On a representative
`PreSet.mk α A`, the proof-side definition recursively reindexes each node
by `ULift α`, then descends through the extensional quotient. The compared
laws below expose its equality and membership semantics independently of
that implementation. -/
def ulift (x : TarskiSet.{u}) : TarskiSet.{u + 1} :=
  sorry

/-! ## Auditable universe lifting -/

/-- `ulift` preserves and reflects equality, so it is an embedding rather
than an arbitrary map between universe levels. -/
theorem ulift_eq_iff (X Y : TarskiSet.{u}) :
    ulift X = ulift Y ↔ X = Y := by
  sorry

/-- `ulift` preserves and reflects membership. -/
theorem ulift_mem_iff (X Y : TarskiSet.{u}) :
    ulift X ∈ ulift Y ↔ X ∈ Y := by
  sorry

/-! ## TARSKI:1 — Extensionality -/

theorem th1 {X Y : TarskiSet.{u}} : (∀ x, x ∈ X ↔ x ∈ Y) → X = Y := by
  sorry

/-! ## TARSKI:def 1 — singleton `{ y }` -/

theorem def1 (y x : TarskiSet.{u}) : x ∈ singleton y ↔ x = y := by
  sorry

/-! ## TARSKI:def 2 — unordered pair `{ y, z }` -/

theorem def2 (y z x : TarskiSet.{u}) : x ∈ upair y z ↔ x = y ∨ x = z := by
  sorry

theorem upair_comm (y z : TarskiSet.{u}) : upair y z = upair z y := by
  sorry

/-! ## TARSKI:def 3 — inclusion `c=` -/

theorem def3 (X Y : TarskiSet.{u}) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by
  sorry

@[refl]
theorem subset_refl (X : TarskiSet.{u}) : X ⊆ X := fun _ hx => hx

/-! ## TARSKI:def 4 — `union X` -/

theorem def4 (X x : TarskiSet.{u}) : x ∈ union X ↔ ∃ Y, x ∈ Y ∧ Y ∈ X := by
  sorry

/-! ## TARSKI:2 — Regularity -/

theorem th2 {X x : TarskiSet.{u}} (hx : x ∈ X) :
    ∃ Y, Y ∈ X ∧ ¬∃ z, z ∈ X ∧ z ∈ Y := by
  sorry

/-! ## TARSKI:sch 1 — Fraenkel -/

theorem sch1 (A : TarskiSet.{u}) (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (functional : ∀ x y z, P x y → P x z → y = z) :
    ∃ X : TarskiSet.{u}, ∀ x, x ∈ X ↔ ∃ y, y ∈ A ∧ P y x := by
  sorry

/-! ## TARSKI:def 5 — ordered pair `[x,y]` (Kuratowski) -/

theorem def5 (x y : TarskiSet.{u}) :
    pair x y = upair (upair x y) (singleton x) := by
  sorry

/-! ## TARSKI:def 6 — equipotence -/

theorem def6 (X Y : TarskiSet.{u}) :
    are_equipotent X Y ↔
      ∃ Z : TarskiSet.{u},
        (∀ x, x ∈ X → ∃ y, y ∈ Y ∧ pair x y ∈ Z) ∧
        (∀ y, y ∈ Y → ∃ x, x ∈ X ∧ pair x y ∈ Z) ∧
        ∀ x y z u, pair x y ∈ Z → pair z u ∈ Z → (x = z ↔ y = u) := by
  sorry

/-! ## TARSKI:3 — weakened universe-polymorphic fragment

This does not claim Mizar's power-set witness or inaccessibility clauses.
Together with `ulift_eq_iff` and `ulift_mem_iff`, it says that one
higher-universe set contains faithful lifted copies of all lower-universe
sets and is downward closed under subsets.
-/

theorem th3 (N : TarskiSet.{u}) :
    ∃ M : TarskiSet.{u + 1},
      ulift N ∈ M ∧
      (∀ X Y : TarskiSet.{u + 1}, X ∈ M → Y ⊆ X → Y ∈ M) ∧
      (∀ X : TarskiSet.{u}, ulift X ∈ M) := by
  sorry

end TARSKI

/-! ## Experimental SETWISEO capstone

This additional compared statement is a local editorial experiment. It is
Mizar `SETWISEO:59`: a map that preserves the empty set and binary unions
commutes with finite indexed union.
-/

namespace XBOOLE_0

noncomputable def emptySet : TarskiSet.{u} :=
  sorry

noncomputable instance : EmptyCollection TarskiSet.{u} where
  emptyCollection := emptySet

def unionSet (X Y : TarskiSet.{u}) : TarskiSet.{u} :=
  sorry

noncomputable instance : Union TarskiSet.{u} where
  union := unionSet

end XBOOLE_0

namespace FUNCT_1

def apply (f x : TarskiSet.{u}) : TarskiSet.{u} :=
  sorry

end FUNCT_1

namespace FUNCT_2

def isFunctionOf (f X Y : TarskiSet.{u}) : Prop :=
  sorry

end FUNCT_2

namespace RELAT_1

def comp (f g : TarskiSet.{u}) : TarskiSet.{u} :=
  sorry

end RELAT_1

namespace FINSUB_1

noncomputable def Fin (X : TarskiSet.{u}) : TarskiSet.{u} :=
  sorry

end FINSUB_1

namespace SETWISEO

noncomputable def FinUnion {X A B f : TarskiSet.{u}}
    (_hX : X ≠ (∅ : TarskiSet.{u}))
    (_hB : B ∈ FINSUB_1.Fin X)
    (_hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin A)) : TarskiSet.{u} :=
  sorry

end SETWISEO

namespace PalomarExperiment

/-- `SETWISEO:59`: finite-union homomorphisms commute with finite union. -/
theorem setwiseo_th59 {X Y Z B f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X)
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin Y))
    (hg : FUNCT_2.isFunctionOf g (FINSUB_1.Fin Y) (FINSUB_1.Fin Z))
    (hcomp : FUNCT_2.isFunctionOf (RELAT_1.comp f g) X (FINSUB_1.Fin Z))
    (h0 : FUNCT_1.apply g (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}))
    (hhom : ∀ x y, x ∈ FINSUB_1.Fin Y → y ∈ FINSUB_1.Fin Y →
      FUNCT_1.apply g (x ∪ y) =
        FUNCT_1.apply g x ∪ FUNCT_1.apply g y) :
    FUNCT_1.apply g (SETWISEO.FinUnion hX hB hf) =
      SETWISEO.FinUnion hX hB hcomp := by
  sorry

end PalomarExperiment
