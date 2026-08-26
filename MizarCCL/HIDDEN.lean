/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*`.
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
