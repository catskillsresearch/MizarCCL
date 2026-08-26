/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under GNU GPL-3.0-or-later or CC-BY-SA-3.0.
See `doc/COPYING.*`.
-/

/-!
# HIDDEN

Mizar built-ins that every article sees: the type `set` and membership
`in`. Not an item of `mizarccl_translation_order.yaml`; TARSKI is the
first translated article and imports this module.
-/

/-- Mizar type `set`. Untyped: every translated Mizar object is a set. -/
axiom set : Type

/-- Mizar predicate `in`. Lean notation `x ∈ X`. -/
axiom mizarMem : set → set → Prop

instance : Membership set set where
  mem := mizarMem
