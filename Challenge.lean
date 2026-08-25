/-
Copyright (c) 2000-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under the GNU General Public License version 3.0 or later,
or the Creative Commons Attribution-ShareAlike License version 3.0 or later.
See the notices in `yellow17.miz`.
Authors: Bartłomiej Skorulski (Mizar), Lars Warren Ericson (Lean 4).
-/

import Mathlib.Topology.Compactness.Compact

/-!
# The Tychonoff theorem (Mizar `YELLOW_17`)

Palomar Challenge: statements of the Lean 4 translation of Bartłomiej Skorulski,
*The Tichonov Theorem* (Mizar `YELLOW_17`). Proofs are `sorry`; see `Yellow17.lean`. Mizar’s set-coded products
`product F`, projections `proj(F,i)`, and updates `f+*(i,xi)` become dependent
functions `∀ i, X i`, evaluation `Function.eval`, and `Function.update`.
-/

open Set Function Topology TopologicalSpace

set_option linter.unusedSectionVars false

universe u v

namespace Yellow17

variable {ι : Type u} {X : ι → Type v}

/-! ## Product, projection, and update (`Th1`–`Th13`) -/

/-- **Mizar `Th1` / `Th9`.** A nonempty intersection of the singleton cylinder
over `xi` with the cylinder over `Ai` forces `xi ∈ Ai`. -/
theorem eval_singleton_inter_mem {i : ι} {xi : X i} {Ai : Set (X i)}
    (h : ((eval i ⁻¹' ({xi} : Set (X i))) ∩ (eval i ⁻¹' Ai)).Nonempty) :
    xi ∈ Ai := by
  sorry

/-- **Mizar `Th2`.** Updating one coordinate of a point of `Set.pi univ s`
stays in the product box. -/
theorem update_mem_univ_pi [DecidableEq ι] {s : ∀ i, Set (X i)} {f : ∀ i, X i}
    {i : ι} {xi : X i} (hxi : xi ∈ s i) (hf : f ∈ univ.pi s) :
    update f i xi ∈ univ.pi s := by
  sorry

/-- **Mizar `Th3`.** The `i`-th projection of a product of inhabited types is
surjective onto the `i`-th factor. -/
theorem range_eval_eq_univ [∀ j, Nonempty (X j)] (i : ι) :
    range (eval i : (∀ j, X j) → X i) = univ := by
  sorry

/-- **Mizar `Th4` / `Th10`.** The full cylinder over a factor is the whole
product. -/
@[simp] theorem preimage_eval_univ (i : ι) :
    (eval i : (∀ j, X j) → X i) ⁻¹' (univ : Set (X i)) = univ := by
  sorry

/-- **Mizar `Th5` / `Th11`.** Coordinate update lands in the singleton cylinder. -/
theorem update_mem_eval_singleton [DecidableEq ι] (f : ∀ i, X i) (i : ι)
    (xi : X i) : update f i xi ∈ eval i ⁻¹' ({xi} : Set (X i)) := by
  sorry

/-- **Mizar `Th8`.** Projection is evaluation. -/
theorem eval_apply (f : ∀ i, X i) (i : ι) : eval i f = f i := by
  sorry

/-- **Mizar `Lm1` / `Th6` / `Th13`.** Membership in an off-axis cylinder is
unchanged by updating a different coordinate. -/
theorem mem_preimage_eval_update_iff [DecidableEq ι] {f : ∀ i, X i}
    {i₁ i₂ : ι} {xi₁ : X i₁} {Ai₂ : Set (X i₂)} (hne : i₁ ≠ i₂) :
    update f i₁ xi₁ ∈ eval i₂ ⁻¹' Ai₂ ↔ f ∈ eval i₂ ⁻¹' Ai₂ := by
  sorry

/-- **Mizar `Th7` / `Th12`, same coordinate.** -/
theorem eval_singleton_subset_eval_same [DecidableEq ι] {i : ι} {xi : X i}
    {Ai : Set (X i)} [Nonempty (∀ j, X j)] :
    eval i ⁻¹' ({xi} : Set (X i)) ⊆ eval i ⁻¹' Ai ↔ xi ∈ Ai := by
  sorry

/-- **Mizar `Th7` / `Th12`, distinct coordinates.** A proper cylinder cannot
contain a singleton cylinder on another axis. -/
theorem eval_singleton_not_subset_eval_of_ne [DecidableEq ι]
    [∀ j, Nonempty (X j)] {i₁ i₂ : ι} {xi₁ : X i₁} {Ai₂ : Set (X i₂)}
    (hne : i₁ ≠ i₂) (hAi : Ai₂ ≠ univ) :
    ¬ eval i₁ ⁻¹' ({xi₁} : Set (X i₁)) ⊆ eval i₂ ⁻¹' Ai₂ := by
  sorry

/-- **Mizar `Th7` / `Th12`.** A proper cylinder contains a singleton cylinder
iff the coordinates agree and the point lies in the set. -/
theorem eval_singleton_subset_eval_iff [DecidableEq ι] [∀ j, Nonempty (X j)]
    {i₁ i₂ : ι} {xi₁ : X i₁} {Ai₂ : Set (X i₂)} (hAi : Ai₂ ≠ univ) :
    eval i₁ ⁻¹' ({xi₁} : Set (X i₁)) ⊆ eval i₂ ⁻¹' Ai₂ ↔
      ∃ h : i₁ = i₂, xi₁ ∈ h ▸ Ai₂ := by
  sorry

/-- **Mizar scheme `ElProductEx`.** A point of the product can be assembled
coordinatewise. -/
noncomputable def elProductEx {P : ∀ i, X i → Prop}
    (h : ∀ i, ∃ x : X i, P i x) : ∀ i, X i :=
  sorry

theorem elProductEx_spec {P : ∀ i, X i → Prop} (h : ∀ i, ∃ x : X i, P i x)
    (i : ι) : P i (elProductEx h i) := by
  sorry

/-! ## Cylinder subbasis (`Th16`–`Th18`) -/

variable [∀ i, TopologicalSpace (X i)]

/-- Open cylinders `eval i ⁻¹' U`, the product prebasis of `YELLOW_18`. -/
def cylinderSubbasis (X : ι → Type v) [∀ i, TopologicalSpace (X i)] :
    Set (Set (∀ i, X i)) :=
  {C | ∃ (i : ι) (U : Set (X i)), IsOpen U ∧ C = eval i ⁻¹' U}

/-- **Mizar `Th16`.** Every prebasis element is an open cylinder. -/
theorem mem_cylinderSubbasis_iff {A : Set (∀ i, X i)} :
    A ∈ cylinderSubbasis X ↔
      ∃ (i : ι) (U : Set (X i)), IsOpen U ∧ A = eval i ⁻¹' U := by
  sorry

/-- The open cylinders generate the product topology. -/
theorem pi_eq_generateFrom_cylinderSubbasis :
    (Pi.topologicalSpace : TopologicalSpace (∀ i, X i)) =
      generateFrom (cylinderSubbasis X) := by
  sorry

/-- **Mizar `Th17`.** If a singleton cylinder sits inside a proper prebasis
element, that element is a proper open cylinder on the same axis. -/
theorem cylinder_of_singleton_subset [DecidableEq ι] [∀ j, Nonempty (X j)]
    {i : ι} {xi : X i} {A : Set (∀ i, X i)}
    (hA : A ∈ cylinderSubbasis X)
    (hsub : eval i ⁻¹' ({xi} : Set (X i)) ⊆ A)
    (hne : A ≠ univ) :
    ∃ U : Set (X i), U ≠ univ ∧ xi ∈ U ∧ IsOpen U ∧ A = eval i ⁻¹' U := by
  sorry

/-- **Mizar `Th18`.** An open cover of a factor lifts to a cylinder cover of
the product. -/
theorem univ_subset_iUnion_preimage_eval {i : ι} {Fi : Set (Set (X i))}
    (h : (univ : Set (X i)) ⊆ ⋃₀ Fi) :
    (univ : Set (∀ j, X j)) ⊆ ⋃₀ ((fun U : Set (X i) => eval i ⁻¹' U) '' Fi) := by
  sorry

/-! ## Compactness via open covers and a subbasis (`Th14`–`Th15`) -/

/-- **Mizar `Th14`.** Compactness is the finite-open-subcover property. -/
theorem isCompact_iff_finite_open_subcover {Y : Type u} [TopologicalSpace Y]
    {s : Set Y} :
    IsCompact s ↔ ∀ {κ : Type u} (U : κ → Set Y),
      (∀ k, IsOpen (U k)) → (s ⊆ ⋃ k, U k) →
        ∃ t : Finset κ, s ⊆ ⋃ k ∈ t, U k := by
  sorry

/-- **Mizar `Th15`.** Alexander’s subbasis theorem: it is enough to test
covers drawn from a generating family. -/
theorem isCompact_of_subbasis_finite_subcover {Y : Type*}
    [T : TopologicalSpace Y] {S : Set (Set Y)} (hTS : T = generateFrom S)
    {s : Set Y}
    (h : ∀ P ⊆ S, s ⊆ ⋃₀ P → ∃ Q ⊆ P, Q.Finite ∧ s ⊆ ⋃₀ Q) :
    IsCompact s := by
  sorry

/-! ## Combinatorics of cylinder covers (`Th19`–`Th22`) -/

/-- **Mizar `Th19`.** If a singleton fiber is covered by `G` but no member of
`G` contains the fiber, then `G` covers the whole product. -/
theorem univ_subset_sUnion_of_fiber_cover_no_strict [DecidableEq ι]
    [∀ j, Nonempty (X j)] {i : ι} {xi : X i} {G : Set (Set (∀ j, X j))}
    (hG : G ⊆ cylinderSubbasis X)
    (hcover : eval i ⁻¹' ({xi} : Set (X i)) ⊆ ⋃₀ G)
    (hstrict : ∀ A ∈ G, ¬ eval i ⁻¹' ({xi} : Set (X i)) ⊆ A) :
    (univ : Set (∀ j, X j)) ⊆ ⋃₀ G := by
  sorry

/-- **Mizar `Th20`.** Failure of finite product covers forces a fiber cover to
use a member that contains the fiber. -/
theorem exists_cylinder_containing_fiber_of_finite [DecidableEq ι]
    [∀ j, Nonempty (X j)] {i : ι} {xi : X i} {F : Set (Set (∀ j, X j))}
    (hF : F ⊆ cylinderSubbasis X)
    (hno : ∀ G ⊆ F, G.Finite → ¬ (univ : Set (∀ j, X j)) ⊆ ⋃₀ G)
    {G : Set (Set (∀ j, X j))} (hGF : G ⊆ F) (hGfin : G.Finite)
    (hcover : eval i ⁻¹' ({xi} : Set (X i)) ⊆ ⋃₀ G) :
    ∃ A ∈ G, eval i ⁻¹' ({xi} : Set (X i)) ⊆ A := by
  sorry

/-- **Mizar `Th21`.** Extract a proper open cylinder on the same axis from a
finite fiber cover. -/
theorem exists_proper_open_cylinder_of_fiber_cover [DecidableEq ι]
    [∀ j, Nonempty (X j)] {i : ι} {xi : X i} {F : Set (Set (∀ j, X j))}
    (hF : F ⊆ cylinderSubbasis X)
    (hno : ∀ G ⊆ F, G.Finite → ¬ (univ : Set (∀ j, X j)) ⊆ ⋃₀ G)
    {G : Set (Set (∀ j, X j))} (hGF : G ⊆ F) (hGfin : G.Finite)
    (hcover : eval i ⁻¹' ({xi} : Set (X i)) ⊆ ⋃₀ G) :
    ∃ U : Set (X i), U ≠ univ ∧ xi ∈ U ∧ IsOpen U ∧ eval i ⁻¹' U ∈ G := by
  sorry

/-- **Mizar `Th22`.** Compactness of a factor, plus no finite product cover,
produces a point whose singleton fiber also has no finite cover from `F`. -/
theorem exists_point_fiber_not_finitely_covered [DecidableEq ι]
    [∀ j, Nonempty (X j)] {i : ι} {F : Set (Set (∀ j, X j))}
    (hF : F ⊆ cylinderSubbasis X)
    (hcomp : IsCompact (univ : Set (X i)))
    (hno : ∀ G ⊆ F, G.Finite → ¬ (univ : Set (∀ j, X j)) ⊆ ⋃₀ G) :
    ∃ xi : X i, ∀ G ⊆ F, G.Finite →
      ¬ eval i ⁻¹' ({xi} : Set (X i)) ⊆ ⋃₀ G := by
  sorry

/-! ## The Tychonoff theorem -/

/-- **Mizar Tichonov Theorem, set form.** An arbitrary product of compact
sets is compact. -/
theorem yellow17_tychonoff_sets {s : ∀ i, Set (X i)}
    (hs : ∀ i, IsCompact (s i)) :
    IsCompact (univ.pi s) := by
  sorry

/-- **Mizar Tichonov Theorem.** A dependent product of compact spaces is
compact. -/
theorem yellow17_tychonoff [∀ i, CompactSpace (X i)] :
    CompactSpace (∀ i, X i) := by
  sorry

/-- Space-level form matching the Mizar statement: if each factor is compact,
then the product is compact. -/
theorem yellow17_tychonoff' (h : ∀ i, CompactSpace (X i)) :
    CompactSpace (∀ i, X i) := by
  sorry

end Yellow17
