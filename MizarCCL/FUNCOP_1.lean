import MizarCCL.FUNCT_3
import MizarCCL.WELLORD1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/funcop_1.miz`.
Authors: Andrzej Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Binary Operations Applied to Functions

1–1 Lean rendering of Mizar article `FUNCOP_1`
(`vendor/mml/funcop_1.miz`). Import is `FUNCT_3` and `WELLORD1`
(last queue deps actually used). Mizar `g*f` is Lean `RELAT_1.comp f g`.
Mizar `f~` (pair-component swap on a function) is Lean `tilde f`
(distinct from `RELAT_1.converse`).
-/

universe u

open TarskiSet TARSKI

namespace FUNCOP_1

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

private theorem ne_imp_not_empty {X : TarskiSet.{u}}
    (h : X ≠ (∅ : TarskiSet.{u})) : ¬ XBOOLE_0.isEmpty X :=
  fun he => h (XBOOLE_0.empty_eq he)

private theorem exists_mem_of_ne {X : TarskiSet.{u}}
    (h : X ≠ (∅ : TarskiSet.{u})) : ∃ x, x ∈ X :=
  XBOOLE_0.th7 h

private theorem singleton_ne_empty (x : TarskiSet.{u}) :
    TARSKI.singleton x ≠ (∅ : TarskiSet.{u}) :=
  fun h => XBOOLE_0.singleton_nonempty x
    (Eq.subst (motive := fun s => XBOOLE_0.isEmpty s) h.symm
      XBOOLE_0.emptySet_isEmpty)

/-! ## `f~` (`FUNCOP_1:def 1`) — swap components of pair values -/

/-- Value of `f~` at `x`. -/
noncomputable def tildeVal (f x : TarskiSet.{u}) : TarskiSet.{u} :=
  let v := FUNCT_1.apply f x
  have := Classical.propDecidable (XTUPLE_0.isPair v)
  if h : XTUPLE_0.isPair v then
    TARSKI.pair (XTUPLE_0.snd v) (XTUPLE_0.fst v)
  else v

/-- `FUNCOP_1:def 1` — `f~`. -/
noncomputable def tilde (f : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (FUNCT_1.sch_Lambda (RELAT_1.dom f) (tildeVal f))

theorem tilde_isFunction (f : TarskiSet.{u}) :
    FUNCT_1.isFunction (tilde f) :=
  (Classical.choose_spec
    (FUNCT_1.sch_Lambda (RELAT_1.dom f) (tildeVal f))).1

theorem tilde_dom (f : TarskiSet.{u}) :
    RELAT_1.dom (tilde f) = RELAT_1.dom f :=
  (Classical.choose_spec
    (FUNCT_1.sch_Lambda (RELAT_1.dom f) (tildeVal f))).2.1

private theorem tildeVal_of_pair {f x y z : TarskiSet.{u}}
    (heq : FUNCT_1.apply f x = TARSKI.pair y z) :
    tildeVal f x = TARSKI.pair z y := by
  classical
  have hp : XTUPLE_0.isPair (FUNCT_1.apply f x) :=
    Eq.subst (motive := fun s => XTUPLE_0.isPair s) heq.symm
      (XTUPLE_0.pair_isPair y z)
  unfold tildeVal
  simp only []
  -- re-express with local v
  change (if h : XTUPLE_0.isPair (FUNCT_1.apply f x) then
      TARSKI.pair (XTUPLE_0.snd (FUNCT_1.apply f x))
        (XTUPLE_0.fst (FUNCT_1.apply f x))
      else FUNCT_1.apply f x) = TARSKI.pair z y
  rw [dif_pos hp]
  have hf : XTUPLE_0.fst (FUNCT_1.apply f x) = y :=
    Eq.subst (motive := fun s => XTUPLE_0.fst s = y) heq.symm
      (XTUPLE_0.fst_pair y z)
  have hs : XTUPLE_0.snd (FUNCT_1.apply f x) = z :=
    Eq.subst (motive := fun s => XTUPLE_0.snd s = z) heq.symm
      (XTUPLE_0.snd_pair y z)
  exact (congrArg (fun s => TARSKI.pair s (XTUPLE_0.fst (FUNCT_1.apply f x)))
    hs).trans (congrArg (TARSKI.pair z) hf)

private theorem tildeVal_of_not_pair {f x : TarskiSet.{u}}
    (hn : ¬ ∃ y z, FUNCT_1.apply f x = TARSKI.pair y z) :
    tildeVal f x = FUNCT_1.apply f x := by
  classical
  have hp : ¬ XTUPLE_0.isPair (FUNCT_1.apply f x) :=
    fun h => hn ⟨_, _, Classical.choose_spec (Classical.choose_spec h)⟩
  unfold tildeVal
  change (if h : XTUPLE_0.isPair (FUNCT_1.apply f x) then
      TARSKI.pair (XTUPLE_0.snd (FUNCT_1.apply f x))
        (XTUPLE_0.fst (FUNCT_1.apply f x))
      else FUNCT_1.apply f x) = FUNCT_1.apply f x
  rw [dif_neg hp]

/-- `FUNCOP_1:def 1` characterization. -/
theorem def1 {f x : TarskiSet.{u}} (hx : x ∈ RELAT_1.dom f) :
    (∀ y z, FUNCT_1.apply f x = TARSKI.pair y z →
      FUNCT_1.apply (tilde f) x = TARSKI.pair z y) ∧
    (FUNCT_1.apply f x = FUNCT_1.apply (tilde f) x ∨
      ∃ y z, FUNCT_1.apply f x = TARSKI.pair y z) := by
  have happ : FUNCT_1.apply (tilde f) x = tildeVal f x :=
    (Classical.choose_spec
      (FUNCT_1.sch_Lambda (RELAT_1.dom f) (tildeVal f))).2.2 x hx
  constructor
  · intro y z heq
    exact happ.trans (tildeVal_of_pair heq)
  · have := Classical.propDecidable
      (∃ y z, FUNCT_1.apply f x = TARSKI.pair y z)
    by_cases hex : ∃ y z, FUNCT_1.apply f x = TARSKI.pair y z
    · exact Or.inr hex
    · exact Or.inl
        ((tildeVal_of_not_pair hex).symm.trans happ.symm)

theorem tilde_apply_pair {f x y z : TarskiSet.{u}}
    (hx : x ∈ RELAT_1.dom f)
    (heq : FUNCT_1.apply f x = TARSKI.pair y z) :
    FUNCT_1.apply (tilde f) x = TARSKI.pair z y :=
  (def1 hx).1 y z heq

theorem tilde_apply_eq {f x : TarskiSet.{u}}
    (hx : x ∈ RELAT_1.dom f)
    (hn : ¬ ∃ y z, FUNCT_1.apply f x = TARSKI.pair y z) :
    FUNCT_1.apply (tilde f) x = FUNCT_1.apply f x := by
  have h := (def1 hx).2
  cases h with
  | inl heq => exact heq.symm
  | inr hex => exact (hn hex).elim

/-- Involutiveness of `~`. -/
theorem tilde_tilde (f : TarskiSet.{u}) (_hf : FUNCT_1.isFunction f) :
    tilde (tilde f) = f := by
  refine FUNCT_1.th2 (tilde_isFunction (tilde f)) _hf
    ((tilde_dom (tilde f)).trans (tilde_dom f)) ?_
  intro x hx
  have hxT : x ∈ RELAT_1.dom (tilde f) :=
    Eq.subst (motive := fun s => x ∈ s) (tilde_dom (tilde f)) hx
  have hxF : x ∈ RELAT_1.dom f :=
    Eq.subst (motive := fun s => x ∈ s) (tilde_dom f) hxT
  have := Classical.propDecidable
    (∃ y z, FUNCT_1.apply f x = TARSKI.pair y z)
  by_cases hex : ∃ y z, FUNCT_1.apply f x = TARSKI.pair y z
  · obtain ⟨y, z, heq⟩ := hex
    have h1 : FUNCT_1.apply (tilde f) x = TARSKI.pair z y :=
      tilde_apply_pair hxF heq
    have h2 : FUNCT_1.apply (tilde (tilde f)) x = TARSKI.pair y z :=
      tilde_apply_pair hxT h1
    exact h2.trans heq.symm
  · have h1 : FUNCT_1.apply (tilde f) x = FUNCT_1.apply f x :=
      tilde_apply_eq hxF hex
    have hn2 : ¬ ∃ y z, FUNCT_1.apply (tilde f) x = TARSKI.pair y z := by
      intro ⟨y, z, heq⟩
      exact hex ⟨y, z, h1.symm.trans heq⟩
    exact (tilde_apply_eq hxT hn2).trans h1

/-! ## `FUNCOP_1:1` (`Th1`) -/

private theorem id_isFunctionOf (A : TarskiSet.{u}) :
    FUNCT_2.isFunctionOf (RELAT_1.id A) A A := by
  refine FUNCT_2.functionOf_of (FUNCT_1.id_isFunction A) (RELAT_1.id_dom A) ?_
  intro y hy
  obtain ⟨x, hxD, heq⟩ := (FUNCT_1.def3 (FUNCT_1.id_isFunction A).2).mp hy
  have hx : x ∈ A := Eq.subst (motive := fun s => x ∈ s) (RELAT_1.id_dom A) hxD
  exact Eq.subst (motive := fun s => s ∈ A) (heq.trans (FUNCT_1.th18 hx)).symm hx

/-- `FUNCOP_1:1` (`Th1`) -/
theorem th1 (A : TarskiSet.{u}) :
    FUNCT_3.delta A =
      FUNCT_3.complex (RELAT_1.id A) (RELAT_1.id A) := by
  have hrel : RELSET_1.isRelationOf (FUNCT_3.delta A) A
      (ZFMISC_1.product A A) :=
    FUNCT_2.functionOf_isRelationOf (FUNCT_3.delta_isFunctionOf A)
  have h1 : FUNCT_3.delta A =
      RELAT_1.comp (FUNCT_3.delta A) (RELAT_1.id (ZFMISC_1.product A A)) :=
    (FUNCT_2.th17 hrel).2.symm
  have h2 : RELAT_1.id (ZFMISC_1.product A A) =
      FUNCT_3.productFunc (RELAT_1.id A) (RELAT_1.id A) :=
    (FUNCT_3.th69 A A).symm
  have h3 : RELAT_1.comp (FUNCT_3.delta A)
      (FUNCT_3.productFunc (RELAT_1.id A) (RELAT_1.id A)) =
      FUNCT_3.complex (RELAT_1.id A) (RELAT_1.id A) :=
    (FUNCT_3.th78 (id_isFunctionOf A) (id_isFunctionOf A)).symm
  exact h1.trans
    ((congrArg (RELAT_1.comp (FUNCT_3.delta A)) h2).trans h3)


/-! ## Early theorems on `tilde` and `complex` -/

/-- `FUNCOP_1:2` (`Th2`) -/
theorem th2 {f g : TarskiSet.{u}} (_hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g) :
    FUNCT_3.complex f g = tilde (FUNCT_3.complex g f) := by
  have hdom : RELAT_1.dom (FUNCT_3.complex f g) =
      RELAT_1.dom (tilde (FUNCT_3.complex g f)) := by
    have h1 : RELAT_1.dom (FUNCT_3.complex f g) =
        RELAT_1.dom g ∩ RELAT_1.dom f :=
      (FUNCT_3.complex_dom f g).trans (XBOOLE_0.inter_comm _ _)
    have h2 : RELAT_1.dom (FUNCT_3.complex g f) =
        RELAT_1.dom g ∩ RELAT_1.dom f := FUNCT_3.complex_dom g f
    exact h1.trans (h2.symm.trans (tilde_dom (FUNCT_3.complex g f)).symm)
  refine FUNCT_1.th2 (FUNCT_3.complex_isFunction f g)
    (tilde_isFunction (FUNCT_3.complex g f)) hdom ?_
  intro x hx
  have hxI : x ∈ RELAT_1.dom f ∩ RELAT_1.dom g :=
    Eq.subst (motive := fun s => x ∈ s) (FUNCT_3.complex_dom f g) hx
  have ⟨hxF, hxG⟩ := (XBOOLE_0.def4 _ _ _).mp hxI
  have hxGF : x ∈ RELAT_1.dom (FUNCT_3.complex g f) :=
    Eq.subst (motive := fun s => x ∈ s) (FUNCT_3.complex_dom g f).symm
      ((XBOOLE_0.def4 _ _ _).mpr ⟨hxG, hxF⟩)
  have hfg : FUNCT_1.apply (FUNCT_3.complex f g) x =
      TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x) :=
    FUNCT_3.def7 hx
  have hgf : FUNCT_1.apply (FUNCT_3.complex g f) x =
      TARSKI.pair (FUNCT_1.apply g x) (FUNCT_1.apply f x) :=
    FUNCT_3.def7 hxGF
  exact hfg.trans (tilde_apply_pair hxGF hgf).symm

/-- `FUNCOP_1:3` (`Th3`) -/
theorem th3 {f A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    tilde (RELAT_1.restrict f A) = RELAT_1.restrict (tilde f) A := by
  have hdom : RELAT_1.dom (tilde (RELAT_1.restrict f A)) =
      RELAT_1.dom (RELAT_1.restrict (tilde f) A) := by
    have h1 : RELAT_1.dom (tilde (RELAT_1.restrict f A)) =
        RELAT_1.dom (RELAT_1.restrict f A) :=
      tilde_dom (RELAT_1.restrict f A)
    have h2 : RELAT_1.dom (RELAT_1.restrict f A) = RELAT_1.dom f ∩ A :=
      RELAT_1.th61
    have h3 : RELAT_1.dom (RELAT_1.restrict (tilde f) A) =
        RELAT_1.dom (tilde f) ∩ A := RELAT_1.th61
    have h4 : RELAT_1.dom (tilde f) = RELAT_1.dom f := tilde_dom f
    exact h1.trans (h2.trans
      ((congrArg (fun s => s ∩ A) h4.symm).trans h3.symm))
  refine FUNCT_1.th2 (tilde_isFunction (RELAT_1.restrict f A))
    (FUNCT_1.restrict_isFunction (f := tilde f) (X := A) (tilde_isFunction f)) hdom ?_
  intro x hx
  have hxR : x ∈ RELAT_1.dom (RELAT_1.restrict (tilde f) A) :=
    Eq.subst (motive := fun s => x ∈ s) hdom hx
  have hxTA : x ∈ RELAT_1.dom (tilde f) ∩ A :=
    Eq.subst (motive := fun s => x ∈ s) (RELAT_1.th61 (R := tilde f)) hxR
  have ⟨hxT, hxA⟩ := (XBOOLE_0.def4 _ _ _).mp hxTA
  have hxF : x ∈ RELAT_1.dom f :=
    Eq.subst (motive := fun s => x ∈ s) (tilde_dom f) hxT
  have hxFA : x ∈ RELAT_1.dom (RELAT_1.restrict f A) :=
    Eq.subst (motive := fun s => x ∈ s) (RELAT_1.th61 (R := f)).symm
      ((XBOOLE_0.def4 _ _ _).mpr ⟨hxF, hxA⟩)
  have happR : FUNCT_1.apply (RELAT_1.restrict f A) x = FUNCT_1.apply f x :=
    FUNCT_1.th47 hf.2 hxFA
  have happT : FUNCT_1.apply (RELAT_1.restrict (tilde f) A) x =
      FUNCT_1.apply (tilde f) x :=
    FUNCT_1.th47 (tilde_isFunction f).2 hxR
  have := Classical.propDecidable
    (∃ y z, FUNCT_1.apply (RELAT_1.restrict f A) x = TARSKI.pair y z)
  by_cases hex : ∃ y z,
      FUNCT_1.apply (RELAT_1.restrict f A) x = TARSKI.pair y z
  · obtain ⟨y, z, heq⟩ := hex
    have heqF : FUNCT_1.apply f x = TARSKI.pair y z := happR.symm.trans heq
    have h1 : FUNCT_1.apply (tilde (RELAT_1.restrict f A)) x =
        TARSKI.pair z y := tilde_apply_pair hxFA heq
    have h2 : FUNCT_1.apply (tilde f) x = TARSKI.pair z y :=
      tilde_apply_pair hxF heqF
    exact h1.trans (happT.trans h2).symm
  · have hnF : ¬ ∃ y z, FUNCT_1.apply f x = TARSKI.pair y z := by
      intro ⟨y, z, heq⟩
      exact hex ⟨y, z, happR.trans heq⟩
    have h1 : FUNCT_1.apply (tilde (RELAT_1.restrict f A)) x =
        FUNCT_1.apply (RELAT_1.restrict f A) x :=
      tilde_apply_eq hxFA hex
    have h2 : FUNCT_1.apply (tilde f) x = FUNCT_1.apply f x :=
      tilde_apply_eq hxF hnF
    exact h1.trans (happR.trans (h2.symm.trans happT.symm))

/-- Unlabeled `FUNCOP_1` (`Th4`) -/
theorem th4 (A : TarskiSet.{u}) :
    tilde (FUNCT_3.delta A) = FUNCT_3.delta A := by
  have h2 : FUNCT_3.complex (RELAT_1.id A) (RELAT_1.id A) =
      tilde (FUNCT_3.complex (RELAT_1.id A) (RELAT_1.id A)) :=
    th2 (FUNCT_1.id_isFunction A) (FUNCT_1.id_isFunction A)
  exact (congrArg tilde (th1 A)).trans (h2.symm.trans (th1 A).symm)

/-- `FUNCOP_1:5` (`Th5`) -/
theorem th5 {f g A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    RELAT_1.restrict (FUNCT_3.complex f g) A =
      FUNCT_3.complex (RELAT_1.restrict f A) g := by
  have hdom : RELAT_1.dom (RELAT_1.restrict (FUNCT_3.complex f g) A) =
      RELAT_1.dom (FUNCT_3.complex (RELAT_1.restrict f A) g) := by
    have h1 : RELAT_1.dom (RELAT_1.restrict (FUNCT_3.complex f g) A) =
        RELAT_1.dom (FUNCT_3.complex f g) ∩ A := RELAT_1.th61
    have h2 : RELAT_1.dom (FUNCT_3.complex f g) =
        RELAT_1.dom f ∩ RELAT_1.dom g := FUNCT_3.complex_dom f g
    have h3 : RELAT_1.dom (FUNCT_3.complex (RELAT_1.restrict f A) g) =
        RELAT_1.dom (RELAT_1.restrict f A) ∩ RELAT_1.dom g :=
      FUNCT_3.complex_dom (RELAT_1.restrict f A) g
    have h4 : RELAT_1.dom (RELAT_1.restrict f A) = RELAT_1.dom f ∩ A :=
      RELAT_1.th61
    -- (dom f ∩ dom g) ∩ A = (dom f ∩ A) ∩ dom g
    have hassoc : (RELAT_1.dom f ∩ RELAT_1.dom g) ∩ A =
        (RELAT_1.dom f ∩ A) ∩ RELAT_1.dom g := by
      apply eq_of_mem; intro x; constructor
      · intro hx
        have ⟨hfg, ha⟩ := (XBOOLE_0.def4 _ _ _).mp hx
        have ⟨hf', hg'⟩ := (XBOOLE_0.def4 _ _ _).mp hfg
        exact (XBOOLE_0.def4 _ _ _).mpr
          ⟨(XBOOLE_0.def4 _ _ _).mpr ⟨hf', ha⟩, hg'⟩
      · intro hx
        have ⟨hfa, hg'⟩ := (XBOOLE_0.def4 _ _ _).mp hx
        have ⟨hf', ha⟩ := (XBOOLE_0.def4 _ _ _).mp hfa
        exact (XBOOLE_0.def4 _ _ _).mpr
          ⟨(XBOOLE_0.def4 _ _ _).mpr ⟨hf', hg'⟩, ha⟩
    exact h1.trans ((congrArg (fun s => s ∩ A) h2).trans
      (hassoc.trans ((congrArg (fun s => s ∩ RELAT_1.dom g) h4.symm).trans
        h3.symm)))
  -- Use FUNCT_3.def7 characterization
  have hc := FUNCT_3.complex_isFunction (RELAT_1.restrict f A) g
  refine FUNCT_1.th2
    (FUNCT_1.restrict_isFunction (f := FUNCT_3.complex f g) (X := A)
      (FUNCT_3.complex_isFunction f g)) hc hdom ?_
  intro x hx
  have hxC : x ∈ RELAT_1.dom (FUNCT_3.complex (RELAT_1.restrict f A) g) :=
    Eq.subst (motive := fun s => x ∈ s) hdom hx
  have hxI : x ∈ RELAT_1.dom (RELAT_1.restrict f A) ∩ RELAT_1.dom g :=
    Eq.subst (motive := fun s => x ∈ s)
      (FUNCT_3.complex_dom (RELAT_1.restrict f A) g) hxC
  have ⟨hxFA, hxG⟩ := (XBOOLE_0.def4 _ _ _).mp hxI
  have hxF : x ∈ RELAT_1.dom f :=
    ((XBOOLE_0.def4 _ _ _).mp
      (Eq.subst (motive := fun s => x ∈ s) (RELAT_1.th61 (R := f)) hxFA)).1
  have hxCG : x ∈ RELAT_1.dom (FUNCT_3.complex f g) :=
    Eq.subst (motive := fun s => x ∈ s) (FUNCT_3.complex_dom f g).symm
      ((XBOOLE_0.def4 _ _ _).mpr ⟨hxF, hxG⟩)
  have happR : FUNCT_1.apply (RELAT_1.restrict (FUNCT_3.complex f g) A) x =
      FUNCT_1.apply (FUNCT_3.complex f g) x :=
    FUNCT_1.th47 (FUNCT_3.complex_isFunction f g).2 hx
  have hcg : FUNCT_1.apply (FUNCT_3.complex f g) x =
      TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x) :=
    FUNCT_3.def7 hxCG
  have happF : FUNCT_1.apply (RELAT_1.restrict f A) x = FUNCT_1.apply f x :=
    FUNCT_1.th47 hf.2 hxFA
  have hc2 : FUNCT_1.apply (FUNCT_3.complex (RELAT_1.restrict f A) g) x =
      TARSKI.pair (FUNCT_1.apply (RELAT_1.restrict f A) x) (FUNCT_1.apply g x) :=
    FUNCT_3.def7 hxC
  have hpair : TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x) =
      TARSKI.pair (FUNCT_1.apply (RELAT_1.restrict f A) x)
        (FUNCT_1.apply g x) :=
    congrArg (fun t => TARSKI.pair t (FUNCT_1.apply g x)) happF.symm
  exact happR.trans (hcg.trans (hpair.trans hc2.symm))

/-- `FUNCOP_1:6` (`Th6`) -/
theorem th6 {f g A : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g) :
    RELAT_1.restrict (FUNCT_3.complex f g) A =
      FUNCT_3.complex f (RELAT_1.restrict g A) := by
  have h1 : RELAT_1.restrict (FUNCT_3.complex f g) A =
      RELAT_1.restrict (tilde (FUNCT_3.complex g f)) A :=
    congrArg (fun s => RELAT_1.restrict s A) (th2 hf hg)
  have h2 : RELAT_1.restrict (tilde (FUNCT_3.complex g f)) A =
      tilde (RELAT_1.restrict (FUNCT_3.complex g f) A) :=
    (th3 (FUNCT_3.complex_isFunction g f) (A := A)).symm
  have h3 : RELAT_1.restrict (FUNCT_3.complex g f) A =
      FUNCT_3.complex (RELAT_1.restrict g A) f :=
    th5 hg hf
  have h4 : tilde (FUNCT_3.complex (RELAT_1.restrict g A) f) =
      FUNCT_3.complex f (RELAT_1.restrict g A) :=
    (th2 hf (FUNCT_1.restrict_isFunction (f := g) (X := A) hg)).symm
  exact h1.trans (h2.trans ((congrArg tilde h3).trans h4))

/-! ## Constant functions `A --> z` (`FUNCOP_1:def 2`) -/

/-- `FUNCOP_1:def 2` — `A --> z`. -/
noncomputable def mapsTo (A z : TarskiSet.{u}) : TarskiSet.{u} :=
  ZFMISC_1.product A (TARSKI.singleton z)

theorem def2 (A z : TarskiSet.{u}) :
    mapsTo A z = ZFMISC_1.product A (TARSKI.singleton z) :=
  rfl

theorem mapsTo_isRelation (A z : TarskiSet.{u}) :
    RELAT_1.isRelation (mapsTo A z) :=
  RELAT_1.product_isRelation A (TARSKI.singleton z)

theorem mapsTo_isFunctionLike (A z : TarskiSet.{u}) :
    FUNCT_1.isFunctionLike (mapsTo A z) := by
  intro a b1 b2 h1 h2
  have hb1 : b1 ∈ TARSKI.singleton z :=
    ((ZFMISC_1.th87 (x := a) (y := b1) (X := A) (Y := TARSKI.singleton z)).mp
      h1).2
  have hb2 : b2 ∈ TARSKI.singleton z :=
    ((ZFMISC_1.th87 (x := a) (y := b2) (X := A) (Y := TARSKI.singleton z)).mp
      h2).2
  exact ((TARSKI.singleton_iff z b1).mp hb1).trans
    ((TARSKI.singleton_iff z b2).mp hb2).symm

theorem mapsTo_isFunction (A z : TarskiSet.{u}) :
    FUNCT_1.isFunction (mapsTo A z) :=
  ⟨mapsTo_isRelation A z, mapsTo_isFunctionLike A z⟩

/-- Registration: `A --> z` is a Function. -/
theorem mapsTo_cluster (A z : TarskiSet.{u}) :
    FUNCT_1.isFunction (mapsTo A z) :=
  mapsTo_isFunction A z

/-- `FUNCOP_1:7` (`Th7`) -/
theorem th7 {A z x : TarskiSet.{u}} (hx : x ∈ A) :
    FUNCT_1.apply (mapsTo A z) x = z := by
  have hz : z ∈ TARSKI.singleton z := (TARSKI.singleton_iff z z).mpr rfl
  have hp : TARSKI.pair x z ∈ mapsTo A z :=
    (ZFMISC_1.th87).mpr ⟨hx, hz⟩
  exact (FUNCT_1.apply_of_mem (mapsTo_isFunctionLike A z) hp)

/-- Unlabeled `FUNCOP_1` (`Th8`) -/
theorem th8 {A x : TarskiSet.{u}} (hA : A ≠ (∅ : TarskiSet.{u})) :
    RELAT_1.rng (mapsTo A x) = TARSKI.singleton x :=
  (RELAT_1.th160 hA (singleton_ne_empty x)).2

/-- `FUNCOP_1:9` (`Th9`) -/
theorem th9 {f x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hr : RELAT_1.rng f = TARSKI.singleton x) :
    f = mapsTo (RELAT_1.dom f) x := by
  have hdomNe : RELAT_1.dom f ≠ (∅ : TarskiSet.{u}) := by
    intro h
    have hrng : RELAT_1.rng f = (∅ : TarskiSet.{u}) :=
      (RELAT_1.th42 hf.1).mp h
    have hx : x ∈ TARSKI.singleton x := (TARSKI.singleton_iff x x).mpr rfl
    exact (XBOOLE_0.empty_iff x).mp
      (Eq.subst (motive := fun s => x ∈ s) (hr.symm.trans hrng) hx)
  have hsingNe : TARSKI.singleton x ≠ (∅ : TarskiSet.{u}) :=
    singleton_ne_empty x
  have hd : RELAT_1.dom (mapsTo (RELAT_1.dom f) x) = RELAT_1.dom f :=
    (RELAT_1.th160 hdomNe hsingNe).1
  have hr' : RELAT_1.rng (mapsTo (RELAT_1.dom f) x) = TARSKI.singleton x :=
    (RELAT_1.th160 hdomNe hsingNe).2
  exact FUNCT_1.th7 hf (mapsTo_isFunction (RELAT_1.dom f) x) hd.symm hr hr'

/-- Registration: `{} --> x` is empty. -/
theorem mapsTo_empty_cluster (x : TarskiSet.{u}) :
    mapsTo (∅ : TarskiSet.{u}) x = (∅ : TarskiSet.{u}) :=
  (ZFMISC_1.th90).mpr (Or.inl rfl)

/-- Registration: empty `A --> x` is empty. -/
theorem mapsTo_of_empty {A x : TarskiSet.{u}}
    (hA : A = (∅ : TarskiSet.{u})) :
    mapsTo A x = (∅ : TarskiSet.{u}) :=
  Eq.subst (motive := fun s => mapsTo s x = (∅ : TarskiSet.{u})) hA.symm
    (mapsTo_empty_cluster x)

/-- Registration: nonempty `A --> x` is nonempty. -/
theorem mapsTo_nonempty {A x : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u})) :
    mapsTo A x ≠ (∅ : TarskiSet.{u}) := by
  intro h
  cases (ZFMISC_1.th90).mp h with
  | inl hA' => exact hA hA'
  | inr hS => exact singleton_ne_empty x hS

/-- Unlabeled `FUNCOP_1` (`Th10`) -/
theorem th10 (x : TarskiSet.{u}) :
    RELAT_1.dom (mapsTo (∅ : TarskiSet.{u}) x) = (∅ : TarskiSet.{u}) ∧
      RELAT_1.rng (mapsTo (∅ : TarskiSet.{u}) x) = (∅ : TarskiSet.{u}) := by
  have hempty : mapsTo (∅ : TarskiSet.{u}) x = (∅ : TarskiSet.{u}) :=
    mapsTo_empty_cluster x
  exact ⟨Eq.subst (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u}))
      hempty.symm RELAT_1.th38.1,
    Eq.subst (motive := fun s => RELAT_1.rng s = (∅ : TarskiSet.{u}))
      hempty.symm RELAT_1.th38.2⟩


/-- `FUNCOP_1:11` (`Th11`) -/
theorem th11 {f x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hv : ∀ z, z ∈ RELAT_1.dom f → FUNCT_1.apply f z = x) :
    f = mapsTo (RELAT_1.dom f) x := by
  have := Classical.propDecidable (RELAT_1.dom f = (∅ : TarskiSet.{u}))
  by_cases hdom : RELAT_1.dom f = (∅ : TarskiSet.{u})
  · have h1 : f = (∅ : TarskiSet.{u}) :=
      RELAT_1.th41 hf.1 (Or.inl hdom)
    have h2 : mapsTo (RELAT_1.dom f) x = (∅ : TarskiSet.{u}) :=
      mapsTo_of_empty hdom
    exact h1.trans h2.symm
  · have hrng : RELAT_1.rng f = TARSKI.singleton x := by
      apply eq_of_mem; intro y; constructor
      · intro hy
        obtain ⟨z, hz, heq⟩ := (FUNCT_1.def3 hf.2).mp hy
        exact (TARSKI.singleton_iff x y).mpr (heq.trans (hv z hz))
      · intro hy
        have hyx : y = x := (TARSKI.singleton_iff x y).mp hy
        obtain ⟨z, hz⟩ := exists_mem_of_ne hdom
        exact (FUNCT_1.def3 hf.2).mpr ⟨z, hz, hyx.trans (hv z hz).symm⟩
    exact th9 hf hrng

theorem mapsTo_dom (A x : TarskiSet.{u}) :
    RELAT_1.dom (mapsTo A x) = A := by
  have := Classical.propDecidable (A = (∅ : TarskiSet.{u}))
  by_cases hA : A = (∅ : TarskiSet.{u})
  · exact Eq.subst (motive := fun s =>
        RELAT_1.dom (mapsTo s x) = s) hA.symm (th10 x).1
  · exact (RELAT_1.th160 hA (singleton_ne_empty x)).1

/-- `FUNCOP_1:12` (`Th12`) -/
theorem th12 {A x B : TarskiSet.{u}} :
    RELAT_1.restrict (mapsTo A x) B = mapsTo (A ∩ B) x := by
  have hdom : RELAT_1.dom (RELAT_1.restrict (mapsTo A x) B) =
      RELAT_1.dom (mapsTo (A ∩ B) x) := by
    have h1 : RELAT_1.dom (RELAT_1.restrict (mapsTo A x) B) =
        RELAT_1.dom (mapsTo A x) ∩ B := RELAT_1.th61
    exact h1.trans ((congrArg (fun s => s ∩ B) (mapsTo_dom A x)).trans
      (mapsTo_dom (A ∩ B) x).symm)
  refine FUNCT_1.th2
    (FUNCT_1.restrict_isFunction (f := mapsTo A x) (X := B)
      (mapsTo_isFunction A x))
    (mapsTo_isFunction (A ∩ B) x) hdom ?_
  intro z hz
  have hzD : z ∈ RELAT_1.dom (mapsTo (A ∩ B) x) :=
    Eq.subst (motive := fun s => z ∈ s) hdom hz
  have hzAB : z ∈ A ∩ B :=
    Eq.subst (motive := fun s => z ∈ s) (mapsTo_dom (A ∩ B) x) hzD
  have ⟨hzA, _hzB⟩ := (XBOOLE_0.def4 _ _ _).mp hzAB
  have happ : FUNCT_1.apply (RELAT_1.restrict (mapsTo A x) B) z =
      FUNCT_1.apply (mapsTo A x) z :=
    FUNCT_1.th47 (mapsTo_isFunctionLike A x) hz
  exact happ.trans ((th7 hzA).trans (th7 hzAB).symm)

/-- `FUNCOP_1:13` (`Th13`) -/
theorem th13 (A x : TarskiSet.{u}) :
    RELAT_1.dom (mapsTo A x) = A ∧
      RELAT_1.rng (mapsTo A x) ⊆ TARSKI.singleton x := by
  refine ⟨mapsTo_dom A x, ?_⟩
  have := Classical.propDecidable (A = (∅ : TarskiSet.{u}))
  by_cases hA : A = (∅ : TarskiSet.{u})
  · have hr : RELAT_1.rng (mapsTo A x) = (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => RELAT_1.rng (mapsTo s x) =
          (∅ : TarskiSet.{u})) hA.symm (th10 x).2
    exact Eq.subst (motive := fun s => s ⊆ TARSKI.singleton x) hr.symm
      (XBOOLE_1.th2 (X := TARSKI.singleton x))
  · exact Eq.subst (motive := fun s => s ⊆ TARSKI.singleton x)
      (th8 hA).symm (fun _ h => h)


/-- `FUNCOP_1:14` (`Th14`) -/
theorem th14 {A x B : TarskiSet.{u}} (hx : x ∈ B) :
    RELAT_1.invimage (mapsTo A x) B = A := by
  have := Classical.propDecidable (A = (∅ : TarskiSet.{u}))
  by_cases hA : A = (∅ : TarskiSet.{u})
  · apply eq_of_mem; intro y; constructor
    · intro hy
      have hyD : y ∈ RELAT_1.dom (mapsTo A x) :=
        ((FUNCT_1.def7 (mapsTo_isFunctionLike A x)).mp hy).1
      have hdom : RELAT_1.dom (mapsTo A x) = (∅ : TarskiSet.{u}) :=
        Eq.subst (motive := fun s => RELAT_1.dom (mapsTo s x) =
            (∅ : TarskiSet.{u})) hA.symm (th10 x).1
      exact ((XBOOLE_0.empty_iff y).mp
        (Eq.subst (motive := fun s => y ∈ s) hdom hyD)).elim
    · intro hy
      exact ((XBOOLE_0.empty_iff y).mp
        (Eq.subst (motive := fun s => y ∈ s) hA hy)).elim
  · have hr : RELAT_1.rng (mapsTo A x) = TARSKI.singleton x := th8 hA
    have hsub : RELAT_1.rng (mapsTo A x) ⊆ B :=
      Eq.subst (motive := fun s => s ⊆ B) hr.symm ((ZFMISC_1.th31).mpr hx)
    have hinter : RELAT_1.rng (mapsTo A x) ∩ B = RELAT_1.rng (mapsTo A x) :=
      XBOOLE_1.th28 hsub
    have h1 : RELAT_1.invimage (mapsTo A x) B =
        RELAT_1.invimage (mapsTo A x) (RELAT_1.rng (mapsTo A x) ∩ B) :=
      RELAT_1.th133
    have h2 : RELAT_1.invimage (mapsTo A x)
        (RELAT_1.rng (mapsTo A x) ∩ B) =
        RELAT_1.invimage (mapsTo A x) (RELAT_1.rng (mapsTo A x)) :=
      congrArg (RELAT_1.invimage (mapsTo A x)) hinter
    have h3 : RELAT_1.invimage (mapsTo A x) (RELAT_1.rng (mapsTo A x)) =
        RELAT_1.dom (mapsTo A x) := RELAT_1.th134
    exact h1.trans (h2.trans (h3.trans (mapsTo_dom A x)))

/-- Unlabeled `FUNCOP_1` (`Th15`) -/
theorem th15 (A x : TarskiSet.{u}) :
    RELAT_1.invimage (mapsTo A x) (TARSKI.singleton x) = A :=
  th14 ((TARSKI.singleton_iff x x).mpr rfl)

/-- Unlabeled `FUNCOP_1` (`Th16`) -/
theorem th16 {A x B : TarskiSet.{u}} (hx : x ∉ B) :
    RELAT_1.invimage (mapsTo A x) B = (∅ : TarskiSet.{u}) := by
  have hrng : RELAT_1.rng (mapsTo A x) ⊆ TARSKI.singleton x := (th13 A x).2
  have hmiss : XBOOLE_0.misses (RELAT_1.rng (mapsTo A x)) B :=
    XBOOLE_1.th63 hrng (ZFMISC_1.th50 hx)
  exact (RELAT_1.th138).mpr hmiss

/-- Unlabeled `FUNCOP_1` (`Th17`) -/
theorem th17 {h A x : TarskiSet.{u}} (hf : FUNCT_1.isFunction h)
    (hx : x ∈ RELAT_1.dom h) :
    RELAT_1.comp (mapsTo A x) h = mapsTo A (FUNCT_1.apply h x) := by
  have hdom : RELAT_1.dom (RELAT_1.comp (mapsTo A x) h) =
      RELAT_1.dom (mapsTo A (FUNCT_1.apply h x)) := by
    have h1 : RELAT_1.dom (RELAT_1.comp (mapsTo A x) h) =
        RELAT_1.invimage (mapsTo A x) (RELAT_1.dom h) := RELAT_1.th147
    exact h1.trans ((th14 hx).trans (mapsTo_dom A (FUNCT_1.apply h x)).symm)
  refine FUNCT_1.th2 (FUNCT_1.comp_isFunction (mapsTo_isFunction A x) hf)
    (mapsTo_isFunction A (FUNCT_1.apply h x)) hdom ?_
  intro z hz
  have ⟨hzD, _⟩ := (FUNCT_1.th11 (mapsTo_isFunctionLike A x)).mp hz
  have hzA : z ∈ A := Eq.subst (motive := fun s => z ∈ s) (mapsTo_dom A x) hzD
  have happ : FUNCT_1.apply (RELAT_1.comp (mapsTo A x) h) z =
      FUNCT_1.apply h (FUNCT_1.apply (mapsTo A x) z) :=
    FUNCT_1.th12 (mapsTo_isFunctionLike A x) hf.2 hz
  exact happ.trans
    ((congrArg (FUNCT_1.apply h) (th7 hzA)).trans (th7 hzA).symm)

/-- Unlabeled `FUNCOP_1` (`Th18`) -/
theorem th18 {h A x : TarskiSet.{u}} (hf : FUNCT_1.isFunction h)
    (hA : A ≠ (∅ : TarskiSet.{u})) (hx : x ∈ RELAT_1.dom h) :
    RELAT_1.dom (RELAT_1.comp (mapsTo A x) h) ≠ (∅ : TarskiSet.{u}) := by
  obtain ⟨y, hy⟩ := exists_mem_of_ne hA
  have hyD : y ∈ RELAT_1.dom (mapsTo A x) :=
    Eq.subst (motive := fun s => y ∈ s) (mapsTo_dom A x).symm hy
  have happ : FUNCT_1.apply (mapsTo A x) y = x := th7 hy
  have hycomp : y ∈ RELAT_1.dom (RELAT_1.comp (mapsTo A x) h) :=
    (FUNCT_1.th11 (mapsTo_isFunctionLike A x)).mpr
      ⟨hyD, Eq.subst (motive := fun s => s ∈ RELAT_1.dom h) happ.symm hx⟩
  intro hempty
  exact (XBOOLE_0.empty_iff y).mp
    (Eq.subst (motive := fun s => y ∈ s) hempty hycomp)

/-- Unlabeled `FUNCOP_1` (`Th19`) -/
theorem th19 {A x h : TarskiSet.{u}} (hh : FUNCT_1.isFunction h) :
    RELAT_1.comp h (mapsTo A x) =
      mapsTo (RELAT_1.invimage h A) x := by
  have hdom : RELAT_1.dom (RELAT_1.comp h (mapsTo A x)) =
      RELAT_1.dom (mapsTo (RELAT_1.invimage h A) x) := by
    have h1 : RELAT_1.dom (RELAT_1.comp h (mapsTo A x)) =
        RELAT_1.invimage h (RELAT_1.dom (mapsTo A x)) := RELAT_1.th147
    exact h1.trans ((congrArg (RELAT_1.invimage h) (mapsTo_dom A x)).trans
      (mapsTo_dom (RELAT_1.invimage h A) x).symm)
  refine FUNCT_1.th2 (FUNCT_1.comp_isFunction hh (mapsTo_isFunction A x))
    (mapsTo_isFunction (RELAT_1.invimage h A) x) hdom ?_
  intro z hz
  have ⟨hzD, hhz⟩ := (FUNCT_1.th11 hh.2).mp hz
  have hhA : FUNCT_1.apply h z ∈ A :=
    Eq.subst (motive := fun s => FUNCT_1.apply h z ∈ s) (mapsTo_dom A x) hhz
  have happ : FUNCT_1.apply (RELAT_1.comp h (mapsTo A x)) z =
      FUNCT_1.apply (mapsTo A x) (FUNCT_1.apply h z) :=
    FUNCT_1.th12 hh.2 (mapsTo_isFunctionLike A x) hz
  have hzInv : z ∈ RELAT_1.invimage h A :=
    (FUNCT_1.def7 hh.2).mpr ⟨hzD, hhA⟩
  exact happ.trans ((th7 hhA).trans (th7 hzInv).symm)

/-- Unlabeled `FUNCOP_1` (`Th20`) -/
theorem th20 {A x y : TarskiSet.{u}} :
    tilde (mapsTo A (TARSKI.pair x y)) = mapsTo A (TARSKI.pair y x) := by
  have hdom : RELAT_1.dom (tilde (mapsTo A (TARSKI.pair x y))) =
      RELAT_1.dom (mapsTo A (TARSKI.pair y x)) :=
    (tilde_dom (mapsTo A (TARSKI.pair x y))).trans
      ((mapsTo_dom A (TARSKI.pair x y)).trans
        (mapsTo_dom A (TARSKI.pair y x)).symm)
  refine FUNCT_1.th2 (tilde_isFunction (mapsTo A (TARSKI.pair x y)))
    (mapsTo_isFunction A (TARSKI.pair y x)) hdom ?_
  intro z hz
  have hzD : z ∈ RELAT_1.dom (mapsTo A (TARSKI.pair x y)) :=
    Eq.subst (motive := fun s => z ∈ s)
      (tilde_dom (mapsTo A (TARSKI.pair x y))) hz
  have hzA : z ∈ A :=
    Eq.subst (motive := fun s => z ∈ s) (mapsTo_dom A (TARSKI.pair x y)) hzD
  have heq : FUNCT_1.apply (mapsTo A (TARSKI.pair x y)) z =
      TARSKI.pair x y := th7 hzA
  have h1 : FUNCT_1.apply (tilde (mapsTo A (TARSKI.pair x y))) z =
      TARSKI.pair y x := tilde_apply_pair hzD heq
  exact h1.trans (th7 hzA).symm


/-! ## Binary op applied to functions `F.:(f,g)` (`FUNCOP_1:def 3`) -/

/-- `FUNCOP_1:def 3` — `F.:(f,g)`. -/
noncomputable def applied (F f g : TarskiSet.{u}) : TarskiSet.{u} :=
  RELAT_1.comp (FUNCT_3.complex f g) F

theorem def3 (F f g : TarskiSet.{u}) :
    applied F f g = RELAT_1.comp (FUNCT_3.complex f g) F :=
  rfl

theorem applied_isFunction {F f g : TarskiSet.{u}}
    (hF : FUNCT_1.isFunction F) (_hf : FUNCT_1.isFunction f)
    (_hg : FUNCT_1.isFunction g) :
    FUNCT_1.isFunction (applied F f g) :=
  FUNCT_1.comp_isFunction (FUNCT_3.complex_isFunction f g) hF

/-- `FUNCOP_1:lm 1` -/
theorem lm1 {F f g x : TarskiSet.{u}}
    (hF : FUNCT_1.isFunctionLike F) (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (hx : x ∈ RELAT_1.dom (RELAT_1.comp (FUNCT_3.complex f g) F)) :
    FUNCT_1.apply (RELAT_1.comp (FUNCT_3.complex f g) F) x =
      BINOP_1.apply2 F (FUNCT_1.apply f x) (FUNCT_1.apply g x) := by
  have hxC : x ∈ RELAT_1.dom (FUNCT_3.complex f g) :=
    ((FUNCT_1.th11 (FUNCT_3.complex_isFunction f g).2).mp hx).1
  have happ : FUNCT_1.apply (RELAT_1.comp (FUNCT_3.complex f g) F) x =
      FUNCT_1.apply F (FUNCT_1.apply (FUNCT_3.complex f g) x) :=
    FUNCT_1.th12 (FUNCT_3.complex_isFunction f g).2 hF hx
  have hpair : FUNCT_1.apply (FUNCT_3.complex f g) x =
      TARSKI.pair (FUNCT_1.apply f x) (FUNCT_1.apply g x) :=
    FUNCT_3.def7 hxC
  exact happ.trans (congrArg (FUNCT_1.apply F) hpair)

/-- Unlabeled `FUNCOP_1` (`Th21`) -/
theorem th21 {F f g h : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (hh : FUNCT_1.isFunction h)
    (hd : RELAT_1.dom h = RELAT_1.dom (applied F f g))
    (hv : ∀ z, z ∈ RELAT_1.dom (applied F f g) →
      FUNCT_1.apply h z =
        BINOP_1.apply2 F (FUNCT_1.apply f z) (FUNCT_1.apply g z)) :
    h = applied F f g := by
  refine FUNCT_1.th2 hh (applied_isFunction hF hf hg) hd ?_
  intro z hz
  have hzA : z ∈ RELAT_1.dom (applied F f g) :=
    Eq.subst (motive := fun s => z ∈ s) hd hz
  exact (hv z hzA).trans (lm1 hF.2 hf hg hzA).symm

/-- Unlabeled `FUNCOP_1` (`Th22`) -/
theorem th22 {F f g x : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (hx : x ∈ RELAT_1.dom (applied F f g)) :
    FUNCT_1.apply (applied F f g) x =
      BINOP_1.apply2 F (FUNCT_1.apply f x) (FUNCT_1.apply g x) :=
  lm1 hF.2 hf hg hx

/-- `FUNCOP_1:23` (`Th23`) -/
theorem th23 {F f g h A : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (hh : FUNCT_1.isFunction h)
    (heq : RELAT_1.restrict f A = RELAT_1.restrict g A) :
    RELAT_1.restrict (applied F f h) A =
      RELAT_1.restrict (applied F g h) A := by
  have h1 : RELAT_1.restrict (applied F f h) A =
      RELAT_1.comp (RELAT_1.restrict (FUNCT_3.complex f h) A) F :=
    RELAT_1.th83
  have h2 : RELAT_1.restrict (FUNCT_3.complex f h) A =
      FUNCT_3.complex (RELAT_1.restrict f A) h := th5 hf hh
  have h3 : FUNCT_3.complex (RELAT_1.restrict f A) h =
      FUNCT_3.complex (RELAT_1.restrict g A) h :=
    congrArg (fun s => FUNCT_3.complex s h) heq
  have h4 : FUNCT_3.complex (RELAT_1.restrict g A) h =
      RELAT_1.restrict (FUNCT_3.complex g h) A := (th5 hg hh).symm
  have h5 : RELAT_1.comp (RELAT_1.restrict (FUNCT_3.complex g h) A) F =
      RELAT_1.restrict (applied F g h) A := (RELAT_1.th83).symm
  exact h1.trans ((congrArg (fun s => RELAT_1.comp s F)
    (h2.trans (h3.trans h4))).trans h5)

/-- `FUNCOP_1:24` (`Th24`) -/
theorem th24 {F f g h A : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (hh : FUNCT_1.isFunction h)
    (heq : RELAT_1.restrict f A = RELAT_1.restrict g A) :
    RELAT_1.restrict (applied F h f) A =
      RELAT_1.restrict (applied F h g) A := by
  have h1 : RELAT_1.restrict (applied F h f) A =
      RELAT_1.comp (RELAT_1.restrict (FUNCT_3.complex h f) A) F :=
    RELAT_1.th83
  have h2 : RELAT_1.restrict (FUNCT_3.complex h f) A =
      FUNCT_3.complex h (RELAT_1.restrict f A) := th6 hh hf
  have h3 : FUNCT_3.complex h (RELAT_1.restrict f A) =
      FUNCT_3.complex h (RELAT_1.restrict g A) :=
    congrArg (FUNCT_3.complex h) heq
  have h4 : FUNCT_3.complex h (RELAT_1.restrict g A) =
      RELAT_1.restrict (FUNCT_3.complex h g) A := (th6 hh hg).symm
  have h5 : RELAT_1.comp (RELAT_1.restrict (FUNCT_3.complex h g) A) F =
      RELAT_1.restrict (applied F h g) A := (RELAT_1.th83).symm
  exact h1.trans ((congrArg (fun s => RELAT_1.comp s F)
    (h2.trans (h3.trans h4))).trans h5)

/-- `FUNCOP_1:25` (`Th25`) -/
theorem th25 {F f g h : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (hh : FUNCT_1.isFunction h) :
    RELAT_1.comp h (applied F f g) =
      applied F (RELAT_1.comp h f) (RELAT_1.comp h g) := by
  have h1 : RELAT_1.comp h (applied F f g) =
      RELAT_1.comp (RELAT_1.comp h (FUNCT_3.complex f g)) F :=
    (RELAT_1.th36).symm
  have h2 : RELAT_1.comp h (FUNCT_3.complex f g) =
      FUNCT_3.complex (RELAT_1.comp h f) (RELAT_1.comp h g) :=
    (FUNCT_3.th55 hf hg hh).symm
  exact h1.trans (congrArg (fun s => RELAT_1.comp s F) h2)

/-! ## `F[:](f,x)` (`FUNCOP_1:def 4`) -/

/-- `FUNCOP_1:def 4` — `F[:](f,x)`. -/
noncomputable def appliedRight (F f x : TarskiSet.{u}) : TarskiSet.{u} :=
  applied F f (mapsTo (RELAT_1.dom f) x)

theorem def4 (F f x : TarskiSet.{u}) :
    appliedRight F f x = applied F f (mapsTo (RELAT_1.dom f) x) :=
  rfl

theorem appliedRight_isFunction {F f x : TarskiSet.{u}}
    (hF : FUNCT_1.isFunction F) (hf : FUNCT_1.isFunction f) :
    FUNCT_1.isFunction (appliedRight F f x) :=
  applied_isFunction hF hf (mapsTo_isFunction _ _)

/-- Unlabeled `FUNCOP_1` (`Th26`) -/
theorem th26 (F f x : TarskiSet.{u}) :
    appliedRight F f x = applied F f (mapsTo (RELAT_1.dom f) x) :=
  rfl

/-- `FUNCOP_1:27` (`Th27`) -/
theorem th27 {F f z x : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f)
    (hx : x ∈ RELAT_1.dom (appliedRight F f z)) :
    FUNCT_1.apply (appliedRight F f z) x =
      BINOP_1.apply2 F (FUNCT_1.apply f x) z := by
  have hxC : x ∈ RELAT_1.dom (FUNCT_3.complex f (mapsTo (RELAT_1.dom f) z)) :=
    ((FUNCT_1.th11 (FUNCT_3.complex_isFunction f _).2).mp hx).1
  have hxI : x ∈ RELAT_1.dom f ∩ RELAT_1.dom (mapsTo (RELAT_1.dom f) z) :=
    Eq.subst (motive := fun s => x ∈ s) (FUNCT_3.complex_dom f _) hxC
  have hxF : x ∈ RELAT_1.dom f := ((XBOOLE_0.def4 _ _ _).mp hxI).1
  have happ : FUNCT_1.apply (appliedRight F f z) x =
      BINOP_1.apply2 F (FUNCT_1.apply f x)
        (FUNCT_1.apply (mapsTo (RELAT_1.dom f) z) x) :=
    lm1 hF.2 hf (mapsTo_isFunction _ _) hx
  exact happ.trans (congrArg (BINOP_1.apply2 F (FUNCT_1.apply f x))
    (th7 hxF))

/-- Unlabeled `FUNCOP_1` (`Th28`) -/
theorem th28 {F f g x A : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (heq : RELAT_1.restrict f A = RELAT_1.restrict g A) :
    RELAT_1.restrict (appliedRight F f x) A =
      RELAT_1.restrict (appliedRight F g x) A := by
  have hdom : RELAT_1.dom f ∩ A = RELAT_1.dom g ∩ A := by
    have h1 : RELAT_1.dom f ∩ A = RELAT_1.dom (RELAT_1.restrict f A) :=
      (RELAT_1.th61).symm
    have h2 : RELAT_1.dom (RELAT_1.restrict f A) =
        RELAT_1.dom (RELAT_1.restrict g A) := congrArg RELAT_1.dom heq
    exact h1.trans (h2.trans (RELAT_1.th61))
  have hmaps : RELAT_1.restrict (mapsTo (RELAT_1.dom f) x) A =
      RELAT_1.restrict (mapsTo (RELAT_1.dom g) x) A := by
    have h1 : RELAT_1.restrict (mapsTo (RELAT_1.dom f) x) A =
        mapsTo (RELAT_1.dom f ∩ A) x := th12
    have h2 : mapsTo (RELAT_1.dom f ∩ A) x =
        mapsTo (RELAT_1.dom g ∩ A) x := congrArg (fun s => mapsTo s x) hdom
    exact h1.trans (h2.trans th12.symm)
  have h1 : RELAT_1.restrict (appliedRight F f x) A =
      RELAT_1.restrict (applied F f (mapsTo (RELAT_1.dom f) x)) A := rfl
  have h2 := th23 hF hf hg (mapsTo_isFunction (RELAT_1.dom f) x) heq
  have h3 := th24 hF (mapsTo_isFunction (RELAT_1.dom f) x)
    (mapsTo_isFunction (RELAT_1.dom g) x) hg hmaps
  -- (applied F g (mapsTo (dom f) x))|A = (applied F g (mapsTo (dom g) x))|A
  exact h1.trans (h2.trans (h3.trans rfl))

/-- `FUNCOP_1:29` (`Th29`) -/
theorem th29 {F f x h : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f) (hh : FUNCT_1.isFunction h) :
    RELAT_1.comp h (appliedRight F f x) =
      appliedRight F (RELAT_1.comp h f) x := by
  have hd : RELAT_1.dom (mapsTo (RELAT_1.dom f) x) = RELAT_1.dom f :=
    mapsTo_dom _ _
  have hdomComp : RELAT_1.dom (RELAT_1.comp h (mapsTo (RELAT_1.dom f) x)) =
      RELAT_1.dom (RELAT_1.comp h f) :=
    RELAT_1.th163 hd
  have hv : ∀ z, z ∈ RELAT_1.dom (RELAT_1.comp h (mapsTo (RELAT_1.dom f) x)) →
      FUNCT_1.apply (RELAT_1.comp h (mapsTo (RELAT_1.dom f) x)) z = x := by
    intro z hz
    have ⟨_, hhz⟩ := (FUNCT_1.th11 hh.2).mp hz
    have hhzD : FUNCT_1.apply h z ∈ RELAT_1.dom (mapsTo (RELAT_1.dom f) x) :=
      hhz
    have hhzF : FUNCT_1.apply h z ∈ RELAT_1.dom f :=
      Eq.subst (motive := fun s => FUNCT_1.apply h z ∈ s) hd hhzD
    exact (FUNCT_1.th12 hh.2 (mapsTo_isFunctionLike _ _) hz).trans (th7 hhzF)
  have hmaps : RELAT_1.comp h (mapsTo (RELAT_1.dom f) x) =
      mapsTo (RELAT_1.dom (RELAT_1.comp h f)) x := by
    have hconst := th11 (FUNCT_1.comp_isFunction hh (mapsTo_isFunction _ _)) hv
    exact hconst.trans (congrArg (fun s => mapsTo s x) hdomComp)
  have h1 : RELAT_1.comp h (appliedRight F f x) =
      RELAT_1.comp h (applied F f (mapsTo (RELAT_1.dom f) x)) := rfl
  have h2 : RELAT_1.comp h (applied F f (mapsTo (RELAT_1.dom f) x)) =
      applied F (RELAT_1.comp h f)
        (RELAT_1.comp h (mapsTo (RELAT_1.dom f) x)) :=
    th25 hF hf (mapsTo_isFunction _ _) hh
  exact h1.trans (h2.trans (congrArg (applied F (RELAT_1.comp h f)) hmaps))

/-- Unlabeled `FUNCOP_1` (`Th30`) -/
theorem th30 {F f x A : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f) :
    RELAT_1.comp (RELAT_1.id A) (appliedRight F f x) =
      appliedRight F (RELAT_1.restrict f A) x := by
  have h1 : RELAT_1.comp (RELAT_1.id A) (appliedRight F f x) =
      appliedRight F (RELAT_1.comp (RELAT_1.id A) f) x :=
    th29 (F := F) (f := f) (x := x) (h := RELAT_1.id A) hF hf
      (FUNCT_1.id_isFunction A)
  exact h1.trans (congrArg (fun s => appliedRight F s x)
    (RELAT_1.th65 (R := f) (X := A)).symm)

/-! ## `F[;](x,g)` (`FUNCOP_1:def 5`) -/

/-- `FUNCOP_1:def 5` — `F[;](x,g)`. -/
noncomputable def appliedLeft (F x g : TarskiSet.{u}) : TarskiSet.{u} :=
  applied F (mapsTo (RELAT_1.dom g) x) g

theorem def5 (F x g : TarskiSet.{u}) :
    appliedLeft F x g = applied F (mapsTo (RELAT_1.dom g) x) g :=
  rfl

theorem appliedLeft_isFunction {F x g : TarskiSet.{u}}
    (hF : FUNCT_1.isFunction F) (hg : FUNCT_1.isFunction g) :
    FUNCT_1.isFunction (appliedLeft F x g) :=
  applied_isFunction hF (mapsTo_isFunction _ _) hg

/-- Unlabeled `FUNCOP_1` (`Th31`) -/
theorem th31 (F x g : TarskiSet.{u}) :
    appliedLeft F x g = applied F (mapsTo (RELAT_1.dom g) x) g :=
  rfl

/-- `FUNCOP_1:32` (`Th32`) -/
theorem th32 {F z f x : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f)
    (hx : x ∈ RELAT_1.dom (appliedLeft F z f)) :
    FUNCT_1.apply (appliedLeft F z f) x =
      BINOP_1.apply2 F z (FUNCT_1.apply f x) := by
  have hxC : x ∈ RELAT_1.dom
      (FUNCT_3.complex (mapsTo (RELAT_1.dom f) z) f) :=
    ((FUNCT_1.th11 (FUNCT_3.complex_isFunction _ f).2).mp hx).1
  have hxI : x ∈ RELAT_1.dom (mapsTo (RELAT_1.dom f) z) ∩ RELAT_1.dom f :=
    Eq.subst (motive := fun s => x ∈ s) (FUNCT_3.complex_dom _ f) hxC
  have hxF : x ∈ RELAT_1.dom f := ((XBOOLE_0.def4 _ _ _).mp hxI).2
  have happ : FUNCT_1.apply (appliedLeft F z f) x =
      BINOP_1.apply2 F (FUNCT_1.apply (mapsTo (RELAT_1.dom f) z) x)
        (FUNCT_1.apply f x) :=
    lm1 hF.2 (mapsTo_isFunction _ _) hf hx
  exact happ.trans (congrArg (fun t => BINOP_1.apply2 F t (FUNCT_1.apply f x))
    (th7 hxF))

/-- Unlabeled `FUNCOP_1` (`Th33`) -/
theorem th33 {F f g x A : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (heq : RELAT_1.restrict f A = RELAT_1.restrict g A) :
    RELAT_1.restrict (appliedLeft F x f) A =
      RELAT_1.restrict (appliedLeft F x g) A := by
  have hdom : RELAT_1.dom f ∩ A = RELAT_1.dom g ∩ A := by
    have h1 : RELAT_1.dom f ∩ A = RELAT_1.dom (RELAT_1.restrict f A) :=
      (RELAT_1.th61).symm
    exact h1.trans ((congrArg RELAT_1.dom heq).trans RELAT_1.th61)
  have hmaps : RELAT_1.restrict (mapsTo (RELAT_1.dom f) x) A =
      RELAT_1.restrict (mapsTo (RELAT_1.dom g) x) A :=
    (th12).trans ((congrArg (fun s => mapsTo s x) hdom).trans th12.symm)
  have h2 := th24 hF hf hg (mapsTo_isFunction (RELAT_1.dom f) x) heq
  have h3 := th23 hF (mapsTo_isFunction (RELAT_1.dom f) x)
    (mapsTo_isFunction (RELAT_1.dom g) x) hg hmaps
  exact h2.trans h3

/-- `FUNCOP_1:34` (`Th34`) -/
theorem th34 {F x f h : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f) (hh : FUNCT_1.isFunction h) :
    RELAT_1.comp h (appliedLeft F x f) =
      appliedLeft F x (RELAT_1.comp h f) := by
  have hd : RELAT_1.dom (mapsTo (RELAT_1.dom f) x) = RELAT_1.dom f :=
    mapsTo_dom _ _
  have hdomComp : RELAT_1.dom (RELAT_1.comp h (mapsTo (RELAT_1.dom f) x)) =
      RELAT_1.dom (RELAT_1.comp h f) := RELAT_1.th163 hd
  have hv : ∀ z, z ∈ RELAT_1.dom (RELAT_1.comp h (mapsTo (RELAT_1.dom f) x)) →
      FUNCT_1.apply (RELAT_1.comp h (mapsTo (RELAT_1.dom f) x)) z = x := by
    intro z hz
    have ⟨_, hhz⟩ := (FUNCT_1.th11 hh.2).mp hz
    have hhzF : FUNCT_1.apply h z ∈ RELAT_1.dom f :=
      Eq.subst (motive := fun s => FUNCT_1.apply h z ∈ s) hd hhz
    exact (FUNCT_1.th12 hh.2 (mapsTo_isFunctionLike _ _) hz).trans (th7 hhzF)
  have hmaps : RELAT_1.comp h (mapsTo (RELAT_1.dom f) x) =
      mapsTo (RELAT_1.dom (RELAT_1.comp h f)) x :=
    (th11 (FUNCT_1.comp_isFunction hh (mapsTo_isFunction _ _)) hv).trans
      (congrArg (fun s => mapsTo s x) hdomComp)
  have h2 : RELAT_1.comp h (applied F (mapsTo (RELAT_1.dom f) x) f) =
      applied F (RELAT_1.comp h (mapsTo (RELAT_1.dom f) x)) (RELAT_1.comp h f) :=
    th25 hF (mapsTo_isFunction (RELAT_1.dom f) x) hf hh
  exact h2.trans (congrArg (fun s => applied F s (RELAT_1.comp h f)) hmaps)

/-- Unlabeled `FUNCOP_1` (`Th35`) -/
theorem th35 {F x f A : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f) :
    RELAT_1.comp (RELAT_1.id A) (appliedLeft F x f) =
      appliedLeft F x (RELAT_1.restrict f A) := by
  have h1 : RELAT_1.comp (RELAT_1.id A) (appliedLeft F x f) =
      appliedLeft F x (RELAT_1.comp (RELAT_1.id A) f) :=
    th34 (F := F) (x := x) (f := f) (h := RELAT_1.id A) hF hf
      (FUNCT_1.id_isFunction A)
  exact h1.trans (congrArg (appliedLeft F x)
    (RELAT_1.th65 (R := f) (X := A)).symm)


/-! ## Typed redefinitions for `BinOp` / `Function of` -/

private theorem mapsTo_isFunctionOf (A x B : TarskiSet.{u}) (hx : x ∈ B) :
    FUNCT_2.isFunctionOf (mapsTo A x) A B := by
  have hrng : RELAT_1.rng (mapsTo A x) ⊆ B :=
    XBOOLE_1.th1 (th13 A x).2 ((ZFMISC_1.th31).mpr hx)
  exact FUNCT_2.functionOf_of (mapsTo_isFunction A x) (mapsTo_dom A x) hrng

/-- `FUNCOP_1:36` (`Th36`) -/
theorem th36 {X Y F f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hg : FUNCT_2.isFunctionOf g Y X) :
    FUNCT_2.isFunctionOf (applied F f g) Y X := by
  have hXX : X ≠ (∅ : TarskiSet.{u}) → Y = (∅ : TarskiSet.{u}) →
      Y = (∅ : TarskiSet.{u}) := fun _ h => h
  have hc : FUNCT_2.isFunctionOf (FUNCT_3.complex f g) Y
      (ZFMISC_1.product X X) :=
    FUNCT_3.th58 hf hg (fun h => (hX h).elim) (fun h => (hX h).elim)
  have hF' : FUNCT_2.isFunctionOf F (ZFMISC_1.product X X) X := hF
  refine ⟨⟨FUNCT_1.comp_isFunction (FUNCT_2.functionOf_isFunction hc)
      (FUNCT_2.functionOf_isFunction hF'),
    RELSET_1.comp_isRelationOf (FUNCT_2.functionOf_isRelationOf hc)
      (FUNCT_2.functionOf_isRelationOf hF')⟩, ?_⟩
  exact FUNCT_2.th13 (FUNCT_2.functionOf_isRelationOf hc) hc.2
    (FUNCT_2.functionOf_isRelationOf hF') hF'.2
    (fun hP =>
      Or.inr (Or.elim ((ZFMISC_1.th90).mp hP)
        (fun h => (hX h).elim) (fun h => (hX h).elim)))

/-- Redefine: `F.:(f,g)` is `Function of Z,X` for BinOp. -/
theorem applied_isFunctionOf {X Z F f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Z X) (hg : FUNCT_2.isFunctionOf g Z X) :
    FUNCT_2.isFunctionOf (applied F f g) Z X :=
  th36 hX hF hf hg

/-- `FUNCOP_1:37` (`Th37`) -/
theorem th37 {X Y F f g z : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hg : FUNCT_2.isFunctionOf g Y X)
    (hz : z ∈ Y) :
    FUNCT_1.apply (applied F f g) z =
      BINOP_1.apply2 F (FUNCT_1.apply f z) (FUNCT_1.apply g z) := by
  have happ := applied_isFunctionOf hX hF hf hg
  have hdom : RELAT_1.dom (applied F f g) = Y :=
    FUNCT_2.functionOf_dom_eq happ hX
  exact th22 (FUNCT_2.functionOf_isFunction hF)
    (FUNCT_2.functionOf_isFunction hf) (FUNCT_2.functionOf_isFunction hg)
    (Eq.subst (motive := fun s => z ∈ s) hdom.symm hz)

/-- `FUNCOP_1:38` (`Th38`) -/
theorem th38 {X Y F f g h : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hg : FUNCT_2.isFunctionOf g Y X)
    (hh : FUNCT_2.isFunctionOf h Y X)
    (hv : ∀ z, z ∈ Y → FUNCT_1.apply h z =
      BINOP_1.apply2 F (FUNCT_1.apply f z) (FUNCT_1.apply g z)) :
    h = applied F f g :=
  FUNCT_2.th63 hh (applied_isFunctionOf hX hF hf hg) fun z hz =>
    (hv z hz).trans (th37 hX hY hF hf hg hz).symm

/-- Unlabeled `FUNCOP_1` (`Th39`) -/
theorem th39 {X Y F f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Y X)
    (hg : FUNCT_2.isFunctionOf g X X) :
    RELAT_1.comp f (applied F (RELAT_1.id X) g) =
      applied F f (RELAT_1.comp f g) := by
  have h1 := th25 (FUNCT_2.functionOf_isFunction hF)
    (FUNCT_1.id_isFunction X) (FUNCT_2.functionOf_isFunction hg)
    (FUNCT_2.functionOf_isFunction hf)
  have hid : RELAT_1.comp f (RELAT_1.id X) = f :=
    (FUNCT_2.th17 (FUNCT_2.functionOf_isRelationOf hf)).2
  exact h1.trans (congrArg (fun s => applied F s (RELAT_1.comp f g)) hid)

/-- Unlabeled `FUNCOP_1` (`Th40`) -/
theorem th40 {X Y F f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Y X)
    (hg : FUNCT_2.isFunctionOf g X X) :
    RELAT_1.comp f (applied F g (RELAT_1.id X)) =
      applied F (RELAT_1.comp f g) f := by
  have h1 := th25 (FUNCT_2.functionOf_isFunction hF)
    (FUNCT_2.functionOf_isFunction hg) (FUNCT_1.id_isFunction X)
    (FUNCT_2.functionOf_isFunction hf)
  have hid : RELAT_1.comp f (RELAT_1.id X) = f :=
    (FUNCT_2.th17 (FUNCT_2.functionOf_isRelationOf hf)).2
  exact h1.trans (congrArg (applied F (RELAT_1.comp f g)) hid)

/-- Unlabeled `FUNCOP_1` (`Th41`) -/
theorem th41 {X Y F f : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Y X) :
    RELAT_1.comp f (applied F (RELAT_1.id X) (RELAT_1.id X)) =
      applied F f f := by
  have h1 := th25 (FUNCT_2.functionOf_isFunction hF)
    (FUNCT_1.id_isFunction X) (FUNCT_1.id_isFunction X)
    (FUNCT_2.functionOf_isFunction hf)
  have hid : RELAT_1.comp f (RELAT_1.id X) = f :=
    (FUNCT_2.th17 (FUNCT_2.functionOf_isRelationOf hf)).2
  exact h1.trans ((congrArg (fun s => applied F s (RELAT_1.comp f (RELAT_1.id X)))
    hid).trans (congrArg (applied F f) hid))

/-- Unlabeled `FUNCOP_1` (`Th42`) -/
theorem th42 {X F g x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hg : FUNCT_2.isFunctionOf g X X) (hx : x ∈ X) :
    FUNCT_1.apply (applied F (RELAT_1.id X) g) x =
      BINOP_1.apply2 F x (FUNCT_1.apply g x) := by
  have happ := th37 hX hX hF (id_isFunctionOf X) hg hx
  exact happ.trans (congrArg (fun t => BINOP_1.apply2 F t (FUNCT_1.apply g x))
    (FUNCT_1.th18 hx))

/-- Unlabeled `FUNCOP_1` (`Th43`) -/
theorem th43 {X F g x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hg : FUNCT_2.isFunctionOf g X X) (hx : x ∈ X) :
    FUNCT_1.apply (applied F g (RELAT_1.id X)) x =
      BINOP_1.apply2 F (FUNCT_1.apply g x) x := by
  have happ := th37 hX hX hF hg (id_isFunctionOf X) hx
  exact happ.trans (congrArg (BINOP_1.apply2 F (FUNCT_1.apply g x))
    (FUNCT_1.th18 hx))

/-- Unlabeled `FUNCOP_1` (`Th44`) -/
theorem th44 {X F x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hx : x ∈ X) :
    FUNCT_1.apply (applied F (RELAT_1.id X) (RELAT_1.id X)) x =
      BINOP_1.apply2 F x x := by
  have happ := th37 hX hX hF (id_isFunctionOf X) (id_isFunctionOf X) hx
  exact happ.trans
    ((congrArg (fun t => BINOP_1.apply2 F t (FUNCT_1.apply (RELAT_1.id X) x))
      (FUNCT_1.th18 hx)).trans
      (congrArg (BINOP_1.apply2 F x) (FUNCT_1.th18 hx)))

/-- `FUNCOP_1:45` (`Th45`) -/
theorem th45 (A B x : TarskiSet.{u}) (hx : x ∈ B) :
    FUNCT_2.isFunctionOf (mapsTo A x) A B :=
  mapsTo_isFunctionOf A x B hx

/-- Redefine: `I --> i` is `Function of I,{i}`. -/
theorem mapsTo_isFunctionOf_singleton (I i : TarskiSet.{u}) :
    FUNCT_2.isFunctionOf (mapsTo I i) I (TARSKI.singleton i) :=
  mapsTo_isFunctionOf I i (TARSKI.singleton i)
    ((TARSKI.singleton_iff i i).mpr rfl)

/-- Redefine: `A --> b` for `b ∈ B` nonempty. -/
theorem mapsTo_isFunctionOf_element {A B b : TarskiSet.{u}}
    (hB : B ≠ (∅ : TarskiSet.{u})) (hb : SUBSET_1.isElement b B) :
    FUNCT_2.isFunctionOf (mapsTo A b) A B :=
  mapsTo_isFunctionOf A b B (SUBSET_1.isElement_mem (ne_imp_not_empty hB) hb)


/-- Unlabeled `FUNCOP_1` (`Th46`). Mizar states this without `x ∈ X`;
all in-tree citations have `x ∈ X` (or empty domain). -/
theorem th46 {A X x : TarskiSet.{u}} (hx : x ∈ X) :
    FUNCT_2.isFunctionOf (mapsTo A x) A X :=
  mapsTo_isFunctionOf A x X hx

/-- `FUNCOP_1:47` (`Th47`) -/
theorem th47 {X Y F f x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hx : SUBSET_1.isElement x X) :
    FUNCT_2.isFunctionOf (appliedRight F f x) Y X := by
  have hd : RELAT_1.dom f = Y ∨ Y = (∅ : TarskiSet.{u}) := by
    have := Classical.propDecidable (X = (∅ : TarskiSet.{u}))
    -- dom f = Y when X nonempty via functionOf_dom_eq
    exact Or.inl (FUNCT_2.functionOf_dom_eq hf hX)
  have hmaps : FUNCT_2.isFunctionOf (mapsTo (RELAT_1.dom f) x) Y X := by
    have hxmem : x ∈ X := SUBSET_1.isElement_mem (ne_imp_not_empty hX) hx
    have hdom : RELAT_1.dom f = Y := FUNCT_2.functionOf_dom_eq hf hX
    exact Eq.subst (motive := fun s =>
        FUNCT_2.isFunctionOf (mapsTo s x) Y X) hdom.symm
      (mapsTo_isFunctionOf Y x X hxmem)
  exact applied_isFunctionOf hX hF hf hmaps

/-- Redefine appliedRight as Function of. -/
theorem appliedRight_isFunctionOf {X Z F f x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Z X) (hx : SUBSET_1.isElement x X) :
    FUNCT_2.isFunctionOf (appliedRight F f x) Z X :=
  th47 hX hF hf hx

/-- `FUNCOP_1:48` (`Th48`) -/
theorem th48 {X Y F f x y : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hx : SUBSET_1.isElement x X)
    (hy : y ∈ Y) :
    FUNCT_1.apply (appliedRight F f x) y =
      BINOP_1.apply2 F (FUNCT_1.apply f y) x := by
  have happ := appliedRight_isFunctionOf hX hF hf hx
  have hdom : RELAT_1.dom (appliedRight F f x) = Y :=
    FUNCT_2.functionOf_dom_eq happ hX
  exact th27 (FUNCT_2.functionOf_isFunction hF)
    (FUNCT_2.functionOf_isFunction hf)
    (Eq.subst (motive := fun s => y ∈ s) hdom.symm hy)

/-- `FUNCOP_1:49` (`Th49`) -/
theorem th49 {X Y F f g x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hg : FUNCT_2.isFunctionOf g Y X)
    (hx : SUBSET_1.isElement x X)
    (hv : ∀ y, y ∈ Y → FUNCT_1.apply g y =
      BINOP_1.apply2 F (FUNCT_1.apply f y) x) :
    g = appliedRight F f x :=
  FUNCT_2.th63 hg (appliedRight_isFunctionOf hX hF hf hx) fun y hy =>
    (hv y hy).trans (th48 hX hY hF hf hx hy).symm

/-- Unlabeled `FUNCOP_1` (`Th50`) -/
theorem th50 {X Y F f x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hx : SUBSET_1.isElement x X) :
    RELAT_1.comp f (appliedRight F (RELAT_1.id X) x) =
      appliedRight F f x := by
  have h1 := th29 (FUNCT_2.functionOf_isFunction hF) (FUNCT_1.id_isFunction X)
    (FUNCT_2.functionOf_isFunction hf) (x := x)
  have hid : RELAT_1.comp f (RELAT_1.id X) = f :=
    (FUNCT_2.th17 (FUNCT_2.functionOf_isRelationOf hf)).2
  exact h1.trans (congrArg (fun s => appliedRight F s x) hid)

/-- Unlabeled `FUNCOP_1` (`Th51`) -/
theorem th51 {X F x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hx : SUBSET_1.isElement x X) :
    FUNCT_1.apply (appliedRight F (RELAT_1.id X) x) x =
      BINOP_1.apply2 F x x := by
  have hxmem : x ∈ X := SUBSET_1.isElement_mem (ne_imp_not_empty hX) hx
  have happ := th48 hX hX hF (id_isFunctionOf X) hx hxmem
  exact happ.trans (congrArg (fun t => BINOP_1.apply2 F t x)
    (FUNCT_1.th18 hxmem))

/-- `FUNCOP_1:52` (`Th52`) -/
theorem th52 {X Y F g x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hg : FUNCT_2.isFunctionOf g Y X) (hx : SUBSET_1.isElement x X) :
    FUNCT_2.isFunctionOf (appliedLeft F x g) Y X := by
  have hxmem : x ∈ X := SUBSET_1.isElement_mem (ne_imp_not_empty hX) hx
  have hdom : RELAT_1.dom g = Y := FUNCT_2.functionOf_dom_eq hg hX
  have hmaps : FUNCT_2.isFunctionOf (mapsTo (RELAT_1.dom g) x) Y X :=
    Eq.subst (motive := fun s => FUNCT_2.isFunctionOf (mapsTo s x) Y X)
      hdom.symm (mapsTo_isFunctionOf Y x X hxmem)
  exact applied_isFunctionOf hX hF hmaps hg

theorem appliedLeft_isFunctionOf {X Z F g x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hg : FUNCT_2.isFunctionOf g Z X) (hx : SUBSET_1.isElement x X) :
    FUNCT_2.isFunctionOf (appliedLeft F x g) Z X :=
  th52 hX hF hg hx

/-- `FUNCOP_1:53` (`Th53`) -/
theorem th53 {X Y F f x y : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hx : SUBSET_1.isElement x X)
    (hy : y ∈ Y) :
    FUNCT_1.apply (appliedLeft F x f) y =
      BINOP_1.apply2 F x (FUNCT_1.apply f y) := by
  have happ := appliedLeft_isFunctionOf hX hF hf hx
  have hdom : RELAT_1.dom (appliedLeft F x f) = Y :=
    FUNCT_2.functionOf_dom_eq happ hX
  exact th32 (FUNCT_2.functionOf_isFunction hF)
    (FUNCT_2.functionOf_isFunction hf)
    (Eq.subst (motive := fun s => y ∈ s) hdom.symm hy)

/-- `FUNCOP_1:54` (`Th54`) -/
theorem th54 {X Y F f g x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hg : FUNCT_2.isFunctionOf g Y X)
    (hx : SUBSET_1.isElement x X)
    (hv : ∀ y, y ∈ Y → FUNCT_1.apply g y =
      BINOP_1.apply2 F x (FUNCT_1.apply f y)) :
    g = appliedLeft F x f :=
  FUNCT_2.th63 hg (appliedLeft_isFunctionOf hX hF hf hx) fun y hy =>
    (hv y hy).trans (th53 hX hY hF hf hx hy).symm

/-- Unlabeled `FUNCOP_1` (`Th55`) -/
theorem th55 {X Y F f x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hx : SUBSET_1.isElement x X) :
    RELAT_1.comp f (appliedLeft F x (RELAT_1.id X)) =
      appliedLeft F x f := by
  have h1 := th34 (FUNCT_2.functionOf_isFunction hF) (FUNCT_1.id_isFunction X)
    (FUNCT_2.functionOf_isFunction hf) (x := x)
  have hid : RELAT_1.comp f (RELAT_1.id X) = f :=
    (FUNCT_2.th17 (FUNCT_2.functionOf_isRelationOf hf)).2
  exact h1.trans (congrArg (appliedLeft F x) hid)

/-- Unlabeled `FUNCOP_1` (`Th56`) -/
theorem th56 {X F x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hx : SUBSET_1.isElement x X) :
    FUNCT_1.apply (appliedLeft F x (RELAT_1.id X)) x =
      BINOP_1.apply2 F x x := by
  have hxmem : x ∈ X := SUBSET_1.isElement_mem (ne_imp_not_empty hX) hx
  have happ := th53 hX hX hF (id_isFunctionOf X) hx hxmem
  exact happ.trans (congrArg (BINOP_1.apply2 F x) (FUNCT_1.th18 hxmem))



/-- Unlabeled `FUNCOP_1` (`Th57`) -/
theorem th57 {X Y Z f x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hZ : Z ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X (ZFMISC_1.product Y Z))
    (hx : x ∈ X) :
    FUNCT_1.apply (tilde f) x =
      TARSKI.pair (XTUPLE_0.snd (FUNCT_1.apply f x))
        (XTUPLE_0.fst (FUNCT_1.apply f x)) := by
  have hPne : ZFMISC_1.product Y Z ≠ (∅ : TarskiSet.{u}) :=
    fun h => Or.elim ((ZFMISC_1.th90).mp h) (fun hY' => hY hY')
      (fun hZ' => hZ hZ')
  have hdom : RELAT_1.dom f = X := FUNCT_2.functionOf_dom_eq hf hPne
  have hxD : x ∈ RELAT_1.dom f :=
    Eq.subst (motive := fun s => x ∈ s) hdom.symm hx
  have hfx : FUNCT_1.apply f x ∈ ZFMISC_1.product Y Z :=
    FUNCT_2.th5 hf hPne hx
  have heq : FUNCT_1.apply f x =
      TARSKI.pair (XTUPLE_0.fst (FUNCT_1.apply f x))
        (XTUPLE_0.snd (FUNCT_1.apply f x)) :=
    MCART_1.th22 hY hZ hfx
  exact tilde_apply_pair hxD heq


private theorem product_isRelationOf (Y Z : TarskiSet.{u}) :
    RELSET_1.isRelationOf (ZFMISC_1.product Y Z) Y Z :=
  RELSET_1.th4 (RELAT_1.product_isRelation Y Z) RELAT_1.th158 RELAT_1.th159

/-- Redefine: `rng f` is `Relation of Y,Z`. -/
theorem rng_isRelationOf_product {X Y Z f : TarskiSet.{u}}
    (hf : FUNCT_2.isFunctionOf f X (ZFMISC_1.product Y Z)) :
    RELSET_1.isRelationOf (RELAT_1.rng f) Y Z :=
  RELSET_1.th1 (product_isRelationOf Y Z) (FUNCT_2.functionOf_rng_sub hf)

/-- Redefine: `f~` is `Function of X, [:Z,Y:]`. -/
theorem tilde_isFunctionOf_product {X Y Z f : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hZ : Z ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X (ZFMISC_1.product Y Z)) :
    FUNCT_2.isFunctionOf (tilde f) X (ZFMISC_1.product Z Y) := by
  have hPne : ZFMISC_1.product Y Z ≠ (∅ : TarskiSet.{u}) :=
    fun h => Or.elim ((ZFMISC_1.th90).mp h) (fun hY' => hY hY')
      (fun hZ' => hZ hZ')
  have hPne' : ZFMISC_1.product Z Y ≠ (∅ : TarskiSet.{u}) :=
    fun h => Or.elim ((ZFMISC_1.th90).mp h) (fun hZ' => hZ hZ')
      (fun hY' => hY hY')
  have hdom : RELAT_1.dom (tilde f) = X :=
    (tilde_dom f).trans (FUNCT_2.functionOf_dom_eq hf hPne)
  have hrng : RELAT_1.rng (tilde f) ⊆ ZFMISC_1.product Z Y := by
    intro w hw
    obtain ⟨x, hxD, heq⟩ := (FUNCT_1.def3 (tilde_isFunction f).2).mp hw
    have hx : x ∈ X := Eq.subst (motive := fun s => x ∈ s) hdom hxD
    have hfx : FUNCT_1.apply f x ∈ ZFMISC_1.product Y Z :=
      FUNCT_2.th5 hf hPne hx
    have heqF : FUNCT_1.apply f x =
        TARSKI.pair (XTUPLE_0.fst (FUNCT_1.apply f x))
          (XTUPLE_0.snd (FUNCT_1.apply f x)) :=
      MCART_1.th22 hY hZ hfx
    have hxDf : x ∈ RELAT_1.dom f :=
      Eq.subst (motive := fun s => x ∈ s)
        (FUNCT_2.functionOf_dom_eq hf hPne).symm hx
    have ht : FUNCT_1.apply (tilde f) x =
        TARSKI.pair (XTUPLE_0.snd (FUNCT_1.apply f x))
          (XTUPLE_0.fst (FUNCT_1.apply f x)) :=
      tilde_apply_pair hxDf heqF
    have hmem : TARSKI.pair (XTUPLE_0.snd (FUNCT_1.apply f x))
        (XTUPLE_0.fst (FUNCT_1.apply f x)) ∈ ZFMISC_1.product Z Y := by
      have ⟨a, b, ha, hb, hp⟩ := (ZFMISC_1.def2 Y Z (FUNCT_1.apply f x)).mp hfx
      have hfsta : XTUPLE_0.fst (FUNCT_1.apply f x) = a :=
        Eq.subst (motive := fun s => XTUPLE_0.fst s = a) hp.symm
          (XTUPLE_0.fst_pair a b)
      have hsndb : XTUPLE_0.snd (FUNCT_1.apply f x) = b :=
        Eq.subst (motive := fun s => XTUPLE_0.snd s = b) hp.symm
          (XTUPLE_0.snd_pair a b)
      exact (ZFMISC_1.th87).mpr
        ⟨Eq.subst (motive := fun s => s ∈ Z) hsndb.symm hb,
          Eq.subst (motive := fun s => s ∈ Y) hfsta.symm ha⟩
    exact Eq.subst (motive := fun s => s ∈ ZFMISC_1.product Z Y)
      (heq.trans ht).symm hmem
  exact FUNCT_2.functionOf_of (tilde_isFunction f) hdom hrng


/-- Unlabeled `FUNCOP_1` (`Th58`) — `rng(f~) = (rng f)~`. -/
theorem th58 {X Y Z f : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hZ : Z ≠ (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f X (ZFMISC_1.product Y Z)) :
    RELAT_1.rng (tilde f) = RELAT_1.converse (RELAT_1.rng f) := by
  have hPne : ZFMISC_1.product Y Z ≠ (∅ : TarskiSet.{u}) :=
    fun h => Or.elim ((ZFMISC_1.th90).mp h) (fun hY' => hY hY')
      (fun hZ' => hZ hZ')
  apply eq_of_mem; intro w; constructor
  · intro hw
    obtain ⟨x, hxD, heq⟩ := (FUNCT_1.def3 (tilde_isFunction f).2).mp hw
    have hx : x ∈ X :=
      Eq.subst (motive := fun s => x ∈ s)
        ((tilde_dom f).trans (FUNCT_2.functionOf_dom_eq hf hPne)) hxD
    have hxDf : x ∈ RELAT_1.dom f :=
      Eq.subst (motive := fun s => x ∈ s)
        (FUNCT_2.functionOf_dom_eq hf hPne).symm hx
    have hfx : FUNCT_1.apply f x ∈ ZFMISC_1.product Y Z :=
      FUNCT_2.th5 hf hPne hx
    obtain ⟨a, b, ha, hb, hp⟩ := (ZFMISC_1.def2 Y Z _).mp hfx
    have ht : FUNCT_1.apply (tilde f) x = TARSKI.pair b a :=
      tilde_apply_pair hxDf hp
    have hw' : w = TARSKI.pair b a := heq.trans ht
    have hab : TARSKI.pair a b ∈ RELAT_1.rng f :=
      (FUNCT_1.def3 (FUNCT_2.functionOf_isFunction hf).2).mpr
        ⟨x, hxDf, hp.symm⟩
    exact Eq.subst (motive := fun s => s ∈ RELAT_1.converse (RELAT_1.rng f))
      hw'.symm ((RELAT_1.def7 (RELAT_1.rng f) b a).mpr hab)
  · intro hw
    have hab : ∃ a b, w = TARSKI.pair b a ∧ TARSKI.pair a b ∈ RELAT_1.rng f := by
      -- w in converse(rng) means ∃ decomposition
      have ⟨a, b, heq, hp⟩ : ∃ a b, w = TARSKI.pair a b ∧
          TARSKI.pair b a ∈ RELAT_1.rng f := by
        -- use converse char
        have hwR : RELAT_1.isRelation (RELAT_1.converse (RELAT_1.rng f)) :=
          RELAT_1.converse_isRelation _
        obtain ⟨u, v, heq⟩ := hwR w hw
        refine ⟨u, v, heq, (RELAT_1.def7 _ u v).mp
          (Eq.subst (motive := fun s => s ∈ RELAT_1.converse (RELAT_1.rng f))
            heq hw)⟩
      exact ⟨b, a, heq, hp⟩
    obtain ⟨a, b, hwab, hab⟩ := hab
    obtain ⟨x, hxD, hfx⟩ :=
      (FUNCT_1.def3 (FUNCT_2.functionOf_isFunction hf).2).mp hab
    have ht : FUNCT_1.apply (tilde f) x = TARSKI.pair b a :=
      tilde_apply_pair hxD hfx.symm
    have hxT : x ∈ RELAT_1.dom (tilde f) :=
      Eq.subst (motive := fun s => x ∈ s) (tilde_dom f).symm hxD
    exact (FUNCT_1.def3 (tilde_isFunction f).2).mpr
      ⟨x, hxT, hwab.trans ht.symm⟩


/-- Helper: both sides empty when domain `Y` is empty. -/
private theorem functionOf_of_empty_dom {X Y f g : TarskiSet.{u}}
    (hY : Y = (∅ : TarskiSet.{u}))
    (hf : FUNCT_2.isFunctionOf f Y X) (hg : FUNCT_2.isFunctionOf g Y X) :
    f = g := by
  have hdF : RELAT_1.dom f = (∅ : TarskiSet.{u}) := by
    apply eq_of_mem; intro z; constructor
    · intro hz
      exact Eq.subst (motive := fun s => z ∈ s) hY
        (FUNCT_2.functionOf_dom_sub hf z hz)
    · intro hz
      exact ((XBOOLE_0.empty_iff z).mp hz).elim
  have hdG : RELAT_1.dom g = (∅ : TarskiSet.{u}) := by
    apply eq_of_mem; intro z; constructor
    · intro hz
      exact Eq.subst (motive := fun s => z ∈ s) hY
        (FUNCT_2.functionOf_dom_sub hg z hz)
    · intro hz
      exact ((XBOOLE_0.empty_iff z).mp hz).elim
  have hfE : f = (∅ : TarskiSet.{u}) :=
    RELAT_1.th41 (FUNCT_2.functionOf_isFunction hf).1 (Or.inl hdF)
  have hgE : g = (∅ : TarskiSet.{u}) :=
    RELAT_1.th41 (FUNCT_2.functionOf_isFunction hg).1 (Or.inl hdG)
  exact hfE.trans hgE.symm

/-- Unlabeled `FUNCOP_1` (`Th59`) -/
theorem th59 {X Y F f x1 x2 : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hassoc : BINOP_1.isAssociative F X)
    (hf : FUNCT_2.isFunctionOf f Y X)
    (hx1 : SUBSET_1.isElement x1 X) (hx2 : SUBSET_1.isElement x2 X) :
    appliedRight F (appliedLeft F x1 f) x2 =
      appliedLeft F x1 (appliedRight F f x2) := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact functionOf_of_empty_dom hY
      (appliedRight_isFunctionOf hX hF (appliedLeft_isFunctionOf hX hF hf hx1) hx2)
      (appliedLeft_isFunctionOf hX hF (appliedRight_isFunctionOf hX hF hf hx2) hx1)
  · refine th54 hX hY hF
      (appliedRight_isFunctionOf hX hF hf hx2)
      (appliedRight_isFunctionOf hX hF (appliedLeft_isFunctionOf hX hF hf hx1) hx2)
      hx1 ?_
    intro y hy
    have hfym : FUNCT_1.apply f y ∈ X := FUNCT_2.th5 hf hX hy
    have hx3 : SUBSET_1.isElement (FUNCT_1.apply f y) X :=
      SUBSET_1.isElement_of hfym
    have h1 := th48 hX hY hF (appliedLeft_isFunctionOf hX hF hf hx1) hx2 hy
    have h2 := th53 hX hY hF hf hx1 hy
    have h3 := hassoc x1 (FUNCT_1.apply f y) x2 hx1 hx3 hx2
    have h4 := th48 hX hY hF hf hx2 hy
    exact h1.trans (Eq.subst (motive := fun s =>
        BINOP_1.apply2 F s x2 =
          BINOP_1.apply2 F x1 (FUNCT_1.apply (appliedRight F f x2) y)) h2.symm
      (h3.symm.trans (congrArg (BINOP_1.apply2 F x1) h4.symm)))


/-- Unlabeled `FUNCOP_1` (`Th60`) -/
theorem th60 {X Y F f g x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hassoc : BINOP_1.isAssociative F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hg : FUNCT_2.isFunctionOf g Y X)
    (hx : SUBSET_1.isElement x X) :
    applied F (appliedRight F f x) g = applied F f (appliedLeft F x g) := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact functionOf_of_empty_dom hY
      (applied_isFunctionOf hX hF (appliedRight_isFunctionOf hX hF hf hx) hg)
      (applied_isFunctionOf hX hF hf (appliedLeft_isFunctionOf hX hF hg hx))
  · refine th38 hX hY hF hf (appliedLeft_isFunctionOf hX hF hg hx)
      (applied_isFunctionOf hX hF (appliedRight_isFunctionOf hX hF hf hx) hg) ?_
    intro y hy
    have hfym := FUNCT_2.th5 hf hX hy
    have hgym := FUNCT_2.th5 hg hX hy
    have hx1 : SUBSET_1.isElement (FUNCT_1.apply f y) X := SUBSET_1.isElement_of hfym
    have hx2 : SUBSET_1.isElement (FUNCT_1.apply g y) X := SUBSET_1.isElement_of hgym
    have h1 := th37 hX hY hF (appliedRight_isFunctionOf hX hF hf hx) hg hy
    have h2 := th48 hX hY hF hf hx hy
    have h3 := hassoc (FUNCT_1.apply f y) x (FUNCT_1.apply g y) hx1 hx hx2
    have h4 := th53 hX hY hF hg hx hy
    exact h1.trans (Eq.subst (motive := fun s =>
        BINOP_1.apply2 F s (FUNCT_1.apply g y) =
          BINOP_1.apply2 F (FUNCT_1.apply f y)
            (FUNCT_1.apply (appliedLeft F x g) y)) h2.symm
      (h3.symm.trans (congrArg (BINOP_1.apply2 F (FUNCT_1.apply f y)) h4.symm)))

/-- Unlabeled `FUNCOP_1` (`Th61`) -/
theorem th61 {X Y F f g h : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hassoc : BINOP_1.isAssociative F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hg : FUNCT_2.isFunctionOf g Y X)
    (hh : FUNCT_2.isFunctionOf h Y X) :
    applied F (applied F f g) h = applied F f (applied F g h) := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact functionOf_of_empty_dom hY
      (applied_isFunctionOf hX hF (applied_isFunctionOf hX hF hf hg) hh)
      (applied_isFunctionOf hX hF hf (applied_isFunctionOf hX hF hg hh))
  · refine th38 hX hY hF hf (applied_isFunctionOf hX hF hg hh)
      (applied_isFunctionOf hX hF (applied_isFunctionOf hX hF hf hg) hh) ?_
    intro y hy
    have hx1 : SUBSET_1.isElement (FUNCT_1.apply f y) X :=
      SUBSET_1.isElement_of (FUNCT_2.th5 hf hX hy)
    have hx2 : SUBSET_1.isElement (FUNCT_1.apply g y) X :=
      SUBSET_1.isElement_of (FUNCT_2.th5 hg hX hy)
    have hx3 : SUBSET_1.isElement (FUNCT_1.apply h y) X :=
      SUBSET_1.isElement_of (FUNCT_2.th5 hh hX hy)
    have h1 := th37 hX hY hF (applied_isFunctionOf hX hF hf hg) hh hy
    have h2 := th37 hX hY hF hf hg hy
    have h3 := hassoc (FUNCT_1.apply f y) (FUNCT_1.apply g y)
      (FUNCT_1.apply h y) hx1 hx2 hx3
    have h4 := th37 hX hY hF hg hh hy
    exact h1.trans (Eq.subst (motive := fun s =>
        BINOP_1.apply2 F s (FUNCT_1.apply h y) =
          BINOP_1.apply2 F (FUNCT_1.apply f y)
            (FUNCT_1.apply (applied F g h) y)) h2.symm
      (h3.symm.trans (congrArg (BINOP_1.apply2 F (FUNCT_1.apply f y)) h4.symm)))

/-- Unlabeled `FUNCOP_1` (`Th62`) -/
theorem th62 {X Y F f x1 x2 : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hassoc : BINOP_1.isAssociative F X)
    (hf : FUNCT_2.isFunctionOf f Y X)
    (hx1 : SUBSET_1.isElement x1 X) (hx2 : SUBSET_1.isElement x2 X) :
    appliedLeft F (BINOP_1.apply2 F x1 x2) f =
      appliedLeft F x1 (appliedLeft F x2 f) := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact functionOf_of_empty_dom hY
      (appliedLeft_isFunctionOf hX hF hf
        (BINOP_1.apply2_binop_isElement hF hx1 hx2))
      (appliedLeft_isFunctionOf hX hF (appliedLeft_isFunctionOf hX hF hf hx2) hx1)
  · refine th54 hX hY hF (appliedLeft_isFunctionOf hX hF hf hx2)
      (appliedLeft_isFunctionOf hX hF hf
        (BINOP_1.apply2_binop_isElement hF hx1 hx2)) hx1 ?_
    intro y hy
    have hx3 : SUBSET_1.isElement (FUNCT_1.apply f y) X :=
      SUBSET_1.isElement_of (FUNCT_2.th5 hf hX hy)
    have h1 := th53 hX hY hF hf (BINOP_1.apply2_binop_isElement hF hx1 hx2) hy
    have h3 := hassoc x1 x2 (FUNCT_1.apply f y) hx1 hx2 hx3
    have h4 := th53 hX hY hF hf hx2 hy
    exact h1.trans (h3.symm.trans (congrArg (BINOP_1.apply2 F x1) h4.symm))

/-- Unlabeled `FUNCOP_1` (`Th63`) -/
theorem th63 {X Y F f x1 x2 : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hassoc : BINOP_1.isAssociative F X)
    (hf : FUNCT_2.isFunctionOf f Y X)
    (hx1 : SUBSET_1.isElement x1 X) (hx2 : SUBSET_1.isElement x2 X) :
    appliedRight F f (BINOP_1.apply2 F x1 x2) =
      appliedRight F (appliedRight F f x1) x2 := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact functionOf_of_empty_dom hY
      (appliedRight_isFunctionOf hX hF hf
        (BINOP_1.apply2_binop_isElement hF hx1 hx2))
      (appliedRight_isFunctionOf hX hF (appliedRight_isFunctionOf hX hF hf hx1) hx2)
  · refine th49 hX hY hF (appliedRight_isFunctionOf hX hF hf hx1)
      (appliedRight_isFunctionOf hX hF hf
        (BINOP_1.apply2_binop_isElement hF hx1 hx2)) hx2 ?_
    intro y hy
    have hx3 : SUBSET_1.isElement (FUNCT_1.apply f y) X :=
      SUBSET_1.isElement_of (FUNCT_2.th5 hf hX hy)
    have h1 := th48 hX hY hF hf (BINOP_1.apply2_binop_isElement hF hx1 hx2) hy
    have h3 := hassoc (FUNCT_1.apply f y) x1 x2 hx3 hx1 hx2
    have h4 := th48 hX hY hF hf hx1 hy
    exact h1.trans (h3.trans (congrArg (fun s => BINOP_1.apply2 F s x2)
      h4.symm))

/-- Unlabeled `FUNCOP_1` (`Th64`) -/
theorem th64 {X Y F f x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hcomm : BINOP_1.isCommutative F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hx : SUBSET_1.isElement x X) :
    appliedLeft F x f = appliedRight F f x := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact functionOf_of_empty_dom hY
      (appliedLeft_isFunctionOf hX hF hf hx)
      (appliedRight_isFunctionOf hX hF hf hx)
  · refine th49 hX hY hF hf (appliedLeft_isFunctionOf hX hF hf hx) hx ?_
    intro y hy
    have hx1 : SUBSET_1.isElement (FUNCT_1.apply f y) X :=
      SUBSET_1.isElement_of (FUNCT_2.th5 hf hX hy)
    have h1 := th53 hX hY hF hf hx hy
    exact h1.trans (hcomm x (FUNCT_1.apply f y) hx hx1)

/-- Unlabeled `FUNCOP_1` (`Th65`) -/
theorem th65 {X Y F f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hcomm : BINOP_1.isCommutative F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hg : FUNCT_2.isFunctionOf g Y X) :
    applied F f g = applied F g f := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact functionOf_of_empty_dom hY
      (applied_isFunctionOf hX hF hf hg) (applied_isFunctionOf hX hF hg hf)
  · refine th38 hX hY hF hg hf (applied_isFunctionOf hX hF hf hg) ?_
    intro y hy
    have hx1 : SUBSET_1.isElement (FUNCT_1.apply f y) X :=
      SUBSET_1.isElement_of (FUNCT_2.th5 hf hX hy)
    have hx2 : SUBSET_1.isElement (FUNCT_1.apply g y) X :=
      SUBSET_1.isElement_of (FUNCT_2.th5 hg hX hy)
    have h1 := th37 hX hY hF hf hg hy
    exact h1.trans (hcomm (FUNCT_1.apply f y) (FUNCT_1.apply g y) hx1 hx2)


/-- Unlabeled `FUNCOP_1` (`Th66`) -/
theorem th66 {X Y F f : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hidem : BINOP_1.isIdempotent F X)
    (hf : FUNCT_2.isFunctionOf f Y X) :
    applied F f f = f := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact functionOf_of_empty_dom hY (applied_isFunctionOf hX hF hf hf) hf
  · refine (th38 hX hY hF hf hf hf ?_).symm
    intro y hy
    have hx : SUBSET_1.isElement (FUNCT_1.apply f y) X :=
      SUBSET_1.isElement_of (FUNCT_2.th5 hf hX hy)
    exact (hidem (FUNCT_1.apply f y) hx).symm

/-- Unlabeled `FUNCOP_1` (`Th67`) -/
theorem th67 {X Y F f y : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F X) (hidem : BINOP_1.isIdempotent F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hy : y ∈ Y) :
    FUNCT_1.apply (appliedLeft F (FUNCT_1.apply f y) f) y =
      FUNCT_1.apply f y := by
  have hx : SUBSET_1.isElement (FUNCT_1.apply f y) X :=
    SUBSET_1.isElement_of (FUNCT_2.th5 hf hX hy)
  have h1 := th53 hX hY hF hf hx hy
  exact h1.trans (hidem (FUNCT_1.apply f y) hx)

/-- Unlabeled `FUNCOP_1` (`Th68`) -/
theorem th68 {X Y F f y : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (hF : BINOP_1.isBinOp F X) (hidem : BINOP_1.isIdempotent F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hy : y ∈ Y) :
    FUNCT_1.apply (appliedRight F f (FUNCT_1.apply f y)) y =
      FUNCT_1.apply f y := by
  have hx : SUBSET_1.isElement (FUNCT_1.apply f y) X :=
    SUBSET_1.isElement_of (FUNCT_2.th5 hf hX hy)
  have h1 := th48 hX hY hF hf hx hy
  exact h1.trans (hidem (FUNCT_1.apply f y) hx)

/-- Unlabeled `FUNCOP_1` (`Th69`) -/
theorem th69 {F f g : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hf : FUNCT_1.isFunction f) (hg : FUNCT_1.isFunction g)
    (hsub : ZFMISC_1.product (RELAT_1.rng f) (RELAT_1.rng g) ⊆ RELAT_1.dom F) :
    RELAT_1.dom (applied F f g) = RELAT_1.dom f ∩ RELAT_1.dom g := by
  have hrng : RELAT_1.rng (FUNCT_3.complex f g) ⊆
      ZFMISC_1.product (RELAT_1.rng f) (RELAT_1.rng g) :=
    FUNCT_3.th51 hf hg
  have hsub' : RELAT_1.rng (FUNCT_3.complex f g) ⊆ RELAT_1.dom F :=
    XBOOLE_1.th1 hrng hsub
  have hdom : RELAT_1.dom (RELAT_1.comp (FUNCT_3.complex f g) F) =
      RELAT_1.dom (FUNCT_3.complex f g) := RELAT_1.th27 hsub'
  exact hdom.trans (FUNCT_3.complex_dom f g)


/-! ## Function-yielding (`FUNCOP_1:def 6`) -/

/-- `FUNCOP_1:def 6` -/
def isFunctionYielding (F : TarskiSet.{u}) : Prop :=
  ∀ x, x ∈ RELAT_1.dom F → FUNCT_1.isFunction (FUNCT_1.apply F x)

theorem def6 (F : TarskiSet.{u}) :
    isFunctionYielding F ↔
      ∀ x, x ∈ RELAT_1.dom F → FUNCT_1.isFunction (FUNCT_1.apply F x) :=
  Iff.rfl

/-- Existence cluster: Function-yielding Function. -/
theorem exists_FunctionYielding :
    ∃ F : TarskiSet.{u}, FUNCT_1.isFunction F ∧ isFunctionYielding F :=
  ⟨mapsTo (TARSKI.singleton (∅ : TarskiSet.{u})) (RELAT_1.id (∅ : TarskiSet.{u})),
    mapsTo_isFunction _ _,
    fun x hx => by
      have hxD : x ∈ TARSKI.singleton (∅ : TarskiSet.{u}) :=
        Eq.subst (motive := fun s => x ∈ s)
          (mapsTo_dom (TARSKI.singleton (∅ : TarskiSet.{u}))
            (RELAT_1.id (∅ : TarskiSet.{u}))) hx
      have happ := th7 (A := TARSKI.singleton (∅ : TarskiSet.{u}))
        (z := RELAT_1.id (∅ : TarskiSet.{u})) (x := x) hxD
      exact Eq.subst (motive := FUNCT_1.isFunction) happ.symm
        (FUNCT_1.id_isFunction (∅ : TarskiSet.{u}))⟩

/-- Registration: `B.j` is a Function when `B` is Function-yielding. -/
theorem apply_FunctionYielding_isFunction {B j : TarskiSet.{u}}
    (hB : FUNCT_1.isFunction B) (hY : isFunctionYielding B) :
    FUNCT_1.isFunction (FUNCT_1.apply B j) := by
  have := Classical.propDecidable (j ∈ RELAT_1.dom B)
  by_cases hj : j ∈ RELAT_1.dom B
  · exact hY j hj
  · exact Eq.subst (motive := FUNCT_1.isFunction)
      (FUNCT_1.apply_of_not_mem hj).symm FUNCT_1.empty_isFunction

/-- Registration: composition preserves Function-yielding. -/
theorem comp_FunctionYielding {F f : TarskiSet.{u}}
    (hF : FUNCT_1.isFunction F) (hf : FUNCT_1.isFunction f)
    (hY : isFunctionYielding F) :
    isFunctionYielding (RELAT_1.comp f F) := by
  intro x hx
  have happ : FUNCT_1.apply (RELAT_1.comp f F) x =
      FUNCT_1.apply F (FUNCT_1.apply f x) :=
    FUNCT_1.th12 hf.2 hF.2 hx
  have ⟨_, hfx⟩ := (FUNCT_1.th11 hf.2).mp hx
  exact Eq.subst (motive := FUNCT_1.isFunction) happ.symm (hY _ hfx)

/-- Registration: `B --> c` is non-empty-yielding when `c` nonempty.
Mizar `non-empty` = `∅ ∉ rng`. -/
theorem mapsTo_isEmptyYielding {B c : TarskiSet.{u}}
    (hc : c ≠ (∅ : TarskiSet.{u})) :
    RELAT_1.isEmptyYielding (mapsTo B c) := by
  intro h
  have hsub : RELAT_1.rng (mapsTo B c) ⊆ TARSKI.singleton c := (th13 B c).2
  have : (∅ : TarskiSet.{u}) ∈ TARSKI.singleton c := hsub _ h
  exact hc ((TARSKI.singleton_iff c (∅ : TarskiSet.{u})).mp this).symm

/-- Unlabeled `FUNCOP_1` (`Th70`) -/
theorem th70 {X Y z x y : TarskiSet.{u}}
    (hx : x ∈ X) (hy : y ∈ Y) :
    BINOP_1.apply2 (mapsTo (ZFMISC_1.product X Y) z) x y = z := by
  have hp : TARSKI.pair x y ∈ ZFMISC_1.product X Y :=
    (ZFMISC_1.th87).mpr ⟨hx, hy⟩
  exact th7 hp

/-! ## `(a,b).-->c` (`FUNCOP_1:def 7`) -/

/-- `FUNCOP_1:def 7` — `(a,b).-->c`. -/
noncomputable def mapsTo2 (a b c : TarskiSet.{u}) : TarskiSet.{u} :=
  mapsTo (TARSKI.singleton (TARSKI.pair a b)) c

theorem def7 (a b c : TarskiSet.{u}) :
    mapsTo2 a b c = mapsTo (TARSKI.singleton (TARSKI.pair a b)) c :=
  rfl

theorem mapsTo2_isFunction (a b c : TarskiSet.{u}) :
    FUNCT_1.isFunction (mapsTo2 a b c) :=
  mapsTo_isFunction _ _

/-- Unlabeled `FUNCOP_1` (`Th71`) -/
theorem th71 (a b c : TarskiSet.{u}) :
    BINOP_1.apply2 (mapsTo2 a b c) a b = c := by
  have hp : TARSKI.pair a b ∈ TARSKI.singleton (TARSKI.pair a b) :=
    (TARSKI.singleton_iff _ _).mpr rfl
  exact th7 hp

/-! ## `IFEQ` (`FUNCOP_1:def 8`) -/

/-- `FUNCOP_1:def 8` -/
noncomputable def IFEQ (x y a b : TarskiSet.{u}) : TarskiSet.{u} := by
  classical
  exact if x = y then a else b

theorem def8 (x y a b : TarskiSet.{u}) :
    (x = y → IFEQ x y a b = a) ∧ (x ≠ y → IFEQ x y a b = b) := by
  classical
  constructor
  · intro h
    unfold IFEQ
    exact if_pos h
  · intro h
    unfold IFEQ
    exact if_neg h

theorem IFEQ_isElement {D x y a b : TarskiSet.{u}}
    (ha : SUBSET_1.isElement a D) (hb : SUBSET_1.isElement b D) :
    SUBSET_1.isElement (IFEQ x y a b) D := by
  classical
  by_cases h : x = y
  · have heq : IFEQ x y a b = a := by
      unfold IFEQ; exact if_pos h
    exact Eq.subst (motive := fun s => SUBSET_1.isElement s D) heq.symm ha
  · have heq : IFEQ x y a b = b := by
      unfold IFEQ; exact if_neg h
    exact Eq.subst (motive := fun s => SUBSET_1.isElement s D) heq.symm hb

/-! ## `x .--> y` -/

/-- `x .--> y` = `{x} --> y`. -/
noncomputable def dotArrow (x y : TarskiSet.{u}) : TarskiSet.{u} :=
  mapsTo (TARSKI.singleton x) y

theorem dotArrow_eq (x y : TarskiSet.{u}) :
    dotArrow x y = mapsTo (TARSKI.singleton x) y :=
  rfl

theorem dotArrow_isFunction (x y : TarskiSet.{u}) :
    FUNCT_1.isFunction (dotArrow x y) :=
  mapsTo_isFunction _ _

/-- Registration: `x .--> y` is one-to-one. -/
theorem dotArrow_oneToOne (x y : TarskiSet.{u}) :
    FUNCT_1.isOneToOne (dotArrow x y) := by
  intro x1 x2 hx1 hx2 heq
  have hdom : RELAT_1.dom (dotArrow x y) = TARSKI.singleton x :=
    mapsTo_dom _ _
  have hx1' : x1 = x :=
    (TARSKI.singleton_iff x x1).mp
      (Eq.subst (motive := fun s => x1 ∈ s) hdom hx1)
  have hx2' : x2 = x :=
    (TARSKI.singleton_iff x x2).mp
      (Eq.subst (motive := fun s => x2 ∈ s) hdom hx2)
  exact hx1'.trans hx2'.symm

/-- `FUNCOP_1:72` (`Th72`) -/
theorem th72 (x y : TarskiSet.{u}) :
    FUNCT_1.apply (dotArrow x y) x = y :=
  th7 ((TARSKI.singleton_iff x x).mpr rfl)

/-- Unlabeled `FUNCOP_1` (`Th73`) -/
theorem th73 {a b f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f) :
    dotArrow a b ⊆ f ↔
      a ∈ RELAT_1.dom f ∧ FUNCT_1.apply f a = b := by
  have hdom : RELAT_1.dom (dotArrow a b) = TARSKI.singleton a :=
    mapsTo_dom _ _
  constructor
  · intro hsub
    have hd := (GRFUNC_1.th2 (dotArrow_isFunction a b) hf).mp hsub
    have ha : a ∈ RELAT_1.dom (dotArrow a b) :=
      Eq.subst (motive := fun s => a ∈ s) hdom.symm
        ((TARSKI.singleton_iff a a).mpr rfl)
    exact ⟨hd.1 _ ha, (hd.2 a ha).symm.trans (th72 a b)⟩
  · intro ⟨ha, happ⟩
    refine (GRFUNC_1.th2 (dotArrow_isFunction a b) hf).mpr ⟨?_, ?_⟩
    · intro z hz
      have hz' : z = a :=
        (TARSKI.singleton_iff a z).mp
          (Eq.subst (motive := fun s => z ∈ s) hdom hz)
      exact Eq.subst (motive := fun s => s ∈ RELAT_1.dom f) hz'.symm ha
    · intro z hz
      have hz' : z = a :=
        (TARSKI.singleton_iff a z).mp
          (Eq.subst (motive := fun s => z ∈ s) hdom hz)
      exact Eq.subst (motive := fun s =>
          FUNCT_1.apply (dotArrow a b) s = FUNCT_1.apply f s) hz'.symm
        ((th72 a b).trans happ.symm)


/-- Lm2: `(o,m):->r` is Function of `[:{o},{m}:],{r}`. -/
theorem lm2 (o m r : TarskiSet.{u}) :
    FUNCT_2.isFunctionOf (mapsTo2 o m r)
      (ZFMISC_1.product (TARSKI.singleton o) (TARSKI.singleton m))
      (TARSKI.singleton r) := by
  have hdom : RELAT_1.dom (mapsTo2 o m r) =
      TARSKI.singleton (TARSKI.pair o m) := mapsTo_dom _ _
  have hprod : ZFMISC_1.product (TARSKI.singleton o) (TARSKI.singleton m) =
      TARSKI.singleton (TARSKI.pair o m) := ZFMISC_1.th29
  exact FUNCT_2.functionOf_of (mapsTo2_isFunction o m r)
    (hdom.trans hprod.symm) (th13 _ _).2

/-- Unlabeled `FUNCOP_1` (`Th74`) -/
theorem th74 (x y : TarskiSet.{u}) :
    x ∈ RELAT_1.dom (dotArrow x y) :=
  Eq.subst (motive := fun s => x ∈ s) (mapsTo_dom _ _).symm
    ((TARSKI.singleton_iff x x).mpr rfl)

/-- Unlabeled `FUNCOP_1` (`Th75`) -/
theorem th75 {x y z : TarskiSet.{u}} (hz : z ∈ RELAT_1.dom (dotArrow x y)) :
    z = x :=
  (TARSKI.singleton_iff x z).mp
    (Eq.subst (motive := fun s => z ∈ s) (mapsTo_dom _ _) hz)

/-- Unlabeled `FUNCOP_1` (`Th76`) -/
theorem th76 {x y A : TarskiSet.{u}} (hx : x ∉ A) :
    RELAT_1.restrict (dotArrow x y) A = (∅ : TarskiSet.{u}) := by
  have hmiss : XBOOLE_0.misses (TARSKI.singleton x) A := ZFMISC_1.th50 hx
  have hdom : RELAT_1.dom (dotArrow x y) = TARSKI.singleton x := mapsTo_dom _ _
  have hmiss' : XBOOLE_0.misses (RELAT_1.dom (dotArrow x y)) A :=
    Eq.subst (motive := fun s => XBOOLE_0.misses s A) hdom.symm hmiss
  exact (RELAT_1.th66).mpr hmiss'

/-- Synonym `(o,m):->r` for mapsTo2; Function of form. -/
theorem mapsTo2_isFunctionOf_singletons (o m r : TarskiSet.{u}) :
    FUNCT_2.isFunctionOf (mapsTo2 o m r)
      (ZFMISC_1.product (TARSKI.singleton o) (TARSKI.singleton m))
      (TARSKI.singleton r) :=
  lm2 o m r

/-- Synonym `m:->o` for `dotArrow`; Function of `{m},{o}`. -/
theorem dotArrow_isFunctionOf_singletons (m o : TarskiSet.{u}) :
    FUNCT_2.isFunctionOf (dotArrow m o)
      (TARSKI.singleton m) (TARSKI.singleton o) := by
  change FUNCT_2.isFunctionOf (mapsTo (TARSKI.singleton m) o)
    (TARSKI.singleton m) (TARSKI.singleton o)
  exact mapsTo_isFunctionOf_singleton (TARSKI.singleton m) o

/-- Unlabeled `FUNCOP_1` (`Th77`) -/
theorem th77 {a b c x y : TarskiSet.{u}}
    (hx : x ∈ TARSKI.singleton a) (hy : y ∈ TARSKI.singleton b) :
    BINOP_1.apply2 (mapsTo2 a b c) x y = c := by
  have hx' : x = a := (TARSKI.singleton_iff a x).mp hx
  have hy' : y = b := (TARSKI.singleton_iff b y).mp hy
  exact Eq.subst (motive := fun s => BINOP_1.apply2 (mapsTo2 a b c) s y = c)
    hx'.symm (Eq.subst (motive := fun s =>
      BINOP_1.apply2 (mapsTo2 a b c) a s = c) hy'.symm (th71 a b c))

/-- Registration: restriction of Function-yielding is Function-yielding. -/
theorem restrict_FunctionYielding {f C : TarskiSet.{u}}
    (hf : FUNCT_1.isFunction f) (hY : isFunctionYielding f) :
    isFunctionYielding (RELAT_1.restrict f C) := by
  intro i hi
  have happ : FUNCT_1.apply (RELAT_1.restrict f C) i = FUNCT_1.apply f i :=
    FUNCT_1.th47 hf.2 hi
  have hiD : i ∈ RELAT_1.dom f :=
    ((XBOOLE_0.def4 _ _ _).mp
      (Eq.subst (motive := fun s => i ∈ s) (RELAT_1.th61 (R := f)) hi)).1
  exact Eq.subst (motive := FUNCT_1.isFunction) happ.symm (hY i hiD)

/-- Registration: `A --> f` is Function-yielding. -/
theorem mapsTo_FunctionYielding (A f : TarskiSet.{u})
    (_hf : FUNCT_1.isFunction f) :
    isFunctionYielding (mapsTo A f) := by
  intro a ha
  have haA : a ∈ A := Eq.subst (motive := fun s => a ∈ s) (mapsTo_dom A f) ha
  exact Eq.subst (motive := FUNCT_1.isFunction) (th7 haA).symm _hf

/-- Registration: `X --> a` is constant. -/
theorem mapsTo_isConstant (X a : TarskiSet.{u}) :
    FUNCT_1.isConstant (mapsTo X a) := by
  intro x y hx hy
  have hxA : x ∈ X := Eq.subst (motive := fun s => x ∈ s) (mapsTo_dom X a) hx
  have hyA : y ∈ X := Eq.subst (motive := fun s => y ∈ s) (mapsTo_dom X a) hy
  exact (th7 hxA).trans (th7 hyA).symm

/-- Existence: nonempty constant Function. -/
theorem exists_nonempty_constant :
    ∃ f : TarskiSet.{u}, FUNCT_1.isFunction f ∧ ¬ XBOOLE_0.isEmpty f ∧
      FUNCT_1.isConstant f :=
  ⟨mapsTo (TARSKI.singleton (∅ : TarskiSet.{u})) (TARSKI.singleton (∅ : TarskiSet.{u})),
    mapsTo_isFunction _ _,
    ne_imp_not_empty (mapsTo_nonempty (singleton_ne_empty _)),
    mapsTo_isConstant _ _⟩

/-- Registration: restriction of constant is constant. -/
theorem restrict_isConstant {f X : TarskiSet.{u}}
    (hf : FUNCT_1.isFunction f) (hc : FUNCT_1.isConstant f) :
    FUNCT_1.isConstant (RELAT_1.restrict f X) := by
  intro x y hx hy
  have hxD : x ∈ RELAT_1.dom f :=
    ((XBOOLE_0.def4 _ _ _).mp
      (Eq.subst (motive := fun s => x ∈ s) (RELAT_1.th61 (R := f)) hx)).1
  have hyD : y ∈ RELAT_1.dom f :=
    ((XBOOLE_0.def4 _ _ _).mp
      (Eq.subst (motive := fun s => y ∈ s) (RELAT_1.th61 (R := f)) hy)).1
  have h1 : FUNCT_1.apply (RELAT_1.restrict f X) x = FUNCT_1.apply f x :=
    FUNCT_1.th47 hf.2 hx
  have h2 : FUNCT_1.apply (RELAT_1.restrict f X) y = FUNCT_1.apply f y :=
    FUNCT_1.th47 hf.2 hy
  exact h1.trans ((hc x y hxD hyD).trans h2.symm)

/-- Unlabeled `FUNCOP_1` (`Th78`) -/
theorem th78 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hne : ¬ XBOOLE_0.isEmpty f) (hc : FUNCT_1.isConstant f) :
    ∃ y, ∀ x, x ∈ RELAT_1.dom f → FUNCT_1.apply f x = y := by
  have hfne : f ≠ (∅ : TarskiSet.{u}) := fun h =>
    hne (Eq.subst (motive := XBOOLE_0.isEmpty) h.symm XBOOLE_0.emptySet_isEmpty)
  have hdne : RELAT_1.dom f ≠ (∅ : TarskiSet.{u}) := by
    intro h
    exact hfne (RELAT_1.th41 hf.1 (Or.inl h))
  obtain ⟨x0, hx0⟩ := exists_mem_of_ne hdne
  refine ⟨FUNCT_1.apply f x0, fun x hx => hc x x0 hx hx0⟩

/-- Unlabeled `FUNCOP_1` (`Th79`) -/
theorem th79 {X x : TarskiSet.{u}} (hX : X ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.the_value_of (mapsTo X x) = x := by
  have hdomne : RELAT_1.dom (mapsTo X x) ≠ (∅ : TarskiSet.{u}) :=
    Eq.subst (motive := fun s => s ≠ (∅ : TarskiSet.{u}))
      (mapsTo_dom X x).symm hX
  obtain ⟨i, hi, heq⟩ := FUNCT_1.the_value_of_spec hdomne
  have hiX : i ∈ X := Eq.subst (motive := fun s => i ∈ s) (mapsTo_dom X x) hi
  exact heq.trans (th7 hiX)

/-- Unlabeled `FUNCOP_1` (`Th80`) -/
theorem th80 {f : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hc : FUNCT_1.isConstant f) :
    f = mapsTo (RELAT_1.dom f) (FUNCT_1.the_value_of f) := by
  have := Classical.propDecidable (f = (∅ : TarskiSet.{u}))
  by_cases hempty : f = (∅ : TarskiSet.{u})
  · have hdom : RELAT_1.dom f = (∅ : TarskiSet.{u}) :=
      Eq.subst (motive := fun s => RELAT_1.dom s = (∅ : TarskiSet.{u}))
        hempty.symm RELAT_1.th38.1
    exact hempty.trans (mapsTo_of_empty hdom).symm
  · have hdne : RELAT_1.dom f ≠ (∅ : TarskiSet.{u}) := by
      intro h
      exact hempty (RELAT_1.th41 hf.1 (Or.inl h))
    obtain ⟨i, hi, heq⟩ := FUNCT_1.the_value_of_spec hdne
    refine FUNCT_1.th2 hf (mapsTo_isFunction _ _) (mapsTo_dom _ _).symm ?_
    intro x hx
    have : FUNCT_1.apply (mapsTo (RELAT_1.dom f) (FUNCT_1.the_value_of f)) x =
        FUNCT_1.the_value_of f := th7 hx
    exact (hc x i hx hi).trans (heq.symm.trans this.symm)

/-- Unlabeled `FUNCOP_1` (`Th81`) -/
theorem th81 (A x B : TarskiSet.{u}) :
    RELAT_1.image (mapsTo A x) B ⊆ TARSKI.singleton x := by
  intro y hy
  obtain ⟨z, hzD, hzB, heq⟩ :=
    (FUNCT_1.def6 (mapsTo_isFunctionLike A x)).mp hy
  have hzA : z ∈ A := Eq.subst (motive := fun s => z ∈ s) (mapsTo_dom A x) hzD
  exact Eq.subst (motive := fun s => s ∈ TARSKI.singleton x) heq.symm
    ((TARSKI.singleton_iff x _).mpr (th7 hzA))




/-- `FUNCOP_1:82` (`Th82`) -/
theorem th82 (x y : TarskiSet.{u}) :
    WELLORD1.isIsomorphismOf (dotArrow x y)
      (TARSKI.singleton (TARSKI.pair x x))
      (TARSKI.singleton (TARSKI.pair y y)) := by
  have hdom : RELAT_1.dom (dotArrow x y) = TARSKI.singleton x :=
    mapsTo_dom _ _
  have hfieldR : RELAT_1.field (TARSKI.singleton (TARSKI.pair x x)) =
      TARSKI.singleton x := RELAT_1.th173
  have hfieldS : RELAT_1.field (TARSKI.singleton (TARSKI.pair y y)) =
      TARSKI.singleton y := RELAT_1.th173
  have hrng : RELAT_1.rng (dotArrow x y) = TARSKI.singleton y :=
    (RELAT_1.th160 (singleton_ne_empty x) (singleton_ne_empty y)).2
  refine ⟨dotArrow_isFunction x y, hdom.trans hfieldR.symm,
    hrng.trans hfieldS.symm, dotArrow_oneToOne x y, ?_⟩
  intro a b
  constructor
  · intro hp
    have heq : TARSKI.pair a b = TARSKI.pair x x :=
      (TARSKI.singleton_iff _ _).mp hp
    have ⟨ha, hb⟩ := XTUPLE_0.th1 heq
    have haF : a ∈ RELAT_1.field (TARSKI.singleton (TARSKI.pair x x)) :=
      Eq.subst (motive := fun s => a ∈ s) hfieldR.symm
        ((TARSKI.singleton_iff x a).mpr ha)
    have hbF : b ∈ RELAT_1.field (TARSKI.singleton (TARSKI.pair x x)) :=
      Eq.subst (motive := fun s => b ∈ s) hfieldR.symm
        ((TARSKI.singleton_iff x b).mpr hb)
    have happ : FUNCT_1.apply (dotArrow x y) x = y := th72 x y
    have haapp : FUNCT_1.apply (dotArrow x y) a = y :=
      Eq.subst (motive := fun s => FUNCT_1.apply (dotArrow x y) s = y) ha.symm happ
    have hbapp : FUNCT_1.apply (dotArrow x y) b = y :=
      Eq.subst (motive := fun s => FUNCT_1.apply (dotArrow x y) s = y) hb.symm happ
    have hpair : TARSKI.pair (FUNCT_1.apply (dotArrow x y) a)
        (FUNCT_1.apply (dotArrow x y) b) = TARSKI.pair y y :=
      (congrArg (fun s => TARSKI.pair s
          (FUNCT_1.apply (dotArrow x y) b)) haapp).trans
        (congrArg (TARSKI.pair y) hbapp)
    exact ⟨haF, hbF, (TARSKI.singleton_iff _ _).mpr hpair⟩
  · intro ⟨haF, hbF, _⟩
    have ha : a = x :=
      (TARSKI.singleton_iff x a).mp
        (Eq.subst (motive := fun s => a ∈ s) hfieldR haF)
    have hb : b = x :=
      (TARSKI.singleton_iff x b).mp
        (Eq.subst (motive := fun s => b ∈ s) hfieldR hbF)
    have hpair : TARSKI.pair a b = TARSKI.pair x x :=
      (congrArg (fun s => TARSKI.pair s b) ha).trans (congrArg (TARSKI.pair x) hb)
    exact (TARSKI.singleton_iff _ _).mpr hpair

/-- Unlabeled `FUNCOP_1` (`Th83`) -/
theorem th83 (x y : TarskiSet.{u}) :
    WELLORD1.areIsomorphic
      (TARSKI.singleton (TARSKI.pair x x))
      (TARSKI.singleton (TARSKI.pair y y)) :=
  ⟨dotArrow x y, th82 x y⟩

theorem mapsTo_isTotal (I A : TarskiSet.{u}) :
    PARTFUN1.isTotal (mapsTo I A) I :=
  mapsTo_dom I A

/-- Unlabeled `FUNCOP_1` (`Th84`) -/
theorem th84 {f x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hx : x ∈ RELAT_1.dom f) :
    dotArrow x (FUNCT_1.apply f x) ⊆ f := by
  have hp : TARSKI.pair x (FUNCT_1.apply f x) ∈ f :=
    (FUNCT_1.th1 hf.2).mpr ⟨hx, rfl⟩
  have hsing : TARSKI.singleton (TARSKI.pair x (FUNCT_1.apply f x)) ⊆ f :=
    (ZFMISC_1.th31).mpr hp
  have heq : ZFMISC_1.product (TARSKI.singleton x)
      (TARSKI.singleton (FUNCT_1.apply f x)) =
      TARSKI.singleton (TARSKI.pair x (FUNCT_1.apply f x)) :=
    ZFMISC_1.th29
  exact Eq.subst (motive := fun s => s ⊆ f) heq.symm hsing

/-- Unlabeled `FUNCOP_1` (`Th85`) -/
theorem th85 {X Y F f g x : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u})) (hF : BINOP_1.isBinOp F X)
    (hassoc : BINOP_1.isAssociative F X)
    (hf : FUNCT_2.isFunctionOf f Y X) (hg : FUNCT_2.isFunctionOf g Y X)
    (hx : SUBSET_1.isElement x X) :
    applied F (appliedLeft F x f) g = appliedLeft F x (applied F f g) := by
  have := Classical.propDecidable (Y = (∅ : TarskiSet.{u}))
  by_cases hY : Y = (∅ : TarskiSet.{u})
  · exact functionOf_of_empty_dom hY
      (applied_isFunctionOf hX hF (appliedLeft_isFunctionOf hX hF hf hx) hg)
      (appliedLeft_isFunctionOf hX hF (applied_isFunctionOf hX hF hf hg) hx)
  · refine th54 hX hY hF (applied_isFunctionOf hX hF hf hg)
      (applied_isFunctionOf hX hF (appliedLeft_isFunctionOf hX hF hf hx) hg) hx ?_
    intro y hy
    have hx1 : SUBSET_1.isElement (FUNCT_1.apply f y) X :=
      SUBSET_1.isElement_of (FUNCT_2.th5 hf hX hy)
    have hx2 : SUBSET_1.isElement (FUNCT_1.apply g y) X :=
      SUBSET_1.isElement_of (FUNCT_2.th5 hg hX hy)
    have hL := th37 hX hY hF (appliedLeft_isFunctionOf hX hF hf hx) hg hy
    have hAL := th53 hX hY hF hf hx hy
    have hAs := hassoc x (FUNCT_1.apply f y) (FUNCT_1.apply g y) hx hx1 hx2
    have hR := th37 hX hY hF hf hg hy
    exact hL.trans (Eq.subst (motive := fun s =>
        BINOP_1.apply2 F s (FUNCT_1.apply g y) =
          BINOP_1.apply2 F x (FUNCT_1.apply (applied F f g) y)) hAL.symm
      (hAs.symm.trans (congrArg (BINOP_1.apply2 F x) hR.symm)))

/-- Unlabeled `FUNCOP_1` (`Th86`) -/
theorem th86 {x y A : TarskiSet.{u}} (hx : x ∈ A) :
    RELAT_1.restrict (dotArrow x y) A = dotArrow x y := by
  have hsub : TARSKI.singleton x ⊆ A := (ZFMISC_1.th31).mpr hx
  have hdom : RELAT_1.dom (dotArrow x y) ⊆ A :=
    Eq.subst (motive := fun s => s ⊆ A) (mapsTo_dom _ _).symm hsub
  exact RELAT_1.th68 (dotArrow_isFunction x y).1 hdom

/-! ## Relation-yielding -/

/-- Unlabeled attr: Relation-yielding. -/
def isRelationYielding (F : TarskiSet.{u}) : Prop :=
  ∀ x, x ∈ RELAT_1.dom F → RELAT_1.isRelation (FUNCT_1.apply F x)

theorem FunctionYielding_imp_RelationYielding {F : TarskiSet.{u}}
    (h : isFunctionYielding F) : isRelationYielding F :=
  fun x hx => (h x hx).1

theorem empty_isFunctionYielding {f : TarskiSet.{u}}
    (hf : f = (∅ : TarskiSet.{u})) : isFunctionYielding f := by
  intro x hx
  have hx' : x ∈ RELAT_1.dom (∅ : TarskiSet.{u}) :=
    Eq.subst (motive := fun s => x ∈ RELAT_1.dom s) hf hx
  have : x ∈ (∅ : TarskiSet.{u}) :=
    Eq.subst (motive := fun s => x ∈ s) RELAT_1.th38.1 hx'
  exact ((XBOOLE_0.empty_iff x).mp this).elim

/-- Unlabeled `FUNCOP_1` (`Th87`) -/
theorem th87 (X Y x y : TarskiSet.{u}) :
    PARTFUN1.tolerates (mapsTo X x) (mapsTo Y y) ↔
      x = y ∨ XBOOLE_0.misses X Y := by
  have hdX : RELAT_1.dom (mapsTo X x) = X := mapsTo_dom X x
  have hdY : RELAT_1.dom (mapsTo Y y) = Y := mapsTo_dom Y y
  constructor
  · intro ht
    have := Classical.propDecidable (x = y)
    by_cases heq : x = y
    · exact Or.inl heq
    · refine Or.inr ?_
      apply eq_of_mem; intro z; constructor
      · intro hz
        have ⟨hzX, hzY⟩ := (XBOOLE_0.def4 X Y z).mp hz
        have hzD : z ∈ RELAT_1.dom (mapsTo X x) ∩ RELAT_1.dom (mapsTo Y y) :=
          (XBOOLE_0.def4 _ _ _).mpr
            ⟨Eq.subst (motive := fun s => z ∈ s) hdX.symm hzX,
              Eq.subst (motive := fun s => z ∈ s) hdY.symm hzY⟩
        have happ : FUNCT_1.apply (mapsTo X x) z =
            FUNCT_1.apply (mapsTo Y y) z := ht z hzD
        exact (heq ((th7 hzX).symm.trans (happ.trans (th7 hzY)))).elim
      · intro hz
        exact ((XBOOLE_0.empty_iff z).mp hz).elim
  · intro h
    intro z hz
    have ⟨hzX', hzY'⟩ := (XBOOLE_0.def4 _ _ _).mp hz
    have hzX : z ∈ X := Eq.subst (motive := fun s => z ∈ s) hdX hzX'
    have hzY : z ∈ Y := Eq.subst (motive := fun s => z ∈ s) hdY hzY'
    cases h with
    | inl heq =>
      exact (th7 hzX).trans (heq.trans (th7 hzY).symm)
    | inr hmiss =>
      have hzI : z ∈ X ∩ Y := (XBOOLE_0.def4 X Y z).mpr ⟨hzX, hzY⟩
      exact ((XBOOLE_0.empty_iff z).mp
        (Eq.subst (motive := fun s => z ∈ s) hmiss hzI)).elim

/-- `FUNCOP_1:88` (`Th88`) -/
theorem th88 (x y : TarskiSet.{u}) :
    RELAT_1.rng (dotArrow x y) = TARSKI.singleton y :=
  th8 (singleton_ne_empty x)

/-- Unlabeled `FUNCOP_1` (`Th89`) -/
theorem th89 {A x y z : TarskiSet.{u}} (hz : z ∈ A) :
    RELAT_1.comp (dotArrow y z) (mapsTo A x) = dotArrow y x := by
  have hdomL : RELAT_1.dom (dotArrow y z) = TARSKI.singleton y :=
    mapsTo_dom _ _
  have hdomR : RELAT_1.dom (dotArrow y x) = TARSKI.singleton y :=
    mapsTo_dom _ _
  have hrng : RELAT_1.rng (dotArrow y z) = TARSKI.singleton z := th88 y z
  have hsub : RELAT_1.rng (dotArrow y z) ⊆ RELAT_1.dom (mapsTo A x) :=
    Eq.subst (motive := fun s => s ⊆ RELAT_1.dom (mapsTo A x)) hrng.symm
      (Eq.subst (motive := fun s => TARSKI.singleton z ⊆ s)
        (mapsTo_dom A x).symm ((ZFMISC_1.th31).mpr hz))
  have hdom : RELAT_1.dom (RELAT_1.comp (dotArrow y z) (mapsTo A x)) =
      RELAT_1.dom (dotArrow y x) :=
    (RELAT_1.th27 hsub).trans (hdomL.trans hdomR.symm)
  refine FUNCT_1.th2
    (FUNCT_1.comp_isFunction (dotArrow_isFunction y z) (mapsTo_isFunction A x))
    (dotArrow_isFunction y x) hdom ?_
  intro e he
  have heY : e ∈ TARSKI.singleton y :=
    Eq.subst (motive := fun s => e ∈ s)
      ((RELAT_1.th27 hsub).trans hdomL) he
  have happ : FUNCT_1.apply (RELAT_1.comp (dotArrow y z) (mapsTo A x)) e =
      FUNCT_1.apply (mapsTo A x) (FUNCT_1.apply (dotArrow y z) e) :=
    FUNCT_1.th12 (dotArrow_isFunction y z).2 (mapsTo_isFunctionLike A x) he
  have heeq : e = y := (TARSKI.singleton_iff y e).mp heY
  have h1 : FUNCT_1.apply (dotArrow y z) e = z :=
    Eq.subst (motive := fun s => FUNCT_1.apply (dotArrow y z) s = z) heeq.symm
      (th72 y z)
  exact happ.trans ((congrArg (FUNCT_1.apply (mapsTo A x)) h1).trans
    ((th7 hz).trans (Eq.subst (motive := fun s =>
        x = FUNCT_1.apply (dotArrow y x) s) heeq.symm (th72 y x).symm)))

/-! ## Final registrations -/

theorem mapsTo_isXdefined (I A : TarskiSet.{u}) :
    RELAT_1.isXdefined (mapsTo I A) I :=
  fun _ hx => Eq.subst (motive := fun s => _ ∈ s) (mapsTo_dom I A) hx

theorem dotArrow_isXdefined (I A : TarskiSet.{u}) :
    RELAT_1.isXdefined (dotArrow I A) (TARSKI.singleton I) :=
  fun _ hx => Eq.subst (motive := fun s => _ ∈ s) (mapsTo_dom _ _) hx

theorem mapsTo_isXvalued {A B x : TarskiSet.{u}}
    (hB : B ≠ (∅ : TarskiSet.{u})) (hx : SUBSET_1.isElement x B) :
    RELAT_1.isXvalued (mapsTo A x) B :=
  FUNCT_2.functionOf_rng_sub (mapsTo_isFunctionOf_element hB hx)

theorem dotArrow_isXvalued {A x i : TarskiSet.{u}}
    (hA : A ≠ (∅ : TarskiSet.{u})) (hi : SUBSET_1.isElement i A) :
    RELAT_1.isXvalued (dotArrow x i) A := by
  have hrng : RELAT_1.rng (dotArrow x i) = TARSKI.singleton i := th88 x i
  exact Eq.subst (motive := fun s => s ⊆ A) hrng.symm
    ((ZFMISC_1.th31).mpr (SUBSET_1.isElement_mem (ne_imp_not_empty hA) hi))

theorem Y_valued_FunctionYielding {Y f : TarskiSet.{u}}
    (hY : FUNCT_1.isFunctional Y) (hf : FUNCT_1.isFunction f)
    (hv : RELAT_1.isXvalued f Y) : isFunctionYielding f := by
  intro x hx
  have happ : FUNCT_1.apply f x ∈ Y := hv _ (FUNCT_1.th3 hf.2 hx)
  exact hY _ happ

theorem exists_total_PartFunc {X Y : TarskiSet.{u}}
    (hY : Y ≠ (∅ : TarskiSet.{u})) :
    ∃ f, PARTFUN1.isPartFunc f X Y ∧ PARTFUN1.isTotal f X := by
  obtain ⟨y, hy⟩ := exists_mem_of_ne hY
  refine ⟨mapsTo X y, ?_, mapsTo_dom X y⟩
  exact ⟨mapsTo_isFunction X y,
    RELSET_1.th4 (mapsTo_isRelation X y)
      (fun z hz => Eq.subst (motive := fun s => z ∈ s) (mapsTo_dom X y) hz)
      (XBOOLE_1.th1 (th13 X y).2 ((ZFMISC_1.th31).mpr hy))⟩

end FUNCOP_1
