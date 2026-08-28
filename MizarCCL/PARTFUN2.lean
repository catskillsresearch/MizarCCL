import MizarCCL.FUNCOP_1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/partfun2.miz`.
Authors: Jarosław Kotowicz (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Partial Functions from a Domain to a Domain

1–1 Lean rendering of Mizar article `PARTFUN2`
(`vendor/mml/partfun2.miz`). Import is `FUNCOP_1` (pulls `FUNCT_2` /
`PARTFUN1` / `GRFUNC_1`). Mizar `s*f` is Lean `RELAT_1.comp f s`;
Mizar `f/.c` is `PARTFUN1.apply_at`; Mizar `A --> z` is
`FUNCOP_1.mapsTo`.
-/

universe u

open TarskiSet TARSKI

namespace PARTFUN2

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

private theorem mem_dom_of_part {f C D c : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f C D) (hc : c ∈ RELAT_1.dom f) : c ∈ C :=
  RELSET_1.relationOf_defined hf.2 c hc

private theorem mem_rng_of_part {f C D y : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f C D) (hy : y ∈ RELAT_1.rng f) : y ∈ D :=
  RELSET_1.relationOf_valued hf.2 y hy

private theorem apply_mem_cod {f C D c : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f C D) (hc : c ∈ RELAT_1.dom f) :
    FUNCT_1.apply f c ∈ D :=
  PARTFUN1.th4 hf.1 (RELSET_1.relationOf_valued hf.2) hc

private noncomputable def nonempty_choose {X : TarskiSet.{u}}
    (h : X ≠ (∅ : TarskiSet.{u})) : TarskiSet.{u} :=
  Classical.choose (XBOOLE_0.th7 h)

private theorem nonempty_choose_mem {X : TarskiSet.{u}}
    (h : X ≠ (∅ : TarskiSet.{u})) : nonempty_choose h ∈ X :=
  Classical.choose_spec (XBOOLE_0.th7 h)

private theorem comp_isPartFunc {C D E f s : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f C D) (hs : PARTFUN1.isPartFunc s D E) :
    PARTFUN1.isPartFunc (RELAT_1.comp f s) C E :=
  PARTFUN1.partFunc_of (FUNCT_1.comp_isFunction hf.1 hs.1)
    (fun x hx => mem_dom_of_part hf ((FUNCT_1.th11 hf.1.2).mp hx).1)
    (fun y hy =>
      let ⟨x, hx, heq⟩ :=
        (FUNCT_1.def3 (FUNCT_1.comp_isFunction hf.1 hs.1).2).mp hy
      let hv := FUNCT_1.th12 hf.1.2 hs.1.2 hx
      Eq.subst (motive := fun z => z ∈ E) (heq.trans hv).symm
        (apply_mem_cod hs ((FUNCT_1.th11 hf.1.2).mp hx).2))

/-- Redefine: `id SD` is a `PartFunc of D,D`. -/
theorem id_isPartFunc (D SD : TarskiSet.{u}) (hSD : SD ⊆ D) :
    PARTFUN1.isPartFunc (RELAT_1.id SD) D D :=
  PARTFUN1.partFunc_of (FUNCT_1.id_isFunction SD)
    (Eq.subst (motive := fun s => s ⊆ D) (RELAT_1.th45 (X := SD)).1.symm hSD)
    (Eq.subst (motive := fun s => s ⊆ D) (RELAT_1.th45 (X := SD)).2.symm hSD)

/-- Redefine: inverse of one-to-one `PartFunc` is a `PartFunc`. -/
theorem inv_isPartFunc {X Y f : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f X Y)
    (h1 : FUNCT_1.isOneToOne f) :
    PARTFUN1.isPartFunc (FUNCT_1.inv f) Y X :=
  PARTFUN1.th9 hf h1

/-- Redefine: `X|`f` is a `PartFunc of C,D`. -/
theorem restrictRng_isPartFunc {C D X f : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f C D) :
    PARTFUN1.isPartFunc (RELAT_1.restrictRng X f) C D :=
  PARTFUN1.th13 hf

/-- Redefine: `SC --> d` is a `PartFunc of C,D`. -/
theorem mapsTo_isPartFunc {C D SC d : TarskiSet.{u}}
    (hSC : SC ⊆ C) (hd : d ∈ D) :
    PARTFUN1.isPartFunc (FUNCOP_1.mapsTo SC d) C D :=
  PARTFUN1.partFunc_of (FUNCOP_1.mapsTo_isFunction SC d)
    (Eq.subst (motive := fun s => s ⊆ C) (FUNCOP_1.mapsTo_dom SC d).symm hSC)
    (fun y hy =>
      Eq.subst (motive := fun s => s ∈ D)
        ((TARSKI.singleton_iff d y).mp ((FUNCOP_1.th13 SC d).2 y hy)).symm hd)

/-- `PARTFUN2` redefine of `constant` for nonempty-codomain PartFuncs. -/
theorem def_constant {C D f : TarskiSet.{u}}
    (hf : PARTFUN1.isPartFunc f C D) (hD : D ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.isConstant f ↔
      ∃ d, d ∈ D ∧ ∀ c, c ∈ RELAT_1.dom f → FUNCT_1.apply f c = d := by
  constructor
  · intro hc
    refine Or.elim (Classical.em (RELAT_1.dom f = (∅ : TarskiSet.{u})))
      (fun hdom =>
        ⟨nonempty_choose hD, nonempty_choose_mem hD, fun c hcdom =>
          False.elim ((XBOOLE_0.empty_iff c).mp
            (Eq.subst (motive := fun s => c ∈ s) hdom hcdom))⟩)
      (fun hne =>
        let ⟨c0, hc0⟩ := XBOOLE_0.th7 hne
        ⟨FUNCT_1.apply f c0, apply_mem_cod hf hc0,
          fun c hcdom => (hc c0 c hc0 hcdom).symm⟩)
  · intro ⟨_, _, hv⟩ x y hx hy
    exact (hv x hx).trans (hv y hy).symm

/-- `PARTFUN2:1` (`Th1`) -/
theorem th1 {C D f g : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hg : PARTFUN1.isPartFunc g C D)
    (hd : RELAT_1.dom f = RELAT_1.dom g)
    (hv : ∀ c, c ∈ RELAT_1.dom f →
      PARTFUN1.apply_at f c = PARTFUN1.apply_at g c) :
    f = g :=
  FUNCT_1.th2 hf.1 hg.1 hd fun x hx => hv x hx

/-- `PARTFUN2:2` (`Th2`) -/
theorem th2 {C D f y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D) :
    y ∈ RELAT_1.rng f ↔
      ∃ c, c ∈ RELAT_1.dom f ∧ y = PARTFUN1.apply_at f c := by
  constructor
  · intro hy
    obtain ⟨x, hx, heq⟩ := (FUNCT_1.def3 hf.1.2).mp hy
    exact ⟨x, hx, heq⟩
  · intro ⟨c, hc, heq⟩
    exact Eq.subst (motive := fun s => s ∈ RELAT_1.rng f) heq.symm
      (FUNCT_1.th3 hf.1.2 hc)

/-- `PARTFUN2:3` (`Th3`) -/
theorem th3 {C D E f s h : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hs : PARTFUN1.isPartFunc s D E) (hh : PARTFUN1.isPartFunc h C E) :
    h = RELAT_1.comp f s ↔
      (∀ c, c ∈ RELAT_1.dom h ↔
        c ∈ RELAT_1.dom f ∧ PARTFUN1.apply_at f c ∈ RELAT_1.dom s) ∧
        ∀ c, c ∈ RELAT_1.dom h →
          PARTFUN1.apply_at h c =
            PARTFUN1.apply_at s (PARTFUN1.apply_at f c) := by
  constructor
  · intro heq
    refine ⟨fun c => ?_, fun c hc => ?_⟩
    · exact Iff.trans
        (Iff.of_eq (congrArg (fun t => c ∈ RELAT_1.dom t) heq))
        (FUNCT_1.th11 hf.1.2 (f := f) (g := s) (x := c))
    · have hc' : c ∈ RELAT_1.dom (RELAT_1.comp f s) :=
        Eq.subst (motive := fun t => c ∈ RELAT_1.dom t) heq hc
      exact Eq.subst (motive := fun t =>
          PARTFUN1.apply_at t c =
            PARTFUN1.apply_at s (PARTFUN1.apply_at f c)) heq.symm
        (FUNCT_1.th12 hf.1.2 hs.1.2 hc')
  · intro ⟨hd, hv⟩
    exact FUNCT_1.th10 hf.1 hs.1 hh.1 hd hv

/-- `PARTFUN2:4` (`Th4`) -/
theorem th4 {C D E f s c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hs : PARTFUN1.isPartFunc s D E)
    (hc : c ∈ RELAT_1.dom f)
    (hfc : PARTFUN1.apply_at f c ∈ RELAT_1.dom s) :
    PARTFUN1.apply_at (RELAT_1.comp f s) c =
      PARTFUN1.apply_at s (PARTFUN1.apply_at f c) := by
  have hh := comp_isPartFunc hf hs
  have hdom : c ∈ RELAT_1.dom (RELAT_1.comp f s) :=
    (FUNCT_1.th11 hf.1.2).mpr ⟨hc, hfc⟩
  exact ((th3 hf hs hh).mp rfl).2 c hdom

/-- Unlabeled `PARTFUN2:5` -/
theorem th5 {C D E f s c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hs : PARTFUN1.isPartFunc s D E)
    (hr : RELAT_1.rng f ⊆ RELAT_1.dom s) (hc : c ∈ RELAT_1.dom f) :
    PARTFUN1.apply_at (RELAT_1.comp f s) c =
      PARTFUN1.apply_at s (PARTFUN1.apply_at f c) :=
  th4 hf hs hc (hr _ ((th2 hf).mpr ⟨c, hc, rfl⟩))

/-- `PARTFUN2:6` (`Th6`) -/
theorem th6 {D SD F : TarskiSet.{u}} (_hSD : SD ⊆ D)
    (hF : PARTFUN1.isPartFunc F D D) :
    F = RELAT_1.id SD ↔
      RELAT_1.dom F = SD ∧
        ∀ d, d ∈ SD → PARTFUN1.apply_at F d = d :=
  (FUNCT_1.th17 hF.1).trans
    (Iff.rfl)

/-- Unlabeled `PARTFUN2:7` -/
theorem th7 {D SD F d : TarskiSet.{u}} (_hSD : SD ⊆ D)
    (hF : PARTFUN1.isPartFunc F D D)
    (hd : d ∈ RELAT_1.dom F ∩ SD) :
    PARTFUN1.apply_at F d =
      PARTFUN1.apply_at (RELAT_1.comp (RELAT_1.id SD) F) d :=
  FUNCT_1.th20 hF.1.2 hd

/-- Unlabeled `PARTFUN2:8` -/
theorem th8 {D SD F d : TarskiSet.{u}} (hSD : SD ⊆ D)
    (hF : PARTFUN1.isPartFunc F D D) :
    d ∈ RELAT_1.dom (RELAT_1.comp F (RELAT_1.id SD)) ↔
      d ∈ RELAT_1.dom F ∧ PARTFUN1.apply_at F d ∈ SD := by
  have hid := id_isPartFunc D SD hSD
  have hcomp := comp_isPartFunc hF hid
  have := (th3 hF hid hcomp).mp rfl
  exact Iff.trans (this.1 d)
    (and_congr Iff.rfl
      (Iff.trans
        (Iff.of_eq (congrArg (fun s => PARTFUN1.apply_at F d ∈ s)
          (RELAT_1.th45 (X := SD)).1))
        Iff.rfl))

/-- Unlabeled `PARTFUN2:9` -/
theorem th9 {C D f : TarskiSet.{u}} (_hf : PARTFUN1.isPartFunc f C D)
    (h : ∀ c1 c2, c1 ∈ RELAT_1.dom f → c2 ∈ RELAT_1.dom f →
      PARTFUN1.apply_at f c1 = PARTFUN1.apply_at f c2 → c1 = c2) :
    FUNCT_1.isOneToOne f :=
  fun x y hx hy heq => h x y hx hy heq

/-- Unlabeled `PARTFUN2:10` -/
theorem th10 {C D f x y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (h1 : FUNCT_1.isOneToOne f)
    (hx : x ∈ RELAT_1.dom f) (hy : y ∈ RELAT_1.dom f)
    (heq : PARTFUN1.apply_at f x = PARTFUN1.apply_at f y) : x = y :=
  h1 x y hx hy heq

/-- `PARTFUN2:11` (`Th11`) -/
theorem th11 {C D f g : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (h1 : FUNCT_1.isOneToOne f) (hg : PARTFUN1.isPartFunc g D C) :
    g = FUNCT_1.inv f ↔
      RELAT_1.dom g = RELAT_1.rng f ∧
        ∀ d c, (d ∈ RELAT_1.rng f ∧ c = PARTFUN1.apply_at g d) ↔
          (c ∈ RELAT_1.dom f ∧ d = PARTFUN1.apply_at f c) :=
  FUNCT_1.th32 hf.1 hg.1 h1

/-- Unlabeled `PARTFUN2:12` -/
theorem th12 {C D f c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (h1 : FUNCT_1.isOneToOne f) (hc : c ∈ RELAT_1.dom f) :
    c = PARTFUN1.apply_at (FUNCT_1.inv f) (PARTFUN1.apply_at f c) ∧
      c = PARTFUN1.apply_at (RELAT_1.comp f (FUNCT_1.inv f)) c :=
  let h := FUNCT_1.th34 hf.1 h1 hc
  ⟨h.1.symm, h.2.symm⟩

/-- Unlabeled `PARTFUN2:13` -/
theorem th13 {C D f d : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (h1 : FUNCT_1.isOneToOne f) (hd : d ∈ RELAT_1.rng f) :
    d = PARTFUN1.apply_at f (PARTFUN1.apply_at (FUNCT_1.inv f) d) ∧
      d = PARTFUN1.apply_at (RELAT_1.comp (FUNCT_1.inv f) f) d :=
  let h := FUNCT_1.th35 hf.1 h1 hd
  ⟨h.1.symm, h.2.symm⟩

/-- Unlabeled `PARTFUN2:14` -/
theorem th14 {C D f t : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (ht : PARTFUN1.isPartFunc t D C)
    (h1 : FUNCT_1.isOneToOne f)
    (hd : RELAT_1.dom f = RELAT_1.rng t)
    (hr : RELAT_1.rng f = RELAT_1.dom t)
    (hchar : ∀ c d, c ∈ RELAT_1.dom f → d ∈ RELAT_1.dom t →
      (PARTFUN1.apply_at f c = d ↔ PARTFUN1.apply_at t d = c)) :
    t = FUNCT_1.inv f :=
  FUNCT_1.th38 hf.1 ht.1 h1 hd hr hchar

/-- `PARTFUN2:15` (`Th15`) -/
theorem th15 {C D f g X : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hg : PARTFUN1.isPartFunc g C D) :
    g = RELAT_1.restrict f X ↔
      RELAT_1.dom g = RELAT_1.dom f ∩ X ∧
        ∀ c, c ∈ RELAT_1.dom g →
          PARTFUN1.apply_at g c = PARTFUN1.apply_at f c := by
  constructor
  · intro heq
    refine ⟨Eq.subst (motive := fun s => RELAT_1.dom s = RELAT_1.dom f ∩ X)
      heq.symm RELAT_1.th61, fun c hc => ?_⟩
    have hc' : c ∈ RELAT_1.dom (RELAT_1.restrict f X) :=
      Eq.subst (motive := fun s => c ∈ RELAT_1.dom s) heq hc
    exact Eq.subst (motive := fun s =>
        PARTFUN1.apply_at s c = PARTFUN1.apply_at f c) heq.symm
      (FUNCT_1.th47 hf.1.2 hc')
  · intro ⟨hd, hv⟩
    exact FUNCT_1.th46 hf.1 hg.1 hd hv

/-- `PARTFUN2:16` (`Th16`) -/
theorem th16 {C D f X c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hc : c ∈ RELAT_1.dom f ∩ X) :
    PARTFUN1.apply_at (RELAT_1.restrict f X) c = PARTFUN1.apply_at f c :=
  FUNCT_1.th48 hf.1.2 hc

/-- Unlabeled `PARTFUN2:17` -/
theorem th17 {C D f X c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hc : c ∈ RELAT_1.dom f) (hx : c ∈ X) :
    PARTFUN1.apply_at (RELAT_1.restrict f X) c = PARTFUN1.apply_at f c :=
  th16 hf ((XBOOLE_0.def4 (RELAT_1.dom f) X c).mpr ⟨hc, hx⟩)

/-- Unlabeled `PARTFUN2:18` -/
theorem th18 {C D f X c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hc : c ∈ RELAT_1.dom f) (hx : c ∈ X) :
    PARTFUN1.apply_at f c ∈ RELAT_1.rng (RELAT_1.restrict f X) :=
  FUNCT_1.th50 hf.1.2 hc hx

/-- `PARTFUN2:19` (`Th19`) -/
theorem th19 {C D f g X : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hg : PARTFUN1.isPartFunc g C D) :
    g = RELAT_1.restrictRng X f ↔
      (∀ c, c ∈ RELAT_1.dom g ↔
        c ∈ RELAT_1.dom f ∧ PARTFUN1.apply_at f c ∈ X) ∧
        ∀ c, c ∈ RELAT_1.dom g →
          PARTFUN1.apply_at g c = PARTFUN1.apply_at f c := by
  constructor
  · intro heq
    refine ⟨fun c => ?_, fun c hc => ?_⟩
    · exact Iff.trans
        (Iff.of_eq (congrArg (fun t => c ∈ RELAT_1.dom t) heq))
        (FUNCT_1.th54 hf.1 (Y := X) (x := c))
    · have hc' : c ∈ RELAT_1.dom (RELAT_1.restrictRng X f) :=
        Eq.subst (motive := fun t => c ∈ RELAT_1.dom t) heq hc
      exact Eq.subst (motive := fun t =>
          PARTFUN1.apply_at t c = PARTFUN1.apply_at f c) heq.symm
        (FUNCT_1.th55 hf.1 hc')
  · intro ⟨hd, hv⟩
    exact (FUNCT_1.th53 hf.1 hg.1 (Y := X)).mpr ⟨hd, hv⟩

/-- Unlabeled `PARTFUN2:20` -/
theorem th20 {C D f X c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D) :
    c ∈ RELAT_1.dom (RELAT_1.restrictRng X f) ↔
      c ∈ RELAT_1.dom f ∧ PARTFUN1.apply_at f c ∈ X :=
  ((th19 hf (restrictRng_isPartFunc hf)).mp rfl).1 c

/-- Unlabeled `PARTFUN2:21` -/
theorem th21 {C D f X c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hc : c ∈ RELAT_1.dom (RELAT_1.restrictRng X f)) :
    PARTFUN1.apply_at (RELAT_1.restrictRng X f) c = PARTFUN1.apply_at f c :=
  ((th19 hf (restrictRng_isPartFunc hf)).mp rfl).2 c hc

/-- `PARTFUN2:22` (`Th22`) -/
theorem th22 {C D f X SD : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (_hSD : SD ⊆ D) :
    SD = RELAT_1.image f X ↔
      ∀ d, d ∈ SD ↔
        ∃ c, c ∈ RELAT_1.dom f ∧ c ∈ X ∧ d = PARTFUN1.apply_at f c := by
  constructor
  · intro heq d
    exact Iff.trans
      (Iff.of_eq (congrArg (fun s => d ∈ s) heq))
      (FUNCT_1.def6 hf.1.2 (X := X) (y := d))
  · intro hchar
    exact eq_of_mem fun d =>
      (hchar d).trans (FUNCT_1.def6 hf.1.2 (X := X) (y := d)).symm

/-- Unlabeled `PARTFUN2:23` -/
theorem th23 {C D f X d : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D) :
    d ∈ RELAT_1.image f X ↔
      ∃ c, c ∈ RELAT_1.dom f ∧ c ∈ X ∧ d = PARTFUN1.apply_at f c :=
  FUNCT_1.def6 hf.1.2

/-- Unlabeled `PARTFUN2:24` -/
theorem th24 {C D f c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hc : c ∈ RELAT_1.dom f) :
    RELAT_1.Im f c = TARSKI.singleton (PARTFUN1.apply_at f c) :=
  FUNCT_1.th59 hf.1.2 hc

/-- Unlabeled `PARTFUN2:25` -/
theorem th25 {C D f c1 c2 : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (h1 : c1 ∈ RELAT_1.dom f) (h2 : c2 ∈ RELAT_1.dom f) :
    RELAT_1.image f (TARSKI.upair c1 c2) =
      TARSKI.upair (PARTFUN1.apply_at f c1) (PARTFUN1.apply_at f c2) :=
  FUNCT_1.th60 hf.1.2 h1 h2

/-- `PARTFUN2:26` (`Th26`) -/
theorem th26 {C D f X SC : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (_hSC : SC ⊆ C) :
    SC = RELAT_1.invimage f X ↔
      ∀ c, c ∈ SC ↔ c ∈ RELAT_1.dom f ∧ PARTFUN1.apply_at f c ∈ X := by
  constructor
  · intro heq c
    exact Iff.trans
      (Iff.of_eq (congrArg (fun s => c ∈ s) heq))
      (FUNCT_1.def7 hf.1.2 (Y := X) (x := c))
  · intro hchar
    exact eq_of_mem fun c =>
      (hchar c).trans (FUNCT_1.def7 hf.1.2 (Y := X) (x := c)).symm

/-- Unlabeled `PARTFUN2:27` -/
theorem th27 {C D f : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hCD : D = (∅ : TarskiSet.{u}) → C = (∅ : TarskiSet.{u})) :
    ∃ g, FUNCT_2.isFunctionOf g C D ∧
      ∀ c, c ∈ RELAT_1.dom f → FUNCT_1.apply g c = PARTFUN1.apply_at f c :=
  FUNCT_2.th71 hf hCD

/-- Unlabeled `PARTFUN2:28` -/
theorem th28 {C D f g : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hg : PARTFUN1.isPartFunc g C D) :
    PARTFUN1.tolerates f g ↔
      ∀ c, c ∈ RELAT_1.dom f ∩ RELAT_1.dom g →
        PARTFUN1.apply_at f c = PARTFUN1.apply_at g c :=
  Iff.rfl

/-- `PARTFUN2:sch PartFuncExD` -/
theorem sch_PartFuncExD (D C : TarskiSet.{u})
    (hD : D ≠ (∅ : TarskiSet.{u})) (hC : C ≠ (∅ : TarskiSet.{u}))
    (P : TarskiSet.{u} → TarskiSet.{u} → Prop) :
    ∃ f, PARTFUN1.isPartFunc f D C ∧
      (∀ d, d ∈ D → (d ∈ RELAT_1.dom f ↔ ∃ c, c ∈ C ∧ P d c)) ∧
        ∀ d, d ∈ RELAT_1.dom f → P d (PARTFUN1.apply_at f d) := by
  let x0 := nonempty_choose hC
  have hx0 : x0 ∈ C := nonempty_choose_mem hC
  obtain ⟨X, hX⟩ :=
    XBOOLE_0.sch_separation D (fun z => ∃ c, c ∈ C ∧ P z c)
  have hXsub : X ⊆ D := fun z hz => ((hX z).mp hz).1
  have hQ : ∀ d, d ∈ D → ∃ z, z ∈ C ∧
      ((∃ c, c ∈ C ∧ P d c) → P d z) ∧
        ((∀ c, c ∈ C → ¬ P d c) → z = x0) := by
    intro d _
    refine Or.elim (Classical.em (∃ c, c ∈ C ∧ P d c))
      (fun ⟨c, hc, hp⟩ => ⟨c, hc, fun _ => hp, fun hn => (hn c hc hp).elim⟩)
      (fun hn => ⟨x0, hx0,
        fun hex => (hn hex).elim,
        fun _ => rfl⟩)
  obtain ⟨g, hg, hv⟩ := FUNCT_2.sch_FuncExD D C hD hC
    (fun d z => ((∃ c, c ∈ C ∧ P d c) → P d z) ∧
      ((∀ c, c ∈ C → ¬ P d c) → z = x0))
    (fun d hd =>
      let ⟨z, hzC, h1, h2⟩ := hQ d hd
      ⟨z, hzC, h1, h2⟩)
  let f := RELAT_1.restrict g X
  have hf : PARTFUN1.isPartFunc f D C := PARTFUN1.th11 hg.1
  refine ⟨f, hf, ?_, ?_⟩
  · intro d hd
    have hdomg : RELAT_1.dom g = D :=
      FUNCT_2.functionOf_dom_eq' hg (fun h => (hC h).elim)
    constructor
    · intro hdf
      have hdfX : d ∈ X := RELAT_1.th58 (R := g) (X := X) d hdf
      exact ((hX d).mp hdfX).2
    · intro hex
      have hdX : d ∈ X := (hX d).mpr ⟨hd, hex⟩
      have : d ∈ RELAT_1.dom g ∩ X :=
        (XBOOLE_0.def4 (RELAT_1.dom g) X d).mpr
          ⟨Eq.subst (motive := fun s => d ∈ s) hdomg.symm hd, hdX⟩
      exact Eq.subst (motive := fun s => d ∈ s) RELAT_1.th61.symm this
  · intro d hdf
    have hdfX : d ∈ X := RELAT_1.th58 (R := g) (X := X) d hdf
    have hex : ∃ c, c ∈ C ∧ P d c := ((hX d).mp hdfX).2
    have hdD : d ∈ D := hXsub _ hdfX
    have hPg : P d (FUNCT_1.apply g d) := (hv d hdD).1 hex
    have happ : FUNCT_1.apply f d = FUNCT_1.apply g d :=
      FUNCT_1.th47 (FUNCT_2.functionOf_isFunction hg).2 hdf
    exact Eq.subst (motive := fun z => P d z) happ.symm hPg

/-- `PARTFUN2:sch LambdaPFD` -/
theorem sch_LambdaPFD (D C : TarskiSet.{u})
    (hD : D ≠ (∅ : TarskiSet.{u})) (hC : C ≠ (∅ : TarskiSet.{u}))
    (F : TarskiSet.{u} → TarskiSet.{u})
    (hF : ∀ d, d ∈ D → F d ∈ C)
    (P : TarskiSet.{u} → Prop) :
    ∃ f, PARTFUN1.isPartFunc f D C ∧
      (∀ d, d ∈ D → (d ∈ RELAT_1.dom f ↔ P d)) ∧
        ∀ d, d ∈ RELAT_1.dom f → PARTFUN1.apply_at f d = F d := by
  obtain ⟨f, hf, hdom, hv⟩ := sch_PartFuncExD D C hD hC
    (fun d c => P d ∧ c = F d)
  refine ⟨f, hf, ?_, ?_⟩
  · intro d hd
    constructor
    · intro hdf
      obtain ⟨c, hc, hp, heq⟩ := (hdom d hd).mp hdf
      exact hp
    · intro hP
      exact (hdom d hd).mpr ⟨F d, hF d hd, hP, rfl⟩
  · intro d hdf
    have hdD : d ∈ D := mem_dom_of_part hf hdf
    exact (hv d hdf).2

/-- `PARTFUN2:sch UnPartFuncD` -/
theorem sch_UnPartFuncD (C D : TarskiSet.{u})
    (_hC : C ≠ (∅ : TarskiSet.{u})) (_hD : D ≠ (∅ : TarskiSet.{u}))
    (X : TarskiSet.{u}) (F : TarskiSet.{u} → TarskiSet.{u})
    {f g : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hg : PARTFUN1.isPartFunc g C D)
    (hdf : RELAT_1.dom f = X)
    (hvf : ∀ c, c ∈ RELAT_1.dom f → PARTFUN1.apply_at f c = F c)
    (hdg : RELAT_1.dom g = X)
    (hvg : ∀ c, c ∈ RELAT_1.dom g → PARTFUN1.apply_at g c = F c) :
    f = g :=
  th1 hf hg (hdf.trans hdg.symm) fun c hc =>
    (hvf c hc).trans (hvg c (Eq.subst (motive := fun s => c ∈ s)
      (hdf.trans hdg.symm) hc)).symm

/-- `PARTFUN2:29` (`Th29`) -/
theorem th29 {C D SC d c : TarskiSet.{u}} (hSC : SC ⊆ C) (hd : d ∈ D)
    (hc : c ∈ SC) :
    PARTFUN1.apply_at (FUNCOP_1.mapsTo SC d) c = d := by
  have hdom : RELAT_1.dom (FUNCOP_1.mapsTo SC d) = SC :=
    FUNCOP_1.mapsTo_dom SC d
  have hcD : c ∈ RELAT_1.dom (FUNCOP_1.mapsTo SC d) :=
    Eq.subst (motive := fun s => c ∈ s) hdom.symm hc
  exact FUNCOP_1.th7 hc

/-- Unlabeled `PARTFUN2:30` -/
theorem th30 {C D f d : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hd : d ∈ D)
    (hv : ∀ c, c ∈ RELAT_1.dom f → PARTFUN1.apply_at f c = d) :
    f = FUNCOP_1.mapsTo (RELAT_1.dom f) d :=
  FUNCOP_1.th11 hf.1 (fun x hx => hv x hx)

/-- Unlabeled `PARTFUN2:31` -/
theorem th31 {C D E f SE c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hSE : SE ⊆ E) (hc : c ∈ RELAT_1.dom f) :
    RELAT_1.comp (FUNCOP_1.mapsTo SE c) f =
      FUNCOP_1.mapsTo SE (PARTFUN1.apply_at f c) :=
  FUNCOP_1.th17 hf.1 hc

/-- Unlabeled `PARTFUN2:32` -/
theorem th32 {C SC : TarskiSet.{u}} (hSC : SC ⊆ C) :
    PARTFUN1.isTotal (RELAT_1.id SC) C ↔ SC = C := by
  constructor
  · intro ht
    exact (RELAT_1.th45 (X := SC)).1.symm.trans ht
  · intro heq
    exact Eq.subst (motive := fun s => RELAT_1.dom (RELAT_1.id s) = C) heq.symm
      (RELAT_1.th45 (X := C)).1

/-- Unlabeled `PARTFUN2:33` -/
theorem th33 {C D SC d : TarskiSet.{u}} (hC : C ≠ (∅ : TarskiSet.{u}))
    (_hSC : SC ⊆ C) (_hd : d ∈ D)
    (ht : PARTFUN1.isTotal (FUNCOP_1.mapsTo SC d) C) :
    SC ≠ (∅ : TarskiSet.{u}) := by
  intro he
  have hdom : RELAT_1.dom (FUNCOP_1.mapsTo SC d) = C := ht
  have hempty : RELAT_1.dom (FUNCOP_1.mapsTo SC d) = (∅ : TarskiSet.{u}) :=
    Eq.subst (motive := fun s => RELAT_1.dom (FUNCOP_1.mapsTo s d) =
      (∅ : TarskiSet.{u})) he.symm (FUNCOP_1.th10 d).1
  exact hC (hdom.symm.trans hempty)


/-- Unlabeled `PARTFUN2:34` -/
theorem th34 {C D SC d : TarskiSet.{u}} (_hSC : SC ⊆ C) (_hd : d ∈ D) :
    PARTFUN1.isTotal (FUNCOP_1.mapsTo SC d) C ↔ SC = C := by
  constructor
  · intro ht
    exact (FUNCOP_1.mapsTo_dom SC d).symm.trans ht
  · intro heq
    exact Eq.subst (motive := fun s => RELAT_1.dom (FUNCOP_1.mapsTo s d) = C)
      heq.symm (FUNCOP_1.mapsTo_dom C d)

/-- `PARTFUN2:35` (`Th35`) -/
theorem th35 {C D f X : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hD : D ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.isConstant (RELAT_1.restrict f X) ↔
      ∃ d, d ∈ D ∧ ∀ c, c ∈ X ∩ RELAT_1.dom f →
        PARTFUN1.apply_at f c = d := by
  have hr : PARTFUN1.isPartFunc (RELAT_1.restrict f X) C D :=
    PARTFUN1.th11 hf
  constructor
  · intro hc
    obtain ⟨d, hd, hv⟩ := (def_constant hr hD).mp hc
    refine ⟨d, hd, fun c hcI => ?_⟩
    have hcR : c ∈ RELAT_1.dom (RELAT_1.restrict f X) :=
      Eq.subst (motive := fun s => c ∈ s) RELAT_1.th61.symm
        (Eq.subst (motive := fun s => c ∈ s)
          (XBOOLE_0.inter_comm (RELAT_1.dom f) X).symm hcI)
    have hcF : c ∈ RELAT_1.dom f :=
      ((XBOOLE_0.def4 X (RELAT_1.dom f) c).mp hcI).2
    exact (FUNCT_1.th47 hf.1.2 hcR).symm.trans (hv c hcR)
  · intro ⟨d, hd, hv⟩
    refine (def_constant hr hD).mpr ⟨d, hd, fun c hcR => ?_⟩
    have hcI : c ∈ X ∩ RELAT_1.dom f :=
      Eq.subst (motive := fun s => c ∈ s)
        (XBOOLE_0.inter_comm (RELAT_1.dom f) X)
        (Eq.subst (motive := fun s => c ∈ s) RELAT_1.th61 hcR)
    exact (FUNCT_1.th47 hf.1.2 hcR).trans (hv c hcI)

/-- Unlabeled `PARTFUN2:36` -/
theorem th36 {C D f X : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hD : D ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.isConstant (RELAT_1.restrict f X) ↔
      ∀ c1 c2, c1 ∈ X ∩ RELAT_1.dom f → c2 ∈ X ∩ RELAT_1.dom f →
        PARTFUN1.apply_at f c1 = PARTFUN1.apply_at f c2 := by
  constructor
  · intro hc c1 c2 h1 h2
    obtain ⟨d, _, hv⟩ := (th35 hf hD).mp hc
    exact (hv c1 h1).trans (hv c2 h2).symm
  · intro hpair
    refine Or.elim (Classical.em (X ∩ RELAT_1.dom f = (∅ : TarskiSet.{u})))
      (fun hempty =>
        (th35 hf hD).mpr ⟨nonempty_choose hD, nonempty_choose_mem hD,
          fun c hc => False.elim ((XBOOLE_0.empty_iff c).mp
            (Eq.subst (motive := fun s => c ∈ s) hempty hc))⟩)
      (fun hne =>
        let x := nonempty_choose hne
        have hx := nonempty_choose_mem hne
        (th35 hf hD).mpr ⟨PARTFUN1.apply_at f x, apply_mem_cod hf
          ((XBOOLE_0.def4 X (RELAT_1.dom f) x).mp hx).2,
          fun c hc => hpair c x hc hx⟩)

/-- Unlabeled `PARTFUN2:37` -/
theorem th37 {C D f X : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hmeet : X ∩ RELAT_1.dom f ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.isConstant (RELAT_1.restrict f X) ↔
      ∃ d, d ∈ D ∧ RELAT_1.rng (RELAT_1.restrict f X) = TARSKI.singleton d := by
  have hr : PARTFUN1.isPartFunc (RELAT_1.restrict f X) C D :=
    PARTFUN1.th11 hf
  constructor
  · intro hc
    obtain ⟨d, hd, hv⟩ := (th35 hf hD).mp hc
    refine ⟨d, hd, eq_of_mem fun x => ?_⟩
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ :=
        (FUNCT_1.def3 (FUNCT_1.restrict_isFunction hf.1).2).mp hx
      have hyI : y ∈ X ∩ RELAT_1.dom f :=
        Eq.subst (motive := fun s => y ∈ s)
          (XBOOLE_0.inter_comm (RELAT_1.dom f) X)
          (Eq.subst (motive := fun s => y ∈ s) RELAT_1.th61 hy)
      have happ : FUNCT_1.apply (RELAT_1.restrict f X) y = d :=
        (FUNCT_1.th47 hf.1.2 hy).trans (hv y hyI)
      exact (TARSKI.singleton_iff d x).mpr (heq.trans happ)
    · intro hx
      have heq : x = d := (TARSKI.singleton_iff d x).mp hx
      let y := nonempty_choose hmeet
      have hy := nonempty_choose_mem hmeet
      have hyR : y ∈ RELAT_1.dom (RELAT_1.restrict f X) :=
        Eq.subst (motive := fun s => y ∈ s) RELAT_1.th61.symm
          (Eq.subst (motive := fun s => y ∈ s)
            (XBOOLE_0.inter_comm (RELAT_1.dom f) X).symm hy)
      have happ : FUNCT_1.apply (RELAT_1.restrict f X) y = d :=
        (FUNCT_1.th47 hf.1.2 hyR).trans (hv y hy)
      exact Eq.subst (motive := fun s => s ∈ RELAT_1.rng (RELAT_1.restrict f X))
        (happ.trans heq.symm) ((th2 hr).mpr ⟨y, hyR, rfl⟩)
  · intro ⟨d, hd, hrng⟩
    refine (def_constant hr hD).mpr ⟨d, hd, fun c hc => ?_⟩
    have hin : PARTFUN1.apply_at (RELAT_1.restrict f X) c ∈ TARSKI.singleton d :=
      Eq.subst (motive := fun s =>
          PARTFUN1.apply_at (RELAT_1.restrict f X) c ∈ s) hrng
        ((th2 hr).mpr ⟨c, hc, rfl⟩)
    exact (TARSKI.singleton_iff d _).mp hin

/-- Unlabeled `PARTFUN2:38` -/
theorem th38 {C D f X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hc : FUNCT_1.isConstant (RELAT_1.restrict f X)) (hY : Y ⊆ X) :
    FUNCT_1.isConstant (RELAT_1.restrict f Y) := by
  obtain ⟨d, hd, hv⟩ := (th35 hf hD).mp hc
  refine (th35 hf hD).mpr ⟨d, hd, fun c hcI => ?_⟩
  have ⟨hcY, hcF⟩ := (XBOOLE_0.def4 Y (RELAT_1.dom f) c).mp hcI
  exact hv c ((XBOOLE_0.def4 X (RELAT_1.dom f) c).mpr ⟨hY _ hcY, hcF⟩)

/-- `PARTFUN2:39` (`Th39`) -/
theorem th39 {C D f X : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hmiss : X ∩ RELAT_1.dom f = (∅ : TarskiSet.{u})) :
    FUNCT_1.isConstant (RELAT_1.restrict f X) :=
  (th35 hf hD).mpr ⟨nonempty_choose hD, nonempty_choose_mem hD,
    fun c hc => False.elim ((XBOOLE_0.empty_iff c).mp
      (Eq.subst (motive := fun s => c ∈ s) hmiss hc))⟩

/-- Unlabeled `PARTFUN2:40` -/
theorem th40 {C D f SC d : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hD : D ≠ (∅ : TarskiSet.{u})) (_hSC : SC ⊆ C) (hd : d ∈ D)
    (heq : RELAT_1.restrict f SC =
      FUNCOP_1.mapsTo (RELAT_1.dom (RELAT_1.restrict f SC)) d) :
    FUNCT_1.isConstant (RELAT_1.restrict f SC) := by
  refine (th35 hf hD).mpr ⟨d, hd, fun c hcI => ?_⟩
  have hcR : c ∈ RELAT_1.dom (RELAT_1.restrict f SC) :=
    Eq.subst (motive := fun s => c ∈ s) RELAT_1.th61.symm
      (Eq.subst (motive := fun s => c ∈ s)
        (XBOOLE_0.inter_comm (RELAT_1.dom f) SC).symm hcI)
  have hmem : c ∈ RELAT_1.dom (RELAT_1.restrict f SC) := hcR
  have happM : FUNCT_1.apply
      (FUNCOP_1.mapsTo (RELAT_1.dom (RELAT_1.restrict f SC)) d) c = d :=
    FUNCOP_1.th7 hmem
  have happR : PARTFUN1.apply_at (RELAT_1.restrict f SC) c = d :=
    Eq.subst (motive := fun s => FUNCT_1.apply s c = d) heq.symm happM
  have hcIF : c ∈ RELAT_1.dom f ∩ SC :=
    Eq.subst (motive := fun s => c ∈ s) RELAT_1.th61 hcR
  exact (th16 hf hcIF).symm.trans happR


/-- Unlabeled `PARTFUN2:41` -/
theorem th41 {C D f x : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hD : D ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.isConstant (RELAT_1.restrict f (TARSKI.singleton x)) := by
  refine Or.elim (Classical.em
      (TARSKI.singleton x ∩ RELAT_1.dom f = (∅ : TarskiSet.{u})))
    (fun hempty => th39 hf hD hempty)
    (fun hne =>
      let y := nonempty_choose hne
      have hy := nonempty_choose_mem hne
      have ⟨hyS, hyD⟩ := (XBOOLE_0.def4 (TARSKI.singleton x) (RELAT_1.dom f) y).mp hy
      have hyx : y = x := (TARSKI.singleton_iff x y).mp hyS
      have hxD : x ∈ RELAT_1.dom f :=
        Eq.subst (motive := fun s => s ∈ RELAT_1.dom f) hyx hyD
      (th35 hf hD).mpr ⟨PARTFUN1.apply_at f x, apply_mem_cod hf hxD,
        fun c hc =>
          let ⟨hcS, _⟩ :=
            (XBOOLE_0.def4 (TARSKI.singleton x) (RELAT_1.dom f) c).mp hc
          let hcx : c = x := (TARSKI.singleton_iff x c).mp hcS
          Eq.subst (motive := fun s => PARTFUN1.apply_at f s =
            PARTFUN1.apply_at f x) hcx.symm rfl⟩)

/-- Unlabeled `PARTFUN2:42` -/
theorem th42 {C D f X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hX : FUNCT_1.isConstant (RELAT_1.restrict f X))
    (hY : FUNCT_1.isConstant (RELAT_1.restrict f Y))
    (hmeet : X ∩ Y ∩ RELAT_1.dom f ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.isConstant (RELAT_1.restrict f (X ∪ Y)) := by
  obtain ⟨d1, hd1, hv1⟩ := (th35 hf hD).mp hX
  obtain ⟨d2, hd2, hv2⟩ := (th35 hf hD).mp hY
  let z := nonempty_choose hmeet
  have hz := nonempty_choose_mem hmeet
  have ⟨hzXY, hzF⟩ := (XBOOLE_0.def4 (X ∩ Y) (RELAT_1.dom f) z).mp hz
  have ⟨hzX, hzY⟩ := (XBOOLE_0.def4 X Y z).mp hzXY
  have hzXF : z ∈ X ∩ RELAT_1.dom f :=
    (XBOOLE_0.def4 X (RELAT_1.dom f) z).mpr ⟨hzX, hzF⟩
  have hzYF : z ∈ Y ∩ RELAT_1.dom f :=
    (XBOOLE_0.def4 Y (RELAT_1.dom f) z).mpr ⟨hzY, hzF⟩
  have heq12 : d1 = d2 := (hv1 z hzXF).symm.trans (hv2 z hzYF)
  refine (def_constant (PARTFUN1.th11 hf) hD).mpr ⟨d1, hd1, fun c hc => ?_⟩
  have hcI : c ∈ (X ∪ Y) ∩ RELAT_1.dom f := by
    have h : c ∈ RELAT_1.dom f ∩ (X ∪ Y) :=
      Eq.subst (motive := fun s => c ∈ s) RELAT_1.th61 hc
    exact (XBOOLE_0.def4 (X ∪ Y) (RELAT_1.dom f) c).mpr
      ⟨((XBOOLE_0.def4 (RELAT_1.dom f) (X ∪ Y) c).mp h).2,
        ((XBOOLE_0.def4 (RELAT_1.dom f) (X ∪ Y) c).mp h).1⟩
  have ⟨hcU, hcF⟩ := (XBOOLE_0.def4 (X ∪ Y) (RELAT_1.dom f) c).mp hcI
  have happ : PARTFUN1.apply_at f c = d1 :=
    Or.elim ((XBOOLE_0.def3 X Y c).mp hcU)
      (fun hcX => hv1 c ((XBOOLE_0.def4 X (RELAT_1.dom f) c).mpr ⟨hcX, hcF⟩))
      (fun hcY =>
        (hv2 c ((XBOOLE_0.def4 Y (RELAT_1.dom f) c).mpr ⟨hcY, hcF⟩)).trans
          heq12.symm)
  exact (FUNCT_1.th47 hf.1.2 hc).trans happ

/-- Unlabeled `PARTFUN2:43` -/
theorem th43 {C D f X Y : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hD : D ≠ (∅ : TarskiSet.{u}))
    (hY : FUNCT_1.isConstant (RELAT_1.restrict f Y)) :
    FUNCT_1.isConstant (RELAT_1.restrict (RELAT_1.restrict f X) Y) := by
  obtain ⟨d, hd, hv⟩ := (th35 hf hD).mp hY
  refine (def_constant (PARTFUN1.th11 (PARTFUN1.th11 hf)) hD).mpr
    ⟨d, hd, fun c hc => ?_⟩
  have hcI : c ∈ Y ∩ RELAT_1.dom (RELAT_1.restrict f X) := by
    have h : c ∈ RELAT_1.dom (RELAT_1.restrict f X) ∩ Y :=
      Eq.subst (motive := fun s => c ∈ s) RELAT_1.th61 hc
    exact (XBOOLE_0.def4 Y (RELAT_1.dom (RELAT_1.restrict f X)) c).mpr
      ⟨((XBOOLE_0.def4 (RELAT_1.dom (RELAT_1.restrict f X)) Y c).mp h).2,
        ((XBOOLE_0.def4 (RELAT_1.dom (RELAT_1.restrict f X)) Y c).mp h).1⟩
  have ⟨hcY, hcRX⟩ :=
    (XBOOLE_0.def4 Y (RELAT_1.dom (RELAT_1.restrict f X)) c).mp hcI
  have hcF : c ∈ RELAT_1.dom f :=
    ((XBOOLE_0.def4 (RELAT_1.dom f) X c).mp
      (Eq.subst (motive := fun s => c ∈ s) RELAT_1.th61 hcRX)).1
  have happ : PARTFUN1.apply_at f c = d :=
    hv c ((XBOOLE_0.def4 Y (RELAT_1.dom f) c).mpr ⟨hcY, hcF⟩)
  have happX : PARTFUN1.apply_at (RELAT_1.restrict f X) c = d :=
    (FUNCT_1.th47 hf.1.2 hcRX).trans happ
  exact (FUNCT_1.th47 (FUNCT_1.restrict_isFunction hf.1).2 hc).trans happX

/-- Unlabeled `PARTFUN2:44` -/
theorem th44 {C D SC d : TarskiSet.{u}} (hSC : SC ⊆ C) (hd : d ∈ D)
    (hD : D ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.isConstant
      (RELAT_1.restrict (FUNCOP_1.mapsTo SC d) SC) := by
  have hm := mapsTo_isPartFunc (C := C) (D := D) hSC hd
  refine (def_constant (PARTFUN1.th11 hm) hD).mpr ⟨d, hd, fun c hc => ?_⟩
  have hcI : c ∈ SC ∩ RELAT_1.dom (FUNCOP_1.mapsTo SC d) := by
    have h : c ∈ RELAT_1.dom (FUNCOP_1.mapsTo SC d) ∩ SC :=
      Eq.subst (motive := fun s => c ∈ s) RELAT_1.th61 hc
    exact (XBOOLE_0.def4 SC (RELAT_1.dom (FUNCOP_1.mapsTo SC d)) c).mpr
      ⟨((XBOOLE_0.def4 (RELAT_1.dom (FUNCOP_1.mapsTo SC d)) SC c).mp h).2,
        ((XBOOLE_0.def4 (RELAT_1.dom (FUNCOP_1.mapsTo SC d)) SC c).mp h).1⟩
  have hcSC : c ∈ SC :=
    ((XBOOLE_0.def4 SC (RELAT_1.dom (FUNCOP_1.mapsTo SC d)) c).mp hcI).1
  exact (FUNCT_1.th47 (FUNCOP_1.mapsTo_isFunction SC d).2 hc).trans
    (FUNCOP_1.th7 hcSC)

/-- Unlabeled `PARTFUN2:45` -/
theorem th45 {C D f g : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hg : PARTFUN1.isPartFunc g C D)
    (hd : RELAT_1.dom f ⊆ RELAT_1.dom g)
    (hv : ∀ c, c ∈ RELAT_1.dom f →
      PARTFUN1.apply_at f c = PARTFUN1.apply_at g c) :
    f ⊆ g :=
  (GRFUNC_1.th2 hf.1 hg.1).mpr ⟨hd, hv⟩

/-- `PARTFUN2:46` (`Th46`) -/
theorem th46 {C D f c d : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D) :
    (c ∈ RELAT_1.dom f ∧ d = PARTFUN1.apply_at f c) ↔
      TARSKI.pair c d ∈ f :=
  (FUNCT_1.th1 hf.1.2 (x := c) (y := d)).symm

/-- Unlabeled `PARTFUN2:47` -/
theorem th47 {C D E f s c e : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (_hs : PARTFUN1.isPartFunc s D E)
    (hp : TARSKI.pair c e ∈ RELAT_1.comp f s) :
    TARSKI.pair c (PARTFUN1.apply_at f c) ∈ f ∧
      TARSKI.pair (PARTFUN1.apply_at f c) e ∈ s :=
  GRFUNC_1.th4 hf.1.2 hp

/-- Unlabeled `PARTFUN2:48` -/
theorem th48 {C D f c d : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (heq : f = TARSKI.singleton (TARSKI.pair c d)) :
    PARTFUN1.apply_at f c = d :=
  GRFUNC_1.th6 hf.1.2 heq

/-- Unlabeled `PARTFUN2:49` -/
theorem th49 {C D f c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hd : RELAT_1.dom f = TARSKI.singleton c) :
    f = TARSKI.singleton (TARSKI.pair c (PARTFUN1.apply_at f c)) :=
  GRFUNC_1.th7 hf.1 hd

/-- Unlabeled `PARTFUN2:50` -/
theorem th50 {C D f g f1 c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hg : PARTFUN1.isPartFunc g C D)
    (hf1 : PARTFUN1.isPartFunc f1 C D)
    (heq : f1 = f ∩ g) (hc : c ∈ RELAT_1.dom f1) :
    PARTFUN1.apply_at f1 c = PARTFUN1.apply_at f c ∧
      PARTFUN1.apply_at f1 c = PARTFUN1.apply_at g c := by
  have hcI : c ∈ RELAT_1.dom (f ∩ g) :=
    Eq.subst (motive := fun s => c ∈ RELAT_1.dom s) heq hc
  have h1 : FUNCT_1.apply (f ∩ g) c = FUNCT_1.apply f c :=
    GRFUNC_1.th11 hf.1 hcI
  have hcI' : c ∈ RELAT_1.dom (g ∩ f) :=
    Eq.subst (motive := fun s => c ∈ RELAT_1.dom s)
      (XBOOLE_0.inter_comm f g) hcI
  have h2 : FUNCT_1.apply (g ∩ f) c = FUNCT_1.apply g c :=
    GRFUNC_1.th11 hg.1 hcI'
  have h2' : FUNCT_1.apply (f ∩ g) c = FUNCT_1.apply g c :=
    Eq.subst (motive := fun s => FUNCT_1.apply s c = FUNCT_1.apply g c)
      (XBOOLE_0.inter_comm g f) h2
  exact ⟨Eq.subst (motive := fun s => FUNCT_1.apply s c = FUNCT_1.apply f c)
      heq.symm h1,
    Eq.subst (motive := fun s => FUNCT_1.apply s c = FUNCT_1.apply g c)
      heq.symm h2'⟩

/-- Unlabeled `PARTFUN2:51` -/
theorem th51 {C D f g f1 c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hg : PARTFUN1.isPartFunc g C D)
    (hf1 : PARTFUN1.isPartFunc f1 C D)
    (hc : c ∈ RELAT_1.dom f) (heq : f1 = f ∪ g) :
    PARTFUN1.apply_at f1 c = PARTFUN1.apply_at f c :=
  GRFUNC_1.th15 hf1.1.2 hf.1.2 hc
    (heq.trans (XBOOLE_0.union_comm f g))

/-- Unlabeled `PARTFUN2:52` -/
theorem th52 {C D f g f1 c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hg : PARTFUN1.isPartFunc g C D)
    (hf1 : PARTFUN1.isPartFunc f1 C D)
    (hc : c ∈ RELAT_1.dom g) (heq : f1 = f ∪ g) :
    PARTFUN1.apply_at f1 c = PARTFUN1.apply_at g c :=
  GRFUNC_1.th15 hf1.1.2 hg.1.2 hc heq

/-- Unlabeled `PARTFUN2:53` -/
theorem th53 {C D f g f1 c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hg : PARTFUN1.isPartFunc g C D)
    (hf1 : PARTFUN1.isPartFunc f1 C D)
    (hc : c ∈ RELAT_1.dom f1) (heq : f1 = f ∪ g) :
    PARTFUN1.apply_at f1 c = PARTFUN1.apply_at f c ∨
      PARTFUN1.apply_at f1 c = PARTFUN1.apply_at g c :=
  GRFUNC_1.th16 hf1.1.2 hf.1.2 hg.1.2 hc heq

/-- Unlabeled `PARTFUN2:54` -/
theorem th54 {C D f SC c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (_hSC : SC ⊆ C) :
    (c ∈ RELAT_1.dom f ∧ c ∈ SC) ↔
      TARSKI.pair c (PARTFUN1.apply_at f c) ∈ RELAT_1.restrict f SC :=
  GRFUNC_1.th22

/-- Unlabeled `PARTFUN2:55` -/
theorem th55 {C D f SD c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (_hSD : SD ⊆ D) :
    (c ∈ RELAT_1.dom f ∧ PARTFUN1.apply_at f c ∈ SD) ↔
      TARSKI.pair c (PARTFUN1.apply_at f c) ∈ RELAT_1.restrictRng SD f :=
  GRFUNC_1.th24

/-- Unlabeled `PARTFUN2:56` -/
theorem th56 {C D f SD c : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (_hSD : SD ⊆ D) :
    c ∈ RELAT_1.invimage f SD ↔
      TARSKI.pair c (PARTFUN1.apply_at f c) ∈ f ∧
        PARTFUN1.apply_at f c ∈ SD :=
  GRFUNC_1.th26 hf.1.2

/-- `PARTFUN2:57` (`Th57`) -/
theorem th57 {C D f X : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hD : D ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.isConstant (RELAT_1.restrict f X) ↔
      ∃ d, d ∈ D ∧ ∀ c, c ∈ X ∩ RELAT_1.dom f →
        FUNCT_1.apply f c = d := by
  constructor
  · intro hc
    obtain ⟨d, hd, hv⟩ := (th35 hf hD).mp hc
    exact ⟨d, hd, fun c hcI => hv c hcI⟩
  · intro ⟨d, hd, hv⟩
    exact (th35 hf hD).mpr ⟨d, hd, fun c hcI => hv c hcI⟩

/-- Unlabeled `PARTFUN2:58` -/
theorem th58 {C D f X : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hD : D ≠ (∅ : TarskiSet.{u})) :
    FUNCT_1.isConstant (RELAT_1.restrict f X) ↔
      ∀ c1 c2, c1 ∈ X ∩ RELAT_1.dom f → c2 ∈ X ∩ RELAT_1.dom f →
        FUNCT_1.apply f c1 = FUNCT_1.apply f c2 :=
  (th36 hf hD).trans Iff.rfl

/-- Unlabeled `PARTFUN2:59` -/
theorem th59 {C D f X d : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (hd : d ∈ RELAT_1.image f X) :
    ∃ c, c ∈ RELAT_1.dom f ∧ c ∈ X ∧ d = FUNCT_1.apply f c :=
  (FUNCT_1.def6 hf.1.2).mp hd

/-- Unlabeled `PARTFUN2:60` -/
theorem th60 {C D f c d : TarskiSet.{u}} (hf : PARTFUN1.isPartFunc f C D)
    (h1 : FUNCT_1.isOneToOne f) :
    (d ∈ RELAT_1.rng f ∧ c = FUNCT_1.apply (FUNCT_1.inv f) d) ↔
      (c ∈ RELAT_1.dom f ∧ d = FUNCT_1.apply f c) :=
  ((FUNCT_1.th32 hf.1 (FUNCT_1.inv_isFunction hf.1 h1) h1).mp rfl).2 d c

/-- Unlabeled `PARTFUN2:61` -/
theorem th61 {Y f g x : TarskiSet.{u}} (hf : FUNCT_1.isFunction f)
    (hg : FUNCT_1.isFunction g)
    (_hvf : RELAT_1.isXvalued f Y) (_hvg : RELAT_1.isXvalued g Y)
    (hsub : f ⊆ g) (hx : x ∈ RELAT_1.dom f) :
    PARTFUN1.apply_at f x = PARTFUN1.apply_at g x :=
  ((GRFUNC_1.th2 hf hg).mp hsub).2 x hx

end PARTFUN2
