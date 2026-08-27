import MizarCCL.ENUMSET1

/-
Copyright (c) 2011-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/xtuple_0.miz`.
Authors: Grzegorz Bancerek, Artur Korniłowicz, Andrzej Trybulec (Mizar),
  Lars Warren Ericson (Lean 4).
-/

/-!
# Kuratowski pairs, tuples, and projections

1–1 Lean rendering of Mizar article `XTUPLE_0`
(`vendor/mml/xtuple_0.miz`). Environ theorems: `ENUMSET1`, `TARSKI`,
`XBOOLE_0`, `XBOOLE_1`; schemes: `XBOOLE_0`. Ordered pairs are
`TARSKI.pair`. Lean list notation is not used for tuples.
-/

universe u

open TarskiSet TARSKI

namespace XTUPLE_0

variable {x x1 x2 x3 x4 y y1 y2 y3 y4 z : TarskiSet.{u}}

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

/-! ## Pair attribute and injectivity -/

def isPair (x : TarskiSet.{u}) : Prop :=
  ∃ x1 x2, x = pair x1 x2

theorem pair_isPair (x1 x2 : TarskiSet.{u}) : isPair (pair x1 x2) :=
  ⟨x1, x2, rfl⟩

/-- `XTUPLE_0:1` (`Th1`). -/
theorem th1 {x1 x2 y1 y2 : TarskiSet.{u}}
    (h : pair x1 x2 = pair y1 y2) : x1 = y1 ∧ x2 = y2 :=
  pair_inj.mp h

/-! ## Component projections `x`1`, `x`2` -/

noncomputable def fst (x : TarskiSet.{u}) : TarskiSet.{u} :=
  have := Classical.propDecidable (isPair x)
  if h : isPair x then Classical.choose h else XBOOLE_0.theSet

noncomputable def snd (x : TarskiSet.{u}) : TarskiSet.{u} :=
  have := Classical.propDecidable (isPair x)
  if h : isPair x then Classical.choose (Classical.choose_spec h)
  else XBOOLE_0.theSet

theorem fst_pair (x1 x2 : TarskiSet.{u}) : fst (pair x1 x2) = x1 := by
  classical
  have h : isPair (pair x1 x2) := pair_isPair x1 x2
  obtain ⟨y2, heq⟩ := Classical.choose_spec h
  change (if h : isPair (pair x1 x2) then Classical.choose h else XBOOLE_0.theSet) = x1
  rw [dif_pos h]
  exact (th1 heq.symm).1

theorem snd_pair (x1 x2 : TarskiSet.{u}) : snd (pair x1 x2) = x2 := by
  classical
  have h : isPair (pair x1 x2) := pair_isPair x1 x2
  have heq := Classical.choose_spec (Classical.choose_spec h)
  change (if h : isPair (pair x1 x2) then
      Classical.choose (Classical.choose_spec h) else XBOOLE_0.theSet) = x2
  rw [dif_pos h]
  exact (th1 heq.symm).2

/-- `XTUPLE_0:def 1`. -/
theorem def1 {x y1 y2 : TarskiSet.{u}} (h : x = pair y1 y2) : fst x = y1 :=
  h ▸ fst_pair y1 y2

/-- `XTUPLE_0:def 2`. -/
theorem def2 {x y1 y2 : TarskiSet.{u}} (h : x = pair y1 y2) : snd x = y2 :=
  h ▸ snd_pair y1 y2

theorem pair_exists : ∃ x : TarskiSet.{u}, isPair x :=
  ⟨pair XBOOLE_0.theSet XBOOLE_0.theSet, pair_isPair _ _⟩

theorem pair_eta {x : TarskiSet.{u}} (h : isPair x) : pair (fst x) (snd x) = x := by
  obtain ⟨x1, x2, rfl⟩ := h
  rw [fst_pair, snd_pair]

/-- Unlabeled theorem after the pair-eta registration. -/
theorem th2 {a b : TarskiSet.{u}} (ha : isPair a) (hb : isPair b)
    (h1 : fst a = fst b) (h2 : snd a = snd b) : a = b := by
  rw [← pair_eta ha, ← pair_eta hb, h1, h2]

/-! ## Triples -/

def triple (x1 x2 x3 : TarskiSet.{u}) : TarskiSet.{u} :=
  pair (pair x1 x2) x3

def isTriple (x : TarskiSet.{u}) : Prop :=
  ∃ x1 x2 x3, x = triple x1 x2 x3

theorem triple_isTriple (x1 x2 x3 : TarskiSet.{u}) :
    isTriple (triple x1 x2 x3) :=
  ⟨x1, x2, x3, rfl⟩

/-- `XTUPLE_0:3` (`Th3`). -/
theorem th3 {x1 x2 x3 y1 y2 y3 : TarskiSet.{u}}
    (h : triple x1 x2 x3 = triple y1 y2 y3) :
    x1 = y1 ∧ x2 = y2 ∧ x3 = y3 := by
  have hp := th1 h
  have hq := th1 hp.1
  exact ⟨hq.1, hq.2, hp.2⟩

theorem triple_exists : ∃ x : TarskiSet.{u}, isTriple x :=
  ⟨triple XBOOLE_0.theSet XBOOLE_0.theSet XBOOLE_0.theSet, triple_isTriple _ _ _⟩

theorem triple_isPair {x : TarskiSet.{u}} (h : isTriple x) : isPair x := by
  obtain ⟨x1, x2, x3, rfl⟩ := h
  exact pair_isPair _ _

noncomputable def fst3 (x : TarskiSet.{u}) : TarskiSet.{u} := fst (fst x)
noncomputable def snd3 (x : TarskiSet.{u}) : TarskiSet.{u} := snd (fst x)
noncomputable def thd3 (x : TarskiSet.{u}) : TarskiSet.{u} := snd x

theorem fst3_triple (x1 x2 x3 : TarskiSet.{u}) :
    fst3 (triple x1 x2 x3) = x1 := by
  simp [fst3, triple, fst_pair]

theorem snd3_triple (x1 x2 x3 : TarskiSet.{u}) :
    snd3 (triple x1 x2 x3) = x2 := by
  simp [snd3, triple, fst_pair, snd_pair]

theorem thd3_triple (x1 x2 x3 : TarskiSet.{u}) :
    thd3 (triple x1 x2 x3) = x3 := by
  simp [thd3, triple, snd_pair]

theorem triple_eta {x : TarskiSet.{u}} (h : isTriple x) :
    triple (fst3 x) (snd3 x) (thd3 x) = x := by
  obtain ⟨x1, x2, x3, rfl⟩ := h
  rw [fst3_triple, snd3_triple, thd3_triple]

theorem th4 {a b : TarskiSet.{u}} (ha : isTriple a) (hb : isTriple b)
    (h1 : fst3 a = fst3 b) (h2 : snd3 a = snd3 b) (h3 : thd3 a = thd3 b) :
    a = b := by
  rw [← triple_eta ha, ← triple_eta hb, h1, h2, h3]

/-! ## Quadruples -/

def quadruple (x1 x2 x3 x4 : TarskiSet.{u}) : TarskiSet.{u} :=
  pair (triple x1 x2 x3) x4

def isQuadruple (x : TarskiSet.{u}) : Prop :=
  ∃ x1 x2 x3 x4, x = quadruple x1 x2 x3 x4

theorem quadruple_isQuadruple (x1 x2 x3 x4 : TarskiSet.{u}) :
    isQuadruple (quadruple x1 x2 x3 x4) :=
  ⟨x1, x2, x3, x4, rfl⟩

theorem th5 {x1 x2 x3 x4 y1 y2 y3 y4 : TarskiSet.{u}}
    (h : quadruple x1 x2 x3 x4 = quadruple y1 y2 y3 y4) :
    x1 = y1 ∧ x2 = y2 ∧ x3 = y3 ∧ x4 = y4 := by
  have hp := th1 h
  have hq := th3 hp.1
  exact ⟨hq.1, hq.2.1, hq.2.2, hp.2⟩

theorem quadruple_exists : ∃ x : TarskiSet.{u}, isQuadruple x :=
  ⟨quadruple XBOOLE_0.theSet XBOOLE_0.theSet XBOOLE_0.theSet XBOOLE_0.theSet,
    quadruple_isQuadruple _ _ _ _⟩

theorem quadruple_isTriple {x : TarskiSet.{u}} (h : isQuadruple x) :
    isTriple x := by
  obtain ⟨x1, x2, x3, x4, rfl⟩ := h
  refine ⟨pair x1 x2, x3, x4, ?_⟩
  simp [quadruple, triple]

noncomputable def fst4 (x : TarskiSet.{u}) : TarskiSet.{u} := fst (fst (fst x))
noncomputable def snd4 (x : TarskiSet.{u}) : TarskiSet.{u} := snd (fst (fst x))
noncomputable def thd4 (x : TarskiSet.{u}) : TarskiSet.{u} := snd3 x
noncomputable def fth4 (x : TarskiSet.{u}) : TarskiSet.{u} := snd x

theorem fst4_quadruple (x1 x2 x3 x4 : TarskiSet.{u}) :
    fst4 (quadruple x1 x2 x3 x4) = x1 := by
  simp [fst4, quadruple, triple, fst_pair]

theorem snd4_quadruple (x1 x2 x3 x4 : TarskiSet.{u}) :
    snd4 (quadruple x1 x2 x3 x4) = x2 := by
  simp [snd4, quadruple, triple, fst_pair, snd_pair]

theorem thd4_quadruple (x1 x2 x3 x4 : TarskiSet.{u}) :
    thd4 (quadruple x1 x2 x3 x4) = x3 := by
  simp [thd4, snd3, quadruple, triple, fst_pair, snd_pair]

theorem fth4_quadruple (x1 x2 x3 x4 : TarskiSet.{u}) :
    fth4 (quadruple x1 x2 x3 x4) = x4 := by
  simp [fth4, quadruple, snd_pair]

theorem quadruple_eta {x : TarskiSet.{u}} (h : isQuadruple x) :
    quadruple (fst4 x) (snd4 x) (thd4 x) (fth4 x) = x := by
  obtain ⟨x1, x2, x3, x4, rfl⟩ := h
  rw [fst4_quadruple, snd4_quadruple, thd4_quadruple, fth4_quadruple]

/-! ## Preliminaries -/

/-- `XTUPLE_0` `Pre1`. -/
theorem pre1 {x y X : TarskiSet.{u}} (h : pair x y ∈ X) :
    x ∈ union (union X) := by
  have hs : TARSKI.singleton x ∈ pair x y :=
    (upair_iff _ _ _).mpr (Or.inr rfl)
  have hsU : TARSKI.singleton x ∈ union X :=
    (union_iff _ _).mpr ⟨pair x y, hs, h⟩
  exact (union_iff _ _).mpr ⟨TARSKI.singleton x, (singleton_iff x x).mpr rfl, hsU⟩

/-- `XTUPLE_0` `Pre2`. -/
theorem pre2 {x y X : TarskiSet.{u}} (h : pair x y ∈ X) :
    y ∈ union (union X) := by
  have hu : upair x y ∈ pair x y :=
    (upair_iff _ _ _).mpr (Or.inl rfl)
  have huU : upair x y ∈ union X :=
    (union_iff _ _).mpr ⟨pair x y, hu, h⟩
  exact (union_iff _ _).mpr ⟨upair x y, (upair_iff x y y).mpr (Or.inr rfl), huU⟩

/-! ## Set projections -/

noncomputable def proj1 (X : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose <|
    XBOOLE_0.sch_separation (union (union X)) (fun x => ∃ y, pair x y ∈ X)

noncomputable def proj2 (X : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose <|
    XBOOLE_0.sch_separation (union (union X)) (fun x => ∃ y, pair y x ∈ X)

/-- `XTUPLE_0:def 4`. -/
theorem def4 (X x : TarskiSet.{u}) :
    x ∈ proj1 X ↔ ∃ y, pair x y ∈ X := by
  have h := Classical.choose_spec
    (XBOOLE_0.sch_separation (union (union X)) (fun x => ∃ y, pair x y ∈ X)) x
  constructor
  · intro hx
    exact (h.mp hx).2
  · intro ⟨y, hp⟩
    exact h.mpr ⟨pre1 hp, ⟨y, hp⟩⟩

/-- `XTUPLE_0:def 5`. -/
theorem def5 (X x : TarskiSet.{u}) :
    x ∈ proj2 X ↔ ∃ y, pair y x ∈ X := by
  have h := Classical.choose_spec
    (XBOOLE_0.sch_separation (union (union X)) (fun x => ∃ y, pair y x ∈ X)) x
  constructor
  · intro hx
    exact (h.mp hx).2
  · intro ⟨y, hp⟩
    exact h.mpr ⟨pre2 hp, ⟨y, hp⟩⟩

/-- `XTUPLE_0:10` (`Th10`). -/
theorem th10 {X Y : TarskiSet.{u}} (h : X ⊆ Y) : proj1 X ⊆ proj1 Y := by
  intro x hx
  obtain ⟨y, hp⟩ := (def4 X x).mp hx
  exact (def4 Y x).mpr ⟨y, h _ hp⟩

/-- `XTUPLE_0:11` (`Th11`). -/
theorem th11 {X Y : TarskiSet.{u}} (h : X ⊆ Y) : proj2 X ⊆ proj2 Y := by
  intro x hx
  obtain ⟨y, hp⟩ := (def5 X x).mp hx
  exact (def5 Y x).mpr ⟨y, h _ hp⟩

noncomputable def proj1_3 (X : TarskiSet.{u}) : TarskiSet.{u} := proj1 (proj1 X)
noncomputable def proj2_3 (X : TarskiSet.{u}) : TarskiSet.{u} := proj2 (proj1 X)
noncomputable def proj3_3 (X : TarskiSet.{u}) : TarskiSet.{u} := proj2 X

/-- `XTUPLE_0:12`. -/
theorem th12 {X Y : TarskiSet.{u}} (h : X ⊆ Y) : proj1_3 X ⊆ proj1_3 Y :=
  th10 (th10 h)

/-- `XTUPLE_0:13`. -/
theorem th13 {X Y : TarskiSet.{u}} (h : X ⊆ Y) : proj2_3 X ⊆ proj2_3 Y :=
  th11 (th10 h)

/-- `XTUPLE_0:14`. -/
theorem th14 {x X : TarskiSet.{u}} (h : x ∈ proj1_3 X) :
    ∃ y z, triple x y z ∈ X := by
  obtain ⟨y, hy⟩ := (def4 (proj1 X) x).mp h
  obtain ⟨z, hz⟩ := (def4 X (pair x y)).mp hy
  exact ⟨y, z, hz⟩

/-- `XTUPLE_0:14a`. -/
theorem th14a {x y z X : TarskiSet.{u}} (h : triple x y z ∈ X) :
    x ∈ proj1_3 X :=
  (def4 (proj1 X) x).mpr ⟨y, (def4 X (pair x y)).mpr ⟨z, h⟩⟩

/-- `XTUPLE_0:15`. -/
theorem th15 {x X : TarskiSet.{u}} (h : x ∈ proj2_3 X) :
    ∃ y z, triple y x z ∈ X := by
  obtain ⟨y, hy⟩ := (def5 (proj1 X) x).mp h
  obtain ⟨z, hz⟩ := (def4 X (pair y x)).mp hy
  exact ⟨y, z, hz⟩

/-- `XTUPLE_0:15a`. -/
theorem th15a {x y z X : TarskiSet.{u}} (h : triple x y z ∈ X) :
    y ∈ proj2_3 X :=
  (def5 (proj1 X) y).mpr ⟨x, (def4 X (pair x y)).mpr ⟨z, h⟩⟩

noncomputable def proj1_4 (X : TarskiSet.{u}) : TarskiSet.{u} := proj1 (proj1_3 X)
noncomputable def proj2_4 (X : TarskiSet.{u}) : TarskiSet.{u} := proj2 (proj1_3 X)
noncomputable def proj3_4 (X : TarskiSet.{u}) : TarskiSet.{u} := proj2_3 X
noncomputable def proj4_4 (X : TarskiSet.{u}) : TarskiSet.{u} := proj2 X

/-- `XTUPLE_0:17`. -/
theorem th17 {X Y : TarskiSet.{u}} (h : X ⊆ Y) : proj1_4 X ⊆ proj1_4 Y :=
  th10 (th12 h)

/-- `XTUPLE_0:18`. -/
theorem th18 {X Y : TarskiSet.{u}} (h : X ⊆ Y) : proj2_4 X ⊆ proj2_4 Y :=
  th11 (th12 h)

/-- `XTUPLE_0:19`. -/
theorem th19 {x X : TarskiSet.{u}} (h : x ∈ proj1_4 X) :
    ∃ x1 x2 x3, quadruple x x1 x2 x3 ∈ X := by
  obtain ⟨x1, hx1⟩ := (def4 (proj1_3 X) x).mp h
  obtain ⟨x2, hx2⟩ := (def4 (proj1 X) (pair x x1)).mp hx1
  obtain ⟨x3, hx3⟩ := (def4 X (pair (pair x x1) x2)).mp hx2
  exact ⟨x1, x2, x3, hx3⟩

/-- `XTUPLE_0:19a`. -/
theorem th19a {x x1 x2 x3 X : TarskiSet.{u}}
    (h : quadruple x x1 x2 x3 ∈ X) : x ∈ proj1_4 X := by
  have h' : triple (pair x x1) x2 x3 ∈ X := h
  have : pair x x1 ∈ proj1_3 X := th14a h'
  exact (def4 (proj1_3 X) x).mpr ⟨x1, this⟩

/-- `XTUPLE_0:20`. -/
theorem th20 {x X : TarskiSet.{u}} (h : x ∈ proj2_4 X) :
    ∃ x1 x2 x3, quadruple x1 x x2 x3 ∈ X := by
  obtain ⟨x1, hx1⟩ := (def5 (proj1_3 X) x).mp h
  obtain ⟨x2, hx2⟩ := (def4 (proj1 X) (pair x1 x)).mp hx1
  obtain ⟨x3, hx3⟩ := (def4 X (pair (pair x1 x) x2)).mp hx2
  exact ⟨x1, x2, x3, hx3⟩

/-- `XTUPLE_0:20a`. -/
theorem th20a {x1 x x2 x3 X : TarskiSet.{u}}
    (h : quadruple x1 x x2 x3 ∈ X) : x ∈ proj2_4 X := by
  have h' : triple (pair x1 x) x2 x3 ∈ X := h
  have : pair x1 x ∈ proj1_3 X := th14a h'
  exact (def5 (proj1_3 X) x).mpr ⟨x1, this⟩

theorem th21 {a b : TarskiSet.{u}} (ha : isQuadruple a) (hb : isQuadruple b)
    (h1 : fst4 a = fst4 b) (h2 : snd4 a = snd4 b)
    (h3 : thd4 a = thd4 b) (h4 : fth4 a = fth4 b) : a = b := by
  rw [← quadruple_eta ha, ← quadruple_eta hb, h1, h2, h3, h4]

/-! ## Boolean properties of projections -/

theorem proj1_empty {X : TarskiSet.{u}} (hX : XBOOLE_0.isEmpty X) :
    XBOOLE_0.isEmpty (proj1 X) := by
  intro ⟨x, hx⟩
  obtain ⟨y, hp⟩ := (def4 X x).mp hx
  exact hX ⟨pair x y, hp⟩

theorem proj2_empty {X : TarskiSet.{u}} (hX : XBOOLE_0.isEmpty X) :
    XBOOLE_0.isEmpty (proj2 X) := by
  intro ⟨x, hx⟩
  obtain ⟨y, hp⟩ := (def5 X x).mp hx
  exact hX ⟨pair y x, hp⟩

theorem proj1_3_empty {X : TarskiSet.{u}} (hX : XBOOLE_0.isEmpty X) :
    XBOOLE_0.isEmpty (proj1_3 X) :=
  proj1_empty (proj1_empty hX)

theorem proj2_3_empty {X : TarskiSet.{u}} (hX : XBOOLE_0.isEmpty X) :
    XBOOLE_0.isEmpty (proj2_3 X) :=
  proj2_empty (proj1_empty hX)

theorem proj1_4_empty {X : TarskiSet.{u}} (hX : XBOOLE_0.isEmpty X) :
    XBOOLE_0.isEmpty (proj1_4 X) :=
  proj1_empty (proj1_3_empty hX)

theorem proj2_4_empty {X : TarskiSet.{u}} (hX : XBOOLE_0.isEmpty X) :
    XBOOLE_0.isEmpty (proj2_4 X) :=
  proj2_empty (proj1_3_empty hX)

private theorem of_symmdiff
    {P : TarskiSet.{u} → TarskiSet.{u}} {X Y : TarskiSet.{u}}
    (hunion : ∀ A B, P (A ∪ B) = P A ∪ P B)
    (hdiff : ∀ A B, P A \ P B ⊆ P (A \ B)) :
    P X ∆ P Y ⊆ P (X ∆ Y) := by
  intro x hx
  rw [XBOOLE_0.def6] at hx
  rw [XBOOLE_0.def6, hunion]
  exact XBOOLE_1.th13 (hdiff X Y) (hdiff Y X) x hx

/-- `XTUPLE_0:22`. -/
theorem th22 (X Y : TarskiSet.{u}) : proj1 (X ∪ Y) = proj1 X ∪ proj1 Y :=
  eq_of_mem fun x => by
    constructor
    · intro hx
      obtain ⟨y, hp⟩ := (def4 (X ∪ Y) x).mp hx
      rcases (XBOOLE_0.def3 X Y (pair x y)).mp hp with hX | hY
      · exact (XBOOLE_0.def3 (proj1 X) (proj1 Y) x).mpr
          (Or.inl ((def4 X x).mpr ⟨y, hX⟩))
      · exact (XBOOLE_0.def3 (proj1 X) (proj1 Y) x).mpr
          (Or.inr ((def4 Y x).mpr ⟨y, hY⟩))
    · intro hx
      exact XBOOLE_1.th8
        (th10 (XBOOLE_1.th7 (X := X) (Y := Y)))
        (by
          rw [XBOOLE_0.union_comm X Y]
          exact th10 (XBOOLE_1.th7 (X := Y) (Y := X)))
        x hx

theorem th23 (X Y : TarskiSet.{u}) : proj1 (X ∩ Y) ⊆ proj1 X ∩ proj1 Y :=
  XBOOLE_1.th19 (th10 (XBOOLE_1.th17 (X := X) (Y := Y)))
    (th10 (by
      rw [XBOOLE_0.inter_comm X Y]
      exact XBOOLE_1.th17 (X := Y) (Y := X)))

/-- `XTUPLE_0:24`. -/
theorem th24 (X Y : TarskiSet.{u}) : proj1 X \ proj1 Y ⊆ proj1 (X \ Y) := by
  intro x hx
  have ⟨hxX, hxY⟩ := (XBOOLE_0.def5 (proj1 X) (proj1 Y) x).mp hx
  obtain ⟨y, hp⟩ := (def4 X x).mp hxX
  have hny : pair x y ∉ Y := fun hY => hxY ((def4 Y x).mpr ⟨y, hY⟩)
  exact (def4 (X \ Y) x).mpr ⟨y, (XBOOLE_0.def5 X Y (pair x y)).mpr ⟨hp, hny⟩⟩

theorem th25 (X Y : TarskiSet.{u}) : proj1 X ∆ proj1 Y ⊆ proj1 (X ∆ Y) :=
  of_symmdiff th22 th24

/-- `XTUPLE_0:26`. -/
theorem th26 (X Y : TarskiSet.{u}) : proj2 (X ∪ Y) = proj2 X ∪ proj2 Y :=
  eq_of_mem fun y => by
    constructor
    · intro hy
      obtain ⟨x, hp⟩ := (def5 (X ∪ Y) y).mp hy
      rcases (XBOOLE_0.def3 X Y (pair x y)).mp hp with hX | hY
      · exact (XBOOLE_0.def3 (proj2 X) (proj2 Y) y).mpr
          (Or.inl ((def5 X y).mpr ⟨x, hX⟩))
      · exact (XBOOLE_0.def3 (proj2 X) (proj2 Y) y).mpr
          (Or.inr ((def5 Y y).mpr ⟨x, hY⟩))
    · intro hy
      exact XBOOLE_1.th8
        (th11 (XBOOLE_1.th7 (X := X) (Y := Y)))
        (by
          rw [XBOOLE_0.union_comm X Y]
          exact th11 (XBOOLE_1.th7 (X := Y) (Y := X)))
        y hy

theorem th27 (X Y : TarskiSet.{u}) : proj2 (X ∩ Y) ⊆ proj2 X ∩ proj2 Y := by
  intro y hy
  obtain ⟨x, hp⟩ := (def5 (X ∩ Y) y).mp hy
  have ⟨hX, hY⟩ := (XBOOLE_0.def4 X Y (pair x y)).mp hp
  exact (XBOOLE_0.def4 (proj2 X) (proj2 Y) y).mpr
    ⟨(def5 X y).mpr ⟨x, hX⟩, (def5 Y y).mpr ⟨x, hY⟩⟩

/-- `XTUPLE_0:28`. -/
theorem th28 (X Y : TarskiSet.{u}) : proj2 X \ proj2 Y ⊆ proj2 (X \ Y) := by
  intro y hy
  have ⟨hyX, hyY⟩ := (XBOOLE_0.def5 (proj2 X) (proj2 Y) y).mp hy
  obtain ⟨x, hp⟩ := (def5 X y).mp hyX
  have hnx : pair x y ∉ Y := fun hY => hyY ((def5 Y y).mpr ⟨x, hY⟩)
  exact (def5 (X \ Y) y).mpr ⟨x, (XBOOLE_0.def5 X Y (pair x y)).mpr ⟨hp, hnx⟩⟩

theorem th29 (X Y : TarskiSet.{u}) : proj2 X ∆ proj2 Y ⊆ proj2 (X ∆ Y) :=
  of_symmdiff th26 th28

/-- `XTUPLE_0:30`. -/
theorem th30 (X Y : TarskiSet.{u}) : proj1_3 (X ∪ Y) = proj1_3 X ∪ proj1_3 Y :=
  (congrArg proj1 (th22 X Y)).trans (th22 (proj1 X) (proj1 Y))

theorem th31 (X Y : TarskiSet.{u}) : proj1_3 (X ∩ Y) ⊆ proj1_3 X ∩ proj1_3 Y :=
  XBOOLE_1.th19 (th12 (XBOOLE_1.th17 (X := X) (Y := Y)))
    (th12 (by
      rw [XBOOLE_0.inter_comm X Y]
      exact XBOOLE_1.th17 (X := Y) (Y := X)))

/-- `XTUPLE_0:32` (triples). -/
theorem th32 (X Y : TarskiSet.{u}) : proj1_3 X \ proj1_3 Y ⊆ proj1_3 (X \ Y) := by
  intro x hx
  have ⟨hxX, hxY⟩ := (XBOOLE_0.def5 (proj1_3 X) (proj1_3 Y) x).mp hx
  obtain ⟨y, z, hp⟩ := th14 hxX
  have hn : triple x y z ∉ Y := fun hY => hxY (th14a hY)
  exact th14a ((XBOOLE_0.def5 X Y (triple x y z)).mpr ⟨hp, hn⟩)

theorem th33 (X Y : TarskiSet.{u}) : proj1_3 X ∆ proj1_3 Y ⊆ proj1_3 (X ∆ Y) :=
  of_symmdiff th30 th32

/-- `XTUPLE_0:34` (triples). -/
theorem th34 (X Y : TarskiSet.{u}) : proj2_3 (X ∪ Y) = proj2_3 X ∪ proj2_3 Y :=
  (congrArg proj2 (th22 X Y)).trans (th26 (proj1 X) (proj1 Y))

theorem th35 (X Y : TarskiSet.{u}) : proj2_3 (X ∩ Y) ⊆ proj2_3 X ∩ proj2_3 Y :=
  XBOOLE_1.th19 (th13 (XBOOLE_1.th17 (X := X) (Y := Y)))
    (th13 (by
      rw [XBOOLE_0.inter_comm X Y]
      exact XBOOLE_1.th17 (X := Y) (Y := X)))

/-- `XTUPLE_0:36` (triples). -/
theorem th36 (X Y : TarskiSet.{u}) : proj2_3 X \ proj2_3 Y ⊆ proj2_3 (X \ Y) := by
  intro x hx
  have ⟨hxX, hxY⟩ := (XBOOLE_0.def5 (proj2_3 X) (proj2_3 Y) x).mp hx
  obtain ⟨y, z, hp⟩ := th15 hxX
  have hn : triple y x z ∉ Y := fun hY => hxY (th15a hY)
  exact th15a ((XBOOLE_0.def5 X Y (triple y x z)).mpr ⟨hp, hn⟩)

theorem th37 (X Y : TarskiSet.{u}) : proj2_3 X ∆ proj2_3 Y ⊆ proj2_3 (X ∆ Y) :=
  of_symmdiff th34 th36

/-- `XTUPLE_0:38`. -/
theorem th38 (X Y : TarskiSet.{u}) : proj1_4 (X ∪ Y) = proj1_4 X ∪ proj1_4 Y :=
  (congrArg proj1 (th30 X Y)).trans (th22 (proj1_3 X) (proj1_3 Y))

theorem th39 (X Y : TarskiSet.{u}) : proj1_4 (X ∩ Y) ⊆ proj1_4 X ∩ proj1_4 Y :=
  XBOOLE_1.th19 (th17 (XBOOLE_1.th17 (X := X) (Y := Y)))
    (th17 (by
      rw [XBOOLE_0.inter_comm X Y]
      exact XBOOLE_1.th17 (X := Y) (Y := X)))

/-- Second `Th32` in the article (quadruples). -/
theorem th40 (X Y : TarskiSet.{u}) : proj1_4 X \ proj1_4 Y ⊆ proj1_4 (X \ Y) := by
  intro x hx
  have ⟨hxX, hxY⟩ := (XBOOLE_0.def5 (proj1_4 X) (proj1_4 Y) x).mp hx
  obtain ⟨x1, x2, x3, hp⟩ := th19 hxX
  have hn : quadruple x x1 x2 x3 ∉ Y := fun hY => hxY (th19a hY)
  exact th19a ((XBOOLE_0.def5 X Y (quadruple x x1 x2 x3)).mpr ⟨hp, hn⟩)

theorem th41 (X Y : TarskiSet.{u}) : proj1_4 X ∆ proj1_4 Y ⊆ proj1_4 (X ∆ Y) :=
  of_symmdiff th38 th40

/-- Second `Th34` in the article (quadruples). -/
theorem th42 (X Y : TarskiSet.{u}) : proj2_4 (X ∪ Y) = proj2_4 X ∪ proj2_4 Y :=
  (congrArg proj2 (th30 X Y)).trans (th26 (proj1_3 X) (proj1_3 Y))

theorem th43 (X Y : TarskiSet.{u}) : proj2_4 (X ∩ Y) ⊆ proj2_4 X ∩ proj2_4 Y :=
  XBOOLE_1.th19 (th18 (XBOOLE_1.th17 (X := X) (Y := Y)))
    (th18 (by
      rw [XBOOLE_0.inter_comm X Y]
      exact XBOOLE_1.th17 (X := Y) (Y := X)))

/-- Second `Th36` in the article (quadruples). -/
theorem th44 (X Y : TarskiSet.{u}) : proj2_4 X \ proj2_4 Y ⊆ proj2_4 (X \ Y) := by
  intro x hx
  have ⟨hxX, hxY⟩ := (XBOOLE_0.def5 (proj2_4 X) (proj2_4 Y) x).mp hx
  obtain ⟨x1, x2, x3, hp⟩ := th20 hxX
  have hn : quadruple x1 x x2 x3 ∉ Y := fun hY => hxY (th20a hY)
  exact th20a ((XBOOLE_0.def5 X Y (quadruple x1 x x2 x3)).mpr ⟨hp, hn⟩)

theorem th45 (X Y : TarskiSet.{u}) : proj2_4 X ∆ proj2_4 Y ⊆ proj2_4 (X ∆ Y) :=
  of_symmdiff th42 th44

end XTUPLE_0
