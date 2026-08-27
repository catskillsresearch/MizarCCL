import MizarCCL.SUBSET_1

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/setfam_1.miz`.
Authors: Beata Padlewska (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Families of Sets

1–1 Lean rendering of Mizar article `SETFAM_1`
(`vendor/mml/setfam_1.miz`). `meet X` is Separation on `union X`.
Pairwise `UNION` / `INTERSECTION` / `DIFFERENCE` are Separation on
a `bool` of unions as in the article. Import is `SUBSET_1` only.
-/

universe u

open TarskiSet TARSKI

namespace SETFAM_1

variable {X Y Z Z1 Z2 D x y SFX SFY SFZ F G P : TarskiSet.{u}}

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

/-! ## `meet X` (`SETFAM_1:def 1`) -/

noncomputable def meet (X : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (XBOOLE_0.sch_separation (union X) (fun x => ∀ Y, Y ∈ X → x ∈ Y))

theorem meet_sep (X : TarskiSet.{u}) :
    ∀ x, x ∈ meet X ↔ x ∈ union X ∧ ∀ Y, Y ∈ X → x ∈ Y :=
  Classical.choose_spec
    (XBOOLE_0.sch_separation (union X) (fun x => ∀ Y, Y ∈ X → x ∈ Y))


theorem def1_empty : meet (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) :=
  eq_of_mem fun x =>
    (meet_sep ∅ x).trans
      ⟨fun ⟨hxU, _⟩ => ((XBOOLE_0.empty_iff x).mp
          (ZFMISC_1.th2 ▸ hxU)).elim,
        fun hx => ((XBOOLE_0.empty_iff x).mp hx).elim⟩

theorem def1 {X x : TarskiSet.{u}} (hne : X ≠ (∅ : TarskiSet.{u})) :
    x ∈ meet X ↔ ∀ Y, Y ∈ X → x ∈ Y := by
  constructor
  · intro hx Y hY
    exact (meet_sep X x).mp hx |>.2 Y hY
  · intro hall
    obtain ⟨Y, hY⟩ := XBOOLE_0.th7 hne
    exact (meet_sep X x).mpr ⟨(union_iff X x).mpr ⟨Y, hall Y hY, hY⟩, hall⟩

/-- `SETFAM_1:1` -/
theorem th1 : meet (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) :=
  def1_empty

/-- `SETFAM_1:2` (`Th2`) -/
theorem th2 : meet X ⊆ union X :=
  fun x hx => (meet_sep X x).mp hx |>.1

/-- `SETFAM_1:3` (`Th3`) -/
theorem th3 (hZ : Z ∈ X) : meet X ⊆ Z :=
  fun x hx => (meet_sep X x).mp hx |>.2 Z hZ

/-- `SETFAM_1:4` -/
theorem th4 (h : (∅ : TarskiSet.{u}) ∈ X) : meet X = (∅ : TarskiSet.{u}) :=
  XBOOLE_1.th3 (th3 h)

/-- `SETFAM_1:5` -/
theorem th5 (hne : X ≠ (∅ : TarskiSet.{u}))
    (h : ∀ Z1, Z1 ∈ X → Z ⊆ Z1) : Z ⊆ meet X :=
  fun x hx => (def1 hne).mpr fun Y hY => h Y hY x hx

/-- `SETFAM_1:6` (`Th6`) -/
theorem th6 (hne : X ≠ (∅ : TarskiSet.{u})) (h : X ⊆ Y) : meet Y ⊆ meet X :=
  fun x hx => (def1 hne).mpr fun Z hZ =>
    (meet_sep Y x).mp hx |>.2 Z (h Z hZ)

/-- `SETFAM_1:7` -/
theorem th7 (hX : X ∈ Y) (hXZ : X ⊆ Z) : meet Y ⊆ Z :=
  XBOOLE_1.th1 (th3 hX) hXZ

/-- `SETFAM_1:8` -/
theorem th8 (hX : X ∈ Y) (hmiss : XBOOLE_0.misses X Z) :
    XBOOLE_0.misses (meet Y) Z :=
  XBOOLE_1.th63 (th3 hX) hmiss

/-- `SETFAM_1:9` -/
theorem th9 (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u})) :
    meet (X ∪ Y) = meet X ∩ meet Y := by
  have hXY : X ∪ Y ≠ (∅ : TarskiSet.{u}) :=
    fun h => hX (XBOOLE_1.th15 (X := X) (Y := Y) h)
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro x hx
    have hall := (def1 hXY).mp hx
    exact (XBOOLE_0.def4 (meet X) (meet Y) x).mpr
      ⟨(def1 hX).mpr fun Z hZ => hall Z ((XBOOLE_0.def3 X Y Z).mpr (Or.inl hZ)),
        (def1 hY).mpr fun Z hZ => hall Z ((XBOOLE_0.def3 X Y Z).mpr (Or.inr hZ))⟩
  · intro x hx
    have ⟨hxX, hxY⟩ := (XBOOLE_0.def4 (meet X) (meet Y) x).mp hx
    exact (def1 hXY).mpr fun Z hZ =>
      ((XBOOLE_0.def3 X Y Z).mp hZ).elim
        (fun hZ => (def1 hX).mp hxX Z hZ)
        (fun hZ => (def1 hY).mp hxY Z hZ)

/-- `SETFAM_1:10` -/
theorem th10 : meet (TARSKI.singleton x) = x := by
  have hne : TARSKI.singleton x ≠ (∅ : TarskiSet.{u}) :=
    fun h => XBOOLE_0.singleton_nonempty x (h ▸ XBOOLE_0.emptySet_isEmpty)
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · exact th3 ((singleton_iff x x).mpr rfl)
  · intro y hy
    exact (def1 hne).mpr fun Z hZ =>
      (singleton_iff x Z).mp hZ ▸ hy

/-- `SETFAM_1:11` -/
theorem th11 : meet (upair X Y) = X ∩ Y := by
  have hne : upair X Y ≠ (∅ : TarskiSet.{u}) :=
    fun h => XBOOLE_0.upair_nonempty X Y (h ▸ XBOOLE_0.emptySet_isEmpty)
  have hX : X ∈ upair X Y := (upair_iff X Y X).mpr (Or.inl rfl)
  have hY : Y ∈ upair X Y := (upair_iff X Y Y).mpr (Or.inr rfl)
  apply eq_of_mem
  intro z
  constructor
  · intro hz
    exact (XBOOLE_0.def4 X Y z).mpr
      ⟨(def1 hne).mp hz X hX, (def1 hne).mp hz Y hY⟩
  · intro hz
    have ⟨hzX, hzY⟩ := (XBOOLE_0.def4 X Y z).mp hz
    exact (def1 hne).mpr fun W hW =>
      ((upair_iff X Y W).mp hW).elim (fun h => h ▸ hzX) (fun h => h ▸ hzY)

/-! ## `is_finer_than` / `is_coarser_than` -/

def isFiner (SFX SFY : TarskiSet.{u}) : Prop :=
  ∀ X, X ∈ SFX → ∃ Y, Y ∈ SFY ∧ X ⊆ Y

def isCoarser (SFY SFX : TarskiSet.{u}) : Prop :=
  ∀ Y, Y ∈ SFY → ∃ X, X ∈ SFX ∧ X ⊆ Y

theorem isFiner_refl (SFX : TarskiSet.{u}) : isFiner SFX SFX :=
  fun X hX => ⟨X, hX, subset_refl X⟩

theorem isCoarser_refl (SFX : TarskiSet.{u}) : isCoarser SFX SFX :=
  fun Y hY => ⟨Y, hY, subset_refl Y⟩

/-- `SETFAM_1:12` -/
theorem th12 (h : SFX ⊆ SFY) : isFiner SFX SFY :=
  fun X hX => ⟨X, h X hX, subset_refl X⟩

/-- `SETFAM_1:13` -/
theorem th13 (h : isFiner SFX SFY) : union SFX ⊆ union SFY := by
  intro x hx
  obtain ⟨Y, hxY, hYS⟩ := (union_iff SFX x).mp hx
  obtain ⟨Z, hZ, hYZ⟩ := h Y hYS
  exact (union_iff SFY x).mpr ⟨Z, hYZ x hxY, hZ⟩

/-- `SETFAM_1:14` -/
theorem th14 (hne : SFY ≠ (∅ : TarskiSet.{u})) (h : isCoarser SFY SFX) :
    meet SFX ⊆ meet SFY :=
  fun x hx => (def1 hne).mpr fun Z hZ =>
    let ⟨Z1, hZ1, hsub⟩ := h Z hZ
    hsub x ((meet_sep SFX x).mp hx |>.2 Z1 hZ1)

/-- `SETFAM_1:15` -/
theorem th15 : isFiner (∅ : TarskiSet.{u}) SFX :=
  fun X hX => ((XBOOLE_0.empty_iff X).mp hX).elim

/-- `SETFAM_1:16` -/
theorem th16 (h : isFiner SFX (∅ : TarskiSet.{u})) :
    SFX = (∅ : TarskiSet.{u}) := by
  apply eq_of_mem
  intro W
  constructor
  · intro hW
    obtain ⟨Y, hY, _⟩ := h W hW
    exact ((XBOOLE_0.empty_iff Y).mp hY).elim
  · intro hW
    exact ((XBOOLE_0.empty_iff W).mp hW).elim

/-- `SETFAM_1:17` -/
theorem th17 (h1 : isFiner SFX SFY) (h2 : isFiner SFY SFZ) : isFiner SFX SFZ :=
  fun X hX =>
    let ⟨Y, hY, hXY⟩ := h1 X hX
    let ⟨Z, hZ, hYZ⟩ := h2 Y hY
    ⟨Z, hZ, XBOOLE_1.th1 hXY hYZ⟩

/-- `SETFAM_1:18` -/
theorem th18 (h : isFiner SFX (TARSKI.singleton Y)) :
    ∀ X, X ∈ SFX → X ⊆ Y :=
  fun X hX =>
    let ⟨Z, hZ, hXZ⟩ := h X hX
    (singleton_iff Y Z).mp hZ ▸ hXZ

/-- `SETFAM_1:19` -/
theorem th19 (h : isFiner SFX (upair X Y)) :
    ∀ Z, Z ∈ SFX → Z ⊆ X ∨ Z ⊆ Y :=
  fun Z hZ =>
    let ⟨W, hW, hZW⟩ := h Z hZ
    ((upair_iff X Y W).mp hW).elim
      (fun he => Or.inl (he ▸ hZW)) (fun he => Or.inr (he ▸ hZW))

/-! ## Pairwise family operations (`def 4`–`def 6`) -/

noncomputable def familyUnion (SFX SFY : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (XBOOLE_0.sch_separation (ZFMISC_1.bool (union SFX ∪ union SFY))
      (fun Z => ∃ X Y, X ∈ SFX ∧ Y ∈ SFY ∧ Z = X ∪ Y))

theorem familyUnion_sep (SFX SFY : TarskiSet.{u}) :
    ∀ Z, Z ∈ familyUnion SFX SFY ↔
      Z ∈ ZFMISC_1.bool (union SFX ∪ union SFY) ∧
        ∃ X Y, X ∈ SFX ∧ Y ∈ SFY ∧ Z = X ∪ Y :=
  Classical.choose_spec
    (XBOOLE_0.sch_separation (ZFMISC_1.bool (union SFX ∪ union SFY))
      (fun Z => ∃ X Y, X ∈ SFX ∧ Y ∈ SFY ∧ Z = X ∪ Y))

theorem def4 (SFX SFY Z : TarskiSet.{u}) :
    Z ∈ familyUnion SFX SFY ↔ ∃ X Y, X ∈ SFX ∧ Y ∈ SFY ∧ Z = X ∪ Y := by
  constructor
  · intro h
    exact (familyUnion_sep SFX SFY Z).mp h |>.2
  · intro ⟨X, Y, hX, hY, heq⟩
    have hsub : X ∪ Y ⊆ union SFX ∪ union SFY :=
      XBOOLE_1.th13 (ZFMISC_1.th74 hX) (ZFMISC_1.th74 hY)
    exact (familyUnion_sep SFX SFY Z).mpr
      ⟨(ZFMISC_1.def1 _ _).mpr (heq ▸ hsub), ⟨X, Y, hX, hY, heq⟩⟩

theorem familyUnion_comm (SFX SFY : TarskiSet.{u}) :
    familyUnion SFX SFY = familyUnion SFY SFX :=
  eq_of_mem fun Z =>
    (def4 SFX SFY Z).trans <|
      Iff.trans
        ⟨fun ⟨X, Y, hX, hY, heq⟩ =>
            ⟨Y, X, hY, hX, heq.trans (XBOOLE_0.union_comm X Y)⟩,
          fun ⟨Y, X, hY, hX, heq⟩ =>
            ⟨X, Y, hX, hY, heq.trans (XBOOLE_0.union_comm Y X)⟩⟩
        (def4 SFY SFX Z).symm

noncomputable def familyIntersection (SFX SFY : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (XBOOLE_0.sch_separation (ZFMISC_1.bool (union SFX ∩ union SFY))
      (fun Z => ∃ X Y, X ∈ SFX ∧ Y ∈ SFY ∧ Z = X ∩ Y))

theorem familyIntersection_sep (SFX SFY : TarskiSet.{u}) :
    ∀ Z, Z ∈ familyIntersection SFX SFY ↔
      Z ∈ ZFMISC_1.bool (union SFX ∩ union SFY) ∧
        ∃ X Y, X ∈ SFX ∧ Y ∈ SFY ∧ Z = X ∩ Y :=
  Classical.choose_spec
    (XBOOLE_0.sch_separation (ZFMISC_1.bool (union SFX ∩ union SFY))
      (fun Z => ∃ X Y, X ∈ SFX ∧ Y ∈ SFY ∧ Z = X ∩ Y))

theorem def5 (SFX SFY Z : TarskiSet.{u}) :
    Z ∈ familyIntersection SFX SFY ↔
      ∃ X Y, X ∈ SFX ∧ Y ∈ SFY ∧ Z = X ∩ Y := by
  constructor
  · intro h
    exact (familyIntersection_sep SFX SFY Z).mp h |>.2
  · intro ⟨X, Y, hX, hY, heq⟩
    have hsub : X ∩ Y ⊆ union SFX ∩ union SFY :=
      XBOOLE_1.th27 (ZFMISC_1.th74 hX) (ZFMISC_1.th74 hY)
    exact (familyIntersection_sep SFX SFY Z).mpr
      ⟨(ZFMISC_1.def1 _ _).mpr (heq ▸ hsub), ⟨X, Y, hX, hY, heq⟩⟩

theorem familyIntersection_comm (SFX SFY : TarskiSet.{u}) :
    familyIntersection SFX SFY = familyIntersection SFY SFX :=
  eq_of_mem fun Z =>
    (def5 SFX SFY Z).trans <|
      Iff.trans
        ⟨fun ⟨X, Y, hX, hY, heq⟩ =>
            ⟨Y, X, hY, hX, heq.trans (XBOOLE_0.inter_comm X Y)⟩,
          fun ⟨Y, X, hY, hX, heq⟩ =>
            ⟨X, Y, hX, hY, heq.trans (XBOOLE_0.inter_comm Y X)⟩⟩
        (def5 SFY SFX Z).symm

noncomputable def familyDifference (SFX SFY : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (XBOOLE_0.sch_separation (ZFMISC_1.bool (union SFX))
      (fun Z => ∃ X Y, X ∈ SFX ∧ Y ∈ SFY ∧ Z = X \ Y))

theorem familyDifference_sep (SFX SFY : TarskiSet.{u}) :
    ∀ Z, Z ∈ familyDifference SFX SFY ↔
      Z ∈ ZFMISC_1.bool (union SFX) ∧
        ∃ X Y, X ∈ SFX ∧ Y ∈ SFY ∧ Z = X \ Y :=
  Classical.choose_spec
    (XBOOLE_0.sch_separation (ZFMISC_1.bool (union SFX))
      (fun Z => ∃ X Y, X ∈ SFX ∧ Y ∈ SFY ∧ Z = X \ Y))

theorem def6 (SFX SFY Z : TarskiSet.{u}) :
    Z ∈ familyDifference SFX SFY ↔
      ∃ X Y, X ∈ SFX ∧ Y ∈ SFY ∧ Z = X \ Y := by
  constructor
  · intro h
    exact (familyDifference_sep SFX SFY Z).mp h |>.2
  · intro ⟨X, Y, hX, hY, heq⟩
    have hsub : X \ Y ⊆ union SFX :=
      XBOOLE_1.th1 XBOOLE_1.th36 (ZFMISC_1.th74 hX)
    exact (familyDifference_sep SFX SFY Z).mpr
      ⟨(ZFMISC_1.def1 _ _).mpr (heq ▸ hsub), ⟨X, Y, hX, hY, heq⟩⟩

/-- `SETFAM_1:20` -/
theorem th20 : isFiner SFX (familyUnion SFX SFX) :=
  fun X hX => ⟨X, (def4 SFX SFX X).mpr ⟨X, X, hX, hX, (XBOOLE_0.unionSet_idem X).symm⟩,
    subset_refl X⟩

/-- `SETFAM_1:21` -/
theorem th21 : isFiner (familyIntersection SFX SFX) SFX :=
  fun X hX =>
    let ⟨Z1, _, h1, _, heq⟩ := (def5 SFX SFX X).mp hX
    ⟨Z1, h1, heq ▸ XBOOLE_1.th17⟩

/-- `SETFAM_1:22` -/
theorem th22 : isFiner (familyDifference SFX SFX) SFX :=
  fun X hX =>
    let ⟨Z1, _, h1, _, heq⟩ := (def6 SFX SFX X).mp hX
    ⟨Z1, h1, heq ▸ XBOOLE_1.th36⟩

/-- `SETFAM_1:23` -/
theorem th23 (hmeet : XBOOLE_0.meets SFX SFY) :
    meet SFX ∩ meet SFY = meet (familyIntersection SFX SFY) := by
  have hne : SFX ∩ SFY ≠ (∅ : TarskiSet.{u}) := hmeet
  have hSFX : SFX ≠ (∅ : TarskiSet.{u}) :=
    fun h => hne (XBOOLE_1.th3 (h ▸ XBOOLE_1.th17 (X := SFX) (Y := SFY)))
  have hSFY : SFY ≠ (∅ : TarskiSet.{u}) :=
    fun h =>
      hne (XBOOLE_1.th3 (h ▸
        ((XBOOLE_0.inter_comm SFX SFY) ▸
          XBOOLE_1.th17 (X := SFY) (Y := SFX))))
  obtain ⟨y, hy⟩ := XBOOLE_0.th7 hne
  have hyX : y ∈ SFX := (XBOOLE_0.def4 SFX SFY y).mp hy |>.1
  have hyY : y ∈ SFY := (XBOOLE_0.def4 SFX SFY y).mp hy |>.2
  have hIne : familyIntersection SFX SFY ≠ (∅ : TarskiSet.{u}) :=
    fun h => (XBOOLE_0.empty_iff (y ∩ y)).mp
      (h ▸ (def5 SFX SFY (y ∩ y)).mpr ⟨y, y, hyX, hyY, rfl⟩)
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro x hx
    have ⟨hxX, hxY⟩ := (XBOOLE_0.def4 (meet SFX) (meet SFY) x).mp hx
    exact (def1 hIne).mpr fun Z hZ =>
      let ⟨Z1, Z2, h1, h2, heq⟩ := (def5 SFX SFY Z).mp hZ
      heq ▸ (XBOOLE_0.def4 Z1 Z2 x).mpr
        ⟨(def1 hSFX).mp hxX Z1 h1, (def1 hSFY).mp hxY Z2 h2⟩
  · intro x hx
    have hall := (def1 hIne).mp hx
    have hxY : x ∈ meet SFY :=
      (def1 hSFY).mpr fun Z hZ =>
        ((XBOOLE_0.def4 y Z x).mp
          (hall (y ∩ Z) ((def5 SFX SFY (y ∩ Z)).mpr ⟨y, Z, hyX, hZ, rfl⟩))).2
    have hxX : x ∈ meet SFX :=
      (def1 hSFX).mpr fun Z hZ =>
        ((XBOOLE_0.def4 Z y x).mp
          (hall (Z ∩ y) ((def5 SFX SFY (Z ∩ y)).mpr ⟨Z, y, hZ, hyY, rfl⟩))).1
    exact (XBOOLE_0.def4 (meet SFX) (meet SFY) x).mpr ⟨hxX, hxY⟩

/-- `SETFAM_1:24` -/
theorem th24 (hne : SFY ≠ (∅ : TarskiSet.{u})) :
    X ∪ meet SFY = meet (familyUnion (TARSKI.singleton X) SFY) := by
  obtain ⟨y, hy⟩ := XBOOLE_0.th7 hne
  have hX : X ∈ TARSKI.singleton X := (singleton_iff X X).mpr rfl
  have hUne : familyUnion (TARSKI.singleton X) SFY ≠ (∅ : TarskiSet.{u}) :=
    fun h => (XBOOLE_0.empty_iff (X ∪ y)).mp
      (h ▸ (def4 (TARSKI.singleton X) SFY (X ∪ y)).mpr ⟨X, y, hX, hy, rfl⟩)
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro x hx
    exact (def1 hUne).mpr fun Z hZ =>
      let ⟨Z1, Z2, h1, h2, heq⟩ := (def4 (TARSKI.singleton X) SFY Z).mp hZ
      have hZ1 : Z1 = X := (singleton_iff X Z1).mp h1
      heq ▸ (XBOOLE_0.def3 Z1 Z2 x).mpr
        (hZ1 ▸ ((XBOOLE_0.def3 X (meet SFY) x).mp hx).elim
          Or.inl fun hxM => Or.inr ((def1 hne).mp hxM Z2 h2))
  · intro x hx
    refine Classical.byContradiction fun hxU => ?_
    have hxX : x ∉ X :=
      fun h => hxU ((XBOOLE_0.def3 X (meet SFY) x).mpr (Or.inl h))
    have hxM : x ∉ meet SFY :=
      fun h => hxU ((XBOOLE_0.def3 X (meet SFY) x).mpr (Or.inr h))
    have ⟨Z, hZ, hxZ⟩ : ∃ Z, Z ∈ SFY ∧ x ∉ Z :=
      Classical.byContradiction fun h =>
        hxM ((def1 hne).mpr fun Z hZ =>
          Classical.byContradiction fun nZ => h ⟨Z, hZ, nZ⟩)
    have hxXZ : x ∈ X ∪ Z :=
      (def1 hUne).mp hx (X ∪ Z)
        ((def4 (TARSKI.singleton X) SFY (X ∪ Z)).mpr ⟨X, Z, hX, hZ, rfl⟩)
    exact ((XBOOLE_0.def3 X Z x).mp hxXZ).elim hxX hxZ

/-- `SETFAM_1:25` -/
theorem th25 :
    X ∩ union SFY = union (familyIntersection (TARSKI.singleton X) SFY) := by
  have hX : X ∈ TARSKI.singleton X := (singleton_iff X X).mpr rfl
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro x hx
    have ⟨hxX, hxU⟩ := (XBOOLE_0.def4 X (union SFY) x).mp hx
    obtain ⟨Z, hxZ, hZ⟩ := (union_iff SFY x).mp hxU
    exact (union_iff _ x).mpr
      ⟨X ∩ Z, (XBOOLE_0.def4 X Z x).mpr ⟨hxX, hxZ⟩,
        (def5 (TARSKI.singleton X) SFY (X ∩ Z)).mpr ⟨X, Z, hX, hZ, rfl⟩⟩
  · intro x hx
    obtain ⟨Z, hxZ, hZ⟩ := (union_iff _ x).mp hx
    obtain ⟨X1, X2, h1, h2, heq⟩ :=
      (def5 (TARSKI.singleton X) SFY Z).mp hZ
    have hX1 : X1 = X := (singleton_iff X X1).mp h1
    have ⟨hx1, hx2⟩ := (XBOOLE_0.def4 X1 X2 x).mp (heq ▸ hxZ)
    exact (XBOOLE_0.def4 X (union SFY) x).mpr
      ⟨hX1 ▸ hx1, (union_iff SFY x).mpr ⟨X2, hx2, h2⟩⟩

/-- `SETFAM_1:26` -/
theorem th26 (hne : SFY ≠ (∅ : TarskiSet.{u})) :
    X \ union SFY = meet (familyDifference (TARSKI.singleton X) SFY) := by
  obtain ⟨y, hy⟩ := XBOOLE_0.th7 hne
  have hX : X ∈ TARSKI.singleton X := (singleton_iff X X).mpr rfl
  have hDne : familyDifference (TARSKI.singleton X) SFY ≠ (∅ : TarskiSet.{u}) :=
    fun h => (XBOOLE_0.empty_iff (X \ y)).mp
      (h ▸ (def6 (TARSKI.singleton X) SFY (X \ y)).mpr ⟨X, y, hX, hy, rfl⟩)
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro x hx
    have ⟨hxX, hxU⟩ := (XBOOLE_0.def5 X (union SFY) x).mp hx
    exact (def1 hDne).mpr fun Z hZ =>
      let ⟨Z1, Z2, h1, h2, heq⟩ := (def6 (TARSKI.singleton X) SFY Z).mp hZ
      have hZ1 : Z1 = X := (singleton_iff X Z1).mp h1
      heq ▸ (XBOOLE_0.def5 Z1 Z2 x).mpr
        ⟨hZ1 ▸ hxX, fun hx2 => hxU ((union_iff SFY x).mpr ⟨Z2, hx2, h2⟩)⟩
  · intro x hx
    have hxXy : x ∈ X \ y :=
      (def1 hDne).mp hx (X \ y)
        ((def6 (TARSKI.singleton X) SFY (X \ y)).mpr ⟨X, y, hX, hy, rfl⟩)
    have hxX := (XBOOLE_0.def5 X y x).mp hxXy |>.1
    have hxU : x ∉ union SFY := fun hU =>
      let ⟨Z, hxZ, hZ⟩ := (union_iff SFY x).mp hU
      ((XBOOLE_0.def5 X Z x).mp
        ((def1 hDne).mp hx (X \ Z)
          ((def6 (TARSKI.singleton X) SFY (X \ Z)).mpr ⟨X, Z, hX, hZ, rfl⟩))).2 hxZ
    exact (XBOOLE_0.def5 X (union SFY) x).mpr ⟨hxX, hxU⟩

/-- `SETFAM_1:27` -/
theorem th27 (hne : SFY ≠ (∅ : TarskiSet.{u})) :
    X \ meet SFY = union (familyDifference (TARSKI.singleton X) SFY) := by
  have hX : X ∈ TARSKI.singleton X := (singleton_iff X X).mpr rfl
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro x hx
    have ⟨hxX, hxM⟩ := (XBOOLE_0.def5 X (meet SFY) x).mp hx
    have ⟨Z, hZ, hxZ⟩ : ∃ Z, Z ∈ SFY ∧ x ∉ Z :=
      Classical.byContradiction fun h =>
        hxM ((def1 hne).mpr fun Z hZ =>
          Classical.byContradiction fun nZ => h ⟨Z, hZ, nZ⟩)
    exact (union_iff _ x).mpr
      ⟨X \ Z, (XBOOLE_0.def5 X Z x).mpr ⟨hxX, hxZ⟩,
        (def6 (TARSKI.singleton X) SFY (X \ Z)).mpr ⟨X, Z, hX, hZ, rfl⟩⟩
  · intro x hx
    obtain ⟨Z, hxZ, hZ⟩ := (union_iff _ x).mp hx
    obtain ⟨Z1, Z2, h1, h2, heq⟩ := (def6 (TARSKI.singleton X) SFY Z).mp hZ
    have hZ1 : Z1 = X := (singleton_iff X Z1).mp h1
    have ⟨hx1, hx2⟩ := (XBOOLE_0.def5 Z1 Z2 x).mp (heq ▸ hxZ)
    exact (XBOOLE_0.def5 X (meet SFY) x).mpr
      ⟨hZ1 ▸ hx1, fun hxM => hx2 ((def1 hne).mp hxM Z2 h2)⟩

/-- `SETFAM_1:28` -/
theorem th28 :
    union (familyIntersection SFX SFY) = union SFX ∩ union SFY := by
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro x hx
    obtain ⟨Z, hxZ, hZ⟩ := (union_iff _ x).mp hx
    obtain ⟨A, B, hA, hB, heq⟩ := (def5 SFX SFY Z).mp hZ
    have ⟨hxA, hxB⟩ := (XBOOLE_0.def4 A B x).mp (heq ▸ hxZ)
    exact (XBOOLE_0.def4 (union SFX) (union SFY) x).mpr
      ⟨(union_iff SFX x).mpr ⟨A, hxA, hA⟩,
        (union_iff SFY x).mpr ⟨B, hxB, hB⟩⟩
  · intro x hx
    have ⟨hxX, hxY⟩ := (XBOOLE_0.def4 (union SFX) (union SFY) x).mp hx
    obtain ⟨A, hxA, hA⟩ := (union_iff SFX x).mp hxX
    obtain ⟨B, hxB, hB⟩ := (union_iff SFY x).mp hxY
    exact (union_iff _ x).mpr
      ⟨A ∩ B, (XBOOLE_0.def4 A B x).mpr ⟨hxA, hxB⟩,
        (def5 SFX SFY (A ∩ B)).mpr ⟨A, B, hA, hB, rfl⟩⟩

/-- `SETFAM_1:29` -/
theorem th29 (hX : SFX ≠ (∅ : TarskiSet.{u})) (hY : SFY ≠ (∅ : TarskiSet.{u})) :
    meet SFX ∪ meet SFY ⊆ meet (familyUnion SFX SFY) := by
  obtain ⟨y, hy⟩ := XBOOLE_0.th7 hX
  obtain ⟨z, hz⟩ := XBOOLE_0.th7 hY
  have hUne : familyUnion SFX SFY ≠ (∅ : TarskiSet.{u}) :=
    fun h => (XBOOLE_0.empty_iff (y ∪ z)).mp
      (h ▸ (def4 SFX SFY (y ∪ z)).mpr ⟨y, z, hy, hz, rfl⟩)
  intro x hx
  exact (def1 hUne).mpr fun Z hZ =>
    let ⟨A, B, hA, hB, heq⟩ := (def4 SFX SFY Z).mp hZ
    heq ▸ (XBOOLE_0.def3 A B x).mpr
      (((XBOOLE_0.def3 (meet SFX) (meet SFY) x).mp hx).elim
        (fun hxM => Or.inl ((def1 hX).mp hxM A hA))
        (fun hxM => Or.inr ((def1 hY).mp hxM B hB)))

/-- `SETFAM_1:30` -/
theorem th30 : meet (familyDifference SFX SFY) ⊆ meet SFX \ meet SFY := by
  by_cases hempty : SFX = (∅ : TarskiSet.{u}) ∨ SFY = (∅ : TarskiSet.{u})
  · have hD : familyDifference SFX SFY = (∅ : TarskiSet.{u}) := by
      apply eq_of_mem
      intro e
      constructor
      · intro he
        obtain ⟨A, B, hA, hB, _⟩ := (def6 SFX SFY e).mp he
        cases hempty with
        | inl h => exact ((XBOOLE_0.empty_iff A).mp (h ▸ hA)).elim
        | inr h => exact ((XBOOLE_0.empty_iff B).mp (h ▸ hB)).elim
      · intro he
        exact ((XBOOLE_0.empty_iff e).mp he).elim
    have : meet (familyDifference SFX SFY) = (∅ : TarskiSet.{u}) :=
      hD ▸ def1_empty
    exact this ▸ XBOOLE_1.th2
  · have hX : SFX ≠ (∅ : TarskiSet.{u}) := fun h => hempty (Or.inl h)
    have hY : SFY ≠ (∅ : TarskiSet.{u}) := fun h => hempty (Or.inr h)
    obtain ⟨z, hz⟩ := XBOOLE_0.th7 hX
    obtain ⟨y, hy⟩ := XBOOLE_0.th7 hY
    intro x hx
    have hxX : x ∈ meet SFX :=
      (def1 hX).mpr fun Z hZ =>
        ((XBOOLE_0.def5 Z y x).mp
          ((meet_sep (familyDifference SFX SFY) x).mp hx |>.2 (Z \ y)
            ((def6 SFX SFY (Z \ y)).mpr ⟨Z, y, hZ, hy, rfl⟩))).1
    have hxY : x ∉ meet SFY := fun hxM =>
      ((XBOOLE_0.def5 z y x).mp
        ((meet_sep (familyDifference SFX SFY) x).mp hx |>.2 (z \ y)
          ((def6 SFX SFY (z \ y)).mpr ⟨z, y, hz, hy, rfl⟩))).2
        ((def1 hY).mp hxM y hy)
    exact (XBOOLE_0.def5 (meet SFX) (meet SFY) x).mpr ⟨hxX, hxY⟩

/-! ## Subset-Family of D -/

def isSubsetFamily (F D : TarskiSet.{u}) : Prop := F ⊆ ZFMISC_1.bool D

theorem union_isSubset {D F : TarskiSet.{u}} (hF : isSubsetFamily F D) :
    SUBSET_1.isSubset (union F) D :=
  fun x hx =>
    let ⟨Z, hxZ, hZ⟩ := (union_iff F x).mp hx
    (ZFMISC_1.def1 D Z).mp (hF Z hZ) x hxZ

theorem meet_isSubset {D F : TarskiSet.{u}} (hF : isSubsetFamily F D) :
    SUBSET_1.isSubset (meet F) D :=
  XBOOLE_1.th1 th2 (union_isSubset hF)

/-- `SETFAM_1:31` (`Th31`) -/
theorem th31 (h : ∀ P, P ∈ F ↔ P ∈ G) : F = G :=
  eq_of_mem h

/-! ## `COMPLEMENT(F)` (`SETFAM_1:def 7`) -/

noncomputable def complement (D F : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose
    (SUBSET_1.sch_SubsetEx (ZFMISC_1.bool D)
      (fun P => SUBSET_1.compl D P ∈ F))

theorem complement_sep (D F : TarskiSet.{u}) :
    SUBSET_1.isSubset (complement D F) (ZFMISC_1.bool D) ∧
      ∀ P, P ∈ complement D F ↔
        P ∈ ZFMISC_1.bool D ∧ SUBSET_1.compl D P ∈ F :=
  Classical.choose_spec
    (SUBSET_1.sch_SubsetEx (ZFMISC_1.bool D)
      (fun P => SUBSET_1.compl D P ∈ F))

theorem complement_isSubsetFamily (D F : TarskiSet.{u}) :
    isSubsetFamily (complement D F) D :=
  (complement_sep D F).1

theorem def7 {D F P : TarskiSet.{u}} (hP : SUBSET_1.isSubset P D) :
    P ∈ complement D F ↔ SUBSET_1.compl D P ∈ F :=
  ((complement_sep D F).2 P).trans
    ⟨And.right, fun h => ⟨(ZFMISC_1.def1 D P).mpr hP, h⟩⟩

theorem complement_involutive {D F : TarskiSet.{u}}
    (hF : isSubsetFamily F D) : complement D (complement D F) = F := by
  apply eq_of_mem
  intro P
  constructor
  · intro hP
    have hPsub : SUBSET_1.isSubset P D :=
      (ZFMISC_1.def1 D P).mp (complement_isSubsetFamily D (complement D F) P hP)
    have hCmem : SUBSET_1.compl D P ∈ complement D F := (def7 hPsub).mp hP
    have hC : SUBSET_1.isSubset (SUBSET_1.compl D P) D :=
      SUBSET_1.compl_isSubset D P
    exact Eq.subst (motive := fun s => s ∈ F) (SUBSET_1.compl_involutive hPsub)
      ((def7 hC).mp hCmem)
  · intro hP
    have hPsub : SUBSET_1.isSubset P D := (ZFMISC_1.def1 D P).mp (hF P hP)
    have hC : SUBSET_1.isSubset (SUBSET_1.compl D P) D :=
      SUBSET_1.compl_isSubset D P
    exact (def7 hPsub).mpr
      ((def7 hC).mpr (Eq.subst (motive := fun s => s ∈ F)
        (SUBSET_1.compl_involutive hPsub).symm hP))

/-- `SETFAM_1:32` (`Th32`) -/
theorem th32 {D F : TarskiSet.{u}} (hF : isSubsetFamily F D)
    (hne : F ≠ (∅ : TarskiSet.{u})) :
    complement D F ≠ (∅ : TarskiSet.{u}) := by
  obtain ⟨X, hX⟩ := XBOOLE_0.th7 hne
  have hXsub : SUBSET_1.isSubset X D := (ZFMISC_1.def1 D X).mp (hF X hX)
  have hC : SUBSET_1.isSubset (SUBSET_1.compl D X) D :=
    SUBSET_1.compl_isSubset D X
  intro he
  have hmem : SUBSET_1.compl D X ∈ complement D F :=
    (def7 hC).mpr (Eq.subst (motive := fun s => s ∈ F)
      (SUBSET_1.compl_involutive hXsub).symm hX)
  exact (XBOOLE_0.empty_iff (SUBSET_1.compl D X)).mp
    (Eq.subst (motive := fun s => SUBSET_1.compl D X ∈ s) he hmem)

/-- `SETFAM_1:33` -/
theorem th33 {D F : TarskiSet.{u}} (hF : isSubsetFamily F D)
    (hne : F ≠ (∅ : TarskiSet.{u})) :
    SUBSET_1.hash D \ union F = meet (complement D F) := by
  have hCne := th32 hF hne
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro x hx
    have ⟨hxD, hxU⟩ := (XBOOLE_0.def5 D (union F) x).mp hx
    exact (def1 hCne).mpr fun Y hY => by
      have hYsub : SUBSET_1.isSubset Y D :=
        (ZFMISC_1.def1 D Y).mp (complement_isSubsetFamily D F Y hY)
      have hY' : SUBSET_1.compl D Y ∈ F := (def7 hYsub).mp hY
      have hxY' : x ∉ SUBSET_1.compl D Y :=
        fun h => hxU ((union_iff F x).mpr ⟨SUBSET_1.compl D Y, h, hY'⟩)
      by_cases hxY : x ∈ Y
      · exact hxY
      · exact (hxY' ((XBOOLE_0.def5 D Y x).mpr ⟨hxD, hxY⟩)).elim
  · intro x hx
    have hall := (def1 hCne).mp hx
    have hxD : x ∈ D := meet_isSubset (complement_isSubsetFamily D F) x hx
    have hxU : x ∉ union F := fun hU =>
      let ⟨Y, hxY, hY⟩ := (union_iff F x).mp hU
      have hYsub : SUBSET_1.isSubset Y D := (ZFMISC_1.def1 D Y).mp (hF Y hY)
      have hCmem : SUBSET_1.compl D Y ∈ complement D F :=
        (def7 (SUBSET_1.compl_isSubset D Y)).mpr
          (Eq.subst (motive := fun s => s ∈ F)
            (SUBSET_1.compl_involutive hYsub).symm hY)
      ((XBOOLE_0.def5 D Y x).mp (hall _ hCmem)).2 hxY
    exact (XBOOLE_0.def5 D (union F) x).mpr ⟨hxD, hxU⟩

/-- `SETFAM_1:34` -/
theorem th34 {D F : TarskiSet.{u}} (hF : isSubsetFamily F D)
    (hne : F ≠ (∅ : TarskiSet.{u})) :
    union (complement D F) = SUBSET_1.hash D \ meet F := by
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro x hx
    obtain ⟨Y, hxY, hY⟩ := (union_iff _ x).mp hx
    have hYsub : SUBSET_1.isSubset Y D :=
      (ZFMISC_1.def1 D Y).mp (complement_isSubsetFamily D F Y hY)
    have hY' : SUBSET_1.compl D Y ∈ F := (def7 hYsub).mp hY
    have hxD : x ∈ D := hYsub x hxY
    have hxY' : x ∉ SUBSET_1.compl D Y :=
      fun h => ((XBOOLE_0.def5 D Y x).mp h).2 hxY
    have hxM : x ∉ meet F := fun hmeet =>
      hxY' ((def1 hne).mp hmeet _ hY')
    exact (XBOOLE_0.def5 D (meet F) x).mpr ⟨hxD, hxM⟩
  · intro x hx
    have ⟨hxD, hxM⟩ := (XBOOLE_0.def5 D (meet F) x).mp hx
    obtain ⟨Y, hY, hxY⟩ : ∃ Y, Y ∈ F ∧ x ∉ Y :=
      Classical.byContradiction fun h =>
        hxM ((def1 hne).mpr fun Y hY =>
          Classical.byContradiction fun nY => h ⟨Y, hY, nY⟩)
    have hYsub : SUBSET_1.isSubset Y D := (ZFMISC_1.def1 D Y).mp (hF Y hY)
    have hC : SUBSET_1.isSubset (SUBSET_1.compl D Y) D :=
      SUBSET_1.compl_isSubset D Y
    exact (union_iff _ x).mpr
      ⟨SUBSET_1.compl D Y,
        (XBOOLE_0.def5 D Y x).mpr ⟨hxD, hxY⟩,
        (def7 hC).mpr (Eq.subst (motive := fun s => s ∈ F)
          (SUBSET_1.compl_involutive hYsub).symm hY)⟩

/-- `SETFAM_1:35` -/
theorem th35 {D F P : TarskiSet.{u}} (_hF : isSubsetFamily F D)
    (hP : SUBSET_1.isSubset P D) :
    SUBSET_1.compl D P ∈ complement D F ↔ P ∈ F :=
  (def7 (SUBSET_1.compl_isSubset D P)).trans
    (Iff.of_eq (congrArg (fun s => s ∈ F) (SUBSET_1.compl_involutive hP)))

/-- `SETFAM_1:36` (`Th36`) -/
theorem th36 {D F G : TarskiSet.{u}} (hF : isSubsetFamily F D)
    (_hG : isSubsetFamily G D) (h : complement D F ⊆ complement D G) : F ⊆ G := by
  intro x hx
  have hxsub : SUBSET_1.isSubset x D := (ZFMISC_1.def1 D x).mp (hF x hx)
  have hxcc : x ∈ complement D (complement D F) :=
    Eq.subst (motive := fun s => x ∈ s) (complement_involutive hF).symm hx
  have hx' : SUBSET_1.compl D x ∈ complement D F := (def7 hxsub).mp hxcc
  have hx'G : SUBSET_1.compl D x ∈ complement D G := h _ hx'
  exact Eq.subst (motive := fun s => s ∈ G) (SUBSET_1.compl_involutive hxsub)
    ((def7 (SUBSET_1.compl_isSubset D x)).mp hx'G)

/-- `SETFAM_1:37` -/
theorem th37 {D F G : TarskiSet.{u}} (hF : isSubsetFamily F D)
    (hG : isSubsetFamily G D) :
    complement D F ⊆ G ↔ F ⊆ complement D G :=
  ⟨fun h => th36 hF (complement_isSubsetFamily D G)
      (Eq.subst (motive := fun s => complement D F ⊆ s)
        (complement_involutive hG).symm h),
    fun h => th36 (complement_isSubsetFamily D F) hG
      (Eq.subst (motive := fun s => s ⊆ complement D G)
        (complement_involutive hF).symm h)⟩

/-- `SETFAM_1:38` -/
theorem th38 {D F G : TarskiSet.{u}} (hF : isSubsetFamily F D)
    (hG : isSubsetFamily G D) (h : complement D F = complement D G) : F = G :=
  (complement_involutive hF).symm.trans
    ((congrArg (complement D) h).trans (complement_involutive hG))

/-- `SETFAM_1:39` -/
theorem th39 {D F G : TarskiSet.{u}} (_hF : isSubsetFamily F D)
    (_hG : isSubsetFamily G D) :
    complement D (F ∪ G) = complement D F ∪ complement D G := by
  apply th31
  intro P
  by_cases hP : SUBSET_1.isSubset P D
  · constructor
    · intro hPG
      have hP' := (def7 hP).mp hPG
      exact (XBOOLE_0.def3 (complement D F) (complement D G) P).mpr
        (((XBOOLE_0.def3 F G (SUBSET_1.compl D P)).mp hP').elim
          (fun h => Or.inl ((def7 hP).mpr h))
          (fun h => Or.inr ((def7 hP).mpr h)))
    · intro hPG
      apply (def7 hP).mpr
      exact ((XBOOLE_0.def3 (complement D F) (complement D G) P).mp hPG).elim
        (fun h => (XBOOLE_0.def3 F G _).mpr (Or.inl ((def7 hP).mp h)))
        (fun h => (XBOOLE_0.def3 F G _).mpr (Or.inr ((def7 hP).mp h)))
  · constructor
    · intro hPG
      exact (hP ((ZFMISC_1.def1 D P).mp
        (complement_isSubsetFamily D (F ∪ G) P hPG))).elim
    · intro hPG
      exact ((XBOOLE_0.def3 (complement D F) (complement D G) P).mp hPG).elim
        (fun h => (hP ((ZFMISC_1.def1 D P).mp
          (complement_isSubsetFamily D F P h))).elim)
        (fun h => (hP ((ZFMISC_1.def1 D P).mp
          (complement_isSubsetFamily D G P h))).elim)

private theorem diff_self_eq (X : TarskiSet.{u}) :
    X \ X = (∅ : TarskiSet.{u}) :=
  (XBOOLE_1.th37 (X := X) (Y := X)).mpr (subset_refl X)

private theorem diff_empty_eq (X : TarskiSet.{u}) :
    X \ (∅ : TarskiSet.{u}) = X :=
  eq_of_mem fun x =>
    (XBOOLE_0.def5 X ∅ x).trans
      ⟨And.left, fun hx => ⟨hx, fun h => (XBOOLE_0.empty_iff x).mp h⟩⟩

/-- `SETFAM_1:40` -/
theorem th40 {D F : TarskiSet.{u}} (_hF : isSubsetFamily F D)
    (h : F = TARSKI.singleton D) :
    complement D F = TARSKI.singleton (∅ : TarskiSet.{u}) := by
  have hG : isSubsetFamily (TARSKI.singleton (∅ : TarskiSet.{u})) D :=
    (ZFMISC_1.th31 (x := (∅ : TarskiSet.{u})) (X := ZFMISC_1.bool D)).mpr
      ((ZFMISC_1.def1 D ∅).mpr XBOOLE_1.th2)
  apply th31
  intro P
  by_cases hP : SUBSET_1.isSubset P D
  · constructor
    · intro hPG
      have hPF : SUBSET_1.compl D P ∈ F := (def7 hP).mp hPG
      have hPD : SUBSET_1.compl D P = D :=
        (singleton_iff D (SUBSET_1.compl D P)).mp (h ▸ hPF)
      have hcc : SUBSET_1.compl D (SUBSET_1.compl D P) = (∅ : TarskiSet.{u}) :=
        Eq.subst (motive := fun s => SUBSET_1.compl D s = (∅ : TarskiSet.{u}))
          hPD.symm (diff_self_eq D)
      have hP0 : P = (∅ : TarskiSet.{u}) :=
        (SUBSET_1.compl_involutive hP).symm.trans hcc
      exact (singleton_iff (∅ : TarskiSet.{u}) P).mpr hP0
    · intro hPG
      have hP0 : P = (∅ : TarskiSet.{u}) :=
        (singleton_iff (∅ : TarskiSet.{u}) P).mp hPG
      have : SUBSET_1.compl D P = D :=
        Eq.subst (motive := fun s => SUBSET_1.compl D s = D) hP0.symm
          (diff_empty_eq D)
      exact (def7 hP).mpr (Eq.subst (motive := fun s => SUBSET_1.compl D P ∈ s)
        h.symm ((singleton_iff D (SUBSET_1.compl D P)).mpr this))
  · constructor
    · intro hPG
      exact (hP ((ZFMISC_1.def1 D P).mp
        (complement_isSubsetFamily D F P hPG))).elim
    · intro hPG
      exact (hP ((ZFMISC_1.def1 D P).mp (hG P hPG))).elim

theorem complement_empty {D F : TarskiSet.{u}} (_hF : isSubsetFamily F D)
    (hE : XBOOLE_0.isEmpty F) : XBOOLE_0.isEmpty (complement D F) :=
  fun ⟨P, hP⟩ =>
    hE ⟨SUBSET_1.compl D P,
      (def7 ((ZFMISC_1.def1 D P).mp
        (complement_isSubsetFamily D F P hP))).mp hP⟩

/-! ## Attributes and addenda -/

def withNonemptyElements (IT : TarskiSet.{u}) : Prop :=
  (∅ : TarskiSet.{u}) ∉ IT

theorem def8 (IT : TarskiSet.{u}) :
    withNonemptyElements IT ↔ (∅ : TarskiSet.{u}) ∉ IT := Iff.rfl

theorem singleton_withNonempty {A : TarskiSet.{u}}
    (hA : ¬ XBOOLE_0.isEmpty A) : withNonemptyElements (TARSKI.singleton A) :=
  fun h => hA ((singleton_iff A ∅).mp h ▸ XBOOLE_0.emptySet_isEmpty)

theorem union_withNonempty {A B : TarskiSet.{u}}
    (hA : withNonemptyElements A) (hB : withNonemptyElements B) :
    withNonemptyElements (A ∪ B) :=
  fun h => ((XBOOLE_0.def3 A B ∅).mp h).elim hA hB

/-- `SETFAM_1:41` -/
theorem th41 (hU : union Y ⊆ Z) (hX : X ∈ Y) : X ⊆ Z :=
  fun x hx => hU x ((union_iff Y x).mpr ⟨X, hx, hX⟩)

/-- `SETFAM_1:42` -/
theorem th42 (hX : X ⊆ union (A ∪ B))
    (hmiss : ∀ Y, Y ∈ B → XBOOLE_0.misses Y X) : X ⊆ union A := by
  intro x hx
  have hxU : x ∈ union (A ∪ B) := hX x hx
  obtain ⟨Y, hxY, hY⟩ := (union_iff (A ∪ B) x).mp hxU
  rcases (XBOOLE_0.def3 A B Y).mp hY with hA | hB
  · exact (union_iff A x).mpr ⟨Y, hxY, hA⟩
  · exact ((XBOOLE_0.empty_iff x).mp
      (hmiss Y hB ▸ (XBOOLE_0.def4 Y X x).mpr ⟨hxY, hx⟩)).elim

noncomputable def Intersect (M B : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose <|
    show ∃ Z, (B ≠ (∅ : TarskiSet.{u}) → Z = meet B) ∧
        (B = (∅ : TarskiSet.{u}) → Z = M) from by
      by_cases h : B = (∅ : TarskiSet.{u})
      · exact ⟨M, fun hne => (hne h).elim, fun _ => rfl⟩
      · exact ⟨meet B, fun _ => rfl, fun he => (h he).elim⟩

theorem Intersect_spec (M B : TarskiSet.{u}) :
    (B ≠ (∅ : TarskiSet.{u}) → Intersect M B = meet B) ∧
      (B = (∅ : TarskiSet.{u}) → Intersect M B = M) :=
  Classical.choose_spec <|
    show ∃ Z, (B ≠ (∅ : TarskiSet.{u}) → Z = meet B) ∧
        (B = (∅ : TarskiSet.{u}) → Z = M) from by
      by_cases h : B = (∅ : TarskiSet.{u})
      · exact ⟨M, fun hne => (hne h).elim, fun _ => rfl⟩
      · exact ⟨meet B, fun _ => rfl, fun he => (h he).elim⟩

theorem def9 {M B : TarskiSet.{u}} (hne : B ≠ (∅ : TarskiSet.{u})) :
    Intersect M B = meet B :=
  (Intersect_spec M B).1 hne

theorem def9_empty (M : TarskiSet.{u}) :
    Intersect M (∅ : TarskiSet.{u}) = M :=
  (Intersect_spec M ∅).2 rfl

/-- `SETFAM_1:43` (`Th43`) -/
theorem th43 {X x R : TarskiSet.{u}} (_hR : isSubsetFamily R X) (hx : x ∈ X) :
    x ∈ Intersect X R ↔ ∀ Y, Y ∈ R → x ∈ Y := by
  constructor
  · intro hY Y hYR
    have hne : R ≠ (∅ : TarskiSet.{u}) :=
      fun h => (XBOOLE_0.empty_iff Y).mp (h ▸ hYR)
    exact (def1 hne).mp
      (Eq.subst (motive := fun s => x ∈ s) (def9 (M := X) hne) hY) Y hYR
  · intro hall
    by_cases hR0 : R = (∅ : TarskiSet.{u})
    · exact Eq.subst (motive := fun s => x ∈ Intersect X s) hR0.symm
        (Eq.subst (motive := fun s => x ∈ s) (def9_empty X).symm hx)
    · exact Eq.subst (motive := fun s => x ∈ s) (def9 (M := X) hR0).symm
        ((def1 hR0).mpr hall)

/-- `SETFAM_1:44` -/
theorem th44 {X H J : TarskiSet.{u}} (hH : isSubsetFamily H X)
    (hJ : isSubsetFamily J X) (h : H ⊆ J) :
    Intersect X J ⊆ Intersect X H := by
  intro x hx
  have hxX : x ∈ X := by
    by_cases hJ0 : J = (∅ : TarskiSet.{u})
    · exact Eq.subst (motive := fun s => x ∈ s) (hJ0 ▸ def9_empty X) hx
    · exact meet_isSubset hJ x
        (Eq.subst (motive := fun s => x ∈ s) (def9 (M := X) hJ0) hx)
  exact (th43 hH hxX).mpr fun Y hY => (th43 hJ hxX).mp hx Y (h Y hY)

def isEmptyMembered (E : TarskiSet.{u}) : Prop :=
  ¬ ∃ x, ¬ XBOOLE_0.isEmpty x ∧ x ∈ E

theorem def10 (E : TarskiSet.{u}) :
    isEmptyMembered E ↔ ¬ ∃ x, ¬ XBOOLE_0.isEmpty x ∧ x ∈ E := Iff.rfl

def withNonemptyElement (E : TarskiSet.{u}) : Prop := ¬ isEmptyMembered E

theorem withNonemptyElement_exists {E : TarskiSet.{u}}
    (h : withNonemptyElement E) : ∃ x, ¬ XBOOLE_0.isEmpty x ∧ x ∈ E :=
  Classical.not_not.mp h

def isCover (F X : TarskiSet.{u}) : Prop := X ⊆ union F

theorem def11 (F X : TarskiSet.{u}) : isCover F X ↔ X ⊆ union F := Iff.rfl

/-- `SETFAM_1:45` -/
theorem th45 {X F : TarskiSet.{u}} (hF : isSubsetFamily F X) :
    isCover F X ↔ union F = X :=
  ⟨fun h => XBOOLE_0.eq_iff_subset.mpr ⟨union_isSubset hF, h⟩,
    fun h => h.symm ▸ subset_refl (union F)⟩

/-- `SETFAM_1:46` (`Th46`) -/
theorem th46 : isSubsetFamily (TARSKI.singleton (∅ : TarskiSet.{u})) X :=
  (ZFMISC_1.th31 (x := (∅ : TarskiSet.{u})) (X := ZFMISC_1.bool X)).mpr
    ((ZFMISC_1.def1 X ∅).mpr XBOOLE_1.th2)

def withProperSubsets (F X : TarskiSet.{u}) : Prop := X ∉ F

theorem def12 (F X : TarskiSet.{u}) : withProperSubsets F X ↔ X ∉ F := Iff.rfl

/-- `SETFAM_1:47` -/
theorem th47 {TS F G : TarskiSet.{u}} (hF : withProperSubsets F TS)
    (hG : G ⊆ F) : withProperSubsets G TS :=
  fun h => hF (hG TS h)

/-- `SETFAM_1:48` -/
theorem th48 {TS A B : TarskiSet.{u}} (hA : withProperSubsets A TS)
    (hB : withProperSubsets B TS) : withProperSubsets (A ∪ B) TS :=
  fun h => ((XBOOLE_0.def3 A B TS).mp h).elim hA hB

theorem bool_isSubsetFamily (X : TarskiSet.{u}) :
    isSubsetFamily (ZFMISC_1.bool X) X :=
  subset_refl (ZFMISC_1.bool X)

/-- `SETFAM_1:49` -/
theorem th49 {A b : TarskiSet.{u}} (hA : ¬ XBOOLE_0.isEmpty A)
    (hne : A ≠ TARSKI.singleton b) :
    ∃ a, SUBSET_1.isElement a A ∧ a ≠ b := by
  refine Classical.byContradiction fun h => ?_
  have hall : ∀ a, SUBSET_1.isElement a A → a = b :=
    fun a ha => Classical.byContradiction fun hne => h ⟨a, ha, hne⟩
  apply hne
  apply eq_of_mem
  intro a
  constructor
  · intro ha
    exact (singleton_iff b a).mpr (hall a (SUBSET_1.isElement_of ha))
  · intro ha
    have hab : a = b := (singleton_iff b a).mp ha
    obtain ⟨a0, ha0⟩ := Classical.not_not.mp hA
    have ha0b : a0 = b := hall a0 (SUBSET_1.isElement_of ha0)
    exact Eq.subst (motive := fun s => s ∈ A) hab.symm
      (Eq.subst (motive := fun s => s ∈ A) ha0b ha0)

end SETFAM_1
