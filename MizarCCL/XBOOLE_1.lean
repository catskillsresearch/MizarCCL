import MizarCCL.XBOOLE_0

/-
Copyright (c) 2002-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/xboole_1.miz`.
Authors: Library Committee (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Boolean properties of sets — theorems

1–1 Lean rendering of Mizar article `XBOOLE_1`
(`vendor/mml/xboole_1.miz`, Mizar 7.13.01 / MML 4.181.1147).

Environ imports `TARSKI` and `XBOOLE_0`. Proofs follow the Mizar
article: membership via `def 3`–`def 5`, inclusion via `TARSKI:def 3`,
extensionality via `TARSKI:1`. No Mathlib.
-/

universe u

open TarskiSet TARSKI XBOOLE_0

namespace XBOOLE_1

variable {X Y Z V A B X9 Y9 : TarskiSet.{u}}

/-! ## Inclusion and union -/

/-- `XBOOLE_1:1` (`Th1`, Modus Barbara). -/
theorem th1 (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z :=
  fun x hx => hYZ x (hXY x hx)

/-- `XBOOLE_1:2` (`Th2`). -/
theorem th2 : (∅ : TarskiSet.{u}) ⊆ X :=
  fun x hx => (empty_iff x).mp hx |>.elim

/-- `XBOOLE_1:3` (`Th3`). -/
theorem th3 (h : X ⊆ (∅ : TarskiSet.{u})) : X = (∅ : TarskiSet.{u}) :=
  def10.mpr ⟨h, th2⟩

/-- `XBOOLE_1:4` (`Th4`). -/
theorem th4 : (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) := by
  apply extensionality
  intro x
  constructor
  · intro hx
    rcases (def3 (X ∪ Y) Z x).mp hx with hXY | hZ
    · rcases (def3 X Y x).mp hXY with hX | hY
      · exact (def3 X (Y ∪ Z) x).mpr (Or.inl hX)
      · exact (def3 X (Y ∪ Z) x).mpr (Or.inr ((def3 Y Z x).mpr (Or.inl hY)))
    · exact (def3 X (Y ∪ Z) x).mpr (Or.inr ((def3 Y Z x).mpr (Or.inr hZ)))
  · intro hx
    rcases (def3 X (Y ∪ Z) x).mp hx with hX | hYZ
    · exact (def3 (X ∪ Y) Z x).mpr (Or.inl ((def3 X Y x).mpr (Or.inl hX)))
    · rcases (def3 Y Z x).mp hYZ with hY | hZ
      · exact (def3 (X ∪ Y) Z x).mpr (Or.inl ((def3 X Y x).mpr (Or.inr hY)))
      · exact (def3 (X ∪ Y) Z x).mpr (Or.inr hZ)

/-- `XBOOLE_1:5` -/
theorem th5 : (X ∪ Y) ∪ Z = (X ∪ Z) ∪ (Y ∪ Z) := by
  calc
    (X ∪ Y) ∪ Z = X ∪ ((Z ∪ Z) ∪ Y) := by
      rw [union_idem Z, union_comm Z Y, th4]
    _ = X ∪ (Z ∪ (Z ∪ Y)) := by rw [th4]
    _ = (X ∪ Z) ∪ (Y ∪ Z) := by
      rw [show Z ∪ Y = Y ∪ Z from union_comm Z Y, th4]

/-- `XBOOLE_1:6` -/
theorem th6 : X ∪ (X ∪ Y) = X ∪ Y := by
  rw [← th4, union_idem X]

/-- `XBOOLE_1:7` (`Th7`). -/
theorem th7 : X ⊆ X ∪ Y :=
  fun x hx => (def3 X Y x).mpr (Or.inl hx)

/-- `XBOOLE_1:8` (`Th8`). -/
theorem th8 (hX : X ⊆ Z) (hY : Y ⊆ Z) : X ∪ Y ⊆ Z := by
  intro x hx
  rcases (def3 X Y x).mp hx with h | h
  · exact hX x h
  · exact hY x h

/-- `XBOOLE_1:9` -/
theorem th9 (h : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z := by
  intro x hx
  rcases (def3 X Z x).mp hx with hX | hZ
  · exact (def3 Y Z x).mpr (Or.inl (h x hX))
  · exact (def3 Y Z x).mpr (Or.inr hZ)

/-- `XBOOLE_1:10` -/
theorem th10 (h : X ⊆ Y) : X ⊆ Z ∪ Y :=
  th1 h (show Y ⊆ Z ∪ Y from by
    rw [union_comm Z Y]; exact th7)

/-- `XBOOLE_1:11` -/
theorem th11 (h : X ∪ Y ⊆ Z) : X ⊆ Z :=
  th1 th7 h

/-- `XBOOLE_1:12` (`Th12`). -/
theorem th12 (h : X ⊆ Y) : X ∪ Y = Y := by
  apply def10.mpr
  constructor
  · exact th8 h (subset_refl Y)
  · intro x hx
    exact (def3 X Y x).mpr (Or.inr hx)

/-- `XBOOLE_1:13` -/
theorem th13 (hXY : X ⊆ Y) (hZV : Z ⊆ V) : X ∪ Z ⊆ Y ∪ V := by
  intro x hx
  rcases (def3 X Z x).mp hx with hX | hZ
  · exact (def3 Y V x).mpr (Or.inl (hXY x hX))
  · exact (def3 Y V x).mpr (Or.inr (hZV x hZ))

/-- `XBOOLE_1:14` -/
theorem th14 (hYX : Y ⊆ X) (hZX : Z ⊆ X)
    (hleast : ∀ V, Y ⊆ V → Z ⊆ V → X ⊆ V) : X = Y ∪ Z :=
  def10.mpr ⟨hleast (Y ∪ Z) (th7) (by rw [union_comm]; exact th7),
    th8 hYX hZX⟩

/-- `XBOOLE_1:15` -/
theorem th15 (h : X ∪ Y = (∅ : TarskiSet.{u})) : X = (∅ : TarskiSet.{u}) :=
  th3 (fun x hx => (empty_iff x).mp (h ▸ (def3 X Y x).mpr (Or.inl hx)) |>.elim)

/-! ## Intersection -/

/-- `XBOOLE_1:16` (`Th16`). -/
theorem th16 : (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) := by
  apply extensionality
  intro x
  constructor
  · intro hx
    have ⟨hXY, hZ⟩ := (def4 (X ∩ Y) Z x).mp hx
    have ⟨hX, hY⟩ := (def4 X Y x).mp hXY
    exact (def4 X (Y ∩ Z) x).mpr ⟨hX, (def4 Y Z x).mpr ⟨hY, hZ⟩⟩
  · intro hx
    have ⟨hX, hYZ⟩ := (def4 X (Y ∩ Z) x).mp hx
    have ⟨hY, hZ⟩ := (def4 Y Z x).mp hYZ
    exact (def4 (X ∩ Y) Z x).mpr ⟨(def4 X Y x).mpr ⟨hX, hY⟩, hZ⟩

/-- `XBOOLE_1:17` (`Th17`). -/
theorem th17 : X ∩ Y ⊆ X :=
  fun x hx => ((def4 X Y x).mp hx).1

/-- `XBOOLE_1:18` -/
theorem th18 (h : X ⊆ Y ∩ Z) : X ⊆ Y :=
  th1 h th17

/-- `XBOOLE_1:19` (`Th19`). -/
theorem th19 (hZX : Z ⊆ X) (hZY : Z ⊆ Y) : Z ⊆ X ∩ Y :=
  fun x hx => (def4 X Y x).mpr ⟨hZX x hx, hZY x hx⟩

/-- `XBOOLE_1:20` -/
theorem th20 (hXY : X ⊆ Y) (hXZ : X ⊆ Z)
    (hgreat : ∀ V, V ⊆ Y → V ⊆ Z → V ⊆ X) : X = Y ∩ Z :=
  def10.mpr ⟨th19 hXY hXZ, hgreat (Y ∩ Z) th17 (by
    rw [inter_comm Y Z]; exact th17)⟩

/-- `XBOOLE_1:21` -/
theorem th21 : X ∩ (X ∪ Y) = X := by
  apply def10.mpr
  constructor
  · exact th17
  · intro x hx
    exact (def4 X (X ∪ Y) x).mpr ⟨hx, (def3 X Y x).mpr (Or.inl hx)⟩

/-- `XBOOLE_1:22` (`Th22`). -/
theorem th22 : X ∪ (X ∩ Y) = X := by
  apply def10.mpr
  constructor
  · intro x hx
    rcases (def3 X (X ∩ Y) x).mp hx with hX | hXY
    · exact hX
    · exact ((def4 X Y x).mp hXY).1
  · exact th7

/-- `XBOOLE_1:23` (`Th23`). -/
theorem th23 : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by
  apply extensionality
  intro x
  constructor
  · intro hx
    have ⟨hX, hYZ⟩ := (def4 X (Y ∪ Z) x).mp hx
    rcases (def3 Y Z x).mp hYZ with hY | hZ
    · exact (def3 (X ∩ Y) (X ∩ Z) x).mpr (Or.inl ((def4 X Y x).mpr ⟨hX, hY⟩))
    · exact (def3 (X ∩ Y) (X ∩ Z) x).mpr (Or.inr ((def4 X Z x).mpr ⟨hX, hZ⟩))
  · intro hx
    rcases (def3 (X ∩ Y) (X ∩ Z) x).mp hx with hXY | hXZ
    · have ⟨hX, hY⟩ := (def4 X Y x).mp hXY
      exact (def4 X (Y ∪ Z) x).mpr ⟨hX, (def3 Y Z x).mpr (Or.inl hY)⟩
    · have ⟨hX, hZ⟩ := (def4 X Z x).mp hXZ
      exact (def4 X (Y ∪ Z) x).mpr ⟨hX, (def3 Y Z x).mpr (Or.inr hZ)⟩

/-- `XBOOLE_1:24` (`Th24`). -/
theorem th24 : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := by
  apply extensionality
  intro x
  constructor
  · intro hx
    rcases (def3 X (Y ∩ Z) x).mp hx with hX | hYZ
    · exact (def4 (X ∪ Y) (X ∪ Z) x).mpr
        ⟨(def3 X Y x).mpr (Or.inl hX), (def3 X Z x).mpr (Or.inl hX)⟩
    · have ⟨hY, hZ⟩ := (def4 Y Z x).mp hYZ
      exact (def4 (X ∪ Y) (X ∪ Z) x).mpr
        ⟨(def3 X Y x).mpr (Or.inr hY), (def3 X Z x).mpr (Or.inr hZ)⟩
  · intro hx
    have ⟨hXY, hXZ⟩ := (def4 (X ∪ Y) (X ∪ Z) x).mp hx
    rcases (def3 X Y x).mp hXY with hX | hY
    · exact (def3 X (Y ∩ Z) x).mpr (Or.inl hX)
    · rcases (def3 X Z x).mp hXZ with hX | hZ
      · exact (def3 X (Y ∩ Z) x).mpr (Or.inl hX)
      · exact (def3 X (Y ∩ Z) x).mpr (Or.inr ((def4 Y Z x).mpr ⟨hY, hZ⟩))

/-- `XBOOLE_1:25` -/
theorem th25 :
    ((X ∩ Y) ∪ (Y ∩ Z)) ∪ (Z ∩ X) = ((X ∪ Y) ∩ (Y ∪ Z)) ∩ (Z ∪ X) := by
  apply extensionality
  intro x
  have memL : x ∈ ((X ∩ Y) ∪ (Y ∩ Z)) ∪ (Z ∩ X) ↔
      x ∈ X ∧ x ∈ Y ∨ x ∈ Y ∧ x ∈ Z ∨ x ∈ Z ∧ x ∈ X := by
    constructor
    · intro hx
      rcases (def3 ((X ∩ Y) ∪ (Y ∩ Z)) (Z ∩ X) x).mp hx with h | hZX
      · rcases (def3 (X ∩ Y) (Y ∩ Z) x).mp h with hXY | hYZ
        · exact Or.inl ((def4 X Y x).mp hXY)
        · exact Or.inr (Or.inl ((def4 Y Z x).mp hYZ))
      · exact Or.inr (Or.inr ((def4 Z X x).mp hZX))
    · intro h
      match h with
      | Or.inl hXY =>
        exact (def3 ((X ∩ Y) ∪ (Y ∩ Z)) (Z ∩ X) x).mpr
          (Or.inl ((def3 (X ∩ Y) (Y ∩ Z) x).mpr (Or.inl ((def4 X Y x).mpr hXY))))
      | Or.inr (Or.inl hYZ) =>
        exact (def3 ((X ∩ Y) ∪ (Y ∩ Z)) (Z ∩ X) x).mpr
          (Or.inl ((def3 (X ∩ Y) (Y ∩ Z) x).mpr (Or.inr ((def4 Y Z x).mpr hYZ))))
      | Or.inr (Or.inr hZX) =>
        exact (def3 ((X ∩ Y) ∪ (Y ∩ Z)) (Z ∩ X) x).mpr
          (Or.inr ((def4 Z X x).mpr hZX))
  have memR : x ∈ ((X ∪ Y) ∩ (Y ∪ Z)) ∩ (Z ∪ X) ↔
      (x ∈ X ∨ x ∈ Y) ∧ (x ∈ Y ∨ x ∈ Z) ∧ (x ∈ Z ∨ x ∈ X) := by
    constructor
    · intro hx
      have ⟨hXYZ, hZX⟩ := (def4 ((X ∪ Y) ∩ (Y ∪ Z)) (Z ∪ X) x).mp hx
      have ⟨hXY, hYZ⟩ := (def4 (X ∪ Y) (Y ∪ Z) x).mp hXYZ
      exact ⟨(def3 X Y x).mp hXY, (def3 Y Z x).mp hYZ, (def3 Z X x).mp hZX⟩
    · intro ⟨hXY, hYZ, hZX⟩
      exact (def4 ((X ∪ Y) ∩ (Y ∪ Z)) (Z ∪ X) x).mpr
        ⟨(def4 (X ∪ Y) (Y ∪ Z) x).mpr
          ⟨(def3 X Y x).mpr hXY, (def3 Y Z x).mpr hYZ⟩,
          (def3 Z X x).mpr hZX⟩
  refine memL.trans ?_ |>.trans memR.symm
  constructor
  · intro h
    match h with
    | Or.inl ⟨hX, hY⟩ => exact ⟨Or.inl hX, Or.inl hY, Or.inr hX⟩
    | Or.inr (Or.inl ⟨hY, hZ⟩) => exact ⟨Or.inr hY, Or.inl hY, Or.inl hZ⟩
    | Or.inr (Or.inr ⟨hZ, hX⟩) => exact ⟨Or.inl hX, Or.inr hZ, Or.inl hZ⟩
  · intro ⟨hXY, hYZ, hZX⟩
    cases hXY with
    | inl hX =>
      cases hZX with
      | inl hZ => exact Or.inr (Or.inr ⟨hZ, hX⟩)
      | inr _ =>
        cases hYZ with
        | inl hY => exact Or.inl ⟨hX, hY⟩
        | inr hZ => exact Or.inr (Or.inr ⟨hZ, hX⟩)
    | inr hY =>
      cases hYZ with
      | inl _ =>
        cases hZX with
        | inl hZ => exact Or.inr (Or.inl ⟨hY, hZ⟩)
        | inr hX => exact Or.inl ⟨hX, hY⟩
      | inr hZ => exact Or.inr (Or.inl ⟨hY, hZ⟩)

/-! ## More intersection and difference -/

/-- `XBOOLE_1:26` (`Th26`). -/
theorem th26 (h : X ⊆ Y) : X ∩ Z ⊆ Y ∩ Z := by
  intro x hx
  have ⟨hX, hZ⟩ := (def4 X Z x).mp hx
  exact (def4 Y Z x).mpr ⟨h x hX, hZ⟩

/-- `XBOOLE_1:27` -/
theorem th27 (hXY : X ⊆ Y) (hZV : Z ⊆ V) : X ∩ Z ⊆ Y ∩ V := by
  intro x hx
  have ⟨hX, hZ⟩ := (def4 X Z x).mp hx
  exact (def4 Y V x).mpr ⟨hXY x hX, hZV x hZ⟩

/-- `XBOOLE_1:28` (`Th28`). -/
theorem th28 (h : X ⊆ Y) : X ∩ Y = X := by
  apply def10.mpr
  constructor
  · exact th17
  · intro x hx
    exact (def4 X Y x).mpr ⟨hx, h x hx⟩

/-- `XBOOLE_1:29` -/
theorem th29 : X ∩ Y ⊆ X ∪ Z :=
  th1 th17 th7

/-- `XBOOLE_1:30` -/
theorem th30 (h : X ⊆ Z) : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ Z := by
  apply extensionality
  intro x
  constructor
  · intro hx
    rcases (def3 X (Y ∩ Z) x).mp hx with hX | hYZ
    · exact (def4 (X ∪ Y) Z x).mpr ⟨(def3 X Y x).mpr (Or.inl hX), h x hX⟩
    · have ⟨hY, hZ⟩ := (def4 Y Z x).mp hYZ
      exact (def4 (X ∪ Y) Z x).mpr ⟨(def3 X Y x).mpr (Or.inr hY), hZ⟩
  · intro hx
    have ⟨hXY, hZ⟩ := (def4 (X ∪ Y) Z x).mp hx
    rcases (def3 X Y x).mp hXY with hX | hY
    · exact (def3 X (Y ∩ Z) x).mpr (Or.inl hX)
    · exact (def3 X (Y ∩ Z) x).mpr (Or.inr ((def4 Y Z x).mpr ⟨hY, hZ⟩))

/-- `XBOOLE_1:31` -/
theorem th31 : (X ∩ Y) ∪ (X ∩ Z) ⊆ Y ∪ Z :=
  fun x hx =>
    (def3 Y Z x).mpr <|
      match (def3 (X ∩ Y) (X ∩ Z) x).mp hx with
      | Or.inl hXY => Or.inl ((def4 X Y x).mp hXY).2
      | Or.inr hXZ => Or.inr ((def4 X Z x).mp hXZ).2

/-- `Lm1`: `X \ Y = {}` iff `X ⊆ Y`. -/
theorem lm1 : X \ Y = (∅ : TarskiSet.{u}) ↔ X ⊆ Y := by
  constructor
  · intro h x hx
    by_cases hxY : x ∈ Y
    · exact hxY
    · exact (empty_iff x).mp (h ▸ (def5 X Y x).mpr ⟨hx, hxY⟩) |>.elim
  · intro h
    apply extensionality
    intro x
    constructor
    · intro hx
      have ⟨hxX, hxY⟩ := (def5 X Y x).mp hx
      exact (hxY (h x hxX)).elim
    · intro hx
      exact (empty_iff x).mp hx |>.elim

/-- `XBOOLE_1:32` -/
theorem th32 (h : X \ Y = Y \ X) : X = Y := by
  apply extensionality
  intro x
  constructor
  · intro hxX
    by_cases hxY : x ∈ Y
    · exact hxY
    · have : x ∈ Y \ X := h ▸ (def5 X Y x).mpr ⟨hxX, hxY⟩
      exact ((def5 Y X x).mp this).1
  · intro hxY
    by_cases hxX : x ∈ X
    · exact hxX
    · have : x ∈ X \ Y := h.symm ▸ (def5 Y X x).mpr ⟨hxY, hxX⟩
      exact ((def5 X Y x).mp this).1

/-- `XBOOLE_1:33` (`Th33`). -/
theorem th33 (h : X ⊆ Y) : X \ Z ⊆ Y \ Z := by
  intro x hx
  have ⟨hX, hZ⟩ := (def5 X Z x).mp hx
  exact (def5 Y Z x).mpr ⟨h x hX, hZ⟩

/-- `XBOOLE_1:34` (`Th34`). -/
theorem th34 (h : X ⊆ Y) : Z \ Y ⊆ Z \ X := by
  intro x hx
  have ⟨hZ, hY⟩ := (def5 Z Y x).mp hx
  exact (def5 Z X x).mpr ⟨hZ, fun hX => hY (h x hX)⟩

/-- `Lm2`. -/
theorem lm2 : X \ (Y ∩ Z) = (X \ Y) ∪ (X \ Z) := by
  apply def10.mpr
  constructor
  · intro x hx
    have ⟨hX, hnYZ⟩ := (def5 X (Y ∩ Z) x).mp hx
    have : x ∉ Y ∨ x ∉ Z := by
      by_cases hY : x ∈ Y
      · exact Or.inr fun hZ => hnYZ ((def4 Y Z x).mpr ⟨hY, hZ⟩)
      · exact Or.inl hY
    cases this with
    | inl hY => exact (def3 (X \ Y) (X \ Z) x).mpr (Or.inl ((def5 X Y x).mpr ⟨hX, hY⟩))
    | inr hZ => exact (def3 (X \ Y) (X \ Z) x).mpr (Or.inr ((def5 X Z x).mpr ⟨hX, hZ⟩))
  · exact th8 (th34 th17) (th34 (by rw [inter_comm Y Z]; exact th17))

/-- `XBOOLE_1:35` -/
theorem th35 (hXY : X ⊆ Y) (hZV : Z ⊆ V) : X \ V ⊆ Y \ Z :=
  th1 (th33 hXY) (th34 hZV)

/-- `XBOOLE_1:36` (`Th36`). -/
theorem th36 : X \ Y ⊆ X :=
  fun x hx => ((def5 X Y x).mp hx).1

/-- `XBOOLE_1:37` -/
theorem th37 : X \ Y = (∅ : TarskiSet.{u}) ↔ X ⊆ Y :=
  lm1

/-- `XBOOLE_1:38` -/
theorem th38 (h : X ⊆ Y \ X) : X = (∅ : TarskiSet.{u}) :=
  th3 fun x hx =>
    let ⟨_, hxX⟩ := (def5 Y X x).mp (h x hx)
    (hxX hx).elim

/-- `XBOOLE_1:39` (`Th39`). -/
theorem th39 : X ∪ (Y \ X) = X ∪ Y := by
  apply extensionality
  intro x
  constructor
  · intro hx
    rcases (def3 X (Y \ X) x).mp hx with hX | hYX
    · exact (def3 X Y x).mpr (Or.inl hX)
    · exact (def3 X Y x).mpr (Or.inr ((def5 Y X x).mp hYX).1)
  · intro hx
    rcases (def3 X Y x).mp hx with hX | hY
    · exact (def3 X (Y \ X) x).mpr (Or.inl hX)
    · by_cases hX : x ∈ X
      · exact (def3 X (Y \ X) x).mpr (Or.inl hX)
      · exact (def3 X (Y \ X) x).mpr (Or.inr ((def5 Y X x).mpr ⟨hY, hX⟩))

/-- `XBOOLE_1:40` -/
theorem th40 : (X ∪ Y) \ Y = X \ Y := by
  apply extensionality
  intro x
  constructor
  · intro hx
    have ⟨hXY, hY⟩ := (def5 (X ∪ Y) Y x).mp hx
    rcases (def3 X Y x).mp hXY with hX | hY'
    · exact (def5 X Y x).mpr ⟨hX, hY⟩
    · exact (hY hY').elim
  · intro hx
    have ⟨hX, hY⟩ := (def5 X Y x).mp hx
    exact (def5 (X ∪ Y) Y x).mpr ⟨(def3 X Y x).mpr (Or.inl hX), hY⟩

/-- `XBOOLE_1:41` (`Th41`). -/
theorem th41 : (X \ Y) \ Z = X \ (Y ∪ Z) := by
  apply extensionality
  intro x
  constructor
  · intro hx
    have ⟨hXY, hZ⟩ := (def5 (X \ Y) Z x).mp hx
    have ⟨hX, hY⟩ := (def5 X Y x).mp hXY
    exact (def5 X (Y ∪ Z) x).mpr
      ⟨hX, fun hYZ => (def3 Y Z x).mp hYZ |>.elim hY hZ⟩
  · intro hx
    have ⟨hX, hYZ⟩ := (def5 X (Y ∪ Z) x).mp hx
    have hY : x ∉ Y := fun hY => hYZ ((def3 Y Z x).mpr (Or.inl hY))
    have hZ : x ∉ Z := fun hZ => hYZ ((def3 Y Z x).mpr (Or.inr hZ))
    exact (def5 (X \ Y) Z x).mpr ⟨(def5 X Y x).mpr ⟨hX, hY⟩, hZ⟩

/-- `XBOOLE_1:42` (`Th42`). -/
theorem th42 : (X ∪ Y) \ Z = (X \ Z) ∪ (Y \ Z) := by
  apply extensionality
  intro x
  constructor
  · intro hx
    have ⟨hXY, hZ⟩ := (def5 (X ∪ Y) Z x).mp hx
    rcases (def3 X Y x).mp hXY with hX | hY
    · exact (def3 (X \ Z) (Y \ Z) x).mpr (Or.inl ((def5 X Z x).mpr ⟨hX, hZ⟩))
    · exact (def3 (X \ Z) (Y \ Z) x).mpr (Or.inr ((def5 Y Z x).mpr ⟨hY, hZ⟩))
  · intro hx
    rcases (def3 (X \ Z) (Y \ Z) x).mp hx with hXZ | hYZ
    · have ⟨hX, hZ⟩ := (def5 X Z x).mp hXZ
      exact (def5 (X ∪ Y) Z x).mpr ⟨(def3 X Y x).mpr (Or.inl hX), hZ⟩
    · have ⟨hY, hZ⟩ := (def5 Y Z x).mp hYZ
      exact (def5 (X ∪ Y) Z x).mpr ⟨(def3 X Y x).mpr (Or.inr hY), hZ⟩

/-- `XBOOLE_1:43` -/
theorem th43 (h : X ⊆ Y ∪ Z) : X \ Y ⊆ Z := by
  intro x hx
  have ⟨hX, hY⟩ := (def5 X Y x).mp hx
  cases (def3 Y Z x).mp (h x hX) with
  | inl hY' => exact (hY hY').elim
  | inr hZ => exact hZ

/-- `XBOOLE_1:44` -/
theorem th44 (h : X \ Y ⊆ Z) : X ⊆ Y ∪ Z := by
  intro x hx
  by_cases hY : x ∈ Y
  · exact (def3 Y Z x).mpr (Or.inl hY)
  · exact (def3 Y Z x).mpr (Or.inr (h x ((def5 X Y x).mpr ⟨hx, hY⟩)))

/-- `XBOOLE_1:45` -/
theorem th45 (h : X ⊆ Y) : Y = X ∪ (Y \ X) := by
  apply extensionality
  intro x
  constructor
  · intro hxY
    by_cases hxX : x ∈ X
    · exact (def3 X (Y \ X) x).mpr (Or.inl hxX)
    · exact (def3 X (Y \ X) x).mpr (Or.inr ((def5 Y X x).mpr ⟨hxY, hxX⟩))
  · intro hx
    rcases (def3 X (Y \ X) x).mp hx with hX | hYX
    · exact h x hX
    · exact ((def5 Y X x).mp hYX).1

/-- `XBOOLE_1:46` -/
theorem th46 : X \ (X ∪ Y) = (∅ : TarskiSet.{u}) :=
  lm1.mpr th7

/-- `XBOOLE_1:47` (`Th47`). -/
theorem th47 : X \ (X ∩ Y) = X \ Y := by
  apply extensionality
  intro x
  constructor
  · intro hx
    have ⟨hX, hnXY⟩ := (def5 X (X ∩ Y) x).mp hx
    exact (def5 X Y x).mpr ⟨hX, fun hY => hnXY ((def4 X Y x).mpr ⟨hX, hY⟩)⟩
  · intro hx
    have ⟨hX, hY⟩ := (def5 X Y x).mp hx
    exact (def5 X (X ∩ Y) x).mpr ⟨hX, fun hXY => hY ((def4 X Y x).mp hXY).2⟩

/-- `XBOOLE_1:48` -/
theorem th48 : X \ (X \ Y) = X ∩ Y := by
  apply extensionality
  intro x
  constructor
  · intro hx
    have ⟨hX, hnXY⟩ := (def5 X (X \ Y) x).mp hx
    have hY : x ∈ Y :=
      Classical.byContradiction fun hY => hnXY ((def5 X Y x).mpr ⟨hX, hY⟩)
    exact (def4 X Y x).mpr ⟨hX, hY⟩
  · intro hx
    have ⟨hX, hY⟩ := (def4 X Y x).mp hx
    exact (def5 X (X \ Y) x).mpr ⟨hX, fun hXY => ((def5 X Y x).mp hXY).2 hY⟩

/-- `XBOOLE_1:49` (`Th49`). -/
theorem th49 : X ∩ (Y \ Z) = (X ∩ Y) \ Z := by
  apply extensionality
  intro x
  constructor
  · intro hx
    have ⟨hX, hYZ⟩ := (def4 X (Y \ Z) x).mp hx
    have ⟨hY, hZ⟩ := (def5 Y Z x).mp hYZ
    exact (def5 (X ∩ Y) Z x).mpr ⟨(def4 X Y x).mpr ⟨hX, hY⟩, hZ⟩
  · intro hx
    have ⟨hXY, hZ⟩ := (def5 (X ∩ Y) Z x).mp hx
    have ⟨hX, hY⟩ := (def4 X Y x).mp hXY
    exact (def4 X (Y \ Z) x).mpr ⟨hX, (def5 Y Z x).mpr ⟨hY, hZ⟩⟩

/-- `XBOOLE_1:50` (`Th50`). -/
theorem th50 : X ∩ (Y \ Z) = (X ∩ Y) \ (X ∩ Z) := by
  have hLm2 : (X ∩ Y) \ (X ∩ Z) = ((X ∩ Y) \ X) ∪ ((X ∩ Y) \ Z) := lm2
  have hempty : (X ∩ Y) \ X = (∅ : TarskiSet.{u}) := lm1.mpr th17
  calc
    X ∩ (Y \ Z) = (X ∩ Y) \ Z := th49
    _ = (∅ : TarskiSet.{u}) ∪ ((X ∩ Y) \ Z) := (th12 (X := ∅) (Y := (X ∩ Y) \ Z) th2).symm
    _ = ((X ∩ Y) \ X) ∪ ((X ∩ Y) \ Z) := by rw [hempty]
    _ = (X ∩ Y) \ (X ∩ Z) := hLm2.symm

/-- `XBOOLE_1:51` (`Th51`). -/
theorem th51 : (X ∩ Y) ∪ (X \ Y) = X := by
  apply def10.mpr
  constructor
  · intro x hx
    rcases (def3 (X ∩ Y) (X \ Y) x).mp hx with hXY | hXY'
    · exact ((def4 X Y x).mp hXY).1
    · exact ((def5 X Y x).mp hXY').1
  · intro x hx
    by_cases hY : x ∈ Y
    · exact (def3 (X ∩ Y) (X \ Y) x).mpr (Or.inl ((def4 X Y x).mpr ⟨hx, hY⟩))
    · exact (def3 (X ∩ Y) (X \ Y) x).mpr (Or.inr ((def5 X Y x).mpr ⟨hx, hY⟩))

/-- `XBOOLE_1:52` (`Th52`). -/
theorem th52 : X \ (Y \ Z) = (X \ Y) ∪ (X ∩ Z) := by
  apply extensionality
  intro x
  constructor
  · intro hx
    have ⟨hX, hnYZ⟩ := (def5 X (Y \ Z) x).mp hx
    by_cases hY : x ∈ Y
    · have hZ : x ∈ Z :=
        Classical.byContradiction fun hZ => hnYZ ((def5 Y Z x).mpr ⟨hY, hZ⟩)
      exact (def3 (X \ Y) (X ∩ Z) x).mpr (Or.inr ((def4 X Z x).mpr ⟨hX, hZ⟩))
    · exact (def3 (X \ Y) (X ∩ Z) x).mpr (Or.inl ((def5 X Y x).mpr ⟨hX, hY⟩))
  · intro hx
    rcases (def3 (X \ Y) (X ∩ Z) x).mp hx with hXY | hXZ
    · have ⟨hX, hY⟩ := (def5 X Y x).mp hXY
      exact (def5 X (Y \ Z) x).mpr ⟨hX, fun hYZ => hY ((def5 Y Z x).mp hYZ).1⟩
    · have ⟨hX, hZ⟩ := (def4 X Z x).mp hXZ
      exact (def5 X (Y \ Z) x).mpr ⟨hX, fun hYZ => ((def5 Y Z x).mp hYZ).2 hZ⟩

/-- `XBOOLE_1:53` -/
theorem th53 : X \ (Y ∪ Z) = (X \ Y) ∩ (X \ Z) := by
  apply def10.mpr
  constructor
  · exact th19 (th34 th7) (th34 (by rw [union_comm Y Z]; exact th7))
  · intro x hx
    have ⟨hXY, hXZ⟩ := (def4 (X \ Y) (X \ Z) x).mp hx
    have ⟨hX, hY⟩ := (def5 X Y x).mp hXY
    have ⟨_, hZ⟩ := (def5 X Z x).mp hXZ
    exact (def5 X (Y ∪ Z) x).mpr
      ⟨hX, fun hYZ => (def3 Y Z x).mp hYZ |>.elim hY hZ⟩

/-- `XBOOLE_1:54` -/
theorem th54 : X \ (Y ∩ Z) = (X \ Y) ∪ (X \ Z) :=
  lm2

/-- `XBOOLE_1:55` (`Th55`). -/
theorem th55 : (X ∪ Y) \ (X ∩ Y) = (X \ Y) ∪ (Y \ X) := by
  apply extensionality
  intro x
  constructor
  · intro hx
    have ⟨hXY, hnI⟩ := (def5 (X ∪ Y) (X ∩ Y) x).mp hx
    have nand : ¬ (x ∈ X ∧ x ∈ Y) := fun h => hnI ((def4 X Y x).mpr h)
    rcases (def3 X Y x).mp hXY with hX | hY
    · exact (def3 (X \ Y) (Y \ X) x).mpr
        (Or.inl ((def5 X Y x).mpr ⟨hX, fun hY => nand ⟨hX, hY⟩⟩))
    · exact (def3 (X \ Y) (Y \ X) x).mpr
        (Or.inr ((def5 Y X x).mpr ⟨hY, fun hX => nand ⟨hX, hY⟩⟩))
  · intro hx
    rcases (def3 (X \ Y) (Y \ X) x).mp hx with hXY | hYX
    · have ⟨hX, hY⟩ := (def5 X Y x).mp hXY
      exact (def5 (X ∪ Y) (X ∩ Y) x).mpr
        ⟨(def3 X Y x).mpr (Or.inl hX), fun hI => hY ((def4 X Y x).mp hI).2⟩
    · have ⟨hY, hX⟩ := (def5 Y X x).mp hYX
      exact (def5 (X ∪ Y) (X ∩ Y) x).mpr
        ⟨(def3 X Y x).mpr (Or.inr hY), fun hI => hX ((def4 X Y x).mp hI).1⟩

/-- `Lm3`. -/
theorem lm3 (hXY : X ⊆ Y) (hYZ : Y ⊂ Z) : X ⊂ Z :=
  ⟨th1 hXY hYZ.1, fun hXZ => hYZ.2 (def10.mpr ⟨hYZ.1, hXZ.symm ▸ hXY⟩)⟩

/-- `XBOOLE_1:56` -/
theorem th56 (hXY : X ⊂ Y) (hYZ : Y ⊂ Z) : X ⊂ Z :=
  lm3 hXY.1 hYZ

/-- `XBOOLE_1:57` -/
theorem th57 : ¬ (X ⊂ Y ∧ Y ⊂ X) :=
  fun ⟨hXY, hYX⟩ => ssubset_asymm hXY hYX

/-- `XBOOLE_1:58` -/
theorem th58 (hXY : X ⊂ Y) (hYZ : Y ⊆ Z) : X ⊂ Z :=
  ⟨th1 hXY.1 hYZ, fun hXZ => hXY.2 (def10.mpr ⟨hXY.1, hXZ.symm ▸ hYZ⟩)⟩

/-- `XBOOLE_1:59` -/
theorem th59 (hXY : X ⊆ Y) (hYZ : Y ⊂ Z) : X ⊂ Z :=
  lm3 hXY hYZ

/-- `XBOOLE_1:60` (`Th60`). -/
theorem th60 (h : X ⊆ Y) : ¬ Y ⊂ X :=
  fun hYX => hYX.2 (def10.mpr ⟨hYX.1, h⟩)

/-- `XBOOLE_1:61` -/
theorem th61 (h : X ≠ (∅ : TarskiSet.{u})) : (∅ : TarskiSet.{u}) ⊂ X :=
  ⟨th2, fun he => h he.symm⟩

/-- `XBOOLE_1:62` -/
theorem th62 : ¬ X ⊂ (∅ : TarskiSet.{u}) :=
  fun h => h.2 (th3 h.1)

/-- `XBOOLE_1:63` (`Th63`, Modus Celarent / Darii). -/
theorem th63 (hXY : X ⊆ Y) (hmiss : misses Y Z) : misses X Z := by
  have : X ∩ Z ⊆ Y ∩ Z := th26 hXY
  have : X ∩ Z ⊆ (∅ : TarskiSet.{u}) := hmiss ▸ this
  exact th3 this

/-- `XBOOLE_1:64` -/
theorem th64 (hAX : A ⊆ X) (hBY : B ⊆ Y) (hmiss : misses X Y) : misses A B :=
  misses_symm (th63 hBY (misses_symm (th63 hAX hmiss)))

/-- `XBOOLE_1:65` -/
theorem th65 : misses X (∅ : TarskiSet.{u}) :=
  th3 fun x hx => ((def4 X ∅ x).mp hx).2

/-- `XBOOLE_1:66` -/
theorem th66 : meets X X ↔ X ≠ (∅ : TarskiSet.{u}) := by
  constructor
  · intro hmeets he
    obtain ⟨x, hx, _⟩ := (XBOOLE_0.th3 X X).mp hmeets
    exact (empty_iff x).mp (he ▸ hx)
  · intro hne hmiss
    have : X ∩ X = X := inter_idem X
    exact hne (this.symm.trans hmiss)

/-- `XBOOLE_1:67` -/
theorem th67 (hXY : X ⊆ Y) (hXZ : X ⊆ Z) (hmiss : misses Y Z) :
    X = (∅ : TarskiSet.{u}) :=
  th3 (hmiss ▸ th19 hXY hXZ)

/-- `XBOOLE_1:68` (`Th68`, Modus Darapti). -/
theorem th68 {A : TarskiSet.{u}} (hA : ¬ isEmpty A) (hAY : A ⊆ Y) (hAZ : A ⊆ Z) :
    meets Y Z := by
  obtain ⟨x, hx⟩ := Classical.not_not.mp hA
  exact (XBOOLE_0.th3 Y Z).mpr ⟨x, hAY x hx, hAZ x hx⟩

/-- `XBOOLE_1:69` -/
theorem th69 {A : TarskiSet.{u}} (hA : ¬ isEmpty A) (hAY : A ⊆ Y) : meets A Y :=
  th68 hA (subset_refl A) hAY

/-- `XBOOLE_1:70` (`Th70`). -/
theorem th70 : meets X (Y ∪ Z) ↔ meets X Y ∨ meets X Z := by
  constructor
  · intro h
    obtain ⟨x, hxX, hxYZ⟩ := (XBOOLE_0.th3 X (Y ∪ Z)).mp h
    rcases (def3 Y Z x).mp hxYZ with hY | hZ
    · exact Or.inl ((XBOOLE_0.th3 X Y).mpr ⟨x, hxX, hY⟩)
    · exact Or.inr ((XBOOLE_0.th3 X Z).mpr ⟨x, hxX, hZ⟩)
  · intro h
    cases h with
    | inl hY =>
      obtain ⟨x, hxX, hxY⟩ := (XBOOLE_0.th3 X Y).mp hY
      exact (XBOOLE_0.th3 X (Y ∪ Z)).mpr ⟨x, hxX, (def3 Y Z x).mpr (Or.inl hxY)⟩
    | inr hZ =>
      obtain ⟨x, hxX, hxZ⟩ := (XBOOLE_0.th3 X Z).mp hZ
      exact (XBOOLE_0.th3 X (Y ∪ Z)).mpr ⟨x, hxX, (def3 Y Z x).mpr (Or.inr hxZ)⟩

/-- `XBOOLE_1:71` -/
theorem th71 (hEq : X ∪ Y = Z ∪ Y) (hXY : misses X Y) (hZY : misses Z Y) : X = Z := by
  apply def10.mpr
  constructor
  · intro x hx
    have hxZY : x ∈ Z ∪ Y := hEq ▸ th7 (X := X) (Y := Y) x hx
    have hnY : x ∉ Y := fun hY =>
      (empty_iff x).mp (hXY ▸ (def4 X Y x).mpr ⟨hx, hY⟩)
    cases (def3 Z Y x).mp hxZY with
    | inl hZ => exact hZ
    | inr hY => exact (hnY hY).elim
  · intro x hx
    have hxXY : x ∈ X ∪ Y := hEq.symm ▸ th7 (X := Z) (Y := Y) x hx
    have hnY : x ∉ Y := fun hY =>
      (empty_iff x).mp (hZY ▸ (def4 Z Y x).mpr ⟨hx, hY⟩)
    cases (def3 X Y x).mp hxXY with
    | inl hX => exact hX
    | inr hY => exact (hnY hY).elim

/-- `XBOOLE_1:72` -/
theorem th72 (hEq : X9 ∪ Y9 = X ∪ Y) (hXX9 : misses X X9) (hYY9 : misses Y Y9) :
    X = Y9 := by
  have hY9sub : Y9 ⊆ X ∪ Y := by
    have : Y9 ⊆ X9 ∪ Y9 := by
      rw [union_comm]; exact th7
    exact hEq ▸ this
  calc
    X = X ∩ (X9 ∪ Y9) := by
      have : X ⊆ X9 ∪ Y9 := by
        have : X ⊆ X ∪ Y := th7
        exact hEq.symm ▸ this
      exact (th28 this).symm
    _ = (X ∩ X9) ∪ (X ∩ Y9) := th23
    _ = (∅ : TarskiSet.{u}) ∪ (X ∩ Y9) := by rw [hXX9]
    _ = X ∩ Y9 := th12 th2
    _ = (X ∪ Y) ∩ Y9 := by
      rw [inter_comm (X ∪ Y) Y9, th23, inter_comm Y9 X, inter_comm Y9 Y,
        hYY9, union_comm, th12 th2]
    _ = Y9 := by
      rw [inter_comm (X ∪ Y) Y9, th28 hY9sub]

/-- `XBOOLE_1:73` -/
theorem th73 (h : X ⊆ Y ∪ Z) (hmiss : misses X Z) : X ⊆ Y := by
  intro x hx
  have hnZ : x ∉ Z := fun hZ =>
    (empty_iff x).mp (hmiss ▸ (def4 X Z x).mpr ⟨hx, hZ⟩)
  cases (def3 Y Z x).mp (h x hx) with
  | inl hY => exact hY
  | inr hZ => exact (hnZ hZ).elim

/-- `XBOOLE_1:74` (`Th74`). -/
theorem th74 (h : meets X (Y ∩ Z)) : meets X Y := by
  obtain ⟨x, hxX, hxYZ⟩ := (XBOOLE_0.th3 X (Y ∩ Z)).mp h
  exact (XBOOLE_0.th3 X Y).mpr ⟨x, hxX, ((def4 Y Z x).mp hxYZ).1⟩

/-- `XBOOLE_1:75` -/
theorem th75 (h : meets X Y) : meets (X ∩ Y) Y := by
  obtain ⟨x, hxX, hxY⟩ := (XBOOLE_0.th3 X Y).mp h
  exact (XBOOLE_0.th3 (X ∩ Y) Y).mpr ⟨x, (def4 X Y x).mpr ⟨hxX, hxY⟩, hxY⟩

/-- `XBOOLE_1:76` -/
theorem th76 (h : misses Y Z) : misses (X ∩ Y) (X ∩ Z) :=
  th3 fun x hx =>
    let ⟨hXY, hXZ⟩ := (def4 (X ∩ Y) (X ∩ Z) x).mp hx
    let ⟨_, hY⟩ := (def4 X Y x).mp hXY
    let ⟨_, hZ⟩ := (def4 X Z x).mp hXZ
    h ▸ (def4 Y Z x).mpr ⟨hY, hZ⟩

/-- `XBOOLE_1:77` -/
theorem th77 (hmeet : meets X Y) (hXZ : X ⊆ Z) : meets X (Y ∩ Z) := by
  intro hmiss
  have : X ∩ Y = X ∩ (Y ∩ Z) := by
    calc
      X ∩ Y = (X ∩ Z) ∩ Y := by rw [th28 hXZ]
      _ = X ∩ (Z ∩ Y) := th16
      _ = X ∩ (Y ∩ Z) := by rw [inter_comm Z Y]
  exact hmeet (this.trans hmiss)

/-- `XBOOLE_1:78` -/
theorem th78 (h : misses X Y) : X ∩ (Y ∪ Z) = X ∩ Z := by
  calc
    X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := th23
    _ = (∅ : TarskiSet.{u}) ∪ (X ∩ Z) := by rw [h]
    _ = X ∩ Z := th12 th2

/-- `XBOOLE_1:79` (`Th79`). -/
theorem th79 : misses (X \ Y) Y :=
  th3 fun x hx =>
    let ⟨hXY, hY⟩ := (def4 (X \ Y) Y x).mp hx
    (empty_iff x).mpr (((def5 X Y x).mp hXY).2 hY)

/-- `XBOOLE_1:80` -/
theorem th80 (h : misses X Y) : misses X (Y \ Z) := by
  apply misses_of
  intro hmeet
  obtain ⟨x, hxX, hxYZ⟩ := (XBOOLE_0.th3 X (Y \ Z)).mp hmeet
  exact (XBOOLE_0.th3 X Y).mpr ⟨x, hxX, ((def5 Y Z x).mp hxYZ).1⟩ h

/-- `XBOOLE_1:81` -/
theorem th81 (h : misses X (Y \ Z)) : misses Y (X \ Z) := by
  have : X ∩ (Y \ Z) = Y ∩ (X \ Z) := by
    calc
      X ∩ (Y \ Z) = (X ∩ Y) \ Z := th49
      _ = (Y ∩ X) \ Z := by rw [inter_comm X Y]
      _ = Y ∩ (X \ Z) := th49.symm
  exact this.symm.trans h

/-- `XBOOLE_1:82` -/
theorem th82 : misses (X \ Y) (Y \ X) := by
  apply misses_of
  intro hmeet
  obtain ⟨x, hXY, hYX⟩ := (XBOOLE_0.th3 (X \ Y) (Y \ X)).mp hmeet
  exact ((def5 Y X x).mp hYX).2 ((def5 X Y x).mp hXY).1

/-- `XBOOLE_1:83` (`Th83`). -/
theorem th83 : misses X Y ↔ X \ Y = X := by
  constructor
  · intro h
    apply extensionality
    intro x
    constructor
    · exact fun hx => ((def5 X Y x).mp hx).1
    · intro hx
      have hnY : x ∉ Y := fun hY =>
        (empty_iff x).mp (h ▸ (def4 X Y x).mpr ⟨hx, hY⟩)
      exact (def5 X Y x).mpr ⟨hx, hnY⟩
  · intro h
    apply th3
    intro x hx
    have ⟨hX, hY⟩ := (def4 X Y x).mp hx
    exact (empty_iff x).mpr (((def5 X Y x).mp (h.symm ▸ hX)).2 hY)

/-- `XBOOLE_1:84` -/
theorem th84 (hmeet : meets X Y) (hmiss : misses X Z) : meets X (Y \ Z) := by
  have : X ∩ (Y \ Z) = (X ∩ Y) \ (X ∩ Z) := th50
  rw [hmiss, show (X ∩ Y) \ (∅ : TarskiSet.{u}) = X ∩ Y from ?_] at this
  · exact fun h => hmeet (this.symm.trans h)
  · apply extensionality
    intro x
    constructor
    · exact fun hx => ((def5 (X ∩ Y) ∅ x).mp hx).1
    · intro hx
      exact (def5 (X ∩ Y) ∅ x).mpr ⟨hx, fun hE => (empty_iff x).mp hE⟩

/-- `XBOOLE_1:85` -/
theorem th85 (h : X ⊆ Y) : misses X (Z \ Y) := by
  calc
    X ∩ (Z \ Y) = (X ∩ Z) \ Y := th49
    _ = (Z ∩ X) \ Y := by rw [inter_comm X Z]
    _ = Z ∩ (X \ Y) := th49.symm
    _ = Z ∩ (∅ : TarskiSet.{u}) := by rw [lm1.mpr h]
    _ = (∅ : TarskiSet.{u}) := th65 (X := Z)

/-- `XBOOLE_1:86` (`Th86`). -/
theorem th86 (hXY : X ⊆ Y) (hmiss : misses X Z) : X ⊆ Y \ Z := by
  intro x hx
  have hnZ : x ∉ Z := fun hZ =>
    (empty_iff x).mp (hmiss ▸ (def4 X Z x).mpr ⟨hx, hZ⟩)
  exact (def5 Y Z x).mpr ⟨hXY x hx, hnZ⟩

/-- `XBOOLE_1:87` -/
theorem th87 (h : misses Y Z) : (X \ Y) ∪ Z = (X ∪ Z) \ Y := by
  have hz : Z = Z \ Y := (th83.mp (misses_symm h)).symm
  calc
    (X \ Y) ∪ Z = (X \ Y) ∪ (Z \ Y) := congrArg (fun W => (X \ Y) ∪ W) hz
    _ = (X ∪ Z) \ Y := th42.symm

/-- `XBOOLE_1:88` (`Th88`). -/
theorem th88 (h : misses X Y) : (X ∪ Y) \ Y = X := by
  calc
    (X ∪ Y) \ Y = (X \ Y) ∪ (Y \ Y) := th42
    _ = (X \ Y) ∪ (∅ : TarskiSet.{u}) := by rw [lm1.mpr (subset_refl Y)]
    _ = X \ Y := by rw [union_comm]; exact th12 th2
    _ = X := th83.mp h

/-- `XBOOLE_1:89` (`Th89`). -/
theorem th89 : misses (X ∩ Y) (X \ Y) := by
  apply misses_of
  intro hmeet
  obtain ⟨x, hXY, hXd⟩ := (XBOOLE_0.th3 (X ∩ Y) (X \ Y)).mp hmeet
  exact ((def5 X Y x).mp hXd).2 ((def4 X Y x).mp hXY).2

/-- `XBOOLE_1:90` -/
theorem th90 : misses (X \ (X ∩ Y)) Y := by
  rw [th47]
  exact th79

/-- `Lm4`. -/
theorem lm4 : misses (X ∩ Y) (X ∆ Y) := by
  have h1 : misses (X ∩ Y) (X \ Y) := th89
  have h2 : misses (X ∩ Y) (Y \ X) := by
    rw [inter_comm X Y]
    exact th89 (X := Y) (Y := X)
  apply misses_of
  intro hmeet
  exact (th70 (X := X ∩ Y) (Y := X \ Y) (Z := Y \ X)).mp hmeet |>.elim
    (fun h => h h1) (fun h => h h2)

/-- `Lm5`. -/
theorem lm5 : X ∆ Y = (X ∪ Y) \ (X ∩ Y) := by
  calc
    X ∆ Y = (X \ Y) ∪ (Y \ X) := rfl
    _ = (X \ (X ∩ Y)) ∪ (Y \ X) := by rw [th47]
    _ = (X \ (X ∩ Y)) ∪ (Y \ (X ∩ Y)) := by
      have : Y \ X = Y \ (X ∩ Y) := by
        rw [inter_comm X Y, th47]
      rw [this]
    _ = (X ∪ Y) \ (X ∩ Y) := th42.symm

private theorem xor_assoc (p q r : Prop) :
    ¬ (¬ (p ↔ q) ↔ r) ↔ ¬ (p ↔ ¬ (q ↔ r)) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;>
    simp [hp, hq, hr]

/-- `XBOOLE_1:91` -/
theorem th91 : (X ∆ Y) ∆ Z = X ∆ (Y ∆ Z) := by
  apply extensionality
  intro x
  exact (XBOOLE_0.th1 (X ∆ Y) Z x).trans <|
    Iff.trans (not_congr (iff_congr (XBOOLE_0.th1 X Y x) Iff.rfl)) <|
      Iff.trans (xor_assoc (x ∈ X) (x ∈ Y) (x ∈ Z)) <|
        Iff.trans (not_congr (iff_congr Iff.rfl (XBOOLE_0.th1 Y Z x).symm))
          (XBOOLE_0.th1 X (Y ∆ Z) x).symm

/-- `XBOOLE_1:92` -/
theorem th92 : X ∆ X = (∅ : TarskiSet.{u}) := by
  have h : X \ X = (∅ : TarskiSet.{u}) := lm1.mpr (subset_refl X)
  change (X \ X) ∪ (X \ X) = ∅
  rw [h, union_idem]

/-- `XBOOLE_1:93` (`Th93`). -/
theorem th93 : X ∪ Y = (X ∆ Y) ∪ (X ∩ Y) := by
  apply extensionality
  intro x
  constructor
  · intro hx
    rcases (def3 X Y x).mp hx with hX | hY
    · by_cases hY : x ∈ Y
      · exact (def3 (X ∆ Y) (X ∩ Y) x).mpr
          (Or.inr ((def4 X Y x).mpr ⟨hX, hY⟩))
      · exact (def3 (X ∆ Y) (X ∩ Y) x).mpr
          (Or.inl ((def3 (X \ Y) (Y \ X) x).mpr (Or.inl ((def5 X Y x).mpr ⟨hX, hY⟩))))
    · by_cases hX : x ∈ X
      · exact (def3 (X ∆ Y) (X ∩ Y) x).mpr
          (Or.inr ((def4 X Y x).mpr ⟨hX, hY⟩))
      · exact (def3 (X ∆ Y) (X ∩ Y) x).mpr
          (Or.inl ((def3 (X \ Y) (Y \ X) x).mpr (Or.inr ((def5 Y X x).mpr ⟨hY, hX⟩))))
  · intro hx
    rcases (def3 (X ∆ Y) (X ∩ Y) x).mp hx with hd | hI
    · rcases (def3 (X \ Y) (Y \ X) x).mp hd with hXY | hYX
      · exact (def3 X Y x).mpr (Or.inl ((def5 X Y x).mp hXY).1)
      · exact (def3 X Y x).mpr (Or.inr ((def5 Y X x).mp hYX).1)
    · exact (def3 X Y x).mpr (Or.inl ((def4 X Y x).mp hI).1)

/-- `XBOOLE_1:94` -/
theorem th94 : X ∪ Y = (X ∆ Y) ∆ (X ∩ Y) := by
  have hmiss : misses (X ∩ Y) (X ∆ Y) := lm4
  change X ∪ Y = ((X ∆ Y) \ (X ∩ Y)) ∪ ((X ∩ Y) \ (X ∆ Y))
  rw [th83.mp (misses_symm hmiss), th83.mp hmiss, th93]

/-- `XBOOLE_1:95` -/
theorem th95 : X ∩ Y = (X ∆ Y) ∆ (X ∪ Y) := by
  have hsub : X ∆ Y ⊆ X ∪ Y := by
    rw [lm5]; exact th36
  have hempty : (X ∆ Y) \ (X ∪ Y) = (∅ : TarskiSet.{u}) := lm1.mpr hsub
  have hdiff : (X ∪ Y) \ (X ∆ Y) = X ∩ Y := by
    have h88 := th88 (X := X ∩ Y) (Y := X ∆ Y) (lm4 (X := X) (Y := Y))
    rw [union_comm (X ∩ Y) (X ∆ Y)] at h88
    exact th93 ▸ h88
  change X ∩ Y = ((X ∆ Y) \ (X ∪ Y)) ∪ ((X ∪ Y) \ (X ∆ Y))
  rw [hempty, hdiff]
  exact (th12 (X := (∅ : TarskiSet.{u})) (Y := X ∩ Y) th2).symm

/-- `XBOOLE_1:96` -/
theorem th96 : X \ Y ⊆ X ∆ Y :=
  th7

/-- `XBOOLE_1:97` -/
theorem th97 (hX : X \ Y ⊆ Z) (hY : Y \ X ⊆ Z) : X ∆ Y ⊆ Z :=
  th8 hX hY

/-- `XBOOLE_1:98` -/
theorem th98 : X ∪ Y = X ∆ (Y \ X) := by
  have h1 : (Y \ X) \ X = Y \ X := by
    rw [th41, union_idem]
  have h2 : X \ (Y \ X) = X := by
    rw [th52, inter_idem, th12 th36]
  -- X ∪ Y = X ∪ (Y \ X) = X ∆ (Y \ X) after the two identities
  have : X ∪ (Y \ X) = X ∪ Y := th39
  change X ∪ Y = (X \ (Y \ X)) ∪ ((Y \ X) \ X)
  rw [h2, h1, this.symm]

/-- `XBOOLE_1:99` -/
theorem th99 : (X ∆ Y) \ Z = (X \ (Y ∪ Z)) ∪ (Y \ (X ∪ Z)) := by
  calc
    (X ∆ Y) \ Z = ((X \ Y) \ Z) ∪ ((Y \ X) \ Z) := th42
    _ = (X \ (Y ∪ Z)) ∪ ((Y \ X) \ Z) := by rw [th41]
    _ = (X \ (Y ∪ Z)) ∪ (Y \ (X ∪ Z)) := by rw [th41]

/-- `XBOOLE_1:100` -/
theorem th100 : X \ Y = X ∆ (X ∩ Y) := by
  have : (X ∩ Y) \ X = (∅ : TarskiSet.{u}) := lm1.mpr th17
  change X \ Y = (X \ (X ∩ Y)) ∪ ((X ∩ Y) \ X)
  rw [th47, this, union_comm, th12 th2]

/-- `XBOOLE_1:101` -/
theorem th101 : X ∆ Y = (X ∪ Y) \ (X ∩ Y) :=
  lm5

/-- `XBOOLE_1:102` -/
theorem th102 : X \ (Y ∆ Z) = (X \ (Y ∪ Z)) ∪ (X ∩ Y ∩ Z) := by
  calc
    X \ (Y ∆ Z) = X \ ((Y ∪ Z) \ (Y ∩ Z)) := by rw [lm5]
    _ = (X \ (Y ∪ Z)) ∪ (X ∩ (Y ∩ Z)) := th52
    _ = (X \ (Y ∪ Z)) ∪ ((X ∩ Y) ∩ Z) := by rw [th16]

/-- `XBOOLE_1:103` -/
theorem th103 : misses (X ∩ Y) (X ∆ Y) :=
  lm4

/-- `XBOOLE_1:104` -/
theorem th104 : (X ⊂ Y ∨ X = Y ∨ Y ⊂ X) ↔ are_ccomparable X Y := by
  constructor
  · intro h
    cases h with
    | inl hXY => exact Or.inl hXY.1
    | inr h =>
      cases h with
      | inl heq => exact Or.inl (heq ▸ subset_refl X)
      | inr hYX => exact Or.inr hYX.1
  · intro h
    cases h with
    | inl hXY =>
      by_cases heq : X = Y
      · exact Or.inr (Or.inl heq)
      · exact Or.inl ⟨hXY, heq⟩
    | inr hYX =>
      by_cases heq : X = Y
      · exact Or.inr (Or.inl heq)
      · exact Or.inr (Or.inr ⟨hYX, fun h => heq h.symm⟩)

/-- `XBOOLE_1:105` -/
theorem th105 (h : X ⊂ Y) : Y \ X ≠ (∅ : TarskiSet.{u}) :=
  fun hempty => th60 h.1 (⟨lm1.mp hempty, fun he => h.2 he.symm⟩)

/-- `XBOOLE_1:106` (`Th106`). -/
theorem th106 (h : X ⊆ A \ B) : X ⊆ A ∧ misses X B := by
  constructor
  · exact th1 h th36
  · apply misses_of
    intro hmeet
    obtain ⟨x, hxX, hxB⟩ := (XBOOLE_0.th3 X B).mp hmeet
    exact ((def5 A B x).mp (h x hxX)).2 hxB

/-- `XBOOLE_1:107` -/
theorem th107 : X ⊆ A ∆ B ↔ X ⊆ A ∪ B ∧ misses X (A ∩ B) := by
  rw [lm5]
  constructor
  · intro h
    exact ⟨th1 h th36, th106 h |>.2⟩
  · intro ⟨hU, hmiss⟩
    exact th86 hU hmiss

/-- `XBOOLE_1:108` -/
theorem th108 (h : X ⊆ A) : X ∩ Y ⊆ A :=
  th1 th17 h

/-- `XBOOLE_1:109` (`Th109`). -/
theorem th109 (h : X ⊆ A) : X \ Y ⊆ A :=
  th1 th36 h

/-- `XBOOLE_1:110` -/
theorem th110 (hX : X ⊆ A) (hY : Y ⊆ A) : X ∆ Y ⊆ A :=
  th8 (th109 hX) (th109 hY)

/-- `XBOOLE_1:111` (`Th111`). -/
theorem th111 : (X ∩ Z) \ (Y ∩ Z) = (X \ Y) ∩ Z := by
  apply extensionality
  intro x
  constructor
  · intro hx
    have ⟨hXZ, hnYZ⟩ := (def5 (X ∩ Z) (Y ∩ Z) x).mp hx
    have ⟨hX, hZ⟩ := (def4 X Z x).mp hXZ
    have hY : x ∉ Y := fun hY => hnYZ ((def4 Y Z x).mpr ⟨hY, hZ⟩)
    exact (def4 (X \ Y) Z x).mpr ⟨(def5 X Y x).mpr ⟨hX, hY⟩, hZ⟩
  · intro hx
    have ⟨hXY, hZ⟩ := (def4 (X \ Y) Z x).mp hx
    have ⟨hX, hY⟩ := (def5 X Y x).mp hXY
    exact (def5 (X ∩ Z) (Y ∩ Z) x).mpr
      ⟨(def4 X Z x).mpr ⟨hX, hZ⟩, fun hYZ => hY ((def4 Y Z x).mp hYZ).1⟩

/-- `XBOOLE_1:112` -/
theorem th112 : (X ∩ Z) ∆ (Y ∩ Z) = (X ∆ Y) ∩ Z := by
  calc
    (X ∩ Z) ∆ (Y ∩ Z) = ((X ∩ Z) \ (Y ∩ Z)) ∪ ((Y ∩ Z) \ (X ∩ Z)) := rfl
    _ = ((X \ Y) ∩ Z) ∪ ((Y \ X) ∩ Z) := by rw [th111, th111 (X := Y) (Y := X)]
    _ = (Z ∩ (X \ Y)) ∪ (Z ∩ (Y \ X)) := by
      rw [inter_comm (X \ Y) Z, inter_comm (Y \ X) Z]
    _ = Z ∩ ((X \ Y) ∪ (Y \ X)) := (th23 (X := Z) (Y := X \ Y) (Z := Y \ X)).symm
    _ = (X ∆ Y) ∩ Z := inter_comm Z (X ∆ Y)

/-- `XBOOLE_1:113` -/
theorem th113 {W : TarskiSet.{u}} : ((X ∪ Y) ∪ Z) ∪ W = X ∪ ((Y ∪ Z) ∪ W) := by
  rw [th4, th4, th4]

/-- `XBOOLE_1:114` -/
theorem th114 {C D : TarskiSet.{u}}
    (hA : misses A D) (hB : misses B D) (hC : misses C D) :
    misses ((A ∪ B) ∪ C) D := by
  apply th3
  intro x hx
  have ⟨hABC, hD⟩ := (def4 ((A ∪ B) ∪ C) D x).mp hx
  have hmiss : x ∉ A ∧ x ∉ B ∧ x ∉ C := by
    refine ⟨?_, ?_, ?_⟩
    · exact fun hA' => (empty_iff x).mp (hA ▸ (def4 A D x).mpr ⟨hA', hD⟩)
    · exact fun hB' => (empty_iff x).mp (hB ▸ (def4 B D x).mpr ⟨hB', hD⟩)
    · exact fun hC' => (empty_iff x).mp (hC ▸ (def4 C D x).mpr ⟨hC', hD⟩)
  rcases (def3 (A ∪ B) C x).mp hABC with hAB | hC'
  · rcases (def3 A B x).mp hAB with hA' | hB'
    · exact (hmiss.1 hA').elim
    · exact (hmiss.2.1 hB').elim
  · exact (hmiss.2.2 hC').elim

/-- `XBOOLE_1:115` -/
theorem th115 : ¬ A ⊂ (∅ : TarskiSet.{u}) :=
  th62 (X := A)

/-- `XBOOLE_1:116` -/
theorem th116 : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z) := by
  apply extensionality
  intro x
  constructor
  · intro hx
    have ⟨hX, hYZ⟩ := (def4 X (Y ∩ Z) x).mp hx
    have ⟨hY, hZ⟩ := (def4 Y Z x).mp hYZ
    exact (def4 (X ∩ Y) (X ∩ Z) x).mpr
      ⟨(def4 X Y x).mpr ⟨hX, hY⟩, (def4 X Z x).mpr ⟨hX, hZ⟩⟩
  · intro hx
    have ⟨hXY, hXZ⟩ := (def4 (X ∩ Y) (X ∩ Z) x).mp hx
    have ⟨hX, hY⟩ := (def4 X Y x).mp hXY
    have ⟨_, hZ⟩ := (def4 X Z x).mp hXZ
    exact (def4 X (Y ∩ Z) x).mpr ⟨hX, (def4 Y Z x).mpr ⟨hY, hZ⟩⟩

/-- `XBOOLE_1:117` -/
theorem th117 {P G C : TarskiSet.{u}} (h : C ⊆ G) :
    P \ C = (P \ G) ∪ (P ∩ (G \ C)) := by
  apply def10.mpr
  constructor
  · intro x hx
    have ⟨hP, hC⟩ := (def5 P C x).mp hx
    by_cases hG : x ∈ G
    · exact (def3 (P \ G) (P ∩ (G \ C)) x).mpr
        (Or.inr ((def4 P (G \ C) x).mpr ⟨hP, (def5 G C x).mpr ⟨hG, hC⟩⟩))
    · exact (def3 (P \ G) (P ∩ (G \ C)) x).mpr
        (Or.inl ((def5 P G x).mpr ⟨hP, hG⟩))
  · exact th8 (th34 h) fun x hx =>
      let ⟨hP, hGC⟩ := (def4 P (G \ C) x).mp hx
      (def5 P C x).mpr ⟨hP, ((def5 G C x).mp hGC).2⟩

end XBOOLE_1






