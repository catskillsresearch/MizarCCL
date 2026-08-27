import MizarCCL.ENUMSET1

/-
Copyright (c) 2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/xregular.miz`.
Authors: Andrzej Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Consequences of the regularity axiom

1–1 Lean rendering of Mizar article `XREGULAR`
(`vendor/mml/xregular.miz`). Environ: `TARSKI`, `XBOOLE_0`,
`XBOOLE_1`, `ENUMSET1`. Does not import `XTUPLE_0`.
-/

universe u

open TarskiSet TARSKI

namespace XREGULAR

private theorem exists_mem {X : TarskiSet.{u}} (h : ¬ XBOOLE_0.isEmpty X) :
    ∃ x, x ∈ X :=
  Classical.byContradiction fun hne => h hne

private theorem misses_of_no_common {A B : TarskiSet.{u}}
    (h : ¬ ∃ x, x ∈ A ∧ x ∈ B) : XBOOLE_0.misses A B :=
  XBOOLE_0.misses_of fun hmeet => h ((XBOOLE_0.th3 A B).mp hmeet)

private theorem mem_union_left {A B x : TarskiSet.{u}} (hx : x ∈ A) :
    x ∈ A ∪ B :=
  (XBOOLE_0.def3 A B x).mpr (Or.inl hx)

private theorem mem_union_right {A B x : TarskiSet.{u}} (hx : x ∈ B) :
    x ∈ A ∪ B :=
  (XBOOLE_0.def3 A B x).mpr (Or.inr hx)

private theorem meets_union_left {A B C : TarskiSet.{u}}
    (h : XBOOLE_0.meets A B) : XBOOLE_0.meets A (B ∪ C) :=
  (XBOOLE_1.th70 (X := A) (Y := B) (Z := C)).mpr (Or.inl h)

private theorem mem_union {A B x : TarskiSet.{u}} :
    x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B :=
  XBOOLE_0.def3 A B x

private theorem miss_contra {A B x : TarskiSet.{u}}
    (hA : x ∈ A) (hB : x ∈ B) (hmiss : XBOOLE_0.misses A B) : False :=
  (XBOOLE_0.th3 A B).mpr ⟨x, hA, hB⟩ hmiss

private theorem meets_of_mem {A B x : TarskiSet.{u}}
    (hA : x ∈ A) (hB : x ∈ B) : XBOOLE_0.meets A B :=
  (XBOOLE_0.th3 A B).mpr ⟨x, hA, hB⟩

private theorem union_assoc (A B C : TarskiSet.{u}) :
    (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
  XBOOLE_1.th4 (X := A) (Y := B) (Z := C)

/-- `XREGULAR:1` (`Th1`). A nonempty set has an element disjoint from it. -/
theorem th1 {X : TarskiSet.{u}} (hX : ¬ XBOOLE_0.isEmpty X) :
    ∃ Y, Y ∈ X ∧ XBOOLE_0.misses Y X := by
  obtain ⟨x, hx⟩ := exists_mem hX
  obtain ⟨Y, hYX, hdisj⟩ := TARSKI.th2 hx
  exact ⟨Y, hYX, misses_of_no_common fun ⟨z, hzY, hzX⟩ => hdisj ⟨z, hzX, hzY⟩⟩

/-- Depth-1 regularity. -/
theorem th2 {X : TarskiSet.{u}} (hX : ¬ XBOOLE_0.isEmpty X) :
    ∃ Y, Y ∈ X ∧ ∀ Y1, Y1 ∈ Y → XBOOLE_0.misses Y1 X := by
  obtain ⟨Z, hZ⟩ :=
    XBOOLE_0.sch_separation (union X) (fun Y => XBOOLE_0.meets Y X)
  have hXZ : ¬ XBOOLE_0.isEmpty (X ∪ Z) := XBOOLE_0.union_nonempty_left hX
  obtain ⟨Y, hY, hmiss⟩ := th1 hXZ
  refine Classical.byContradiction fun hnot => ?_
  have hnotX : Y ∉ X := by
    intro hYX
    have ⟨Y1, hY1Y, hmeet⟩ : ∃ Y1, Y1 ∈ Y ∧ ¬ XBOOLE_0.misses Y1 X := by
      have : ¬ ∀ Y1, Y1 ∈ Y → XBOOLE_0.misses Y1 X := fun hall =>
        hnot ⟨Y, hYX, hall⟩
      exact Classical.byContradiction fun hne =>
        this fun Y1 hY1 => XBOOLE_0.misses_of fun hm => hne ⟨Y1, hY1, hm⟩
    have hY1U : Y1 ∈ union X :=
      (union_iff _ _).mpr ⟨Y, hY1Y, hYX⟩
    have hY1Z : Y1 ∈ Z := (hZ Y1).mpr ⟨hY1U, hmeet⟩
    exact miss_contra hY1Y (mem_union_right hY1Z) hmiss
  have hYZ : Y ∈ Z := by
    rcases (mem_union (A := X) (B := Z) (x := Y)).mp hY with h | h
    · exact (hnotX h).elim
    · exact h
  have hmeet : XBOOLE_0.meets Y X := ((hZ Y).mp hYZ).2
  exact (meets_union_left (C := Z) hmeet) hmiss

/-- Depth-2 regularity. -/
theorem th3 {X : TarskiSet.{u}} (hX : ¬ XBOOLE_0.isEmpty X) :
    ∃ Y, Y ∈ X ∧ ∀ Y1 Y2, Y1 ∈ Y2 → Y2 ∈ Y → XBOOLE_0.misses Y1 X := by
  obtain ⟨Z1, hZ1⟩ :=
    XBOOLE_0.sch_separation (union X)
      (fun Y => ∃ Y1, Y1 ∈ Y ∧ XBOOLE_0.meets Y1 X)
  obtain ⟨Z2, hZ2⟩ :=
    XBOOLE_0.sch_separation (union (union X))
      (fun Y => XBOOLE_0.meets Y X)
  let V := X ∪ Z1 ∪ Z2
  have hV : ¬ XBOOLE_0.isEmpty V :=
    XBOOLE_0.union_nonempty_left (XBOOLE_0.union_nonempty_left hX)
  obtain ⟨Y, hY, hmiss⟩ := th1 hV
  have notZ1 : Y ∉ Z1 := by
    intro hYZ1
    obtain ⟨Y1, hY1Y, hmeet⟩ := ((hZ1 Y).mp hYZ1).2
    have hYU : Y ∈ union X := ((hZ1 Y).mp hYZ1).1
    have hY1UU : Y1 ∈ union (union X) :=
      (union_iff _ _).mpr ⟨Y, hY1Y, hYU⟩
    have hY1Z2 : Y1 ∈ Z2 := (hZ2 Y1).mpr ⟨hY1UU, hmeet⟩
    exact miss_contra hY1Y (mem_union_right hY1Z2) hmiss
  refine Classical.byContradiction fun hnot => ?_
  have notX : Y ∉ X := by
    intro hYX
    have ⟨Y1, Y2, h12, h2Y, hmeet⟩ :
        ∃ Y1 Y2, Y1 ∈ Y2 ∧ Y2 ∈ Y ∧ ¬ XBOOLE_0.misses Y1 X := by
      have : ¬ ∀ Y1 Y2, Y1 ∈ Y2 → Y2 ∈ Y → XBOOLE_0.misses Y1 X := fun hall =>
        hnot ⟨Y, hYX, hall⟩
      exact Classical.byContradiction fun hne =>
        this fun Y1 Y2 h12 h2Y =>
          XBOOLE_0.misses_of fun hm => hne ⟨Y1, Y2, h12, h2Y, hm⟩
    have hY2U : Y2 ∈ union X := (union_iff _ _).mpr ⟨Y, h2Y, hYX⟩
    have hY2Z1 : Y2 ∈ Z1 := (hZ1 Y2).mpr ⟨hY2U, ⟨Y1, h12, hmeet⟩⟩
    exact miss_contra h2Y (mem_union_left (mem_union_right hY2Z1)) hmiss
  have hY' : Y ∈ X ∪ (Z1 ∪ Z2) :=
    union_assoc X Z1 Z2 ▸ (show Y ∈ X ∪ Z1 ∪ Z2 from hY)
  have hZ12 : Y ∈ Z1 ∪ Z2 := by
    rcases (mem_union (A := X) (B := Z1 ∪ Z2) (x := Y)).mp hY' with h | h
    · exact (notX h).elim
    · exact h
  have hYZ2 : Y ∈ Z2 := by
    rcases (mem_union (A := Z1) (B := Z2) (x := Y)).mp hZ12 with h | h
    · exact (notZ1 h).elim
    · exact h
  have hmeet : XBOOLE_0.meets Y X := ((hZ2 Y).mp hYZ2).2
  have hmeet' : XBOOLE_0.meets Y (X ∪ Z1) := meets_union_left hmeet
  exact (meets_union_left (C := Z2) hmeet') hmiss

/-- Depth-3 regularity. -/
theorem th4 {X : TarskiSet.{u}} (hX : ¬ XBOOLE_0.isEmpty X) :
    ∃ Y, Y ∈ X ∧
      ∀ Y1 Y2 Y3, Y1 ∈ Y2 → Y2 ∈ Y3 → Y3 ∈ Y → XBOOLE_0.misses Y1 X := by
  obtain ⟨Z1, hZ1⟩ :=
    XBOOLE_0.sch_separation (union X)
      (fun Y => ∃ Y1 Y2, Y1 ∈ Y2 ∧ Y2 ∈ Y ∧ XBOOLE_0.meets Y1 X)
  obtain ⟨Z2, hZ2⟩ :=
    XBOOLE_0.sch_separation (union (union X))
      (fun Y => ∃ Y1, Y1 ∈ Y ∧ XBOOLE_0.meets Y1 X)
  obtain ⟨Z3, hZ3⟩ :=
    XBOOLE_0.sch_separation (union (union (union X)))
      (fun Y => XBOOLE_0.meets Y X)
  let V := X ∪ Z1 ∪ Z2 ∪ Z3
  have hVne : ¬ XBOOLE_0.isEmpty V :=
    XBOOLE_0.union_nonempty_left
      (XBOOLE_0.union_nonempty_left (XBOOLE_0.union_nonempty_left hX))
  obtain ⟨Y, hY, hmiss⟩ := th1 hVne
  have notZ2 : Y ∉ Z2 := by
    intro hYZ2
    obtain ⟨Y1, hY1Y, hmeet⟩ := ((hZ2 Y).mp hYZ2).2
    have hYU : Y ∈ union (union X) := ((hZ2 Y).mp hYZ2).1
    have hY1U : Y1 ∈ union (union (union X)) :=
      (union_iff _ _).mpr ⟨Y, hY1Y, hYU⟩
    have hY1Z3 : Y1 ∈ Z3 := (hZ3 Y1).mpr ⟨hY1U, hmeet⟩
    exact miss_contra hY1Y (mem_union_right hY1Z3) hmiss
  have notZ1 : Y ∉ Z1 := by
    intro hYZ1
    obtain ⟨Y1, Y2, h12, h2Y, hmeet⟩ := ((hZ1 Y).mp hYZ1).2
    have hYU : Y ∈ union X := ((hZ1 Y).mp hYZ1).1
    have hY2U : Y2 ∈ union (union X) :=
      (union_iff _ _).mpr ⟨Y, h2Y, hYU⟩
    have hY2Z2 : Y2 ∈ Z2 := (hZ2 Y2).mpr ⟨hY2U, ⟨Y1, h12, hmeet⟩⟩
    have hY2V : Y2 ∈ X ∪ Z1 ∪ Z2 := mem_union_right hY2Z2
    exact meets_union_left (C := Z3) (meets_of_mem h2Y hY2V) hmiss
  have hVeq : V = X ∪ (Z1 ∪ Z2 ∪ Z3) := by
    change X ∪ Z1 ∪ Z2 ∪ Z3 = X ∪ (Z1 ∪ Z2 ∪ Z3)
    rw [union_assoc X Z1 Z2, union_assoc X (Z1 ∪ Z2) Z3]
  refine Classical.byContradiction fun hnot => ?_
  have notX : Y ∉ X := by
    intro hYX
    have ⟨Y1, Y2, Y3, h12, h23, h3Y, hmeet⟩ :
        ∃ Y1 Y2 Y3, Y1 ∈ Y2 ∧ Y2 ∈ Y3 ∧ Y3 ∈ Y ∧ ¬ XBOOLE_0.misses Y1 X := by
      have : ¬ ∀ Y1 Y2 Y3, Y1 ∈ Y2 → Y2 ∈ Y3 → Y3 ∈ Y →
          XBOOLE_0.misses Y1 X := fun hall => hnot ⟨Y, hYX, hall⟩
      exact Classical.byContradiction fun hne =>
        this fun Y1 Y2 Y3 h12 h23 h3Y =>
          XBOOLE_0.misses_of fun hm => hne ⟨Y1, Y2, Y3, h12, h23, h3Y, hm⟩
    have hY3U : Y3 ∈ union X := (union_iff _ _).mpr ⟨Y, h3Y, hYX⟩
    have hY3Z1 : Y3 ∈ Z1 :=
      (hZ1 Y3).mpr ⟨hY3U, ⟨Y1, Y2, h12, h23, hmeet⟩⟩
    exact miss_contra h3Y (mem_union_left (mem_union_left (mem_union_right hY3Z1)))
      hmiss
  have hRest : Y ∈ Z1 ∪ Z2 ∪ Z3 := by
    have : Y ∈ X ∪ (Z1 ∪ Z2 ∪ Z3) := hVeq ▸ hY
    rcases (mem_union (A := X) (B := Z1 ∪ Z2 ∪ Z3) (x := Y)).mp this with h | h
    · exact (notX h).elim
    · exact h
  have hRest' : Y ∈ Z1 ∪ (Z2 ∪ Z3) := by
    rw [union_assoc] at hRest
    exact hRest
  have hZ23 : Y ∈ Z2 ∪ Z3 := by
    rcases (mem_union (A := Z1) (B := Z2 ∪ Z3) (x := Y)).mp hRest' with h | h
    · exact (notZ1 h).elim
    · exact h
  have hYZ3 : Y ∈ Z3 := by
    rcases (mem_union (A := Z2) (B := Z3) (x := Y)).mp hZ23 with h | h
    · exact (notZ2 h).elim
    · exact h
  have hmeet : XBOOLE_0.meets Y X := ((hZ3 Y).mp hYZ3).2
  exact (hVeq ▸ meets_union_left (C := Z1 ∪ Z2 ∪ Z3) hmeet) hmiss

/-- Depth-4 regularity. -/
theorem th5 {X : TarskiSet.{u}} (hX : ¬ XBOOLE_0.isEmpty X) :
    ∃ Y, Y ∈ X ∧
      ∀ Y1 Y2 Y3 Y4, Y1 ∈ Y2 → Y2 ∈ Y3 → Y3 ∈ Y4 → Y4 ∈ Y →
        XBOOLE_0.misses Y1 X := by
  obtain ⟨Z1, hZ1⟩ :=
    XBOOLE_0.sch_separation (union X)
      (fun Y => ∃ Y1 Y2 Y3, Y1 ∈ Y2 ∧ Y2 ∈ Y3 ∧ Y3 ∈ Y ∧ XBOOLE_0.meets Y1 X)
  obtain ⟨Z2, hZ2⟩ :=
    XBOOLE_0.sch_separation (union (union X))
      (fun Y => ∃ Y1 Y2, Y1 ∈ Y2 ∧ Y2 ∈ Y ∧ XBOOLE_0.meets Y1 X)
  obtain ⟨Z4, hZ4⟩ :=
    XBOOLE_0.sch_separation (union (union (union (union X))))
      (fun Y => XBOOLE_0.meets Y X)
  obtain ⟨Z3, hZ3⟩ :=
    XBOOLE_0.sch_separation (union (union (union X)))
      (fun Y => ∃ Y1, Y1 ∈ Y ∧ XBOOLE_0.meets Y1 X)
  let V := X ∪ Z1 ∪ Z2 ∪ Z3 ∪ Z4
  have hVne : ¬ XBOOLE_0.isEmpty V :=
    XBOOLE_0.union_nonempty_left (XBOOLE_0.union_nonempty_left
      (XBOOLE_0.union_nonempty_left (XBOOLE_0.union_nonempty_left hX)))
  obtain ⟨Y, hY, hmiss⟩ := th1 hVne
  have notZ3 : Y ∉ Z3 := by
    intro hYZ3
    obtain ⟨Y1, hY1Y, hmeet⟩ := ((hZ3 Y).mp hYZ3).2
    have hYU : Y ∈ union (union (union X)) := ((hZ3 Y).mp hYZ3).1
    have hY1U : Y1 ∈ union (union (union (union X))) :=
      (union_iff _ _).mpr ⟨Y, hY1Y, hYU⟩
    have hY1Z4 : Y1 ∈ Z4 := (hZ4 Y1).mpr ⟨hY1U, hmeet⟩
    exact miss_contra hY1Y (mem_union_right hY1Z4) hmiss
  have notZ1 : Y ∉ Z1 := by
    intro hYZ1
    obtain ⟨Y1, Y2, Y3, h12, h23, h3Y, hmeet⟩ := ((hZ1 Y).mp hYZ1).2
    have hYU : Y ∈ union X := ((hZ1 Y).mp hYZ1).1
    have hY3U : Y3 ∈ union (union X) :=
      (union_iff _ _).mpr ⟨Y, h3Y, hYU⟩
    have hY3Z2 : Y3 ∈ Z2 :=
      (hZ2 Y3).mpr ⟨hY3U, ⟨Y1, Y2, h12, h23, hmeet⟩⟩
    have : XBOOLE_0.meets Y (X ∪ Z1 ∪ Z2) :=
      meets_of_mem h3Y (mem_union_right hY3Z2)
    exact (meets_union_left (C := Z4) (meets_union_left (C := Z3) this)) hmiss
  have hVeq : V = X ∪ (Z1 ∪ Z2 ∪ Z3 ∪ Z4) := by
    change X ∪ Z1 ∪ Z2 ∪ Z3 ∪ Z4 = X ∪ (Z1 ∪ Z2 ∪ Z3 ∪ Z4)
    rw [union_assoc X Z1 Z2, union_assoc X (Z1 ∪ Z2) Z3,
      union_assoc X (Z1 ∪ Z2 ∪ Z3) Z4]
  have notZ2 : Y ∉ Z2 := by
    intro hYZ2
    obtain ⟨Y1, Y2, h12, h2Y, hmeet⟩ := ((hZ2 Y).mp hYZ2).2
    have hYU : Y ∈ union (union X) := ((hZ2 Y).mp hYZ2).1
    have hY2U : Y2 ∈ union (union (union X)) :=
      (union_iff _ _).mpr ⟨Y, h2Y, hYU⟩
    have hY2Z3 : Y2 ∈ Z3 := (hZ3 Y2).mpr ⟨hY2U, ⟨Y1, h12, hmeet⟩⟩
    have : XBOOLE_0.meets Y (X ∪ Z1 ∪ Z2 ∪ Z3) :=
      meets_of_mem h2Y (mem_union_right hY2Z3)
    exact meets_union_left (C := Z4) this hmiss
  refine Classical.byContradiction fun hnot => ?_
  have notX : Y ∉ X := by
    intro hYX
    have ⟨Y1, Y2, Y3, Y4, h12, h23, h34, h4Y, hmeet⟩ :
        ∃ Y1 Y2 Y3 Y4, Y1 ∈ Y2 ∧ Y2 ∈ Y3 ∧ Y3 ∈ Y4 ∧ Y4 ∈ Y ∧
          ¬ XBOOLE_0.misses Y1 X := by
      have : ¬ ∀ Y1 Y2 Y3 Y4, Y1 ∈ Y2 → Y2 ∈ Y3 → Y3 ∈ Y4 → Y4 ∈ Y →
          XBOOLE_0.misses Y1 X := fun hall => hnot ⟨Y, hYX, hall⟩
      exact Classical.byContradiction fun hne =>
        this fun Y1 Y2 Y3 Y4 h12 h23 h34 h4Y =>
          XBOOLE_0.misses_of fun hm =>
            hne ⟨Y1, Y2, Y3, Y4, h12, h23, h34, h4Y, hm⟩
    have hY4U : Y4 ∈ union X := (union_iff _ _).mpr ⟨Y, h4Y, hYX⟩
    have hY4Z1 : Y4 ∈ Z1 :=
      (hZ1 Y4).mpr ⟨hY4U, ⟨Y1, Y2, Y3, h12, h23, h34, hmeet⟩⟩
    exact miss_contra h4Y
      (mem_union_left (mem_union_left (mem_union_left (mem_union_right hY4Z1))))
      hmiss
  have hRest : Y ∈ Z1 ∪ Z2 ∪ Z3 ∪ Z4 := by
    have : Y ∈ X ∪ (Z1 ∪ Z2 ∪ Z3 ∪ Z4) := hVeq ▸ hY
    rcases (mem_union (A := X) (B := Z1 ∪ Z2 ∪ Z3 ∪ Z4) (x := Y)).mp this with
      h | h
    · exact (notX h).elim
    · exact h
  have h1234 : Y ∈ Z1 ∪ (Z2 ∪ Z3 ∪ Z4) := by
    have h1 : Y ∈ Z1 ∪ (Z2 ∪ Z3) ∪ Z4 := by
      rw [union_assoc (A := Z1) (B := Z2) (C := Z3)] at hRest
      exact hRest
    rw [union_assoc] at h1
    exact h1
  have h234 : Y ∈ Z2 ∪ Z3 ∪ Z4 := by
    rcases (mem_union (A := Z1) (B := Z2 ∪ Z3 ∪ Z4) (x := Y)).mp h1234 with h | h
    · exact (notZ1 h).elim
    · exact h
  have h234' : Y ∈ Z2 ∪ (Z3 ∪ Z4) := by
    rw [union_assoc] at h234
    exact h234
  have h34 : Y ∈ Z3 ∪ Z4 := by
    rcases (mem_union (A := Z2) (B := Z3 ∪ Z4) (x := Y)).mp h234' with h | h
    · exact (notZ2 h).elim
    · exact h
  have hYZ4 : Y ∈ Z4 := by
    rcases (mem_union (A := Z3) (B := Z4) (x := Y)).mp h34 with h | h
    · exact (notZ3 h).elim
    · exact h
  have hmeet : XBOOLE_0.meets Y X := ((hZ4 Y).mp hYZ4).2
  exact (hVeq ▸ meets_union_left (C := Z1 ∪ Z2 ∪ Z3 ∪ Z4) hmeet) hmiss

/-- Depth-5 regularity. -/
theorem th6 {X : TarskiSet.{u}} (hX : ¬ XBOOLE_0.isEmpty X) :
    ∃ Y, Y ∈ X ∧
      ∀ Y1 Y2 Y3 Y4 Y5, Y1 ∈ Y2 → Y2 ∈ Y3 → Y3 ∈ Y4 → Y4 ∈ Y5 → Y5 ∈ Y →
        XBOOLE_0.misses Y1 X := by
  obtain ⟨Z1, hZ1⟩ :=
    XBOOLE_0.sch_separation (union X)
      (fun Y => ∃ Y1 Y2 Y3 Y4,
        Y1 ∈ Y2 ∧ Y2 ∈ Y3 ∧ Y3 ∈ Y4 ∧ Y4 ∈ Y ∧ XBOOLE_0.meets Y1 X)
  obtain ⟨Z2, hZ2⟩ :=
    XBOOLE_0.sch_separation (union (union X))
      (fun Y => ∃ Y1 Y2 Y3, Y1 ∈ Y2 ∧ Y2 ∈ Y3 ∧ Y3 ∈ Y ∧ XBOOLE_0.meets Y1 X)
  obtain ⟨Z5, hZ5⟩ :=
    XBOOLE_0.sch_separation (union (union (union (union (union X)))))
      (fun Y => XBOOLE_0.meets Y X)
  obtain ⟨Z3, hZ3⟩ :=
    XBOOLE_0.sch_separation (union (union (union X)))
      (fun Y => ∃ Y1 Y2, Y1 ∈ Y2 ∧ Y2 ∈ Y ∧ XBOOLE_0.meets Y1 X)
  obtain ⟨Z4, hZ4⟩ :=
    XBOOLE_0.sch_separation (union (union (union (union X))))
      (fun Y => ∃ Y1, Y1 ∈ Y ∧ XBOOLE_0.meets Y1 X)
  let V := X ∪ Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ Z5
  have hVne : ¬ XBOOLE_0.isEmpty V :=
    XBOOLE_0.union_nonempty_left (XBOOLE_0.union_nonempty_left
      (XBOOLE_0.union_nonempty_left (XBOOLE_0.union_nonempty_left
        (XBOOLE_0.union_nonempty_left hX))))
  obtain ⟨Y, hY, hmiss⟩ := th1 hVne
  have hVeq : V = X ∪ (Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ Z5) := by
    change X ∪ Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ Z5 = X ∪ (Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ Z5)
    rw [union_assoc X Z1 Z2, union_assoc X (Z1 ∪ Z2) Z3,
      union_assoc X (Z1 ∪ Z2 ∪ Z3) Z4, union_assoc X (Z1 ∪ Z2 ∪ Z3 ∪ Z4) Z5]
  have notZ1 : Y ∉ Z1 := by
    intro hYZ1
    obtain ⟨Y1, Y2, Y3, Y4, h12, h23, h34, h4Y, hmeet⟩ :=
      ((hZ1 Y).mp hYZ1).2
    have hYU : Y ∈ union X := ((hZ1 Y).mp hYZ1).1
    have hY4U : Y4 ∈ union (union X) :=
      (union_iff _ _).mpr ⟨Y, h4Y, hYU⟩
    have hY4Z2 : Y4 ∈ Z2 :=
      (hZ2 Y4).mpr ⟨hY4U, ⟨Y1, Y2, Y3, h12, h23, h34, hmeet⟩⟩
    have : XBOOLE_0.meets Y (X ∪ Z1 ∪ Z2) :=
      meets_of_mem h4Y (mem_union_right hY4Z2)
    exact (meets_union_left (C := Z5)
      (meets_union_left (C := Z4) (meets_union_left (C := Z3) this))) hmiss
  have notZ2 : Y ∉ Z2 := by
    intro hYZ2
    obtain ⟨Y1, Y2, Y3, h12, h23, h3Y, hmeet⟩ := ((hZ2 Y).mp hYZ2).2
    have hYU : Y ∈ union (union X) := ((hZ2 Y).mp hYZ2).1
    have hY3U : Y3 ∈ union (union (union X)) :=
      (union_iff _ _).mpr ⟨Y, h3Y, hYU⟩
    have hY3Z3 : Y3 ∈ Z3 :=
      (hZ3 Y3).mpr ⟨hY3U, ⟨Y1, Y2, h12, h23, hmeet⟩⟩
    exact miss_contra h3Y
      (mem_union_left (mem_union_left (mem_union_right hY3Z3))) hmiss
  have notZ3 : Y ∉ Z3 := by
    intro hYZ3
    obtain ⟨Y1, Y2, h12, h2Y, hmeet⟩ := ((hZ3 Y).mp hYZ3).2
    have hYU : Y ∈ union (union (union X)) := ((hZ3 Y).mp hYZ3).1
    have hY2U : Y2 ∈ union (union (union (union X))) :=
      (union_iff _ _).mpr ⟨Y, h2Y, hYU⟩
    have hY2Z4 : Y2 ∈ Z4 := (hZ4 Y2).mpr ⟨hY2U, ⟨Y1, h12, hmeet⟩⟩
    exact miss_contra h2Y (mem_union_left (mem_union_right hY2Z4)) hmiss
  have notZ4 : Y ∉ Z4 := by
    intro hYZ4
    obtain ⟨Y1, hY1Y, hmeet⟩ := ((hZ4 Y).mp hYZ4).2
    have hYU : Y ∈ union (union (union (union X))) := ((hZ4 Y).mp hYZ4).1
    have hY1U : Y1 ∈ union (union (union (union (union X)))) :=
      (union_iff _ _).mpr ⟨Y, hY1Y, hYU⟩
    have hY1Z5 : Y1 ∈ Z5 := (hZ5 Y1).mpr ⟨hY1U, hmeet⟩
    exact miss_contra hY1Y (mem_union_right hY1Z5) hmiss
  refine Classical.byContradiction fun hnot => ?_
  have notX : Y ∉ X := by
    intro hYX
    have ⟨Y1, Y2, Y3, Y4, Y5, h12, h23, h34, h45, h5Y, hmeet⟩ :
        ∃ Y1 Y2 Y3 Y4 Y5, Y1 ∈ Y2 ∧ Y2 ∈ Y3 ∧ Y3 ∈ Y4 ∧ Y4 ∈ Y5 ∧ Y5 ∈ Y ∧
          ¬ XBOOLE_0.misses Y1 X := by
      have : ¬ ∀ Y1 Y2 Y3 Y4 Y5,
          Y1 ∈ Y2 → Y2 ∈ Y3 → Y3 ∈ Y4 → Y4 ∈ Y5 → Y5 ∈ Y →
            XBOOLE_0.misses Y1 X := fun hall => hnot ⟨Y, hYX, hall⟩
      exact Classical.byContradiction fun hne =>
        this fun Y1 Y2 Y3 Y4 Y5 h12 h23 h34 h45 h5Y =>
          XBOOLE_0.misses_of fun hm =>
            hne ⟨Y1, Y2, Y3, Y4, Y5, h12, h23, h34, h45, h5Y, hm⟩
    have hY5U : Y5 ∈ union X := (union_iff _ _).mpr ⟨Y, h5Y, hYX⟩
    have hY5Z1 : Y5 ∈ Z1 :=
      (hZ1 Y5).mpr ⟨hY5U, ⟨Y1, Y2, Y3, Y4, h12, h23, h34, h45, hmeet⟩⟩
    have : XBOOLE_0.meets Y (X ∪ Z1 ∪ Z2 ∪ Z3) :=
      meets_of_mem h5Y (mem_union_left (mem_union_left (mem_union_right hY5Z1)))
    exact (meets_union_left (C := Z5) (meets_union_left (C := Z4) this)) hmiss
  have hRest : Y ∈ Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ Z5 := by
    have : Y ∈ X ∪ (Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ Z5) := hVeq ▸ hY
    rcases (mem_union (A := X) (B := Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ Z5) (x := Y)).mp this
      with h | h
    · exact (notX h).elim
    · exact h
  have h1 : Y ∈ Z1 ∪ (Z2 ∪ Z3 ∪ Z4 ∪ Z5) := by
    have h' : Y ∈ (Z1 ∪ (Z2 ∪ Z3)) ∪ Z4 ∪ Z5 :=
      union_assoc Z1 Z2 Z3 ▸ hRest
    have h'' : Y ∈ (Z1 ∪ ((Z2 ∪ Z3) ∪ Z4)) ∪ Z5 :=
      union_assoc Z1 (Z2 ∪ Z3) Z4 ▸ h'
    exact union_assoc Z1 ((Z2 ∪ Z3) ∪ Z4) Z5 ▸ h''
  have h2345 : Y ∈ Z2 ∪ Z3 ∪ Z4 ∪ Z5 := by
    rcases (mem_union (A := Z1) (B := Z2 ∪ Z3 ∪ Z4 ∪ Z5) (x := Y)).mp h1 with
      h | h
    · exact (notZ1 h).elim
    · exact h
  have h2 : Y ∈ Z2 ∪ (Z3 ∪ Z4 ∪ Z5) := by
    have h' : Y ∈ Z2 ∪ (Z3 ∪ Z4) ∪ Z5 := by
      rw [union_assoc (A := Z2) (B := Z3) (C := Z4)] at h2345; exact h2345
    rw [union_assoc] at h'; exact h'
  have h345 : Y ∈ Z3 ∪ Z4 ∪ Z5 := by
    rcases (mem_union (A := Z2) (B := Z3 ∪ Z4 ∪ Z5) (x := Y)).mp h2 with h | h
    · exact (notZ2 h).elim
    · exact h
  have h3 : Y ∈ Z3 ∪ (Z4 ∪ Z5) := by
    rw [union_assoc] at h345; exact h345
  have h45 : Y ∈ Z4 ∪ Z5 := by
    rcases (mem_union (A := Z3) (B := Z4 ∪ Z5) (x := Y)).mp h3 with h | h
    · exact (notZ3 h).elim
    · exact h
  have hYZ5 : Y ∈ Z5 := by
    rcases (mem_union (A := Z4) (B := Z5) (x := Y)).mp h45 with h | h
    · exact (notZ4 h).elim
    · exact h
  have hmeet : XBOOLE_0.meets Y X := ((hZ5 Y).mp hYZ5).2
  exact (hVeq ▸ meets_union_left (C := Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ Z5) hmeet) hmiss

/-- No 3-cycle. -/
theorem th7 {X1 X2 X3 : TarskiSet.{u}} :
    ¬ (X1 ∈ X2 ∧ X2 ∈ X3 ∧ X3 ∈ X1) := by
  intro ⟨h12, h23, h31⟩
  let S := ENUMSET1.enumset3 X1 X2 X3
  have h1 : X1 ∈ S := (ENUMSET1.def1 X1 X2 X3 X1).mpr (Or.inl rfl)
  have h2 : X2 ∈ S := (ENUMSET1.def1 X1 X2 X3 X2).mpr (Or.inr (Or.inl rfl))
  have h3 : X3 ∈ S := (ENUMSET1.def1 X1 X2 X3 X3).mpr (Or.inr (Or.inr rfl))
  have hS : ¬ XBOOLE_0.isEmpty S := fun hempty => hempty ⟨X1, h1⟩
  obtain ⟨T, hT, hmiss⟩ := th1 hS
  rcases (ENUMSET1.def1 X1 X2 X3 T).mp hT with h | h | h
  · exact miss_contra (h.symm ▸ h31) h3 hmiss
  · exact miss_contra (h.symm ▸ h12) h1 hmiss
  · exact miss_contra (h.symm ▸ h23) h2 hmiss

/-- No 4-cycle. -/
theorem th8 {X1 X2 X3 X4 : TarskiSet.{u}} :
    ¬ (X1 ∈ X2 ∧ X2 ∈ X3 ∧ X3 ∈ X4 ∧ X4 ∈ X1) := by
  intro ⟨h12, h23, h34, h41⟩
  let S := ENUMSET1.enumset4 X1 X2 X3 X4
  have h1 : X1 ∈ S := (ENUMSET1.def2 X1 X2 X3 X4 X1).mpr (Or.inl rfl)
  have h2 : X2 ∈ S :=
    (ENUMSET1.def2 X1 X2 X3 X4 X2).mpr (Or.inr (Or.inl rfl))
  have h3 : X3 ∈ S :=
    (ENUMSET1.def2 X1 X2 X3 X4 X3).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : X4 ∈ S :=
    (ENUMSET1.def2 X1 X2 X3 X4 X4).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hS : ¬ XBOOLE_0.isEmpty S := fun hempty => hempty ⟨X1, h1⟩
  obtain ⟨T, hT, hmiss⟩ := th1 hS
  rcases (ENUMSET1.def2 X1 X2 X3 X4 T).mp hT with h | h | h | h
  · exact miss_contra (h.symm ▸ h41) h4 hmiss
  · exact miss_contra (h.symm ▸ h12) h1 hmiss
  · exact miss_contra (h.symm ▸ h23) h2 hmiss
  · exact miss_contra (h.symm ▸ h34) h3 hmiss

/-- No 5-cycle. -/
theorem th9 {X1 X2 X3 X4 X5 : TarskiSet.{u}} :
    ¬ (X1 ∈ X2 ∧ X2 ∈ X3 ∧ X3 ∈ X4 ∧ X4 ∈ X5 ∧ X5 ∈ X1) := by
  intro ⟨h12, h23, h34, h45, h51⟩
  let S := ENUMSET1.enumset5 X1 X2 X3 X4 X5
  have memS : ∀ x, x = X1 ∨ x = X2 ∨ x = X3 ∨ x = X4 ∨ x = X5 → x ∈ S :=
    fun x hx => (ENUMSET1.def3 X1 X2 X3 X4 X5 x).mpr hx
  have h1 : X1 ∈ S := memS X1 (Or.inl rfl)
  have hall : ∀ Y, Y ∈ S → XBOOLE_0.meets S Y := by
    intro Y hY
    rcases (ENUMSET1.def3 X1 X2 X3 X4 X5 Y).mp hY with h | h | h | h | h
    · exact (XBOOLE_0.th3 S Y).mpr ⟨X5,
        memS X5 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), h.symm ▸ h51⟩
    · exact (XBOOLE_0.th3 S Y).mpr ⟨X1, h1, h.symm ▸ h12⟩
    · exact (XBOOLE_0.th3 S Y).mpr ⟨X2, memS X2 (Or.inr (Or.inl rfl)),
        h.symm ▸ h23⟩
    · exact (XBOOLE_0.th3 S Y).mpr ⟨X3, memS X3 (Or.inr (Or.inr (Or.inl rfl))),
        h.symm ▸ h34⟩
    · exact (XBOOLE_0.th3 S Y).mpr ⟨X4,
        memS X4 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h.symm ▸ h45⟩
  have hS : ¬ XBOOLE_0.isEmpty S := fun hempty => hempty ⟨X1, h1⟩
  obtain ⟨T, hT, hmiss⟩ := th1 hS
  exact hall T hT (XBOOLE_0.misses_symm hmiss)

/-- No 6-cycle. -/
theorem th10 {X1 X2 X3 X4 X5 X6 : TarskiSet.{u}} :
    ¬ (X1 ∈ X2 ∧ X2 ∈ X3 ∧ X3 ∈ X4 ∧ X4 ∈ X5 ∧ X5 ∈ X6 ∧ X6 ∈ X1) := by
  intro ⟨h12, h23, h34, h45, h56, h61⟩
  let S := ENUMSET1.enumset6 X1 X2 X3 X4 X5 X6
  have memS : ∀ x,
      x = X1 ∨ x = X2 ∨ x = X3 ∨ x = X4 ∨ x = X5 ∨ x = X6 → x ∈ S :=
    fun x hx => (ENUMSET1.def4 X1 X2 X3 X4 X5 X6 x).mpr hx
  have h1 : X1 ∈ S := memS X1 (Or.inl rfl)
  have hall : ∀ Y, Y ∈ S → XBOOLE_0.meets S Y := by
    intro Y hY
    rcases (ENUMSET1.def4 X1 X2 X3 X4 X5 X6 Y).mp hY with h | h | h | h | h | h
    · exact (XBOOLE_0.th3 S Y).mpr ⟨X6,
        memS X6 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), h.symm ▸ h61⟩
    · exact (XBOOLE_0.th3 S Y).mpr ⟨X1, h1, h.symm ▸ h12⟩
    · exact (XBOOLE_0.th3 S Y).mpr ⟨X2, memS X2 (Or.inr (Or.inl rfl)),
        h.symm ▸ h23⟩
    · exact (XBOOLE_0.th3 S Y).mpr ⟨X3, memS X3 (Or.inr (Or.inr (Or.inl rfl))),
        h.symm ▸ h34⟩
    · exact (XBOOLE_0.th3 S Y).mpr ⟨X4,
        memS X4 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h.symm ▸ h45⟩
    · exact (XBOOLE_0.th3 S Y).mpr ⟨X5,
        memS X5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), h.symm ▸ h56⟩
  have hS : ¬ XBOOLE_0.isEmpty S := fun hempty => hempty ⟨X1, h1⟩
  obtain ⟨T, hT, hmiss⟩ := th1 hS
  exact hall T hT (XBOOLE_0.misses_symm hmiss)

end XREGULAR
