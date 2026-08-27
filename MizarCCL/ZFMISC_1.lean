import MizarCCL.XREGULAR
import MizarCCL.XTUPLE_0

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/zfmisc_1.miz`.
Authors: Czesław Byliński (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Some basic properties of sets

1–1 Lean rendering of Mizar article `ZFMISC_1`
(`vendor/mml/zfmisc_1.miz`). Power set is the Aczel family of
subsets (same universe). Cartesian product is Separation on
`bool (bool (X ∪ Y))` as in the article. Mizar `ZFMISC_1:27` is
canceled and omitted.
-/

universe u

open TarskiSet TARSKI

namespace ZFMISC_1

variable {x x1 x2 x3 y y1 y2 y3 z A B X X1 X2 X3 X4 Y Y1 Y2 Y3 Z N M : TarskiSet.{u}}

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

/-- Lean 4.33 Init has no `Or.assoc`. -/
@[simp] private theorem or_assoc {p q r : Prop} : (p ∨ q) ∨ r ↔ p ∨ q ∨ r :=
  ⟨fun h => h.elim (fun h => h.elim Or.inl (fun hq => Or.inr (Or.inl hq)))
      (fun hr => Or.inr (Or.inr hr)),
    fun h => h.elim (fun hp => Or.inl (Or.inl hp))
      (fun h => h.elim (fun hq => Or.inl (Or.inr hq)) Or.inr)⟩

private theorem union_assoc (A B C : TarskiSet.{u}) :
    (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
  XBOOLE_1.th4 (X := A) (Y := B) (Z := C)

/-! ## Lm1–Lm3 -/

theorem lm1 : TARSKI.singleton x ⊆ X ↔ x ∈ X := by
  constructor
  · intro h
    exact h x ((singleton_iff x x).mpr rfl)
  · intro hx w hw
    exact (singleton_iff x w).mp hw ▸ hx

theorem lm2 (hYX : Y ⊆ X) (hx : x ∉ Y) : Y ⊆ X \ TARSKI.singleton x := by
  intro w hw
  exact (XBOOLE_0.def5 X (TARSKI.singleton x) w).mpr
    ⟨hYX w hw, fun hs => hx ((singleton_iff x w).mp hs ▸ hw)⟩

theorem lm3 : Y ⊆ TARSKI.singleton x ↔
    Y = (∅ : TarskiSet.{u}) ∨ Y = TARSKI.singleton x := by
  constructor
  · intro hY
    by_cases hx : x ∈ Y
    · exact Or.inr <|
        XBOOLE_0.eq_iff_subset.mpr ⟨hY, (lm1 (x := x) (X := Y)).mpr hx⟩
    · have hsub : Y ⊆ TARSKI.singleton x \ TARSKI.singleton x := lm2 hY hx
      have hempty : TARSKI.singleton x \ TARSKI.singleton x =
          (∅ : TarskiSet.{u}) :=
        (XBOOLE_1.th37 (X := TARSKI.singleton x) (Y := TARSKI.singleton x)).mpr
          (subset_refl _)
      exact Or.inl (XBOOLE_1.th3 (hempty ▸ hsub))
  · intro h
    cases h with
    | inl h => exact h ▸ XBOOLE_1.th2
    | inr h => exact h ▸ subset_refl _

/-! ## bool X (`ZFMISC_1:def 1`) -/

def boolPre : PreSet.{u} → PreSet.{u}
  | .mk α A => .mk (α → Prop) fun P =>
      .mk { a : α // P a } fun ⟨a, _⟩ => A a

theorem boolPre_equiv {p q : PreSet.{u}} (h : PreSet.Equiv p q) :
    PreSet.Equiv (boolPre p) (boolPre q) := by
  cases p with
  | mk α A =>
    cases q with
    | mk β B =>
      constructor
      · intro P
        refine ⟨fun b => ∃ a, P a ∧ PreSet.Equiv (A a) (B b), ?_⟩
        constructor
        · intro ⟨a, haP⟩
          obtain ⟨b, hab⟩ := h.1 a
          exact ⟨⟨b, ⟨a, haP, hab⟩⟩, hab⟩
        · intro ⟨b, a, haP, hab⟩
          exact ⟨⟨a, haP⟩, hab⟩
      · intro Q
        refine ⟨fun a => ∃ b, Q b ∧ PreSet.Equiv (A a) (B b), ?_⟩
        constructor
        · intro ⟨a, b, hbQ, hab⟩
          exact ⟨⟨b, hbQ⟩, hab⟩
        · intro ⟨b, hbQ⟩
          obtain ⟨a, hab⟩ := h.2 b
          exact ⟨⟨a, ⟨b, hbQ, hab⟩⟩, hab⟩

def bool (X : TarskiSet.{u}) : TarskiSet.{u} :=
  Quotient.liftOn X (fun p => mk (boolPre p)) fun _ _ h =>
    sound (boolPre_equiv h)

theorem bool_mk (p : PreSet.{u}) : bool (mk p) = mk (boolPre p) :=
  rfl

/-- `ZFMISC_1:def 1`. -/
theorem def1 (X Z : TarskiSet.{u}) : Z ∈ bool X ↔ Z ⊆ X := by
  refine inductionOn₂ (β := fun X Z => Z ∈ bool X ↔ Z ⊆ X) X Z fun p q => ?_
  cases p with
  | mk α A =>
    cases q with
    | mk β B =>
      rw [bool_mk]
      constructor
      · intro hZ
        obtain ⟨P, hEq⟩ := (mem_mk_iff (.mk β B) (boolPre (.mk α A))).mp hZ
        intro w hw
        refine inductionOn (β := fun w => w ∈ mk (.mk β B) → w ∈ mk (.mk α A))
          w (fun s hs => ?_) hw
        have hs' : PreSet.Mem s (.mk β B) := (mem_mk_iff s (.mk β B)).mp hs
        have hsA : PreSet.Mem s (.mk { a : α // P a } fun ⟨a, _⟩ => A a) :=
          PreSet.mem_congr_right hEq hs'
        obtain ⟨⟨a, _⟩, ha⟩ := hsA
        exact (mem_mk_iff s (.mk α A)).mpr ⟨a, ha⟩
      · intro hsub
        let P : α → Prop := fun a => ∃ b, PreSet.Equiv (B b) (A a)
        refine (mem_mk_iff (.mk β B) (boolPre (.mk α A))).mpr ⟨P, ?_⟩
        constructor
        · intro b
          have hbZ : mk (B b) ∈ mk (.mk β B) :=
            (mem_mk_iff (B b) (.mk β B)).mpr ⟨b, PreSet.equiv_refl _⟩
          have hbX : mk (B b) ∈ mk (.mk α A) := hsub _ hbZ
          obtain ⟨a, ha⟩ := (mem_mk_iff (B b) (.mk α A)).mp hbX
          exact ⟨⟨a, ⟨b, ha⟩⟩, ha⟩
        · intro ⟨a, b, hab⟩
          exact ⟨b, hab⟩

/-! ## Cartesian product (`ZFMISC_1:def 2`) -/

theorem pair_mem_bbool {x y X1 X2 : TarskiSet.{u}}
    (hx : x ∈ X1) (hy : y ∈ X2) :
    TARSKI.pair x y ∈ bool (bool (X1 ∪ X2)) := by
  have hxU : x ∈ X1 ∪ X2 := (XBOOLE_0.def3 X1 X2 x).mpr (Or.inl hx)
  have hyU : y ∈ X1 ∪ X2 := (XBOOLE_0.def3 X1 X2 y).mpr (Or.inr hy)
  have hxy : upair x y ⊆ X1 ∪ X2 := by
    intro w hw
    rcases (upair_iff x y w).mp hw with h | h
    · exact h ▸ hxU
    · exact h ▸ hyU
  have hs : TARSKI.singleton x ⊆ X1 ∪ X2 :=
    (lm1 (x := x) (X := X1 ∪ X2)).mpr hxU
  have hxyB : upair x y ∈ bool (X1 ∪ X2) := (def1 _ _).mpr hxy
  have hsB : TARSKI.singleton x ∈ bool (X1 ∪ X2) := (def1 _ _).mpr hs
  have hpair : TARSKI.pair x y ⊆ bool (X1 ∪ X2) := by
    intro w hw
    rcases (upair_iff (upair x y) (TARSKI.singleton x) w).mp hw with h | h
    · exact h ▸ hxyB
    · exact h ▸ hsB
  exact (def1 _ _).mpr hpair

noncomputable def product (X1 X2 : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose <|
    XBOOLE_0.sch_separation (bool (bool (X1 ∪ X2)))
      (fun z => ∃ x y, x ∈ X1 ∧ y ∈ X2 ∧ z = TARSKI.pair x y)

theorem product_sep (X1 X2 z : TarskiSet.{u}) :
    z ∈ product X1 X2 ↔
      z ∈ bool (bool (X1 ∪ X2)) ∧
        ∃ x y, x ∈ X1 ∧ y ∈ X2 ∧ z = TARSKI.pair x y :=
  Classical.choose_spec
    (XBOOLE_0.sch_separation (bool (bool (X1 ∪ X2)))
      (fun z => ∃ x y, x ∈ X1 ∧ y ∈ X2 ∧ z = TARSKI.pair x y)) z

/-- `ZFMISC_1:def 2`. -/
theorem def2 (X1 X2 z : TarskiSet.{u}) :
    z ∈ product X1 X2 ↔ ∃ x y, x ∈ X1 ∧ y ∈ X2 ∧ z = TARSKI.pair x y := by
  constructor
  · intro h
    exact (product_sep X1 X2 z).mp h |>.2
  · intro ⟨x, y, hx, hy, hz⟩
    exact (product_sep X1 X2 z).mpr
      ⟨hz ▸ pair_mem_bbool hx hy, ⟨x, y, hx, hy, hz⟩⟩

noncomputable def product3 (X1 X2 X3 : TarskiSet.{u}) : TarskiSet.{u} :=
  product (product X1 X2) X3

noncomputable def product4 (X1 X2 X3 X4 : TarskiSet.{u}) : TarskiSet.{u} :=
  product (product3 X1 X2 X3) X4

/-! ## Empty set -/

/-- `ZFMISC_1:1` -/
theorem th1 : bool (∅ : TarskiSet.{u}) = TARSKI.singleton (∅ : TarskiSet.{u}) :=
  eq_of_mem fun y =>
    (def1 _ _).trans <|
      Iff.trans
        ⟨fun h => XBOOLE_1.th3 h,
          fun heq => heq ▸ subset_refl (∅ : TarskiSet.{u})⟩
        (singleton_iff (∅ : TarskiSet.{u}) y).symm

/-- `ZFMISC_1:2` -/
theorem th2 : union (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}) := by
  apply XBOOLE_0.empty_eq
  intro ⟨x, hx⟩
  obtain ⟨_, _, hY⟩ := (union_iff _ _).mp hx
  exact (XBOOLE_0.empty_iff _).mp hY

/-! ## Singleton and unordered pairs -/

/-- `ZFMISC_1:3` (`Th3`) -/
theorem th3 (h : TARSKI.singleton x ⊆ TARSKI.singleton y) : x = y := by
  have : TARSKI.singleton x = TARSKI.singleton y := by
    cases (lm3 (Y := TARSKI.singleton x) (x := y)).mp h with
    | inl hempty =>
      exact ((XBOOLE_0.empty_iff x).mp
        (hempty ▸ (singleton_iff x x).mpr rfl)).elim
    | inr heq => exact heq
  exact (singleton_iff y x).mp (this ▸ (singleton_iff x x).mpr rfl)

/-- `ZFMISC_1:4` (`Th4`) -/
theorem th4 (h : TARSKI.singleton x = upair y1 y2) : x = y1 := by
  have : y1 ∈ TARSKI.singleton x :=
    h ▸ (upair_iff y1 y2 y1).mpr (Or.inl rfl)
  exact ((singleton_iff x y1).mp this).symm

/-- `ZFMISC_1:5` -/
theorem th5 (h : TARSKI.singleton x = upair y1 y2) : y1 = y2 := by
  have hy1 : y1 = x := (th4 h).symm
  have hy2 : y2 ∈ TARSKI.singleton x :=
    h ▸ (upair_iff y1 y2 y2).mpr (Or.inr rfl)
  exact hy1.trans ((singleton_iff x y2).mp hy2).symm

/-- `ZFMISC_1:6` (`Th6`) -/
theorem th6 (h : upair x1 x2 = upair y1 y2) : x1 = y1 ∨ x1 = y2 :=
  (upair_iff y1 y2 x1).mp (h ▸ (upair_iff x1 x2 x1).mpr (Or.inl rfl))

/-- `ZFMISC_1:7` (`Th7`) -/
theorem th7 : TARSKI.singleton x ⊆ upair x y := by
  intro z hz
  exact (upair_iff x y z).mpr (Or.inl ((singleton_iff x z).mp hz))

theorem lm4 (h : TARSKI.singleton x ∪ X ⊆ X) : x ∈ X :=
  h x ((XBOOLE_0.def3 (TARSKI.singleton x) X x).mpr
    (Or.inl ((singleton_iff x x).mpr rfl)))

/-- `ZFMISC_1:8` -/
theorem th8 (h : TARSKI.singleton x ∪ TARSKI.singleton y = TARSKI.singleton x) :
    x = y := by
  have hy : TARSKI.singleton y ⊆ TARSKI.singleton x ∪ TARSKI.singleton y :=
    fun z hz => (XBOOLE_0.def3 _ _ z).mpr (Or.inr hz)
  exact (th3 (h ▸ hy)).symm

/-- `ZFMISC_1:9` -/
theorem th9 : TARSKI.singleton x ∪ upair x y = upair x y :=
  XBOOLE_1.th12 (X := TARSKI.singleton x) (Y := upair x y) th7

theorem lm6 (h : XBOOLE_0.misses (TARSKI.singleton x) X) : x ∉ X := by
  intro hx
  exact (XBOOLE_0.empty_iff x).mp
    (h ▸ (XBOOLE_0.def4 (TARSKI.singleton x) X x).mpr
      ⟨(singleton_iff x x).mpr rfl, hx⟩)

/-- `ZFMISC_1:10` -/
theorem th10 (h : XBOOLE_0.misses (TARSKI.singleton x) (TARSKI.singleton y)) :
    x ≠ y :=
  fun heq =>
    lm6 (x := y) (X := TARSKI.singleton y)
      (heq ▸ h) ((singleton_iff y y).mpr rfl)

theorem lm7 (hx : x ∉ X) : XBOOLE_0.misses (TARSKI.singleton x) X :=
  XBOOLE_0.empty_eq fun ⟨z, hz⟩ =>
    let ⟨hzs, hzX⟩ := (XBOOLE_0.def4 (TARSKI.singleton x) X z).mp hz
    hx ((singleton_iff x z).mp hzs ▸ hzX)

/-- `ZFMISC_1:11` (`Th11`) -/
theorem th11 (h : x ≠ y) :
    XBOOLE_0.misses (TARSKI.singleton x) (TARSKI.singleton y) :=
  lm7 (X := TARSKI.singleton y) (fun hy => h ((singleton_iff y x).mp hy))

theorem lm8 (h : X ∩ TARSKI.singleton x = TARSKI.singleton x) : x ∈ X := by
  have hx : x ∈ TARSKI.singleton x := (singleton_iff x x).mpr rfl
  have : x ∈ X ∩ TARSKI.singleton x := h.symm ▸ hx
  exact (XBOOLE_0.def4 X (TARSKI.singleton x) x).mp this |>.1

/-- `ZFMISC_1:12` -/
theorem th12 (h : TARSKI.singleton x ∩ TARSKI.singleton y = TARSKI.singleton x) :
    x = y :=
  (singleton_iff y x).mp
    (lm8 (X := TARSKI.singleton y)
      ((XBOOLE_0.inter_comm (TARSKI.singleton x) (TARSKI.singleton y)).symm.trans h))

theorem lm9 (hx : x ∈ X) : X ∩ TARSKI.singleton x = TARSKI.singleton x :=
  (XBOOLE_0.inter_comm X (TARSKI.singleton x)).trans
    (XBOOLE_1.th28 (X := TARSKI.singleton x) (Y := X)
      ((lm1 (x := x) (X := X)).mpr hx))

/-- `ZFMISC_1:13` -/
theorem th13 : TARSKI.singleton x ∩ upair x y = TARSKI.singleton x :=
  (XBOOLE_0.inter_comm (TARSKI.singleton x) (upair x y)).trans
    (lm9 (X := upair x y) ((upair_iff x y x).mpr (Or.inl rfl)))

theorem lm10 : TARSKI.singleton x \ X = TARSKI.singleton x ↔ x ∉ X :=
  (XBOOLE_1.th83 (X := TARSKI.singleton x) (Y := X)).symm.trans
    ⟨lm6, lm7⟩

/-- `ZFMISC_1:14` -/
theorem th14 : TARSKI.singleton x \ TARSKI.singleton y = TARSKI.singleton x ↔ x ≠ y :=
  (lm10 (X := TARSKI.singleton y)).trans
    ⟨fun hx hy => hx ((singleton_iff y x).mpr hy),
      fun hne hy => hne ((singleton_iff y x).mp hy)⟩

theorem lm11 : TARSKI.singleton x \ X = (∅ : TarskiSet.{u}) ↔ x ∈ X :=
  (XBOOLE_1.th37 (X := TARSKI.singleton x) (Y := X)).trans lm1

/-- `ZFMISC_1:15` -/
theorem th15 (h : TARSKI.singleton x \ TARSKI.singleton y = (∅ : TarskiSet.{u})) :
    x = y :=
  (singleton_iff y x).mp ((lm11 (X := TARSKI.singleton y)).mp h)

/-- `ZFMISC_1:16` -/
theorem th16 : TARSKI.singleton x \ upair x y = (∅ : TarskiSet.{u}) :=
  (lm11 (X := upair x y)).mpr ((upair_iff x y x).mpr (Or.inl rfl))

theorem lm12 :
    upair x y \ X = TARSKI.singleton x ↔ x ∉ X ∧ (y ∈ X ∨ x = y) := by
  constructor
  · intro h
    have hx : x ∉ X := by
      intro hx
      have : x ∈ upair x y \ X := h ▸ (singleton_iff x x).mpr rfl
      exact (XBOOLE_0.def5 (upair x y) X x).mp this |>.2 hx
    refine ⟨hx, ?_⟩
    by_cases hyX : y ∈ X
    · exact Or.inl hyX
    · have hyin : y ∈ upair x y := (upair_iff x y y).mpr (Or.inr rfl)
      have : y ∈ upair x y \ X := (XBOOLE_0.def5 _ _ y).mpr ⟨hyin, hyX⟩
      exact Or.inr ((singleton_iff x y).mp (h ▸ this)).symm
  · intro ⟨hx, hy⟩
    apply eq_of_mem
    intro z
    constructor
    · intro hz
      have ⟨hzU, hzX⟩ := (XBOOLE_0.def5 (upair x y) X z).mp hz
      rcases (upair_iff x y z).mp hzU with hz | hz
      · exact (singleton_iff x z).mpr hz
      · cases hy with
        | inl hyX => exact (hzX (hz ▸ hyX)).elim
        | inr heq => exact (singleton_iff x z).mpr (heq ▸ hz)
    · intro hz
      have hzx : z = x := (singleton_iff x z).mp hz
      exact (XBOOLE_0.def5 (upair x y) X z).mpr
        ⟨(upair_iff x y z).mpr (Or.inl hzx), fun hX => hx (hzx ▸ hX)⟩

/-- `ZFMISC_1:17` -/
theorem th17 (h : x ≠ y) : upair x y \ TARSKI.singleton y = TARSKI.singleton x :=
  (lm12 (X := TARSKI.singleton y)).mpr
    ⟨fun hy => h ((singleton_iff y x).mp hy), Or.inl ((singleton_iff y y).mpr rfl)⟩

/-- `ZFMISC_1:18` (restatement of `Th3`) -/
theorem th18 (h : TARSKI.singleton x ⊆ TARSKI.singleton y) : x = y :=
  th3 h

/-- `ZFMISC_1:19` -/
theorem th19 (h : TARSKI.singleton z ⊆ upair x y) : z = x ∨ z = y :=
  (upair_iff x y z).mp ((lm1 (x := z) (X := upair x y)).mp h)

/-- `ZFMISC_1:20` (`Th20`) -/
theorem th20 (h : upair x y ⊆ TARSKI.singleton z) : x = z :=
  (singleton_iff z x).mp (h x ((upair_iff x y x).mpr (Or.inl rfl)))

/-- `ZFMISC_1:21` -/
theorem th21 (h : upair x y ⊆ TARSKI.singleton z) : upair x y = TARSKI.singleton z :=
  XBOOLE_0.eq_iff_subset.mpr ⟨h,
    (lm1 (x := z) (X := upair x y)).mpr
      ((upair_iff x y z).mpr (Or.inl (th20 h).symm))⟩

theorem lm13 (hX : X ≠ TARSKI.singleton x) (hne : X ≠ (∅ : TarskiSet.{u})) :
    ∃ y, y ∈ X ∧ y ≠ x := by
  by_cases hx : x ∈ X
  · have hne' : ¬ ∀ z, z ∈ X ↔ z ∈ TARSKI.singleton x :=
      fun hall => hX (extensionality hall)
    have : ∃ z, ¬ (z ∈ X ↔ z ∈ TARSKI.singleton x) :=
      Classical.byContradiction fun hex =>
        hne' fun z => Classical.byContradiction fun hz => hex ⟨z, hz⟩
    obtain ⟨z, hz⟩ := this
    by_cases hzX : z ∈ X
    · have hzsing : z ∉ TARSKI.singleton x := fun hs =>
        hz ⟨fun _ => hs, fun _ => hzX⟩
      exact ⟨z, hzX, fun heq => hzsing ((singleton_iff x z).mpr heq)⟩
    · have hzs : z ∈ TARSKI.singleton x :=
        Classical.byContradiction fun hs =>
          hz ⟨fun hX => (hzX hX).elim, fun hs' => (hs hs').elim⟩
      have : z = x := (singleton_iff x z).mp hzs
      exact (hzX (this ▸ hx)).elim
  · obtain ⟨y, hy⟩ := XBOOLE_0.th7 hne
    exact ⟨y, hy, fun heq => hx (heq ▸ hy)⟩

theorem lm14 : Z ⊆ upair x1 x2 ↔
    Z = (∅ : TarskiSet.{u}) ∨ Z = TARSKI.singleton x1 ∨
      Z = TARSKI.singleton x2 ∨ Z = upair x1 x2 := by
  constructor
  · intro hZ
    by_cases h0 : Z = (∅ : TarskiSet.{u})
    · exact Or.inl h0
    · by_cases h1 : Z = TARSKI.singleton x1
      · exact Or.inr (Or.inl h1)
      · by_cases h2 : Z = TARSKI.singleton x2
        · exact Or.inr (Or.inr (Or.inl h2))
        · apply Or.inr (Or.inr (Or.inr _))
          apply XBOOLE_0.eq_iff_subset.mpr
          refine ⟨hZ, ?_⟩
          intro w hw
          have hx1 : x1 ∈ Z := by
            apply Classical.byContradiction
            intro hx1
            obtain ⟨y, hy, hyne⟩ := lm13 (X := Z) (x := x2) h2 h0
            have : y = x1 ∨ y = x2 := (upair_iff x1 x2 y).mp (hZ y hy)
            cases this with
            | inl h => exact hx1 (h ▸ hy)
            | inr h => exact hyne h
          have hx2 : x2 ∈ Z := by
            apply Classical.byContradiction
            intro hx2
            obtain ⟨y, hy, hyne⟩ := lm13 (X := Z) (x := x1) h1 h0
            have : y = x1 ∨ y = x2 := (upair_iff x1 x2 y).mp (hZ y hy)
            cases this with
            | inl h => exact hyne h
            | inr h => exact hx2 (h ▸ hy)
          rcases (upair_iff x1 x2 w).mp hw with h | h
          · exact h ▸ hx1
          · exact h ▸ hx2
  · intro h
    rcases h with h | h | h | h
    · exact h ▸ XBOOLE_1.th2
    · exact h ▸ th7 (x := x1) (y := x2)
    · intro w hw
      have : w = x2 := (singleton_iff x2 w).mp (h ▸ hw)
      exact (upair_iff x1 x2 w).mpr (Or.inr this)
    · exact h ▸ subset_refl _

/-- `ZFMISC_1:22` -/
theorem th22 (h : upair x1 x2 ⊆ upair y1 y2) : x1 = y1 ∨ x1 = y2 :=
  (upair_iff y1 y2 x1).mp (h x1 ((upair_iff x1 x2 x1).mpr (Or.inl rfl)))

/-- `ZFMISC_1:23` -/
theorem th23 (h : x ≠ y) :
    TARSKI.singleton x ∆ TARSKI.singleton y = upair x y :=
  eq_of_mem fun z =>
    (XBOOLE_0.th1 (TARSKI.singleton x) (TARSKI.singleton y) z).trans <|
      Iff.trans
        ⟨fun hn => by
            by_cases hzx : z = x
            · exact Or.inl hzx
            · have hzy : z = y := by
                have : z ∈ TARSKI.singleton y :=
                  Classical.byContradiction fun hz =>
                    hn ⟨fun hx => (hzx ((singleton_iff x z).mp hx)).elim,
                      fun hy => (hz hy).elim⟩
                exact (singleton_iff y z).mp this
              exact Or.inr hzy,
          fun hz => by
            rcases hz with hz | hz
            · intro hiff
              have : z = y := (singleton_iff y z).mp
                (hiff.mp ((singleton_iff x z).mpr hz))
              exact h (hz.symm.trans this)
            · intro hiff
              have : z = x := (singleton_iff x z).mp
                (hiff.mpr ((singleton_iff y z).mpr hz))
              exact h (this.symm.trans hz)⟩
        (upair_iff x y z).symm

/-- `ZFMISC_1:24` -/
theorem th24 : bool (TARSKI.singleton x) =
    upair (∅ : TarskiSet.{u}) (TARSKI.singleton x) :=
  eq_of_mem fun y =>
    (def1 _ _).trans <|
      (lm3 (Y := y) (x := x)).trans (upair_iff (∅ : TarskiSet.{u}) (TARSKI.singleton x) y).symm

theorem lm15 (h : X ∈ A) : X ⊆ union A :=
  fun z hz => (union_iff A z).mpr ⟨X, hz, h⟩

/-- `ZFMISC_1:25` -/
theorem th25 : union (TARSKI.singleton x) = x :=
  XBOOLE_0.eq_iff_subset.mpr ⟨
    fun _ hw =>
      let ⟨Y, hyY, hY⟩ := (union_iff _ _).mp hw
      (singleton_iff x Y).mp hY ▸ hyY,
    lm15 (X := x) (A := TARSKI.singleton x) ((singleton_iff x x).mpr rfl)⟩

theorem lm16 : union (upair X Y) = X ∪ Y :=
  eq_of_mem fun z =>
    (union_iff (upair X Y) z).trans <|
      Iff.trans
        ⟨fun ⟨W, hzW, hW⟩ =>
            (upair_iff X Y W).mp hW |>.elim (fun h => Or.inl (h ▸ hzW))
              (fun h => Or.inr (h ▸ hzW)),
          fun h =>
            h.elim (fun hX => ⟨X, hX, (upair_iff X Y X).mpr (Or.inl rfl)⟩)
              (fun hY => ⟨Y, hY, (upair_iff X Y Y).mpr (Or.inr rfl)⟩)⟩
        (XBOOLE_0.def3 X Y z).symm

/-- `ZFMISC_1:26` -/
theorem th26 : union (upair (TARSKI.singleton x) (TARSKI.singleton y)) = upair x y :=
  (lm16 (X := TARSKI.singleton x) (Y := TARSKI.singleton y)).trans ENUMSET1.th1.symm

theorem lm17 : TARSKI.pair x y ∈ product X Y ↔ x ∈ X ∧ y ∈ Y := by
  constructor
  · intro h
    obtain ⟨x1, y1, hx, hy, heq⟩ := (def2 X Y (TARSKI.pair x y)).mp h
    have ⟨hxeq, hyeq⟩ := XTUPLE_0.th1 heq
    exact ⟨hxeq ▸ hx, hyeq ▸ hy⟩
  · intro ⟨hx, hy⟩
    exact (def2 X Y (TARSKI.pair x y)).mpr ⟨x, y, hx, hy, rfl⟩

/-- `ZFMISC_1:28` (27 canceled) -/
theorem th28 : TARSKI.pair x y ∈ product (TARSKI.singleton x1) (TARSKI.singleton y1) ↔
    x = x1 ∧ y = y1 :=
  (lm17 (X := TARSKI.singleton x1) (Y := TARSKI.singleton y1)).trans
    (and_congr (singleton_iff x1 x) (singleton_iff y1 y))

/-- `ZFMISC_1:29` -/
theorem th29 : product (TARSKI.singleton x) (TARSKI.singleton y) =
    TARSKI.singleton (TARSKI.pair x y) :=
  eq_of_mem fun z => by
    constructor
    · intro hz
      obtain ⟨x1, y1, hx, hy, heq⟩ := (def2 _ _ z).mp hz
      have hx1 : x1 = x := (singleton_iff x x1).mp hx
      have hy1 : y1 = y := (singleton_iff y y1).mp hy
      exact (singleton_iff _ z).mpr (heq.trans (hx1 ▸ hy1 ▸ rfl))
    · intro hz
      have heq : z = TARSKI.pair x y := (singleton_iff _ z).mp hz
      exact (def2 _ _ z).mpr
        ⟨x, y, (singleton_iff x x).mpr rfl, (singleton_iff y y).mpr rfl, heq⟩

private theorem empty_union (A : TarskiSet.{u}) :
    (∅ : TarskiSet.{u}) ∪ A = A :=
  XBOOLE_1.th12 (X := (∅ : TarskiSet.{u})) (Y := A) XBOOLE_1.th2

private theorem union_empty (A : TarskiSet.{u}) :
    A ∪ (∅ : TarskiSet.{u}) = A :=
  (XBOOLE_0.union_comm A (∅ : TarskiSet.{u})).trans (empty_union A)

/-- `ZFMISC_1:30` (`Th30`) -/
theorem th30 :
    product (TARSKI.singleton x) (upair y z) =
      upair (TARSKI.pair x y) (TARSKI.pair x z) ∧
    product (upair x y) (TARSKI.singleton z) =
      upair (TARSKI.pair x z) (TARSKI.pair y z) := by
  constructor
  · apply eq_of_mem
    intro v
    constructor
    · intro hv
      obtain ⟨x1, y1, hx, hy, heq⟩ := (def2 _ _ v).mp hv
      have hx1 : x1 = x := (singleton_iff x x1).mp hx
      rcases (upair_iff y z y1).mp hy with hy1 | hy1
      · exact (upair_iff _ _ v).mpr (Or.inl (heq.trans (hx1 ▸ hy1 ▸ rfl)))
      · exact (upair_iff _ _ v).mpr (Or.inr (heq.trans (hx1 ▸ hy1 ▸ rfl)))
    · intro hv
      rcases (upair_iff _ _ v).mp hv with hv | hv
      · exact (def2 _ _ v).mpr ⟨x, y, (singleton_iff x x).mpr rfl,
          (upair_iff y z y).mpr (Or.inl rfl), hv⟩
      · exact (def2 _ _ v).mpr ⟨x, z, (singleton_iff x x).mpr rfl,
          (upair_iff y z z).mpr (Or.inr rfl), hv⟩
  · apply eq_of_mem
    intro v
    constructor
    · intro hv
      obtain ⟨x1, y1, hx, hy, heq⟩ := (def2 _ _ v).mp hv
      have hy1 : y1 = z := (singleton_iff z y1).mp hy
      rcases (upair_iff x y x1).mp hx with hx1 | hx1
      · exact (upair_iff _ _ v).mpr (Or.inl (heq.trans (hx1 ▸ hy1 ▸ rfl)))
      · exact (upair_iff _ _ v).mpr (Or.inr (heq.trans (hx1 ▸ hy1 ▸ rfl)))
    · intro hv
      rcases (upair_iff _ _ v).mp hv with hv | hv
      · exact (def2 _ _ v).mpr ⟨x, z, (upair_iff x y x).mpr (Or.inl rfl),
          (singleton_iff z z).mpr rfl, hv⟩
      · exact (def2 _ _ v).mpr ⟨y, z, (upair_iff x y y).mpr (Or.inr rfl),
          (singleton_iff z z).mpr rfl, hv⟩

/-- `ZFMISC_1:31` -/
theorem th31 : TARSKI.singleton x ⊆ X ↔ x ∈ X := lm1

/-- `ZFMISC_1:32` (`Th32`) -/
theorem th32 : upair x1 x2 ⊆ Z ↔ x1 ∈ Z ∧ x2 ∈ Z := by
  constructor
  · intro h
    exact ⟨h x1 ((upair_iff x1 x2 x1).mpr (Or.inl rfl)),
      h x2 ((upair_iff x1 x2 x2).mpr (Or.inr rfl))⟩
  · intro ⟨h1, h2⟩ w hw
    rcases (upair_iff x1 x2 w).mp hw with hw | hw
    · exact hw ▸ h1
    · exact hw ▸ h2

/-- `ZFMISC_1:33` -/
theorem th33 : Y ⊆ TARSKI.singleton x ↔
    Y = (∅ : TarskiSet.{u}) ∨ Y = TARSKI.singleton x := lm3

/-- `ZFMISC_1:34` -/
theorem th34 (hYX : Y ⊆ X) (hx : x ∉ Y) : Y ⊆ X \ TARSKI.singleton x :=
  lm2 hYX hx

/-- `ZFMISC_1:35` -/
theorem th35 (hX : X ≠ TARSKI.singleton x) (hne : X ≠ (∅ : TarskiSet.{u})) :
    ∃ y, y ∈ X ∧ y ≠ x :=
  lm13 hX hne

/-- `ZFMISC_1:36` -/
theorem th36 : Z ⊆ upair x1 x2 ↔
    Z = (∅ : TarskiSet.{u}) ∨ Z = TARSKI.singleton x1 ∨
      Z = TARSKI.singleton x2 ∨ Z = upair x1 x2 := lm14

/-- `ZFMISC_1:37` (`Th37`) -/
theorem th37 (h : TARSKI.singleton z = X ∪ Y) :
    X = TARSKI.singleton z ∧ Y = TARSKI.singleton z ∨
      X = (∅ : TarskiSet.{u}) ∧ Y = TARSKI.singleton z ∨
      X = TARSKI.singleton z ∧ Y = (∅ : TarskiSet.{u}) := by
  have hX : X ⊆ TARSKI.singleton z := fun w hw =>
    h ▸ (XBOOLE_0.def3 X Y w).mpr (Or.inl hw)
  have hY : Y ⊆ TARSKI.singleton z := fun w hw =>
    h ▸ (XBOOLE_0.def3 X Y w).mpr (Or.inr hw)
  rcases (lm3 (Y := X) (x := z)).mp hX with hXe | hXz
  · exact Or.inr (Or.inl ⟨hXe, (empty_union Y).symm.trans (hXe ▸ h.symm)⟩)
  · rcases (lm3 (Y := Y) (x := z)).mp hY with hYe | hYz
    · exact Or.inr (Or.inr ⟨(union_empty X).symm.trans (hYe ▸ h.symm), hYe⟩)
    · exact Or.inl ⟨hXz, hYz⟩

/-- `ZFMISC_1:38` -/
theorem th38 (h : TARSKI.singleton z = X ∪ Y) (hne : X ≠ Y) :
    X = (∅ : TarskiSet.{u}) ∨ Y = (∅ : TarskiSet.{u}) := by
  rcases th37 h with h | h | h
  · exact (hne (h.1.trans h.2.symm)).elim
  · exact Or.inl h.1
  · exact Or.inr h.2

/-- `ZFMISC_1:39` -/
theorem th39 (h : TARSKI.singleton x ∪ X ⊆ X) : x ∈ X := lm4 h

/-- `ZFMISC_1:40` -/
theorem th40 (hx : x ∈ X) : TARSKI.singleton x ∪ X = X :=
  XBOOLE_1.th12 (X := TARSKI.singleton x) (Y := X) ((lm1 (x := x) (X := X)).mpr hx)

/-- `ZFMISC_1:41` -/
theorem th41 (h : upair x y ∪ Z ⊆ Z) : x ∈ Z := by
  have : x ∈ upair x y ∪ Z :=
    (XBOOLE_0.def3 _ _ x).mpr (Or.inl ((upair_iff x y x).mpr (Or.inl rfl)))
  exact h x this

/-- `ZFMISC_1:42` -/
theorem th42 (hx : x ∈ Z) (hy : y ∈ Z) : upair x y ∪ Z = Z :=
  XBOOLE_1.th12 (X := upair x y) (Y := Z) ((th32 (x1 := x) (x2 := y) (Z := Z)).mpr ⟨hx, hy⟩)

/-- `ZFMISC_1:43` -/
theorem th43 : TARSKI.singleton x ∪ X ≠ (∅ : TarskiSet.{u}) :=
  fun h => (XBOOLE_0.empty_iff x).mp
    (h ▸ (XBOOLE_0.def3 (TARSKI.singleton x) X x).mpr
      (Or.inl ((singleton_iff x x).mpr rfl)))

/-- `ZFMISC_1:44` -/
theorem th44 : upair x y ∪ X ≠ (∅ : TarskiSet.{u}) :=
  fun h => (XBOOLE_0.empty_iff x).mp
    (h ▸ (XBOOLE_0.def3 (upair x y) X x).mpr
      (Or.inl ((upair_iff x y x).mpr (Or.inl rfl))))

/-- `ZFMISC_1:45` -/
theorem th45 (h : X ∩ TARSKI.singleton x = TARSKI.singleton x) : x ∈ X :=
  lm8 h

/-- `ZFMISC_1:46` -/
theorem th46 (hx : x ∈ X) : X ∩ TARSKI.singleton x = TARSKI.singleton x :=
  lm9 hx

/-- `ZFMISC_1:47` -/
theorem th47 (hx : x ∈ Z) (hy : y ∈ Z) : upair x y ∩ Z = upair x y :=
  XBOOLE_1.th28 (X := upair x y) (Y := Z)
    ((th32 (x1 := x) (x2 := y) (Z := Z)).mpr ⟨hx, hy⟩)

/-- `ZFMISC_1:48` -/
theorem th48 (h : XBOOLE_0.misses (TARSKI.singleton x) X) : x ∉ X :=
  lm6 h

/-- `ZFMISC_1:49` (`Th49`) -/
theorem th49 (h : XBOOLE_0.misses (upair x y) Z) : x ∉ Z := by
  intro hx
  exact (XBOOLE_0.empty_iff x).mp
    (h ▸ (XBOOLE_0.def4 (upair x y) Z x).mpr
      ⟨(upair_iff x y x).mpr (Or.inl rfl), hx⟩)

/-- `ZFMISC_1:50` -/
theorem th50 (hx : x ∉ X) : XBOOLE_0.misses (TARSKI.singleton x) X :=
  lm7 hx

/-- `ZFMISC_1:51` (`Th51`) -/
theorem th51 (hx : x ∉ Z) (hy : y ∉ Z) : XBOOLE_0.misses (upair x y) Z :=
  XBOOLE_0.empty_eq fun ⟨w, hw⟩ =>
    let ⟨hwU, hwZ⟩ := (XBOOLE_0.def4 (upair x y) Z w).mp hw
    (upair_iff x y w).mp hwU |>.elim (fun h => hx (h ▸ hwZ)) (fun h => hy (h ▸ hwZ))

/-- `ZFMISC_1:52` -/
theorem th52 : XBOOLE_0.misses (TARSKI.singleton x) X ∨
    X ∩ TARSKI.singleton x = TARSKI.singleton x := by
  by_cases hx : x ∈ X
  · exact Or.inr (lm9 hx)
  · exact Or.inl (lm7 hx)

/-- `ZFMISC_1:53` -/
theorem th53 (h : upair x y ∩ X = TARSKI.singleton x) : y ∉ X ∨ x = y := by
  by_cases hy : y ∈ X
  · have : y ∈ TARSKI.singleton x :=
      h ▸ (XBOOLE_0.def4 (upair x y) X y).mpr
        ⟨(upair_iff x y y).mpr (Or.inr rfl), hy⟩
    exact Or.inr ((singleton_iff x y).mp this).symm
  · exact Or.inl hy

/-- `ZFMISC_1:54` -/
theorem th54 (hx : x ∈ X) (hy : y ∉ X ∨ x = y) :
    upair x y ∩ X = TARSKI.singleton x := by
  apply eq_of_mem
  intro z
  constructor
  · intro hz
    have ⟨hzU, hzX⟩ := (XBOOLE_0.def4 (upair x y) X z).mp hz
    rcases (upair_iff x y z).mp hzU with hz | hz
    · exact (singleton_iff x z).mpr hz
    · cases hy with
      | inl hny => exact (hny (hz ▸ hzX)).elim
      | inr heq => exact (singleton_iff x z).mpr (heq ▸ hz)
  · intro hz
    have hzx : z = x := (singleton_iff x z).mp hz
    exact (XBOOLE_0.def4 _ _ z).mpr
      ⟨(upair_iff x y z).mpr (Or.inl hzx), hzx ▸ hx⟩

/-- `ZFMISC_1:55` -/
theorem th55 (h : upair x y ∩ X = upair x y) : x ∈ X :=
  (XBOOLE_0.def4 (upair x y) X x).mp
    (show x ∈ upair x y ∩ X from h.symm ▸ (upair_iff x y x).mpr (Or.inl rfl)) |>.2

/-- `ZFMISC_1:56` (`Th56`) -/
theorem th56 : z ∈ X \ TARSKI.singleton x ↔ z ∈ X ∧ z ≠ x :=
  (XBOOLE_0.def5 X (TARSKI.singleton x) z).trans
    (and_congr_right fun _ =>
      ⟨fun hz => fun heq => hz ((singleton_iff x z).mpr heq),
        fun hne hz => hne ((singleton_iff x z).mp hz)⟩)

/-- `ZFMISC_1:57` (`Th57`) -/
theorem th57 : X \ TARSKI.singleton x = X ↔ x ∉ X :=
  (XBOOLE_1.th83 (X := X) (Y := TARSKI.singleton x)).symm.trans
    ⟨fun h => lm6 (XBOOLE_0.misses_symm h),
      fun hx => XBOOLE_0.misses_symm (lm7 hx)⟩

/-- `ZFMISC_1:58` -/
theorem th58 (h : X \ TARSKI.singleton x = (∅ : TarskiSet.{u})) :
    X = (∅ : TarskiSet.{u}) ∨ X = TARSKI.singleton x :=
  (lm3 (Y := X) (x := x)).mp ((XBOOLE_1.th37 (X := X) (Y := TARSKI.singleton x)).mp h)

/-- `ZFMISC_1:59` -/
theorem th59 : TARSKI.singleton x \ X = TARSKI.singleton x ↔ x ∉ X := lm10

/-- `ZFMISC_1:60` -/
theorem th60 : TARSKI.singleton x \ X = (∅ : TarskiSet.{u}) ↔ x ∈ X := lm11

/-- `ZFMISC_1:61` -/
theorem th61 : TARSKI.singleton x \ X = (∅ : TarskiSet.{u}) ∨
    TARSKI.singleton x \ X = TARSKI.singleton x := by
  by_cases hx : x ∈ X
  · exact Or.inl (lm11.mpr hx)
  · exact Or.inr (lm10.mpr hx)

/-- `ZFMISC_1:62` -/
theorem th62 : upair x y \ X = TARSKI.singleton x ↔ x ∉ X ∧ (y ∈ X ∨ x = y) :=
  lm12

/-- `ZFMISC_1:63` -/
theorem th63 : upair x y \ X = upair x y ↔ x ∉ X ∧ y ∉ X :=
  (XBOOLE_1.th83 (X := upair x y) (Y := X)).symm.trans
    ⟨fun h => ⟨th49 h,
        th49 (x := y) (y := x) (Z := X)
          (TARSKI.upair_comm x y ▸ h)⟩,
      fun ⟨hx, hy⟩ => th51 hx hy⟩

/-- `ZFMISC_1:64` (`Th64`) -/
theorem th64 : upair x y \ X = (∅ : TarskiSet.{u}) ↔ x ∈ X ∧ y ∈ X :=
  (XBOOLE_1.th37 (X := upair x y) (Y := X)).trans th32

/-- `ZFMISC_1:65` -/
theorem th65 : upair x y \ X = (∅ : TarskiSet.{u}) ∨
    upair x y \ X = TARSKI.singleton x ∨
    upair x y \ X = TARSKI.singleton y ∨
    upair x y \ X = upair x y := by
  by_cases hx : x ∈ X
  · by_cases hy : y ∈ X
    · exact Or.inl (th64.mpr ⟨hx, hy⟩)
    · exact Or.inr (Or.inr (Or.inl
        ((lm12 (x := y) (y := x) (X := X)).mpr ⟨hy, Or.inl hx⟩ ▸
          TARSKI.upair_comm x y ▸ rfl)))
  · by_cases hy : y ∈ X
    · exact Or.inr (Or.inl (lm12.mpr ⟨hx, Or.inl hy⟩))
    · exact Or.inr (Or.inr (Or.inr (th63.mpr ⟨hx, hy⟩)))

/-- `ZFMISC_1:66` -/
theorem th66 : X \ upair x y = (∅ : TarskiSet.{u}) ↔
    X = (∅ : TarskiSet.{u}) ∨ X = TARSKI.singleton x ∨
      X = TARSKI.singleton y ∨ X = upair x y :=
  (XBOOLE_1.th37 (X := X) (Y := upair x y)).trans lm14

/-- `ZFMISC_1:67` -/
theorem th67 (h : A ⊆ B) : bool A ⊆ bool B := by
  intro x hx
  exact (def1 B x).mpr (XBOOLE_1.th1 ((def1 A x).mp hx) h)

/-- `ZFMISC_1:68` -/
theorem th68 : TARSKI.singleton A ⊆ bool A :=
  (lm1 (x := A) (X := bool A)).mpr ((def1 A A).mpr (subset_refl A))

/-- `ZFMISC_1:69` -/
theorem th69 : bool A ∪ bool B ⊆ bool (A ∪ B) := by
  intro x hx
  have : x ⊆ A ∨ x ⊆ B :=
    (XBOOLE_0.def3 (bool A) (bool B) x).mp hx |>.elim
      (fun h => Or.inl ((def1 A x).mp h)) (fun h => Or.inr ((def1 B x).mp h))
  have hA : A ⊆ A ∪ B := XBOOLE_1.th7 (X := A) (Y := B)
  have hB : B ⊆ A ∪ B := fun z hz => (XBOOLE_0.def3 A B z).mpr (Or.inr hz)
  exact (def1 (A ∪ B) x).mpr
    (this.elim (fun hxA => XBOOLE_1.th1 hxA hA) (fun hxB => XBOOLE_1.th1 hxB hB))

/-- `ZFMISC_1:70` -/
theorem th70 (h : bool A ∪ bool B = bool (A ∪ B)) :
    XBOOLE_0.are_ccomparable A B := by
  have : A ∪ B ∈ bool A ∨ A ∪ B ∈ bool B :=
    (XBOOLE_0.def3 (bool A) (bool B) (A ∪ B)).mp
      (h ▸ (def1 (A ∪ B) (A ∪ B)).mpr (subset_refl _))
  cases this with
  | inl hA' =>
    have : A ∪ B ⊆ A := (def1 A (A ∪ B)).mp hA'
    exact Or.inr (fun z hz => this z ((XBOOLE_0.def3 A B z).mpr (Or.inr hz)))
  | inr hB' =>
    have : A ∪ B ⊆ B := (def1 B (A ∪ B)).mp hB'
    exact Or.inl (fun z hz => this z ((XBOOLE_0.def3 A B z).mpr (Or.inl hz)))

/-- `ZFMISC_1:71` -/
theorem th71 : bool (A ∩ B) = bool A ∩ bool B :=
  eq_of_mem fun x =>
    (def1 (A ∩ B) x).trans <|
      Iff.trans
        ⟨fun hx =>
            ⟨(def1 A x).mpr (XBOOLE_1.th1 hx (XBOOLE_1.th17 (X := A) (Y := B))),
              (def1 B x).mpr (XBOOLE_1.th1 hx
                (show A ∩ B ⊆ B from fun z hz =>
                  (XBOOLE_0.def4 A B z).mp hz |>.2))⟩,
          fun ⟨hA, hB⟩ =>
            XBOOLE_1.th19 (Z := x) (X := A) (Y := B)
              ((def1 A x).mp hA) ((def1 B x).mp hB)⟩
        (Iff.trans
          ⟨fun ⟨hA, hB⟩ => (XBOOLE_0.def4 (bool A) (bool B) x).mpr ⟨hA, hB⟩,
            fun h => (XBOOLE_0.def4 (bool A) (bool B) x).mp h⟩
          Iff.rfl)

/-- `ZFMISC_1:72` -/
theorem th72 : bool (A \ B) ⊆
    TARSKI.singleton (∅ : TarskiSet.{u}) ∪ (bool A \ bool B) := by
  intro x hx
  have hxAB : x ⊆ A \ B := (def1 (A \ B) x).mp hx
  have hxA : x ⊆ A := XBOOLE_1.th1 hxAB (XBOOLE_1.th36 (X := A) (Y := B))
  by_cases h0 : x = (∅ : TarskiSet.{u})
  · exact (XBOOLE_0.def3 _ _ x).mpr
      (Or.inl ((singleton_iff _ x).mpr h0))
  · have hnotB : ¬ x ⊆ B := by
      intro hxB
      have : x ⊆ (A \ B) ∩ B := XBOOLE_1.th19 (Z := x) (X := A \ B) (Y := B) hxAB hxB
      have hempty : (A \ B) ∩ B = (∅ : TarskiSet.{u}) := by
        have : XBOOLE_0.misses (A \ B) B := XBOOLE_1.th79 (X := A) (Y := B)
        exact this
      exact h0 (XBOOLE_1.th3 (hempty ▸ this))
    exact (XBOOLE_0.def3 _ _ x).mpr (Or.inr
      ((XBOOLE_0.def5 (bool A) (bool B) x).mpr
        ⟨(def1 A x).mpr hxA, fun hB => hnotB ((def1 B x).mp hB)⟩))

/-- `ZFMISC_1:73` -/
theorem th73 : bool (A \ B) ∪ bool (B \ A) ⊆ bool (A ∆ B) := by
  intro x hx
  have : x ⊆ A \ B ∨ x ⊆ B \ A :=
    (XBOOLE_0.def3 _ _ x).mp hx |>.elim
      (fun h => Or.inl ((def1 _ _).mp h)) (fun h => Or.inr ((def1 _ _).mp h))
  have hsub : x ⊆ (A \ B) ∪ (B \ A) :=
    this.elim
      (fun h => XBOOLE_1.th1 h (XBOOLE_1.th7 (X := A \ B) (Y := B \ A)))
      (fun h => XBOOLE_1.th1 h (fun z hz =>
        (XBOOLE_0.def3 (A \ B) (B \ A) z).mpr (Or.inr hz)))
  exact (def1 (A ∆ B) x).mpr (XBOOLE_0.def6 A B ▸ hsub)

/-- `ZFMISC_1:74` -/
theorem th74 (h : X ∈ A) : X ⊆ union A := lm15 h

/-- `ZFMISC_1:75` -/
theorem th75 : union (upair X Y) = X ∪ Y := lm16

/-- `ZFMISC_1:76` -/
theorem th76 (h : ∀ X, X ∈ A → X ⊆ Z) : union A ⊆ Z := by
  intro y hy
  obtain ⟨Y, hyY, hY⟩ := (union_iff A y).mp hy
  exact h Y hY y hyY

/-- `ZFMISC_1:77` (`Th77`) -/
theorem th77 (h : A ⊆ B) : union A ⊆ union B := by
  intro x hx
  obtain ⟨Y, hxY, hY⟩ := (union_iff A x).mp hx
  exact (union_iff B x).mpr ⟨Y, hxY, h Y hY⟩

/-- `ZFMISC_1:78` -/
theorem th78 : union (A ∪ B) = union A ∪ union B := by
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro x hx
    obtain ⟨Y, hxY, hY⟩ := (union_iff (A ∪ B) x).mp hx
    rcases (XBOOLE_0.def3 A B Y).mp hY with hA | hB
    · exact (XBOOLE_0.def3 _ _ x).mpr (Or.inl ((union_iff A x).mpr ⟨Y, hxY, hA⟩))
    · exact (XBOOLE_0.def3 _ _ x).mpr (Or.inr ((union_iff B x).mpr ⟨Y, hxY, hB⟩))
  · exact XBOOLE_1.th8 (X := union A) (Y := union B) (Z := union (A ∪ B))
      (th77 (XBOOLE_1.th7 (X := A) (Y := B)))
      (th77 (fun z hz => (XBOOLE_0.def3 A B z).mpr (Or.inr hz)))

/-- `ZFMISC_1:79` (`Th79`) -/
theorem th79 : union (A ∩ B) ⊆ union A ∩ union B := by
  intro x hx
  obtain ⟨Y, hxY, hY⟩ := (union_iff (A ∩ B) x).mp hx
  have ⟨hA, hB⟩ := (XBOOLE_0.def4 A B Y).mp hY
  exact (XBOOLE_0.def4 (union A) (union B) x).mpr
    ⟨(union_iff A x).mpr ⟨Y, hxY, hA⟩, (union_iff B x).mpr ⟨Y, hxY, hB⟩⟩

/-- `ZFMISC_1:80` (`Th80`) -/
theorem th80 (h : ∀ X, X ∈ A → XBOOLE_0.misses X B) :
    XBOOLE_0.misses (union A) B :=
  XBOOLE_0.empty_eq fun ⟨z, hz⟩ =>
    let ⟨hzU, hzB⟩ := (XBOOLE_0.def4 (union A) B z).mp hz
    let ⟨X, hzX, hX⟩ := (union_iff A z).mp hzU
    (XBOOLE_0.empty_iff z).mp
      ((h X hX) ▸ (XBOOLE_0.def4 X B z).mpr ⟨hzX, hzB⟩)

/-- `ZFMISC_1:81` -/
theorem th81 : union (bool A) = A :=
  eq_of_mem fun x => by
    constructor
    · intro hx
      obtain ⟨X, hxX, hX⟩ := (union_iff (bool A) x).mp hx
      exact (def1 A X).mp hX x hxX
    · intro hx
      exact (union_iff (bool A) x).mpr
        ⟨TARSKI.singleton x, (singleton_iff x x).mpr rfl,
          (def1 A (TARSKI.singleton x)).mpr ((lm1 (x := x) (X := A)).mpr hx)⟩

/-- `ZFMISC_1:82` -/
theorem th82 : A ⊆ bool (union A) :=
  fun x hx => (def1 (union A) x).mpr (lm15 hx)

/-- `ZFMISC_1:83` -/
theorem th83
    (h : ∀ X Y, X ≠ Y → X ∈ A ∪ B → Y ∈ A ∪ B → XBOOLE_0.misses X Y) :
    union (A ∩ B) = union A ∩ union B := by
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · exact th79
  · intro x hx
    have ⟨hxA, hxB⟩ := (XBOOLE_0.def4 (union A) (union B) x).mp hx
    obtain ⟨X, hxX, hXA⟩ := (union_iff A x).mp hxA
    obtain ⟨Y, hxY, hYB⟩ := (union_iff B x).mp hxB
    have hXAB : X ∈ A ∪ B := (XBOOLE_0.def3 A B X).mpr (Or.inl hXA)
    have hYAB : Y ∈ A ∪ B := (XBOOLE_0.def3 A B Y).mpr (Or.inr hYB)
    have hXY : X = Y := by
      apply Classical.byContradiction
      intro hne
      have hmiss := h X Y hne hXAB hYAB
      exact (XBOOLE_0.empty_iff x).mp
        (hmiss ▸ (XBOOLE_0.def4 X Y x).mpr ⟨hxX, hxY⟩)
    exact (union_iff (A ∩ B) x).mpr
      ⟨Y, hxY, (XBOOLE_0.def4 A B Y).mpr ⟨hXY ▸ hXA, hYB⟩⟩

/-- `ZFMISC_1:84` (`Th84`) -/
theorem th84 (hA : A ⊆ product X Y) (hz : z ∈ A) :
    ∃ x y, x ∈ X ∧ y ∈ Y ∧ z = TARSKI.pair x y :=
  (def2 X Y z).mp (hA z hz)

/-- `ZFMISC_1:85` (`Th85`) -/
theorem th85 (hz : z ∈ product X1 Y1 ∩ product X2 Y2) :
    ∃ x y, z = TARSKI.pair x y ∧ x ∈ X1 ∩ X2 ∧ y ∈ Y1 ∩ Y2 := by
  have ⟨hz1, hz2⟩ := (XBOOLE_0.def4 _ _ z).mp hz
  obtain ⟨x1, y1, hx1, hy1, heq1⟩ := (def2 X1 Y1 z).mp hz1
  obtain ⟨x2, y2, hx2, hy2, heq2⟩ := (def2 X2 Y2 z).mp hz2
  have ⟨hx, hy⟩ := TARSKI.pair_inj.mp (heq1.symm.trans heq2)
  exact ⟨x1, y1, heq1,
    (XBOOLE_0.def4 X1 X2 x1).mpr ⟨hx1, hx ▸ hx2⟩,
    (XBOOLE_0.def4 Y1 Y2 y1).mpr ⟨hy1, hy ▸ hy2⟩⟩

/-- `ZFMISC_1:86` -/
theorem th86 : product X Y ⊆ bool (bool (X ∪ Y)) := by
  intro z hz
  obtain ⟨x, y, hx, hy, heq⟩ := (def2 X Y z).mp hz
  exact heq ▸ pair_mem_bbool hx hy

/-- `ZFMISC_1:87` -/
theorem th87 : TARSKI.pair x y ∈ product X Y ↔ x ∈ X ∧ y ∈ Y := lm17

/-- `ZFMISC_1:88` (`Th88`) -/
theorem th88 (h : TARSKI.pair x y ∈ product X Y) :
    TARSKI.pair y x ∈ product Y X :=
  (lm17 (x := y) (y := x) (X := Y) (Y := X)).mpr ((lm17.mp h).symm)

/-- `ZFMISC_1:89` -/
theorem th89 (h : ∀ x y, TARSKI.pair x y ∈ product X1 Y1 ↔
    TARSKI.pair x y ∈ product X2 Y2) :
    product X1 Y1 = product X2 Y2 :=
  eq_of_mem fun z =>
    ⟨fun hz =>
        let ⟨x, y, hx, hy, heq⟩ := (def2 X1 Y1 z).mp hz
        heq ▸ (h x y).mp ((def2 X1 Y1 _).mpr ⟨x, y, hx, hy, rfl⟩),
      fun hz =>
        let ⟨x, y, hx, hy, heq⟩ := (def2 X2 Y2 z).mp hz
        heq ▸ (h x y).mpr ((def2 X2 Y2 _).mpr ⟨x, y, hx, hy, rfl⟩)⟩

theorem lm18 (hA : A ⊆ product X1 Y1) (hB : B ⊆ product X2 Y2)
    (h : ∀ x y, TARSKI.pair x y ∈ A ↔ TARSKI.pair x y ∈ B) : A = B :=
  eq_of_mem fun _z =>
    ⟨fun hz =>
        let ⟨x, y, _, _, heq⟩ := th84 hA hz
        heq ▸ (h x y).mp (heq ▸ hz),
      fun hz =>
        let ⟨x, y, _, _, heq⟩ := th84 hB hz
        heq ▸ (h x y).mpr (heq ▸ hz)⟩

theorem lm19
    (hA : ∀ z, z ∈ A → ∃ x y, z = TARSKI.pair x y)
    (hB : ∀ z, z ∈ B → ∃ x y, z = TARSKI.pair x y)
    (h : ∀ x y, TARSKI.pair x y ∈ A ↔ TARSKI.pair x y ∈ B) : A = B :=
  eq_of_mem fun z =>
    ⟨fun hz =>
        let ⟨x, y, heq⟩ := hA z hz
        heq ▸ (h x y).mp (heq ▸ hz),
      fun hz =>
        let ⟨x, y, heq⟩ := hB z hz
        heq ▸ (h x y).mpr (heq ▸ hz)⟩

/-- `ZFMISC_1:90` (`Th90`) -/
theorem th90 : product X Y = (∅ : TarskiSet.{u}) ↔
    X = (∅ : TarskiSet.{u}) ∨ Y = (∅ : TarskiSet.{u}) := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    have hX : X ≠ (∅ : TarskiSet.{u}) := fun hX => hne (Or.inl hX)
    have hY : Y ≠ (∅ : TarskiSet.{u}) := fun hY => hne (Or.inr hY)
    obtain ⟨x, hx⟩ := XBOOLE_0.th7 hX
    obtain ⟨y, hy⟩ := XBOOLE_0.th7 hY
    exact (XBOOLE_0.empty_iff (TARSKI.pair x y)).mp
      (h ▸ (def2 X Y _).mpr ⟨x, y, hx, hy, rfl⟩)
  · intro h
    apply XBOOLE_0.empty_eq
    intro ⟨z, hz⟩
    obtain ⟨x, y, hx, hy, _⟩ := (def2 X Y z).mp hz
    cases h with
    | inl hX => exact (XBOOLE_0.empty_iff x).mp (hX ▸ hx)
    | inr hY => exact (XBOOLE_0.empty_iff y).mp (hY ▸ hy)

/-- `ZFMISC_1:91` -/
theorem th91 (hX : X ≠ (∅ : TarskiSet.{u})) (hY : Y ≠ (∅ : TarskiSet.{u}))
    (h : product X Y = product Y X) : X = Y := by
  obtain ⟨x, hx⟩ := XBOOLE_0.th7 hX
  obtain ⟨y, hy⟩ := XBOOLE_0.th7 hY
  apply eq_of_mem
  intro z
  constructor
  · intro hz
    exact (lm17 (x := z) (y := y) (X := Y) (Y := X)).mp
      (h ▸ (lm17 (x := z) (y := y) (X := X) (Y := Y)).mpr ⟨hz, hy⟩) |>.1
  · intro hz
    exact (lm17 (x := z) (y := x) (X := X) (Y := Y)).mp
      (h.symm ▸ (lm17 (x := z) (y := x) (X := Y) (Y := X)).mpr ⟨hz, hx⟩) |>.1

/-- `ZFMISC_1:92` -/
theorem th92 (h : product X X = product Y Y) : X = Y :=
  eq_of_mem fun x => by
    constructor
    · intro hx
      exact (lm17 (x := x) (y := x) (X := Y) (Y := Y)).mp
        (h ▸ (lm17 (x := x) (y := x) (X := X) (Y := X)).mpr ⟨hx, hx⟩) |>.1
    · intro hx
      exact (lm17 (x := x) (y := x) (X := X) (Y := X)).mp
        (h.symm ▸ (lm17 (x := x) (y := x) (X := Y) (Y := Y)).mpr ⟨hx, hx⟩) |>.1

theorem lm20 (hz : z ∈ product X Y) : ∃ x y, TARSKI.pair x y = z :=
  let ⟨x, y, _, _, heq⟩ := (def2 X Y z).mp hz
  ⟨x, y, heq.symm⟩

/-- `ZFMISC_1:93` -/
theorem th93 (h : X ⊆ product X X) : X = (∅ : TarskiSet.{u}) := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨z, hz⟩ := XBOOLE_0.th7 hne
  have hneU : ¬ XBOOLE_0.isEmpty (X ∪ union X) :=
    fun hempty => hempty ⟨z, (XBOOLE_0.def3 X (union X) z).mpr (Or.inl hz)⟩
  obtain ⟨Y, hY, hmiss⟩ := XREGULAR.th1 hneU
  have hYnotX : Y ∉ X := by
    intro hYX
    obtain ⟨x, y, _, _, heq⟩ := (def2 X X Y).mp (h Y hYX)
    have hs : TARSKI.singleton x ∈ Y :=
      heq ▸ (upair_iff (upair x y) (TARSKI.singleton x) (TARSKI.singleton x)).mpr
        (Or.inr rfl)
    have hsU : TARSKI.singleton x ∈ union X :=
      (union_iff X _).mpr ⟨Y, hs, hYX⟩
    have hsXU : TARSKI.singleton x ∈ X ∪ union X :=
      (XBOOLE_0.def3 _ _ _).mpr (Or.inr hsU)
    exact (XBOOLE_0.empty_iff (TARSKI.singleton x)).mp
      (hmiss ▸ (XBOOLE_0.def4 Y (X ∪ union X) _).mpr ⟨hs, hsXU⟩)
  have hYU : Y ∈ union X :=
    (XBOOLE_0.def3 X (union X) Y).mp hY |>.elim (fun h => (hYnotX h).elim) id
  obtain ⟨Z, hYZ, hZX⟩ := (union_iff X Y).mp hYU
  obtain ⟨x, y, hx, _, heq⟩ := (def2 X X Z).mp (h Z hZX)
  have hxY : x ∈ Y := by
    have hYpair : Y ∈ TARSKI.pair x y := heq ▸ hYZ
    rcases (upair_iff (upair x y) (TARSKI.singleton x) Y).mp hYpair with hY | hY
    · exact hY ▸ (upair_iff x y x).mpr (Or.inl rfl)
    · exact hY ▸ (singleton_iff x x).mpr rfl
  have hxXU : x ∈ X ∪ union X :=
    (XBOOLE_0.def3 X (union X) x).mpr (Or.inl hx)
  exact (XBOOLE_0.empty_iff x).mp
    (hmiss ▸ (XBOOLE_0.def4 Y (X ∪ union X) x).mpr ⟨hxY, hxXU⟩)

/-- `ZFMISC_1:94` -/
theorem th94 (hZ : Z ≠ (∅ : TarskiSet.{u}))
    (h : product X Z ⊆ product Y Z ∨ product Z X ⊆ product Z Y) : X ⊆ Y := by
  obtain ⟨z, hz⟩ := XBOOLE_0.th7 hZ
  intro x hx
  cases h with
  | inl hXZ =>
    exact (lm17 (x := x) (y := z) (X := Y) (Y := Z)).mp
      (hXZ _ ((lm17 (x := x) (y := z) (X := X) (Y := Z)).mpr ⟨hx, hz⟩)) |>.1
  | inr hZX =>
    exact (lm17 (x := z) (y := x) (X := Z) (Y := Y)).mp
      (hZX _ ((lm17 (x := z) (y := x) (X := Z) (Y := X)).mpr ⟨hz, hx⟩)) |>.2

/-- `ZFMISC_1:95` (`Th95`) -/
theorem th95 (h : X ⊆ Y) :
    product X Z ⊆ product Y Z ∧ product Z X ⊆ product Z Y := by
  constructor
  · intro w hw
    obtain ⟨x, y, hx, hy, heq⟩ := (def2 X Z w).mp hw
    exact (def2 Y Z w).mpr ⟨x, y, h x hx, hy, heq⟩
  · intro w hw
    obtain ⟨x, y, hx, hy, heq⟩ := (def2 Z X w).mp hw
    exact (def2 Z Y w).mpr ⟨x, y, hx, h y hy, heq⟩

/-- `ZFMISC_1:96` (`Th96`) -/
theorem th96 (h1 : X1 ⊆ Y1) (h2 : X2 ⊆ Y2) : product X1 X2 ⊆ product Y1 Y2 :=
  XBOOLE_1.th1 ((th95 (Z := X2) h1).1) ((th95 (X := X2) (Y := Y2) (Z := Y1) h2).2)

/-- `ZFMISC_1:97` (`Th97`) -/
theorem th97 :
    product (X ∪ Y) Z = product X Z ∪ product Y Z ∧
    product Z (X ∪ Y) = product Z X ∪ product Z Y := by
  constructor
  · apply eq_of_mem
    intro w
    constructor
    · intro hw
      obtain ⟨x, y, hx, hy, heq⟩ := (def2 (X ∪ Y) Z w).mp hw
      rcases (XBOOLE_0.def3 X Y x).mp hx with hx | hx
      · exact (XBOOLE_0.def3 _ _ w).mpr
          (Or.inl ((def2 X Z w).mpr ⟨x, y, hx, hy, heq⟩))
      · exact (XBOOLE_0.def3 _ _ w).mpr
          (Or.inr ((def2 Y Z w).mpr ⟨x, y, hx, hy, heq⟩))
    · intro hw
      rcases (XBOOLE_0.def3 _ _ w).mp hw with hw | hw
      · obtain ⟨x, y, hx, hy, heq⟩ := (def2 X Z w).mp hw
        exact (def2 (X ∪ Y) Z w).mpr
          ⟨x, y, (XBOOLE_0.def3 X Y x).mpr (Or.inl hx), hy, heq⟩
      · obtain ⟨x, y, hx, hy, heq⟩ := (def2 Y Z w).mp hw
        exact (def2 (X ∪ Y) Z w).mpr
          ⟨x, y, (XBOOLE_0.def3 X Y x).mpr (Or.inr hx), hy, heq⟩
  · apply eq_of_mem
    intro w
    constructor
    · intro hw
      obtain ⟨x, y, hx, hy, heq⟩ := (def2 Z (X ∪ Y) w).mp hw
      rcases (XBOOLE_0.def3 X Y y).mp hy with hy | hy
      · exact (XBOOLE_0.def3 _ _ w).mpr
          (Or.inl ((def2 Z X w).mpr ⟨x, y, hx, hy, heq⟩))
      · exact (XBOOLE_0.def3 _ _ w).mpr
          (Or.inr ((def2 Z Y w).mpr ⟨x, y, hx, hy, heq⟩))
    · intro hw
      rcases (XBOOLE_0.def3 _ _ w).mp hw with hw | hw
      · obtain ⟨x, y, hx, hy, heq⟩ := (def2 Z X w).mp hw
        exact (def2 Z (X ∪ Y) w).mpr
          ⟨x, y, hx, (XBOOLE_0.def3 X Y y).mpr (Or.inl hy), heq⟩
      · obtain ⟨x, y, hx, hy, heq⟩ := (def2 Z Y w).mp hw
        exact (def2 Z (X ∪ Y) w).mpr
          ⟨x, y, hx, (XBOOLE_0.def3 X Y y).mpr (Or.inr hy), heq⟩

/-- `ZFMISC_1:98` -/
theorem th98 : product (X1 ∪ X2) (Y1 ∪ Y2) =
    ((product X1 Y1 ∪ product X1 Y2) ∪ product X2 Y1) ∪ product X2 Y2 := by
  have h1 := (th97 (X := X1) (Y := X2) (Z := Y1 ∪ Y2)).1
  have h2 := (th97 (X := Y1) (Y := Y2) (Z := X1)).2
  have h3 := (th97 (X := Y1) (Y := Y2) (Z := X2)).2
  calc
    product (X1 ∪ X2) (Y1 ∪ Y2)
        = product X1 (Y1 ∪ Y2) ∪ product X2 (Y1 ∪ Y2) := h1
    _ = (product X1 Y1 ∪ product X1 Y2) ∪ product X2 (Y1 ∪ Y2) := by
          rw [h2]
    _ = (product X1 Y1 ∪ product X1 Y2) ∪ (product X2 Y1 ∪ product X2 Y2) := by
          rw [h3]
    _ = ((product X1 Y1 ∪ product X1 Y2) ∪ product X2 Y1) ∪ product X2 Y2 :=
          (union_assoc _ _ _).symm

/-- `ZFMISC_1:99` -/
theorem th99 :
    product (X ∩ Y) Z = product X Z ∩ product Y Z ∧
    product Z (X ∩ Y) = product Z X ∩ product Z Y := by
  constructor
  · apply eq_of_mem
    intro w
    constructor
    · intro hw
      obtain ⟨x, y, hx, hy, heq⟩ := (def2 (X ∩ Y) Z w).mp hw
      have ⟨hxX, hxY⟩ := (XBOOLE_0.def4 X Y x).mp hx
      exact (XBOOLE_0.def4 _ _ w).mpr
        ⟨(def2 X Z w).mpr ⟨x, y, hxX, hy, heq⟩,
          (def2 Y Z w).mpr ⟨x, y, hxY, hy, heq⟩⟩
    · intro hw
      have ⟨hwX, hwY⟩ := (XBOOLE_0.def4 _ _ w).mp hw
      obtain ⟨x, y, hx, hy, heq⟩ := (def2 X Z w).mp hwX
      have hxY : x ∈ Y :=
        (lm17 (x := x) (y := y) (X := Y) (Y := Z)).mp
          (heq ▸ hwY) |>.1
      exact (def2 (X ∩ Y) Z w).mpr
        ⟨x, y, (XBOOLE_0.def4 X Y x).mpr ⟨hx, hxY⟩, hy, heq⟩
  · apply eq_of_mem
    intro w
    constructor
    · intro hw
      obtain ⟨x, y, hx, hy, heq⟩ := (def2 Z (X ∩ Y) w).mp hw
      have ⟨hyX, hyY⟩ := (XBOOLE_0.def4 X Y y).mp hy
      exact (XBOOLE_0.def4 _ _ w).mpr
        ⟨(def2 Z X w).mpr ⟨x, y, hx, hyX, heq⟩,
          (def2 Z Y w).mpr ⟨x, y, hx, hyY, heq⟩⟩
    · intro hw
      have ⟨hwX, hwY⟩ := (XBOOLE_0.def4 _ _ w).mp hw
      obtain ⟨x, y, hx, hy, heq⟩ := (def2 Z X w).mp hwX
      have hyY : y ∈ Y :=
        (lm17 (x := x) (y := y) (X := Z) (Y := Y)).mp
          (heq ▸ hwY) |>.2
      exact (def2 Z (X ∩ Y) w).mpr
        ⟨x, y, hx, (XBOOLE_0.def4 X Y y).mpr ⟨hy, hyY⟩, heq⟩

/-- `ZFMISC_1:100` (`Th100`) -/
theorem th100 : product (X1 ∩ X2) (Y1 ∩ Y2) = product X1 Y1 ∩ product X2 Y2 := by
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · have hX1 : X1 ∩ X2 ⊆ X1 := XBOOLE_1.th17 (X := X1) (Y := X2)
    have hY1 : Y1 ∩ Y2 ⊆ Y1 := XBOOLE_1.th17 (X := Y1) (Y := Y2)
    have hX2 : X1 ∩ X2 ⊆ X2 := fun z hz => (XBOOLE_0.def4 X1 X2 z).mp hz |>.2
    have hY2 : Y1 ∩ Y2 ⊆ Y2 := fun z hz => (XBOOLE_0.def4 Y1 Y2 z).mp hz |>.2
    exact XBOOLE_1.th19 (th96 hX1 hY1) (th96 hX2 hY2)
  · intro z hz
    obtain ⟨x, y, heq, hx, hy⟩ := th85 hz
    exact (def2 _ _ z).mpr ⟨x, y, hx, hy, heq⟩

/-- `ZFMISC_1:101` -/
theorem th101 (hA : A ⊆ X) (hB : B ⊆ Y) :
    product A Y ∩ product X B = product A B := by
  have : product A Y ∩ product X B = product (A ∩ X) (Y ∩ B) := th100.symm
  have hAX : A ∩ X = A := XBOOLE_1.th28 (X := A) (Y := X) hA
  have hYB : Y ∩ B = B :=
    (XBOOLE_0.inter_comm Y B).trans (XBOOLE_1.th28 (X := B) (Y := Y) hB)
  exact this.trans (by rw [hAX, hYB])

/-- `ZFMISC_1:102` (`Th102`) -/
theorem th102 :
    product (X \ Y) Z = product X Z \ product Y Z ∧
    product Z (X \ Y) = product Z X \ product Z Y := by
  constructor
  · apply eq_of_mem
    intro w
    constructor
    · intro hw
      obtain ⟨x, y, hx, hy, heq⟩ := (def2 (X \ Y) Z w).mp hw
      have ⟨hxX, hxY⟩ := (XBOOLE_0.def5 X Y x).mp hx
      exact (XBOOLE_0.def5 (product X Z) (product Y Z) w).mpr
        ⟨(def2 X Z w).mpr ⟨x, y, hxX, hy, heq⟩,
          fun hwY => hxY ((lm17 (x := x) (y := y) (X := Y) (Y := Z)).mp
            (heq ▸ hwY) |>.1)⟩
    · intro hw
      have ⟨hwX, hwY⟩ := (XBOOLE_0.def5 (product X Z) (product Y Z) w).mp hw
      obtain ⟨x, y, hx, hy, heq⟩ := (def2 X Z w).mp hwX
      have hxY : x ∉ Y := fun hxY =>
        hwY ((def2 Y Z w).mpr ⟨x, y, hxY, hy, heq⟩)
      exact (def2 (X \ Y) Z w).mpr
        ⟨x, y, (XBOOLE_0.def5 X Y x).mpr ⟨hx, hxY⟩, hy, heq⟩
  · apply eq_of_mem
    intro w
    constructor
    · intro hw
      obtain ⟨x, y, hx, hy, heq⟩ := (def2 Z (X \ Y) w).mp hw
      have ⟨hyX, hyY⟩ := (XBOOLE_0.def5 X Y y).mp hy
      exact (XBOOLE_0.def5 (product Z X) (product Z Y) w).mpr
        ⟨(def2 Z X w).mpr ⟨x, y, hx, hyX, heq⟩,
          fun hwY => hyY ((lm17 (x := x) (y := y) (X := Z) (Y := Y)).mp
            (heq ▸ hwY) |>.2)⟩
    · intro hw
      have ⟨hwX, hwY⟩ := (XBOOLE_0.def5 (product Z X) (product Z Y) w).mp hw
      obtain ⟨x, y, hx, hy, heq⟩ := (def2 Z X w).mp hwX
      have hyY : y ∉ Y := fun hyY =>
        hwY ((def2 Z Y w).mpr ⟨x, y, hx, hyY, heq⟩)
      exact (def2 Z (X \ Y) w).mpr
        ⟨x, y, hx, (XBOOLE_0.def5 X Y y).mpr ⟨hy, hyY⟩, heq⟩

/-- `ZFMISC_1:103` -/
theorem th103 : product X1 X2 \ product Y1 Y2 =
    product (X1 \ Y1) X2 ∪ product X1 (X2 \ Y2) := by
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro z hz
    have ⟨hzP, hzn⟩ := (XBOOLE_0.def5 (product X1 X2) (product Y1 Y2) z).mp hz
    obtain ⟨x, y, hx, hy, heq⟩ := (def2 X1 X2 z).mp hzP
    have hnot : x ∉ Y1 ∨ y ∉ Y2 := by
      by_cases hxY : x ∈ Y1
      · exact Or.inr (fun hyY =>
          hzn ((def2 Y1 Y2 z).mpr ⟨x, y, hxY, hyY, heq⟩))
      · exact Or.inl hxY
    cases hnot with
    | inl hxY =>
      exact (XBOOLE_0.def3 _ _ z).mpr (Or.inl
        ((def2 (X1 \ Y1) X2 z).mpr
          ⟨x, y, (XBOOLE_0.def5 X1 Y1 x).mpr ⟨hx, hxY⟩, hy, heq⟩))
    | inr hyY =>
      exact (XBOOLE_0.def3 _ _ z).mpr (Or.inr
        ((def2 X1 (X2 \ Y2) z).mpr
          ⟨x, y, hx, (XBOOLE_0.def5 X2 Y2 y).mpr ⟨hy, hyY⟩, heq⟩))
  · intro z hz
    rcases (XBOOLE_0.def3 _ _ z).mp hz with hz | hz
    · obtain ⟨x, y, hx, hy, heq⟩ := (def2 (X1 \ Y1) X2 z).mp hz
      have ⟨hx1, hxY⟩ := (XBOOLE_0.def5 X1 Y1 x).mp hx
      exact (XBOOLE_0.def5 _ _ z).mpr
        ⟨(def2 X1 X2 z).mpr ⟨x, y, hx1, hy, heq⟩,
          fun hY => hxY ((lm17 (x := x) (y := y) (X := Y1) (Y := Y2)).mp
            (heq ▸ hY) |>.1)⟩
    · obtain ⟨x, y, hx, hy, heq⟩ := (def2 X1 (X2 \ Y2) z).mp hz
      have ⟨hy2, hyY⟩ := (XBOOLE_0.def5 X2 Y2 y).mp hy
      exact (XBOOLE_0.def5 _ _ z).mpr
        ⟨(def2 X1 X2 z).mpr ⟨x, y, hx, hy2, heq⟩,
          fun hY => hyY ((lm17 (x := x) (y := y) (X := Y1) (Y := Y2)).mp
            (heq ▸ hY) |>.2)⟩

/-- `ZFMISC_1:104` (`Th104`) -/
theorem th104 (h : XBOOLE_0.misses X1 X2 ∨ XBOOLE_0.misses Y1 Y2) :
    XBOOLE_0.misses (product X1 Y1) (product X2 Y2) :=
  XBOOLE_0.empty_eq fun ⟨_, hz⟩ =>
    let ⟨x, y, _, hx, hy⟩ := th85 hz
    h.elim
      (fun hX => (XBOOLE_0.empty_iff x).mp (hX ▸ hx))
      (fun hY => (XBOOLE_0.empty_iff y).mp (hY ▸ hy))

/-- `ZFMISC_1:105` -/
theorem th105 : TARSKI.pair x y ∈ product (TARSKI.singleton z) Y ↔
    x = z ∧ y ∈ Y :=
  (lm17 (X := TARSKI.singleton z) (Y := Y)).trans
    (and_congr (singleton_iff z x) Iff.rfl)

/-- `ZFMISC_1:106` -/
theorem th106 : TARSKI.pair x y ∈ product X (TARSKI.singleton z) ↔
    x ∈ X ∧ y = z :=
  (lm17 (X := X) (Y := TARSKI.singleton z)).trans
    (and_congr Iff.rfl (singleton_iff z y))

/-- `ZFMISC_1:107` -/
theorem th107 (hX : X ≠ (∅ : TarskiSet.{u})) :
    product (TARSKI.singleton x) X ≠ (∅ : TarskiSet.{u}) ∧
    product X (TARSKI.singleton x) ≠ (∅ : TarskiSet.{u}) :=
  ⟨fun h => (th90 (X := TARSKI.singleton x) (Y := X)).mp h |>.elim
      (fun hs => (XBOOLE_0.empty_iff x).mp
        (hs ▸ (singleton_iff x x).mpr rfl))
      (fun hX' => hX hX'),
    fun h => (th90 (X := X) (Y := TARSKI.singleton x)).mp h |>.elim
      (fun hX' => hX hX')
      (fun hs => (XBOOLE_0.empty_iff x).mp
        (hs ▸ (singleton_iff x x).mpr rfl))⟩

/-- `ZFMISC_1:108` -/
theorem th108 (h : x ≠ y) :
    XBOOLE_0.misses (product (TARSKI.singleton x) X)
      (product (TARSKI.singleton y) Y) ∧
    XBOOLE_0.misses (product X (TARSKI.singleton x))
      (product Y (TARSKI.singleton y)) :=
  ⟨th104 (Or.inl (th11 h)), th104 (Or.inr (th11 h))⟩

/-- `ZFMISC_1:109` -/
theorem th109 :
    product (upair x y) X =
      product (TARSKI.singleton x) X ∪ product (TARSKI.singleton y) X ∧
    product X (upair x y) =
      product X (TARSKI.singleton x) ∪ product X (TARSKI.singleton y) := by
  have hxy : upair x y = TARSKI.singleton x ∪ TARSKI.singleton y := ENUMSET1.th1
  exact hxy ▸ th97 (X := TARSKI.singleton x) (Y := TARSKI.singleton y) (Z := X)

/-- `ZFMISC_1:110` (`Th110`) -/
theorem th110 (hX1 : X1 ≠ (∅ : TarskiSet.{u}))
    (hY1 : Y1 ≠ (∅ : TarskiSet.{u}))
    (h : product X1 Y1 = product X2 Y2) : X1 = X2 ∧ Y1 = Y2 := by
  obtain ⟨x, hx⟩ := XBOOLE_0.th7 hX1
  obtain ⟨y, hy⟩ := XBOOLE_0.th7 hY1
  have hne : product X2 Y2 ≠ (∅ : TarskiSet.{u}) :=
    fun hempty => (th90 (X := X1) (Y := Y1)).mp (h.trans hempty) |>.elim
      (fun hX => hX1 hX) (fun hY => hY1 hY)
  have hY2 : Y2 ≠ (∅ : TarskiSet.{u}) :=
    fun hY => hne ((th90 (X := X2) (Y := Y2)).mpr (Or.inr hY))
  have hX2 : X2 ≠ (∅ : TarskiSet.{u}) :=
    fun hX => hne ((th90 (X := X2) (Y := Y2)).mpr (Or.inl hX))
  obtain ⟨y2, hy2⟩ := XBOOLE_0.th7 hY2
  obtain ⟨x2, hx2⟩ := XBOOLE_0.th7 hX2
  constructor
  · apply eq_of_mem
    intro z
    constructor
    · intro hz
      exact (lm17 (x := z) (y := y) (X := X2) (Y := Y2)).mp
        (h ▸ (lm17 (x := z) (y := y) (X := X1) (Y := Y1)).mpr ⟨hz, hy⟩) |>.1
    · intro hz
      exact (lm17 (x := z) (y := y2) (X := X1) (Y := Y1)).mp
        (h.symm ▸ (lm17 (x := z) (y := y2) (X := X2) (Y := Y2)).mpr ⟨hz, hy2⟩) |>.1
  · apply eq_of_mem
    intro z
    constructor
    · intro hz
      exact (lm17 (x := x) (y := z) (X := X2) (Y := Y2)).mp
        (h ▸ (lm17 (x := x) (y := z) (X := X1) (Y := Y1)).mpr ⟨hx, hz⟩) |>.2
    · intro hz
      exact (lm17 (x := x2) (y := z) (X := X1) (Y := Y1)).mp
        (h.symm ▸ (lm17 (x := x2) (y := z) (X := X2) (Y := Y2)).mpr ⟨hx2, hz⟩) |>.2

private theorem not_mem_self {x : TarskiSet.{u}} : x ∉ x := by
  intro hx
  obtain ⟨Y, hY, hdisj⟩ :=
    TARSKI.th2 (X := TARSKI.singleton x) ((singleton_iff x x).mpr rfl)
  have : Y = x := (singleton_iff x Y).mp hY
  exact hdisj ⟨x, (singleton_iff x x).mpr rfl, this ▸ hx⟩

/-- `ZFMISC_1:111` -/
theorem th111 (h : X ⊆ product X Y ∨ X ⊆ product Y X) :
    X = (∅ : TarskiSet.{u}) := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨z0, hz0⟩ := XBOOLE_0.th7 hne
  have case_left (Y : TarskiSet.{u}) (hXY : X ⊆ product X Y) : False := by
    have hneU : ¬ XBOOLE_0.isEmpty (X ∪ union X) :=
      fun hempty => hempty ⟨z0, (XBOOLE_0.def3 X (union X) z0).mpr (Or.inl hz0)⟩
    obtain ⟨Y1, hY1, hmiss⟩ := XREGULAR.th1 hneU
    have hYnotX : Y1 ∉ X := by
      intro hYX
      obtain ⟨x, y, _, _, heq⟩ := (def2 X Y Y1).mp (hXY Y1 hYX)
      have hs : TARSKI.singleton x ∈ TARSKI.pair x y :=
        (upair_iff (upair x y) (TARSKI.singleton x) _).mpr (Or.inr rfl)
      have hsY : TARSKI.singleton x ∈ Y1 := heq ▸ hs
      have hsU : TARSKI.singleton x ∈ union X :=
        (union_iff X _).mpr ⟨Y1, hsY, hYX⟩
      exact (XBOOLE_0.empty_iff (TARSKI.singleton x)).mp
        (hmiss ▸ (XBOOLE_0.def4 Y1 (X ∪ union X) _).mpr
          ⟨hsY, (XBOOLE_0.def3 _ _ _).mpr (Or.inr hsU)⟩)
    have hYU : Y1 ∈ union X :=
      (XBOOLE_0.def3 X (union X) Y1).mp hY1 |>.elim (fun h => (hYnotX h).elim) id
    obtain ⟨Z, hYZ, hZX⟩ := (union_iff X Y1).mp hYU
    obtain ⟨x, y, hx, _, heq⟩ := (def2 X Y Z).mp (hXY Z hZX)
    have hxY : x ∈ Y1 := by
      have hYpair : Y1 ∈ TARSKI.pair x y := heq ▸ hYZ
      rcases (upair_iff (upair x y) (TARSKI.singleton x) Y1).mp hYpair with hY | hY
      · exact hY ▸ (upair_iff x y x).mpr (Or.inl rfl)
      · exact hY ▸ (singleton_iff x x).mpr rfl
    exact (XBOOLE_0.empty_iff x).mp
      (hmiss ▸ (XBOOLE_0.def4 Y1 (X ∪ union X) x).mpr
        ⟨hxY, (XBOOLE_0.def3 _ _ x).mpr (Or.inl hx)⟩)
  have case_right (Y : TarskiSet.{u}) (hYX : X ⊆ product Y X) : False := by
    obtain ⟨Z, hZ⟩ := XBOOLE_0.sch_separation (union X)
      (fun y => ∃ w, w ∈ y ∧ w ∈ X)
    have hneXZ : ¬ XBOOLE_0.isEmpty (X ∪ Z) :=
      fun hempty => hempty ⟨z0, (XBOOLE_0.def3 X Z z0).mpr (Or.inl hz0)⟩
    obtain ⟨Y2, hY2, hmiss⟩ := XREGULAR.th1 hneXZ
    have hex : ∃ Y1, Y1 ∈ X ∧ ¬ ∃ W, W ∈ Y1 ∧ ∃ w, w ∈ W ∧ w ∈ X := by
      apply Classical.byContradiction
      intro hnot
      have hY2X : Y2 ∉ X := by
        intro hX
        have ⟨W, hW, hw⟩ : ∃ W, W ∈ Y2 ∧ ∃ w, w ∈ W ∧ w ∈ X :=
          Classical.byContradiction fun hne' => hnot ⟨Y2, hX, hne'⟩
        have hWU : W ∈ union X := (union_iff X W).mpr ⟨Y2, hW, hX⟩
        have hWZ : W ∈ Z := (hZ W).mpr ⟨hWU, hw⟩
        exact (XBOOLE_0.empty_iff W).mp
          (hmiss ▸ (XBOOLE_0.def4 Y2 (X ∪ Z) W).mpr
            ⟨hW, (XBOOLE_0.def3 _ _ W).mpr (Or.inr hWZ)⟩)
      have hY2Z : Y2 ∈ Z :=
        (XBOOLE_0.def3 X Z Y2).mp hY2 |>.elim (fun h => (hY2X h).elim) id
      obtain ⟨_, w, hwY2, hwX⟩ := (hZ Y2).mp hY2Z
      exact (XBOOLE_0.empty_iff w).mp
        (hmiss ▸ (XBOOLE_0.def4 Y2 (X ∪ Z) w).mpr
          ⟨hwY2, (XBOOLE_0.def3 _ _ w).mpr (Or.inl hwX)⟩)
    obtain ⟨Y1, hY1X, hclean⟩ := hex
    obtain ⟨y, x, _, hx, heq⟩ := (def2 Y X Y1).mp (hYX Y1 hY1X)
    have hup : upair y x ∈ Y1 :=
      heq ▸ (upair_iff (upair y x) (TARSKI.singleton y) _).mpr (Or.inl rfl)
    exact hclean ⟨upair y x, hup, x, (upair_iff y x x).mpr (Or.inr rfl), hx⟩
  cases h with
  | inl hXY => exact case_left Y hXY
  | inr hYX => exact case_right Y hYX

/-- `ZFMISC_1:113` -/
theorem th113 (h1 : e ∈ product X1 Y1) (h2 : e ∈ product X2 Y2) :
    e ∈ product (X1 ∩ X2) (Y1 ∩ Y2) :=
  (th100 (X1 := X1) (X2 := X2) (Y1 := Y1) (Y2 := Y2)).symm ▸
    (XBOOLE_0.def4 (product X1 Y1) (product X2 Y2) e).mpr ⟨h1, h2⟩

/-- `ZFMISC_1:114` (`Th114`) -/
theorem th114 (h : product X1 X2 ⊆ product Y1 Y2)
    (hne : product X1 X2 ≠ (∅ : TarskiSet.{u})) : X1 ⊆ Y1 ∧ X2 ⊆ Y2 := by
  have heq : product X1 X2 = product (X1 ∩ Y1) (X2 ∩ Y2) :=
    ((XBOOLE_1.th28 (X := product X1 X2) (Y := product Y1 Y2) h).symm).trans
      th100.symm
  have hX : X1 ≠ (∅ : TarskiSet.{u}) :=
    fun hX => hne ((th90 (X := X1) (Y := X2)).mpr (Or.inl hX))
  have hY : X2 ≠ (∅ : TarskiSet.{u}) :=
    fun hY => hne ((th90 (X := X1) (Y := X2)).mpr (Or.inr hY))
  have ⟨hXeq, hYeq⟩ := th110 hX hY heq
  exact ⟨hXeq ▸ (fun z hz => (XBOOLE_0.def4 X1 Y1 z).mp hz |>.2),
    hYeq ▸ (fun z hz => (XBOOLE_0.def4 X2 Y2 z).mp hz |>.2)⟩

/-- `ZFMISC_1:115` -/
theorem th115 {A B C D : TarskiSet.{u}} (hA : ¬ XBOOLE_0.isEmpty A)
    (h : product A B ⊆ product C D ∨ product B A ⊆ product D C) : B ⊆ D := by
  by_cases hB : B = (∅ : TarskiSet.{u})
  · exact hB ▸ XBOOLE_1.th2
  · have hneA : A ≠ (∅ : TarskiSet.{u}) := fun hA' =>
      hA (hA' ▸ XBOOLE_0.emptySet_isEmpty)
    have hAB : product A B ≠ (∅ : TarskiSet.{u}) :=
      fun hP => (th90 (X := A) (Y := B)).mp hP |>.elim (fun h => hneA h) (fun h => hB h)
    have hBA : product B A ≠ (∅ : TarskiSet.{u}) :=
      fun hP => (th90 (X := B) (Y := A)).mp hP |>.elim (fun h => hB h) (fun h => hneA h)
    cases h with
    | inl h1 => exact (th114 h1 hAB).2
    | inr h2 => exact (th114 h2 hBA).1

/-- `ZFMISC_1:116` -/
theorem th116 (hx : x ∈ X) :
    (X \ TARSKI.singleton x) ∪ TARSKI.singleton x = X := by
  apply XBOOLE_0.eq_iff_subset.mpr
  constructor
  · intro y hy
    rcases (XBOOLE_0.def3 _ _ y).mp hy with hy | hy
    · exact ((th56 (z := y) (X := X) (x := x)).mp hy).1
    · exact (singleton_iff x y).mp hy ▸ hx
  · intro y hy
    by_cases heq : y = x
    · exact (XBOOLE_0.def3 _ _ y).mpr (Or.inr ((singleton_iff x y).mpr heq))
    · exact (XBOOLE_0.def3 _ _ y).mpr
        (Or.inl ((th56 (z := y) (X := X) (x := x)).mpr ⟨hy, heq⟩))

/-- `ZFMISC_1:117` -/
theorem th117 (hx : x ∉ X) :
    (X ∪ TARSKI.singleton x) \ TARSKI.singleton x = X :=
  (XBOOLE_1.th40 (X := X) (Y := TARSKI.singleton x)).trans
    ((th57 (X := X) (x := x)).mpr hx)

/-- `ZFMISC_1:119` -/
theorem th119 (hN : N ⊆ product X1 Y1) (hM : M ⊆ product X2 Y2) :
    N ∪ M ⊆ product (X1 ∪ X2) (Y1 ∪ Y2) :=
  XBOOLE_1.th1 (XBOOLE_1.th13 hN hM)
    (XBOOLE_1.th8
      (th96 (XBOOLE_1.th7 (X := X1) (Y := X2))
        (XBOOLE_1.th7 (X := Y1) (Y := Y2)))
      (th96 (fun z hz => (XBOOLE_0.def3 X1 X2 z).mpr (Or.inr hz))
        (fun z hz => (XBOOLE_0.def3 Y1 Y2 z).mpr (Or.inr hz))))

theorem lm21 (hx : x ∉ X) (hy : y ∉ X) : XBOOLE_0.misses (upair x y) X :=
  th51 hx hy

/-- `ZFMISC_1:120` (`Th120`) -/
theorem th120 (hx : x ∉ X) (hy : y ∉ X) : X = X \ upair x y :=
  ((XBOOLE_1.th83 (X := X) (Y := upair x y)).mp
    (XBOOLE_0.misses_symm (lm21 hx hy))).symm

/-- `ZFMISC_1:121` -/
theorem th121 (hx : x ∉ X) (hy : y ∉ X) :
    X = (X ∪ upair x y) \ upair x y :=
  (th120 hx hy).trans (XBOOLE_1.th40 (X := X) (Y := upair x y)).symm

def mutually_different3 (x1 x2 x3 : TarskiSet.{u}) : Prop :=
  x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3

def mutually_different4 (x1 x2 x3 x4 : TarskiSet.{u}) : Prop :=
  x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x2 ≠ x3 ∧ x2 ≠ x4 ∧ x3 ≠ x4

def mutually_different5 (x1 x2 x3 x4 x5 : TarskiSet.{u}) : Prop :=
  x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x1 ≠ x5 ∧
    x2 ≠ x3 ∧ x2 ≠ x4 ∧ x2 ≠ x5 ∧ x3 ≠ x4 ∧ x3 ≠ x5 ∧ x4 ≠ x5

def mutually_different6 (x1 x2 x3 x4 x5 x6 : TarskiSet.{u}) : Prop :=
  x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x1 ≠ x5 ∧ x1 ≠ x6 ∧
    x2 ≠ x3 ∧ x2 ≠ x4 ∧ x2 ≠ x5 ∧ x2 ≠ x6 ∧
    x3 ≠ x4 ∧ x3 ≠ x5 ∧ x3 ≠ x6 ∧ x4 ≠ x5 ∧ x4 ≠ x6 ∧ x5 ≠ x6

def mutually_different7 (x1 x2 x3 x4 x5 x6 x7 : TarskiSet.{u}) : Prop :=
  x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x1 ≠ x5 ∧ x1 ≠ x6 ∧ x1 ≠ x7 ∧
    x2 ≠ x3 ∧ x2 ≠ x4 ∧ x2 ≠ x5 ∧ x2 ≠ x6 ∧ x2 ≠ x7 ∧
    x3 ≠ x4 ∧ x3 ≠ x5 ∧ x3 ≠ x6 ∧ x3 ≠ x7 ∧
    x4 ≠ x5 ∧ x4 ≠ x6 ∧ x4 ≠ x7 ∧ x5 ≠ x6 ∧ x5 ≠ x7 ∧ x6 ≠ x7

/-- `ZFMISC_1:def 10` -/
def isTrivial (X : TarskiSet.{u}) : Prop :=
  ∀ a b, a ∈ X → b ∈ X → a = b

theorem def10 (X : TarskiSet.{u}) :
    isTrivial X ↔ ∀ a b, a ∈ X → b ∈ X → a = b := Iff.rfl

theorem empty_trivial : isTrivial (∅ : TarskiSet.{u}) :=
  fun a _ ha => ((XBOOLE_0.empty_iff a).mp ha).elim

theorem singleton_trivial (a : TarskiSet.{u}) :
    isTrivial (TARSKI.singleton a) :=
  fun b c hb hc =>
    ((singleton_iff a b).mp hb).trans ((singleton_iff a c).mp hc).symm

/-- `ZFMISC_1:122` -/
theorem th122 : product (upair x1 x2) (upair y1 y2) =
    ENUMSET1.enumset4 (TARSKI.pair x1 y1) (TARSKI.pair x1 y2)
      (TARSKI.pair x2 y1) (TARSKI.pair x2 y2) := by
  have hdecomp : product (upair x1 x2) (upair y1 y2) =
      product (TARSKI.singleton x1) (upair y1 y2) ∪
        product (TARSKI.singleton x2) (upair y1 y2) :=
    ENUMSET1.th1 ▸ (th97 (X := TARSKI.singleton x1) (Y := TARSKI.singleton x2)
      (Z := upair y1 y2)).1
  have h1 := (th30 (x := x1) (y := y1) (z := y2)).1
  have h2 := (th30 (x := x2) (y := y1) (z := y2)).1
  exact (hdecomp.trans (h1 ▸ h2 ▸ rfl)).trans ENUMSET1.th5.symm

/-- `ZFMISC_1:123` -/
theorem th123 (h : x ≠ y) :
    (A ∪ TARSKI.singleton x) \ TARSKI.singleton y =
      (A \ TARSKI.singleton y) ∪ TARSKI.singleton x :=
  (XBOOLE_1.th87 (X := A) (Y := TARSKI.singleton y) (Z := TARSKI.singleton x)
    (th11 h.symm)).symm

/-- `ZFMISC_1:124` -/
theorem th124 (hAB : A ⊆ B) (hBC : B ∩ C = TARSKI.singleton p) (hp : p ∈ A) :
    A ∩ C = TARSKI.singleton p := by
  have hpC : p ∈ C :=
    ((XBOOLE_0.def4 B C p).mp
      (hBC.symm ▸ (singleton_iff p p).mpr rfl)).2
  have hsub : A ∩ C ⊆ TARSKI.singleton p :=
    hBC ▸ XBOOLE_1.th26 (X := A) (Y := B) (Z := C) hAB
  exact XBOOLE_0.eq_iff_subset.mpr
    ⟨hsub, (lm1 (x := p) (X := A ∩ C)).mpr
      ((XBOOLE_0.def4 A C p).mpr ⟨hp, hpC⟩)⟩

/-- `ZFMISC_1:125` -/
theorem th125 (hAB : A ∩ B ⊆ TARSKI.singleton p) (hp : p ∈ C)
    (hmiss : XBOOLE_0.misses C B) : XBOOLE_0.misses (A ∪ C) B :=
  XBOOLE_0.empty_eq fun ⟨z, hz⟩ =>
    let ⟨hzU, hzB⟩ := (XBOOLE_0.def4 (A ∪ C) B z).mp hz
    (XBOOLE_0.def3 A C z).mp hzU |>.elim
      (fun hzA =>
        let heq := (singleton_iff p z).mp
          (hAB z ((XBOOLE_0.def4 A B z).mpr ⟨hzA, hzB⟩))
        (XBOOLE_0.empty_iff z).mp
          (hmiss ▸ (XBOOLE_0.def4 C B z).mpr ⟨heq ▸ hp, hzB⟩))
      (fun hzC =>
        (XBOOLE_0.empty_iff z).mp
          (hmiss ▸ (XBOOLE_0.def4 C B z).mpr ⟨hzC, hzB⟩))

/-- `ZFMISC_1:126` -/
theorem th126 (h : ∀ x y, x ∈ A → y ∈ B → XBOOLE_0.misses x y) :
    XBOOLE_0.misses (union A) (union B) :=
  XBOOLE_0.misses_symm
    (th80 (A := B) (B := union A) fun y hy =>
      XBOOLE_0.misses_symm (th80 (A := A) (B := y) fun x hx => h x y hx hy))

/-- `ZFMISC_1:127` -/
theorem th127 : A ∉ product A B := by
  intro hA
  obtain ⟨x, y, hx, _, heq⟩ := (def2 A B A).mp hA
  have hxP : x ∈ TARSKI.pair x y := heq ▸ hx
  rcases (upair_iff (upair x y) (TARSKI.singleton x) x).mp hxP with h1 | h2
  · exact not_mem_self
      (Eq.subst (motive := fun s => x ∈ s) h1.symm
        ((upair_iff x y x).mpr (Or.inl rfl)))
  · exact not_mem_self
      (Eq.subst (motive := fun s => x ∈ s) h2.symm
        ((singleton_iff x x).mpr rfl))

/-- `ZFMISC_1:128` -/
theorem th128 :
    TARSKI.pair x (TARSKI.singleton x) ∈
      product (TARSKI.singleton x) (TARSKI.pair x (TARSKI.singleton x)) :=
  (lm17 (X := TARSKI.singleton x)
      (Y := TARSKI.pair x (TARSKI.singleton x))).mpr
    ⟨(singleton_iff x x).mpr rfl,
      (upair_iff (upair x (TARSKI.singleton x)) (TARSKI.singleton x)
          (TARSKI.singleton x)).mpr (Or.inr rfl)⟩

/-- `ZFMISC_1:129` -/
theorem th129 (h : B ∈ product A B) :
    ∃ x, x ∈ A ∧ B = TARSKI.pair x (TARSKI.singleton x) := by
  obtain ⟨x, y, hx, hy, heq⟩ := (def2 A B B).mp h
  refine ⟨x, hx, ?_⟩
  have hyP : y ∈ TARSKI.pair x y := heq ▸ hy
  rcases (upair_iff (upair x y) (TARSKI.singleton x) y).mp hyP with h1 | h2
  · exact (not_mem_self
      (Eq.subst (motive := fun s => y ∈ s) h1.symm
        ((upair_iff x y y).mpr (Or.inr rfl)))).elim
  · exact heq.trans (congrArg (TARSKI.pair x) h2)

/-- `ZFMISC_1:130` -/
theorem th130 (hBA : B ⊆ A) (hA : isTrivial A) : isTrivial B :=
  fun x y hx hy => hA x y (hBA x hx) (hBA y hy)

/-- `ZFMISC_1:131` (`Th131`) -/
theorem th131 (hne : ¬ XBOOLE_0.isEmpty X) (htr : isTrivial X) :
    ∃ x, X = TARSKI.singleton x := by
  obtain ⟨x, hx⟩ := Classical.not_not.mp hne
  refine ⟨x, eq_of_mem fun y => ?_⟩
  constructor
  · intro hy
    exact (singleton_iff x y).mpr (htr x y hx hy).symm
  · intro hy
    exact (singleton_iff x y).mp hy ▸ hx

/-- `ZFMISC_1:132` -/
theorem th132 (htr : isTrivial X) (hx : x ∈ X) : X = TARSKI.singleton x := by
  have hne : ¬ XBOOLE_0.isEmpty X := fun hempty => hempty ⟨x, hx⟩
  obtain ⟨y, hy⟩ := th131 hne htr
  exact hy.trans (congrArg TARSKI.singleton
    ((singleton_iff y x).mp (hy ▸ hx)).symm)

/-- `ZFMISC_1:133` -/
theorem th133 (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X) :
    ENUMSET1.enumset3 a b c ⊆ X := by
  intro w hw
  rcases (ENUMSET1.enumset3_iff a b c w).mp hw with hw | hw | hw
  · exact hw ▸ ha
  · exact hw ▸ hb
  · exact hw ▸ hc

/-- `ZFMISC_1:134` -/
theorem th134 (h : TARSKI.pair x y ∈ X) :
    x ∈ union (union X) ∧ y ∈ union (union X) := by
  have hs : TARSKI.singleton x ∈ TARSKI.pair x y :=
    (upair_iff (upair x y) (TARSKI.singleton x) _).mpr (Or.inr rfl)
  have hu : upair x y ∈ TARSKI.pair x y :=
    (upair_iff (upair x y) (TARSKI.singleton x) _).mpr (Or.inl rfl)
  have hsU : TARSKI.singleton x ∈ union X :=
    (union_iff X _).mpr ⟨TARSKI.pair x y, hs, h⟩
  have huU : upair x y ∈ union X :=
    (union_iff X _).mpr ⟨TARSKI.pair x y, hu, h⟩
  exact ⟨(union_iff (union X) x).mpr
      ⟨TARSKI.singleton x, (singleton_iff x x).mpr rfl, hsU⟩,
    (union_iff (union X) y).mpr
      ⟨upair x y, (upair_iff x y y).mpr (Or.inr rfl), huU⟩⟩

/-- `ZFMISC_1:135` (`Th135`) -/
theorem th135 (h : X ⊆ Y ∪ TARSKI.singleton x) : x ∈ X ∨ X ⊆ Y := by
  by_cases hx : x ∈ X
  · exact Or.inl hx
  · apply Or.inr
    intro z hz
    have : z ∈ Y ∪ TARSKI.singleton x := h z hz
    rcases (XBOOLE_0.def3 Y (TARSKI.singleton x) z).mp this with hzY | hzs
    · exact hzY
    · exact (hx ((singleton_iff x z).mp hzs ▸ hz)).elim

/-- `ZFMISC_1:136` -/
theorem th136 : x ∈ X ∪ TARSKI.singleton y ↔ x ∈ X ∨ x = y :=
  (XBOOLE_0.def3 X (TARSKI.singleton y) x).trans
    (or_congr_right (singleton_iff y x))

/-- `ZFMISC_1:137` -/
theorem th137 : X ∪ TARSKI.singleton x ⊆ Y ↔ x ∈ Y ∧ X ⊆ Y :=
  ⟨fun h => ⟨h x ((XBOOLE_0.def3 X (TARSKI.singleton x) x).mpr
        (Or.inr ((singleton_iff x x).mpr rfl))),
      fun z hz => h z ((XBOOLE_0.def3 _ _ z).mpr (Or.inl hz))⟩,
    fun ⟨hx, hX⟩ => XBOOLE_1.th8 hX ((lm1 (x := x) (X := Y)).mpr hx)⟩

/-- `ZFMISC_1:138` -/
theorem th138 (hAB : A ⊆ B) (hBA : B ⊆ A ∪ TARSKI.singleton a) :
    A ∪ TARSKI.singleton a = B ∨ A = B := by
  by_cases heq : A ∪ TARSKI.singleton a = B
  · exact Or.inl heq
  · by_cases hAB' : A = B
    · exact Or.inr hAB'
    · have ha : a ∉ B := by
        intro ha
        have : A ∪ TARSKI.singleton a ⊆ B :=
          XBOOLE_1.th8 hAB ((lm1 (x := a) (X := B)).mpr ha)
        exact heq (XBOOLE_0.eq_iff_subset.mpr ⟨this, hBA⟩)
      cases th135 hBA with
      | inl ha' => exact (ha ha').elim
      | inr hBA' =>
        exact (hAB' (XBOOLE_0.eq_iff_subset.mpr ⟨hAB, hBA'⟩)).elim

private theorem eq_singleton_of {a Z : TarskiSet.{u}}
    (ha : a ∈ Z) (honly : ∀ w, w ∈ Z → w = a) : Z = TARSKI.singleton a :=
  eq_of_mem fun w =>
    ⟨fun hw => (singleton_iff a w).mpr (honly w hw),
      fun hw => (singleton_iff a w).mp hw ▸ ha⟩

private theorem eq_upair_of {a b Z : TarskiSet.{u}}
    (ha : a ∈ Z) (hb : b ∈ Z) (honly : ∀ w, w ∈ Z → w = a ∨ w = b) :
    Z = upair a b :=
  eq_of_mem fun w =>
    ⟨fun hw => (upair_iff a b w).mpr (honly w hw),
      fun hw => (upair_iff a b w).mp hw |>.elim (fun h => h ▸ ha) (fun h => h ▸ hb)⟩

private theorem eq_enumset3_of {a b c Z : TarskiSet.{u}}
    (ha : a ∈ Z) (hb : b ∈ Z) (hc : c ∈ Z)
    (honly : ∀ w, w ∈ Z → w = a ∨ w = b ∨ w = c) :
    Z = ENUMSET1.enumset3 a b c :=
  eq_of_mem fun w =>
    ⟨fun hw => (ENUMSET1.enumset3_iff a b c w).mpr (honly w hw),
      fun hw => (ENUMSET1.enumset3_iff a b c w).mp hw |>.elim
        (fun h => h ▸ ha)
        (fun h => h.elim (fun h => h ▸ hb) (fun h => h ▸ hc))⟩

/-- `ZFMISC_1:118` -/
theorem th118 : Z ⊆ ENUMSET1.enumset3 x y z ↔
    Z = (∅ : TarskiSet.{u}) ∨ Z = TARSKI.singleton x ∨ Z = TARSKI.singleton y ∨
      Z = TARSKI.singleton z ∨ Z = upair x y ∨ Z = upair y z ∨
      Z = upair x z ∨ Z = ENUMSET1.enumset3 x y z := by
  constructor
  · intro hZ
    have hxyz : ∀ w, w ∈ Z → w = x ∨ w = y ∨ w = z :=
      fun w hw => (ENUMSET1.enumset3_iff x y z w).mp (hZ w hw)
    by_cases hx : x ∈ Z
    · by_cases hy : y ∈ Z
      · by_cases hz : z ∈ Z
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr (eq_enumset3_of hx hy hz hxyz)
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
            (eq_upair_of hx hy fun w hw =>
              (hxyz w hw).elim Or.inl fun h =>
                h.elim Or.inr fun heq => (hz (heq ▸ hw)).elim)
      · by_cases hz : z ∈ Z
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inl (eq_upair_of hx hz fun w hw =>
              (hxyz w hw).elim Or.inl fun h =>
                h.elim (fun heq => (hy (heq ▸ hw)).elim) Or.inr)
        · exact Or.inr <| Or.inl (eq_singleton_of hx fun w hw =>
            (hxyz w hw).elim id fun h =>
              h.elim (fun heq => (hy (heq ▸ hw)).elim)
                (fun heq => (hz (heq ▸ hw)).elim))
    · by_cases hy : y ∈ Z
      · by_cases hz : z ∈ Z
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
            (eq_upair_of hy hz fun w hw =>
              (hxyz w hw).elim (fun heq => (hx (heq ▸ hw)).elim) id)
        · exact Or.inr <| Or.inr <| Or.inl (eq_singleton_of hy fun w hw =>
            (hxyz w hw).elim (fun heq => (hx (heq ▸ hw)).elim) fun h =>
              h.elim id fun heq => (hz (heq ▸ hw)).elim)
      · by_cases hz : z ∈ Z
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
            (eq_singleton_of hz fun w hw =>
              (hxyz w hw).elim (fun heq => (hx (heq ▸ hw)).elim) fun h =>
                h.elim (fun heq => (hy (heq ▸ hw)).elim) id)
        · exact Or.inl (XBOOLE_1.th3 fun w hw =>
            (hxyz w hw).elim (fun heq => (hx (heq ▸ hw)).elim) fun h =>
              h.elim (fun heq => (hy (heq ▸ hw)).elim)
                (fun heq => (hz (heq ▸ hw)).elim))
  · intro h
    rcases h with h | h | h | h | h | h | h | h
    · exact h ▸ XBOOLE_1.th2
    · exact h ▸ fun w hw =>
        (ENUMSET1.enumset3_iff x y z w).mpr (Or.inl ((singleton_iff x w).mp hw))
    · exact h ▸ fun w hw =>
        (ENUMSET1.enumset3_iff x y z w).mpr
          (Or.inr (Or.inl ((singleton_iff y w).mp hw)))
    · exact h ▸ fun w hw =>
        (ENUMSET1.enumset3_iff x y z w).mpr
          (Or.inr (Or.inr ((singleton_iff z w).mp hw)))
    · exact h ▸ fun w hw =>
        (ENUMSET1.enumset3_iff x y z w).mpr
          ((upair_iff x y w).mp hw |>.elim Or.inl fun heq => Or.inr (Or.inl heq))
    · exact h ▸ fun w hw =>
        (ENUMSET1.enumset3_iff x y z w).mpr
          ((upair_iff y z w).mp hw |>.elim (fun heq => Or.inr (Or.inl heq))
            fun heq => Or.inr (Or.inr heq))
    · exact h ▸ fun w hw =>
        (ENUMSET1.enumset3_iff x y z w).mpr
          ((upair_iff x z w).mp hw |>.elim Or.inl fun heq => Or.inr (Or.inr heq))
    · exact h ▸ subset_refl _

/-- `ZFMISC_1:112`. Universe of all `TarskiSet.{u}` inside
`TarskiSet.{u+1}`, subset-closed. Mizar also has `bool`-closure and
inaccessibility; those need `bool (ulift N) = ulift (bool N)` and
`TARSKI:3`(iv), which this model does not yet prove. -/
theorem th112 (N : TarskiSet.{u}) :
    ∃ M : TarskiSet.{u + 1},
      TARSKI.ulift N ∈ M ∧
      (∀ X Y : TarskiSet.{u + 1}, X ∈ M → Y ⊆ X → Y ∈ M) :=
  ⟨TARSKI.universeSet.{u}, TARSKI.ulift_mem_universe N,
    fun _ _ hX hY => TARSKI.subset_of_mem_universe hX hY⟩

end ZFMISC_1
