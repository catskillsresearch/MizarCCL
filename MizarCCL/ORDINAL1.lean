import MizarCCL.FUNCT_1
import MizarCCL.XREGULAR

/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/ordinal1.miz`.
Authors: Grzegorz Bancerek (Mizar), Lars Warren Ericson (Lean 4).
-/

/-!
# Ordinal numbers

1–1 Lean rendering of Mizar article `ORDINAL1`
(`vendor/mml/ordinal1.miz`). Import is `FUNCT_1` and `XREGULAR`.
Canceled: `th1`–`th4`.
-/

universe u

open TarskiSet TARSKI

namespace ORDINAL1

theorem not_mem_self (x : TarskiSet.{u}) : x ∉ x :=
  fun hx =>
    let ⟨Y, hY, hdisj⟩ := TARSKI.th2 ((singleton_iff x x).mpr rfl)
    let heq : Y = x := (singleton_iff x Y).mp hY
    hdisj ⟨x, (singleton_iff x x).mpr rfl,
      Eq.subst (motive := fun s => x ∈ s) heq.symm hx⟩

theorem not_two_cycle {x y : TarskiSet.{u}} : ¬ (x ∈ y ∧ y ∈ x) :=
  fun ⟨hxy, hyx⟩ =>
    let ⟨Z, hZ, hdisj⟩ :=
      TARSKI.th2 (X := upair x y) ((upair_iff x y x).mpr (Or.inl rfl))
    Or.elim ((upair_iff x y Z).mp hZ)
      (fun hZx =>
        hdisj ⟨y, (upair_iff x y y).mpr (Or.inr rfl),
          Eq.subst (motive := fun s => y ∈ s) hZx.symm hyx⟩)
      (fun hZy =>
        hdisj ⟨x, (upair_iff x y x).mpr (Or.inl rfl),
          Eq.subst (motive := fun s => x ∈ s) hZy.symm hxy⟩)

/-- `ORDINAL1:5` (`Th5`). Canceled `1`–`4`. -/
theorem th5 {Y X : TarskiSet.{u}} (h : Y ∈ X) : ¬ X ⊆ Y :=
  fun hsub => not_mem_self Y (hsub Y h)

/-- `ORDINAL1:def 1` — `succ X = X ∪ {X}`. -/
noncomputable def succ (X : TarskiSet.{u}) : TarskiSet.{u} :=
  X ∪ TARSKI.singleton X

theorem succ_def (X : TarskiSet.{u}) : succ X = X ∪ TARSKI.singleton X :=
  rfl

theorem succ_nonempty (X : TarskiSet.{u}) : ¬ XBOOLE_0.isEmpty (succ X) :=
  fun hempty =>
    hempty ⟨X, (XBOOLE_0.def3 X (TARSKI.singleton X) X).mpr
      (Or.inr ((singleton_iff X X).mpr rfl))⟩

/-- `ORDINAL1:6` (`Th6`) -/
theorem th6 (X : TarskiSet.{u}) : X ∈ succ X :=
  (XBOOLE_0.def3 X (TARSKI.singleton X) X).mpr
    (Or.inr ((singleton_iff X X).mpr rfl))

/-- `ORDINAL1:8` (`Th8`) -/
theorem th8 (x X : TarskiSet.{u}) : x ∈ succ X ↔ x ∈ X ∨ x = X :=
  Iff.trans (XBOOLE_0.def3 X (TARSKI.singleton X) x)
    ⟨fun o => Or.elim o Or.inl fun hs => Or.inr ((singleton_iff X x).mp hs),
      fun o => Or.elim o Or.inl fun heq =>
        Or.inr ((singleton_iff X x).mpr heq)⟩

/-- `ORDINAL1:7` -/
theorem th7 {X Y : TarskiSet.{u}} (h : succ X = succ Y) : X = Y :=
  Classical.byContradiction fun hne =>
    let hY := (th8 Y X).mp
      (Eq.subst (motive := fun s => Y ∈ s) h.symm (th6 Y))
    let hX := (th8 X Y).mp
      (Eq.subst (motive := fun s => X ∈ s) h (th6 X))
    let hYinX : Y ∈ X :=
      Or.elim hY (fun hx => hx) fun heq => (hne heq.symm).elim
    let hXinY : X ∈ Y :=
      Or.elim hX (fun hy => hy) fun heq => (hne heq).elim
    let ⟨Z, hZ, hdisj⟩ :=
      TARSKI.th2 (X := upair X Y) ((upair_iff X Y X).mpr (Or.inl rfl))
    Or.elim ((upair_iff X Y Z).mp hZ)
      (fun hZX =>
        hdisj ⟨Y, (upair_iff X Y Y).mpr (Or.inr rfl),
          Eq.subst (motive := fun s => Y ∈ s) hZX.symm hYinX⟩)
      (fun hZY =>
        hdisj ⟨X, (upair_iff X Y X).mpr (Or.inl rfl),
          Eq.subst (motive := fun s => X ∈ s) hZY.symm hXinY⟩)

/-- `ORDINAL1:9` (`Th9`) -/
theorem th9 (X : TarskiSet.{u}) : X ≠ succ X :=
  fun heq => not_mem_self X
    (Eq.subst (motive := fun s => X ∈ s) heq.symm (th6 X))

/-- `ORDINAL1:def 2` -/
def isEpsilonTransitive (X : TarskiSet.{u}) : Prop :=
  ∀ x, x ∈ X → x ⊆ X

theorem def2 (X : TarskiSet.{u}) :
    isEpsilonTransitive X ↔ ∀ x, x ∈ X → x ⊆ X :=
  Iff.rfl

/-- `ORDINAL1:def 3` -/
def isEpsilonConnected (X : TarskiSet.{u}) : Prop :=
  ∀ x y, x ∈ X → y ∈ X → x ∈ y ∨ x = y ∨ y ∈ x

theorem def3 (X : TarskiSet.{u}) :
    isEpsilonConnected X ↔
      ∀ x y, x ∈ X → y ∈ X → x ∈ y ∨ x = y ∨ y ∈ x :=
  Iff.rfl

/-- `ORDINAL1:lm 1` -/
theorem lm1 :
    isEpsilonTransitive (∅ : TarskiSet.{u}) ∧
      isEpsilonConnected (∅ : TarskiSet.{u}) :=
  ⟨fun x hx => ((XBOOLE_0.empty_iff x).mp hx).elim,
    fun x _ hx => ((XBOOLE_0.empty_iff x).mp hx).elim⟩

/-- `ORDINAL1:def 4` -/
def isOrdinal (IT : TarskiSet.{u}) : Prop :=
  isEpsilonTransitive IT ∧ isEpsilonConnected IT

theorem def4 (IT : TarskiSet.{u}) :
    isOrdinal IT ↔ isEpsilonTransitive IT ∧ isEpsilonConnected IT :=
  Iff.rfl

theorem empty_isOrdinal : isOrdinal (∅ : TarskiSet.{u}) :=
  lm1

/-- `ORDINAL1:10` (`Th10`) -/
theorem th10 {A B C : TarskiSet.{u}} (hC : isEpsilonTransitive C)
    (hAB : A ∈ B) (hBC : B ∈ C) : A ∈ C :=
  hC B hBC A hAB

private theorem eq_of_mem {A B : TarskiSet.{u}}
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  extensionality h

/-- `ORDINAL1:11` (`Th11`) -/
theorem th11 {x A : TarskiSet.{u}} (hx : isEpsilonTransitive x)
    (hA : isOrdinal A) (hss : x ⊂ A) : x ∈ A := by
  have hxA : x ⊆ A := hss.1
  have hne : A \ x ≠ (∅ : TarskiSet.{u}) := fun heq =>
    hss.2 ((XBOOLE_0.def10).mpr
      ⟨hxA, (XBOOLE_1.th37 (X := A) (Y := x)).mp heq⟩)
  obtain ⟨t, ht⟩ := XBOOLE_0.th7 hne
  obtain ⟨y, hy, hmin⟩ := TARSKI.th2 ht
  have hyA : y ∈ A := ((XBOOLE_0.def5 A x y).mp hy).1
  have hynx : y ∉ x := ((XBOOLE_0.def5 A x y).mp hy).2
  have hxy : x ⊆ y := by
    intro a ha
    have hza : a ⊆ x := hx a ha
    have hyna : y ∉ a := fun hya => hynx (hza y hya)
    have haA : a ∈ A := hxA a ha
    rcases hA.2 a y haA hyA with h | h | h
    · exact h
    · exact (hynx (h ▸ ha)).elim
    · exact (hyna h).elim
  have hyAsub : y ⊆ A := hA.1 y hyA
  have hyx : y ⊆ x := by
    intro a ha
    have hnot : ¬ (a ∈ A ∧ a ∉ x) := fun hAx =>
      hmin ⟨a, (XBOOLE_0.def5 A x a).mpr hAx, ha⟩
    have haA : a ∈ A := hyAsub a ha
    exact Classical.not_not.mp (fun hnx => hnot ⟨haA, hnx⟩)
  exact Eq.subst (motive := fun s => s ∈ A)
    (XBOOLE_0.def10.mpr ⟨hxy, hyx⟩).symm hyA

/-- Unlabeled `ORDINAL1` after `Th11` (`L216`). -/
theorem th12 {A B C : TarskiSet.{u}} (hA : isEpsilonTransitive A)
    (_hB : isOrdinal B) (hC : isOrdinal C) (hAB : A ⊆ B) (hBC : B ∈ C) :
    A ∈ C := by
  have hBsub : B ⊆ C := hC.1 B hBC
  have hAC : A ⊆ C := XBOOLE_1.th1 hAB hBsub
  have hne : A ≠ C := fun heq => th5 hBC (heq ▸ hAB)
  exact th11 hA hC ⟨hAC, hne⟩

/-- `ORDINAL1:13` (`Th13`) -/
theorem th13 {a A : TarskiSet.{u}} (hA : isOrdinal A) (ha : a ∈ A) :
    isOrdinal a := by
  have haA : a ⊆ A := hA.1 a ha
  have htrans : isEpsilonTransitive a := by
    intro y hy
    refine fun b hb => ?_
    apply Classical.byContradiction
    intro hnba
    have hbdiff : b ∈ y \ a :=
      (XBOOLE_0.def5 y a b).mpr ⟨hb, hnba⟩
    obtain ⟨z, hz, hmin⟩ := TARSKI.th2 hbdiff
    have hzy : z ∈ y := ((XBOOLE_0.def5 y a z).mp hz).1
    have hzna : z ∉ a := ((XBOOLE_0.def5 y a z).mp hz).2
    have hyA : y ∈ A := haA y hy
    have hzA : z ∈ A := hA.1 y hyA z hzy
    rcases hA.2 z a hzA ha with hza | heq | haz
    · exact hzna hza
    · exact not_two_cycle ⟨hzy, Eq.subst (motive := fun s => y ∈ s) heq.symm hy⟩
    · exact XREGULAR.th7 ⟨hzy, hy, haz⟩
  have hconn : isEpsilonConnected a :=
    fun y z hy hz => hA.2 y z (haA y hy) (haA z hz)
  exact ⟨htrans, hconn⟩

/-- `ORDINAL1:14` (`Th14`) -/
theorem th14 {A B : TarskiSet.{u}} (hA : isOrdinal A) (hB : isOrdinal B) :
    A ∈ B ∨ A = B ∨ B ∈ A := by
  apply Classical.byContradiction
  intro h
  have hnAB : A ∉ B := fun hAB => h (Or.inl hAB)
  have hne : A ≠ B := fun heq => h (Or.inr (Or.inl heq))
  have hnss : ¬ A ⊂ B := fun hss => hnAB (th11 hA.1 hB hss)
  have hnsub : ¬ A ⊆ B := fun hsub => hnss ⟨hsub, hne⟩
  have hex : ∃ a, a ∈ A ∧ a ∉ B :=
    Classical.byContradiction fun hnex =>
      hnsub (fun x hx =>
        Classical.not_not.mp (fun hnx =>
          hnex ⟨x, hx, hnx⟩))
  obtain ⟨a, haA, hanB⟩ := hex
  have hAdiff : a ∈ A \ B :=
    (XBOOLE_0.def5 A B a).mpr ⟨haA, hanB⟩
  obtain ⟨X, hX, hmin⟩ := TARSKI.th2 hAdiff
  have hXA : X ∈ A := ((XBOOLE_0.def5 A B X).mp hX).1
  have hXnB : X ∉ B := ((XBOOLE_0.def5 A B X).mp hX).2
  have hXord : isOrdinal X := th13 hA hXA
  have hXsubA : X ⊆ A := hA.1 X hXA
  have hXsubB : X ⊆ B := by
    intro b hb
    have hnot : ¬ (b ∈ A ∧ b ∉ B) := fun hAB =>
      hmin ⟨b, (XBOOLE_0.def5 A B b).mpr hAB, hb⟩
    have hbA : b ∈ A := hXsubA b hb
    exact Classical.not_not.mp (fun hnb => hnot ⟨hbA, hnb⟩)
  have hXB : X ⊂ B ∨ X = B :=
    Or.elim (Classical.em (X = B)) Or.inr
      (fun hne => Or.inl ⟨hXsubB, hne⟩)
  exact Or.elim hXB
    (fun hss => hXnB (th11 hXord.1 hB hss))
    (fun heq => h (Or.inr (Or.inr (heq ▸ hXA))))

/-- Redefine of `c=` on ordinals (`ORDINAL1:def 5`). Compatibility
is `TARSKI:def 3`; connectedness is the next theorem. -/
theorem def5 {A B : TarskiSet.{u}} (hA : isOrdinal A) :
    A ⊆ B ↔ ∀ C, isOrdinal C → C ∈ A → C ∈ B :=
  ⟨fun hsub _ _ hC => hsub _ hC,
    fun h x hx => h x (th13 hA hx) hx⟩

/-- Unlabeled `ORDINAL1` after the `c=` redefine (`L319`). -/
theorem th15 {A B : TarskiSet.{u}} (hA : isOrdinal A) (hB : isOrdinal B) :
    XBOOLE_0.are_ccomparable A B :=
  Or.elim (th14 hA hB)
    (fun hAB => Or.inl (hB.1 A hAB))
    (fun h => Or.elim h
      (fun heq => Or.inl (Eq.subst (motive := fun s => s ⊆ B) heq.symm
        (fun _ hx => hx)))
      (fun hBA => Or.inr (hA.1 B hBA)))

/-- `ORDINAL1:16` (`Th16`) -/
theorem th16 {A B : TarskiSet.{u}} (hA : isOrdinal A) (hB : isOrdinal B) :
    A ⊆ B ∨ B ∈ A :=
  Or.elim (th14 hA hB)
    (fun hAB => Or.inl (hB.1 A hAB))
    (fun h => Or.elim h
      (fun heq => Or.inl (Eq.subst (motive := fun s => s ⊆ B) heq.symm
        (fun _ hx => hx)))
      Or.inr)

/-- `ORDINAL1:17` (`Th17`) -/
theorem th17 {x : TarskiSet.{u}} (hx : isOrdinal x) : isOrdinal (succ x) := by
  have htrans : isEpsilonTransitive (succ x) := by
    intro y hy
    rcases (th8 y x).mp hy with hyx | heq
    · exact XBOOLE_1.th1 (hx.1 y hyx) (XBOOLE_1.th7 (X := x) (Y := TARSKI.singleton x))
    · exact Eq.subst (motive := fun s => s ⊆ succ x) heq.symm
        (XBOOLE_1.th7 (X := x) (Y := TARSKI.singleton x))
  have hconn : isEpsilonConnected (succ x) := by
    intro y z hy hz
    have hy' := (th8 y x).mp hy
    have hz' := (th8 z x).mp hz
    rcases hy' with hyx | hey
    · rcases hz' with hzx | hez
      · exact hx.2 y z hyx hzx
      · exact Or.inl (hez ▸ hyx)
    · rcases hz' with hzx | hez
      · exact Or.inr (Or.inr (hey ▸ hzx))
      · exact Or.inr (Or.inl (hey.trans hez.symm))
  exact ⟨htrans, hconn⟩

/-- `ORDINAL1:18` (`Th18`) -/
theorem th18 {x : TarskiSet.{u}} (hx : isOrdinal x) :
    isOrdinal (TARSKI.union x) := by
  have htrans : isEpsilonTransitive (TARSKI.union x) := by
    intro y hy
    obtain ⟨z, hyz, hzx⟩ := (TARSKI.def4 x y).mp hy
    have hzord : isOrdinal z := th13 hx hzx
    have hyx : y ∈ x := hx.1 z hzx y hyz
    exact ZFMISC_1.th74 hyx
  have hconn : isEpsilonConnected (TARSKI.union x) := by
    intro y z hy hz
    obtain ⟨X, hyX, hXx⟩ := (TARSKI.def4 x y).mp hy
    obtain ⟨Y, hzY, hYx⟩ := (TARSKI.def4 x z).mp hz
    have hXord : isOrdinal X := th13 hx hXx
    have hYord : isOrdinal Y := th13 hx hYx
    exact th14 (th13 hXord hyX) (th13 hYord hzY)
  exact ⟨htrans, hconn⟩

/-- `ORDINAL1:19` (`Th19`) -/
theorem th19 {X : TarskiSet.{u}}
    (h : ∀ x, x ∈ X → isOrdinal x ∧ x ⊆ X) : isOrdinal X :=
  ⟨fun x hx => (h x hx).2,
    fun x y hx hy => th14 (h x hx).1 (h y hy).1⟩

/-- `ORDINAL1:20` (`Th20`) -/
theorem th20 {X A : TarskiSet.{u}} (hA : isOrdinal A) (hXA : X ⊆ A)
    (hne : X ≠ (∅ : TarskiSet.{u})) :
    ∃ C, C ∈ X ∧ ∀ B, B ∈ X → C ⊆ B := by
  obtain ⟨t, ht⟩ := XBOOLE_0.th7 hne
  obtain ⟨Y, hY, hmin⟩ := TARSKI.th2 ht
  have hYord : isOrdinal Y := th13 hA (hXA Y hY)
  refine ⟨Y, hY, ?_⟩
  intro B hB
  have hnBY : B ∉ Y := fun hBY => hmin ⟨B, hB, hBY⟩
  rcases th14 (th13 hA (hXA B hB)) hYord with hBYin | heq | hYB
  · exact (hnBY hBYin).elim
  · exact Eq.subst (motive := fun s => s ⊆ B) heq (fun x hx => hx)
  · exact (th13 hA (hXA B hB)).1 Y hYB

/-- `ORDINAL1:21` (`Th21`) -/
theorem th21 {A B : TarskiSet.{u}} (_hA : isOrdinal A) (hB : isOrdinal B) :
    A ∈ B ↔ succ A ⊆ B := by
  constructor
  · intro hAB
    have hsing : TARSKI.singleton A ⊆ B :=
      fun a ha => (singleton_iff A a).mp ha ▸ hAB
    exact XBOOLE_1.th8 (hB.1 A hAB) hsing
  · intro hsub
    exact hsub A (th6 A)

/-- `ORDINAL1:22` (`Th22`) -/
theorem th22 {A C : TarskiSet.{u}} (hA : isOrdinal A) (hC : isOrdinal C) :
    A ∈ succ C ↔ A ⊆ C := by
  constructor
  · intro h
    rcases (th8 A C).mp h with hAC | heq
    · exact hC.1 A hAC
    · exact Eq.subst (motive := fun s => s ⊆ C) heq.symm (fun x hx => hx)
  · intro hAC
    apply Classical.byContradiction
    intro hn
    have hsucc : isOrdinal (succ C) := th17 hC
    rcases th14 hA hsucc with hAs | heq | hsA
    · exact hn hAs
    · have hsub : succ C ⊆ C :=
        Eq.subst (motive := fun s => s ⊆ C) heq hAC
      have hCsub : C ⊆ succ C :=
        XBOOLE_1.th7 (X := C) (Y := TARSKI.singleton C)
      exact th9 C ((XBOOLE_0.def10).mpr ⟨hCsub, hsub⟩)
    · have hsub : succ C ⊆ C := XBOOLE_1.th1 (hA.1 (succ C) hsA) hAC
      have hCsub : C ⊆ succ C :=
        XBOOLE_1.th7 (X := C) (Y := TARSKI.singleton C)
      exact th9 C ((XBOOLE_0.def10).mpr ⟨hCsub, hsub⟩)

/-- `ORDINAL1:sch OrdinalMin` -/
theorem sch_OrdinalMin (P : TarskiSet.{u} → Prop)
    (hex : ∃ A, isOrdinal A ∧ P A) :
    ∃ A, isOrdinal A ∧ P A ∧ ∀ B, isOrdinal B → P B → A ⊆ B := by
  obtain ⟨A0, hA0, hP0⟩ := hex
  obtain ⟨X, hX⟩ :=
    XBOOLE_0.sch_separation (succ A0) (fun x => isOrdinal x ∧ P x)
  have hXsub : X ⊆ succ A0 := fun x hx => ((hX x).mp hx).1
  have hXne : X ≠ (∅ : TarskiSet.{u}) := fun hempty =>
    (XBOOLE_0.empty_iff A0).mp
      (Eq.subst (motive := fun s => A0 ∈ s) hempty
        ((hX A0).mpr ⟨th6 A0, hA0, hP0⟩))
  obtain ⟨C, hC, hleast⟩ := th20 (th17 hA0) hXsub hXne
  have ⟨_, hCord, hPC⟩ := (hX C).mp hC
  refine ⟨C, hCord, hPC, ?_⟩
  intro B hBord hPB
  apply Classical.byContradiction
  intro hnsub
  have hBsubC : B ⊆ C :=
    Or.elim (th15 hCord hBord)
      (fun hCB => (hnsub hCB).elim)
      (fun hBC => hBC)
  have hne : B ≠ C := fun heq =>
    hnsub (Eq.subst (motive := fun s => C ⊆ s) heq.symm
      (fun _ hx => hx))
  have hBin : B ∈ C := th11 hBord.1 hCord ⟨hBsubC, hne⟩
  have hCsucc : C ⊆ succ A0 := (th17 hA0).1 C ((hX C).mp hC).1
  have hBX : B ∈ X :=
    (hX B).mpr ⟨hCsucc B hBin, hBord, hPB⟩
  exact hnsub (hleast B hBX)

/-- `ORDINAL1:sch TransfiniteInd` -/
theorem sch_TransfiniteInd (P : TarskiSet.{u} → Prop)
    (hind : ∀ A, isOrdinal A → (∀ C, C ∈ A → P C) → P A)
    (A : TarskiSet.{u}) (hA : isOrdinal A) : P A := by
  obtain ⟨Z, hZ⟩ :=
    XBOOLE_0.sch_separation (succ A) (fun x => isOrdinal x ∧ P x)
  have hempty : succ A \ Z = (∅ : TarskiSet.{u}) := by
    apply Classical.byContradiction
    intro hne
    have hDsub : succ A \ Z ⊆ succ A :=
      fun x hx => ((XBOOLE_0.def5 (succ A) Z x).mp hx).1
    obtain ⟨C, hC, hleast⟩ := th20 (th17 hA) hDsub hne
    have hCY : C ∈ succ A := ((XBOOLE_0.def5 (succ A) Z C).mp hC).1
    have hCnZ : C ∉ Z := ((XBOOLE_0.def5 (succ A) Z C).mp hC).2
    have hCord : isOrdinal C := th13 (th17 hA) hCY
    have hCsub : C ⊆ succ A := (th17 hA).1 C hCY
    have hindC : ∀ B, B ∈ C → P B := by
      intro B hB
      have hBZ : B ∈ Z := by
        apply Classical.byContradiction
        intro hnZ
        have hBdiff : B ∈ succ A \ Z :=
          (XBOOLE_0.def5 (succ A) Z B).mpr ⟨hCsub B hB, hnZ⟩
        have hCle : C ⊆ B := hleast B hBdiff
        exact th5 hB hCle
      exact ((hZ B).mp hBZ).2.2
    have hPC : P C := hind C hCord hindC
    exact hCnZ ((hZ C).mpr ⟨hCY, hCord, hPC⟩)
  have hAin : A ∈ Z :=
    (XBOOLE_1.th37 (X := succ A) (Y := Z)).mp hempty A (th6 A)
  exact ((hZ A).mp hAin).2.2

/-- `ORDINAL1:23` (`Th23`) -/
theorem th23 {X : TarskiSet.{u}} (h : ∀ a, a ∈ X → isOrdinal a) :
    isOrdinal (TARSKI.union X) := by
  have htrans : isEpsilonTransitive (TARSKI.union X) := by
    intro x hx
    obtain ⟨Y, hxY, hYX⟩ := (TARSKI.def4 X x).mp hx
    have hY : isOrdinal Y := h Y hYX
    have hxYsub : x ⊆ Y := hY.1 x hxY
    intro a ha
    exact (TARSKI.def4 X a).mpr ⟨Y, hxYsub a ha, hYX⟩
  have hconn : isEpsilonConnected (TARSKI.union X) := by
    intro x y hx hy
    obtain ⟨Z, hyZ, hZX⟩ := (TARSKI.def4 X y).mp hy
    obtain ⟨Y, hxY, hYX⟩ := (TARSKI.def4 X x).mp hx
    exact th14 (th13 (h Y hYX) hxY) (th13 (h Z hZX) hyZ)
  exact ⟨htrans, hconn⟩

/-- `ORDINAL1:24` (`Th24`) -/
theorem th24 {X : TarskiSet.{u}} (h : ∀ a, a ∈ X → isOrdinal a) :
    ∃ A, isOrdinal A ∧ X ⊆ A := by
  have hU : isOrdinal (TARSKI.union X) := th23 h
  refine ⟨succ (TARSKI.union X), th17 hU, ?_⟩
  intro a ha
  have hA : isOrdinal a := h a ha
  have hsub : a ⊆ TARSKI.union X :=
    fun b hb => (TARSKI.def4 X b).mpr ⟨a, hb, ha⟩
  exact (th22 hA hU).mpr hsub

/-- `ORDINAL1:25` (`Th25`) -/
theorem th25 : ¬ ∃ X : TarskiSet.{u}, ∀ x, x ∈ X ↔ isOrdinal x := by
  intro ⟨X, hX⟩
  have htrans : isEpsilonTransitive X := by
    intro x hx a ha
    exact (hX a).mpr (th13 ((hX x).mp hx) ha)
  have hconn : isEpsilonConnected X :=
    fun x y hx hy => th14 ((hX x).mp hx) ((hX y).mp hy)
  exact not_mem_self X ((hX X).mpr ⟨htrans, hconn⟩)

/-- `ORDINAL1:26` (`Th26`). `A` is reserved as an ordinal. -/
theorem th26 : ¬ ∃ X : TarskiSet.{u}, ∀ A, isOrdinal A → A ∈ X := by
  intro ⟨X, hX⟩
  obtain ⟨Y, hY⟩ :=
    XBOOLE_0.sch_separation X (fun a => isOrdinal a)
  exact th25 ⟨Y, fun x =>
    ⟨fun hx => ((hY x).mp hx).2,
      fun hord => (hY x).mpr ⟨hX x hord, hord⟩⟩⟩

/-- Unlabeled `ORDINAL1` after `Th26` (`L701`). -/
theorem th27 (X : TarskiSet.{u}) :
    ∃ A, isOrdinal A ∧ A ∉ X ∧ ∀ B, isOrdinal B → B ∉ X → A ⊆ B := by
  have hex : ∃ B, isOrdinal B ∧ B ∉ X :=
    Classical.byContradiction fun hne =>
      th26 ⟨X, fun A hA =>
        Classical.not_not.mp (fun hn => hne ⟨A, hA, hn⟩)⟩
  obtain ⟨B0, hB0, hB0n⟩ := hex
  obtain ⟨Y, hY⟩ :=
    XBOOLE_0.sch_separation (succ B0) (fun a => a ∉ X)
  have hYsub : Y ⊆ succ B0 := fun a ha => ((hY a).mp ha).1
  have hYne : Y ≠ (∅ : TarskiSet.{u}) := fun hempty =>
    (XBOOLE_0.empty_iff B0).mp
      (Eq.subst (motive := fun s => B0 ∈ s) hempty
        ((hY B0).mpr ⟨th6 B0, hB0n⟩))
  obtain ⟨A, hA, hleast⟩ := th20 (th17 hB0) hYsub hYne
  have hAord : isOrdinal A := th13 (th17 hB0) ((hY A).mp hA).1
  have hAnX : A ∉ X := ((hY A).mp hA).2
  have hAsub : A ⊆ succ B0 := (th17 hB0).1 A ((hY A).mp hA).1
  refine ⟨A, hAord, hAnX, ?_⟩
  intro C hCord hCnX
  apply Classical.byContradiction
  intro hnsub
  have hCinA : C ∈ A :=
    Or.elim (th14 hAord hCord)
      (fun hAC => (hnsub (hCord.1 A hAC)).elim)
      (fun h => Or.elim h
        (fun heq => (hnsub (Eq.subst (motive := fun s => A ⊆ s) heq
          (fun _ hx => hx))).elim)
        (fun hCA => hCA))
  exact hnsub (hleast C ((hY C).mpr ⟨hAsub C hCinA, hCnX⟩))

/-- `ORDINAL1:def 6` -/
def isLimitOrdinal (A : TarskiSet.{u}) : Prop :=
  A = TARSKI.union A

theorem def6 (A : TarskiSet.{u}) :
    isLimitOrdinal A ↔ A = TARSKI.union A :=
  Iff.rfl

/-- `ORDINAL1:28` (`Th28`) -/
theorem th28 {A : TarskiSet.{u}} (hA : isOrdinal A) :
    isLimitOrdinal A ↔ ∀ C, C ∈ A → succ C ∈ A := by
  constructor
  · intro hlim C hC
    have hAU : A = TARSKI.union A := hlim
    obtain ⟨z, hCz, hzA⟩ :=
      (TARSKI.def4 A C).mp (Eq.subst (motive := fun s => C ∈ s) hAU hC)
    have hzord : isOrdinal z := th13 hA hzA
    have hsing : TARSKI.singleton C ⊆ z :=
      fun b hb => (singleton_iff C b).mp hb ▸ hCz
    have hsucc : succ C ⊆ z := XBOOLE_1.th8 (hzord.1 C hCz) hsing
    have hcases : succ C = z ∨ succ C ⊂ z :=
      Or.elim (Classical.em (succ C = z)) Or.inl
        (fun hne => Or.inr ⟨hsucc, hne⟩)
    have hsin : succ C = z ∨ succ C ∈ z :=
      Or.elim hcases Or.inl
        (fun hss => Or.inr (th11 (th17 (th13 hA hC)).1 hzord hss))
    have hzsub : z ⊆ A := hA.1 z hzA
    exact Or.elim hsin (fun heq => heq ▸ hzA) (fun hin => hzsub _ hin)
  · intro hcl
    have hAsubU : A ⊆ TARSKI.union A := by
      intro a ha
      have hsucc : succ a ∈ A := hcl a ha
      exact (TARSKI.def4 A a).mpr ⟨succ a, th6 a, hsucc⟩
    have hUsubA : TARSKI.union A ⊆ A := by
      intro a ha
      obtain ⟨z, haz, hzA⟩ := (TARSKI.def4 A a).mp ha
      exact hA.1 z hzA a haz
    exact XBOOLE_0.def10.mpr ⟨hAsubU, hUsubA⟩

/-- Unlabeled `ORDINAL1` after `Th28` (`L799`). -/
theorem th29 {A : TarskiSet.{u}} (hA : isOrdinal A) :
    ¬ isLimitOrdinal A ↔ ∃ B, isOrdinal B ∧ A = succ B := by
  constructor
  · intro hn
    have hex : ∃ B, B ∈ A ∧ succ B ∉ A :=
      Classical.byContradiction fun hne =>
        hn ((th28 hA).mpr fun C hC =>
          Classical.not_not.mp (fun hns => hne ⟨C, hC, hns⟩))
    obtain ⟨B, hB, hns⟩ := hex
    have hBord : isOrdinal B := th13 hA hB
    refine ⟨B, hBord, ?_⟩
    apply Classical.byContradiction
    intro hne
    have hsub : succ B ⊆ A := (th21 hBord hA).mp hB
    exact hns (th11 (th17 hBord).1 hA ⟨hsub, fun heq => hne heq.symm⟩)
  · intro ⟨B, _hBord, heq⟩
    have hBin : B ∈ A :=
      Eq.subst (motive := fun s => B ∈ s) heq.symm (th6 B)
    have hns : succ B ∉ A := fun h =>
      not_mem_self (succ B)
        (Eq.subst (motive := fun s => succ B ∈ s) heq h)
    exact fun hlim => hns (((th28 hA).mp hlim) B hBin)

/-- `ORDINAL1:def 7` -/
def isTSequenceLike (IT : TarskiSet.{u}) : Prop :=
  isOrdinal (RELAT_1.dom IT)

theorem def7 (IT : TarskiSet.{u}) :
    isTSequenceLike IT ↔ isOrdinal (RELAT_1.dom IT) :=
  Iff.rfl

theorem empty_isTSequenceLike :
    isTSequenceLike (∅ : TarskiSet.{u}) :=
  Eq.subst (motive := isOrdinal) RELAT_1.th38.1.symm empty_isOrdinal

def isTSequence (IT : TarskiSet.{u}) : Prop :=
  FUNCT_1.isFunction IT ∧ isTSequenceLike IT

theorem empty_isTSequence : isTSequence (∅ : TarskiSet.{u}) :=
  ⟨FUNCT_1.empty_isFunction, empty_isTSequenceLike⟩

def isTSequenceOf (L Z : TarskiSet.{u}) : Prop :=
  isTSequence L ∧ RELAT_1.isXvalued L Z

/-- Unlabeled `ORDINAL1` (`L866`). -/
theorem th30 (Z : TarskiSet.{u}) :
    isTSequenceOf (∅ : TarskiSet.{u}) Z :=
  ⟨empty_isTSequence,
    Eq.subst (motive := fun s => s ⊆ Z) RELAT_1.th38.2.symm
      (XBOOLE_1.th2 (X := Z))⟩

/-- Unlabeled `ORDINAL1` (`L877`). -/
theorem th31 {F : TarskiSet.{u}} (hF : FUNCT_1.isFunction F)
    (hdom : isOrdinal (RELAT_1.dom F)) :
    isTSequenceOf F (RELAT_1.rng F) :=
  ⟨⟨hF, hdom⟩, fun _ hx => hx⟩

/-- Unlabeled `ORDINAL1` (`L886`). -/
theorem th32 {X Y L : TarskiSet.{u}} (hXY : X ⊆ Y)
    (hL : isTSequenceOf L X) : isTSequenceOf L Y :=
  ⟨hL.1, XBOOLE_1.th1 hL.2 hXY⟩

theorem restrict_isTSequenceLike {L A : TarskiSet.{u}}
    (hL : isTSequence L) (hA : isOrdinal A) :
    isTSequenceLike (RELAT_1.restrict L A) :=
  Or.elim (th16 hA hL.2)
    (fun hsub =>
      Eq.subst (motive := isOrdinal)
        (RELAT_1.th62 (R := L) (X := A) hsub).symm hA)
    (fun hdomA =>
      let hdomsub : RELAT_1.dom L ⊆ A := hA.1 (RELAT_1.dom L) hdomA
      let heq : RELAT_1.restrict L A = L := RELAT_1.th68 hL.1.1 hdomsub
      Eq.subst (motive := fun s => isOrdinal (RELAT_1.dom s)) heq.symm hL.2)

theorem restrict_isTSequence {L A : TarskiSet.{u}}
    (hL : isTSequence L) (hA : isOrdinal A) :
    isTSequence (RELAT_1.restrict L A) :=
  ⟨FUNCT_1.restrict_isFunction hL.1, restrict_isTSequenceLike hL hA⟩

/-- Unlabeled `ORDINAL1` (`L908`). -/
theorem th33 {L X A : TarskiSet.{u}} (hL : isTSequenceOf L X)
    (hA : isOrdinal A) :
    isTSequenceOf (RELAT_1.restrict L A) X :=
  ⟨restrict_isTSequence hL.1 hA,
    XBOOLE_1.th1 (RELAT_1.th70 (R := L) (X := A)) hL.2⟩

/-- `ORDINAL1:def 8` -/
def isCLinear (IT : TarskiSet.{u}) : Prop :=
  ∀ x y, x ∈ IT → y ∈ IT → XBOOLE_0.are_ccomparable x y

theorem def8 (IT : TarskiSet.{u}) :
    isCLinear IT ↔
      ∀ x y, x ∈ IT → y ∈ IT → XBOOLE_0.are_ccomparable x y :=
  Iff.rfl

/-- Unlabeled `ORDINAL1` (`L919`). -/
theorem th34 {X : TarskiSet.{u}}
    (hTS : ∀ a, a ∈ X → isTSequence a) (hlin : isCLinear X) :
    isTSequence (TARSKI.union X) := by
  have hRel : RELAT_1.isRelation (TARSKI.union X) := by
    intro a ha
    obtain ⟨x, hax, hxX⟩ := (TARSKI.def4 X a).mp ha
    exact (hTS x hxX).1.1 a hax
  have hFun : FUNCT_1.isFunctionLike (TARSKI.union X) := by
    intro a b c hab hac
    obtain ⟨y, hay, hyX⟩ := (TARSKI.def4 X (TARSKI.pair a c)).mp hac
    obtain ⟨x, hbx, hxX⟩ := (TARSKI.def4 X (TARSKI.pair a b)).mp hab
    have hxy := (XBOOLE_0.def9 x y).mp (hlin x y hxX hyX)
    exact Or.elim hxy
      (fun hsub => (hTS y hyX).1.2 a b c (hsub _ hbx) hay)
      (fun hsub => (hTS x hxX).1.2 a b c hbx (hsub _ hay))
  have hF : FUNCT_1.isFunction (TARSKI.union X) := ⟨hRel, hFun⟩
  let F := TARSKI.union X
  obtain ⟨G, hGfun, hG⟩ :=
    FUNCT_1.sch_GraphFunc X
      (fun a b => ∀ L, L = a → RELAT_1.dom L = b)
      (fun a b c hb hc => (hb a rfl).symm.trans (hc a rfl))
  have hGrng : ∀ a, a ∈ RELAT_1.rng G → isOrdinal a := by
    intro a ha
    obtain ⟨b, hb, heq⟩ := (FUNCT_1.def3 hGfun.2).mp ha
    have hp : TARSKI.pair b a ∈ G :=
      (FUNCT_1.th1 hGfun.2 (x := b) (y := a)).mpr ⟨hb, heq⟩
    have ⟨hbX, hP⟩ := (hG b a).mp hp
    exact Eq.subst (motive := isOrdinal) (hP b rfl)
      (hTS b hbX).2
  obtain ⟨A0, hA0, hA0sub⟩ := th24 hGrng
  have hexP : ∃ A, isOrdinal A ∧ ∀ B, B ∈ RELAT_1.rng G → B ⊆ A :=
    ⟨A0, hA0, fun B hB => hA0.1 B (hA0sub B hB)⟩
  obtain ⟨A, hAord, hAP, hAleast⟩ :=
    sch_OrdinalMin (fun A => ∀ B, B ∈ RELAT_1.rng G → B ⊆ A) hexP
  have hdom : RELAT_1.dom F = A := by
    apply eq_of_mem
    intro a
    constructor
    · intro ha
      obtain ⟨b, hp⟩ := (RELAT_1.dom_iff F a).mp ha
      obtain ⟨x, hpx, hxX⟩ := (TARSKI.def4 X (TARSKI.pair a b)).mp hp
      have hGmem : TARSKI.pair x (RELAT_1.dom x) ∈ G :=
        (hG x (RELAT_1.dom x)).mpr ⟨hxX, fun L hL =>
          Eq.subst (motive := fun s => RELAT_1.dom s = RELAT_1.dom x) hL.symm rfl⟩
      have hxdom : x ∈ RELAT_1.dom G :=
        ((FUNCT_1.th1 hGfun.2 (x := x) (y := RELAT_1.dom x)).mp hGmem).1
      have hdx : RELAT_1.dom x = FUNCT_1.apply G x :=
        ((FUNCT_1.th1 hGfun.2 (x := x) (y := RELAT_1.dom x)).mp hGmem).2
      have hdxrng : RELAT_1.dom x ∈ RELAT_1.rng G :=
        (FUNCT_1.def3 hGfun.2).mpr ⟨x, hxdom, hdx⟩
      have hdxA : RELAT_1.dom x ⊆ A := hAP (RELAT_1.dom x) hdxrng
      exact hdxA a ((RELAT_1.dom_iff x a).mpr ⟨b, hpx⟩)
    · intro ha
      have haord : isOrdinal a := th13 hAord ha
      have hexL : ∃ L, L ∈ X ∧ a ∈ RELAT_1.dom L :=
        Classical.byContradiction fun hne => by
          have hbound : ∀ B, B ∈ RELAT_1.rng G → B ⊆ a := by
            intro B hB
            obtain ⟨c, hc, heq⟩ := (FUNCT_1.def3 hGfun.2).mp hB
            have hp : TARSKI.pair c B ∈ G :=
              (FUNCT_1.th1 hGfun.2 (x := c) (y := B)).mpr ⟨hc, heq⟩
            have ⟨hcX, hP⟩ := (hG c B).mp hp
            have hBdom : RELAT_1.dom c = B := hP c rfl
            have hnin : a ∉ RELAT_1.dom c :=
              fun hin => hne ⟨c, hcX, hin⟩
            exact Or.elim (th16 (Eq.subst (motive := isOrdinal) hBdom
                (hTS c hcX).2) haord)
              (fun hsub => hsub)
              (fun hin => (hnin (Eq.subst (motive := fun s => a ∈ s)
                hBdom.symm hin)).elim)
          have hAle : A ⊆ a := hAleast a haord hbound
          have haA : a ⊆ A := hAord.1 a ha
          have heqAA : a = A :=
            (XBOOLE_0.def10 (X := a) (Y := A)).mpr ⟨haA, hAle⟩
          exact not_mem_self a
            (Eq.subst (motive := fun s => a ∈ s) heqAA.symm ha)
      obtain ⟨L, hLX, haL⟩ := hexL
      obtain ⟨b, hpL⟩ := (RELAT_1.dom_iff L a).mp haL
      have hLF : L ⊆ F := ZFMISC_1.th74 hLX
      exact (RELAT_1.dom_iff F a).mpr ⟨b, hLF _ hpL⟩
  exact ⟨hF, Eq.subst (motive := isOrdinal) hdom.symm hAord⟩

/-- `ORDINAL1:sch TSUniq` -/
theorem sch_TSUniq (H : TarskiSet.{u} → TarskiSet.{u})
    {A L1 L2 : TarskiSet.{u}} (hA : isOrdinal A)
    (hL1 : isTSequence L1) (hL2 : isTSequence L2)
    (hd1 : RELAT_1.dom L1 = A) (hd2 : RELAT_1.dom L2 = A)
    (hH1 : ∀ B L, B ∈ A → L = RELAT_1.restrict L1 B →
      FUNCT_1.apply L1 B = H L)
    (hH2 : ∀ B L, B ∈ A → L = RELAT_1.restrict L2 B →
      FUNCT_1.apply L2 B = H L) :
    L1 = L2 := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨X, hX⟩ :=
    XBOOLE_0.sch_separation A
      (fun x => FUNCT_1.apply L1 x ≠ FUNCT_1.apply L2 x)
  have hXsub : X ⊆ A := fun x hx => ((hX x).mp hx).1
  have hex : ∃ a, a ∈ A ∧ FUNCT_1.apply L1 a ≠ FUNCT_1.apply L2 a :=
    Classical.byContradiction fun hnex =>
      hne (FUNCT_1.th2 hL1.1 hL2.1 (hd1.trans hd2.symm) fun x hx =>
        Classical.not_not.mp (fun hneq =>
          hnex ⟨x, Eq.subst (motive := fun s => x ∈ s) hd1 hx, hneq⟩))
  have hXne : X ≠ (∅ : TarskiSet.{u}) := fun hempty =>
    let ⟨a, ha, hneq⟩ := hex
    (XBOOLE_0.empty_iff a).mp
      (Eq.subst (motive := fun s => a ∈ s) hempty ((hX a).mpr ⟨ha, hneq⟩))
  obtain ⟨B, hB, hleast⟩ := th20 hA hXsub hXne
  have hBA : B ∈ A := ((hX B).mp hB).1
  have hBsub : B ⊆ A := hA.1 B hBA
  have hdL1B : RELAT_1.dom (RELAT_1.restrict L1 B) = B :=
    RELAT_1.th62 (R := L1) (X := B)
      (Eq.subst (motive := fun s => B ⊆ s) hd1.symm hBsub)
  have hdL2B : RELAT_1.dom (RELAT_1.restrict L2 B) = B :=
    RELAT_1.th62 (R := L2) (X := B)
      (Eq.subst (motive := fun s => B ⊆ s) hd2.symm hBsub)
  have heqR : RELAT_1.restrict L1 B = RELAT_1.restrict L2 B :=
    FUNCT_1.th2 (FUNCT_1.restrict_isFunction hL1.1)
      (FUNCT_1.restrict_isFunction hL2.1) (hdL1B.trans hdL2B.symm)
      (fun C hC => by
        have hCB : C ∈ B :=
          Eq.subst (motive := fun s => C ∈ s) hdL1B hC
        have hCA : C ∈ A := hBsub C hCB
        have hCeq : FUNCT_1.apply L1 C = FUNCT_1.apply L2 C :=
          Classical.not_not.mp (fun hneq =>
            th5 hCB (hleast C ((hX C).mpr ⟨hCA, hneq⟩)))
        have h1 := FUNCT_1.th47 hL1.1.2 hC
        have h2 := FUNCT_1.th47 hL2.1.2
          (Eq.subst (motive := fun s => C ∈ s) hdL2B.symm hCB)
        exact h1.trans (hCeq.trans h2.symm))
  have hneq : FUNCT_1.apply L1 B ≠ FUNCT_1.apply L2 B :=
    ((hX B).mp hB).2
  have h1 := hH1 B (RELAT_1.restrict L1 B) hBA rfl
  have h2 := hH2 B (RELAT_1.restrict L2 B) hBA rfl
  have hH : H (RELAT_1.restrict L1 B) = H (RELAT_1.restrict L2 B) :=
    Eq.subst (motive := fun s => H (RELAT_1.restrict L1 B) = H s) heqR rfl
  exact hneq (h1.trans (hH.trans h2.symm))

/-- `ORDINAL1:sch TSExist` -/
theorem sch_TSExist (H : TarskiSet.{u} → TarskiSet.{u})
    {A : TarskiSet.{u}} (hA : isOrdinal A) :
    ∃ L, isTSequence L ∧ RELAT_1.dom L = A ∧
      ∀ B L1, B ∈ A → L1 = RELAT_1.restrict L B →
        FUNCT_1.apply L B = H L1 := by
  let S : TarskiSet.{u} → Prop := fun B =>
    ∃ L, isTSequence L ∧ RELAT_1.dom L = B ∧
      ∀ D, D ∈ B → FUNCT_1.apply L D = H (RELAT_1.restrict L D)
  have hind : ∀ B, isOrdinal B → (∀ C, C ∈ B → S C) → S B := by
    intro B hB hIH
    let P : TarskiSet.{u} → TarskiSet.{u} → Prop := fun a b =>
      isOrdinal a ∧ isTSequence b ∧ RELAT_1.dom b = a ∧
        ∀ D, D ∈ a → FUNCT_1.apply b D = H (RELAT_1.restrict b D)
    have hPfun : ∀ a b c, P a b → P a c → b = c :=
      fun a b c hb hc =>
        sch_TSUniq H hb.1 hb.2.1 hc.2.1 hb.2.2.1 hc.2.2.1
          (fun D L hD hL =>
            Eq.subst (motive := fun s => FUNCT_1.apply b D = H s) hL.symm
              (hb.2.2.2 D hD))
          (fun D L hD hL =>
            Eq.subst (motive := fun s => FUNCT_1.apply c D = H s) hL.symm
              (hc.2.2.2 D hD))
    obtain ⟨G, hGfun, hG⟩ := FUNCT_1.sch_GraphFunc B P hPfun
    have hGdom : RELAT_1.dom G = B := by
      apply eq_of_mem
      intro a
      constructor
      · intro ha
        obtain ⟨b, hp⟩ := (RELAT_1.dom_iff G a).mp ha
        exact ((hG a b).mp hp).1
      · intro ha
        obtain ⟨L, hLTS, hLdom, hLH⟩ := hIH a ha
        have hP : P a L :=
          ⟨th13 hB ha, hLTS, hLdom, hLH⟩
        exact (RELAT_1.dom_iff G a).mpr
          ⟨L, (hG a L).mpr ⟨ha, hP⟩⟩
    have hexR : ∀ a, a ∈ B →
        ∃ b, ∃ L, L = FUNCT_1.apply G a ∧ b = H L :=
      fun a ha =>
        let ⟨c, hp⟩ := (RELAT_1.dom_iff G a).mp
          (Eq.subst (motive := fun s => a ∈ s) hGdom.symm ha)
        let hPc := ((hG a c).mp hp).2
        ⟨H c, c, ((FUNCT_1.th1 hGfun.2 (x := a) (y := c)).mp hp).2, rfl⟩
    have hRuniq : ∀ a b c, a ∈ B →
        (∃ L, L = FUNCT_1.apply G a ∧ b = H L) →
        (∃ L, L = FUNCT_1.apply G a ∧ c = H L) → b = c :=
      fun _ _ _ _ hb hc =>
        let ⟨L1, hL1, hb'⟩ := hb
        let ⟨L2, hL2, hc'⟩ := hc
        hb'.trans
          ((Eq.subst (motive := fun s => H L1 = H s) (hL1.trans hL2.symm)
            rfl).trans hc'.symm)
    obtain ⟨F, hFfun, hFdom, hFR⟩ :=
      FUNCT_1.sch_FuncEx B
        (fun a b => ∃ L, L = FUNCT_1.apply G a ∧ b = H L)
        hRuniq hexR
    have hLTS : isTSequence F :=
      ⟨hFfun, Eq.subst (motive := isOrdinal) hFdom.symm hB⟩
    refine ⟨F, hLTS, hFdom, ?_⟩
    intro D hD
    obtain ⟨K, hKeq, hFH⟩ := hFR D hD
    have hKTS : isTSequence K := by
      have hp : TARSKI.pair D K ∈ G :=
        (FUNCT_1.th1 hGfun.2 (x := D) (y := K)).mpr
          ⟨Eq.subst (motive := fun s => D ∈ s) hGdom.symm hD, hKeq⟩
      exact ((hG D K).mp hp).2.2.1
    have hKdom : RELAT_1.dom K = D := by
      have hp : TARSKI.pair D K ∈ G :=
        (FUNCT_1.th1 hGfun.2 (x := D) (y := K)).mpr
          ⟨Eq.subst (motive := fun s => D ∈ s) hGdom.symm hD, hKeq⟩
      exact ((hG D K).mp hp).2.2.2.1
    have hKrec : ∀ C, C ∈ D →
        FUNCT_1.apply K C = H (RELAT_1.restrict K C) := by
      have hp : TARSKI.pair D K ∈ G :=
        (FUNCT_1.th1 hGfun.2 (x := D) (y := K)).mpr
          ⟨Eq.subst (motive := fun s => D ∈ s) hGdom.symm hD, hKeq⟩
      exact ((hG D K).mp hp).2.2.2.2
    have hGrest : ∀ C, C ∈ D → FUNCT_1.apply G C = RELAT_1.restrict K C := by
      intro C hC
      have hCB : C ∈ B := th10 hB.1 hC hD
      have hCsubD : C ⊆ D := (th13 hB hD).1 C hC
      have hP : P C (RELAT_1.restrict K C) :=
        ⟨th13 hB hCB, restrict_isTSequence hKTS (th13 hB hCB),
          RELAT_1.th62 (R := K) (X := C)
            (Eq.subst (motive := fun s => C ⊆ s) hKdom.symm hCsubD),
          fun E hE => by
            have hEA : E ∈ C := hE
            have hED : E ∈ D := hCsubD E hEA
            have hEsub : E ⊆ C := (th13 (th13 hB hD) hC).1 E hEA
            have hrest : RELAT_1.restrict K E =
                RELAT_1.restrict (RELAT_1.restrict K C) E :=
              (FUNCT_1.th51 (f := K) (X := E) (Y := C) hEsub).2.symm
            have hdKC : RELAT_1.dom (RELAT_1.restrict K C) = C :=
              RELAT_1.th62 (R := K) (X := C)
                (Eq.subst (motive := fun s => C ⊆ s) hKdom.symm hCsubD)
            have happ : FUNCT_1.apply (RELAT_1.restrict K C) E =
                FUNCT_1.apply K E :=
              FUNCT_1.th47 hKTS.1.2
                (Eq.subst (motive := fun s => E ∈ s) hdKC.symm hEA)
            exact happ.trans ((hKrec E hED).trans
              (Eq.subst (motive := fun s => H (RELAT_1.restrict K E) = H s)
                hrest rfl))⟩
      have hp : TARSKI.pair C (RELAT_1.restrict K C) ∈ G :=
        (hG C (RELAT_1.restrict K C)).mpr ⟨hCB, hP⟩
      exact ((FUNCT_1.th1 hGfun.2 (x := C)
        (y := RELAT_1.restrict K C)).mp hp).2.symm
    have hdLD : RELAT_1.dom (RELAT_1.restrict F D) = D :=
      RELAT_1.th62 (R := F) (X := D)
        (Eq.subst (motive := fun s => D ⊆ s) hFdom.symm (hB.1 D hD))
    have heqKD : RELAT_1.restrict F D = K :=
      FUNCT_1.th2 (FUNCT_1.restrict_isFunction hFfun) hKTS.1
        (hdLD.trans hKdom.symm) fun a ha => by
          have haD : a ∈ D :=
            Eq.subst (motive := fun s => a ∈ s) hdLD ha
          have haB : a ∈ B := th10 hB.1 haD hD
          obtain ⟨J, hJeq, hFapp⟩ := hFR a haB
          have hGrest' : FUNCT_1.apply G a = RELAT_1.restrict K a :=
            hGrest a haD
          have happF : FUNCT_1.apply (RELAT_1.restrict F D) a =
              FUNCT_1.apply F a := FUNCT_1.th47 hFfun.2 ha
          have hKapp : FUNCT_1.apply K a = H (RELAT_1.restrict K a) :=
            hKrec a haD
          have hJrest : J = RELAT_1.restrict K a := hJeq.trans hGrest'
          have hHJ : H J = FUNCT_1.apply K a :=
            Eq.subst (motive := fun s => H s = FUNCT_1.apply K a)
              hJrest.symm hKapp.symm
          exact happF.trans (hFapp.trans hHJ)
    exact hFH.trans
      (Eq.subst (motive := fun s => H K = H s) heqKD.symm rfl)
  obtain ⟨L, hLTS, hLdom, hLrec⟩ :=
    sch_TransfiniteInd S hind A hA
  exact ⟨L, hLTS, hLdom, fun B L1 hB hL1 =>
    Eq.subst (motive := fun s => FUNCT_1.apply L B = H s) hL1.symm
      (hLrec B hB)⟩

/-- `ORDINAL1:sch FuncTS` -/
theorem sch_FuncTS (F H : TarskiSet.{u} → TarskiSet.{u})
    {L0 : TarskiSet.{u}} (hL0 : isTSequence L0)
    (h1 : ∀ A a, a = F A ↔ ∃ L, isTSequence L ∧ a = H L ∧
      RELAT_1.dom L = A ∧
      ∀ B, B ∈ A → FUNCT_1.apply L B = H (RELAT_1.restrict L B))
    (h2 : ∀ A, A ∈ RELAT_1.dom L0 → FUNCT_1.apply L0 A = F A) :
    ∀ B, B ∈ RELAT_1.dom L0 →
      FUNCT_1.apply L0 B = H (RELAT_1.restrict L0 B) := by
  obtain ⟨L, hLTS, hLdom, hLrec⟩ := sch_TSExist H hL0.2
  have hL0eq : L0 = L :=
    FUNCT_1.th2 hL0.1 hLTS.1 hLdom.symm fun b hb => by
      have hBord : isOrdinal b := th13 hL0.2 hb
      have hsub : b ⊆ RELAT_1.dom L :=
        Eq.subst (motive := fun s => b ⊆ s) hLdom.symm (hL0.2.1 b hb)
      have hK : isTSequence (RELAT_1.restrict L b) :=
        restrict_isTSequence hLTS hBord
      have hKdom : RELAT_1.dom (RELAT_1.restrict L b) = b :=
        RELAT_1.th62 (R := L) (X := b) hsub
      have hKrec : ∀ C, C ∈ b →
          FUNCT_1.apply (RELAT_1.restrict L b) C =
            H (RELAT_1.restrict (RELAT_1.restrict L b) C) := by
        intro C hC
        have hCdom : C ∈ RELAT_1.dom (RELAT_1.restrict L b) :=
          Eq.subst (motive := fun s => C ∈ s) hKdom.symm hC
        have hCL : C ∈ RELAT_1.dom L0 :=
          Eq.subst (motive := fun s => C ∈ s) hLdom (hsub C hC)
        have happ : FUNCT_1.apply (RELAT_1.restrict L b) C =
            FUNCT_1.apply L C := FUNCT_1.th47 hLTS.1.2 hCdom
        have hCsub : C ⊆ b := hBord.1 C hC
        have hrest : RELAT_1.restrict L C =
            RELAT_1.restrict (RELAT_1.restrict L b) C :=
          (FUNCT_1.th51 (f := L) (X := C) (Y := b) hCsub).2.symm
        exact happ.trans ((hLrec C (RELAT_1.restrict L C) hCL rfl).trans
          (Eq.subst (motive := fun s => H (RELAT_1.restrict L C) = H s)
            hrest rfl))
      have hFeq : H (RELAT_1.restrict L b) = F b :=
        (h1 b (H (RELAT_1.restrict L b))).mpr
          ⟨RELAT_1.restrict L b, hK, rfl, hKdom, hKrec⟩
      have happL : FUNCT_1.apply L b = H (RELAT_1.restrict L b) :=
        hLrec b (RELAT_1.restrict L b) hb rfl
      exact (h2 b hb).trans (hFeq.symm.trans happL.symm)
  intro B hB
  have hBeq : FUNCT_1.apply L0 B = FUNCT_1.apply L B :=
    Eq.subst (motive := fun s => FUNCT_1.apply L0 B = FUNCT_1.apply s B)
      hL0eq rfl
  have hH : FUNCT_1.apply L B = H (RELAT_1.restrict L B) :=
    hLrec B (RELAT_1.restrict L B) hB rfl
  have hR : RELAT_1.restrict L0 B = RELAT_1.restrict L B :=
    Eq.subst (motive := fun s => RELAT_1.restrict L0 B =
      RELAT_1.restrict s B) hL0eq rfl
  exact hBeq.trans (hH.trans
    (Eq.subst (motive := fun s => H (RELAT_1.restrict L B) = H s)
      hR.symm rfl))

/-- Unlabeled `ORDINAL1` (`L1264`). -/
theorem th35 {A B : TarskiSet.{u}} (hA : isOrdinal A) (hB : isOrdinal B) :
    A ⊂ B ∨ A = B ∨ B ⊂ A :=
  Or.elim (th15 hA hB)
    (fun hAB => Or.elim (Classical.em (A = B))
      (fun heq => Or.inr (Or.inl heq))
      (fun hne => Or.inl ⟨hAB, hne⟩))
    (fun hBA => Or.elim (Classical.em (A = B))
      (fun heq => Or.inr (Or.inl heq))
      (fun hne => Or.inr (Or.inr ⟨hBA, fun heq => hne heq.symm⟩)))

/-- `ORDINAL1:def 9` -/
noncomputable def On (X : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (XBOOLE_0.sch_separation X isOrdinal)

theorem def9 (X x : TarskiSet.{u}) :
    x ∈ On X ↔ x ∈ X ∧ isOrdinal x :=
  Classical.choose_spec (XBOOLE_0.sch_separation X isOrdinal) x

/-- Limit ordinals of `X`. Unlabeled `func` after `Def9` (`def 10`). -/
noncomputable def Lim (X : TarskiSet.{u}) : TarskiSet.{u} :=
  Classical.choose (XBOOLE_0.sch_separation X isLimitOrdinal)

theorem def10 (X x : TarskiSet.{u}) :
    x ∈ Lim X ↔ x ∈ X ∧ isLimitOrdinal x :=
  Classical.choose_spec (XBOOLE_0.sch_separation X isLimitOrdinal) x

noncomputable def succIterate : Nat → TarskiSet.{u} → TarskiSet.{u}
  | 0, X => succ X
  | n + 1, X => succ (succIterate n X)

theorem succIterate_ordinal (n : Nat) {X : TarskiSet.{u}}
    (hX : isOrdinal X) : isOrdinal (succIterate n X) := by
  induction n with
  | zero => exact th17 hX
  | succ _n ih => exact th17 ih

noncomputable def omegaChain (X : TarskiSet.{u}) : TarskiSet.{u} :=
  mk (PreSet.mk (ULift.{u} Nat) fun ⟨n⟩ => out (succIterate n X))

theorem mem_omegaChain (X y : TarskiSet.{u}) :
    y ∈ omegaChain X ↔ ∃ n : Nat, y = succIterate n X := by
  constructor
  · intro hy
    refine inductionOn (β := fun y => y ∈ omegaChain X →
        ∃ n, y = succIterate n X) y (fun p hp => ?_) hy
    change mk p ∈
        mk (PreSet.mk (ULift.{u} Nat) fun ⟨n⟩ => out (succIterate n X)) at hp
    rw [mem_mk_iff, PreSet.mem_mk] at hp
    obtain ⟨⟨n⟩, heq⟩ := hp
    exact ⟨n, (sound heq).trans (out_eq _)⟩
  · intro ⟨n, heq⟩
    have hmem : mk (out (succIterate n X)) ∈ omegaChain X := by
      change mk (out (succIterate n X)) ∈
        mk (PreSet.mk (ULift.{u} Nat) fun ⟨m⟩ => out (succIterate m X))
      rw [mem_mk_iff, PreSet.mem_mk]
      exact ⟨⟨n⟩, PreSet.equiv_refl _⟩
    exact Eq.subst (motive := fun s => s ∈ omegaChain X)
      ((out_eq (succIterate n X)).trans heq.symm) hmem

/-- `ORDINAL1:36` (`Th36`). `D` is reserved as an ordinal. -/
theorem th36 {D : TarskiSet.{u}} (hD : isOrdinal D) :
    ∃ A, isOrdinal A ∧ D ∈ A ∧ isLimitOrdinal A := by
  let W := omegaChain D
  have hWord : ∀ a, a ∈ W → isOrdinal a := by
    intro a ha
    obtain ⟨n, heq⟩ := (mem_omegaChain D a).mp ha
    exact Eq.subst (motive := isOrdinal) heq.symm
      (succIterate_ordinal n hD)
  let A := TARSKI.union W
  have hAord : isOrdinal A := th23 hWord
  have hDin : D ∈ A :=
    (TARSKI.def4 W D).mpr ⟨succ D, th6 D,
      (mem_omegaChain D (succ D)).mpr ⟨0, rfl⟩⟩
  have hAsubU : A ⊆ TARSKI.union A := by
    intro a ha
    obtain ⟨z, haz, hzW⟩ := (TARSKI.def4 W a).mp ha
    obtain ⟨n, hzn⟩ := (mem_omegaChain D z).mp hzW
    have hzsucc : z ∈ succIterate (n + 1) D :=
      Eq.subst (motive := fun s => s ∈ succ (succIterate n D)) hzn.symm
        (th6 (succIterate n D))
    have hsn : succIterate (n + 1) D ∈ W :=
      (mem_omegaChain D (succIterate (n + 1) D)).mpr ⟨n + 1, rfl⟩
    have hzA : z ∈ A := (TARSKI.def4 W z).mpr ⟨succIterate (n + 1) D, hzsucc, hsn⟩
    exact (TARSKI.def4 A a).mpr ⟨z, haz, hzA⟩
  have hUsubA : TARSKI.union A ⊆ A := by
    intro a ha
    obtain ⟨z, haz, hzA⟩ := (TARSKI.def4 A a).mp ha
    obtain ⟨w, hzw, hwW⟩ := (TARSKI.def4 W z).mp hzA
    exact (TARSKI.def4 W a).mpr ⟨w, (hWord w hwW).1 z hzw a haz, hwW⟩
  have hlim : isLimitOrdinal A :=
    (XBOOLE_0.def10 (X := A) (Y := TARSKI.union A)).mpr ⟨hAsubU, hUsubA⟩
  exact ⟨A, hAord, hDin, hlim⟩

private theorem omega_hex :
    ∃ A, isOrdinal A ∧
      ((∅ : TarskiSet.{u}) ∈ A ∧ isLimitOrdinal A) :=
  let ⟨A, hA, h0, hlim⟩ := th36 empty_isOrdinal
  ⟨A, hA, h0, hlim⟩

/-- `ORDINAL1:def 11` -/
noncomputable def omega : TarskiSet.{u} :=
  Classical.choose (sch_OrdinalMin
    (fun A => (∅ : TarskiSet.{u}) ∈ A ∧ isLimitOrdinal A) omega_hex)

theorem def11 :
    isOrdinal (omega : TarskiSet.{u}) ∧
      (∅ : TarskiSet.{u}) ∈ omega ∧
      isLimitOrdinal (omega : TarskiSet.{u}) ∧
      ∀ A, isOrdinal A → (∅ : TarskiSet.{u}) ∈ A → isLimitOrdinal A →
        omega ⊆ A :=
  let h := Classical.choose_spec (sch_OrdinalMin
    (fun A => (∅ : TarskiSet.{u}) ∈ A ∧ isLimitOrdinal A) omega_hex)
  ⟨h.1, h.2.1.1, h.2.1.2, fun A hA h0 hlim => h.2.2 A hA ⟨h0, hlim⟩⟩

/-- `ORDINAL1:def 12` -/
def isNatural (A : TarskiSet.{u}) : Prop := A ∈ omega

theorem def12 (A : TarskiSet.{u}) : isNatural A ↔ A ∈ omega :=
  Iff.rfl

theorem empty_isNatural : isNatural (∅ : TarskiSet.{u}) :=
  def11.2.1

theorem natural_isOrdinal {n : TarskiSet.{u}} (hn : isNatural n) :
    isOrdinal n :=
  th13 def11.1 hn

theorem succ_isNatural {a : TarskiSet.{u}} (ha : isNatural a) :
    isNatural (succ a) :=
  ((th28 def11.1).mp def11.2.2.1) a ha

/-- `ORDINAL1:sch ALFA` -/
theorem sch_ALFA (D : TarskiSet.{u}) (P : TarskiSet.{u} → TarskiSet.{u} → Prop)
    (_hne : D ≠ (∅ : TarskiSet.{u}))
    (hex : ∀ d, d ∈ D → ∃ A, isOrdinal A ∧ P d A) :
    ∃ F, FUNCT_1.isFunction F ∧ RELAT_1.dom F = D ∧
      ∀ d, d ∈ D → ∃ A, isOrdinal A ∧ A = FUNCT_1.apply F d ∧ P d A ∧
        ∀ B, isOrdinal B → P d B → A ⊆ B := by
  have hQex : ∀ x, x ∈ D →
      ∃ y, ∃ A, isOrdinal A ∧ y = A ∧ P x A ∧
        ∀ B, isOrdinal B → P x B → A ⊆ B := by
    intro x hx
    obtain ⟨A0, hA0, hP0⟩ := hex x hx
    obtain ⟨A, hA, hPA, hleast⟩ :=
      sch_OrdinalMin (fun A => P x A) ⟨A0, hA0, hP0⟩
    exact ⟨A, A, hA, rfl, hPA, hleast⟩
  have hQfun : ∀ x y1 y2, x ∈ D →
      (∃ A, isOrdinal A ∧ y1 = A ∧ P x A ∧
        ∀ B, isOrdinal B → P x B → A ⊆ B) →
      (∃ A, isOrdinal A ∧ y2 = A ∧ P x A ∧
        ∀ B, isOrdinal B → P x B → A ⊆ B) → y1 = y2 :=
    fun _ y1 y2 _ h1 h2 =>
      let ⟨A1, hA1, hy1, hP1, hl1⟩ := h1
      let ⟨A2, hA2, hy2, hP2, hl2⟩ := h2
      hy1.trans
        (((XBOOLE_0.def10 (X := A1) (Y := A2)).mpr
          ⟨hl1 A2 hA2 hP2, hl2 A1 hA1 hP1⟩).trans hy2.symm)
  obtain ⟨F, hF, hdom, happ⟩ :=
    FUNCT_1.sch_FuncEx D
      (fun x y => ∃ A, isOrdinal A ∧ y = A ∧ P x A ∧
        ∀ B, isOrdinal B → P x B → A ⊆ B)
      hQfun hQex
  refine ⟨F, hF, hdom, ?_⟩
  intro d hd
  obtain ⟨A, hA, hy, hP, hl⟩ := happ d hd
  exact ⟨A, hA, hy.symm, hP, hl⟩

/-- Unlabeled `ORDINAL1` (`L1494`). -/
theorem th37 (X : TarskiSet.{u}) :
    succ X \ TARSKI.singleton X = X := by
  apply eq_of_mem
  intro x
  constructor
  · intro hx
    have ⟨hs, hns⟩ := (XBOOLE_0.def5 (succ X) (TARSKI.singleton X) x).mp hx
    rcases (th8 x X).mp hs with hxX | heq
    · exact hxX
    · exact (hns ((singleton_iff X x).mpr heq)).elim
  · intro hx
    have hne : x ≠ X := fun heq =>
      not_mem_self X (Eq.subst (motive := fun s => s ∈ X) heq hx)
    exact (XBOOLE_0.def5 (succ X) (TARSKI.singleton X) x).mpr
      ⟨(th8 x X).mpr (Or.inl hx),
        fun hs => hne ((singleton_iff X x).mp hs)⟩

theorem empty_isCLinear : isCLinear (∅ : TarskiSet.{u}) :=
  fun x _ hx => ((XBOOLE_0.empty_iff x).mp hx).elim

theorem subset_isCLinear {X Y : TarskiSet.{u}} (hX : isCLinear X)
    (hY : Y ⊆ X) : isCLinear Y :=
  fun x y hx hy => hX x y (hY x hx) (hY y hy)

end ORDINAL1
