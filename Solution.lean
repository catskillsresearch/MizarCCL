/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/tarski.miz`.
Authors: Andrzej Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/
import MizarCCL.TARSKI

/-!
# Solutions to the Challenge

Palomar **Solution** module: proofs for every declaration listed in
`comparator.json`.

Unlike `Challenge.lean`, this file **may** import project libraries.
It re-exports `MizarCCL.TARSKI`, which supplies the same
module-qualified names (`TARSKI.*`) with no `sorry`.

Compared theorems audit to `{propext, Classical.choice, Quot.sound}`
(see `comparator.json` → `permitted_axioms`). Choice appears only in regularity
(`th2`) and Fraenkel (`sch1`).
-/
