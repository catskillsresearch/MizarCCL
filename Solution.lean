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

Importing `MizarCCL.TARSKI` supplies every compared declaration from
`Challenge.lean`, with the same module-qualified names `TARSKI.*` and
no `sorry`. The proofs are the Lean 4 translation of Mizar article
`TARSKI` (Andrzej Trybulec, *Tarski Grothendieck Set Theory*).

Compared theorems audit to `{propext, Classical.choice, Quot.sound}`.
Those axioms are listed in `comparator.json`. Choice appears only in
regularity (`th2`) and Fraenkel (`sch1`).
-/
