/-
Copyright (c) 2000-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under the GNU General Public License version 3.0 or later,
or the Creative Commons Attribution-ShareAlike License version 3.0 or later.
See the notices in `yellow17.miz`.
Authors: Bartłomiej Skorulski (Mizar), Lars Warren Ericson (Lean 4).
-/
import Yellow17

/-!
# Solutions to the Challenge

Importing `Yellow17` supplies every compared declaration from
`Challenge.lean`, with the same module-qualified names `Yellow17.*` and
no `sorry`. The proofs are the idiomatic Lean 4 translation of Mizar
article `YELLOW_17` (Bartłomiej Skorulski, *The Tichonov Theorem*).

The headline Tychonoff theorems audit to
`{propext, Classical.choice, Quot.sound}`. Those axioms are listed in
`comparator.json`.
-/
