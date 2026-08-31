/-
Copyright (c) 1990-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache-2.0.
See `doc/COPYING.*` and the notices in `vendor/mml/tarski.miz`.
Authors: Andrzej Trybulec (Mizar), Lars Warren Ericson (Lean 4).
-/
import MizarCCL.SETWISEO

/-!
# Solutions to the Challenge

Palomar **Solution** module: proofs for every declaration listed in
`comparator.json`.

Like `Challenge.lean`, this is an interim TARSKI scaffold. Registry
submission is deferred until the full 368-article translation is
complete and the 58 seed capstones have been selected.

Unlike `Challenge.lean`, this file **may** import project libraries.
It re-exports `MizarCCL.TARSKI`, which supplies the same
module-qualified names (`TARSKI.*`) with no `sorry`.

The compared `TARSKI.ulift_eq_iff` and `TARSKI.ulift_mem_iff` laws
make the cross-universe lift auditable: it reflects equality and
preserves and reflects membership. Thus `TARSKI.th3` cannot be read
using a constant or otherwise unspecified map. The structural
implementation and its quotient well-definedness proof are
`TARSKI.uliftPre`, `TARSKI.uliftPre_equiv`, and `TARSKI.ulift`.

Compared theorems audit to `{propext, Classical.choice, Quot.sound}`
(see `comparator.json` → `permitted_axioms`). Choice appears only in regularity
(`th2`) and Fraenkel (`sch1`).
-/

namespace PalomarExperiment

/-- `SETWISEO:59`: finite-union homomorphisms commute with finite union. -/
theorem setwiseo_th59 {X Y Z B f g : TarskiSet.{u}}
    (hX : X ≠ (∅ : TarskiSet.{u}))
    (hB : B ∈ FINSUB_1.Fin X)
    (hf : FUNCT_2.isFunctionOf f X (FINSUB_1.Fin Y))
    (hg : FUNCT_2.isFunctionOf g (FINSUB_1.Fin Y) (FINSUB_1.Fin Z))
    (hcomp : FUNCT_2.isFunctionOf (RELAT_1.comp f g) X (FINSUB_1.Fin Z))
    (h0 : FUNCT_1.apply g (∅ : TarskiSet.{u}) = (∅ : TarskiSet.{u}))
    (hhom : ∀ x y, x ∈ FINSUB_1.Fin Y → y ∈ FINSUB_1.Fin Y →
      FUNCT_1.apply g (x ∪ y) =
        FUNCT_1.apply g x ∪ FUNCT_1.apply g y) :
    FUNCT_1.apply g (SETWISEO.FinUnion hX hB hf) =
      SETWISEO.FinUnion hX hB hcomp := by
  exact SETWISEO.th59 hX hB hf hg h0 hhom

end PalomarExperiment
