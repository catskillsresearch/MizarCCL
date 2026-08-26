# Provenance

## Mizar source

The Mizar Mathematical Library is vendored as the git submodule
[`vendor/MML`](vendor/MML) of
[MizarSystem/MML](https://github.com/MizarSystem/MML.git)
at revision `047822c4d814630b28eec8ca6b455e9eb912d5ff` (commit date
2012-03-17; Mizar 7.13.01 / MML 4.181.1147). See `vendor/README.md`.

The first translated article is `TARSKI`:
[`vendor/MML/mml/tarski.miz`](vendor/MML/mml/tarski.miz)
([upstream](https://github.com/MizarSystem/MML/blob/047822c4d814630b28eec8ca6b455e9eb912d5ff/mml/tarski.miz)).
Andrzej Trybulec, *Tarski Grothendieck Set Theory*, received
1 January 1989. Copyright Association of Mizar Users. License:
GPL-3.0-or-later or CC-BY-SA-3.0 (`doc/COPYING.*`).

This repository does not run the Mizar checker. The 1–1 Lean queue
is `mizarccl_translation_order.yaml`.

## Lean translation

`MizarCCL/HIDDEN.lean` defines `TarskiSet` (Aczel quotient).
`MizarCCL/TARSKI.lean` is the 1–1 Lean translation of `tarski.miz`.
`Challenge.lean` / `Solution.lean` are the Palomar surface for that
article. No Mathlib.
