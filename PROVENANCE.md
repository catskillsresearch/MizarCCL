# Provenance

## Mizar source

The Mizar Mathematical Library is
[MizarSystem/MML](https://github.com/MizarSystem/MML.git)
at revision `047822c4d814630b28eec8ca6b455e9eb912d5ff` (commit date
2012-03-17; Mizar 7.13.01 / MML 4.181.1147). Palomar cannot preserve
git submodules, so this repository vendors a used-module slice as
ordinary files under [`vendor/mml/`](vendor/mml):

- [`vendor/mml/hidden.miz`](vendor/mml/hidden.miz)
- the 368 articles listed in `mizarccl_translation_order.yaml`

Pin: [`vendor/MML_PIN`](vendor/MML_PIN). See `vendor/README.md`.

The first translated article is `TARSKI`
([`vendor/mml/tarski.miz`](vendor/mml/tarski.miz);
[upstream](https://github.com/MizarSystem/MML/blob/047822c4d814630b28eec8ca6b455e9eb912d5ff/mml/tarski.miz)).
Andrzej Trybulec, *Tarski Grothendieck Set Theory*, received
1 January 1989. Copyright Association of Mizar Users. License:
GPL-3.0-or-later or CC-BY-SA-3.0 (`doc/COPYING.*`).

This repository does not run the Mizar checker. The 1–1 Lean queue
is `mizarccl_translation_order.yaml`. A full local MML clone may be
placed at `vendor/MML` (gitignored) to regenerate the queue.

## Lean translation

`MizarCCL/HIDDEN.lean` defines `TarskiSet` (Aczel quotient).
`MizarCCL/TARSKI.lean` is the Lean translation of `tarski.miz`.
`Challenge.lean` / `Solution.lean` are the Palomar surface for that
article. No Mathlib.
