# Provenance

## Mizar source

The Mizar Mathematical Library is vendored as the git submodule
[`vendor/MML`](vendor/MML) of
[MizarSystem/MML](https://github.com/MizarSystem/MML.git)
at revision `047822c4d814630b28eec8ca6b455e9eb912d5ff` (commit date
2012-03-17; Mizar 7.13.01 / MML 4.181.1147). See `vendor/README.md`.

`YELLOW_17` is
[`vendor/MML/mml/yellow17.miz`](vendor/MML/mml/yellow17.miz)
([upstream](https://github.com/MizarSystem/MML/blob/047822c4d814630b28eec8ca6b455e9eb912d5ff/mml/yellow17.miz)).
Bartłomiej Skorulski, *The Tichonov Theorem*, received 23 May 2000,
Formalized Mathematics 9(2), 2001. Copyright Association of Mizar
Users. License: GPL-3.0-or-later or CC-BY-SA-3.0 (`doc/COPYING.*`).

This repository does not run the Mizar checker. The 1–1 Lean queue
is `mizarccl_translation_order.yaml`.

## Lean translation

`Yellow17.lean` is an idiomatic Lean 4 translation (dependent products,
Mathlib compactness), first written in
[`catskillsresearch/scott_models`](https://github.com/catskillsresearch/scott_models)
as a standalone root file and extracted here as the Palomar/arxiv
package. Same author.

Mathlib v4.33.0 supplies `isCompact_univ_pi`, `Pi.compactSpace`,
`isCompact_generateFrom`, and `isCompact_iff_finite_subcover`. Those
are dependencies, not a prior formalization of Skorulski’s article.
