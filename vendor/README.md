# Vendored Mizar

`vendor/MML` is a git submodule of
[MizarSystem/MML](https://github.com/MizarSystem/MML.git) pinned at

```
047822c4d814630b28eec8ca6b455e9eb912d5ff
```

That commit is **Mizar 7.13.01 / MML 4.181.1147** (2012-03-17): the
processor, `prel` database, and all 1153 `mml/*.miz` articles.

## Clone / update

```bash
git submodule update --init --recursive
git -C vendor/MML rev-parse HEAD
```

The expected SHA is the pin above. Do not advance the submodule until
the translation queue is deliberately retargeted.

## Why the whole library

A 1–1 Lean translation of a Mizar article needs the articles named in
its `environ` (and theirs), not a Mathlib paraphrase. The YELLOW* /
WAYBEL* family closes to 368 articles; the other ~800 stay vendored
but are not on the translation queue. See
`mizarccl_translation_order.yaml`.
