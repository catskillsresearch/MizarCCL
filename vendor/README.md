# Vendored Mizar

Palomar cannot preserve git submodules. This repository vendors a
**used-module slice** of Mizar 7.13.01 / MML 4.181.1147 as ordinary
files, not a submodule of [MizarSystem/MML](https://github.com/MizarSystem/MML.git).

## What is checked in

Pin (also `vendor/MML_PIN`):

```
047822c4d814630b28eec8ca6b455e9eb912d5ff
```

`vendor/mml/` contains:

- `hidden.miz` (Mizar built-ins; not on the translation queue)
- the 368 articles in `mizarccl_translation_order.yaml`

That is the YELLOW* / WAYBEL* environ closure. Unreached MML
articles are not vendored.

## Optional full library

Regenerating the queue (`scripts/mizarccl_translation_order.py`)
needs the complete MML plus `mml.lar`. That checkout is
**gitignored** at `vendor/MML`:

```bash
git clone https://github.com/MizarSystem/MML.git vendor/MML
git -C vendor/MML checkout "$(cat vendor/MML_PIN)"
```

Do not add `vendor/MML` as a submodule.

## PalomarPolicy snapshot

Editorial audit prompts are vendored under `vendor/palomar-policy/` with pin
`vendor/PALOMAR_POLICY_PIN` (from
[PalomarRegistry/PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy)).
`scripts/palomar_policy_sync.py` refreshes from upstream before full preflight.
See `docs/PALOMAR_EDITORIAL_AUDIT.md`.
