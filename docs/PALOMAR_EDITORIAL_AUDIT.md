# Palomar editorial audit (local dry-run)

This repository vendors [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy)
under `vendor/palomar-policy/` and runs the same editorial prompt rubric locally
before treating a Comparator kit as submission-ready.

## Full preflight

```bash
# CURSOR_API_KEY in env, or in ../tokens_ssto.yaml (same as scott1964 OCR pipeline)
bash scripts/palomar_preflight.sh
```

Full preflight runs:

1. Mechanical Comparator checks (build, type match, sorry scan, axioms, …)
2. **Policy sync** — compares `vendor/PALOMAR_POLICY_PIN` to upstream `main` and
   refreshes the vendored tree when newer
3. Deterministic editorial pre-checks (`scripts/palomar_editorial_checks.py`)
4. Local `mechanical-report.json` stub
5. **LLM editorial audit** via **Cursor SDK** (`scripts/palomar_editorial_audit.sh`)
   - **Substantive passes** (matching Palomar content reports): **`gpt-5.6-sol`**
     — `statement_alignment`, `definition_fidelity`, `literature_notability`, `synthesis`
   - **Lighter passes** (cheaper): **`composer-2.5`**
     — `classification`, `metadata`, optional `proof_account`

Output: `.cache/palomar-editorial/review-draft.json` (gitignored).

Preflight is green only when synthesis outcome is **`neutral`**.

## Mechanical-only (CI / translation work)

```bash
bash scripts/palomar_preflight.sh --mechanical-only
```

Skips policy sync and LLM audit. **Use this by default** while translating
the 368-article queue. GitHub Actions uses this until the 58 capstone
Comparator kit exists.

Interim infrastructure articles (TARSKI, SETWISEO, FUNCT_*, …) are not
capstone candidates. Tweaking the Comparator narrative as each article
lands will not clear Palomar's research-interest floor; defer full
editorial audit until real YELLOW*/WAYBEL* seed capstones are selected.

## Workflow: translation vs capstone packaging

| Phase | Preflight | Comparator kit |
| --- | --- | --- |
| Queue translation (now) | `--mechanical-only` only | Optional experiments; do not update per article |
| Capstone selection (after 368 green) | Full preflight on each seed kit | One headline theorem per `palomar_seeds` entry |
| Pre-submission dry-run | One full audit before locking the first kit | All packaging checks green |

Full editorial audit cost: about **six sequential LLM calls**
(two `composer-2.5`, four `gpt-5.6-sol`), roughly **$1–1.50** and several
minutes wall time per run. Running it on interim scaffolds mostly repeats
predictable **literature_notability** rejections.

## Capstone kit checklist

Before running full preflight on a submission candidate, confirm:

1. **Research interest** — the selected theorem is a seed headline from
   YELLOW*/WAYBEL*, not queue infrastructure. Palomar indexes results that
   could plausibly warrant a research paper or serious note; development
   size and faithful translation alone do not qualify.
2. **Definition pinning** — every material symbol in each compared theorem
   type is either primitive, defined without `sorry` in Challenge.lean, or
   listed in `comparator.json` → `definition_names` with its defining or
   semantic law also compared. Opaque `sorry` stubs make the theorem
   unauditable (`definition_fidelity` failure).
3. **Metadata sync** — `formalization.yaml` `status.scope`, `limitations`,
   `alignment`, and `main_results` match `comparator.json` and the actual
   Challenge/Solution imports.
4. **Sources** — each distinct compared result group has a `sources:` entry
   (Mizar article location, authorship, relationship). Do not compare
   SETWISEO (or any non-TARSKI) theorems while `sources:` lists TARSKI only.
5. **Mechanical green** — `bash scripts/palomar_preflight.sh --mechanical-only`
   passes, then `bash vendor/palomar-preflight/compare_challenge_solution_types.sh`.

Deterministic packaging checks live in `scripts/palomar_editorial_checks.py`
(scope/comparator sync, sorry-definition pinning, compared-source hints).
They run during **full** preflight only and fail fast before the LLM audit.

## Lessons from interim experiments (2026-08-31)

Adding `SETWISEO:59` to the TARSKI scaffold confirmed:

- **Notability cannot be narrated away** — the rubric rejected TARSKI +
  a finite-union homomorphism lemma even when statement alignment was neutral.
  Better prose on infrastructure theorems does not substitute for seed
  capstone selection.
- **Opaque dependencies fail definition fidelity** — `setwiseo_th59` used
  seven `sorry`'d Challenge names (`FinUnion`, `Fin`, `apply`, …) omitted
  from `definition_names`. Comparator accepted the theorem type without
  pinning what “finite union” means.
- **Metadata drift is mechanical** — `formalization.yaml` still described a
  14-theorem TARSKI-only kit after `comparator.json` listed 15 entries.
- **Value of one experiment** — packaging rules are now encoded in
  `palomar_editorial_checks.py` and this doc. Repeat full audits only when
  deliberately testing a capstone-shaped kit.

## Experimental pre-submission surface

- Pin file: `vendor/PALOMAR_POLICY_PIN`
- Sync script: `scripts/palomar_policy_sync.py`
- Skip upstream check: `bash scripts/palomar_preflight.sh --no-policy-sync`

If a bad upstream draft is pulled, revert before committing:

```bash
git checkout -- vendor/palomar-policy vendor/PALOMAR_POLICY_PIN
```

After a good audit that updated policy, commit the vendored snapshot and pin
together so GitHub records which editorial contract was in effect.

## Experimental pre-submission surface

Before the queue is complete, Challenge/Solution/comparator are an
experimental surface and may be changed freely to test translated results
against the Palomar editorial rubric. The current experiment adds
`SETWISEO:59` to the TARSKI scaffold. A full editorial audit may still fail
**literature_notability**: that is useful feedback, not a mechanical defect.

Registry submission remains deferred per `HANDOFF.md` until the full closure
and 58 seed capstones are ready.

## Models and auth

| Pass | Model | Notes |
|------|-------|-------|
| statement_alignment, definition_fidelity, literature_notability, synthesis | `gpt-5.6-sol` | Palomar production editorial model |
| classification, metadata, proof_account | `composer-2.5` | cheaper ancillary checks |

Override via `PALOMAR_EDITORIAL_PRIMARY_MODEL` / `PALOMAR_EDITORIAL_ECONOMY_MODEL`.

Auth: `CURSOR_API_KEY` environment variable, or `CURSOR_API_KEY` in
`../tokens_ssto.yaml` (shared with `scott1964` scripts).

First run creates `.venv-editorial/` with `cursor-sdk` and `pyyaml`.

## Files

| Path | Role |
|------|------|
| `vendor/palomar-policy/` | Vendored prompts, rubric, CONTRIBUTING, schemas |
| `vendor/PALOMAR_POLICY_PIN` | Upstream PalomarPolicy commit SHA |
| `vendor/palomar-preflight/` | Vendored local preflight toolkit (not a submodule) |
| `vendor/PALOMAR_PREFLIGHT_PIN` | palomar-preflight commit SHA |
| `scripts/palomar_preflight.sh` | Project wrapper: mechanical + editorial gate |
