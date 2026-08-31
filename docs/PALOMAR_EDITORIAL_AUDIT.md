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

Skips policy sync and LLM audit. GitHub Actions uses this until the 58 capstone
Comparator kit exists.

## Policy sync and revert

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
| `scripts/palomar_policy_sync.py` | Upstream check + auto-update |
| `scripts/palomar_editorial_checks.py` | Fast deterministic pre-checks |
| `scripts/palomar_mechanical_report.py` | Local mechanical report JSON |
| `scripts/palomar_editorial_audit.py` | LLM rubric orchestrator |
| `scripts/palomar_editorial_audit.sh` | Venv wrapper for cursor-sdk |
| `scripts/palomar_preflight.sh` | Mechanical + editorial gate |
