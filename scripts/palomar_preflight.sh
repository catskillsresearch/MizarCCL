#!/usr/bin/env bash
# Thin wrapper: Palomar local preflight lives in vendor/palomar-preflight.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
export PALOMAR_PROJECT_ROOT="$ROOT"
export PALOMAR_SORRY_PATHS="MizarCCL/HIDDEN.lean MizarCCL/TARSKI.lean Solution.lean"
export PALOMAR_CHECK_DECL_KINDS=0
export PALOMAR_CLOSURE_PREFIXES="PreSet TarskiSet instMembership"
export PALOMAR_EXTRA_PRINT_NAMES="PreSet PreSet.Equiv PreSet.instSetoid PreSet.Mem TarskiSet TarskiSet.mem instMembership TARSKI.subset TARSKI.instHasSubset"
exec bash "$ROOT/vendor/palomar-preflight/palomar_preflight.sh" "$@"
