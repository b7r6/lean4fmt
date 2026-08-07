#!/usr/bin/env bash
# Run or resume the production mathlib lock under its monotone clearances.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export MATHLIB_CENSUS_RES="${MATHLIB_CENSUS_RES:-$here/.lean4fmt/mathlib-full}"
exec "$here/mathlib-census.sh" all "$here/mathlib-full-clearances.json"
