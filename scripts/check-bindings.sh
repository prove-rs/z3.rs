#!/usr/bin/env bash
# Check that all Z3 API functions in the z3-src header are declared in
# z3-sys/src/lib.rs. Exits non-zero if any functions are missing.
#
# Run this after bumping the z3-src submodule to catch newly-added Z3 functions.
#
# Requires: bindgen CLI (cargo install bindgen-cli)
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HEADER="${REPO_ROOT}/z3-src/z3/src/api/z3.h"
INCLUDE_DIR="${REPO_ROOT}/z3-src/z3/src/api"
LIBRS="${REPO_ROOT}/z3-sys/src/lib.rs"

if ! command -v bindgen &>/dev/null; then
    echo "error: bindgen not found. Install it with: cargo install bindgen-cli" >&2
    exit 1
fi

if [[ ! -f "${HEADER}" ]]; then
    echo "error: ${HEADER} not found. Did you init the z3-src submodule?" >&2
    echo "  git submodule update --init z3-src/z3" >&2
    exit 1
fi

# Extract function names from the Z3 header via bindgen.
# --allowlist-function "Z3_.*" captures all public Z3 API functions.
# --blocklist-type removes type definitions; functions still use the type names.
generated_fns=$(
    bindgen "${HEADER}" \
        --no-doc-comments \
        --disable-header-comment \
        --allowlist-function "Z3_.*" \
        --blocklist-type "Z3_.*" \
        --blocklist-type "_Z3_.*" \
        -- "-I${INCLUDE_DIR}" 2>/dev/null \
    | grep -oE "fn Z3_[a-zA-Z0-9_]+" \
    | sed 's/fn //' \
    | sort -u
)

# Extract function names from the hand-written bindings.
librs_fns=$(
    grep -oE "fn Z3_[a-zA-Z0-9_]+" "${LIBRS}" \
    | sed 's/fn //' \
    | sort -u
)

# Functions present in the header but not in lib.rs.
missing=$(comm -23 <(echo "${generated_fns}") <(echo "${librs_fns}") || true)

if [[ -n "${missing}" ]]; then
    count=$(echo "${missing}" | wc -l | tr -d ' ')
    echo "ERROR: ${count} Z3 API function(s) in the header are not declared in" >&2
    echo "       z3-sys/src/lib.rs:" >&2
    echo "${missing}" | sed 's/^/  /' >&2
    echo "" >&2
    echo "Add these functions to z3-sys/src/lib.rs (or run scripts/gen-bindings.sh" >&2
    echo "to generate functions_check.rs for reference)." >&2
    exit 1
fi

total=$(echo "${generated_fns}" | wc -l | tr -d ' ')
echo "OK: all ${total} Z3 API functions are declared in z3-sys/src/lib.rs"
