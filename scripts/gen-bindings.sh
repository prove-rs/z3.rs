#!/usr/bin/env bash
# Regenerate the pre-generated bindings in z3-sys/src/generated/ from the
# pinned Z3 source in z3-src/z3. Run this after bumping the z3-src submodule.
#
# Generates:
#   - z3-sys/src/generated/{enum}.rs  — rustified enum types (committed)
#   - z3-sys/src/generated/functions_check.rs  — transformed function signatures
#     for drift detection (not committed; see .gitignore)
#
# Requires: bindgen CLI (cargo install bindgen-cli)
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HEADER="${REPO_ROOT}/z3-src/z3/src/api/z3.h"
INCLUDE_DIR="${REPO_ROOT}/z3-src/z3/src/api"
OUT_DIR="${REPO_ROOT}/z3-sys/src/generated"
TRANSFORM="${REPO_ROOT}/scripts/bindgen-transform"

if ! command -v bindgen &>/dev/null; then
    echo "error: bindgen not found. Install it with: cargo install bindgen-cli" >&2
    exit 1
fi

if [[ ! -f "${HEADER}" ]]; then
    echo "error: ${HEADER} not found. Did you init the z3-src submodule?" >&2
    echo "  git submodule update --init z3-src/z3" >&2
    exit 1
fi

mkdir -p "${OUT_DIR}"

for x in ast_kind ast_print_mode decl_kind error_code goal_prec param_kind parameter_kind sort_kind symbol_kind; do
    bindgen "${HEADER}" \
        --disable-header-comment \
        --rustified-enum "Z3_${x}" \
        --allowlist-type "Z3_${x}" \
        -- "-I${INCLUDE_DIR}" \
        > "${OUT_DIR}/${x}.rs"
    echo "Generated ${x}.rs"
done

echo "Generating functions_check.rs..."
bindgen "${HEADER}" \
    --use-core \
    --disable-header-comment \
    --allowlist-function "Z3_.*" \
    --blocklist-type "Z3_.*" \
    --blocklist-type "_Z3_.*" \
    -- "-I${INCLUDE_DIR}" \
    | cargo run --manifest-path "${TRANSFORM}/Cargo.toml" --quiet \
    > "${OUT_DIR}/functions_check.rs"
echo "Generated functions_check.rs"

echo ""
echo "Done. Review enum diffs with: git diff z3-sys/src/generated/"
echo "Check API coverage with:      scripts/check-bindings.sh"
