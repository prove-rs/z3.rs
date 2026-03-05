#!/usr/bin/env bash
# Regenerate the pre-generated bindings in z3-sys/src/generated/ from the
# pinned Z3 source in z3-src/z3. Run this after bumping the z3-src submodule.
#
# Generates:
#   - z3-sys/src/generated/enums.rs     — transformed rustified enum types (committed)
#   - z3-sys/src/generated/functions.rs — transformed function signatures (committed)
#
# Requires: libclang (for the bindgen feature build)
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HEADER="${REPO_ROOT}/z3-src/z3/src/api/z3.h"

if [[ ! -f "${HEADER}" ]]; then
    echo "error: ${HEADER} not found. Did you init the z3-src submodule?" >&2
    echo "  git submodule update --init z3-src/z3" >&2
    exit 1
fi

echo "Generating enums.rs and functions.rs via bindgen feature..."
Z3_SYS_Z3_HEADER="${HEADER}" Z3_SYS_UPDATE_GENERATED=1 \
    cargo build -p z3-sys --features bindgen -q
echo "Generated enums.rs and functions.rs"

echo ""
echo "Done. Review diffs with:   git diff z3-sys/src/generated/"
echo "Check API coverage with:   scripts/check-bindings.sh"
