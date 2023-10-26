
WORKSPACE=$1
VCPKG_ROOT=$2
VCPKG_TRIPLET=$3
LIB=$4

ls $VCPKG_ROOT/installed/$VCPKG_TRIPLET/lib
ls $VCPKG_ROOT/installed/$VCPKG_TRIPLET/include

mkdir "$WORKSPACE/$VCPKG_TRIPLET"

headers=("z3.h" "z3_algebraic.h" "z3_api.h" "z3_ast_containers.h" "z3_fixedpoint.h" "z3_fpa.h" "z3_macros.h" "z3_optimization.h" "z3_polynomial.h" "z3_rcf.h" "z3_spacer.h" "z3_v1.h" "z3_version.h")
for i in $headers
do
cp "$VCPKG_ROOT/installed/$VCPKG_TRIPLET/include/$file" "$WORKSPACE/$VCPKG_TRIPLET/$file"
done
cp "$VCPKG_ROOT/installed/$VCPKG_TRIPLET/lib/$LIB" "$WORKSPACE/$VCPKG_TRIPLET/$LIB"

tar -jcvf "$WORKSPACE/$VCPKG_TRIPLET.tar.gz" "$WORKSPACE/$VCPKG_TRIPLET"