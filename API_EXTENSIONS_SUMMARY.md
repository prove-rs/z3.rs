# Z3 Rust API Extensions

This document summarizes the enhancements made to the Z3 Rust bindings to provide better coverage of the Z3 C API and expose more functionality.

## Summary of Changes

### 1. Enhanced AST Types

#### Algebraic Numbers (`z3/src/ast/algebraic.rs`)
- **New type**: `Algebraic` for working with algebraic number values
- **Key functions**:
  - `is_value()` - Check if AST is a valid algebraic value
  - `is_positive()`, `is_negative()`, `is_zero()` - Sign checks  
  - `sign()` - Get numeric sign (-1, 0, 1)
  - `add()`, `sub()`, `mul()`, `div()` - Arithmetic operations
  - `root()`, `power()` - Root and power operations
  - `lt()`, `gt()`, `eq_algebraic()` - Comparison operations
- **API coverage**: Covers 19 Z3 algebraic number functions from `z3_algebraic.h`

#### Polynomial Operations (`z3/src/ast/polynomial.rs`)
- **New type**: `Polynomial` for polynomial operations on Z3 expressions
- **Key functions**:
  - `subresultants()` - Compute nonzero subresultants of two polynomials
- **API coverage**: Covers polynomial operations from `z3_polynomial.h`

### 2. Enhanced Floating-Point Operations (`z3/src/ast/float.rs`)
- **Extended existing `Float` type** with additional operations:
  - `is_negative()`, `is_positive()` - Sign predicates
  - `eq_fpa()` - Floating-point equality
  - `min()`, `max()` - Min/max operations
  - `rem()` - Remainder operation  
  - `sqrt()`, `sqrt_with_rounding_mode()` - Square root
  - `round_to_integral()` - Round to integer
  - `fma()`, `fma_with_rounding_mode()` - Fused multiply-add
  - `to_sbv_with_rounding_mode()`, `to_ubv_with_rounding_mode()` - Bit-vector conversions
  - `to_real()` - Convert to real number
  - `to_fp_with_rounding_mode()` - Convert between FP formats
- **API coverage**: Extended coverage of the 81 functions in `z3_fpa.h`

### 3. Container Types

#### AST Vector (`z3/src/ast_vector.rs`) 
- **New type**: `AstVector` for managing collections of Z3 AST objects
- **Key functions**:
  - `new()` - Create empty vector
  - `len()`, `is_empty()` - Size queries
  - `get()`, `set()` - Element access
  - `push()` - Add elements
  - `resize()` - Change size
  - `to_vec()` - Convert to Rust Vec
  - `from_slice()` - Create from slice
  - `translate()` - Translate to another context
  - Iterator support via `IntoIterator`
- **Memory management**: Proper Z3 reference counting

### 4. Quantifier Elimination (`z3/src/quantifier_elimination_simple.rs`)
- **New type**: `QuantifierElimination` for basic quantifier elimination
- **Key functions**:
  - `lite()` - Light quantifier elimination using Z3_qe_lite
- **Note**: This is a simplified implementation due to some Z3 QE functions not being available in the current Z3 version

## API Coherence Improvements

### Alignment with C API Structure
The new Rust API now more closely mirrors the C API structure from `C:\z3\src\api\`:
- **Algebraic operations** (`api_algebraic.cpp` → `ast/algebraic.rs`)
- **Polynomial operations** (`api_polynomial.cpp` → `ast/polynomial.rs`)  
- **Enhanced FPA operations** (`api_fpa.cpp` → enhanced `ast/float.rs`)
- **AST containers** (`api_ast_vector.cpp` → `ast_vector.rs`)
- **Quantifier elimination** (`api_qe.cpp` → `quantifier_elimination_simple.rs`)

### Function Coverage Analysis
- **Original C API**: 559 total functions
- **Added coverage**: ~40+ new function bindings across:
  - 19 algebraic number functions
  - 1 polynomial function  
  - 15+ enhanced floating-point functions
  - 10+ AST vector functions
  - Basic quantifier elimination

### API Design Principles
1. **Safety**: All unsafe C API calls are wrapped in safe Rust interfaces
2. **Memory Management**: Proper Z3 reference counting via RAII
3. **Type Safety**: Strong typing with appropriate Rust type system usage
4. **Ergonomics**: Idiomatic Rust API design with builder patterns where appropriate
5. **Documentation**: Comprehensive documentation with examples

## Usage Examples

See `examples/api_extensions_demo.rs` for demonstrations of:
- AstVector container operations
- Algebraic number arithmetic and comparisons  
- Polynomial subresultant computation
- Enhanced floating-point operations including FMA

## Build Requirements

The enhanced API maintains the same build requirements as the original:
- LLVM/Clang for bindgen (handled via winget install)
- Z3 libraries (via gh-release feature for precompiled binaries)

## Testing

All enhancements pass the existing test suite and maintain backward compatibility with the original Z3 Rust API.

## Future Work

Additional C API areas that could be added in future iterations:
- **Fixedpoint** (`z3_fixedpoint.h`) - Horn clause solving
- **Optimization** (`z3_optimization.h`) - Optimization queries  
- **Spacer** (`z3_spacer.h`) - Spacer engine
- **Special Relations** - Special relation support
- **Enhanced Sequence/String** operations
- **Advanced Model** operations
- **Parser** functions for string-to-AST conversion

This implementation provides a solid foundation for expanding Z3 Rust API coverage while maintaining safety and ergonomics.