use crate::generated;

/// The different kinds of symbol.
/// In Z3, a symbol can be represented using integers and
/// strings. See [`Z3_get_symbol_kind`].
///
/// This corresponds to `Z3_symbol_kind` in the C API.
///
/// # See also:
///
/// - [`Z3_mk_int_symbol`]
/// - [`Z3_mk_string_symbol`]
/// - [`Z3_symbol`]
#[repr(u32)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    /// An integer symbol.
    ///
    /// This corresponds to `Z3_INT_SYMBOL` in the C API.
    Int = generated::Z3_symbol_kind::Z3_INT_SYMBOL as u32,
    /// A string symbol.
    ///
    /// This corresponds to `Z3_STRING_SYMBOL` in the C API.
    String = generated::Z3_symbol_kind::Z3_STRING_SYMBOL as u32,
}

/// The different kinds of parameters that can be associated with function symbols.
///
/// This corresponds to `Z3_parameter_kind` in the C API.
///
/// # See also:
///
/// - [`Z3_get_decl_num_parameters`]
/// - [`Z3_get_decl_parameter_kind`]
#[repr(u32)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ParameterKind {
    /// An integer parameter.
    ///
    /// This corresponds to `Z3_PARAMETER_INT` in the C API.
    Int = generated::Z3_parameter_kind::Z3_PARAMETER_INT as u32,
    /// A double parameter.
    ///
    /// This corresponds to `Z3_PARAMETER_DOUBLE` in the C API.
    Double = generated::Z3_parameter_kind::Z3_PARAMETER_DOUBLE as u32,
    /// A rational number parameter.
    ///
    /// This corresponds to `Z3_PARAMETER_RATIONAL` in the C API.
    Rational = generated::Z3_parameter_kind::Z3_PARAMETER_RATIONAL as u32,
    /// A symbol parameter.
    ///
    /// This corresponds to `Z3_PARAMETER_SYMBOL` in the C API.
    Symbol = generated::Z3_parameter_kind::Z3_PARAMETER_SYMBOL as u32,
    /// A sort parameter.
    ///
    /// This corresponds to `Z3_PARAMETER_SORT` in the C API.
    Sort = generated::Z3_parameter_kind::Z3_PARAMETER_SORT as u32,
    /// An expression parameter.
    ///
    /// This corresponds to `Z3_PARAMETER_AST` in the C API.
    AST = generated::Z3_parameter_kind::Z3_PARAMETER_AST as u32,
    /// A function declaration parameter.
    ///
    /// This corresponds to `Z3_PARAMETER_FUNC_DECL` in the C API.
    FuncDecl = generated::Z3_parameter_kind::Z3_PARAMETER_FUNC_DECL as u32,
}

/// The different kinds of Z3 types.
///
/// This corresponds to `Z3_sort_kind` in the C API.
#[repr(u32)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum SortKind {
    /// This corresponds to `Z3_UNINTERPRETED_SORT` in the C API.
    Uninterpreted = generated::Z3_sort_kind::Z3_UNINTERPRETED_SORT as u32,
    /// This corresponds to `Z3_BOOL_SORT` in the C API.
    Bool = generated::Z3_sort_kind::Z3_BOOL_SORT as u32,
    /// This corresponds to `Z3_INT_SORT` in the C API.
    Int = generated::Z3_sort_kind::Z3_INT_SORT as u32,
    /// This corresponds to `Z3_REAL_SORT` in the C API.
    Real = generated::Z3_sort_kind::Z3_REAL_SORT as u32,
    /// This corresponds to `Z3_BV_SORT` in the C API.
    BV = generated::Z3_sort_kind::Z3_BV_SORT as u32,
    /// This corresponds to `Z3_ARRAY_SORT` in the C API.
    Array = generated::Z3_sort_kind::Z3_ARRAY_SORT as u32,
    /// This corresponds to `Z3_DATATYPE_SORT` in the C API.
    Datatype = generated::Z3_sort_kind::Z3_DATATYPE_SORT as u32,
    /// This corresponds to `Z3_RELATION_SORT` in the C API.
    Relation = generated::Z3_sort_kind::Z3_RELATION_SORT as u32,
    /// This corresponds to `Z3_FINITE_DOMAIN_SORT` in the C API.
    FiniteDomain = generated::Z3_sort_kind::Z3_FINITE_DOMAIN_SORT as u32,
    /// This corresponds to `Z3_FLOATING_POINT_SORT` in the C API.
    FloatingPoint = generated::Z3_sort_kind::Z3_FLOATING_POINT_SORT as u32,
    /// This corresponds to `Z3_ROUNDING_MODE_SORT` in the C API.
    RoundingMode = generated::Z3_sort_kind::Z3_ROUNDING_MODE_SORT as u32,
    /// This corresponds to `Z3_SEQ_SORT` in the C API.
    Seq = generated::Z3_sort_kind::Z3_SEQ_SORT as u32,
    /// This corresponds to `Z3_RE_SORT` in the C API.
    RE = generated::Z3_sort_kind::Z3_RE_SORT as u32,
    /// This corresponds to `Z3_CHAR_SORT` in the C API.
    Char = generated::Z3_sort_kind::Z3_CHAR_SORT as u32,
    /// This corresponds to `Z3_TYPE_VAR` in the C API.
    TypeVar = generated::Z3_sort_kind::Z3_TYPE_VAR as u32,
    /// This corresponds to `Z3_UNKNOWN_SORT` in the C API.
    Unknown = generated::Z3_sort_kind::Z3_UNKNOWN_SORT as u32,
}

/// The different kinds of Z3 AST (abstract syntax trees). That is, terms, formulas and types.
///
/// This corresponds to `Z3_ast_kind` in the C API.
#[repr(u32)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum AstKind {
    /// numeral constants
    ///
    /// This corresponds to `Z3_NUMERAL_AST` in the C API.
    Numeral = generated::Z3_ast_kind::Z3_NUMERAL_AST as u32,
    /// constant and applications
    ///
    /// This corresponds to `Z3_APP_AST` in the C API.
    App = generated::Z3_ast_kind::Z3_APP_AST as u32,
    /// bound variables
    ///
    /// This corresponds to `Z3_VAR_AST` in the C API.
    Var = generated::Z3_ast_kind::Z3_VAR_AST as u32,
    /// quantifiers
    ///
    /// This corresponds to `Z3_QUANTIFIER_AST` in the C API.
    Quantifier = generated::Z3_ast_kind::Z3_QUANTIFIER_AST as u32,
    /// sort
    ///
    /// This corresponds to `Z3_SORT_AST` in the C API.
    Sort = generated::Z3_ast_kind::Z3_SORT_AST as u32,
    /// function declaration
    ///
    /// This corresponds to `Z3_FUNC_DECL_AST` in the C API.
    FuncDecl = generated::Z3_ast_kind::Z3_FUNC_DECL_AST as u32,
    /// internal
    ///
    /// This corresponds to `Z3_UNKNOWN_AST` in the C API.
    Unknown = generated::Z3_ast_kind::Z3_UNKNOWN_AST as u32,
}

/// The different kinds of interpreted function kinds.
///
/// This corresponds to `Z3_decl_kind` in the C API.
#[repr(u32)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum DeclKind {
    /// The constant `true`.
    TRUE = generated::Z3_decl_kind::Z3_OP_TRUE as u32,
    /// The constant `false`.
    FALSE = generated::Z3_decl_kind::Z3_OP_FALSE as u32,
    /// The equality predicate.
    EQ = generated::Z3_decl_kind::Z3_OP_EQ as u32,
    /// The n-ary distinct predicate (every argument is mutually distinct).
    DISTINCT = generated::Z3_decl_kind::Z3_OP_DISTINCT as u32,
    /// The ternary if-then-else term.
    ITE = generated::Z3_decl_kind::Z3_OP_ITE as u32,
    /// n-ary conjunction.
    AND = generated::Z3_decl_kind::Z3_OP_AND as u32,
    /// n-ary disjunction.
    OR = generated::Z3_decl_kind::Z3_OP_OR as u32,
    /// equivalence (binary).
    IFF = generated::Z3_decl_kind::Z3_OP_IFF as u32,
    /// Exclusive or.
    XOR = generated::Z3_decl_kind::Z3_OP_XOR as u32,
    /// Negation.
    NOT = generated::Z3_decl_kind::Z3_OP_NOT as u32,
    /// Implication.
    IMPLIES = generated::Z3_decl_kind::Z3_OP_IMPLIES as u32,
    /// Binary equivalence modulo namings. This binary predicate is used
    /// in proof terms. It captures equisatisfiability and equivalence
    /// modulo renamings.
    OEQ = generated::Z3_decl_kind::Z3_OP_OEQ as u32,
    /// Arithmetic numeral.
    ANUM = generated::Z3_decl_kind::Z3_OP_ANUM as u32,
    /// Arithmetic algebraic numeral. Algebraic numbers are used to
    /// represent irrational numbers in Z3.
    AGNUM = generated::Z3_decl_kind::Z3_OP_AGNUM as u32,
    /// `<=`.
    LE = generated::Z3_decl_kind::Z3_OP_LE as u32,
    /// `>=`.
    GE = generated::Z3_decl_kind::Z3_OP_GE as u32,
    /// `<`.
    LT = generated::Z3_decl_kind::Z3_OP_LT as u32,
    /// `>`.
    GT = generated::Z3_decl_kind::Z3_OP_GT as u32,
    /// Addition - Binary.
    ADD = generated::Z3_decl_kind::Z3_OP_ADD as u32,
    /// Binary subtraction.
    SUB = generated::Z3_decl_kind::Z3_OP_SUB as u32,
    /// Unary minus.
    UMINUS = generated::Z3_decl_kind::Z3_OP_UMINUS as u32,
    /// Multiplication - Binary.
    MUL = generated::Z3_decl_kind::Z3_OP_MUL as u32,
    /// Division - Binary.
    DIV = generated::Z3_decl_kind::Z3_OP_DIV as u32,
    /// Integer division - Binary.
    IDIV = generated::Z3_decl_kind::Z3_OP_IDIV as u32,
    /// Remainder - Binary.
    REM = generated::Z3_decl_kind::Z3_OP_REM as u32,
    /// Modulus - Binary.
    MOD = generated::Z3_decl_kind::Z3_OP_MOD as u32,
    /// Coercion of integer to real - Unary.
    TO_REAL = generated::Z3_decl_kind::Z3_OP_TO_REAL as u32,
    /// Coercion of real to integer - Unary.
    TO_INT = generated::Z3_decl_kind::Z3_OP_TO_INT as u32,
    /// Check if real is also an integer - Unary.
    IS_INT = generated::Z3_decl_kind::Z3_OP_IS_INT as u32,
    /// Power operator `x^y`.
    POWER = generated::Z3_decl_kind::Z3_OP_POWER as u32,
    /// Array store. It satisfies `select(store(a,i,v),j) = if i = j then v else select(a,j)`.
    /// Array store takes at least 3 arguments.
    STORE = generated::Z3_decl_kind::Z3_OP_STORE as u32,
    /// Array select.
    SELECT = generated::Z3_decl_kind::Z3_OP_SELECT as u32,
    /// The constant array. For example, `select(const(v),i) = v`
    /// holds for every `v` and `i`. The function is unary.
    CONST_ARRAY = generated::Z3_decl_kind::Z3_OP_CONST_ARRAY as u32,
    /// Array map operator.
    /// It satisfies `map[f](a1,..,a_n)[i] = f(a1[i],...,a_n[i])` for every `i`.
    ARRAY_MAP = generated::Z3_decl_kind::Z3_OP_ARRAY_MAP as u32,
    /// Default value of arrays. For example `default(const(v)) = v`. The function is unary.
    ARRAY_DEFAULT = generated::Z3_decl_kind::Z3_OP_ARRAY_DEFAULT as u32,
    /// Set union between two Boolean arrays (two arrays whose range
    /// type is Boolean). The function is binary.
    SET_UNION = generated::Z3_decl_kind::Z3_OP_SET_UNION as u32,
    /// Set intersection between two Boolean arrays. The function is binary.
    SET_INTERSECT = generated::Z3_decl_kind::Z3_OP_SET_INTERSECT as u32,
    /// Set difference between two Boolean arrays. The function is binary.
    SET_DIFFERENCE = generated::Z3_decl_kind::Z3_OP_SET_DIFFERENCE as u32,
    /// Set complement of a Boolean array. The function is unary.
    SET_COMPLEMENT = generated::Z3_decl_kind::Z3_OP_SET_COMPLEMENT as u32,
    /// Subset predicate between two Boolean arrays. The relation is binary.
    SET_SUBSET = generated::Z3_decl_kind::Z3_OP_SET_SUBSET as u32,
    /// An array value that behaves as the function graph of the
    /// function passed as parameter.
    AS_ARRAY = generated::Z3_decl_kind::Z3_OP_AS_ARRAY as u32,
    /// Array extensionality function. It takes two arrays as arguments and
    /// produces an index, such that the arrays
    /// are different if they are different on the index.
    ARRAY_EXT = generated::Z3_decl_kind::Z3_OP_ARRAY_EXT as u32,
    /// Bit-vector numeral.
    BNUM = generated::Z3_decl_kind::Z3_OP_BNUM as u32,
    /// One bit bit-vector.
    BIT1 = generated::Z3_decl_kind::Z3_OP_BIT1 as u32,
    /// Zero bit bit-vector.
    BIT0 = generated::Z3_decl_kind::Z3_OP_BIT0 as u32,
    /// Unary minus.
    BNEG = generated::Z3_decl_kind::Z3_OP_BNEG as u32,
    /// Binary addition.
    BADD = generated::Z3_decl_kind::Z3_OP_BADD as u32,
    /// Binary subtraction.
    BSUB = generated::Z3_decl_kind::Z3_OP_BSUB as u32,
    /// Binary multiplication.
    BMUL = generated::Z3_decl_kind::Z3_OP_BMUL as u32,
    /// Binary signed division.
    BSDIV = generated::Z3_decl_kind::Z3_OP_BSDIV as u32,
    /// Binary unsigned division.
    BUDIV = generated::Z3_decl_kind::Z3_OP_BUDIV as u32,
    /// Binary signed remainder.
    BSREM = generated::Z3_decl_kind::Z3_OP_BSREM as u32,
    /// Binary unsigned remainder.
    BUREM = generated::Z3_decl_kind::Z3_OP_BUREM as u32,
    /// Binary signed modulus.
    BSMOD = generated::Z3_decl_kind::Z3_OP_BSMOD as u32,
    /// Unary function. `bsdiv(x, 0)` is congruent to `bsdiv0(x)`.
    BSDIV0 = generated::Z3_decl_kind::Z3_OP_BSDIV0 as u32,
    /// Unary function. `budiv(x, 0)` is congruent to `budiv0(x)`.
    BUDIV0 = generated::Z3_decl_kind::Z3_OP_BUDIV0 as u32,
    /// Unary function. `bsrem(x, 0)` is congruent to `bsrem0(x)`.
    BSREM0 = generated::Z3_decl_kind::Z3_OP_BSREM0 as u32,
    /// Unary function. `burem(x, 0)` is congruent to `burem0(x)`.
    BUREM0 = generated::Z3_decl_kind::Z3_OP_BUREM0 as u32,
    /// Unary function. `bsmod(x, 0)` is congruent to `bsmod0(x)`.
    BSMOD0 = generated::Z3_decl_kind::Z3_OP_BSMOD0 as u32,
    /// Unsigned bit-vector <= - Binary relation.
    ULEQ = generated::Z3_decl_kind::Z3_OP_ULEQ as u32,
    /// Signed bit-vector  <= - Binary relation.
    SLEQ = generated::Z3_decl_kind::Z3_OP_SLEQ as u32,
    /// Unsigned bit-vector  >= - Binary relation.
    UGEQ = generated::Z3_decl_kind::Z3_OP_UGEQ as u32,
    /// Signed bit-vector  >= - Binary relation.
    SGEQ = generated::Z3_decl_kind::Z3_OP_SGEQ as u32,
    /// Unsigned bit-vector  < - Binary relation.
    ULT = generated::Z3_decl_kind::Z3_OP_ULT as u32,
    /// Signed bit-vector < - Binary relation.
    SLT = generated::Z3_decl_kind::Z3_OP_SLT as u32,
    /// Unsigned bit-vector > - Binary relation.
    UGT = generated::Z3_decl_kind::Z3_OP_UGT as u32,
    /// Signed bit-vector > - Binary relation.
    SGT = generated::Z3_decl_kind::Z3_OP_SGT as u32,
    /// Bit-wise and - Binary.
    BAND = generated::Z3_decl_kind::Z3_OP_BAND as u32,
    /// Bit-wise or - Binary.
    BOR = generated::Z3_decl_kind::Z3_OP_BOR as u32,
    /// Bit-wise not - Unary.
    BNOT = generated::Z3_decl_kind::Z3_OP_BNOT as u32,
    /// Bit-wise xor - Binary.
    BXOR = generated::Z3_decl_kind::Z3_OP_BXOR as u32,
    /// Bit-wise nand - Binary.
    BNAND = generated::Z3_decl_kind::Z3_OP_BNAND as u32,
    /// Bit-wise nor - Binary.
    BNOR = generated::Z3_decl_kind::Z3_OP_BNOR as u32,
    /// Bit-wise xnor - Binary.
    BXNOR = generated::Z3_decl_kind::Z3_OP_BXNOR as u32,
    /// Bit-vector concatenation - Binary.
    CONCAT = generated::Z3_decl_kind::Z3_OP_CONCAT as u32,
    /// Bit-vector sign extension.
    SIGN_EXT = generated::Z3_decl_kind::Z3_OP_SIGN_EXT as u32,
    /// Bit-vector zero extension.
    ZERO_EXT = generated::Z3_decl_kind::Z3_OP_ZERO_EXT as u32,
    /// Bit-vector extraction.
    EXTRACT = generated::Z3_decl_kind::Z3_OP_EXTRACT as u32,
    /// Repeat bit-vector n times.
    REPEAT = generated::Z3_decl_kind::Z3_OP_REPEAT as u32,
    /// Bit-vector reduce or - Unary.
    BREDOR = generated::Z3_decl_kind::Z3_OP_BREDOR as u32,
    /// Bit-vector reduce and - Unary.
    BREDAND = generated::Z3_decl_kind::Z3_OP_BREDAND as u32,
    BCOMP = generated::Z3_decl_kind::Z3_OP_BCOMP as u32,
    /// Shift left.
    BSHL = generated::Z3_decl_kind::Z3_OP_BSHL as u32,
    /// Logical shift right.
    BLSHR = generated::Z3_decl_kind::Z3_OP_BLSHR as u32,
    /// Arithmetical shift right.
    BASHR = generated::Z3_decl_kind::Z3_OP_BASHR as u32,
    /// Left rotation.
    ROTATE_LEFT = generated::Z3_decl_kind::Z3_OP_ROTATE_LEFT as u32,
    /// Right rotation.
    ROTATE_RIGHT = generated::Z3_decl_kind::Z3_OP_ROTATE_RIGHT as u32,
    /// (extended) Left rotation. Similar to `DeclKind::ROTATE_LEFT`,
    /// but it is a binary operator instead of a parametric one.
    EXT_ROTATE_LEFT = generated::Z3_decl_kind::Z3_OP_EXT_ROTATE_LEFT as u32,
    /// (extended) Right rotation. Similar to `DeclKind::ROTATE_RIGHT`,
    /// but it is a binary operator instead of a parametric one.
    EXT_ROTATE_RIGHT = generated::Z3_decl_kind::Z3_OP_EXT_ROTATE_RIGHT as u32,
    BIT2BOOL = generated::Z3_decl_kind::Z3_OP_BIT2BOOL as u32,
    /// Coerce integer to bit-vector.
    ///
    /// NB. This function is not supported by the decision procedures.
    /// Only the most rudimentary simplification rules are applied to
    /// this function.
    INT2BV = generated::Z3_decl_kind::Z3_OP_INT2BV as u32,
    /// Coerce bit-vector to integer.
    ///
    /// NB. This function is not supported by the decision procedures.
    /// Only the most rudimentary simplification rules are applied to
    /// this function.
    BV2INT = generated::Z3_decl_kind::Z3_OP_BV2INT as u32,
    /// Compute the carry bit in a full-adder.
    /// The meaning is given by the equivalence:
    ///
    /// ```text
    /// (carry l1 l2 l3) <=> (or (and l1 l2) (and l1 l3) (and l2 l3)))
    /// ```
    CARRY = generated::Z3_decl_kind::Z3_OP_CARRY as u32,
    /// Compute ternary XOR.
    ///
    /// The meaning is given by the equivalence:
    ///
    /// ```text
    /// (xor3 l1 l2 l3) <=> (xor (xor l1 l2) l3)
    /// ```
    XOR3 = generated::Z3_decl_kind::Z3_OP_XOR3 as u32,
    /// Check that bit-wise signed multiplication does not overflow.
    ///
    /// Signed multiplication overflows if the operands have the
    /// same sign and the result of multiplication does not fit
    /// within the available bits.
    ///
    /// # See also:
    ///
    /// - [`Z3_mk_bvmul_no_overflow`]
    BSMUL_NO_OVFL = generated::Z3_decl_kind::Z3_OP_BSMUL_NO_OVFL as u32,
    /// Check that bit-wise unsigned multiplication does not overflow.
    ///
    /// Unsigned multiplication overflows if the result does not fit
    /// within the available bits.
    ///
    /// # See also:
    ///
    /// - [`Z3_mk_bvmul_no_overflow`]
    BUMUL_NO_OVFL = generated::Z3_decl_kind::Z3_OP_BUMUL_NO_OVFL as u32,
    /// Check that bit-wise signed multiplication does not underflow.
    ///
    /// Signed multiplication underflows if the operands have opposite
    /// signs and the result of multiplication does not fit within the
    /// available bits.
    ///
    /// # See also:
    ///
    /// - [`Z3_mk_bvmul_no_underflow`]
    BSMUL_NO_UDFL = generated::Z3_decl_kind::Z3_OP_BSMUL_NO_UDFL as u32,
    /// Binary signed division.
    ///
    /// It has the same semantics as `DeclKind::BSDIV`, but created in
    /// a context where the second operand can be assumed to be non-zero.
    BSDIV_I = generated::Z3_decl_kind::Z3_OP_BSDIV_I as u32,
    /// Binary unsigned division.
    ///
    /// It has the same semantics as `DeclKind::BUDIV`, but created in a
    /// context where the second operand can be assumed to be non-zero.
    BUDIV_I = generated::Z3_decl_kind::Z3_OP_BUDIV_I as u32,
    /// Binary signed remainder.
    ///
    /// It has the same semantics as `DeclKind::BSREM`, but created in a
    /// context where the second operand can be assumed to be non-zero.
    BSREM_I = generated::Z3_decl_kind::Z3_OP_BSREM_I as u32,
    /// Binary unsigned remainder.
    ///
    /// It has the same semantics as `DeclKind::BUREM`, but created in a
    /// context where the second operand can be assumed to be non-zero.
    BUREM_I = generated::Z3_decl_kind::Z3_OP_BUREM_I as u32,
    /// Binary signed modulus.
    ///
    /// It has the same semantics as `DeclKind::BSMOD`, but created in a
    /// context where the second operand can be assumed to be non-zero.
    BSMOD_I = generated::Z3_decl_kind::Z3_OP_BSMOD_I as u32,
    /// Undef/Null proof object.
    PR_UNDEF = generated::Z3_decl_kind::Z3_OP_PR_UNDEF as u32,
    /// Proof for the expression 'true'.
    PR_TRUE = generated::Z3_decl_kind::Z3_OP_PR_TRUE as u32,
    /// Proof for a fact asserted by the user.
    PR_ASSERTED = generated::Z3_decl_kind::Z3_OP_PR_ASSERTED as u32,
    /// Proof for a fact (tagged as goal) asserted by the user.
    PR_GOAL = generated::Z3_decl_kind::Z3_OP_PR_GOAL as u32,
    /// Given a proof for p and a proof for (implies p q), produces a proof for q.
    ///
    /// ```text
    /// T1: p
    /// T2: (implies p q)
    /// [mp T1 T2]: q
    /// ```
    ///
    /// The second antecedents may also be a proof for `(iff p q)`.
    PR_MODUS_PONENS = generated::Z3_decl_kind::Z3_OP_PR_MODUS_PONENS as u32,
    /// A proof for `(R t t)`, where `R` is a reflexive relation.
    ///
    /// This proof object has no antecedents.
    ///
    /// The only reflexive relations that are used are
    /// equivalence modulo namings, equality and equivalence.
    /// That is, `R` is either `~`, `=` or `iff`.
    PR_REFLEXIVITY = generated::Z3_decl_kind::Z3_OP_PR_REFLEXIVITY as u32,
    /// Given an symmetric relation `R` and a proof for `(R t s)`,
    /// produces a proof for `(R s t)`.
    ///
    /// ```text
    /// T1: (R t s)
    /// [symmetry T1]: (R s t)
    /// ```
    ///
    /// `T1` is the antecedent of this proof object.
    PR_SYMMETRY = generated::Z3_decl_kind::Z3_OP_PR_SYMMETRY as u32,
    /// Given a transitive relation `R`, and proofs for `(R t s)` and
    /// `(R s u)`, produces a proof for `(R t u)`.
    ///
    /// ```text
    /// T1: (R t s)
    /// T2: (R s u)
    /// [trans T1 T2]: (R t u)
    /// ```
    PR_TRANSITIVITY = generated::Z3_decl_kind::Z3_OP_PR_TRANSITIVITY as u32,
    /// Condensed transitivity proof.
    ///
    /// It combines several symmetry and transitivity proofs.
    ///
    /// Example:
    ///
    /// ```text
    /// T1: (R a b)
    /// T2: (R c b)
    /// T3: (R c d)
    /// [trans* T1 T2 T3]: (R a d)
    /// ```
    ///
    /// `R` must be a symmetric and transitive relation.
    ///
    /// Assuming that this proof object is a proof for `(R s t)`, then
    /// a proof checker must check if it is possible to prove `(R s t)`
    /// using the antecedents, symmetry and transitivity.  That is,
    /// if there is a path from `s` to `t`, if we view every
    /// antecedent `(R a b)` as an edge between `a` and `b`.
    PR_TRANSITIVITY_STAR = generated::Z3_decl_kind::Z3_OP_PR_TRANSITIVITY_STAR as u32,
    /// Monotonicity proof object.
    ///
    /// ```text
    /// T1: (R t_1 s_1)
    /// ...
    /// Tn: (R t_n s_n)
    /// [monotonicity T1 ... Tn]: (R (f t_1 ... t_n) (f s_1 ... s_n))
    /// ```
    ///
    /// Remark: if `t_i == s_i`, then the antecedent `Ti` is suppressed.
    /// That is, reflexivity proofs are suppressed to save space.
    PR_MONOTONICITY = generated::Z3_decl_kind::Z3_OP_PR_MONOTONICITY as u32,
    /// Given a proof for `(~ p q)`, produces a proof for
    /// `(~ (forall (x) p) (forall (x) q))`.
    ///
    /// ```text
    /// T1: (~ p q)
    /// [quant-intro T1]: (~ (forall (x) p) (forall (x) q))
    /// ```
    PR_QUANT_INTRO = generated::Z3_decl_kind::Z3_OP_PR_QUANT_INTRO as u32,

    /// Given a proof `p`, produces a proof of `lambda x . p`, where `x` are free
    /// variables in `p`.
    ///
    /// ```text
    /// T1: f
    /// [proof-bind T1] forall (x) f
    /// ```
    PR_BIND = generated::Z3_decl_kind::Z3_OP_PR_BIND as u32,
    /// Distributivity proof object.
    ///
    /// Given that `f (= or)` distributes over `g (= and)`, produces a proof for
    ///
    /// ```text
    /// (= (f a (g c d))
    /// (g (f a c) (f a d)))
    /// ```
    ///
    /// If `f` and `g` are associative, this proof also justifies the following equality:
    ///
    /// ```text
    /// (= (f (g a b) (g c d))
    /// (g (f a c) (f a d) (f b c) (f b d)))
    /// ```
    ///
    /// where each `f` and `g` can have arbitrary number of arguments.
    ///
    /// This proof object has no antecedents.
    ///
    /// Remark: This rule is used by the CNF conversion pass and
    /// instantiated by `f = or`, and `g = and`.
    PR_DISTRIBUTIVITY = generated::Z3_decl_kind::Z3_OP_PR_DISTRIBUTIVITY as u32,
    /// Given a proof for `(and l_1 ... l_n)`, produces a proof
    /// for `l_i`.
    ///
    /// ```text
    /// T1: (and l_1 ... l_n)
    /// [and-elim T1]: l_i
    /// ```
    PR_AND_ELIM = generated::Z3_decl_kind::Z3_OP_PR_AND_ELIM as u32,
    /// Given a proof for `(not (or l_1 ... l_n))`, produces a
    /// proof for `(not l_i)`.
    ///
    /// ```text
    /// T1: (not (or l_1 ... l_n))
    /// [not-or-elim T1]: (not l_i)
    /// ```
    PR_NOT_OR_ELIM = generated::Z3_decl_kind::Z3_OP_PR_NOT_OR_ELIM as u32,
    /// A proof for a local rewriting step `(= t s)`.
    ///
    /// The head function symbol of `t` is interpreted.
    ///
    /// This proof object has no antecedents.
    ///
    /// The conclusion of a rewrite rule is either an equality `(= t s)`,
    /// an equivalence `(iff t s)`, or equi-satisfiability `(~ t s)`.
    ///
    /// Remark: if `f` is `bool`, then `=` is `iff`.
    ///
    /// Examples:
    ///
    /// ```text
    /// (= (+ x 0) x)
    /// (= (+ x 1 2) (+ 3 x))
    /// (iff (or x false) x)
    /// ```
    PR_REWRITE = generated::Z3_decl_kind::Z3_OP_PR_REWRITE as u32,
    /// A proof for rewriting an expression `t` into an expression `s`.
    ///
    /// This proof object can have `n` antecedents. The antecedents are
    /// proofs for equalities used as substitution rules.
    ///
    /// The object is also used in a few cases. The cases are:
    ///
    /// - When applying contextual simplification `(CONTEXT_SIMPLIFIER=true)`.
    /// - When converting bit-vectors to Booleans `(BIT2BOOL=true)`.
    PR_REWRITE_STAR = generated::Z3_decl_kind::Z3_OP_PR_REWRITE_STAR as u32,
    /// A proof for `(iff (f (forall (x) q(x)) r) (forall (x) (f (q x) r)))`.
    ///
    /// This proof object has no antecedents.
    PR_PULL_QUANT = generated::Z3_decl_kind::Z3_OP_PR_PULL_QUANT as u32,
    /// A proof for:
    ///
    /// ```text
    /// (iff (forall (x_1 ... x_m) (and p_1[x_1 ... x_m] ... p_n[x_1 ... x_m]))
    /// (and (forall (x_1 ... x_m) p_1[x_1 ... x_m])
    /// ...
    /// (forall (x_1 ... x_m) p_n[x_1 ... x_m])))
    /// ```
    ///
    /// This proof object has no antecedents.
    PR_PUSH_QUANT = generated::Z3_decl_kind::Z3_OP_PR_PUSH_QUANT as u32,
    /// A proof for
    ///
    /// ```text
    /// (iff (forall (x_1 ... x_n y_1 ... y_m) p[x_1 ... x_n])
    /// (forall (x_1 ... x_n) p[x_1 ... x_n]))
    /// ```
    ///
    /// It is used to justify the elimination of unused variables.
    ///
    /// This proof object has no antecedents.
    PR_ELIM_UNUSED_VARS = generated::Z3_decl_kind::Z3_OP_PR_ELIM_UNUSED_VARS as u32,
    /// A proof for destructive equality resolution:
    ///
    /// ```text
    /// (iff (forall (x) (or (not (= x t)) P[x])) P[t])
    /// ```
    ///
    /// if `x` does not occur in `t`.
    ///
    /// This proof object has no antecedents.
    ///
    /// Several variables can be eliminated simultaneously.
    PR_DER = generated::Z3_decl_kind::Z3_OP_PR_DER as u32,
    /// A proof of `(or (not (forall (x) (P x))) (P a))`.
    PR_QUANT_INST = generated::Z3_decl_kind::Z3_OP_PR_QUANT_INST as u32,
    /// Mark a hypothesis in a natural deduction style proof.
    PR_HYPOTHESIS = generated::Z3_decl_kind::Z3_OP_PR_HYPOTHESIS as u32,
    /// ```text
    /// T1: false
    /// [lemma T1]: (or (not l_1) ... (not l_n))
    /// ```
    ///
    /// This proof object has one antecedent: a hypothetical proof for false.
    ///
    /// It converts the proof in a proof for `(or (not l_1) ... (not l_n))`,
    /// when `T1` contains the open hypotheses: `l_1, ..., l_n`.
    ///
    /// The hypotheses are closed after an application of a lemma.
    ///
    /// Furthermore, there are no other open hypotheses in the subtree covered by
    /// the lemma.
    PR_LEMMA = generated::Z3_decl_kind::Z3_OP_PR_LEMMA as u32,
    /// ```text
    /// T1:      (or l_1 ... l_n l_1' ... l_m')
    /// T2:      (not l_1)
    /// ...
    /// T(n+1):  (not l_n)
    /// [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m')
    /// ```
    PR_UNIT_RESOLUTION = generated::Z3_decl_kind::Z3_OP_PR_UNIT_RESOLUTION as u32,
    /// ```text
    /// T1: p
    /// [iff-true T1]: (iff p true)
    /// ```
    PR_IFF_TRUE = generated::Z3_decl_kind::Z3_OP_PR_IFF_TRUE as u32,
    /// ```text
    /// T1: (not p)
    /// [iff-false T1]: (iff p false)
    /// ```
    PR_IFF_FALSE = generated::Z3_decl_kind::Z3_OP_PR_IFF_FALSE as u32,
    /// ```text
    /// [comm]: (= (f a b) (f b a))
    /// ```
    ///
    /// `f` is a commutative operator.
    ///
    /// This proof object has no antecedents.
    ///
    /// Remark: if `f` is `bool`, then `=` is `iff`.
    PR_COMMUTATIVITY = generated::Z3_decl_kind::Z3_OP_PR_COMMUTATIVITY as u32,
    /// Proof object used to justify Tseitin's like axioms:
    ///
    /// ```text
    /// (or (not (and p q)) p)
    /// (or (not (and p q)) q)
    /// (or (not (and p q r)) p)
    /// (or (not (and p q r)) q)
    /// (or (not (and p q r)) r)
    /// ...
    /// (or (and p q) (not p) (not q))
    /// (or (not (or p q)) p q)
    /// (or (or p q) (not p))
    /// (or (or p q) (not q))
    /// (or (not (iff p q)) (not p) q)
    /// (or (not (iff p q)) p (not q))
    /// (or (iff p q) (not p) (not q))
    /// (or (iff p q) p q)
    /// (or (not (ite a b c)) (not a) b)
    /// (or (not (ite a b c)) a c)
    /// (or (ite a b c) (not a) (not b))
    /// (or (ite a b c) a (not c))
    /// (or (not (not a)) (not a))
    /// (or (not a) a)
    /// ```
    ///
    /// This proof object has no antecedents.
    ///
    /// Note: all axioms are propositional tautologies.
    /// Note also that `and` and `or` can take multiple arguments.
    /// You can recover the propositional tautologies by
    /// unfolding the Boolean connectives in the axioms a small
    /// bounded number of steps `(=3)`.
    PR_DEF_AXIOM = generated::Z3_decl_kind::Z3_OP_PR_DEF_AXIOM as u32,
    /// Introduces a name for a formula/term.
    ///
    /// Suppose `e` is an expression with free variables `x`, and
    /// `def-intro` introduces the name `n(x)`. The possible cases are:
    ///
    /// When e is of Boolean type:
    ///
    /// ```text
    /// [def-intro]: (and (or n (not e)) (or (not n) e))
    /// ```
    ///
    /// or:
    ///
    /// ```text
    /// [def-intro]: (or (not n) e)
    /// ```
    ///
    /// when e only occurs positively.
    ///
    /// When e is of the form `(ite cond th el)`:
    ///
    /// ```text
    /// [def-intro]: (and (or (not cond) (= n th)) (or cond (= n el)))
    /// ```
    ///
    /// Otherwise:
    ///
    /// ```text
    /// [def-intro]: (= n e)
    /// ```
    PR_DEF_INTRO = generated::Z3_decl_kind::Z3_OP_PR_DEF_INTRO as u32,
    /// ```text
    /// [apply-def T1]: F ~ n
    /// ```
    ///
    /// `F` is 'equivalent' to `n`, given that `T1` is a proof that
    /// `n` is a name for `F`.
    PR_APPLY_DEF = generated::Z3_decl_kind::Z3_OP_PR_APPLY_DEF as u32,
    /// ```text
    /// T1: (iff p q)
    /// [iff~ T1]: (~ p q)
    /// ```
    PR_IFF_OEQ = generated::Z3_decl_kind::Z3_OP_PR_IFF_OEQ as u32,
    /// Proof for a (positive) NNF step. Example:
    ///
    /// ```text
    /// T1: (not s_1) ~ r_1
    /// T2: (not s_2) ~ r_2
    /// T3: s_1 ~ r_1'
    /// T4: s_2 ~ r_2'
    /// [nnf-pos T1 T2 T3 T4]: (~ (iff s_1 s_2)
    /// (and (or r_1 r_2') (or r_1' r_2)))
    /// ```
    ///
    /// The negation normal form steps `NNF_POS` and `NNF_NEG` are used in the
    /// following cases:
    ///
    /// - When creating the NNF of a positive force quantifier.
    ///   The quantifier is retained (unless the bound variables are eliminated).
    ///   Example:
    ///   ```text
    ///   T1: q ~ q_new
    ///   [nnf-pos T1]: (~ (forall (x T) q) (forall (x T) q_new))
    ///   ```
    /// - When recursively creating NNF over Boolean formulas, where the top-level
    ///   connective is changed during NNF conversion. The relevant Boolean connectives
    ///   for `NNF_POS` are `implies`, `iff`, `xor`, `ite`.
    ///   `NNF_NEG` furthermore handles the case where negation is pushed
    ///   over Boolean connectives `and` and `or`.
    PR_NNF_POS = generated::Z3_decl_kind::Z3_OP_PR_NNF_POS as u32,
    /// Proof for a (negative) NNF step. Examples:
    ///
    /// ```text
    /// T1: (not s_1) ~ r_1
    /// ...
    /// Tn: (not s_n) ~ r_n
    /// [nnf-neg T1 ... Tn]: (not (and s_1 ... s_n)) ~ (or r_1 ... r_n)
    /// ```
    ///
    /// and
    ///
    /// ```text
    /// T1: (not s_1) ~ r_1
    /// ...
    /// Tn: (not s_n) ~ r_n
    /// [nnf-neg T1 ... Tn]: (not (or s_1 ... s_n)) ~ (and r_1 ... r_n)
    /// ```
    ///
    /// and
    ///
    /// ```text
    /// T1: (not s_1) ~ r_1
    /// T2: (not s_2) ~ r_2
    /// T3: s_1 ~ r_1'
    /// T4: s_2 ~ r_2'
    /// [nnf-neg T1 T2 T3 T4]: (~ (not (iff s_1 s_2))
    /// (and (or r_1 r_2) (or r_1' r_2')))
    /// ```
    PR_NNF_NEG = generated::Z3_decl_kind::Z3_OP_PR_NNF_NEG as u32,
    /// Proof for:
    ///
    /// ```text
    /// [sk]: (~ (not (forall x (p x y))) (not (p (sk y) y)))
    /// [sk]: (~ (exists x (p x y)) (p (sk y) y))
    /// ```
    ///
    /// This proof object has no antecedents.
    PR_SKOLEMIZE = generated::Z3_decl_kind::Z3_OP_PR_SKOLEMIZE as u32,
    /// Modus ponens style rule for equi-satisfiability.
    ///
    /// ```text
    /// T1: p
    /// T2: (~ p q)
    /// [mp~ T1 T2]: q
    /// ```
    PR_MODUS_PONENS_OEQ = generated::Z3_decl_kind::Z3_OP_PR_MODUS_PONENS_OEQ as u32,
    /// Generic proof for theory lemmas.
    ///
    /// The theory lemma function comes with one or more parameters.
    ///
    /// The first parameter indicates the name of the theory.
    ///
    /// For the theory of arithmetic, additional parameters provide hints for
    /// checking the theory lemma.
    ///
    /// The hints for arithmetic are:
    ///
    /// - `farkas` - followed by rational coefficients. Multiply the coefficients to the
    ///   inequalities in the lemma, add the (negated) inequalities and obtain a contradiction.
    /// - `triangle-eq` - Indicates a lemma related to the equivalence:
    ///   ```text
    ///   (iff (= t1 t2) (and (<= t1 t2) (<= t2 t1)))
    ///   ```
    /// - `gcd-test` - Indicates an integer linear arithmetic lemma that uses a gcd test.
    PR_TH_LEMMA = generated::Z3_decl_kind::Z3_OP_PR_TH_LEMMA as u32,
    /// Hyper-resolution rule.
    ///
    /// The premises of the rules is a sequence of clauses.
    /// The first clause argument is the main clause of the rule.
    /// with a literal from the first (main) clause.
    ///
    /// Premises of the rules are of the form
    ///
    /// ```text
    /// (or l0 l1 l2 .. ln)
    /// ```
    ///
    /// or
    ///
    /// ```text
    /// (=> (and l1 l2 .. ln) l0)
    /// ```
    ///
    /// or in the most general (ground) form:
    ///
    /// ```text
    /// (=> (and ln+1 ln+2 .. ln+m) (or l0 l1 .. ln))
    /// ```
    ///
    /// In other words we use the following (Prolog style) convention for Horn
    /// implications:
    ///
    /// - the head of a Horn implication is position 0,
    /// - the first conjunct in the body of an implication is position 1
    /// - the second conjunct in the body of an implication is position 2
    ///
    /// For general implications where the head is a disjunction, the
    /// first n positions correspond to the n disjuncts in the head.
    /// The next m positions correspond to the m conjuncts in the body.
    ///
    /// The premises can be universally quantified so that the most
    /// general non-ground form is:
    ///
    /// ```text
    /// (forall (vars) (=> (and ln+1 ln+2 .. ln+m) (or l0 l1 .. ln)))
    /// ```
    ///
    /// The hyper-resolution rule takes a sequence of parameters.
    /// The parameters are substitutions of bound variables separated by pairs
    /// of literal positions from the main clause and side clause.
    PR_HYPER_RESOLVE = generated::Z3_decl_kind::Z3_OP_PR_HYPER_RESOLVE as u32,
    /// Insert a record into a relation.
    ///
    /// The function takes `n`+1 arguments, where the first argument
    /// is the relation and the remaining `n` elements
    /// correspond to the `n` columns of the relation.
    RA_STORE = generated::Z3_decl_kind::Z3_OP_RA_STORE as u32,
    /// Creates the empty relation.
    RA_EMPTY = generated::Z3_decl_kind::Z3_OP_RA_EMPTY as u32,
    /// Tests if the relation is empty.
    RA_IS_EMPTY = generated::Z3_decl_kind::Z3_OP_RA_IS_EMPTY as u32,
    /// Create the relational join.
    RA_JOIN = generated::Z3_decl_kind::Z3_OP_RA_JOIN as u32,
    /// Create the union or convex hull of two relations.
    ///
    /// The function takes two arguments.
    RA_UNION = generated::Z3_decl_kind::Z3_OP_RA_UNION as u32,
    /// Widen two relations.
    ///
    /// The function takes two arguments.
    RA_WIDEN = generated::Z3_decl_kind::Z3_OP_RA_WIDEN as u32,
    /// Project the columns (provided as numbers in the parameters).
    ///
    /// The function takes one argument.
    RA_PROJECT = generated::Z3_decl_kind::Z3_OP_RA_PROJECT as u32,
    /// Filter (restrict) a relation with respect to a predicate.
    ///
    /// The first argument is a relation.
    ///
    /// The second argument is a predicate with free de-Bruijn indices
    /// corresponding to the columns of the relation.
    ///
    /// So the first column in the relation has index 0.
    RA_FILTER = generated::Z3_decl_kind::Z3_OP_RA_FILTER as u32,
    /// Intersect the first relation with respect to negation
    /// of the second relation (the function takes two arguments).
    ///
    /// Logically, the specification can be described by a function
    ///
    /// ```text
    /// target = filter_by_negation(pos, neg, columns)
    /// ```
    ///
    /// where columns are pairs `c1`, `d1`, ..,  `cN`, `dN` of columns
    /// from `pos` and `neg`, such that target are elements in `x` in `pos`,
    /// such that there is no `y` in `neg` that agrees with
    /// `x` on the columns `c1`, `d1`, .., `cN`, `dN`.
    RA_NEGATION_FILTER = generated::Z3_decl_kind::Z3_OP_RA_NEGATION_FILTER as u32,
    /// Rename columns in the relation.
    ///
    /// The function takes one argument.
    ///
    /// The parameters contain the renaming as a cycle.
    RA_RENAME = generated::Z3_decl_kind::Z3_OP_RA_RENAME as u32,
    /// Complement the relation.
    RA_COMPLEMENT = generated::Z3_decl_kind::Z3_OP_RA_COMPLEMENT as u32,
    /// Check if a record is an element of the relation.
    ///
    /// The function takes `n`+1 arguments, where the first argument is a relation,
    /// and the remaining `n` arguments correspond to a record.
    RA_SELECT = generated::Z3_decl_kind::Z3_OP_RA_SELECT as u32,
    /// Create a fresh copy (clone) of a relation.
    ///
    /// The function is logically the identity, but
    /// in the context of a register machine allows
    /// for [`DeclKind::RA_UNION`]
    /// to perform destructive updates to the first argument.
    RA_CLONE = generated::Z3_decl_kind::Z3_OP_RA_CLONE as u32,
    FD_CONSTANT = generated::Z3_decl_kind::Z3_OP_FD_CONSTANT as u32,
    /// A less than predicate over the finite domain `SortKind::FiniteDomain`.
    FD_LT = generated::Z3_decl_kind::Z3_OP_FD_LT as u32,
    SEQ_UNIT = generated::Z3_decl_kind::Z3_OP_SEQ_UNIT as u32,
    SEQ_EMPTY = generated::Z3_decl_kind::Z3_OP_SEQ_EMPTY as u32,
    SEQ_CONCAT = generated::Z3_decl_kind::Z3_OP_SEQ_CONCAT as u32,
    SEQ_PREFIX = generated::Z3_decl_kind::Z3_OP_SEQ_PREFIX as u32,
    SEQ_SUFFIX = generated::Z3_decl_kind::Z3_OP_SEQ_SUFFIX as u32,
    SEQ_CONTAINS = generated::Z3_decl_kind::Z3_OP_SEQ_CONTAINS as u32,
    SEQ_EXTRACT = generated::Z3_decl_kind::Z3_OP_SEQ_EXTRACT as u32,
    SEQ_REPLACE = generated::Z3_decl_kind::Z3_OP_SEQ_REPLACE as u32,
    SEQ_AT = generated::Z3_decl_kind::Z3_OP_SEQ_AT as u32,
    SEQ_LENGTH = generated::Z3_decl_kind::Z3_OP_SEQ_LENGTH as u32,
    SEQ_INDEX = generated::Z3_decl_kind::Z3_OP_SEQ_INDEX as u32,
    SEQ_TO_RE = generated::Z3_decl_kind::Z3_OP_SEQ_TO_RE as u32,
    SEQ_IN_RE = generated::Z3_decl_kind::Z3_OP_SEQ_IN_RE as u32,
    STR_TO_INT = generated::Z3_decl_kind::Z3_OP_STR_TO_INT as u32,
    INT_TO_STR = generated::Z3_decl_kind::Z3_OP_INT_TO_STR as u32,
    RE_PLUS = generated::Z3_decl_kind::Z3_OP_RE_PLUS as u32,
    RE_STAR = generated::Z3_decl_kind::Z3_OP_RE_STAR as u32,
    RE_OPTION = generated::Z3_decl_kind::Z3_OP_RE_OPTION as u32,
    RE_CONCAT = generated::Z3_decl_kind::Z3_OP_RE_CONCAT as u32,
    RE_UNION = generated::Z3_decl_kind::Z3_OP_RE_UNION as u32,
    RE_RANGE = generated::Z3_decl_kind::Z3_OP_RE_RANGE as u32,
    RE_LOOP = generated::Z3_decl_kind::Z3_OP_RE_LOOP as u32,
    RE_INTERSECT = generated::Z3_decl_kind::Z3_OP_RE_INTERSECT as u32,
    RE_EMPTY_SET = generated::Z3_decl_kind::Z3_OP_RE_EMPTY_SET as u32,
    RE_FULL_SET = generated::Z3_decl_kind::Z3_OP_RE_FULL_SET as u32,
    RE_COMPLEMENT = generated::Z3_decl_kind::Z3_OP_RE_COMPLEMENT as u32,
    /// A label (used by the Boogie Verification condition generator).
    ///
    /// The label has two parameters, a string and a Boolean polarity.
    ///
    /// It takes one argument, a formula.
    LABEL = generated::Z3_decl_kind::Z3_OP_LABEL as u32,
    /// A label literal (used by the Boogie Verification condition generator).
    ///
    /// A label literal has a set of string parameters. It takes no arguments.
    LABEL_LIT = generated::Z3_decl_kind::Z3_OP_LABEL_LIT as u32,
    /// Datatype constructor.
    DT_CONSTRUCTOR = generated::Z3_decl_kind::Z3_OP_DT_CONSTRUCTOR as u32,
    /// Datatype recognizer.
    DT_RECOGNISER = generated::Z3_decl_kind::Z3_OP_DT_RECOGNISER as u32,
    /// Datatype recognizer.
    DT_IS = generated::Z3_decl_kind::Z3_OP_DT_IS as u32,
    /// Datatype accessor.
    DT_ACCESSOR = generated::Z3_decl_kind::Z3_OP_DT_ACCESSOR as u32,
    /// Datatype field update.
    DT_UPDATE_FIELD = generated::Z3_decl_kind::Z3_OP_DT_UPDATE_FIELD as u32,
    /// Cardinality constraint.
    ///
    /// Example: `x + y + z <= 2`
    PB_AT_MOST = generated::Z3_decl_kind::Z3_OP_PB_AT_MOST as u32,
    /// Cardinality constraint.
    ///
    /// Example: `x + y + z >= 2`
    PB_AT_LEAST = generated::Z3_decl_kind::Z3_OP_PB_AT_LEAST as u32,
    /// Generalized Pseudo-Boolean cardinality constraint.
    ///
    /// Example: `2*x + 3*y <= 4`
    PB_LE = generated::Z3_decl_kind::Z3_OP_PB_LE as u32,
    /// Generalized Pseudo-Boolean cardinality constraint.
    ///
    /// Example: `2*x + 3*y + 2*z >= 4`
    PB_GE = generated::Z3_decl_kind::Z3_OP_PB_GE as u32,
    /// Generalized Pseudo-Boolean equality constraint.
    ///
    /// Example: `2*x + 1*y + 2*z + 1*u = 4`
    PB_EQ = generated::Z3_decl_kind::Z3_OP_PB_EQ as u32,
    /// Floating-point rounding mode RNE
    FPA_RM_NEAREST_TIES_TO_EVEN = generated::Z3_decl_kind::Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN as u32,
    /// Floating-point rounding mode RNA
    FPA_RM_NEAREST_TIES_TO_AWAY = generated::Z3_decl_kind::Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY as u32,
    /// Floating-point rounding mode RTP
    FPA_RM_TOWARD_POSITIVE = generated::Z3_decl_kind::Z3_OP_FPA_RM_TOWARD_POSITIVE as u32,
    /// Floating-point rounding mode RTN
    FPA_RM_TOWARD_NEGATIVE = generated::Z3_decl_kind::Z3_OP_FPA_RM_TOWARD_NEGATIVE as u32,
    /// Floating-point rounding mode RTZ
    FPA_RM_TOWARD_ZERO = generated::Z3_decl_kind::Z3_OP_FPA_RM_TOWARD_ZERO as u32,
    /// Floating-point value
    FPA_NUM = generated::Z3_decl_kind::Z3_OP_FPA_NUM as u32,
    /// Floating-point +oo
    FPA_PLUS_INF = generated::Z3_decl_kind::Z3_OP_FPA_PLUS_INF as u32,
    /// Floating-point -oo
    FPA_MINUS_INF = generated::Z3_decl_kind::Z3_OP_FPA_MINUS_INF as u32,
    /// Floating-point NaN
    FPA_NAN = generated::Z3_decl_kind::Z3_OP_FPA_NAN as u32,
    /// Floating-point +zero
    FPA_PLUS_ZERO = generated::Z3_decl_kind::Z3_OP_FPA_PLUS_ZERO as u32,
    /// Floating-point -zero
    FPA_MINUS_ZERO = generated::Z3_decl_kind::Z3_OP_FPA_MINUS_ZERO as u32,
    /// Floating-point addition
    FPA_ADD = generated::Z3_decl_kind::Z3_OP_FPA_ADD as u32,
    /// Floating-point subtraction
    FPA_SUB = generated::Z3_decl_kind::Z3_OP_FPA_SUB as u32,
    /// Floating-point negation
    FPA_NEG = generated::Z3_decl_kind::Z3_OP_FPA_NEG as u32,
    /// Floating-point multiplication
    FPA_MUL = generated::Z3_decl_kind::Z3_OP_FPA_MUL as u32,
    /// Floating-point division
    FPA_DIV = generated::Z3_decl_kind::Z3_OP_FPA_DIV as u32,
    /// Floating-point remainder
    FPA_REM = generated::Z3_decl_kind::Z3_OP_FPA_REM as u32,
    /// Floating-point absolute value
    FPA_ABS = generated::Z3_decl_kind::Z3_OP_FPA_ABS as u32,
    /// Floating-point minimum
    FPA_MIN = generated::Z3_decl_kind::Z3_OP_FPA_MIN as u32,
    /// Floating-point maximum
    FPA_MAX = generated::Z3_decl_kind::Z3_OP_FPA_MAX as u32,
    /// Floating-point fused multiply-add
    FPA_FMA = generated::Z3_decl_kind::Z3_OP_FPA_FMA as u32,
    /// Floating-point square root
    FPA_SQRT = generated::Z3_decl_kind::Z3_OP_FPA_SQRT as u32,
    /// Floating-point round to integral
    FPA_ROUND_TO_INTEGRAL = generated::Z3_decl_kind::Z3_OP_FPA_ROUND_TO_INTEGRAL as u32,
    /// Floating-point equality
    FPA_EQ = generated::Z3_decl_kind::Z3_OP_FPA_EQ as u32,
    /// Floating-point less than
    FPA_LT = generated::Z3_decl_kind::Z3_OP_FPA_LT as u32,
    /// Floating-point greater than
    FPA_GT = generated::Z3_decl_kind::Z3_OP_FPA_GT as u32,
    /// Floating-point less than or equal
    FPA_LE = generated::Z3_decl_kind::Z3_OP_FPA_LE as u32,
    /// Floating-point greater than or equal
    FPA_GE = generated::Z3_decl_kind::Z3_OP_FPA_GE as u32,
    /// Floating-point isNaN
    FPA_IS_NAN = generated::Z3_decl_kind::Z3_OP_FPA_IS_NAN as u32,
    /// Floating-point isInfinite
    FPA_IS_INF = generated::Z3_decl_kind::Z3_OP_FPA_IS_INF as u32,
    /// Floating-point isZero
    FPA_IS_ZERO = generated::Z3_decl_kind::Z3_OP_FPA_IS_ZERO as u32,
    /// Floating-point isNormal
    FPA_IS_NORMAL = generated::Z3_decl_kind::Z3_OP_FPA_IS_NORMAL as u32,
    /// Floating-point isSubnormal
    FPA_IS_SUBNORMAL = generated::Z3_decl_kind::Z3_OP_FPA_IS_SUBNORMAL as u32,
    /// Floating-point isNegative
    FPA_IS_NEGATIVE = generated::Z3_decl_kind::Z3_OP_FPA_IS_NEGATIVE as u32,
    /// Floating-point isPositive
    FPA_IS_POSITIVE = generated::Z3_decl_kind::Z3_OP_FPA_IS_POSITIVE as u32,
    /// Floating-point constructor from 3 bit-vectors
    FPA_FP = generated::Z3_decl_kind::Z3_OP_FPA_FP as u32,
    /// Floating-point conversion (various)
    FPA_TO_FP = generated::Z3_decl_kind::Z3_OP_FPA_TO_FP as u32,
    /// Floating-point conversion from unsigned bit-vector
    FPA_TO_FP_UNSIGNED = generated::Z3_decl_kind::Z3_OP_FPA_TO_FP_UNSIGNED as u32,
    /// Floating-point conversion to unsigned bit-vector
    FPA_TO_UBV = generated::Z3_decl_kind::Z3_OP_FPA_TO_UBV as u32,
    /// Floating-point conversion to signed bit-vector
    FPA_TO_SBV = generated::Z3_decl_kind::Z3_OP_FPA_TO_SBV as u32,
    /// Floating-point conversion to real number
    FPA_TO_REAL = generated::Z3_decl_kind::Z3_OP_FPA_TO_REAL as u32,
    /// Floating-point conversion to IEEE-754 bit-vector
    FPA_TO_IEEE_BV = generated::Z3_decl_kind::Z3_OP_FPA_TO_IEEE_BV as u32,
    /// Implicitly) represents the internal bitvector-representation
    /// of a floating-point term (used for the lazy encoding
    /// of non-relevant terms in `theory_fpa`)
    FPA_BVWRAP = generated::Z3_decl_kind::Z3_OP_FPA_BVWRAP as u32,
    /// Conversion of a 3-bit bit-vector term to a
    /// floating-point rounding-mode term.
    ///
    /// The conversion uses the following values:
    ///
    /// 0 = 000 = `DeclKind::FPA_RM_NEAREST_TIES_TO_EVEN`,
    /// 1 = 001 = `DeclKind::FPA_RM_NEAREST_TIES_TO_AWAY`,
    /// 2 = 010 = `DeclKind::FPA_RM_TOWARD_POSITIVE`,
    /// 3 = 011 = `DeclKind::FPA_RM_TOWARD_NEGATIVE`,
    /// 4 = 100 = `DeclKind::FPA_RM_TOWARD_ZERO`.
    FPA_BV2RM = generated::Z3_decl_kind::Z3_OP_FPA_BV2RM as u32,
    /// Internal (often interpreted) symbol, but no additional
    /// information is exposed. Tools may use the string
    /// representation of the function declaration to obtain
    /// more information.
    INTERNAL = generated::Z3_decl_kind::Z3_OP_INTERNAL as u32,
    /// Kind used for uninterpreted symbols.
    UNINTERPRETED = generated::Z3_decl_kind::Z3_OP_UNINTERPRETED as u32,
}

/// The different kinds of parameters that can be associated with parameter sets.
/// (see [`Z3_mk_params`]).
///
/// This corresponds to `Z3_param_kind` in the C API.
#[repr(u32)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ParamKind {
    /// integer parameters.
    ///
    /// This corresponds to `Z3_PK_UINT` in the C API.
    UInt = generated::Z3_param_kind::Z3_PK_UINT as u32,
    /// boolean parameters.
    ///
    /// This corresponds to `Z3_PK_BOOL` in the C API.
    Bool = generated::Z3_param_kind::Z3_PK_BOOL as u32,
    /// double parameters.
    ///
    /// This corresponds to `Z3_PK_DOUBLE` in the C API.
    Double = generated::Z3_param_kind::Z3_PK_DOUBLE as u32,
    /// symbol parameters.
    ///
    /// This corresponds to `Z3_PK_SYMBOL` in the C API.
    Symbol = generated::Z3_param_kind::Z3_PK_SYMBOL as u32,
    /// string parameters.
    ///
    /// This corresponds to `Z3_PK_STRING` in the C API.
    String = generated::Z3_param_kind::Z3_PK_STRING as u32,
    /// all internal parameter kinds which are not exposed in the API.
    ///
    /// This corresponds to `Z3_PK_OTHER` in the C API.
    Other = generated::Z3_param_kind::Z3_PK_OTHER as u32,
    /// invalid parameter.
    ///
    /// This corresponds to `Z3_PK_INVALID` in the C API.
    Invalid = generated::Z3_param_kind::Z3_PK_INVALID as u32,
}

/// Z3 pretty printing modes (See [`Z3_set_ast_print_mode`]).
///
/// This corresponds to `Z3_ast_print_mode` in the C API.
#[repr(u32)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum AstPrintMode {
    /// Print AST nodes in SMTLIB verbose format.
    ///
    /// This corresponds to `Z3_PRINT_SMTLIB_FULL` in the C API.
    SmtLibFull = generated::Z3_ast_print_mode::Z3_PRINT_SMTLIB_FULL as u32,
    /// Print AST nodes using a low-level format.
    ///
    /// This corresponds to `Z3_PRINT_LOW_LEVEL` in the C API.
    LowLevel = generated::Z3_ast_print_mode::Z3_PRINT_LOW_LEVEL as u32,
    /// Print AST nodes in SMTLIB 2.x compliant format.
    ///
    /// This corresponds to `Z3_PRINT_SMTLIB2_COMPLIANT` in the C API.
    SmtLib2Compliant = generated::Z3_ast_print_mode::Z3_PRINT_SMTLIB2_COMPLIANT as u32,
}

/// Z3 error codes (See [`Z3_get_error_code`]).
///
/// This corresponds to `Z3_error_code` in the C API.
#[repr(u32)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ErrorCode {
    /// No error.
    ///
    /// This corresponds to `Z3_OK` in the C API.
    OK = generated::Z3_error_code::Z3_OK as u32,
    /// User tried to build an invalid (type incorrect) AST.
    ///
    /// This corresponds to `Z3_SORT_ERROR` in the C API.
    SortError = generated::Z3_error_code::Z3_SORT_ERROR as u32,
    /// Index out of bounds.
    ///
    /// This corresponds to `Z3_IOB` in the C API.
    IOB = generated::Z3_error_code::Z3_IOB as u32,
    /// Invalid argument was provided.
    ///
    /// This corresponds to `Z3_INVALID_ARG` in the C API.
    InvalidArg = generated::Z3_error_code::Z3_INVALID_ARG as u32,
    /// An error occurred when parsing a string or file.
    ///
    /// This corresponds to `Z3_PARSER_ERROR` in the C API.
    ParserError = generated::Z3_error_code::Z3_PARSER_ERROR as u32,
    /// Parser output is not available, that is, user didn't invoke
    /// [`Z3_parse_smtlib2_string`] or [`Z3_parse_smtlib2_file`].
    ///
    /// This corresponds to `Z3_NO_PARSER` in the C API.
    NoParser = generated::Z3_error_code::Z3_NO_PARSER as u32,
    /// Invalid pattern was used to build a quantifier.
    ///
    /// This corresponds to `Z3_INVALID_PATTERN` in the C API.
    InvalidPattern = generated::Z3_error_code::Z3_INVALID_PATTERN as u32,
    /// A memory allocation failure was encountered.
    ///
    /// This corresponds to `Z3_MEMOUT_FAIL` in the C API.
    MemoutFail = generated::Z3_error_code::Z3_MEMOUT_FAIL as u32,
    /// A file could not be accessed.
    ///
    /// This corresponds to `Z3_FILE_ACCESS_ERROR` in the C API.
    FileAccessError = generated::Z3_error_code::Z3_FILE_ACCESS_ERROR as u32,
    /// An error internal to Z3 occurred.
    ///
    /// This corresponds to `Z3_INTERNAL_FATAL` in the C API.
    InternalFatal = generated::Z3_error_code::Z3_INTERNAL_FATAL as u32,
    /// API call is invalid in the current state.
    ///
    /// This corresponds to `Z3_INVALID_USAGE` in the C API.
    InvalidUsage = generated::Z3_error_code::Z3_INVALID_USAGE as u32,
    /// Trying to decrement the reference counter of an AST that was
    /// deleted or the reference counter was not initialized with
    /// [`Z3_inc_ref`].
    ///
    /// This corresponds to `Z3_DEC_REF_ERROR` in the C API.
    DecRefError = generated::Z3_error_code::Z3_DEC_REF_ERROR as u32,
    /// Internal Z3 exception. Additional details can be retrieved
    /// using [`Z3_get_error_msg`].
    ///
    /// This corresponds to `Z3_EXCEPTION` in the C API.
    Exception = generated::Z3_error_code::Z3_EXCEPTION as u32,
}

/// Precision of a given goal. Some goals can be transformed using over/under approximations.
///
/// This corresponds to `Z3_goal_prec` in the C API.
#[repr(u32)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum GoalPrec {
    /// Approximations/Relaxations were not applied on the goal
    /// (sat and unsat answers were preserved).
    ///
    /// This corresponds to `Z3_GOAL_PRECISE` in the C API.
    Precise = generated::Z3_goal_prec::Z3_GOAL_PRECISE as u32,
    /// Goal is the product of a under-approximation (sat answers are preserved).
    ///
    /// This corresponds to `Z3_GOAL_UNDER` in the C API.
    Under = generated::Z3_goal_prec::Z3_GOAL_UNDER as u32,
    /// Goal is the product of an over-approximation (unsat answers are preserved).
    ///
    /// This corresponds to `Z3_GOAL_OVER` in the C API.
    Over = generated::Z3_goal_prec::Z3_GOAL_OVER as u32,
    /// Goal is garbage (it is the product of over- and under-approximations,
    /// sat and unsat answers are not preserved).
    ///
    /// This corresponds to `Z3_GOAL_UNDER_OVER` in the C API.
    UnderOver = generated::Z3_goal_prec::Z3_GOAL_UNDER_OVER as u32,
}

impl From<generated::Z3_sort_kind> for SortKind {
    fn from(raw: generated::Z3_sort_kind) -> Self {
        // Safety: SortKind covers all Z3_sort_kind discriminants (same #[repr(u32)] values).
        unsafe { core::mem::transmute(raw) }
    }
}

impl From<generated::Z3_ast_kind> for AstKind {
    fn from(raw: generated::Z3_ast_kind) -> Self {
        // Safety: AstKind covers all Z3_ast_kind discriminants (same #[repr(u32)] values).
        unsafe { core::mem::transmute(raw) }
    }
}

impl From<generated::Z3_decl_kind> for DeclKind {
    fn from(raw: generated::Z3_decl_kind) -> Self {
        // Safety: Both enums are #[repr(u32)] with matching discriminants for all DeclKind
        // variants. Z3 only returns values from this set for the contexts DeclKind is used.
        unsafe { core::mem::transmute(raw) }
    }
}

impl From<generated::Z3_symbol_kind> for SymbolKind {
    fn from(raw: generated::Z3_symbol_kind) -> Self {
        // Safety: SymbolKind covers all Z3_symbol_kind discriminants (same #[repr(u32)] values).
        unsafe { core::mem::transmute(raw) }
    }
}

impl From<generated::Z3_goal_prec> for GoalPrec {
    fn from(raw: generated::Z3_goal_prec) -> Self {
        // Safety: GoalPrec covers all Z3_goal_prec discriminants (same #[repr(u32)] values).
        unsafe { core::mem::transmute(raw) }
    }
}
