// Hand-written declarations for functions with nullable parameters that require
// Option<T> in their signatures. These are excluded from the bindgen-generated
// functions.rs via blocklist_function in build.rs.

unsafe extern "C" {
    /// Create a constructor.
    ///
    /// - `c`: logical context.
    /// - `name`: constructor name.
    /// - `recognizer`: name of recognizer function.
    /// - `num_fields`: number of fields in constructor.
    /// - `field_names`: names of the constructor fields.
    /// - `sorts`: field sorts, `None` if the field sort refers to a recursive sort.
    /// - `sort_refs`: reference to datatype sort that is an argument to the constructor; if the
    ///   corresponding sort reference is 0, then the value in sort_refs should be an index
    ///   referring to one of the recursive datatypes that is declared.
    ///
    /// # See also
    ///
    /// - [`Z3_del_constructor`]
    /// - [`Z3_mk_constructor_list`]
    /// - [`Z3_query_constructor`]
    pub fn Z3_mk_constructor(
        c: Z3_context,
        name: Z3_symbol,
        recognizer: Z3_symbol,
        num_fields: ::core::ffi::c_uint,
        field_names: *const Z3_symbol,
        sorts: *const Option<Z3_sort>,
        sort_refs: *mut ::core::ffi::c_uint,
    ) -> Option<Z3_constructor>;

    /// Add a universal Horn clause as a named rule.
    /// The `horn_rule` should be of the form:
    ///
    /// ```text
    /// horn_rule ::= (forall (bound-vars) horn_rule)
    /// |  (=> atoms horn_rule)
    /// |  atom
    /// ```
    pub fn Z3_fixedpoint_add_rule(
        c: Z3_context,
        d: Z3_fixedpoint,
        rule: Z3_ast,
        name: Option<Z3_symbol>,
    );

    /// Assert soft constraint to the optimization context.
    ///
    /// - `c`: context
    /// - `o`: optimization context
    /// - `a`: formula
    /// - `weight`: a penalty for violating soft constraint. Negative weights convert into rewards.
    /// - `id`: optional identifier to group soft constraints
    ///
    /// # See also
    ///
    /// - [`Z3_optimize_assert`]
    /// - [`Z3_optimize_assert_and_track`]
    pub fn Z3_optimize_assert_soft(
        c: Z3_context,
        o: Z3_optimize,
        a: Z3_ast,
        weight: Z3_string,
        id: Option<Z3_symbol>,
    ) -> ::core::ffi::c_uint;
}
