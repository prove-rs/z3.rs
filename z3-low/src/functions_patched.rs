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
#[inline]
#[expect(non_snake_case)]
#[expect(clippy::missing_safety_doc)]
#[allow(clippy::too_many_arguments)]
pub unsafe fn Z3_mk_constructor(
    c: Z3_context,
    name: Z3_symbol,
    recognizer: Z3_symbol,
    num_fields: ::core::ffi::c_uint,
    field_names: *const Z3_symbol,
    sorts: *const Option<Z3_sort>,
    sort_refs: *mut ::core::ffi::c_uint,
) -> Result<Z3_constructor, Z3Error> {
    unsafe {
        Z3_set_error(c, ErrorCode::Ok);
    };
    let ret = unsafe {
        ::z3_sys::Z3_mk_constructor(
            c,
            name,
            recognizer,
            num_fields,
            field_names,
            sorts,
            sort_refs,
        )
    };
    unsafe {
        let err = Z3_get_error_code(c);
        if err != ErrorCode::Ok {
            return Err(Z3Error::new(c, err));
        }
    };
    Ok(ret.unwrap())
}

/// Add a universal Horn clause as a named rule.
/// The `horn_rule` should be of the form:
///
/// ```text
/// horn_rule ::= (forall (bound-vars) horn_rule)
/// |  (=> atoms horn_rule)
/// |  atom
/// ```
#[inline]
#[expect(non_snake_case)]
#[expect(clippy::missing_safety_doc)]
#[allow(clippy::too_many_arguments)]
pub unsafe fn Z3_fixedpoint_add_rule(
    c: Z3_context,
    d: Z3_fixedpoint,
    rule: Z3_ast,
    name: Option<Z3_symbol>,
) -> Result<(), Z3Error> {
    unsafe {
        Z3_set_error(c, ErrorCode::Ok);
    };
    unsafe { ::z3_sys::Z3_fixedpoint_add_rule(c, d, rule, name) };
    unsafe {
        let err = Z3_get_error_code(c);
        if err != ErrorCode::Ok {
            return Err(Z3Error::new(c, err));
        }
    };
    Ok(())
}

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
#[inline]
#[expect(non_snake_case)]
#[expect(clippy::missing_safety_doc)]
#[allow(clippy::too_many_arguments)]
pub unsafe fn Z3_optimize_assert_soft(
    c: Z3_context,
    o: Z3_optimize,
    a: Z3_ast,
    weight: Z3_string,
    id: Option<Z3_symbol>,
) -> Result<::core::ffi::c_uint, Z3Error> {
    unsafe {
        Z3_set_error(c, ErrorCode::Ok);
    };
    let res = unsafe { ::z3_sys::Z3_optimize_assert_soft(c, o, a, weight, id) };
    unsafe {
        let err = Z3_get_error_code(c);
        if err != ErrorCode::Ok {
            return Err(Z3Error::new(c, err));
        }
    };
    Ok(res)
}
