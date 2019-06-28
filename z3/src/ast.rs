use std::cmp::{Eq, PartialEq};
use std::convert::{TryFrom, TryInto};
use std::ffi::{CStr, CString};
use std::fmt;
use std::hash::{Hash, Hasher};
use z3_sys::*;
use Context;
use Sort;
use Symbol;
use Z3_MUTEX;

/// [`Ast`](trait.Ast.html) node representing a boolean value.
pub struct Bool<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`](trait.Ast.html) node representing an integer value.
pub struct Int<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`](trait.Ast.html) node representing a real value.
pub struct Real<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`](trait.Ast.html) node representing a bitvector value.
pub struct BV<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`](trait.Ast.html) node representing an array value.
/// An array in Z3 is a mapping from indices to values.
pub struct Array<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`](trait.Ast.html) node representing a set value.
pub struct Set<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

// These `From` impls imply the corresponding `Into` impls
impl<'ctx> From<Bool<'ctx>> for Z3_ast {
    fn from(ast: Bool<'ctx>) -> Self {
        ast.z3_ast
    }
}

impl<'ctx> From<Int<'ctx>> for Z3_ast {
    fn from(ast: Int<'ctx>) -> Self {
        ast.z3_ast
    }
}

impl<'ctx> From<Real<'ctx>> for Z3_ast {
    fn from(ast: Real<'ctx>) -> Self {
        ast.z3_ast
    }
}

impl<'ctx> From<BV<'ctx>> for Z3_ast {
    fn from(ast: BV<'ctx>) -> Self {
        ast.z3_ast
    }
}

impl<'ctx> From<Array<'ctx>> for Z3_ast {
    fn from(ast: Array<'ctx>) -> Self {
        ast.z3_ast
    }
}

impl<'ctx> From<Set<'ctx>> for Z3_ast {
    fn from(ast: Set<'ctx>) -> Self {
        ast.z3_ast
    }
}

macro_rules! unop {
    ( $f:ident, $z3fn:ident, $retty:ty ) => {
        pub fn $f(&self) -> $retty {
            <$retty>::new(self.ctx, unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                $z3fn(self.ctx.z3_ctx, self.z3_ast)
            })
        }
    };
}

macro_rules! binop {
    ( $f:ident, $z3fn:ident, $retty:ty ) => {
        pub fn $f(&self, other: &Self) -> $retty {
            <$retty>::new(self.ctx, unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                $z3fn(self.ctx.z3_ctx, self.z3_ast, other.z3_ast)
            })
        }
    };
}

/* We aren't currently using the trinop! macro for any of our trinops
macro_rules! trinop {
    ( $f:ident, $z3fn:ident, $retty:ty ) => {
        pub fn $f(&self, a: &Self, b: &Self) -> $retty {
            <$retty>::new(self.ctx, unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                $z3fn(self.ctx.z3_ctx, self.z3_ast, a.z3_ast, b.z3_ast)
            })
        }
    };
}
*/

macro_rules! varop {
    ( $f:ident, $z3fn:ident, $retty:ty ) => {
        pub fn $f(&self, other: &[&Self]) -> $retty {
            <$retty>::new(self.ctx, unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let mut tmp = vec![self.z3_ast];
                for a in other {
                    tmp.push(a.z3_ast)
                }
                assert!(tmp.len() <= 0xffff_ffff);
                $z3fn(self.ctx.z3_ctx, tmp.len() as u32, tmp.as_ptr())
            })
        }
    };
}

/// Abstract syntax tree (AST) nodes represent terms, constants, or expressions.
/// The `Ast` trait contains methods common to all AST subtypes.
pub trait Ast<'ctx>: Sized {
    fn get_ctx(&self) -> &'ctx Context;
    fn get_z3_ast(&self) -> Z3_ast;

    // This would be great, but gives error E0071 "expected struct, variant or union type, found Self"
    // so I don't think we can write a generic constructor like this.
    // Instead we just require the method, and use the new_ast! macro defined below to implement it
    // on each Ast subtype.
    /*
    fn new(ctx: &'ctx Context, ast: Z3_ast) -> Self {
        assert!(!ast.is_null());
        Self {
            ctx,
            z3_ast: unsafe {
                debug!("new ast {:p}", ast);
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_inc_ref(ctx.z3_ctx, ast);
                ast
            },
        }
    }
    */
    fn new(ctx: &'ctx Context, ast: Z3_ast) -> Self;

    /// Compare this `Ast` with another `Ast`, and get a [`Bool`](struct.Bool.html)
    /// representing the result.
    ///
    /// This operation works with all possible `Ast`s (int, real, BV, etc), but the two
    /// `Ast`s being compared must be the same type.
    //
    // Note that we can't use the binop! macro because of the `pub` keyword on it
    fn _eq(&self, other: &Self) -> Bool<'ctx> {
        Bool::new(self.get_ctx(), unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_eq(self.get_ctx().z3_ctx, self.get_z3_ast(), other.get_z3_ast())
        })
    }

    /// Compare this `Ast` with a list of other `Ast`s, and get a [`Bool`](struct.Bool.html)
    /// which is true only if all arguments (including Self) are pairwise distinct.
    ///
    /// This operation works with all possible `Ast`s (int, real, BV, etc), but the
    /// `Ast`s being compared must all be the same type.
    //
    // Note that we can't use the varop! macro because of the `pub` keyword on it
    fn distinct(&self, other: &[&Self]) -> Bool<'ctx> {
        Bool::new(self.get_ctx(), unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            let mut tmp = vec![self.get_z3_ast()];
            for a in other {
                tmp.push(a.get_z3_ast())
            }
            assert!(tmp.len() <= 0xffff_ffff);
            Z3_mk_distinct(self.get_ctx().z3_ctx, tmp.len() as u32, tmp.as_ptr())
        })
    }

    /// Get the [`Sort`](../struct.Sort.html) of the `Ast`
    fn get_sort(&self) -> Sort<'ctx> {
        Sort {
            ctx: self.get_ctx(),
            z3_sort: unsafe { Z3_get_sort(self.get_ctx().z3_ctx, self.get_z3_ast()) },
        }
    }
}

// We'd love to have new() implemented directly on the Ast trait, see notes there.
// Instead we'll settle for this macro for now
macro_rules! new_ast {
    () => {
        fn new(ctx: &'ctx Context, ast: Z3_ast) -> Self {
            assert!(!ast.is_null());
            Self {
                ctx,
                z3_ast: unsafe {
                    debug!("new ast {:p}", ast);
                    let guard = Z3_MUTEX.lock().unwrap();
                    Z3_inc_ref(ctx.z3_ctx, ast);
                    ast
                },
            }
        }
    };
}

// While we're at it, we can make the rest of the required impl into a macro too
macro_rules! impl_ast {
    () => {
        fn get_ctx(&self) -> &'ctx Context {
            self.ctx
        }

        fn get_z3_ast(&self) -> Z3_ast {
            self.z3_ast
        }

        new_ast!();
    }
}

impl<'ctx> Ast<'ctx> for Bool<'ctx> {
    impl_ast!();
}

impl<'ctx> Ast<'ctx> for Int<'ctx> {
    impl_ast!();
}

impl<'ctx> Ast<'ctx> for Real<'ctx> {
    impl_ast!();
}

impl<'ctx> Ast<'ctx> for BV<'ctx> {
    impl_ast!();
}

impl<'ctx> Ast<'ctx> for Array<'ctx> {
    impl_ast!();
}

impl<'ctx> Ast<'ctx> for Set<'ctx> {
    impl_ast!();
}

impl<'ctx> Bool<'ctx> {
    pub fn new_const(ctx: &'ctx Context, name: Symbol) -> Bool<'ctx> {
        let sort = Sort::bool(ctx);
        Self::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_const(ctx.z3_ctx, name.as_z3_symbol(ctx), sort.z3_sort)
        })
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str) -> Bool<'ctx> {
        let sort = Sort::bool(ctx);
        Self::new(ctx, unsafe {
            let pp = CString::new(prefix).unwrap();
            let p = pp.as_ptr();
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
        })
    }

    pub fn from_bool(ctx: &'ctx Context, b: bool) -> Bool<'ctx> {
        Self::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            if b {
                Z3_mk_true(ctx.z3_ctx)
            } else {
                Z3_mk_false(ctx.z3_ctx)
            }
        })
    }

    pub fn as_bool(&self) -> Option<bool> {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            match Z3_get_bool_value(self.ctx.z3_ctx, self.z3_ast) {
                Z3_L_TRUE => Some(true),
                Z3_L_FALSE => Some(false),
                _ => None,
            }
        }
    }

    // TODO: this should be on the Ast trait, but I don't know how to return Self<'dest_ctx>.
    // When I try, it gives the error E0109 "lifetime arguments are not allowed for this type".
    pub fn translate<'dest_ctx>(&self, dest: &'dest_ctx Context) -> Bool<'dest_ctx> {
        Bool::new(dest, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_translate(self.ctx.z3_ctx, self.z3_ast, dest.z3_ctx)
        })
    }

    // This doesn't quite fit the trinop! macro because of the generic argty
    pub fn ite<T>(&self, a: &T, b: &T) -> T
    where
        T: Ast<'ctx>,
    {
        T::new(self.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_ite(self.ctx.z3_ctx, self.z3_ast, a.get_z3_ast(), b.get_z3_ast())
        })
    }

    varop!(and, Z3_mk_and, Self);
    varop!(or, Z3_mk_or, Self);
    binop!(xor, Z3_mk_xor, Self);
    unop!(not, Z3_mk_not, Self);
    binop!(iff, Z3_mk_iff, Self);
    binop!(implies, Z3_mk_implies, Self);

    pub fn pb_le(&self, other: &[&Bool<'ctx>], coeffs: Vec<i32>, k: i32) -> Bool<'ctx> {
        Bool::new(self.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            let mut tmp = vec![self.z3_ast];
            for a in other {
                tmp.push(a.z3_ast)
            }
            assert!(tmp.len() <= 0xffffffff);
            let mut tmp_coeffs = coeffs.clone();
            Z3_mk_pble(
                self.ctx.z3_ctx,
                tmp.len() as u32,
                tmp.as_ptr(),
                tmp_coeffs.as_mut_ptr(),
                k,
            )
        })
    }
    pub fn pb_ge(&self, other: &[&Bool<'ctx>], coeffs: Vec<i32>, k: i32) -> Bool<'ctx> {
        Bool::new(self.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            let mut tmp = vec![self.z3_ast];
            for a in other {
                tmp.push(a.z3_ast)
            }
            assert!(tmp.len() <= 0xffffffff);
            let mut tmp_coeffs = coeffs.clone();
            Z3_mk_pbge(
                self.ctx.z3_ctx,
                tmp.len() as u32,
                tmp.as_ptr(),
                tmp_coeffs.as_mut_ptr(),
                k,
            )
        })
    }
    pub fn pb_eq(&self, other: &[&Bool<'ctx>], coeffs: Vec<i32>, k: i32) -> Bool<'ctx> {
        Bool::new(self.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            let mut tmp = vec![self.z3_ast];
            for a in other {
                tmp.push(a.z3_ast)
            }
            assert!(tmp.len() <= 0xffffffff);
            let mut tmp_coeffs = coeffs.clone();
            Z3_mk_pbeq(
                self.ctx.z3_ctx,
                tmp.len() as u32,
                tmp.as_ptr(),
                tmp_coeffs.as_mut_ptr(),
                k,
            )
        })
    }
}

impl<'ctx> Int<'ctx> {
    pub fn new_const(ctx: &'ctx Context, name: Symbol) -> Int<'ctx> {
        let sort = Sort::int(ctx);
        Self::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_const(ctx.z3_ctx, name.as_z3_symbol(ctx), sort.z3_sort)
        })
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str) -> Int<'ctx> {
        let sort = Sort::int(ctx);
        Self::new(ctx, unsafe {
            let pp = CString::new(prefix).unwrap();
            let p = pp.as_ptr();
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
        })
    }

    pub fn from_i64(ctx: &'ctx Context, i: i64) -> Int<'ctx> {
        let sort = Sort::int(ctx);
        Self::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_int64(ctx.z3_ctx, i, sort.z3_sort)
        })
    }

    pub fn from_u64(ctx: &'ctx Context, u: u64) -> Int<'ctx> {
        let sort = Sort::int(ctx);
        Self::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_unsigned_int64(ctx.z3_ctx, u, sort.z3_sort)
        })
    }

    pub fn as_i64(&self) -> Option<i64> {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            let mut tmp: ::std::os::raw::c_longlong = 0;
            if Z3_get_numeral_int64(self.ctx.z3_ctx, self.z3_ast, &mut tmp) {
                Some(tmp)
            } else {
                None
            }
        }
    }

    pub fn as_u64(&self) -> Option<u64> {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            let mut tmp: ::std::os::raw::c_ulonglong = 0;
            if Z3_get_numeral_uint64(self.ctx.z3_ctx, self.z3_ast, &mut tmp) {
                Some(tmp)
            } else {
                None
            }
        }
    }

    pub fn from_real(ast: &Real<'ctx>) -> Int<'ctx> {
        Self::new(ast.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_real2int(ast.ctx.z3_ctx, ast.z3_ast)
        })
    }

    /// Create a real from an integer.
    /// This is just a convenience wrapper around
    /// [`Real::from_int`](struct.Real.html#method.from_int); see notes there
    pub fn to_real(&self) -> Real<'ctx> {
        Real::from_int(self)
    }

    /// Create an integer from a bitvector.
    ///
    /// Signed and unsigned version.
    ///
    /// # Examples
    /// ```
    /// # use z3::{ast, Config, Context, Solver};
    /// # use z3::ast::Ast;
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// let bv = ctx.named_bitvector_const("x", 32);
    /// solver.assert(&bv._eq(&ast::BV::from_i64(&ctx, -3, 32)));
    ///
    /// let x = ast::Int::from_bv(&bv, true);
    ///
    /// assert!(solver.check());
    /// let model = solver.get_model();
    ///
    /// assert_eq!(-3, model.eval(&x).unwrap().as_i64().unwrap());
    /// ```
    pub fn from_bv(ast: &BV<'ctx>, signed: bool) -> Int<'ctx> {
        Self::new(ast.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_bv2int(ast.ctx.z3_ctx, ast.z3_ast, signed)
        })
    }

    /// Create a bitvector from an integer.
    /// This is just a convenience wrapper around
    /// [`BV::from_int`](struct.BV.html#method.from_int); see notes there
    pub fn to_ast(&self, sz: u32) -> BV<'ctx> {
        BV::from_int(self, sz)
    }

    // TODO: this should be on the Ast trait, but I don't know how to return Self<'dest_ctx>.
    // When I try, it gives the error E0109 "lifetime arguments are not allowed for this type".
    pub fn translate<'dest_ctx>(&self, dest: &'dest_ctx Context) -> Int<'dest_ctx> {
        Int::new(dest, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_translate(self.ctx.z3_ctx, self.z3_ast, dest.z3_ctx)
        })
    }

    varop!(add, Z3_mk_add, Self);
    varop!(sub, Z3_mk_sub, Self);
    varop!(mul, Z3_mk_mul, Self);
    binop!(div, Z3_mk_div, Self);
    binop!(rem, Z3_mk_rem, Self);
    binop!(modulo, Z3_mk_mod, Self);
    binop!(power, Z3_mk_power, Self);
    unop!(unary_minus, Z3_mk_unary_minus, Self);
    binop!(lt, Z3_mk_lt, Bool<'ctx>);
    binop!(le, Z3_mk_le, Bool<'ctx>);
    binop!(gt, Z3_mk_gt, Bool<'ctx>);
    binop!(ge, Z3_mk_ge, Bool<'ctx>);
    // Z3 does support mixing ints and reals in add(), sub(), mul(), div(), and power()
    //   (but not rem(), modulo(), lt(), le(), gt(), or ge()).
    // TODO: we could consider expressing this by having a Numeric trait with these methods.
    //    Int and Real would have the Numeric trait, but not the other Asts.
    // For example:
    //   fn add(&self, other: &impl Numeric<'ctx>) -> Dynamic<'ctx> { ... }
    // Note the return type would have to be Dynamic I think (?), as the exact result type
    //   depends on the particular types of the inputs.
    // Alternately, we could just have
    //   Int::add_real(&self, other: &Real<'ctx>) -> Real<'ctx>
    // and
    //   Real::add_int(&self, other: &Int<'ctx>) -> Real<'ctx>
    // This might be cleaner because we know exactly what the output type will be for these methods.
}

impl<'ctx> Real<'ctx> {
    pub fn new_const(ctx: &'ctx Context, name: Symbol) -> Real<'ctx> {
        let sort = Sort::real(ctx);
        Self::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_const(ctx.z3_ctx, name.as_z3_symbol(ctx), sort.z3_sort)
        })
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str) -> Real<'ctx> {
        let sort = Sort::real(ctx);
        Self::new(ctx, unsafe {
            let pp = CString::new(prefix).unwrap();
            let p = pp.as_ptr();
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
        })
    }

    pub fn from_real(ctx: &'ctx Context, num: i32, den: i32) -> Real<'ctx> {
        Self::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_real(
                ctx.z3_ctx,
                num as ::std::os::raw::c_int,
                den as ::std::os::raw::c_int,
            )
        })
    }

    pub fn as_real(&self) -> Option<(i64, i64)> {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            let mut num: i64 = 0;
            let mut den: i64 = 0;
            if Z3_get_numeral_small(self.ctx.z3_ctx, self.z3_ast, &mut num, &mut den) {
                Some((num, den))
            } else {
                None
            }
        }
    }

    pub fn from_int(ast: &Int<'ctx>) -> Real<'ctx> {
        Self::new(ast.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_int2real(ast.ctx.z3_ctx, ast.z3_ast)
        })
    }

    /// Create an integer from a real.
    /// This is just a convenience wrapper around
    /// [`Int::from_real`](struct.Int.html#method.from_real); see notes there
    pub fn to_int(&self) -> Int<'ctx> {
        Int::from_real(self)
    }

    unop!(is_int, Z3_mk_is_int, Bool<'ctx>);

    // TODO: this should be on the Ast trait, but I don't know how to return Self<'dest_ctx>.
    // When I try, it gives the error E0109 "lifetime arguments are not allowed for this type".
    pub fn translate<'dest_ctx>(&self, dest: &'dest_ctx Context) -> Real<'dest_ctx> {
        Real::new(dest, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_translate(self.ctx.z3_ctx, self.z3_ast, dest.z3_ctx)
        })
    }

    varop!(add, Z3_mk_add, Self);
    varop!(sub, Z3_mk_sub, Self);
    varop!(mul, Z3_mk_mul, Self);
    binop!(div, Z3_mk_div, Self);
    binop!(power, Z3_mk_power, Self);
    unop!(unary_minus, Z3_mk_unary_minus, Self);
}

impl<'ctx> BV<'ctx> {
    pub fn new_const(ctx: &'ctx Context, name: Symbol, sz: u32) -> BV<'ctx> {
        let sort = Sort::bitvector(ctx, sz);
        Self::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_const(ctx.z3_ctx, name.as_z3_symbol(ctx), sort.z3_sort)
        })
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, sz: u32) -> BV<'ctx> {
        let sort = Sort::bitvector(ctx, sz);
        Self::new(ctx, unsafe {
            let pp = CString::new(prefix).unwrap();
            let p = pp.as_ptr();
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
        })
    }

    pub fn from_i64(ctx: &'ctx Context, i: i64, sz: u32) -> BV<'ctx> {
        let sort = Sort::bitvector(ctx, sz);
        Self::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_int64(ctx.z3_ctx, i, sort.z3_sort)
        })
    }

    pub fn from_u64(ctx: &'ctx Context, u: u64, sz: u32) -> BV<'ctx> {
        let sort = Sort::bitvector(ctx, sz);
        Self::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_unsigned_int64(ctx.z3_ctx, u, sort.z3_sort)
        })
    }

    pub fn as_i64(&self) -> Option<i64> {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            let mut tmp: ::std::os::raw::c_longlong = 0;
            if Z3_get_numeral_int64(self.ctx.z3_ctx, self.z3_ast, &mut tmp) {
                Some(tmp)
            } else {
                None
            }
        }
    }

    pub fn as_u64(&self) -> Option<u64> {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            let mut tmp: ::std::os::raw::c_ulonglong = 0;
            if Z3_get_numeral_uint64(self.ctx.z3_ctx, self.z3_ast, &mut tmp) {
                Some(tmp)
            } else {
                None
            }
        }
    }

    /// Create a bit vector from an integer.
    ///
    /// The bit vector will have width `sz`.
    ///
    /// # Examples
    /// ```
    /// # use z3::{ast, Config, Context, Solver};
    /// # use z3::ast::Ast;
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// let i = ctx.named_int_const("x");
    /// solver.assert(&i._eq(&ctx.from_i64(-3)));
    ///
    /// let x = ast::BV::from_int(&i, 64);
    /// assert_eq!(64, x.get_size());
    ///
    /// assert!(solver.check());
    /// let model = solver.get_model();
    ///
    /// assert_eq!(-3, model.eval(&x).unwrap().as_i64().expect("as_i64() shouldn't fail"));
    /// ```
    pub fn from_int(ast: &Int<'ctx>, sz: u32) -> BV<'ctx> {
        Self::new(ast.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_int2bv(ast.ctx.z3_ctx, sz, ast.z3_ast)
        })
    }

    /// Create an integer from a bitvector.
    /// This is just a convenience wrapper around
    /// [`Int::from_bv`](struct.Int.html#method.from_bv); see notes there
    pub fn to_int(&self, signed: bool) -> Int<'ctx> {
        Int::from_bv(self, signed)
    }

    /// Get the size of the bitvector (in bits)
    pub fn get_size(&self) -> u32 {
        let sort = self.get_sort();
        unsafe { Z3_get_bv_sort_size(self.ctx.z3_ctx, sort.z3_sort) }
    }

    // TODO: this should be on the Ast trait, but I don't know how to return Self<'dest_ctx>.
    // When I try, it gives the error E0109 "lifetime arguments are not allowed for this type".
    pub fn translate<'dest_ctx>(&self, dest: &'dest_ctx Context) -> BV<'dest_ctx> {
        BV::new(dest, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_translate(self.ctx.z3_ctx, self.z3_ast, dest.z3_ctx)
        })
    }

    unop!(bvnot, Z3_mk_bvnot, Self);
    unop!(bvneg, Z3_mk_bvneg, Self);
    /// Conjunction of all the bits in the vector. Returns a BV with size (bitwidth) 1.
    unop!(bvredand, Z3_mk_bvredand, Self);
    /// Disjunction of all the bits in the vector. Returns a BV with size (bitwidth) 1.
    unop!(bvredor, Z3_mk_bvredor, Self);
    binop!(bvand, Z3_mk_bvand, Self);
    binop!(bvor, Z3_mk_bvor, Self);
    binop!(bvxor, Z3_mk_bvxor, Self);
    binop!(bvnand, Z3_mk_bvnand, Self);
    binop!(bvnor, Z3_mk_bvnor, Self);
    binop!(bvxnor, Z3_mk_bvxnor, Self);
    binop!(bvadd, Z3_mk_bvadd, Self);
    binop!(bvsub, Z3_mk_bvsub, Self);
    binop!(bvmul, Z3_mk_bvmul, Self);
    binop!(bvudiv, Z3_mk_bvudiv, Self);
    binop!(bvsdiv, Z3_mk_bvsdiv, Self);
    binop!(bvurem, Z3_mk_bvurem, Self);
    binop!(bvsrem, Z3_mk_bvsrem, Self);
    binop!(bvsmod, Z3_mk_bvsmod, Self);
    binop!(bvult, Z3_mk_bvult, Bool<'ctx>);
    binop!(bvslt, Z3_mk_bvslt, Bool<'ctx>);
    binop!(bvule, Z3_mk_bvule, Bool<'ctx>);
    binop!(bvsle, Z3_mk_bvsle, Bool<'ctx>);
    binop!(bvuge, Z3_mk_bvuge, Bool<'ctx>);
    binop!(bvsge, Z3_mk_bvsge, Bool<'ctx>);
    binop!(bvugt, Z3_mk_bvugt, Bool<'ctx>);
    binop!(bvsgt, Z3_mk_bvsgt, Bool<'ctx>);
    binop!(concat, Z3_mk_concat, Self);
    binop!(bvshl, Z3_mk_bvshl, Self);
    binop!(bvlshr, Z3_mk_bvlshr, Self);
    binop!(bvashr, Z3_mk_bvashr, Self);
}

impl<'ctx> Array<'ctx> {
    pub fn new_const(
        ctx: &'ctx Context,
        name: Symbol,
        domain: &Sort<'ctx>,
        range: &Sort<'ctx>,
    ) -> Array<'ctx> {
        let sort = Sort::array(ctx, domain, range);
        Self::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_const(ctx.z3_ctx, name.as_z3_symbol(ctx), sort.z3_sort)
        })
    }

    pub fn fresh_const(
        ctx: &'ctx Context,
        prefix: &str,
        domain: &Sort<'ctx>,
        range: &Sort<'ctx>,
    ) -> Array<'ctx> {
        let sort = Sort::array(ctx, domain, range);
        Self::new(ctx, unsafe {
            let pp = CString::new(prefix).unwrap();
            let p = pp.as_ptr();
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
        })
    }

    // TODO: this should be on the Ast trait, but I don't know how to return Self<'dest_ctx>.
    // When I try, it gives the error E0109 "lifetime arguments are not allowed for this type".
    pub fn translate<'dest_ctx>(&self, dest: &'dest_ctx Context) -> Array<'dest_ctx> {
        Array::new(dest, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_translate(self.ctx.z3_ctx, self.z3_ast, dest.z3_ctx)
        })
    }

    /// Get the value at a given index in the array.
    ///
    /// Note that the `index` _must be_ of the array's `domain` sort.
    /// The return type will be of the array's `range` sort.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn select(&self, index: &Dynamic<'ctx>) -> Dynamic<'ctx> {
        // TODO: We could validate here that the index is of the correct type.
        // This would require us either to keep around the original `domain` argument
        // from when the Array was constructed, or to do an additional Z3 query
        // to find the domain sort first.
        // But if we did this check ourselves, we'd just panic, so it doesn't seem
        // like a huge advantage over just letting Z3 panic itself when it discovers the
        // problem.
        // This way we also avoid the redundant check every time this method is called.
        Dynamic::new(self.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_select(self.ctx.z3_ctx, self.z3_ast, index.get_z3_ast())
        })
    }

    /// Update the value at a given index in the array.
    ///
    /// Note that the `index` _must be_ of the array's `domain` sort,
    /// and the `value` _must be_ of the array's `range` sort.
    //
    // We avoid the trinop! macro because the arguments have non-Self types
    pub fn store(&self, index: &Dynamic<'ctx>, value: &Dynamic<'ctx>) -> Self {
        Self::new(self.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_store(
                self.ctx.z3_ctx,
                self.z3_ast,
                index.get_z3_ast(),
                value.get_z3_ast(),
            )
        })
    }
}

impl<'ctx> Set<'ctx> {
    pub fn new_const(ctx: &'ctx Context, name: Symbol, eltype: &Sort<'ctx>) -> Set<'ctx> {
        let sort = Sort::set(ctx, eltype);
        Self::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_const(ctx.z3_ctx, name.as_z3_symbol(ctx), sort.z3_sort)
        })
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, eltype: &Sort<'ctx>) -> Set<'ctx> {
        let sort = Sort::set(ctx, eltype);
        Self::new(ctx, unsafe {
            let pp = CString::new(prefix).unwrap();
            let p = pp.as_ptr();
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
        })
    }

    // TODO: this should be on the Ast trait, but I don't know how to return Self<'dest_ctx>.
    // When I try, it gives the error E0109 "lifetime arguments are not allowed for this type".
    pub fn translate<'dest_ctx>(&self, dest: &'dest_ctx Context) -> Set<'dest_ctx> {
        Set::new(dest, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_translate(self.ctx.z3_ctx, self.z3_ast, dest.z3_ctx)
        })
    }

    /// Add an element to the set.
    ///
    /// Note that the `element` _must be_ of the `Set`'s `eltype` sort.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn add(&self, element: &Dynamic<'ctx>) -> Set<'ctx> {
        Set::new(self.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_set_add(self.ctx.z3_ctx, self.z3_ast, element.get_z3_ast())
        })
    }

    /// Remove an element from the set.
    ///
    /// Note that the `element` _must be_ of the `Set`'s `eltype` sort.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn del(&self, element: &Dynamic<'ctx>) -> Set<'ctx> {
        Set::new(self.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_set_add(self.ctx.z3_ctx, self.z3_ast, element.get_z3_ast())
        })
    }

    /// Check if an item is a member of the set.
    ///
    /// Note that the `element` _must be_ of the `Set`'s `eltype` sort.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn member(&self, element: &Dynamic<'ctx>) -> Bool<'ctx> {
        Bool::new(self.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_set_add(self.ctx.z3_ctx, self.z3_ast, element.get_z3_ast())
        })
    }

    /// Take the intersection of a list of sets.
    varop!(intersect, Z3_mk_set_intersect, Self);
    /// Take the union of a list of sets.
    varop!(set_union, Z3_mk_set_union, Self);
    /// Check if the set is a subset of another set.
    binop!(set_subset, Z3_mk_set_subset, Bool<'ctx>);
    /// Take the complement of the set.
    unop!(complement, Z3_mk_set_complement, Self);
    /// Take the set difference between two sets.
    binop!(difference, Z3_mk_set_difference, Self);
}

/// Create a forall quantifier.
///
/// # Examples
/// ```
/// # use z3::{ast, Config, Context, Solver, Symbol};
/// # use z3::ast::Ast;
/// # use std::convert::TryInto;
/// # let cfg = Config::new();
/// # let ctx = Context::new(&cfg);
/// # let solver = Solver::new(&ctx);
/// let f = ctx.func_decl(Symbol::String("f".to_owned()), &[&ctx.int_sort()], &ctx.int_sort());
///
/// let x: ast::Int = ctx.named_int_const("x");
/// let f_x: ast::Int = f.apply(&[&x.clone().into()]).try_into().unwrap();
/// let forall: ast::Dynamic = ast::forall_const(&ctx, &[&x.clone().into()], &(x._eq(&f_x)).into());
/// solver.assert(&forall.try_into().unwrap());
///
/// assert!(solver.check());
/// let model = solver.get_model();
///
/// let f_f_3: ast::Int = f.apply(&[&f.apply(&[&ctx.from_u64(3).into()])]).try_into().unwrap();
/// assert_eq!(3, model.eval(&f_f_3).unwrap().as_u64().unwrap());
/// ```

pub fn forall_const<'ctx>(
    ctx: &'ctx Context,
    bounds: &[&Dynamic<'ctx>],
    body: &Dynamic<'ctx>,
) -> Dynamic<'ctx> {
    assert!(bounds.iter().all(|a| a.get_ctx().z3_ctx == ctx.z3_ctx));
    assert_eq!(ctx.z3_ctx, body.get_ctx().z3_ctx);

    if bounds.is_empty() {
        return body.clone();
    }

    let bounds: Vec<_> = bounds.iter().map(|a| a.get_z3_ast()).collect();

    Ast::new(ctx, unsafe {
        Z3_mk_forall_const(
            ctx.z3_ctx,
            0,
            bounds.len().try_into().unwrap(),
            bounds.as_ptr() as *const Z3_app,
            0,
            std::ptr::null(),
            body.get_z3_ast(),
        )
    })
}

// TODO: instead of these _is_eq(), _clone(), etc methods we could also just make
// macros to do the various impls.  Not sure if that's better or not.

// for use to implement PartialEq and Eq
fn _is_eq<'ctx, T>(a: &T, b: &T) -> bool
where
    T: Ast<'ctx>,
{
    assert_eq!(a.get_ctx().z3_ctx, b.get_ctx().z3_ctx);
    unsafe { Z3_is_eq_ast(a.get_ctx().z3_ctx, a.get_z3_ast(), b.get_z3_ast()) }
}

// for use to implement Clone
fn _clone<'ctx, T>(ast: &T) -> T
where
    T: Ast<'ctx>,
{
    debug!("clone ast {:p}", ast.get_z3_ast());
    T::new(ast.get_ctx(), ast.get_z3_ast())
}

// for use to implement Drop
fn _drop<'ctx>(ast: &mut impl Ast<'ctx>) {
    debug!("drop ast {:p}", ast.get_z3_ast());
    unsafe {
        let guard = Z3_MUTEX.lock().unwrap();
        Z3_dec_ref(ast.get_ctx().z3_ctx, ast.get_z3_ast());
    }
}

// for use to implement Hash
fn _hash<'ctx, H: Hasher>(ast: &impl Ast<'ctx>, state: &mut H) {
    unsafe {
        let u = Z3_get_ast_hash(ast.get_ctx().z3_ctx, ast.get_z3_ast());
        u.hash(state);
    }
}

// for use to implement fmt::Display
fn _fmt<'ctx>(ast: &impl Ast<'ctx>, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    let p = unsafe {
        CStr::from_ptr(Z3_ast_to_string(ast.get_ctx().z3_ctx, ast.get_z3_ast()) as *mut i8)
    };
    if p.as_ptr().is_null() {
        return Result::Err(fmt::Error);
    }
    match p.to_str() {
        Ok(s) => write!(f, "{}", s),
        Err(_) => Result::Err(fmt::Error),
    }
}

impl<'ctx> PartialEq for Bool<'ctx> {
    fn eq(&self, other: &Bool<'ctx>) -> bool {
        _is_eq(self, other)
    }
}
impl<'ctx> PartialEq for Int<'ctx> {
    fn eq(&self, other: &Int<'ctx>) -> bool {
        _is_eq(self, other)
    }
}
impl<'ctx> PartialEq for Real<'ctx> {
    fn eq(&self, other: &Real<'ctx>) -> bool {
        _is_eq(self, other)
    }
}
impl<'ctx> PartialEq for BV<'ctx> {
    fn eq(&self, other: &BV<'ctx>) -> bool {
        _is_eq(self, other)
    }
}
impl<'ctx> PartialEq for Array<'ctx> {
    fn eq(&self, other: &Array<'ctx>) -> bool {
        _is_eq(self, other)
    }
}
impl<'ctx> PartialEq for Set<'ctx> {
    fn eq(&self, other: &Set<'ctx>) -> bool {
        _is_eq(self, other)
    }
}

impl<'ctx> Eq for Bool<'ctx> {}
impl<'ctx> Eq for Int<'ctx> {}
impl<'ctx> Eq for Real<'ctx> {}
impl<'ctx> Eq for BV<'ctx> {}
impl<'ctx> Eq for Array<'ctx> {}
impl<'ctx> Eq for Set<'ctx> {}

impl<'ctx> Clone for Bool<'ctx> {
    fn clone(&self) -> Self {
        _clone(self)
    }
}
impl<'ctx> Clone for Int<'ctx> {
    fn clone(&self) -> Self {
        _clone(self)
    }
}
impl<'ctx> Clone for Real<'ctx> {
    fn clone(&self) -> Self {
        _clone(self)
    }
}
impl<'ctx> Clone for BV<'ctx> {
    fn clone(&self) -> Self {
        _clone(self)
    }
}
impl<'ctx> Clone for Array<'ctx> {
    fn clone(&self) -> Self {
        _clone(self)
    }
}
impl<'ctx> Clone for Set<'ctx> {
    fn clone(&self) -> Self {
        _clone(self)
    }
}

impl<'ctx> Drop for Bool<'ctx> {
    fn drop(&mut self) {
        _drop(self)
    }
}
impl<'ctx> Drop for Int<'ctx> {
    fn drop(&mut self) {
        _drop(self)
    }
}
impl<'ctx> Drop for Real<'ctx> {
    fn drop(&mut self) {
        _drop(self)
    }
}
impl<'ctx> Drop for BV<'ctx> {
    fn drop(&mut self) {
        _drop(self)
    }
}
impl<'ctx> Drop for Array<'ctx> {
    fn drop(&mut self) {
        _drop(self)
    }
}
impl<'ctx> Drop for Set<'ctx> {
    fn drop(&mut self) {
        _drop(self)
    }
}

impl<'ctx> Hash for Bool<'ctx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        _hash(self, state)
    }
}
impl<'ctx> Hash for Int<'ctx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        _hash(self, state)
    }
}
impl<'ctx> Hash for Real<'ctx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        _hash(self, state)
    }
}
impl<'ctx> Hash for BV<'ctx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        _hash(self, state)
    }
}
impl<'ctx> Hash for Array<'ctx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        _hash(self, state)
    }
}
impl<'ctx> Hash for Set<'ctx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        _hash(self, state)
    }
}

impl<'ctx> fmt::Display for Bool<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        _fmt(self, f)
    }
}
impl<'ctx> fmt::Display for Int<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        _fmt(self, f)
    }
}
impl<'ctx> fmt::Display for Real<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        _fmt(self, f)
    }
}
impl<'ctx> fmt::Display for BV<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        _fmt(self, f)
    }
}
impl<'ctx> fmt::Display for Array<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        _fmt(self, f)
    }
}
impl<'ctx> fmt::Display for Set<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        _fmt(self, f)
    }
}

/// This type is used when we have an [`Ast`](trait.Ast.html) of dynamic type,
/// i.e., we don't know at compile time what type it is.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Dynamic<'ctx> {
    Bool(Bool<'ctx>),
    Int(Int<'ctx>),
    Real(Real<'ctx>),
    BV(BV<'ctx>),
    Array(Array<'ctx>),
    Set(Set<'ctx>),
}

impl<'ctx> Ast<'ctx> for Dynamic<'ctx> {
    fn get_ctx(&self) -> &'ctx Context {
        match self {
            Dynamic::Bool(ast) => ast.get_ctx(),
            Dynamic::Int(ast) => ast.get_ctx(),
            Dynamic::Real(ast) => ast.get_ctx(),
            Dynamic::BV(ast) => ast.get_ctx(),
            Dynamic::Array(ast) => ast.get_ctx(),
            Dynamic::Set(ast) => ast.get_ctx(),
        }
    }

    fn get_z3_ast(&self) -> Z3_ast {
        match self {
            Dynamic::Bool(ast) => ast.get_z3_ast(),
            Dynamic::Int(ast) => ast.get_z3_ast(),
            Dynamic::Real(ast) => ast.get_z3_ast(),
            Dynamic::BV(ast) => ast.get_z3_ast(),
            Dynamic::Array(ast) => ast.get_z3_ast(),
            Dynamic::Set(ast) => ast.get_z3_ast(),
        }
    }

    fn new(ctx: &'ctx Context, ast: Z3_ast) -> Self {
        assert!(!ast.is_null());
        let kind: SortKind = unsafe {
            let z3_sort = Z3_get_sort(ctx.z3_ctx, ast);
            Z3_get_sort_kind(ctx.z3_ctx, z3_sort)
        };
        match kind {
            SortKind::Bool => Dynamic::Bool(Bool::new(ctx, ast)),
            SortKind::Int => Dynamic::Int(Int::new(ctx, ast)),
            SortKind::Real => Dynamic::Real(Real::new(ctx, ast)),
            SortKind::BV => Dynamic::BV(BV::new(ctx, ast)),
            SortKind::Array => Dynamic::Array(Array::new(ctx, ast)),
            // TODO: which SortKind corresponds to Set? There is no `SortKind::Set`
            // SortKind::Set => Dynamic::Set(Set::new(ctx, ast)),
            _ => unimplemented!("Dynamic with kind {:?}", kind),
        }
    }
}

impl<'ctx> Dynamic<'ctx> {
    pub fn from_ast(ast: &impl Ast<'ctx>) -> Self {
        Self::new(ast.get_ctx(), ast.get_z3_ast())
    }

    /// Returns `None` if the `Dynamic` is not actually a `Bool`
    pub fn as_bool(&self) -> Option<&Bool<'ctx>> {
        match self {
            Dynamic::Bool(ast) => Some(&ast),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually an `Int`
    pub fn as_int(&self) -> Option<&Int<'ctx>> {
        match self {
            Dynamic::Int(ast) => Some(&ast),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `Real`
    pub fn as_real(&self) -> Option<&Real<'ctx>> {
        match self {
            Dynamic::Real(ast) => Some(&ast),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `BV`
    pub fn as_bv(&self) -> Option<&BV<'ctx>> {
        match self {
            Dynamic::BV(ast) => Some(&ast),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually an `Array`
    pub fn as_array(&self) -> Option<&Array<'ctx>> {
        match self {
            Dynamic::Array(ast) => Some(&ast),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `Set`
    pub fn as_set(&self) -> Option<&Set<'ctx>> {
        match self {
            Dynamic::Set(ast) => Some(&ast),
            _ => None,
        }
    }
}

/* error E0119: conflicting implementation From<T> for T
    i.e., since Dynamic is an Ast itself, we can't do this impl

impl<'ctx, T> From<T> for Dynamic<'ctx> where T: Ast<'ctx> {
    fn from(ast: T) -> Self {
        Dynamic::from_ast(&ast)
    }
}
*/

// These `From` impls imply the corresponding `Into` impls
impl<'ctx> From<Bool<'ctx>> for Dynamic<'ctx> {
    fn from(ast: Bool<'ctx>) -> Self {
        Dynamic::from_ast(&ast)
    }
}

impl<'ctx> From<Int<'ctx>> for Dynamic<'ctx> {
    fn from(ast: Int<'ctx>) -> Self {
        Dynamic::from_ast(&ast)
    }
}

impl<'ctx> From<Real<'ctx>> for Dynamic<'ctx> {
    fn from(ast: Real<'ctx>) -> Self {
        Dynamic::from_ast(&ast)
    }
}

impl<'ctx> From<BV<'ctx>> for Dynamic<'ctx> {
    fn from(ast: BV<'ctx>) -> Self {
        Dynamic::from_ast(&ast)
    }
}

impl<'ctx> From<Array<'ctx>> for Dynamic<'ctx> {
    fn from(ast: Array<'ctx>) -> Self {
        Dynamic::from_ast(&ast)
    }
}

impl<'ctx> From<Set<'ctx>> for Dynamic<'ctx> {
    fn from(ast: Set<'ctx>) -> Self {
        Dynamic::from_ast(&ast)
    }
}

// These `TryFrom` impls imply the corresponding `TryInto` impls
impl<'ctx> TryFrom<Dynamic<'ctx>> for Bool<'ctx> {
    type Error = String;
    fn try_from(ast: Dynamic<'ctx>) -> Result<Bool<'ctx>, String> {
        ast.as_bool()
            .cloned()
            .ok_or_else(|| format!("Not a bool: {:?}", ast))
    }
}

impl<'ctx> TryFrom<Dynamic<'ctx>> for Int<'ctx> {
    type Error = String;
    fn try_from(ast: Dynamic<'ctx>) -> Result<Int<'ctx>, String> {
        ast.as_int()
            .cloned()
            .ok_or_else(|| format!("Not an int: {:?}", ast))
    }
}

impl<'ctx> TryFrom<Dynamic<'ctx>> for Real<'ctx> {
    type Error = String;
    fn try_from(ast: Dynamic<'ctx>) -> Result<Real<'ctx>, String> {
        ast.as_real()
            .cloned()
            .ok_or_else(|| format!("Not a real: {:?}", ast))
    }
}

impl<'ctx> TryFrom<Dynamic<'ctx>> for BV<'ctx> {
    type Error = String;
    fn try_from(ast: Dynamic<'ctx>) -> Result<BV<'ctx>, String> {
        ast.as_bv()
            .cloned()
            .ok_or_else(|| format!("Not a BV: {:?}", ast))
    }
}

impl<'ctx> TryFrom<Dynamic<'ctx>> for Array<'ctx> {
    type Error = String;
    fn try_from(ast: Dynamic<'ctx>) -> Result<Array<'ctx>, String> {
        ast.as_array()
            .cloned()
            .ok_or_else(|| format!("Not an array: {:?}", ast))
    }
}

impl<'ctx> TryFrom<Dynamic<'ctx>> for Set<'ctx> {
    type Error = String;
    fn try_from(ast: Dynamic<'ctx>) -> Result<Set<'ctx>, String> {
        ast.as_set()
            .cloned()
            .ok_or_else(|| format!("Not a set: {:?}", ast))
    }
}

impl<'ctx> fmt::Debug for Dynamic<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Dynamic::Bool(ast) => write!(f, "Bool( {} )", ast),
            Dynamic::Int(ast) => write!(f, "Int( {} )", ast),
            Dynamic::Real(ast) => write!(f, "Real( {} )", ast),
            Dynamic::BV(ast) => write!(f, "BV( {} )", ast),
            Dynamic::Array(ast) => write!(f, "Array( {} )", ast),
            Dynamic::Set(ast) => write!(f, "Set( {} )", ast),
        }
    }
}
