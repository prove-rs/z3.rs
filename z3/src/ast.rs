//! Abstract syntax tree (AST).

use log::debug;
use std::borrow::Borrow;
use std::cmp::{Eq, PartialEq};
use std::convert::{TryFrom, TryInto};
use std::ffi::{CStr, CString};
use std::fmt;
use std::hash::{Hash, Hasher};

pub use z3_sys::AstKind;
use z3_sys::*;

use crate::{Context, FuncDecl, IsNotApp, Pattern, Sort, SortDiffers, Symbol};

use num::{bigint::BigInt, rational::BigRational};

/// [`Ast`] node representing a boolean value.
pub struct Bool<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`] node representing an integer value.
pub struct Int<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`] node representing a real value.
pub struct Real<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`] node representing a float value.
pub struct Float<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`] node representing a string value.
pub struct String<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`] node representing a bitvector value.
pub struct BV<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`] node representing an array value.
/// An array in Z3 is a mapping from indices to values.
pub struct Array<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`] node representing a set value.
pub struct Set<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`] node representing a sequence value.
pub struct Seq<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`] node representing a datatype or enumeration value.
pub struct Datatype<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// A dynamically typed [`Ast`] node.
pub struct Dynamic<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

/// [`Ast`] node representing a regular expression.
/// ```
/// use z3::ast;
/// use z3::{Config, Context, Solver, SatResult};
///
/// let cfg = Config::new();
/// let ctx = &Context::new(&cfg);
/// let solver = Solver::new(&ctx);
/// let s = ast::String::new_const(ctx, "s");
///
/// // the regexp representing foo[a-c]*
/// let a = ast::Regexp::concat(ctx, &[
///     &ast::Regexp::literal(ctx, "foo"),
///     &ast::Regexp::range(ctx, &'a', &'c').star()
/// ]);
/// // the regexp representing [a-z]+
/// let b = ast::Regexp::range(ctx, &'a', &'z').plus();
/// // intersection of a and b is non-empty
/// let intersect = ast::Regexp::intersect(ctx, &[&a, &b]);
/// solver.assert(&s.regex_matches(&intersect));
/// assert!(solver.check() == SatResult::Sat);
/// ```
pub struct Regexp<'ctx> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) z3_ast: Z3_ast,
}

macro_rules! unop {
    (
        $(
            $( #[ $attr:meta ] )* $f:ident ( $z3fn:ident, $retty:ty ) ;
        )*
    ) => {
        $(
            $( #[ $attr ] )*
            pub fn $f(&self) -> $retty {
                unsafe {
                    <$retty>::wrap(self.ctx, {
                        $z3fn(self.ctx.z3_ctx, self.z3_ast)
                    })
                }
            }
        )*
    };
}

macro_rules! binop {
    (
        $(
            $( #[ $attr:meta ] )* $f:ident ( $z3fn:ident, $retty:ty ) ;
        )*
    ) => {
        $(
            $( #[ $attr ] )*
            pub fn $f(&self, other: &Self) -> $retty {
                assert!(self.ctx == other.ctx);
                unsafe {
                    <$retty>::wrap(self.ctx, {
                        $z3fn(self.ctx.z3_ctx, self.z3_ast, other.z3_ast)
                    })
                }
            }
        )*
    };
}

macro_rules! trinop {
    (
        $(
            $( #[ $attr:meta ] )* $f:ident ( $z3fn:ident, $retty:ty ) ;
        )*
    ) => {
        $(
            $( #[ $attr ] )*
            pub fn $f(&self, a: &Self, b: &Self) -> $retty {
                assert!((self.ctx == a.ctx) && (a.ctx == b.ctx));
                unsafe {
                    <$retty>::wrap(self.ctx, {
                        $z3fn(self.ctx.z3_ctx, self.z3_ast, a.z3_ast, b.z3_ast)
                    })
                }
            }
        )*
    };
}

macro_rules! varop {
    (
        $(
            $( #[ $attr:meta ] )* $f:ident ( $z3fn:ident, $retty:ty ) ;
        )*
    ) => {
        $(
            $( #[ $attr ] )*
            pub fn $f(ctx: &'ctx Context, values: &[impl Borrow<Self>]) -> $retty {
                assert!(values.iter().all(|v| v.borrow().get_ctx().z3_ctx == ctx.z3_ctx));
                unsafe {
                    <$retty>::wrap(ctx, {
                        let tmp: Vec<_> = values.iter().map(|x| x.borrow().z3_ast).collect();
                        assert!(tmp.len() <= 0xffff_ffff);
                        $z3fn(ctx.z3_ctx, tmp.len() as u32, tmp.as_ptr())
                    })
                }
            }
        )*
    };
}

/// Abstract syntax tree (AST) nodes represent terms, constants, or expressions.
/// The `Ast` trait contains methods common to all AST subtypes.
pub trait Ast<'ctx>: fmt::Debug {
    fn get_ctx(&self) -> &'ctx Context;
    fn get_z3_ast(&self) -> Z3_ast;

    // This would be great, but gives error E0071 "expected struct, variant or union type, found Self"
    // so I don't think we can write a generic constructor like this.
    // Instead we just require the method, and use the impl_ast! macro defined below to implement it
    // on each Ast subtype.
    /*
    fn wrap(ctx: &'ctx Context, ast: Z3_ast) -> Self {
        assert!(!ast.is_null());
        Self {
            ctx,
            z3_ast: unsafe {
                debug!("new ast {:p}", ast);
                Z3_inc_ref(ctx.z3_ctx, ast);
                ast
            },
        }
    }
    */
    /// Wrap a raw [`Z3_ast`].
    ///
    /// # Safety
    ///
    /// The `ast` must be a valid pointer to a [`Z3_ast`].
    unsafe fn wrap(ctx: &'ctx Context, ast: Z3_ast) -> Self
    where
        Self: Sized;

    /// Compare this `Ast` with another `Ast`, and get a [`Bool`]
    /// representing the result.
    ///
    /// This operation works with all possible `Ast`s (int, real, BV, etc), but the two
    /// `Ast`s being compared must be the same type.
    //
    // Note that we can't use the binop! macro because of the `pub` keyword on it
    fn _eq(&self, other: &Self) -> Bool<'ctx>
    where
        Self: Sized,
    {
        self._safe_eq(other).unwrap()
    }

    /// Compare this `Ast` with another `Ast`, and get a Result.  Errors if the sort does not
    /// match for the two values.
    fn _safe_eq(&self, other: &Self) -> Result<Bool<'ctx>, SortDiffers<'ctx>>
    where
        Self: Sized,
    {
        assert_eq!(self.get_ctx(), other.get_ctx());

        let left_sort = self.get_sort();
        let right_sort = other.get_sort();
        match left_sort == right_sort {
            true => Ok(unsafe {
                Bool::wrap(self.get_ctx(), {
                    Z3_mk_eq(self.get_ctx().z3_ctx, self.get_z3_ast(), other.get_z3_ast())
                })
            }),
            false => Err(SortDiffers::new(left_sort, right_sort)),
        }
    }

    /// Compare this `Ast` with a list of other `Ast`s, and get a [`Bool`]
    /// which is true only if all arguments (including Self) are pairwise distinct.
    ///
    /// This operation works with all possible `Ast`s (int, real, BV, etc), but the
    /// `Ast`s being compared must all be the same type.
    //
    // Note that we can't use the varop! macro because of the `pub` keyword on it
    fn distinct(ctx: &'ctx Context, values: &[impl Borrow<Self>]) -> Bool<'ctx>
    where
        Self: Sized,
    {
        unsafe {
            Bool::wrap(ctx, {
                assert!(values.len() <= 0xffffffff);
                let values: Vec<Z3_ast> = values
                    .iter()
                    .map(|nodes| nodes.borrow().get_z3_ast())
                    .collect();
                Z3_mk_distinct(ctx.z3_ctx, values.len() as u32, values.as_ptr())
            })
        }
    }

    /// Get the [`Sort`] of the `Ast`.
    fn get_sort(&self) -> Sort<'ctx> {
        unsafe {
            Sort::wrap(
                self.get_ctx(),
                Z3_get_sort(self.get_ctx().z3_ctx, self.get_z3_ast()),
            )
        }
    }

    /// Simplify the `Ast`. Returns a new `Ast` which is equivalent,
    /// but simplified using algebraic simplification rules, such as
    /// constant propagation.
    fn simplify(&self) -> Self
    where
        Self: Sized,
    {
        unsafe {
            Self::wrap(self.get_ctx(), {
                Z3_simplify(self.get_ctx().z3_ctx, self.get_z3_ast())
            })
        }
    }

    /// Performs substitution on the `Ast`. The slice `substitutions` contains a
    /// list of pairs with a "from" `Ast` that will be substituted by a "to" `Ast`.
    fn substitute<T: Ast<'ctx>>(&self, substitutions: &[(&T, &T)]) -> Self
    where
        Self: Sized,
    {
        unsafe {
            Self::wrap(self.get_ctx(), {
                let this_ast = self.get_z3_ast();
                let num_exprs = substitutions.len() as ::std::os::raw::c_uint;
                let mut froms: Vec<_> = vec![];
                let mut tos: Vec<_> = vec![];

                for (from_ast, to_ast) in substitutions {
                    froms.push(from_ast.get_z3_ast());
                    tos.push(to_ast.get_z3_ast());
                }

                Z3_substitute(
                    self.get_ctx().z3_ctx,
                    this_ast,
                    num_exprs,
                    froms.as_ptr(),
                    tos.as_ptr(),
                )
            })
        }
    }

    /// Return the number of children of this `Ast`.
    ///
    /// Leaf nodes (eg `Bool` consts) will return 0.
    fn num_children(&self) -> usize {
        let this_ctx = self.get_ctx().z3_ctx;
        unsafe {
            let this_app = Z3_to_app(this_ctx, self.get_z3_ast());
            Z3_get_app_num_args(this_ctx, this_app) as usize
        }
    }

    /// Return the `n`th child of this `Ast`.
    ///
    /// Out-of-bound indices will return `None`.
    fn nth_child(&self, idx: usize) -> Option<Dynamic<'ctx>> {
        if idx >= self.num_children() {
            None
        } else {
            let idx = u32::try_from(idx).unwrap();
            let this_ctx = self.get_ctx().z3_ctx;
            let child_ast = unsafe {
                let this_app = Z3_to_app(this_ctx, self.get_z3_ast());
                Z3_get_app_arg(this_ctx, this_app, idx)
            };
            Some(unsafe { Dynamic::wrap(self.get_ctx(), child_ast) })
        }
    }

    /// Return the children of this node as a `Vec<Dynamic>`.
    fn children(&self) -> Vec<Dynamic<'ctx>> {
        let n = self.num_children();
        (0..n).map(|i| self.nth_child(i).unwrap()).collect()
    }

    /// Return the `AstKind` for this `Ast`.
    fn kind(&self) -> AstKind {
        unsafe {
            let z3_ctx = self.get_ctx().z3_ctx;
            Z3_get_ast_kind(z3_ctx, self.get_z3_ast())
        }
    }

    /// Return `true` if this is a Z3 function application.
    ///
    /// Note that constants are function applications with 0 arguments.
    fn is_app(&self) -> bool {
        let kind = self.kind();
        kind == AstKind::Numeral || kind == AstKind::App
    }

    /// Return `true` if this is a Z3 constant.
    ///
    /// Note that constants are function applications with 0 arguments.
    fn is_const(&self) -> bool {
        self.is_app() && self.num_children() == 0
    }

    /// Return the `FuncDecl` of the `Ast`.
    ///
    /// This will panic if the `Ast` is not an app, i.e. if [`AstKind`] is not
    /// [`AstKind::App`] or [`AstKind::Numeral`].
    fn decl(&self) -> FuncDecl<'ctx> {
        self.safe_decl().expect("Ast is not an app")
    }

    fn safe_decl(&self) -> Result<FuncDecl<'ctx>, IsNotApp> {
        if !self.is_app() {
            Err(IsNotApp::new(self.kind()))
        } else {
            let ctx = self.get_ctx();
            let func_decl = unsafe {
                let app = Z3_to_app(ctx.z3_ctx, self.get_z3_ast());
                Z3_get_app_decl(ctx.z3_ctx, app)
            };
            Ok(unsafe { FuncDecl::wrap(ctx, func_decl) })
        }
    }
}

macro_rules! impl_ast {
    ($ast:ident) => {
        impl<'ctx> Ast<'ctx> for $ast<'ctx> {
            unsafe fn wrap(ctx: &'ctx Context, ast: Z3_ast) -> Self {
                assert!(!ast.is_null());
                Self {
                    ctx,
                    z3_ast: {
                        debug!(
                            "new ast: id = {}, pointer = {:p}",
                            unsafe { Z3_get_ast_id(ctx.z3_ctx, ast) },
                            ast
                        );
                        unsafe {
                            Z3_inc_ref(ctx.z3_ctx, ast);
                        }
                        ast
                    },
                }
            }

            fn get_ctx(&self) -> &'ctx Context {
                self.ctx
            }

            fn get_z3_ast(&self) -> Z3_ast {
                self.z3_ast
            }
        }

        impl<'ctx> $ast<'ctx> {
            pub fn translate<'dst_ctx>(&self, dest: &'dst_ctx Context) -> $ast<'dst_ctx> {
                unsafe {
                    $ast::wrap(dest, {
                        Z3_translate(self.get_ctx().z3_ctx, self.get_z3_ast(), dest.z3_ctx)
                    })
                }
            }
        }

        impl<'ctx> From<$ast<'ctx>> for Z3_ast {
            fn from(ast: $ast<'ctx>) -> Self {
                ast.z3_ast
            }
        }

        impl<'ctx> PartialEq for $ast<'ctx> {
            fn eq(&self, other: &$ast<'ctx>) -> bool {
                assert_eq!(self.ctx, other.ctx);
                unsafe { Z3_is_eq_ast(self.ctx.z3_ctx, self.z3_ast, other.z3_ast) }
            }
        }

        impl<'ctx> Eq for $ast<'ctx> {}

        impl<'ctx> Clone for $ast<'ctx> {
            fn clone(&self) -> Self {
                debug!(
                    "clone ast: id = {}, pointer = {:p}",
                    unsafe { Z3_get_ast_id(self.ctx.z3_ctx, self.z3_ast) },
                    self.z3_ast
                );
                unsafe { Self::wrap(self.ctx, self.z3_ast) }
            }
        }

        impl<'ctx> Drop for $ast<'ctx> {
            fn drop(&mut self) {
                debug!(
                    "drop ast: id = {}, pointer = {:p}",
                    unsafe { Z3_get_ast_id(self.ctx.z3_ctx, self.z3_ast) },
                    self.z3_ast
                );
                unsafe {
                    Z3_dec_ref(self.ctx.z3_ctx, self.z3_ast);
                }
            }
        }

        impl<'ctx> Hash for $ast<'ctx> {
            fn hash<H: Hasher>(&self, state: &mut H) {
                unsafe {
                    let u = Z3_get_ast_hash(self.ctx.z3_ctx, self.z3_ast);
                    u.hash(state);
                }
            }
        }

        impl<'ctx> fmt::Debug for $ast<'ctx> {
            fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
                let p = unsafe { Z3_ast_to_string(self.ctx.z3_ctx, self.z3_ast) };
                if p.is_null() {
                    return Result::Err(fmt::Error);
                }
                match unsafe { CStr::from_ptr(p) }.to_str() {
                    Ok(s) => write!(f, "{}", s),
                    Err(_) => Result::Err(fmt::Error),
                }
            }
        }

        impl<'ctx> fmt::Display for $ast<'ctx> {
            fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
                <Self as fmt::Debug>::fmt(self, f)
            }
        }
    };
}

macro_rules! impl_from_try_into_dynamic {
    ($ast:ident, $as_ast:ident) => {
        impl<'ctx> From<$ast<'ctx>> for Dynamic<'ctx> {
            fn from(ast: $ast<'ctx>) -> Self {
                unsafe { Dynamic::wrap(ast.ctx, ast.z3_ast) }
            }
        }

        impl<'ctx> From<&$ast<'ctx>> for Dynamic<'ctx> {
            fn from(ast: &$ast<'ctx>) -> Self {
                unsafe { Dynamic::wrap(ast.ctx, ast.z3_ast) }
            }
        }

        impl<'ctx> TryFrom<Dynamic<'ctx>> for $ast<'ctx> {
            type Error = std::string::String;
            fn try_from(ast: Dynamic<'ctx>) -> Result<Self, std::string::String> {
                ast.$as_ast()
                    .ok_or_else(|| format!("Dynamic is not of requested type: {:?}", ast))
            }
        }
    };
}

impl_ast!(Bool);
impl_from_try_into_dynamic!(Bool, as_bool);
impl_ast!(Int);
impl_from_try_into_dynamic!(Int, as_int);
impl_ast!(Real);
impl_from_try_into_dynamic!(Real, as_real);
impl_ast!(Float);
impl_from_try_into_dynamic!(Float, as_float);
impl_ast!(String);
impl_from_try_into_dynamic!(String, as_string);
impl_ast!(BV);
impl_from_try_into_dynamic!(BV, as_bv);
impl_ast!(Array);
impl_from_try_into_dynamic!(Array, as_array);
impl_ast!(Set);
impl_from_try_into_dynamic!(Set, as_set);
impl_ast!(Seq);
impl_from_try_into_dynamic!(Seq, as_seq);
impl_ast!(Regexp);

impl<'ctx> Int<'ctx> {
    pub fn from_big_int(ctx: &'ctx Context, value: &BigInt) -> Int<'ctx> {
        Int::from_str(ctx, &value.to_str_radix(10)).unwrap()
    }

    pub fn from_str(ctx: &'ctx Context, value: &str) -> Option<Int<'ctx>> {
        let sort = Sort::int(ctx);
        let ast = unsafe {
            let int_cstring = CString::new(value).unwrap();
            let numeral_ptr = Z3_mk_numeral(ctx.z3_ctx, int_cstring.as_ptr(), sort.z3_sort);
            if numeral_ptr.is_null() {
                return None;
            }

            numeral_ptr
        };
        Some(unsafe { Int::wrap(ctx, ast) })
    }
}

impl<'ctx> Real<'ctx> {
    pub fn from_big_rational(ctx: &'ctx Context, value: &BigRational) -> Real<'ctx> {
        let num = value.numer();
        let den = value.denom();
        Real::from_real_str(ctx, &num.to_str_radix(10), &den.to_str_radix(10)).unwrap()
    }

    pub fn from_real_str(ctx: &'ctx Context, num: &str, den: &str) -> Option<Real<'ctx>> {
        let sort = Sort::real(ctx);
        let ast = unsafe {
            let fraction_cstring = CString::new(format!("{num:} / {den:}")).unwrap();
            let numeral_ptr = Z3_mk_numeral(ctx.z3_ctx, fraction_cstring.as_ptr(), sort.z3_sort);
            if numeral_ptr.is_null() {
                return None;
            }

            numeral_ptr
        };
        Some(unsafe { Real::wrap(ctx, ast) })
    }
}

impl<'ctx> Float<'ctx> {
    // Create a 32-bit (IEEE-754) Float [`Ast`] from a rust f32
    pub fn from_f32(ctx: &'ctx Context, value: f32) -> Float<'ctx> {
        let sort = Sort::float32(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_fpa_numeral_float(ctx.z3_ctx, value, sort.z3_sort)
            })
        }
    }

    // Create a 364-bit (IEEE-754) Float [`Ast`] from a rust f64
    pub fn from_f64(ctx: &'ctx Context, value: f64) -> Float<'ctx> {
        let sort = Sort::double(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_fpa_numeral_double(ctx.z3_ctx, value, sort.z3_sort)
            })
        }
    }

    pub fn as_f64(&self) -> f64 {
        unsafe { Z3_get_numeral_double(self.ctx.z3_ctx, self.z3_ast) }
    }
}

impl_ast!(Datatype);
impl_from_try_into_dynamic!(Datatype, as_datatype);

impl_ast!(Dynamic);

impl<'ctx> Bool<'ctx> {
    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S) -> Bool<'ctx> {
        let sort = Sort::bool(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str) -> Bool<'ctx> {
        let sort = Sort::bool(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
            })
        }
    }

    pub fn from_bool(ctx: &'ctx Context, b: bool) -> Bool<'ctx> {
        unsafe {
            Self::wrap(ctx, {
                if b {
                    Z3_mk_true(ctx.z3_ctx)
                } else {
                    Z3_mk_false(ctx.z3_ctx)
                }
            })
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        unsafe {
            match Z3_get_bool_value(self.ctx.z3_ctx, self.z3_ast) {
                Z3_L_TRUE => Some(true),
                Z3_L_FALSE => Some(false),
                _ => None,
            }
        }
    }

    // This doesn't quite fit the trinop! macro because of the generic argty
    pub fn ite<T>(&self, a: &T, b: &T) -> T
    where
        T: Ast<'ctx>,
    {
        unsafe {
            T::wrap(self.ctx, {
                Z3_mk_ite(self.ctx.z3_ctx, self.z3_ast, a.get_z3_ast(), b.get_z3_ast())
            })
        }
    }

    varop! {
        and(Z3_mk_and, Self);
        or(Z3_mk_or, Self);
    }
    binop! {
        xor(Z3_mk_xor, Self);
        iff(Z3_mk_iff, Self);
        implies(Z3_mk_implies, Self);
    }
    unop! {
        not(Z3_mk_not, Self);
    }

    pub fn pb_le(ctx: &'ctx Context, values: &[(&Bool<'ctx>, i32)], k: i32) -> Bool<'ctx> {
        unsafe {
            Bool::wrap(ctx, {
                assert!(values.len() <= 0xffffffff);
                let (values, coefficients): (Vec<Z3_ast>, Vec<i32>) = values
                    .iter()
                    .map(|(boolean, coefficient)| (boolean.z3_ast, coefficient))
                    .unzip();
                Z3_mk_pble(
                    ctx.z3_ctx,
                    values.len() as u32,
                    values.as_ptr(),
                    coefficients.as_ptr(),
                    k,
                )
            })
        }
    }
    pub fn pb_ge(ctx: &'ctx Context, values: &[(&Bool<'ctx>, i32)], k: i32) -> Bool<'ctx> {
        unsafe {
            Bool::wrap(ctx, {
                assert!(values.len() <= 0xffffffff);
                let (values, coefficients): (Vec<Z3_ast>, Vec<i32>) = values
                    .iter()
                    .map(|(boolean, coefficient)| (boolean.z3_ast, coefficient))
                    .unzip();
                Z3_mk_pbge(
                    ctx.z3_ctx,
                    values.len() as u32,
                    values.as_ptr(),
                    coefficients.as_ptr(),
                    k,
                )
            })
        }
    }
    pub fn pb_eq(ctx: &'ctx Context, values: &[(&Bool<'ctx>, i32)], k: i32) -> Bool<'ctx> {
        unsafe {
            Bool::wrap(ctx, {
                assert!(values.len() <= 0xffffffff);
                let (values, coefficients): (Vec<Z3_ast>, Vec<i32>) = values
                    .iter()
                    .map(|(boolean, coefficient)| (boolean.z3_ast, coefficient))
                    .unzip();
                Z3_mk_pbeq(
                    ctx.z3_ctx,
                    values.len() as u32,
                    values.as_ptr(),
                    coefficients.as_ptr(),
                    k,
                )
            })
        }
    }
}

pub fn atmost<'a, 'ctx, I: IntoIterator<Item = &'a Bool<'ctx>>>(
    ctx: &'ctx Context,
    args: I,
    k: u32,
) -> Bool<'ctx>
where
    'ctx: 'a,
{
    let args: Vec<_> = args.into_iter().map(|f| f.z3_ast).collect();
    _atmost(ctx, args.as_ref(), k)
}

fn _atmost<'ctx>(ctx: &'ctx Context, args: &[Z3_ast], k: u32) -> Bool<'ctx> {
    unsafe {
        Bool::wrap(
            ctx,
            Z3_mk_atmost(ctx.z3_ctx, args.len().try_into().unwrap(), args.as_ptr(), k),
        )
    }
}

pub fn atleast<'a, 'ctx, I: IntoIterator<Item = &'a Bool<'ctx>>>(
    ctx: &'ctx Context,
    args: I,
    k: u32,
) -> Bool<'ctx>
where
    'ctx: 'a,
{
    let args: Vec<_> = args.into_iter().map(|f| f.z3_ast).collect();
    _atleast(ctx, args.as_ref(), k)
}

fn _atleast<'ctx>(ctx: &'ctx Context, args: &[Z3_ast], k: u32) -> Bool<'ctx> {
    unsafe {
        Bool::wrap(
            ctx,
            Z3_mk_atleast(ctx.z3_ctx, args.len().try_into().unwrap(), args.as_ptr(), k),
        )
    }
}

impl<'ctx> Int<'ctx> {
    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S) -> Int<'ctx> {
        let sort = Sort::int(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str) -> Int<'ctx> {
        let sort = Sort::int(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
            })
        }
    }

    pub fn from_i64(ctx: &'ctx Context, i: i64) -> Int<'ctx> {
        let sort = Sort::int(ctx);
        unsafe { Self::wrap(ctx, Z3_mk_int64(ctx.z3_ctx, i, sort.z3_sort)) }
    }

    pub fn from_u64(ctx: &'ctx Context, u: u64) -> Int<'ctx> {
        let sort = Sort::int(ctx);
        unsafe { Self::wrap(ctx, Z3_mk_unsigned_int64(ctx.z3_ctx, u, sort.z3_sort)) }
    }

    pub fn as_i64(&self) -> Option<i64> {
        unsafe {
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
            let mut tmp: ::std::os::raw::c_ulonglong = 0;
            if Z3_get_numeral_uint64(self.ctx.z3_ctx, self.z3_ast, &mut tmp) {
                Some(tmp)
            } else {
                None
            }
        }
    }

    pub fn from_real(ast: &Real<'ctx>) -> Int<'ctx> {
        unsafe { Self::wrap(ast.ctx, Z3_mk_real2int(ast.ctx.z3_ctx, ast.z3_ast)) }
    }

    /// Create a real from an integer.
    /// This is just a convenience wrapper around
    /// [`Real::from_int()`]; see notes there.
    pub fn to_real(&self) -> Real<'ctx> {
        Real::from_int(self)
    }

    /// Create an integer from a bitvector.
    ///
    /// Signed and unsigned version.
    ///
    /// # Examples
    /// ```
    /// # use z3::{ast, Config, Context, SatResult, Solver};
    /// # use z3::ast::Ast;
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// let bv = ast::BV::new_const(&ctx, "x", 32);
    /// solver.assert(&bv._eq(&ast::BV::from_i64(&ctx, -3, 32)));
    ///
    /// let x = ast::Int::from_bv(&bv, true);
    ///
    /// assert_eq!(solver.check(), SatResult::Sat);
    /// let model = solver.get_model().unwrap();
    ///
    /// assert_eq!(-3, model.eval(&x, true).unwrap().as_i64().unwrap());
    /// ```
    pub fn from_bv(ast: &BV<'ctx>, signed: bool) -> Int<'ctx> {
        unsafe {
            Self::wrap(ast.ctx, {
                Z3_mk_bv2int(ast.ctx.z3_ctx, ast.z3_ast, signed)
            })
        }
    }

    /// Create a bitvector from an integer.
    /// This is just a convenience wrapper around
    /// [`BV::from_int()`]; see notes there.
    pub fn to_ast(&self, sz: u32) -> BV<'ctx> {
        BV::from_int(self, sz)
    }

    varop! {
        add(Z3_mk_add, Self);
        sub(Z3_mk_sub, Self);
        mul(Z3_mk_mul, Self);
    }
    unop! {
        unary_minus(Z3_mk_unary_minus, Self);
    }
    binop! {
        div(Z3_mk_div, Self);
        rem(Z3_mk_rem, Self);
        modulo(Z3_mk_mod, Self);
        power(Z3_mk_power, Real<'ctx>);
        lt(Z3_mk_lt, Bool<'ctx>);
        le(Z3_mk_le, Bool<'ctx>);
        gt(Z3_mk_gt, Bool<'ctx>);
        ge(Z3_mk_ge, Bool<'ctx>);
    }
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
    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S) -> Real<'ctx> {
        let sort = Sort::real(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str) -> Real<'ctx> {
        let sort = Sort::real(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
            })
        }
    }

    pub fn from_real(ctx: &'ctx Context, num: i32, den: i32) -> Real<'ctx> {
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_real(
                    ctx.z3_ctx,
                    num as ::std::os::raw::c_int,
                    den as ::std::os::raw::c_int,
                )
            })
        }
    }

    pub fn as_real(&self) -> Option<(i64, i64)> {
        unsafe {
            let mut num: i64 = 0;
            let mut den: i64 = 0;
            if Z3_get_numeral_small(self.ctx.z3_ctx, self.z3_ast, &mut num, &mut den) {
                Some((num, den))
            } else {
                None
            }
        }
    }

    pub fn approx(&self, precision: usize) -> ::std::string::String {
        let s = unsafe {
            CStr::from_ptr(Z3_get_numeral_decimal_string(
                self.ctx.z3_ctx,
                self.z3_ast,
                precision as _,
            ))
        }
        .to_str()
        .unwrap();
        s.strip_suffix('?').unwrap_or(s).to_owned()
    }
    pub fn approx_f64(&self) -> f64 {
        self.approx(17).parse().unwrap() // 17 decimal digits needed to get full f64 precision
    }

    pub fn from_int(ast: &Int<'ctx>) -> Real<'ctx> {
        unsafe { Self::wrap(ast.ctx, Z3_mk_int2real(ast.ctx.z3_ctx, ast.z3_ast)) }
    }

    /// Create an integer from a real.
    /// This is just a convenience wrapper around
    /// [`Int::from_real()`]; see notes there.
    pub fn to_int(&self) -> Int<'ctx> {
        Int::from_real(self)
    }

    unop! {
        is_int(Z3_mk_is_int, Bool<'ctx>);
    }

    varop! {
        add(Z3_mk_add, Self);
        sub(Z3_mk_sub, Self);
        mul(Z3_mk_mul, Self);
    }
    unop! {
        unary_minus(Z3_mk_unary_minus, Self);
    }
    binop! {
        div(Z3_mk_div, Self);
        power(Z3_mk_power, Self);
        lt(Z3_mk_lt, Bool<'ctx>);
        le(Z3_mk_le, Bool<'ctx>);
        gt(Z3_mk_gt, Bool<'ctx>);
        ge(Z3_mk_ge, Bool<'ctx>);
    }
}

impl<'ctx> Float<'ctx> {
    pub fn new_const<S: Into<Symbol>>(
        ctx: &'ctx Context,
        name: S,
        ebits: u32,
        sbits: u32,
    ) -> Float<'ctx> {
        let sort = Sort::float(ctx, ebits, sbits);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    /// Create a 32-bit (IEEE-754) Float [`Ast`].
    pub fn new_const_float32<S: Into<Symbol>>(ctx: &'ctx Context, name: S) -> Float<'ctx> {
        let sort = Sort::float32(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    /// Create a 64-bit (IEEE-754) Float [`Ast`].
    pub fn new_const_double<S: Into<Symbol>>(ctx: &'ctx Context, name: S) -> Float<'ctx> {
        let sort = Sort::double(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, ebits: u32, sbits: u32) -> Float<'ctx> {
        let sort = Sort::float(ctx, ebits, sbits);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
            })
        }
    }

    pub fn fresh_const_float32(ctx: &'ctx Context, prefix: &str) -> Float<'ctx> {
        let sort = Sort::float32(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
            })
        }
    }

    pub fn fresh_const_double(ctx: &'ctx Context, prefix: &str) -> Float<'ctx> {
        let sort = Sort::double(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
            })
        }
    }

    // returns RoundingMode towards zero
    pub fn round_towards_zero(ctx: &'ctx Context) -> Float<'ctx> {
        unsafe { Self::wrap(ctx, Z3_mk_fpa_round_toward_zero(ctx.z3_ctx)) }
    }

    // returns RoundingMode towards negative
    pub fn round_towards_negative(ctx: &'ctx Context) -> Float<'ctx> {
        unsafe { Self::wrap(ctx, Z3_mk_fpa_round_toward_negative(ctx.z3_ctx)) }
    }

    // returns RoundingMode towards positive
    pub fn round_towards_positive(ctx: &'ctx Context) -> Float<'ctx> {
        unsafe { Self::wrap(ctx, Z3_mk_fpa_round_toward_positive(ctx.z3_ctx)) }
    }

    // Add two floats of the same size, rounding towards zero
    pub fn add_towards_zero(&self, other: &Self) -> Float<'ctx> {
        Self::round_towards_zero(self.ctx).add(self, other)
    }

    // Subtract two floats of the same size, rounding towards zero
    pub fn sub_towards_zero(&self, other: &Self) -> Float<'ctx> {
        Self::round_towards_zero(self.ctx).sub(self, other)
    }

    // Multiply two floats of the same size, rounding towards zero
    pub fn mul_towards_zero(&self, other: &Self) -> Float<'ctx> {
        Self::round_towards_zero(self.ctx).mul(self, other)
    }

    // Divide two floats of the same size, rounding towards zero
    pub fn div_towards_zero(&self, other: &Self) -> Float<'ctx> {
        Self::round_towards_zero(self.ctx).div(self, other)
    }

    // Convert to IEEE-754 bit-vector
    pub fn to_ieee_bv(&self) -> BV<'ctx> {
        unsafe { BV::wrap(self.ctx, Z3_mk_fpa_to_ieee_bv(self.ctx.z3_ctx, self.z3_ast)) }
    }

    /// NaN for an arbitrary FP sort.
    pub fn nan(ctx: &'ctx Context, sort: &Sort<'ctx>) -> Float<'ctx> {
        debug_assert!(matches!(sort.kind(), SortKind::FloatingPoint));
        unsafe { Self::wrap(ctx, Z3_mk_fpa_nan(ctx.z3_ctx, sort.z3_sort)) }
    }

    /// Convenience IEEE-754 single & double.
    pub fn nan32(ctx: &'ctx Context) -> Float<'ctx> {
        let s = Sort::float(ctx, 8, 24);
        Self::nan(ctx, &s)
    }
    pub fn nan64(ctx: &'ctx Context) -> Float<'ctx> {
        let s = Sort::float(ctx, 11, 53);
        Self::nan(ctx, &s)
    }

    unop! {
        unary_abs(Z3_mk_fpa_abs, Self);
        unary_neg(Z3_mk_fpa_neg, Self);
        is_infinite(Z3_mk_fpa_is_infinite, Bool<'ctx>);
        is_normal(Z3_mk_fpa_is_normal, Bool<'ctx>);
        is_subnormal(Z3_mk_fpa_is_subnormal, Bool<'ctx>);
        is_zero(Z3_mk_fpa_is_zero, Bool<'ctx>);
        is_nan(Z3_mk_fpa_is_nan, Bool<'ctx>);
    }
    binop! {
        lt(Z3_mk_fpa_lt, Bool<'ctx>);
        le(Z3_mk_fpa_leq, Bool<'ctx>);
        gt(Z3_mk_fpa_gt, Bool<'ctx>);
        ge(Z3_mk_fpa_geq, Bool<'ctx>);
    }
    trinop! {
        add(Z3_mk_fpa_add, Self);
        sub(Z3_mk_fpa_sub, Self);
        mul(Z3_mk_fpa_mul, Self);
        div(Z3_mk_fpa_div, Self);
    }
}

impl<'ctx> String<'ctx> {
    /// Creates a new constant using the built-in string sort
    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S) -> String<'ctx> {
        let sort = Sort::string(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    /// Creates a fresh constant using the built-in string sort
    pub fn fresh_const(ctx: &'ctx Context, prefix: &str) -> String<'ctx> {
        let sort = Sort::string(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
            })
        }
    }

    /// Creates a Z3 constant string from a `&str`
    pub fn from_str(ctx: &'ctx Context, string: &str) -> Result<String<'ctx>, std::ffi::NulError> {
        let string = CString::new(string)?;
        Ok(unsafe {
            Self::wrap(ctx, {
                Z3_mk_string(ctx.z3_ctx, string.as_c_str().as_ptr())
            })
        })
    }

    /// Retrieves the underlying `std::string::String`
    ///
    /// If this is not a constant `z3::ast::String`, return `None`.
    ///
    /// Note that `to_string()` provided by `std::string::ToString` (which uses
    /// `std::fmt::Display`) returns an escaped string. In contrast,
    /// `z3::ast::String::from_str(&ctx, s).unwrap().as_string()` returns a
    /// `String` equal to the original value.
    pub fn as_string(&self) -> Option<std::string::String> {
        let z3_ctx = self.get_ctx().z3_ctx;
        unsafe {
            let bytes = Z3_get_string(z3_ctx, self.get_z3_ast());
            if bytes.is_null() {
                None
            } else {
                Some(CStr::from_ptr(bytes).to_string_lossy().into_owned())
            }
        }
    }

    /// Retrieve the substring of length 1 positioned at `index`.
    ///
    /// # Examples
    /// ```
    /// # use z3::{Config, Context, Solver};
    /// # use z3::ast::{Ast as _, Int};
    /// #
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// #
    /// let s = z3::ast::String::fresh_const(&ctx, "");
    ///
    /// solver.assert(
    ///     &s.at(&Int::from_u64(&ctx, 0))
    ///         ._eq(&z3::ast::String::from_str(&ctx, "a").unwrap())
    /// );
    /// assert_eq!(solver.check(), z3::SatResult::Sat);
    /// ```
    pub fn at(&self, index: &Int<'ctx>) -> Self {
        unsafe {
            Self::wrap(
                self.ctx,
                Z3_mk_seq_at(self.ctx.z3_ctx, self.z3_ast, index.z3_ast),
            )
        }
    }

    /// Retrieve the substring of length `length` starting at `offset`.
    ///
    /// # Examples
    /// ```
    /// # use z3::{Config, Context, Solver, SatResult};
    /// # use z3::ast::{Ast as _, Int, String};
    /// #
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// #
    /// let s = String::from_str(&ctx, "abc").unwrap();
    /// let sub = String::fresh_const(&ctx, "");
    ///
    /// solver.assert(
    ///     &sub._eq(
    ///         &s.substr(
    ///             &Int::from_u64(&ctx, 1),
    ///             &Int::from_u64(&ctx, 2),
    ///         )
    ///     )
    /// );
    ///
    /// assert_eq!(solver.check(), SatResult::Sat);
    /// assert_eq!(
    ///     solver
    ///         .get_model()
    ///         .unwrap()
    ///         .eval(&sub, true)
    ///         .unwrap()
    ///         .as_string()
    ///         .unwrap()
    ///         .as_str(),
    ///     "bc",
    /// );
    /// ```
    pub fn substr(&self, offset: &Int<'ctx>, length: &Int<'ctx>) -> Self {
        unsafe {
            Self::wrap(
                self.ctx,
                Z3_mk_seq_extract(self.ctx.z3_ctx, self.z3_ast, offset.z3_ast, length.z3_ast),
            )
        }
    }

    /// Checks if this string matches a `z3::ast::Regexp`
    pub fn regex_matches(&self, regex: &Regexp) -> Bool<'ctx> {
        assert!(self.ctx == regex.ctx);
        unsafe {
            Bool::wrap(
                self.ctx,
                Z3_mk_seq_in_re(self.ctx.z3_ctx, self.get_z3_ast(), regex.get_z3_ast()),
            )
        }
    }

    varop! {
        /// Appends the argument strings to `Self`
        concat(Z3_mk_seq_concat, String<'ctx>);
    }

    unop! {
        /// Gets the length of `Self`.
        length(Z3_mk_seq_length, Int<'ctx>);
    }

    binop! {
        /// Checks whether `Self` contains a substring
        contains(Z3_mk_seq_contains, Bool<'ctx>);
        /// Checks whether `Self` is a prefix of the argument
        prefix(Z3_mk_seq_prefix, Bool<'ctx>);
        /// Checks whether `Self` is a suffix of the argument
        suffix(Z3_mk_seq_suffix, Bool<'ctx>);
    }
}

macro_rules! bv_overflow_check_signed {
    (
        $(
            $( #[ $attr:meta ] )* $f:ident ( $z3fn:ident ) ;
        )*
    ) => {
        $(
            $( #[ $attr ] )*
            pub fn $f(&self, other: &BV<'ctx>, b: bool) -> Bool<'ctx> {
                unsafe {
                    Ast::wrap(self.ctx, {
                        $z3fn(self.ctx.z3_ctx, self.z3_ast, other.z3_ast, b)
                    })
                }
            }
        )*
    };
}

impl<'ctx> BV<'ctx> {
    pub fn from_str(ctx: &'ctx Context, sz: u32, value: &str) -> Option<BV<'ctx>> {
        let sort = Sort::bitvector(ctx, sz);
        let ast = unsafe {
            let bv_cstring = CString::new(value).unwrap();
            let numeral_ptr = Z3_mk_numeral(ctx.z3_ctx, bv_cstring.as_ptr(), sort.z3_sort);
            if numeral_ptr.is_null() {
                return None;
            }

            numeral_ptr
        };
        Some(unsafe { Self::wrap(ctx, ast) })
    }

    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S, sz: u32) -> BV<'ctx> {
        let sort = Sort::bitvector(ctx, sz);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, sz: u32) -> BV<'ctx> {
        let sort = Sort::bitvector(ctx, sz);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
            })
        }
    }

    pub fn from_i64(ctx: &'ctx Context, i: i64, sz: u32) -> BV<'ctx> {
        let sort = Sort::bitvector(ctx, sz);
        unsafe { Self::wrap(ctx, Z3_mk_int64(ctx.z3_ctx, i, sort.z3_sort)) }
    }

    pub fn from_u64(ctx: &'ctx Context, u: u64, sz: u32) -> BV<'ctx> {
        let sort = Sort::bitvector(ctx, sz);
        unsafe { Self::wrap(ctx, Z3_mk_unsigned_int64(ctx.z3_ctx, u, sort.z3_sort)) }
    }

    pub fn as_i64(&self) -> Option<i64> {
        unsafe {
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
    /// # use z3::{ast, Config, Context, SatResult, Solver};
    /// # use z3::ast::Ast;
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// let i = ast::Int::new_const(&ctx, "x");
    /// solver.assert(&i._eq(&ast::Int::from_i64(&ctx, -3)));
    ///
    /// let x = ast::BV::from_int(&i, 64);
    /// assert_eq!(64, x.get_size());
    ///
    /// assert_eq!(solver.check(), SatResult::Sat);
    /// let model = solver.get_model().unwrap();;
    ///
    /// assert_eq!(-3, model.eval(&x.to_int(true), true).unwrap().as_i64().expect("as_i64() shouldn't fail"));
    /// ```
    pub fn from_int(ast: &Int<'ctx>, sz: u32) -> BV<'ctx> {
        unsafe { Self::wrap(ast.ctx, Z3_mk_int2bv(ast.ctx.z3_ctx, sz, ast.z3_ast)) }
    }

    /// Create an integer from a bitvector.
    /// This is just a convenience wrapper around
    /// [`Int::from_bv()`]; see notes there.
    pub fn to_int(&self, signed: bool) -> Int<'ctx> {
        Int::from_bv(self, signed)
    }

    /// Get the size of the bitvector (in bits)
    pub fn get_size(&self) -> u32 {
        let sort = self.get_sort();
        unsafe { Z3_get_bv_sort_size(self.ctx.z3_ctx, sort.z3_sort) }
    }

    // Bitwise ops
    unop! {
        /// Bitwise negation
        bvnot(Z3_mk_bvnot, Self);
        /// Two's complement negation
        bvneg(Z3_mk_bvneg, Self);
        /// Conjunction of all the bits in the vector. Returns a BV with size (bitwidth) 1.
        bvredand(Z3_mk_bvredand, Self);
        /// Disjunction of all the bits in the vector. Returns a BV with size (bitwidth) 1.
        bvredor(Z3_mk_bvredor, Self);
    }
    binop! {
        /// Bitwise and
        bvand(Z3_mk_bvand, Self);
        /// Bitwise or
        bvor(Z3_mk_bvor, Self);
        /// Bitwise exclusive-or
        bvxor(Z3_mk_bvxor, Self);
        /// Bitwise nand
        bvnand(Z3_mk_bvnand, Self);
        /// Bitwise nor
        bvnor(Z3_mk_bvnor, Self);
        /// Bitwise xnor
        bvxnor(Z3_mk_bvxnor, Self);
    }

    // Arithmetic ops
    binop! {
        /// Addition
        bvadd(Z3_mk_bvadd, Self);
        /// Subtraction
        bvsub(Z3_mk_bvsub, Self);
        /// Multiplication
        bvmul(Z3_mk_bvmul, Self);
        /// Unsigned division
        bvudiv(Z3_mk_bvudiv, Self);
        /// Signed division
        bvsdiv(Z3_mk_bvsdiv, Self);
        /// Unsigned remainder
        bvurem(Z3_mk_bvurem, Self);
        /// Signed remainder (sign follows dividend)
        bvsrem(Z3_mk_bvsrem, Self);
        /// Signed remainder (sign follows divisor)
        bvsmod(Z3_mk_bvsmod, Self);
    }

    // Comparison ops
    binop! {
        /// Unsigned less than
        bvult(Z3_mk_bvult, Bool<'ctx>);
        /// Signed less than
        bvslt(Z3_mk_bvslt, Bool<'ctx>);
        /// Unsigned less than or equal
        bvule(Z3_mk_bvule, Bool<'ctx>);
        /// Signed less than or equal
        bvsle(Z3_mk_bvsle, Bool<'ctx>);
        /// Unsigned greater or equal
        bvuge(Z3_mk_bvuge, Bool<'ctx>);
        /// Signed greater or equal
        bvsge(Z3_mk_bvsge, Bool<'ctx>);
        /// Unsigned greater than
        bvugt(Z3_mk_bvugt, Bool<'ctx>);
        /// Signed greater than
        bvsgt(Z3_mk_bvsgt, Bool<'ctx>);
    }

    // Shift ops
    binop! {
        /// Shift left
        bvshl(Z3_mk_bvshl, Self);
        /// Logical shift right (add zeroes in the high bits)
        bvlshr(Z3_mk_bvlshr, Self);
        /// Arithmetic shift right (sign-extend in the high bits)
        bvashr(Z3_mk_bvashr, Self);
        /// Rotate left
        bvrotl(Z3_mk_ext_rotate_left, Self);
        /// Rotate right
        bvrotr(Z3_mk_ext_rotate_right, Self);
    }

    binop! {
        /// Concatenate two bitvectors
        concat(Z3_mk_concat, Self);
    }

    // overflow checks
    unop! {
        /// Check if negation overflows
        bvneg_no_overflow(Z3_mk_bvneg_no_overflow, Bool<'ctx>);
    }
    bv_overflow_check_signed! {
        /// Check if addition overflows
        bvadd_no_overflow(Z3_mk_bvadd_no_overflow);
        /// Check if subtraction underflows
        bvsub_no_underflow(Z3_mk_bvsub_no_underflow);
        /// Check if multiplication overflows
        bvmul_no_overflow(Z3_mk_bvmul_no_overflow);
    }
    binop! {
        /// Check if addition underflows
        bvadd_no_underflow(Z3_mk_bvadd_no_underflow, Bool<'ctx>);
        /// Check if subtraction overflows
        bvsub_no_overflow(Z3_mk_bvsub_no_overflow, Bool<'ctx>);
        /// Check if signed division overflows
        bvsdiv_no_overflow(Z3_mk_bvsdiv_no_overflow, Bool<'ctx>);
        /// Check if multiplication underflows
        bvmul_no_underflow(Z3_mk_bvmul_no_underflow, Bool<'ctx>);
    }

    /// Extract the bits `high` down to `low` from the bitvector.
    /// Returns a bitvector of size `n`, where `n = high - low + 1`.
    pub fn extract(&self, high: u32, low: u32) -> Self {
        unsafe {
            Self::wrap(self.ctx, {
                Z3_mk_extract(self.ctx.z3_ctx, high, low, self.z3_ast)
            })
        }
    }

    /// Sign-extend the bitvector to size `m+i`, where `m` is the original size of the bitvector.
    /// That is, `i` bits will be added.
    pub fn sign_ext(&self, i: u32) -> Self {
        unsafe {
            Self::wrap(self.ctx, {
                Z3_mk_sign_ext(self.ctx.z3_ctx, i, self.z3_ast)
            })
        }
    }

    /// Zero-extend the bitvector to size `m+i`, where `m` is the original size of the bitvector.
    /// That is, `i` bits will be added.
    pub fn zero_ext(&self, i: u32) -> Self {
        unsafe {
            Self::wrap(self.ctx, {
                Z3_mk_zero_ext(self.ctx.z3_ctx, i, self.z3_ast)
            })
        }
    }
}

impl<'ctx> Array<'ctx> {
    /// Create an `Array` which maps from indices of the `domain` `Sort` to
    /// values of the `range` `Sort`.
    ///
    /// All values in the `Array` will be unconstrained.
    pub fn new_const<S: Into<Symbol>>(
        ctx: &'ctx Context,
        name: S,
        domain: &Sort<'ctx>,
        range: &Sort<'ctx>,
    ) -> Array<'ctx> {
        let sort = Sort::array(ctx, domain, range);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    pub fn fresh_const(
        ctx: &'ctx Context,
        prefix: &str,
        domain: &Sort<'ctx>,
        range: &Sort<'ctx>,
    ) -> Array<'ctx> {
        let sort = Sort::array(ctx, domain, range);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
            })
        }
    }

    /// Create a "constant array", that is, an `Array` initialized so that all of the
    /// indices in the `domain` map to the given value `val`
    pub fn const_array<A>(ctx: &'ctx Context, domain: &Sort<'ctx>, val: &A) -> Array<'ctx>
    where
        A: Ast<'ctx>,
    {
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const_array(ctx.z3_ctx, domain.z3_sort, val.get_z3_ast())
            })
        }
    }

    /// Get the value at a given index in the array.
    ///
    /// Note that the `index` _must be_ of the array's `domain` sort.
    /// The return type will be of the array's `range` sort.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn select<A>(&self, index: &A) -> Dynamic<'ctx>
    where
        A: Ast<'ctx>,
    {
        // TODO: We could validate here that the index is of the correct type.
        // This would require us either to keep around the original `domain` argument
        // from when the Array was constructed, or to do an additional Z3 query
        // to find the domain sort first.
        // But if we did this check ourselves, we'd just panic, so it doesn't seem
        // like a huge advantage over just letting Z3 panic itself when it discovers the
        // problem.
        // This way we also avoid the redundant check every time this method is called.
        unsafe {
            Dynamic::wrap(self.ctx, {
                Z3_mk_select(self.ctx.z3_ctx, self.z3_ast, index.get_z3_ast())
            })
        }
    }

    /// n-ary Array read. `idxs` are the indices of the array that gets read.
    /// This is useful for applying lambdas.
    pub fn select_n(&self, idxs: &[&dyn Ast]) -> Dynamic<'ctx> {
        let idxs: Vec<_> = idxs.iter().map(|idx| idx.get_z3_ast()).collect();

        unsafe {
            Dynamic::wrap(self.ctx, {
                Z3_mk_select_n(
                    self.ctx.z3_ctx,
                    self.z3_ast,
                    idxs.len().try_into().unwrap(),
                    idxs.as_ptr() as *const Z3_ast,
                )
            })
        }
    }

    /// Update the value at a given index in the array.
    ///
    /// Note that the `index` _must be_ of the array's `domain` sort,
    /// and the `value` _must be_ of the array's `range` sort.
    //
    // We avoid the trinop! macro because the arguments have non-Self types
    pub fn store<A1, A2>(&self, index: &A1, value: &A2) -> Self
    where
        A1: Ast<'ctx>,
        A2: Ast<'ctx>,
    {
        unsafe {
            Self::wrap(self.ctx, {
                Z3_mk_store(
                    self.ctx.z3_ctx,
                    self.z3_ast,
                    index.get_z3_ast(),
                    value.get_z3_ast(),
                )
            })
        }
    }

    /// Returns true if the array is a const array (i.e. `a.is_const_array() => exists v, forall i. select(a, i) == v`)
    ///
    /// # Examples
    /// ```
    /// # use z3::{ast, Config, Context, ast::{Array, Int}, Sort};
    /// # use z3::ast::Ast;
    /// # use std::convert::TryInto;
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let arr = Array::const_array(&ctx, &Sort::int(&ctx), &Int::from_u64(&ctx, 9));
    /// assert!(arr.is_const_array());
    /// let arr2 = Array::fresh_const(&ctx, "a", &Sort::int(&ctx), &Sort::int(&ctx));
    /// assert!(!arr2.is_const_array());
    /// ```
    pub fn is_const_array(&self) -> bool {
        // python:
        // is_app_of(a, Z3_OP_CONST_ARRAY)
        // >> is_app(a) and a.decl().kind() == Z3_OP_CONST_ARRAY
        self.is_app() && matches!(self.decl().kind(), DeclKind::CONST_ARRAY)
    }
}

impl<'ctx> Set<'ctx> {
    pub fn new_const<S: Into<Symbol>>(
        ctx: &'ctx Context,
        name: S,
        eltype: &Sort<'ctx>,
    ) -> Set<'ctx> {
        let sort = Sort::set(ctx, eltype);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, eltype: &Sort<'ctx>) -> Set<'ctx> {
        let sort = Sort::set(ctx, eltype);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
            })
        }
    }

    /// Creates a set that maps the domain to false by default
    pub fn empty(ctx: &'ctx Context, domain: &Sort<'ctx>) -> Set<'ctx> {
        unsafe { Self::wrap(ctx, Z3_mk_empty_set(ctx.z3_ctx, domain.z3_sort)) }
    }

    /// Add an element to the set.
    ///
    /// Note that the `element` _must be_ of the `Set`'s `eltype` sort.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn add<A>(&self, element: &A) -> Set<'ctx>
    where
        A: Ast<'ctx>,
    {
        unsafe {
            Self::wrap(self.ctx, {
                Z3_mk_set_add(self.ctx.z3_ctx, self.z3_ast, element.get_z3_ast())
            })
        }
    }

    /// Remove an element from the set.
    ///
    /// Note that the `element` _must be_ of the `Set`'s `eltype` sort.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn del<A>(&self, element: &A) -> Set<'ctx>
    where
        A: Ast<'ctx>,
    {
        unsafe {
            Self::wrap(self.ctx, {
                Z3_mk_set_del(self.ctx.z3_ctx, self.z3_ast, element.get_z3_ast())
            })
        }
    }

    /// Check if an item is a member of the set.
    ///
    /// Note that the `element` _must be_ of the `Set`'s `eltype` sort.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn member<A>(&self, element: &A) -> Bool<'ctx>
    where
        A: Ast<'ctx>,
    {
        unsafe {
            Bool::wrap(self.ctx, {
                Z3_mk_set_member(self.ctx.z3_ctx, element.get_z3_ast(), self.z3_ast)
            })
        }
    }

    varop! {
        /// Take the intersection of a list of sets.
        intersect(Z3_mk_set_intersect, Self);
        /// Take the union of a list of sets.
        set_union(Z3_mk_set_union, Self);
    }
    unop! {
        /// Take the complement of the set.
        complement(Z3_mk_set_complement, Self);
    }
    binop! {
        /// Check if the set is a subset of another set.
        set_subset(Z3_mk_set_subset, Bool<'ctx>);
        /// Take the set difference between two sets.
        difference(Z3_mk_set_difference, Self);
    }
}

impl<'ctx> Seq<'ctx> {
    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S, eltype: &Sort<'ctx>) -> Self {
        let sort = Sort::seq(ctx, eltype);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, eltype: &Sort<'ctx>) -> Self {
        let sort = Sort::seq(ctx, eltype);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
            })
        }
    }

    /// Create a unit sequence of `a`.
    pub fn unit<A: Ast<'ctx>>(ctx: &'ctx Context, a: &A) -> Self {
        unsafe { Self::wrap(ctx, Z3_mk_seq_unit(ctx.z3_ctx, a.get_z3_ast())) }
    }

    /// Retrieve the unit sequence positioned at position `index`.
    /// Use [`Seq::nth`] to get just the element.
    pub fn at(&self, index: &Int<'ctx>) -> Self {
        unsafe {
            Self::wrap(
                self.ctx,
                Z3_mk_seq_at(self.ctx.z3_ctx, self.z3_ast, index.z3_ast),
            )
        }
    }

    /// Retrieve the element positioned at position `index`.
    ///
    /// # Examples
    /// ```
    /// # use z3::{ast, Config, Context, Solver, Sort};
    /// # use z3::ast::{Ast, Bool, Int, Seq};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// let seq = Seq::fresh_const(&ctx, "", &Sort::bool(&ctx));
    ///
    /// solver.assert(
    ///     &seq.nth(&Int::from_u64(&ctx, 0))
    ///         .simplify()
    ///         .as_bool()
    ///         .unwrap()
    ///         ._eq(&Bool::from_bool(&ctx, true))
    /// );
    /// ```
    pub fn nth(&self, index: &Int<'ctx>) -> Dynamic<'ctx> {
        unsafe {
            Dynamic::wrap(
                self.ctx,
                Z3_mk_seq_nth(self.ctx.z3_ctx, self.z3_ast, index.z3_ast),
            )
        }
    }

    pub fn length(&self) -> Int<'ctx> {
        unsafe { Int::wrap(self.ctx, Z3_mk_seq_length(self.ctx.z3_ctx, self.z3_ast)) }
    }

    varop! {
        /// Concatenate sequences.
        concat(Z3_mk_seq_concat, Self);
    }
}

impl<'ctx> Dynamic<'ctx> {
    pub fn from_ast(ast: &dyn Ast<'ctx>) -> Self {
        unsafe { Self::wrap(ast.get_ctx(), ast.get_z3_ast()) }
    }

    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S, sort: &Sort<'ctx>) -> Self {
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_const(ctx.z3_ctx, name.into().as_z3_symbol(ctx), sort.z3_sort),
            )
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, sort: &Sort<'ctx>) -> Self {
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
            })
        }
    }

    pub fn sort_kind(&self) -> SortKind {
        unsafe { Z3_get_sort_kind(self.ctx.z3_ctx, Z3_get_sort(self.ctx.z3_ctx, self.z3_ast)) }
    }

    /// Returns `None` if the `Dynamic` is not actually a `Bool`
    pub fn as_bool(&self) -> Option<Bool<'ctx>> {
        match self.sort_kind() {
            SortKind::Bool => Some(unsafe { Bool::wrap(self.ctx, self.z3_ast) }),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually an `Int`
    pub fn as_int(&self) -> Option<Int<'ctx>> {
        match self.sort_kind() {
            SortKind::Int => Some(unsafe { Int::wrap(self.ctx, self.z3_ast) }),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `Real`
    pub fn as_real(&self) -> Option<Real<'ctx>> {
        match self.sort_kind() {
            SortKind::Real => Some(unsafe { Real::wrap(self.ctx, self.z3_ast) }),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `Float`
    pub fn as_float(&self) -> Option<Float<'ctx>> {
        match self.sort_kind() {
            SortKind::FloatingPoint => Some(unsafe { Float::wrap(self.ctx, self.z3_ast) }),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `String`
    pub fn as_string(&self) -> Option<String<'ctx>> {
        unsafe {
            if Z3_is_string_sort(self.ctx.z3_ctx, Z3_get_sort(self.ctx.z3_ctx, self.z3_ast)) {
                Some(String::wrap(self.ctx, self.z3_ast))
            } else {
                None
            }
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `BV`
    pub fn as_bv(&self) -> Option<BV<'ctx>> {
        match self.sort_kind() {
            SortKind::BV => Some(unsafe { BV::wrap(self.ctx, self.z3_ast) }),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually an `Array`
    pub fn as_array(&self) -> Option<Array<'ctx>> {
        match self.sort_kind() {
            SortKind::Array => Some(unsafe { Array::wrap(self.ctx, self.z3_ast) }),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `Set`
    pub fn as_set(&self) -> Option<Set<'ctx>> {
        unsafe {
            match self.sort_kind() {
                SortKind::Array => {
                    match Z3_get_sort_kind(
                        self.ctx.z3_ctx,
                        Z3_get_array_sort_range(
                            self.ctx.z3_ctx,
                            Z3_get_sort(self.ctx.z3_ctx, self.z3_ast),
                        ),
                    ) {
                        SortKind::Bool => Some(Set::wrap(self.ctx, self.z3_ast)),
                        _ => None,
                    }
                }
                _ => None,
            }
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `Seq`.
    pub fn as_seq(&self) -> Option<Seq<'ctx>> {
        match self.sort_kind() {
            SortKind::Seq => Some(unsafe { Seq::wrap(self.ctx, self.z3_ast) }),
            _ => None,
        }
    }

    /// Returns `None` if the `Dynamic` is not actually a `Datatype`
    pub fn as_datatype(&self) -> Option<Datatype<'ctx>> {
        match self.sort_kind() {
            SortKind::Datatype => Some(unsafe { Datatype::wrap(self.ctx, self.z3_ast) }),
            _ => None,
        }
    }
}

impl<'ctx> Datatype<'ctx> {
    pub fn new_const<S: Into<Symbol>>(ctx: &'ctx Context, name: S, sort: &Sort<'ctx>) -> Self {
        assert_eq!(ctx, sort.ctx);
        assert_eq!(sort.kind(), SortKind::Datatype);

        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, sort: &Sort<'ctx>) -> Self {
        assert_eq!(ctx, sort.ctx);
        assert_eq!(sort.kind(), SortKind::Datatype);

        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
            })
        }
    }
}

impl<'ctx> Regexp<'ctx> {
    /// Creates a regular expression that recognizes the string given as parameter
    pub fn literal(ctx: &'ctx Context, s: &str) -> Self {
        unsafe {
            Self::wrap(ctx, {
                let c_str = CString::new(s).unwrap();
                Z3_mk_seq_to_re(ctx.z3_ctx, Z3_mk_string(ctx.z3_ctx, c_str.as_ptr()))
            })
        }
    }

    /// Creates a regular expression that recognizes a character in the specified range (e.g.
    /// `[a-z]`)
    pub fn range(ctx: &'ctx Context, lo: &char, hi: &char) -> Self {
        unsafe {
            Self::wrap(ctx, {
                let lo_cs = CString::new(lo.to_string()).unwrap();
                let hi_cs = CString::new(hi.to_string()).unwrap();
                let lo_z3s = Z3_mk_string(ctx.z3_ctx, lo_cs.as_ptr());
                Z3_inc_ref(ctx.z3_ctx, lo_z3s);
                let hi_z3s = Z3_mk_string(ctx.z3_ctx, hi_cs.as_ptr());
                Z3_inc_ref(ctx.z3_ctx, hi_z3s);

                let ret = Z3_mk_re_range(ctx.z3_ctx, lo_z3s, hi_z3s);
                Z3_dec_ref(ctx.z3_ctx, lo_z3s);
                Z3_dec_ref(ctx.z3_ctx, hi_z3s);
                ret
            })
        }
    }

    /// Creates a regular expression that recognizes this regular expression `lo` to `hi` times (e.g. `a{2,3}`)
    pub fn r#loop(&self, lo: u32, hi: u32) -> Self {
        unsafe {
            Self::wrap(self.ctx, {
                Z3_mk_re_loop(self.ctx.z3_ctx, self.z3_ast, lo, hi)
            })
        }
    }

    /// Creates a regular expression that recognizes this regular expression
    /// n number of times
    /// Requires Z3 4.8.15 or later.
    pub fn power(&self, n: u32) -> Self {
        unsafe {
            Self::wrap(self.ctx, {
                Z3_mk_re_power(self.ctx.z3_ctx, self.z3_ast, n)
            })
        }
    }

    /// Creates a regular expression that recognizes all sequences
    pub fn full(ctx: &'ctx Context) -> Self {
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_re_full(
                    ctx.z3_ctx,
                    Z3_mk_re_sort(ctx.z3_ctx, Z3_mk_string_sort(ctx.z3_ctx)),
                )
            })
        }
    }

    /// Creates a regular expression that accepts all singleton sequences of the characters
    /// Requires Z3 4.8.13 or later.
    pub fn allchar(ctx: &'ctx Context) -> Self {
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_re_allchar(
                    ctx.z3_ctx,
                    Z3_mk_re_sort(ctx.z3_ctx, Z3_mk_string_sort(ctx.z3_ctx)),
                )
            })
        }
    }

    /// Creates a regular expression that doesn't recognize any sequences
    pub fn empty(ctx: &'ctx Context) -> Self {
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_re_empty(
                    ctx.z3_ctx,
                    Z3_mk_re_sort(ctx.z3_ctx, Z3_mk_string_sort(ctx.z3_ctx)),
                )
            })
        }
    }

    unop! {
       /// Creates a regular expression that recognizes this regular expression one or more times (e.g. `a+`)
       plus(Z3_mk_re_plus, Self);
       /// Creates a regular expression that recognizes this regular expression any number of times
       /// (Kleene star, e.g. `a*`)
       star(Z3_mk_re_star, Self);
       /// Creates a regular expression that recognizes any sequence that this regular expression
       /// doesn't
       complement(Z3_mk_re_complement, Self);
       /// Creates a regular expression that optionally accepts this regular expression (e.g. `a?`)
       option(Z3_mk_re_option, Self);
    }
    binop! {
        /// Creates a difference regular expression
        /// Requires Z3 4.8.14 or later.
        diff(Z3_mk_re_diff, Self);
    }
    varop! {
       /// Concatenates regular expressions
        concat(Z3_mk_re_concat, Self);
       /// Creates a regular expression that recognizes sequences that any of the regular
       /// expressions given as parameters recognize
        union(Z3_mk_re_union, Self);
        /// Creates a regular expression that only recognizes sequences that all of the parameters
        /// recognize
        intersect(Z3_mk_re_intersect, Self);
    }
}

/// Create a universal quantifier.
///
/// # Examples
/// ```
/// # use z3::{ast, Config, Context, FuncDecl, Pattern, SatResult, Solver, Sort, Symbol};
/// # use z3::ast::Ast;
/// # use std::convert::TryInto;
/// # let cfg = Config::new();
/// # let ctx = Context::new(&cfg);
/// # let solver = Solver::new(&ctx);
/// let f = FuncDecl::new(&ctx, "f", &[&Sort::int(&ctx)], &Sort::int(&ctx));
///
/// let x = ast::Int::new_const(&ctx, "x");
/// let f_x: ast::Int = f.apply(&[&x]).try_into().unwrap();
/// let f_x_pattern: Pattern = Pattern::new(&ctx, &[ &f_x ]);
/// let forall: ast::Bool = ast::forall_const(
///     &ctx,
///     &[&x],
///     &[&f_x_pattern],
///     &x._eq(&f_x)
/// ).try_into().unwrap();
/// solver.assert(&forall);
///
/// assert_eq!(solver.check(), SatResult::Sat);
/// let model = solver.get_model().unwrap();;
///
/// let f_f_3: ast::Int = f.apply(&[&f.apply(&[&ast::Int::from_u64(&ctx, 3)])]).try_into().unwrap();
/// assert_eq!(3, model.eval(&f_f_3, true).unwrap().as_u64().unwrap());
/// ```
pub fn forall_const<'ctx>(
    ctx: &'ctx Context,
    bounds: &[&dyn Ast<'ctx>],
    patterns: &[&Pattern<'ctx>],
    body: &Bool<'ctx>,
) -> Bool<'ctx> {
    assert!(bounds.iter().all(|a| a.get_ctx() == ctx));
    assert!(patterns.iter().all(|p| p.ctx == ctx));
    assert_eq!(ctx, body.get_ctx());

    if bounds.is_empty() {
        return body.clone();
    }

    let bounds: Vec<_> = bounds.iter().map(|a| a.get_z3_ast()).collect();
    let patterns: Vec<_> = patterns.iter().map(|p| p.z3_pattern).collect();

    unsafe {
        Ast::wrap(ctx, {
            Z3_mk_forall_const(
                ctx.z3_ctx,
                0,
                bounds.len().try_into().unwrap(),
                bounds.as_ptr() as *const Z3_app,
                patterns.len().try_into().unwrap(),
                patterns.as_ptr() as *const Z3_pattern,
                body.get_z3_ast(),
            )
        })
    }
}

/// Create an existential quantifier.
///
/// # Examples
/// ```
/// # use z3::{ast, Config, Context, FuncDecl, SatResult, Solver, Sort, Symbol, Pattern};
/// # use z3::ast::Ast;
/// # use std::convert::TryInto;
/// # let cfg = Config::new();
/// # let ctx = Context::new(&cfg);
/// # let solver = Solver::new(&ctx);
/// let f = FuncDecl::new(&ctx, "f", &[&Sort::int(&ctx)], &Sort::int(&ctx));
///
/// let x = ast::Int::new_const(&ctx, "x");
/// let f_x: ast::Int = f.apply(&[&x]).try_into().unwrap();
/// let f_x_pattern: Pattern = Pattern::new(&ctx, &[ &f_x ]);
/// let exists: ast::Bool = ast::exists_const(
///     &ctx,
///     &[&x],
///     &[&f_x_pattern],
///     &x._eq(&f_x).not()
/// ).try_into().unwrap();
/// solver.assert(&exists.not());
///
/// assert_eq!(solver.check(), SatResult::Sat);
/// let model = solver.get_model().unwrap();;
///
/// let f_f_3: ast::Int = f.apply(&[&f.apply(&[&ast::Int::from_u64(&ctx, 3)])]).try_into().unwrap();
/// assert_eq!(3, model.eval(&f_f_3, true).unwrap().as_u64().unwrap());
/// ```
pub fn exists_const<'ctx>(
    ctx: &'ctx Context,
    bounds: &[&dyn Ast<'ctx>],
    patterns: &[&Pattern<'ctx>],
    body: &Bool<'ctx>,
) -> Bool<'ctx> {
    assert!(bounds.iter().all(|a| a.get_ctx() == ctx));
    assert!(patterns.iter().all(|p| p.ctx == ctx));
    assert_eq!(ctx, body.get_ctx());

    if bounds.is_empty() {
        return body.clone();
    }

    let bounds: Vec<_> = bounds.iter().map(|a| a.get_z3_ast()).collect();
    let patterns: Vec<_> = patterns.iter().map(|p| p.z3_pattern).collect();

    unsafe {
        Ast::wrap(ctx, {
            Z3_mk_exists_const(
                ctx.z3_ctx,
                0,
                bounds.len().try_into().unwrap(),
                bounds.as_ptr() as *const Z3_app,
                patterns.len().try_into().unwrap(),
                patterns.as_ptr() as *const Z3_pattern,
                body.get_z3_ast(),
            )
        })
    }
}

/// Create a quantifier with additional attributes.
///
/// - `ctx`: logical context.
/// - `is_forall`: flag to indicate if this is a universal or existential quantifier.
/// - `quantifier_id`: identifier to identify quantifier
/// - `skolem_id`: identifier to identify skolem constants introduced by quantifier.
/// - `weight`: quantifiers are associated with weights indicating the importance of using the quantifier during instantiation. By default, pass the weight 0.
/// - `bounds`: list of variables that the quantifier ranges over
/// - `patterns`: if non-empty, explicit patterns to use for the quantifier.
/// - `no_patterns`: subexpressions to be excluded from inferred patterns.
/// - `body`: the body of the quantifier.
///
/// # Examples
/// ```
/// # use z3::{ast, Config, Context, FuncDecl, Pattern, SatResult, Solver, Sort, Symbol};
/// # use z3::ast::Ast;
/// # use std::convert::TryInto;
/// # let cfg = Config::new();
/// # let ctx = Context::new(&cfg);
/// # let solver = Solver::new(&ctx);
/// let f = FuncDecl::new(&ctx, "f", &[&Sort::int(&ctx)], &Sort::int(&ctx));
///
/// let x = ast::Int::new_const(&ctx, "x");
/// let f_x: ast::Int = f.apply(&[&x]).try_into().unwrap();
/// let f_x_pattern: Pattern = Pattern::new(&ctx, &[ &f_x ]);
/// let forall: ast::Bool = ast::quantifier_const(
///     &ctx,
///     true,
///     0,
///     "def_f",
///     "",
///     &[&x],
///     &[&f_x_pattern],
///     &[],
///     &x._eq(&f_x)
/// ).try_into().unwrap();
/// solver.assert(&forall);
///
/// assert_eq!(solver.check(), SatResult::Sat);
/// let model = solver.get_model().unwrap();;
///
/// let f_f_3: ast::Int = f.apply(&[&f.apply(&[&ast::Int::from_u64(&ctx, 3)])]).try_into().unwrap();
/// assert_eq!(3, model.eval(&f_f_3, true).unwrap().as_u64().unwrap());
/// ```
#[allow(clippy::too_many_arguments)]
pub fn quantifier_const<'ctx>(
    ctx: &'ctx Context,
    is_forall: bool,
    weight: u32,
    quantifier_id: impl Into<Symbol>,
    skolem_id: impl Into<Symbol>,
    bounds: &[&dyn Ast<'ctx>],
    patterns: &[&Pattern<'ctx>],
    no_patterns: &[&dyn Ast<'ctx>],
    body: &Bool<'ctx>,
) -> Bool<'ctx> {
    assert!(bounds.iter().all(|a| a.get_ctx() == ctx));
    assert!(patterns.iter().all(|p| p.ctx == ctx));
    assert!(no_patterns.iter().all(|p| p.get_ctx() == ctx));
    assert_eq!(ctx, body.get_ctx());

    if bounds.is_empty() {
        return body.clone();
    }

    let bounds: Vec<_> = bounds.iter().map(|a| a.get_z3_ast()).collect();
    let patterns: Vec<_> = patterns.iter().map(|p| p.z3_pattern).collect();
    let no_patterns: Vec<_> = no_patterns.iter().map(|a| a.get_z3_ast()).collect();

    unsafe {
        Ast::wrap(ctx, {
            Z3_mk_quantifier_const_ex(
                ctx.z3_ctx,
                is_forall,
                weight,
                quantifier_id.into().as_z3_symbol(ctx),
                skolem_id.into().as_z3_symbol(ctx),
                bounds.len().try_into().unwrap(),
                bounds.as_ptr() as *const Z3_app,
                patterns.len().try_into().unwrap(),
                patterns.as_ptr() as *const Z3_pattern,
                no_patterns.len().try_into().unwrap(),
                no_patterns.as_ptr() as *const Z3_ast,
                body.get_z3_ast(),
            )
        })
    }
}

/// Create a lambda expression.
///
/// - `num_decls`: Number of variables to be bound.
/// - `sorts`: Bound variable sorts.
/// - `decl_names`: Contains the names that the quantified formula uses for the bound variables.
/// - `body`: Expression body that contains bound variables of the same sorts as the sorts listed in the array sorts.
///
/// # Examples
/// ```
/// # use z3::{
/// #     ast::{lambda_const, Ast as _, Int, Dynamic},
/// #     Config, Context, Solver, SatResult,
/// # };
/// #
/// # let cfg = Config::new();
/// # let ctx = Context::new(&cfg);
/// # let solver = Solver::new(&ctx);
/// #
/// let input = Int::fresh_const(&ctx, "");
/// let lambda = lambda_const(
///     &ctx,
///     &[&input],
///     &Dynamic::from_ast(&Int::add(&ctx, &[&input, &Int::from_i64(&ctx, 2)])),
/// );
///
/// solver.assert(
///     &lambda.select_n(&[&Int::from_i64(&ctx, 1)]).as_int().unwrap()
///         ._eq(&Int::from_i64(&ctx, 3))
/// );
///
/// assert_eq!(solver.check(), SatResult::Sat);
///
/// solver.assert(
///     &lambda.select_n(&[&Int::from_i64(&ctx, 1)]).as_int().unwrap()
///         ._eq(&Int::from_i64(&ctx, 2))
/// );
///
/// assert_eq!(solver.check(), SatResult::Unsat);
/// ```
pub fn lambda_const<'ctx>(
    ctx: &'ctx Context,
    bounds: &[&dyn Ast<'ctx>],
    body: &Dynamic<'ctx>,
) -> Array<'ctx> {
    let bounds: Vec<_> = bounds.iter().map(|a| a.get_z3_ast()).collect();

    unsafe {
        Ast::wrap(
            ctx,
            Z3_mk_lambda_const(
                ctx.z3_ctx,
                bounds.len().try_into().unwrap(),
                bounds.as_ptr() as *const Z3_app,
                body.get_z3_ast(),
            ),
        )
    }
}

impl IsNotApp {
    pub fn new(kind: AstKind) -> Self {
        Self { kind }
    }

    pub fn kind(&self) -> AstKind {
        self.kind
    }
}

impl fmt::Display for IsNotApp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "ast node is not a function application, has kind {:?}",
            self.kind()
        )
    }
}
