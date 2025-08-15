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

mod bool;
mod int;
mod real;
mod float;
mod string;
mod bv;
mod array;
mod set;
mod seq;
mod datatype;
mod dynamic;

pub use array::Array;
pub use bool::Bool;
pub use bv::BV;
pub use datatype::Datatype;
pub use dynamic::Dynamic;
pub use float::Float;
pub use int::Int;
pub use real::Real;
pub use set::Set;
pub use seq::Seq;
pub use string::String;

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
/// assert_eq!(solver.check(), SatResult::Sat);
/// ```
pub struct Regexp {
    pub(crate) ctx: Context,
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
                    <$retty>::wrap(&self.ctx, {
                        $z3fn(self.ctx.z3_ctx.0, self.z3_ast)
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
                    <$retty>::wrap(&self.ctx, {
                        $z3fn(self.ctx.z3_ctx.0, self.z3_ast, other.z3_ast)
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
                    <$retty>::wrap(&self.ctx, {
                        $z3fn(self.ctx.z3_ctx.0, self.z3_ast, a.z3_ast, b.z3_ast)
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
            pub fn $f(ctx: &Context, values: &[impl Borrow<Self>]) -> $retty {
                assert!(values.iter().all(|v| v.borrow().get_ctx().z3_ctx == ctx.z3_ctx));
                unsafe {
                    <$retty>::wrap(ctx, {
                        let tmp: Vec<_> = values.iter().map(|x| x.borrow().z3_ast).collect();
                        assert!(tmp.len() <= 0xffff_ffff);
                        $z3fn(ctx.z3_ctx.0, tmp.len() as u32, tmp.as_ptr())
                    })
                }
            }
        )*
    };
}

/// Abstract syntax tree (AST) nodes represent terms, constants, or expressions.
/// The `Ast` trait contains methods common to all AST subtypes.
pub trait Ast: fmt::Debug {
    fn get_ctx(&self) -> &Context;
    fn get_z3_ast(&self) -> Z3_ast;

    // This would be great, but gives error E0071 "expected struct, variant or union type, found Self"
    // so I don't think we can write a generic constructor like this.
    // Instead we just require the method, and use the impl_ast! macro defined below to implement it
    // on each Ast subtype.
    /*
    fn wrap(ctx: &Context, ast: Z3_ast) -> Self {
        assert!(!ast.is_null());
        Self {
            ctx,
            z3_ast: unsafe {
                debug!("new ast {:p}", ast);
                Z3_inc_ref(ctx.z3_ctx.0, ast);
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
    unsafe fn wrap(ctx: &Context, ast: Z3_ast) -> Self
    where
        Self: Sized;

    /// Compare this `Ast` with another `Ast`, and get a [`Bool`]
    /// representing the result.
    ///
    /// This operation works with all possible `Ast`s (int, real, BV, etc), but the two
    /// `Ast`s being compared must be the same type.
    //
    // Note that we can't use the binop! macro because of the `pub` keyword on it
    fn _eq(&self, other: &Self) -> Bool
    where
        Self: Sized,
    {
        self._safe_eq(other).unwrap()
    }

    /// Compare this `Ast` with another `Ast`, and get a Result.  Errors if the sort does not
    /// match for the two values.
    fn _safe_eq(&self, other: &Self) -> Result<Bool, SortDiffers>
    where
        Self: Sized,
    {
        assert_eq!(self.get_ctx(), other.get_ctx());

        let left_sort = self.get_sort();
        let right_sort = other.get_sort();
        match left_sort == right_sort {
            true => Ok(unsafe {
                Bool::wrap(self.get_ctx(), {
                    Z3_mk_eq(
                        self.get_ctx().z3_ctx.0,
                        self.get_z3_ast(),
                        other.get_z3_ast(),
                    )
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
    fn distinct(ctx: &Context, values: &[impl Borrow<Self>]) -> Bool
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
                Z3_mk_distinct(ctx.z3_ctx.0, values.len() as u32, values.as_ptr())
            })
        }
    }

    /// Get the [`Sort`] of the `Ast`.
    fn get_sort(&self) -> Sort {
        unsafe {
            Sort::wrap(
                self.get_ctx(),
                Z3_get_sort(self.get_ctx().z3_ctx.0, self.get_z3_ast()),
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
                Z3_simplify(self.get_ctx().z3_ctx.0, self.get_z3_ast())
            })
        }
    }

    /// Performs substitution on the `Ast`. The slice `substitutions` contains a
    /// list of pairs with a "from" `Ast` that will be substituted by a "to" `Ast`.
    fn substitute<T: Ast>(&self, substitutions: &[(&T, &T)]) -> Self
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
                    self.get_ctx().z3_ctx.0,
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
        let this_ctx = self.get_ctx().z3_ctx.0;
        unsafe {
            let this_app = Z3_to_app(this_ctx, self.get_z3_ast());
            Z3_get_app_num_args(this_ctx, this_app) as usize
        }
    }

    /// Return the `n`th child of this `Ast`.
    ///
    /// Out-of-bound indices will return `None`.
    fn nth_child(&self, idx: usize) -> Option<Dynamic> {
        if idx >= self.num_children() {
            None
        } else {
            let idx = u32::try_from(idx).unwrap();
            let this_ctx = self.get_ctx().z3_ctx.0;
            let child_ast = unsafe {
                let this_app = Z3_to_app(this_ctx, self.get_z3_ast());
                Z3_get_app_arg(this_ctx, this_app, idx)
            };
            Some(unsafe { Dynamic::wrap(self.get_ctx(), child_ast) })
        }
    }

    /// Return the children of this node as a `Vec<Dynamic>`.
    fn children(&self) -> Vec<Dynamic> {
        let n = self.num_children();
        (0..n).map(|i| self.nth_child(i).unwrap()).collect()
    }

    /// Return the `AstKind` for this `Ast`.
    fn kind(&self) -> AstKind {
        unsafe {
            let z3_ctx = self.get_ctx().z3_ctx.0;
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
    fn decl(&self) -> FuncDecl {
        self.safe_decl().expect("Ast is not an app")
    }

    fn safe_decl(&self) -> Result<FuncDecl, IsNotApp> {
        if !self.is_app() {
            Err(IsNotApp::new(self.kind()))
        } else {
            let ctx = self.get_ctx();
            let func_decl = unsafe {
                let app = Z3_to_app(ctx.z3_ctx.0, self.get_z3_ast());
                Z3_get_app_decl(ctx.z3_ctx.0, app)
            };
            Ok(unsafe { FuncDecl::wrap(ctx, func_decl) })
        }
    }
}

macro_rules! impl_ast {
    ($ast:ident) => {
        impl Ast for $ast {
            unsafe fn wrap(ctx: &Context, ast: Z3_ast) -> Self {
                assert!(!ast.is_null());
                Self {
                    ctx: ctx.clone(),
                    z3_ast: {
                        debug!(
                            "new ast: id = {}, pointer = {:p}",
                            unsafe { Z3_get_ast_id(ctx.z3_ctx.0, ast) },
                            ast
                        );
                        unsafe {
                            Z3_inc_ref(ctx.z3_ctx.0, ast);
                        }
                        ast
                    },
                }
            }

            fn get_ctx(&self) -> &Context {
                &self.ctx
            }

            fn get_z3_ast(&self) -> Z3_ast {
                self.z3_ast
            }
        }

        impl From<$ast> for Z3_ast {
            fn from(ast: $ast) -> Self {
                ast.z3_ast
            }
        }

        impl PartialEq for $ast {
            fn eq(&self, other: &$ast) -> bool {
                assert_eq!(self.ctx, other.ctx);
                unsafe { Z3_is_eq_ast(self.ctx.z3_ctx.0, self.z3_ast, other.z3_ast) }
            }
        }

        impl Eq for $ast {}

        impl Clone for $ast {
            fn clone(&self) -> Self {
                debug!(
                    "clone ast: id = {}, pointer = {:p}",
                    unsafe { Z3_get_ast_id(self.ctx.z3_ctx.0, self.z3_ast) },
                    self.z3_ast
                );
                unsafe { Self::wrap(&self.ctx, self.z3_ast) }
            }
        }

        impl Drop for $ast {
            fn drop(&mut self) {
                debug!(
                    "drop ast: id = {}, pointer = {:p}",
                    unsafe { Z3_get_ast_id(self.ctx.z3_ctx.0, self.z3_ast) },
                    self.z3_ast
                );
                unsafe {
                    Z3_dec_ref(self.ctx.z3_ctx.0, self.z3_ast);
                }
            }
        }

        impl Hash for $ast {
            fn hash<H: Hasher>(&self, state: &mut H) {
                unsafe {
                    let u = Z3_get_ast_hash(self.ctx.z3_ctx.0, self.z3_ast);
                    u.hash(state);
                }
            }
        }

        impl fmt::Debug for $ast {
            fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
                let p = unsafe { Z3_ast_to_string(self.ctx.z3_ctx.0, self.z3_ast) };
                if p.is_null() {
                    return Result::Err(fmt::Error);
                }
                match unsafe { CStr::from_ptr(p) }.to_str() {
                    Ok(s) => write!(f, "{}", s),
                    Err(_) => Result::Err(fmt::Error),
                }
            }
        }

        impl fmt::Display for $ast {
            fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
                <Self as fmt::Debug>::fmt(self, f)
            }
        }
    };
}

macro_rules! impl_from_try_into_dynamic {
    ($ast:ident, $as_ast:ident) => {
        impl From<$ast> for Dynamic {
            fn from(ast: $ast) -> Self {
                unsafe { Dynamic::wrap(&ast.ctx, ast.z3_ast) }
            }
        }

        impl From<&$ast> for Dynamic {
            fn from(ast: &$ast) -> Self {
                unsafe { Dynamic::wrap(&ast.ctx, ast.z3_ast) }
            }
        }

        impl TryFrom<Dynamic> for $ast {
            type Error = std::string::String;
            fn try_from(ast: Dynamic) -> Result<Self, std::string::String> {
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

impl_ast!(Datatype);
impl_from_try_into_dynamic!(Datatype, as_datatype);

impl_ast!(Dynamic);

pub fn atmost<'a, I: IntoIterator<Item = &'a Bool>>(ctx: &Context, args: I, k: u32) -> Bool {
    let args: Vec<_> = args.into_iter().map(|f| f.z3_ast).collect();
    _atmost(ctx, args.as_ref(), k)
}

fn _atmost(ctx: &Context, args: &[Z3_ast], k: u32) -> Bool {
    unsafe {
        Bool::wrap(
            ctx,
            Z3_mk_atmost(
                ctx.z3_ctx.0,
                args.len().try_into().unwrap(),
                args.as_ptr(),
                k,
            ),
        )
    }
}

pub fn atleast<'a, I: IntoIterator<Item = &'a Bool>>(ctx: &Context, args: I, k: u32) -> Bool {
    let args: Vec<_> = args.into_iter().map(|f| f.z3_ast).collect();
    _atleast(ctx, args.as_ref(), k)
}

fn _atleast(ctx: &Context, args: &[Z3_ast], k: u32) -> Bool {
    unsafe {
        Bool::wrap(
            ctx,
            Z3_mk_atleast(
                ctx.z3_ctx.0,
                args.len().try_into().unwrap(),
                args.as_ptr(),
                k,
            ),
        )
    }
}

impl Regexp {
    /// Creates a regular expression that recognizes the string given as parameter
    pub fn literal(ctx: &Context, s: &str) -> Self {
        unsafe {
            Self::wrap(ctx, {
                let c_str = CString::new(s).unwrap();
                Z3_mk_seq_to_re(ctx.z3_ctx.0, Z3_mk_string(ctx.z3_ctx.0, c_str.as_ptr()))
            })
        }
    }

    /// Creates a regular expression that recognizes a character in the specified range (e.g.
    /// `[a-z]`)
    pub fn range(ctx: &Context, lo: &char, hi: &char) -> Self {
        unsafe {
            Self::wrap(ctx, {
                let lo_cs = CString::new(lo.to_string()).unwrap();
                let hi_cs = CString::new(hi.to_string()).unwrap();
                let lo_z3s = Z3_mk_string(ctx.z3_ctx.0, lo_cs.as_ptr());
                Z3_inc_ref(ctx.z3_ctx.0, lo_z3s);
                let hi_z3s = Z3_mk_string(ctx.z3_ctx.0, hi_cs.as_ptr());
                Z3_inc_ref(ctx.z3_ctx.0, hi_z3s);

                let ret = Z3_mk_re_range(ctx.z3_ctx.0, lo_z3s, hi_z3s);
                Z3_dec_ref(ctx.z3_ctx.0, lo_z3s);
                Z3_dec_ref(ctx.z3_ctx.0, hi_z3s);
                ret
            })
        }
    }

    /// Creates a regular expression that recognizes this regular expression `lo` to `hi` times (e.g. `a{2,3}`)
    pub fn r#loop(&self, lo: u32, hi: u32) -> Self {
        unsafe {
            Self::wrap(&self.ctx, {
                Z3_mk_re_loop(self.ctx.z3_ctx.0, self.z3_ast, lo, hi)
            })
        }
    }

    /// Creates a regular expression that recognizes this regular expression
    /// n number of times
    /// Requires Z3 4.8.15 or later.
    pub fn power(&self, n: u32) -> Self {
        unsafe {
            Self::wrap(&self.ctx, {
                Z3_mk_re_power(self.ctx.z3_ctx.0, self.z3_ast, n)
            })
        }
    }

    /// Creates a regular expression that recognizes all sequences
    pub fn full(ctx: &Context) -> Self {
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_re_full(
                    ctx.z3_ctx.0,
                    Z3_mk_re_sort(ctx.z3_ctx.0, Z3_mk_string_sort(ctx.z3_ctx.0)),
                )
            })
        }
    }

    /// Creates a regular expression that accepts all singleton sequences of the characters
    /// Requires Z3 4.8.13 or later.
    pub fn allchar(ctx: &Context) -> Self {
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_re_allchar(
                    ctx.z3_ctx.0,
                    Z3_mk_re_sort(ctx.z3_ctx.0, Z3_mk_string_sort(ctx.z3_ctx.0)),
                )
            })
        }
    }

    /// Creates a regular expression that doesn't recognize any sequences
    pub fn empty(ctx: &Context) -> Self {
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_re_empty(
                    ctx.z3_ctx.0,
                    Z3_mk_re_sort(ctx.z3_ctx.0, Z3_mk_string_sort(ctx.z3_ctx.0)),
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
/// let model = solver.get_model().unwrap();
///
/// let f_f_3: ast::Int = f.apply(&[&f.apply(&[&ast::Int::from_u64(&ctx, 3)])]).try_into().unwrap();
/// assert_eq!(3, model.eval(&f_f_3, true).unwrap().as_u64().unwrap());
/// ```
pub fn forall_const(
    ctx: &Context,
    bounds: &[&dyn Ast],
    patterns: &[&Pattern],
    body: &Bool,
) -> Bool {
    assert!(bounds.iter().all(|a| a.get_ctx() == ctx));
    assert!(patterns.iter().all(|p| &p.ctx == ctx));
    assert_eq!(ctx, body.get_ctx());

    if bounds.is_empty() {
        return body.clone();
    }

    let bounds: Vec<_> = bounds.iter().map(|a| a.get_z3_ast()).collect();
    let patterns: Vec<_> = patterns.iter().map(|p| p.z3_pattern).collect();

    unsafe {
        Ast::wrap(ctx, {
            Z3_mk_forall_const(
                ctx.z3_ctx.0,
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
/// let model = solver.get_model().unwrap();
///
/// let f_f_3: ast::Int = f.apply(&[&f.apply(&[&ast::Int::from_u64(&ctx, 3)])]).try_into().unwrap();
/// assert_eq!(3, model.eval(&f_f_3, true).unwrap().as_u64().unwrap());
/// ```
pub fn exists_const(
    ctx: &Context,
    bounds: &[&dyn Ast],
    patterns: &[&Pattern],
    body: &Bool,
) -> Bool {
    assert!(bounds.iter().all(|a| a.get_ctx() == ctx));
    assert!(patterns.iter().all(|p| &p.ctx == ctx));
    assert_eq!(ctx, body.get_ctx());

    if bounds.is_empty() {
        return body.clone();
    }

    let bounds: Vec<_> = bounds.iter().map(|a| a.get_z3_ast()).collect();
    let patterns: Vec<_> = patterns.iter().map(|p| p.z3_pattern).collect();

    unsafe {
        Ast::wrap(ctx, {
            Z3_mk_exists_const(
                ctx.z3_ctx.0,
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
/// let model = solver.get_model().unwrap();
///
/// let f_f_3: ast::Int = f.apply(&[&f.apply(&[&ast::Int::from_u64(&ctx, 3)])]).try_into().unwrap();
/// assert_eq!(3, model.eval(&f_f_3, true).unwrap().as_u64().unwrap());
/// ```
#[allow(clippy::too_many_arguments)]
pub fn quantifier_const(
    ctx: &Context,
    is_forall: bool,
    weight: u32,
    quantifier_id: impl Into<Symbol>,
    skolem_id: impl Into<Symbol>,
    bounds: &[&dyn Ast],
    patterns: &[&Pattern],
    no_patterns: &[&dyn Ast],
    body: &Bool,
) -> Bool {
    assert!(bounds.iter().all(|a| a.get_ctx() == ctx));
    assert!(patterns.iter().all(|p| &p.ctx == ctx));
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
                ctx.z3_ctx.0,
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
pub fn lambda_const(ctx: &Context, bounds: &[&dyn Ast], body: &Dynamic) -> Array {
    let bounds: Vec<_> = bounds.iter().map(|a| a.get_z3_ast()).collect();

    unsafe {
        Ast::wrap(
            ctx,
            Z3_mk_lambda_const(
                ctx.z3_ctx.0,
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

pub(crate) use {varop, binop, unop, trinop};