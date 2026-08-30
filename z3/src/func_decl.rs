use std::convert::TryInto;
use std::ffi::CStr;
use std::fmt;
use std::{borrow::Borrow, ffi::c_uint};
use z3_sys::*;

use crate::ast::{Array, BV, Bool, Char, Datatype, Dynamic, Float, Int, Real, Seq, Set};
use crate::{Context, FuncDecl, Sort, Symbol, Translate, ast, ast::Ast};

/// Describes the argument-list shape of a [`FuncDecl`]'s domain, and how to convert between
/// it and the untyped [`Dynamic`] values Z3's FFI actually deals in.
///
/// Implemented for `()` (nullary), `Sort<A>` (a single typed argument), tuples of
/// `FuncDeclDomain` up to arity 6 (multiple typed arguments), and `Vec<Sort<Dynamic>>`
/// (the dynamic-arity bottom case, and the default domain for [`FuncDecl`]).
pub trait FuncDeclDomain {
    /// The type `apply` accepts for this domain shape.
    type ApplicationParam;

    fn application_args(a: Self::ApplicationParam) -> Vec<Dynamic>;

    fn sorts(&self) -> Vec<Sort<Dynamic>>;
}

/// Describes how a [`FuncDecl`]'s range is recovered from the untyped [`Dynamic`] value
/// `Z3_mk_app` actually produces.
///
/// Implemented for every concrete [`Ast`] type that has a `Dynamic::as_*` conversion, and for
/// `Dynamic` itself (the identity/bottom case, and the default range for [`FuncDecl`]).
pub trait FuncDeclReturn: Ast {
    fn process(d: Dynamic) -> Self;
}

impl FuncDeclDomain for () {
    type ApplicationParam = ();

    fn application_args(_a: Self::ApplicationParam) -> Vec<Dynamic> {
        vec![]
    }

    fn sorts(&self) -> Vec<Sort<Dynamic>> {
        vec![]
    }
}

impl<A: Ast + Clone> FuncDeclDomain for Sort<A> {
    type ApplicationParam = A;

    fn application_args(a: Self::ApplicationParam) -> Vec<Dynamic> {
        vec![Dynamic::from_ast(&a)]
    }

    fn sorts(&self) -> Vec<Sort<Dynamic>> {
        vec![self.as_dyn()]
    }
}

impl FuncDeclDomain for Vec<Sort<Dynamic>> {
    type ApplicationParam = Vec<Dynamic>;

    fn application_args(a: Self::ApplicationParam) -> Vec<Dynamic> {
        a
    }

    fn sorts(&self) -> Vec<Sort<Dynamic>> {
        self.clone()
    }
}

// Macro to implement `FuncDeclDomain` for tuples of `FuncDeclDomain`.
macro_rules! impl_func_decl_domain_for_tuples {
    ($(($($T:ident),+)),+ $(,)?) => {
        $(
            impl<$($T: FuncDeclDomain),+> FuncDeclDomain for ($($T,)+) {
                type ApplicationParam = ($($T::ApplicationParam,)+);

                #[allow(non_snake_case)]
                fn application_args(a: Self::ApplicationParam) -> Vec<Dynamic> {
                    let ($($T,)+) = a;
                    let mut args = Vec::new();
                    $(
                        args.extend($T::application_args($T));
                    )+
                    args
                }

                #[allow(non_snake_case)]
                fn sorts(&self) -> Vec<Sort<Dynamic>> {
                    let ($($T,)+) = self;
                    let mut sorts = Vec::new();
                    $(
                        sorts.extend($T.sorts());
                    )+
                    sorts
                }
            }
        )+
    };
}

// Implement for tuples up to arity 6 (can be extended as needed).
impl_func_decl_domain_for_tuples!(
    (A),
    (A, B),
    (A, B, C),
    (A, B, C, D),
    (A, B, C, D, E),
    (A, B, C, D, E, F)
);

impl FuncDeclReturn for Bool {
    fn process(d: Dynamic) -> Self {
        d.as_bool().unwrap()
    }
}

impl FuncDeclReturn for Int {
    fn process(d: Dynamic) -> Self {
        d.as_int().unwrap()
    }
}

impl FuncDeclReturn for Real {
    fn process(d: Dynamic) -> Self {
        d.as_real().unwrap()
    }
}

impl FuncDeclReturn for BV {
    fn process(d: Dynamic) -> Self {
        d.as_bv().unwrap()
    }
}

impl FuncDeclReturn for Float {
    fn process(d: Dynamic) -> Self {
        d.as_float().unwrap()
    }
}

impl FuncDeclReturn for Char {
    fn process(d: Dynamic) -> Self {
        d.as_char().unwrap()
    }
}

impl FuncDeclReturn for ast::String {
    fn process(d: Dynamic) -> Self {
        d.as_string().unwrap()
    }
}

impl FuncDeclReturn for Seq {
    fn process(d: Dynamic) -> Self {
        d.as_seq().unwrap()
    }
}

impl FuncDeclReturn for Set {
    fn process(d: Dynamic) -> Self {
        d.as_set().unwrap()
    }
}

impl FuncDeclReturn for Array {
    fn process(d: Dynamic) -> Self {
        d.as_array().unwrap()
    }
}

impl FuncDeclReturn for Datatype {
    fn process(d: Dynamic) -> Self {
        d.as_datatype().unwrap()
    }
}

impl FuncDeclReturn for Dynamic {
    fn process(d: Dynamic) -> Self {
        d
    }
}

impl<A: FuncDeclDomain, R: FuncDeclReturn> FuncDecl<A, R> {
    pub(crate) unsafe fn wrap(ctx: &Context, z3_func_decl: Z3_func_decl) -> Self {
        unsafe {
            Z3_inc_ref(
                ctx.z3_ctx.0,
                Z3_func_decl_to_ast(ctx.z3_ctx.0, z3_func_decl).unwrap(),
            );
        }
        Self {
            ctx: ctx.clone(),
            z3_func_decl,
            phantom_a: std::marker::PhantomData,
            phantom_r: std::marker::PhantomData,
        }
    }

    pub fn new<S: Into<Symbol>, RS: Borrow<Sort<R>>>(name: S, domain: A, range: RS) -> Self {
        let ctx = &Context::thread_local();
        let range = range.borrow();
        assert_eq!(ctx.z3_ctx, range.ctx.z3_ctx);

        let domain: Vec<_> = domain.sorts().iter().map(Sort::get_z3_sort).collect();
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_func_decl(
                    ctx.z3_ctx.0,
                    name.into().as_z3_symbol(),
                    domain.len().try_into().unwrap(),
                    domain.as_ptr(),
                    range.z3_sort,
                )
                .unwrap(),
            )
        }
    }

    /// Return the number of arguments of a function declaration.
    ///
    /// If the function declaration is a constant, then the arity is `0`.
    ///
    /// ```
    /// # use z3::{Config, Context, FuncDecl, Solver, Sort, Symbol};
    /// let f = FuncDecl::new(
    ///     "f",
    ///     vec![Sort::int().as_dyn(), Sort::real().as_dyn()],
    ///     Sort::int());
    /// assert_eq!(f.arity(), 2);
    /// ```
    pub fn arity(&self) -> usize {
        unsafe { Z3_get_arity(self.ctx.z3_ctx.0, self.z3_func_decl) as usize }
    }

    /// Create a constant (if `args` has length 0) or function application (otherwise).
    ///
    /// Note that `args` should have the types corresponding to the `domain` of the `FuncDecl`.
    pub fn apply(&self, args: A::ApplicationParam) -> R {
        let a = A::application_args(args);
        let d = self.apply_internal(a.into_iter());
        R::process(d)
    }

    fn apply_internal<I: Iterator<Item = Dynamic>>(&self, args: I) -> ast::Dynamic {
        // Collect Dynamics first to keep them alive (and thus their Z3_ast refcounts > 0)
        // until after Z3_mk_app returns.
        let dynamics: Vec<Dynamic> = args.collect();
        let ast_ptrs: Vec<_> = dynamics.iter().map(|a| a.get_z3_ast()).collect();

        unsafe {
            ast::Dynamic::wrap(&self.ctx, {
                Z3_mk_app(
                    self.ctx.z3_ctx.0,
                    self.z3_func_decl,
                    ast_ptrs.len().try_into().unwrap(),
                    ast_ptrs.as_ptr(),
                )
                .unwrap()
            })
        }
    }

    /// Return the `DeclKind` of this `FuncDecl`.
    pub fn kind(&self) -> DeclKind {
        unsafe { Z3_get_decl_kind(self.ctx.z3_ctx.0, self.z3_func_decl) }
    }

    /// Return the name of this `FuncDecl`.
    ///
    /// Strings will return the `Symbol`.  Ints will have a `"k!"` prepended to
    /// the `Symbol`.
    pub fn name(&self) -> String {
        unsafe {
            let z3_ctx = self.ctx.z3_ctx.0;
            let symbol = Z3_get_decl_name(z3_ctx, self.z3_func_decl).unwrap();
            match Z3_get_symbol_kind(z3_ctx, symbol) {
                SymbolKind::String => CStr::from_ptr(Z3_get_symbol_string(z3_ctx, symbol))
                    .to_string_lossy()
                    .into_owned(),
                SymbolKind::Int => format!("k!{}", Z3_get_symbol_int(z3_ctx, symbol)),
            }
        }
    }

    /// Returns the kind of the `i`-th domain (parameter) of this `FuncDecl`.
    ///
    /// Returns `None` if `i >= |domain|`.
    pub fn domain(&self, i: usize) -> Option<SortKind> {
        let z3_ctx = self.ctx.z3_ctx.0;
        let i = c_uint::try_from(i).unwrap();

        let domain_size = unsafe { Z3_get_domain_size(z3_ctx, self.z3_func_decl) };
        if i >= domain_size {
            return None;
        }

        Some(unsafe {
            Z3_get_sort_kind(
                z3_ctx,
                Z3_get_domain(z3_ctx, self.z3_func_decl, i).expect("cannot get domain of FuncDecl"),
            )
        })
    }

    /// Returns the kind of range (output) of this `FuncDecl`.
    pub fn range(&self) -> SortKind {
        let z3_ctx = self.ctx.z3_ctx.0;
        unsafe {
            Z3_get_sort_kind(
                z3_ctx,
                Z3_get_range(z3_ctx, self.z3_func_decl).expect("cannot get range of FuncDecl"),
            )
        }
    }
}

/// Binary "Special Relation" declarations. Z3's `Z3_mk_partial_order` family always builds a
/// `Bool`-valued relation between two elements of the same (dynamic) sort, so these constructors
/// are pinned to that concrete instantiation rather than being generic over arbitrary `A`/`R`.
impl FuncDecl<(Sort<Dynamic>, Sort<Dynamic>), Bool> {
    /// Create a partial order [`FuncDecl`] "Special Relation" over the given [`Sort`].
    ///
    /// The [`Sort`] may have many
    /// partial orders derived this way, distinguished by the second integer argument to this call,
    /// which represents the "id" of the partial order. Calling this twice with the same ID will
    /// yield the same partial order [`FuncDecl`].
    ///
    /// See <https://microsoft.github.io/z3guide/docs/theories/Special%20Relations/> for more info.
    ///
    /// A partial order is a binary relation that is reflexive, antisymmetric, and transitive.
    ///
    /// # Example
    ///
    /// ```
    /// # use z3::{FuncDecl, Sort, Solver, SatResult, Symbol};
    /// # use z3::ast::{Ast, Bool, Dynamic, Int};
    ///
    ///   let sort = Sort::int().as_dyn();
    ///   let partial_order = FuncDecl::partial_order(&sort, 0);
    ///   // Create a solver to assert properties of the partial order.
    ///   let solver = Solver::new();
    ///   let x = Int::new_const("x");
    ///   let y = Int::new_const("y");
    ///   let z = Int::new_const("z");
    ///   let dx = Dynamic::from_ast(&x);
    ///   let dy = Dynamic::from_ast(&y);
    ///   let dz = Dynamic::from_ast(&z);
    ///
    ///   solver.assert(&partial_order.apply((dx.clone(), dx.clone())));
    ///   // test reflexivity
    ///   assert_eq!(
    ///       solver.check_assumptions(&[partial_order.apply((dx.clone(), dx.clone())).not()]),
    ///       SatResult::Unsat
    ///   );
    ///
    ///   // test antisymmetry
    ///   assert_eq!(
    ///       solver.check_assumptions(&[
    ///           partial_order.apply((dx.clone(), dy.clone())),
    ///           partial_order.apply((dy.clone(), dx.clone())),
    ///           x.eq(&y).not()
    ///       ]),
    ///       SatResult::Unsat
    ///   );
    ///
    ///   // test transitivity
    ///   assert_eq!(
    ///       solver.check_assumptions(&[
    ///           partial_order.apply((dx.clone(), dy.clone())),
    ///           partial_order.apply((dy.clone(), dz.clone())),
    ///           partial_order.apply((dx.clone(), dz.clone())).not(),
    ///       ]),
    ///       SatResult::Unsat
    ///   );
    /// ```
    ///
    /// # See also
    ///
    /// - [`piecewise_linear_order`](Self::piecewise_linear_order)
    /// - [`linear_order`](Self::linear_order)
    /// - [`tree_order`](Self::tree_order)
    /// - [`transitive_closure`](Self::transitive_closure)
    pub fn partial_order<T: Borrow<Sort<Dynamic>>>(a: T, id: usize) -> Self {
        let a = a.borrow();
        let ctx = &a.ctx;
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_partial_order(ctx.z3_ctx.0, a.z3_sort, id as u32).unwrap(),
            )
        }
    }

    /// Create a piecewise linear order [`FuncDecl`] "Special Relation" over the given [`Sort`].
    ///
    /// See <https://microsoft.github.io/z3guide/docs/theories/Special%20Relations/> for more info.
    ///
    /// # See also
    ///
    /// - [`partial_order`](Self::partial_order)
    /// - [`linear_order`](Self::linear_order)
    /// - [`tree_order`](Self::tree_order)
    /// - [`transitive_closure`](Self::transitive_closure)
    pub fn piecewise_linear_order<T: Borrow<Sort<Dynamic>>>(a: T, id: usize) -> Self {
        let a = a.borrow();
        let ctx = &a.ctx;
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_piecewise_linear_order(ctx.z3_ctx.0, a.z3_sort, id as u32).unwrap(),
            )
        }
    }

    /// Create a linear order [`FuncDecl`] "Special Relation" over the given [`Sort`].
    ///
    /// See <https://microsoft.github.io/z3guide/docs/theories/Special%20Relations/> for more info.
    ///
    /// # See also
    ///
    /// - [`partial_order`](Self::partial_order)
    /// - [`piecewise_linear_order`](Self::piecewise_linear_order)
    /// - [`tree_order`](Self::tree_order)
    /// - [`transitive_closure`](Self::transitive_closure)
    pub fn linear_order<T: Borrow<Sort<Dynamic>>>(a: T, id: usize) -> Self {
        let a = a.borrow();
        let ctx = &a.ctx;
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_linear_order(ctx.z3_ctx.0, a.z3_sort, id as u32).unwrap(),
            )
        }
    }

    /// Create a tree order [`FuncDecl`] "Special Relation" over the given [`Sort`].
    ///
    /// See <https://microsoft.github.io/z3guide/docs/theories/Special%20Relations/> for more info.
    ///
    /// # See also
    ///
    /// - [`partial_order`](Self::partial_order)
    /// - [`piecewise_linear_order`](Self::piecewise_linear_order)
    /// - [`linear_order`](Self::linear_order)
    /// - [`transitive_closure`](Self::transitive_closure)
    pub fn tree_order<T: Borrow<Sort<Dynamic>>>(a: T, id: usize) -> Self {
        let a = a.borrow();
        let ctx = &a.ctx;
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_tree_order(ctx.z3_ctx.0, a.z3_sort, id as u32).unwrap(),
            )
        }
    }

    /// Create a transitive closure [`FuncDecl`] "Special Relation" over the given [`FuncDecl`].
    ///
    /// See <https://microsoft.github.io/z3guide/docs/theories/Special%20Relations/> for more info.
    ///
    /// # See also
    ///
    /// - [`partial_order`](Self::partial_order)
    /// - [`piecewise_linear_order`](Self::piecewise_linear_order)
    /// - [`linear_order`](Self::linear_order)
    /// - [`tree_order`](Self::tree_order)
    pub fn transitive_closure<T: Borrow<Self>>(a: T) -> Self {
        let a = a.borrow();
        let ctx = &a.ctx;
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_transitive_closure(ctx.z3_ctx.0, a.z3_func_decl).unwrap(),
            )
        }
    }
}

impl<A: FuncDeclDomain, R: FuncDeclReturn> fmt::Display for FuncDecl<A, R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_func_decl_to_string(self.ctx.z3_ctx.0, self.z3_func_decl) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{s}"),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<A: FuncDeclDomain, R: FuncDeclReturn> fmt::Debug for FuncDecl<A, R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<A: FuncDeclDomain, R: FuncDeclReturn> Drop for FuncDecl<A, R> {
    fn drop(&mut self) {
        unsafe {
            Z3_dec_ref(
                self.ctx.z3_ctx.0,
                Z3_func_decl_to_ast(self.ctx.z3_ctx.0, self.z3_func_decl).unwrap(),
            );
        }
    }
}

unsafe impl<A: FuncDeclDomain, R: FuncDeclReturn> Translate for FuncDecl<A, R> {
    fn translate(&self, dest: &Context) -> Self {
        unsafe {
            let func_decl_ast = Z3_func_decl_to_ast(self.ctx.z3_ctx.0, self.z3_func_decl).unwrap();
            let translated = Z3_translate(self.ctx.z3_ctx.0, func_decl_ast, dest.z3_ctx.0).unwrap();
            let func_decl = Z3_to_func_decl(self.ctx.z3_ctx.0, translated).unwrap();
            Self::wrap(dest, func_decl)
        }
    }
}

#[cfg(test)]
mod test {
    use crate::ast::Bool;
    use crate::{Config, FuncDecl, PrepareSynchronized, Sort, with_z3_config};

    #[test]
    pub fn test_translate_func_decl() {
        let f = FuncDecl::new("foo", Sort::bool(), Sort::bool());
        let ff = f.synchronized();
        with_z3_config(&Config::new(), || {
            let f = ff.recover();
            assert_eq!(f.name(), "foo");
            assert_eq!(f.arity(), 1);
            // `apply` returns a concrete `Bool` directly -- no `.as_bool().unwrap()` needed.
            let _: Bool = f.apply(Bool::from_bool(true));
        });
    }

    #[test]
    pub fn test_func_decl_typed_domain_and_range() {
        // Sort<Int> domain + Sort<Int> range yields a FuncDecl whose `apply` returns a
        // concrete `Int`, not `Dynamic` -- no `.as_int().unwrap()` needed at the call site.
        use crate::ast::Int;

        let f = FuncDecl::new("f", Sort::int(), Sort::int());
        let three: Int = f.apply(Int::from_i64(3));
        assert_eq!(three.as_i64(), None); // symbolic application, not evaluated by a model
    }
}
