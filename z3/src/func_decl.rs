use crate::ast::{Array, BV, Bool, Datatype, Dynamic, Int, Real, Seq, Set};
use crate::{Context, FuncDecl, Sort, Symbol, Translate, ast, ast::Ast};
use std::borrow::Borrow;
use std::convert::TryInto;
use std::ffi::CStr;
use std::fmt;
use std::marker::PhantomData;
use z3_sys::*;

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
            phantom_a: PhantomData::default(),
            phantom_r: PhantomData::default(),
        }
    }

    pub fn new<S: Into<Symbol>>(name: S, domain: A, range: Sort<R>) -> Self {
        let ctx = &Context::thread_local();

        assert_eq!(ctx.z3_ctx, range.ctx.z3_ctx);

        let domain: Vec<_> = domain.sorts().iter().map(|s| s.z3_sort).collect();
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
    /// # use z3::ast::{Bool, Int};
    ///
    ///   let sort = Sort::int();
    ///   let partial_order = FuncDecl::partial_order(&sort, 0);
    ///   // Create a solver to assert properties of the partial order.
    ///   let solver = Solver::new();
    ///   let x = Int::new_const("x");
    ///   let y = Int::new_const("y");
    ///   let z = Int::new_const("z");
    ///
    ///   solver.assert(&partial_order.apply(&[&x, &x]).as_bool().unwrap());
    ///   // test reflexivity
    ///   assert_eq!(
    ///       solver.check_assumptions(&[partial_order.apply(&[&x, &x]).as_bool().unwrap().not()]),
    ///       SatResult::Unsat
    ///   );
    ///
    ///   // test antisymmetry
    ///   assert_eq!(
    ///       solver.check_assumptions(&[
    ///           partial_order.apply(&[&x, &y]).as_bool().unwrap(),
    ///           partial_order.apply(&[&y, &x]).as_bool().unwrap(),
    ///           x.eq(&y).not()
    ///       ]),
    ///       SatResult::Unsat
    ///   );
    ///
    ///   // test transitivity
    ///   assert_eq!(
    ///       solver.check_assumptions(&[
    ///           partial_order.apply(&[&x, &y]).as_bool().unwrap(),
    ///           partial_order.apply(&[&y, &z]).as_bool().unwrap(),
    ///           partial_order.apply(&[&x, &z]).as_bool().unwrap().not(),
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
    pub fn partial_order<T: Borrow<Sort<C>>, C>(a: T, id: usize) -> Self {
        let a = a.borrow();
        let ctx = &a.ctx;
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_partial_order(ctx.z3_ctx.0, a.z3_sort, id).unwrap(),
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
    pub fn piecewise_linear_order<T: Borrow<Sort<C>>, C>(a: T, id: usize) -> Self {
        let a = a.borrow();
        let ctx = &a.ctx;
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_piecewise_linear_order(ctx.z3_ctx.0, a.z3_sort, id).unwrap(),
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
    pub fn linear_order<T: Borrow<Sort<C>>, C>(a: T, id: usize) -> Self {
        let a = a.borrow();
        let ctx = &a.ctx;
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_linear_order(ctx.z3_ctx.0, a.z3_sort, id).unwrap(),
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
    pub fn tree_order<T: Borrow<Sort<C>>, C>(a: T, id: usize) -> Self {
        let a = a.borrow();
        let ctx = &a.ctx;
        unsafe { Self::wrap(ctx, Z3_mk_tree_order(ctx.z3_ctx.0, a.z3_sort, id).unwrap()) }
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
    pub fn transitive_closure<T: Borrow<FuncDecl<A, R>>>(a: T) -> Self {
        let a = a.borrow();
        let ctx = &a.ctx;
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_transitive_closure(ctx.z3_ctx.0, a.z3_func_decl).unwrap(),
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
    ///     &[&Sort::int(), &Sort::real()],
    ///     &Sort::int());
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
        let args: Vec<_> = args.map(|a| a.get_z3_ast()).collect();

        unsafe {
            ast::Dynamic::wrap(&self.ctx, {
                Z3_mk_app(
                    self.ctx.z3_ctx.0,
                    self.z3_func_decl,
                    args.len().try_into().unwrap(),
                    args.as_ptr(),
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
}

impl<A: FuncDeclDomain, R> fmt::Display for FuncDecl<A, R> {
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

impl<A: FuncDeclDomain, R> fmt::Debug for FuncDecl<A, R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<A: FuncDeclDomain, R> Drop for FuncDecl<A, R> {
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
    use crate::ast::{Ast, Bool};
    use crate::{Config, FuncDecl, PrepareSynchronized, Sort, with_z3_config};

    #[test]
    pub fn test_translate_func_decl() {
        let f = FuncDecl::new("foo", vec![Sort::bool().as_dyn()], Sort::bool());
        let ff = f.synchronized();
        with_z3_config(&Config::new(), || {
            let f = ff.recover();
            assert_eq!(f.name(), "foo");
            assert_eq!(f.arity(), 1);
            assert!(f.apply(vec![Bool::from_bool(true).as_dyn()]).as_bool().is_some());
        });
    }

    #[test]
    pub fn test_translate_func_decl2() {
        let f = FuncDecl::new("foo", Sort::bool(), Sort::bool());
        let ff = f.synchronized();
        with_z3_config(&Config::new(), || {
            let f = ff.recover();
            assert_eq!(f.name(), "foo");
            assert_eq!(f.arity(), 1);
            assert!(f.apply(Bool::from_bool(true)).as_bool().is_some());
        });
    }
}

pub trait FuncDeclDomain {
    type ApplicationParam;

    fn application_args(a: Self::ApplicationParam) -> Vec<Dynamic>;

    fn sorts(&self) -> Vec<Sort<Dynamic>>;
}

impl<A: Ast + Clone + 'static> FuncDeclDomain for Sort<A> {
    type ApplicationParam = A;

    fn application_args(a: Self::ApplicationParam) -> Vec<Dynamic> {
        vec![a.as_dyn()]
    }

    fn sorts(&self) -> Vec<Sort<Dynamic>> {
        vec![self.as_dyn()]
    }
}
impl FuncDeclDomain for Vec<Sort<Dynamic>> {
    type ApplicationParam = Vec<Dynamic>;

    fn application_args(a: Self::ApplicationParam) -> Vec<Dynamic> {
        a.iter().map(|x| x.as_dyn()).collect()
    }

    fn sorts(&self) -> Vec<Sort<Dynamic>> {
        self.to_vec()
    }
}

// Macro to implement FuncDeclDomain for tuples of FuncDeclDomain
macro_rules! impl_func_decl_domain_for_tuples {
    ($(($($T:ident),+)),+) => {
        $(
            impl<$($T: FuncDeclDomain),+> FuncDeclDomain for ($($T,)+) {
                type ApplicationParam = ($($T::ApplicationParam,)+);

                fn application_args(a: Self::ApplicationParam) -> Vec<Dynamic> {
                    let ($($T,)+) = a;
                    let mut args = Vec::new();
                    $(
                        args.extend($T::application_args($T));
                    )+
                    args
                }

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

impl FuncDeclDomain for () {
    type ApplicationParam = ();

    fn application_args(_a: Self::ApplicationParam) -> Vec<Dynamic> {
        vec![]
    }

    fn sorts(&self) -> Vec<Sort<Dynamic>> {
        vec![]
    }
}

// Implement for tuples up to arity 5 (can be extended as needed)
impl_func_decl_domain_for_tuples!(
    (A),
    (A, B),
    (A, B, C),
    (A, B, C, D),
    (A, B, C, D, E),
    (A, B, C, D, E, F)
);

pub trait FuncDeclReturn {
    fn process(d: ast::Dynamic) -> Self;
}

impl FuncDeclReturn for BV {
    fn process(d: Dynamic) -> Self {
        d.as_bv().unwrap()
    }
}

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

mod duh {
    use crate::ast::{BV, Int};
    use crate::{FuncDecl, Sort};

    fn test_func_decl() {
        let a = FuncDecl::new("f", (Sort::int(), Sort::bitvector(5)), Sort::int());
        let i = Int::new_const("sdf");
        let b = BV::new_const("sf", 5);
        let b = a.apply((i, b));
    }
}
