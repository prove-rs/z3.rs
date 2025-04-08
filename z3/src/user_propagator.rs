//! Z3's [User Propagator](https://microsoft.github.io/z3guide/programming/Example%20Programs/User%20Propagator/) API

// I am following quite closly this: https://z3prover.github.io/api/html/classz3_1_1user__propagator__base.html

use crate::{
    ast::Ast,
    ast::{self, Dynamic},
    Context, Solver,
};
use log::debug;
use std::{convert::TryInto, fmt::Debug, marker::PhantomData, pin::Pin};
use z3_sys::*;

/// Interface to build a custom [User
/// Propagator](https://microsoft.github.io/z3guide/programming/Example%20Programs/User%20Propagator/)
///
/// All function fowllow their C++ counterparts in the
/// [`user_propagator_base`](https://z3prover.github.io/api/html/classz3_1_1user__propagator__base.html).
/// Callbacks can be made though the `upw` paramter. Those callbacks my panic if
/// called from a wrong place.
///
/// By default all function are implemented and do nothing
#[allow(unused_variables)]
pub trait UserPropagator<'ctx>: Debug {
    fn get_context(&self) -> &'ctx Context;

    /// Called when z3 case splits
    fn push(&self, cb: &CallBack<'ctx>) {}

    /// Called when z3 backtracks `num_scopes` times
    fn pop(&self, cb: &CallBack<'ctx>, num_scopes: u32) {}

    /// Called when `id` is fixed to value `e`
    fn fixed(&self, cb: &CallBack<'ctx>, id: &Dynamic<'ctx>, e: &Dynamic<'ctx>) {}

    /// Called when `x` and `y` are equated.
    ///
    /// This can be somewhat unreliable as z3 may call this less time than you'd
    /// expect.
    ///
    /// See:
    /// <https://microsoft.github.io/z3guide/programming/Example%20Programs/User%20Propagator/#equality-callbacks>
    fn eq(&self, cb: &CallBack<'ctx>, x: &Dynamic<'ctx>, y: &Dynamic<'ctx>) {}

    /// Same as [eq] be on negated equalities
    fn neq(&self, cb: &CallBack<'ctx>, x: &Dynamic<'ctx>, y: &Dynamic<'ctx>) {}

    /// During the final check stage, all propagations have been processed. This
    /// is an opportunity for the user-propagator to delay some analysis that
    /// could be expensive to perform incrementally. It is also an opportunity
    /// for the propagator to implement branch and bound optimization.
    fn final_(&self, cb: &CallBack<'ctx>) {}

    /// `e` was created using one of the function declared with
    /// [`declare_up_function`].
    ///
    /// Remeber to register those expressions! (using [`CallBack::add`] or
    /// [`UPSolver::add`] depending on the calling location)
    ///
    /// **NB**: there is no way to declare a function for specific
    /// [`UserPropagator`].
    ///
    /// [UPSolver::add]: super::UPSolver::add
    fn created(&self, cb: &CallBack<'ctx>, e: &Dynamic<'ctx>) {}

    fn decide(&self, cb: &CallBack<'ctx>, val: &Dynamic<'ctx>, bit: u32, is_pos: bool) {}

    // TODO: figure out how to make fresh work
    // fn fresh<'a>(
    //     upw: &'a UserPropagatorWrapper<'ctx>,
    //     ctx: &'a Context,
    // ) -> Option<&'a dyn UserPropagator<'a>> {
    //     None
    // }
}

#[derive(Debug)]
pub struct CallBack<'ctx> {
    cb: Z3_solver_callback,
    ctx: &'ctx Context,
}

impl<'ctx> CallBack<'ctx> {
    pub fn new(cb: Z3_solver_callback, ctx: &'ctx Context) -> Self {
        Self { cb, ctx }
    }

    /// Sets the next (registered) expression to split on. The function returns
    /// false and ignores the given expression in case the expression is already
    /// assigned internally (due to relevancy propagation, this assignments
    /// might not have been reported yet by the fixed callback). In case the
    /// function is called in the decide callback, it overrides the currently
    /// selected variable and phase.
    ///
    /// panics if not called from a callback
    ///
    /// see [`Z3_solver_next_split`]
    pub fn next_split(&self, expr: &ast::Bool<'ctx>, idx: u32, phase: Option<bool>) -> bool {
        debug_assert_eq!(self.get_ctx(), expr.get_ctx());
        let phase = match phase {
            Some(true) => Z3_L_TRUE,
            Some(false) => Z3_L_FALSE,
            None => Z3_L_UNDEF,
        };
        unsafe { Z3_solver_next_split(self.z3_ctx(), self.cb, expr.get_z3_ast(), idx, phase) }
    }

    /// Tracks `expr` with ([`UserPropagator::fixed()`] or`UserPropagator::eq()`()])
    ///
    /// If `expr` is a Boolean or Bit-vector, the [`UserPropagator::fixed()`]
    /// callback gets invoked when `expr` is bound to a value.a Equalities
    /// between registered expressions  are reported thought
    /// [`UserPropagator::eq()`]. A consumer can use the`Self::propagate`te] or
    /// [`Self::conflict`] functions to invoke propagations or conflicts as a
    /// consequence of these callbacks. These functions take a list of
    /// identifiers for registered expressions that have been fixed. The list of
    /// identifiers must correspond to already fixed values. Similarly, a list
    /// of propagated equalities can be supplied. These must correspond to
    /// equalities that have been registered during a callback.
    ///
    /// see [`Z3_solver_propagate_register_cb`] and [`Z3_solver_propagate_register`]
    pub fn add(&self, expr: &impl Ast<'ctx>) {
        debug_assert_eq!(self.get_ctx(), expr.get_ctx());
        unsafe { Z3_solver_propagate_register_cb(self.z3_ctx(), self.cb, expr.get_z3_ast()) };
    }

    /// Propagate a consequence based on fixed values and equalities.
    ///
    /// A client may invoke it during the `propagate_fixed`, `propagate_eq`,
    /// `propagate_diseq`, and `propagate_final` callbacks. The callback adds a
    /// propagation consequence based on the fixed values passed ids and
    /// equalities eqs based on parameters lhs, rhs.
    ///
    /// The solver might discard the propagation in case it is true in the
    /// current state. The function returns false in this case; otw. the
    /// function returns true. At least one propagation in the final callback
    /// has to return true in order to prevent the solver from finishing.
    ///
    /// - `fixed`: iterator containing terms that are fixed in the current scope
    /// - `lhs`: left side of equalities
    /// - `rhs`: right side of equalities
    /// - `conseq`: consequence to propagate. It is typically an atomic formula,
    ///             but it can be an arbitrary formula.
    ///
    /// panics if not called from a callback or if `lhs` and `rhs` don't have the same
    /// length.
    ///
    /// see [`Z3_solver_propagate_consequence`]
    pub fn propagate<'b, I, J, A>(
        &'b self,
        fixed: I,
        lhs: J,
        rhs: J,
        conseq: &'b ast::Bool<'ctx>,
    ) -> bool
    where
        I: IntoIterator<Item = &'b ast::Bool<'ctx>>,
        J: IntoIterator<Item = &'b A>,
        A: Ast<'ctx> + 'b,
    {
        /* using generics because I need to map on the arguments anyway and it will turn
        the other functions defined from `propagate` into the same things as the C++
        API this is based on */
        fn into_vec_and_check<'ctx, 'b, A: Ast<'ctx> + 'b>(
            ctx: &'ctx Context,
            iter: impl IntoIterator<Item = &'b A>,
        ) -> Vec<Z3_ast> {
            iter.into_iter()
                .inspect(|e| debug_assert_eq!(ctx, e.get_ctx()))
                .map(|e| e.get_z3_ast())
                .collect()
        }
        debug_assert_eq!(self.get_ctx(), conseq.get_ctx());
        let fixed = into_vec_and_check(self.get_ctx(), fixed);
        let lhs = into_vec_and_check(self.get_ctx(), lhs);
        let rhs = into_vec_and_check(self.get_ctx(), rhs);
        let conseq = conseq.get_z3_ast();
        assert_eq!(lhs.len(), rhs.len());

        // not sure what the API does exactly, but it probably expects null pointers
        // rather than dangling ones in case of empty vecs
        let to_ptr = |v: Vec<_>| {
            if v.is_empty() {
                ::std::ptr::null()
            } else {
                v.as_ptr()
            }
        };

        unsafe {
            Z3_solver_propagate_consequence(
                self.z3_ctx(),
                self.cb,
                fixed.len().try_into().unwrap(),
                to_ptr(fixed),
                lhs.len().try_into().unwrap(),
                to_ptr(lhs),
                to_ptr(rhs),
                conseq,
            )
        }
    }

    /// triggers a confict on `fixed`
    ///
    /// Equivalent to [`self.propagate(fixed, [] , [], FALSE)`](Self::propagate)
    ///
    /// panics if not called from a callback.
    pub fn conflict_on(&self, fixed: &[&ast::Bool<'ctx>]) -> bool {
        self.propagate::<_, _, ast::Bool<'ctx>>(
            fixed.iter().copied(),
            [],
            [],
            &ast::Bool::from_bool(self.get_ctx(), false),
        )
    }

    /// triggers a confict on `fixed` and `lhs == rhs`
    ///
    /// Equivalent to [`self.propagate(fixed, lhs, rhs, FALSE)`](Self::propagate)
    ///
    /// panics if not called from a callback or if `lhs` and `rhs` don't have the same
    /// length.
    pub fn conflict(
        &self,
        fixed: &[&ast::Bool<'ctx>],
        lhs: &[&ast::Dynamic<'ctx>],
        rhs: &[&ast::Dynamic<'ctx>],
    ) -> bool {
        self.propagate(
            fixed.iter().copied(),
            lhs.iter().copied(),
            rhs.iter().copied(),
            &ast::Bool::from_bool(self.get_ctx(), false),
        )
    }

    /// Propagate `conseq`
    ///
    /// Equivalent to [`self.propagate(fixed, [], [], conseq)`](Self::propagate)
    ///
    /// panics if not called from a callback.
    pub fn propagate_one(&self, fixed: &[&ast::Bool<'ctx>], conseq: &ast::Bool<'ctx>) -> bool {
        self.propagate::<_, _, ast::Bool>(fixed.iter().copied(), [], [], conseq)
    }

    pub fn get_ctx(&self) -> &'ctx Context {
        self.ctx
    }

    fn z3_ctx(&self) -> Z3_context {
        self.get_ctx().z3_ctx
    }
}

/// The `on_clause` callback
///
/// a callback that is invoked by when a clause is
/// - asserted to the CDCL engine (corresponding to an input clause after pre-processing)
/// - inferred by CDCL(T) using either a SAT or theory conflict/propagation
/// - deleted by the CDCL(T) engine
pub trait OnClause<'ctx>: Debug {
    fn get_ctx(&self) -> &'ctx Context;
    /// the callback
    fn on_clause(&self, proof_hint: &Dynamic<'ctx>, deps: &[u32], literals: &[Dynamic<'ctx>]);
}

/// A quick way to implement [`OnClause`] using a clausure
pub struct ClausureOnClause<'ctx, F>
where
    F: Fn(&Dynamic<'ctx>, &[u32], &[Dynamic<'ctx>]),
{
    ctx: &'ctx Context,
    f: F,
}

impl<'ctx, F> ClausureOnClause<'ctx, F>
where
    F: Fn(&Dynamic<'ctx>, &[u32], &[Dynamic<'ctx>]),
{
    pub fn new(ctx: &'ctx Context, f: F) -> Self {
        Self { ctx, f }
    }
}
impl<'ctx, F> Debug for ClausureOnClause<'ctx, F>
where
    F: Fn(&Dynamic<'ctx>, &[u32], &[Dynamic<'ctx>]),
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ClausureOnClause")
            .field("ctx", &self.ctx)
            .field("f", &std::any::type_name::<F>())
            .finish()
    }
}

impl<'ctx, F> OnClause<'ctx> for ClausureOnClause<'ctx, F>
where
    F: Fn(&Dynamic<'ctx>, &[u32], &[Dynamic<'ctx>]),
{
    fn get_ctx(&self) -> &'ctx Context {
        self.ctx
    }

    fn on_clause(&self, proof_hint: &Dynamic<'ctx>, deps: &[u32], literals: &[Dynamic<'ctx>]) {
        (self.f)(proof_hint, deps, literals)
    }
}

/// Wrapper around a solver to ensure the [`UserPropagator`]s live long enough
///
/// `'ctx` is the liftime of the [Context] and `'a` the commun liftime of the
/// [`UserPropagator`]s
///
/// [Context]: crate::Context
#[derive(Debug)]
pub struct UPSolver<'ctx, 'a> {
    solver: Solver<'ctx>,
    user_propagators: PhantomData<Pin<&'a dyn UserPropagator<'ctx>>>,
    on_clause_propagators: PhantomData<Pin<&'a dyn OnClause<'ctx>>>,
}

impl<'ctx, 'a> UPSolver<'ctx, 'a> {
    pub fn new(solver: Solver<'ctx>) -> Self {
        Self {
            solver,
            user_propagators: Default::default(),
            on_clause_propagators: Default::default(),
        }
    }

    pub fn solver(&self) -> &Solver<'ctx> {
        &self.solver
    }

    /// Add an expression to be tracked by all [`UserPropagator`]s registered to this solver
    pub fn add(&self, expr: &impl Ast<'ctx>) {
        let z3_ctx = self.solver().get_context().z3_ctx;
        let z3_slv = self.solver().z3_slv;
        unsafe { Z3_solver_propagate_register(z3_ctx, z3_slv, expr.get_z3_ast()) }
    }

    /// Registers a [`UserPropagator`] to [`Self::solver`]
    ///
    /// We need `up` to be pined because it will be passed auround to z3. See
    /// [`std::pin`] to get to know how to use [Pin].
    pub fn register_user_propagator<U: UserPropagator<'ctx>>(&mut self, up: Pin<&'a U>) {
        unsafe { z3_user_propagator_init(up, self.solver().z3_slv) }
    }

    pub fn register_on_clause<U: OnClause<'ctx>>(&mut self, up: Pin<&'a U>) {
        let s = self.z3_slv;
        let c = self.ctx.z3_ctx;
        let user_ctx = up.get_ref() as *const _ as *mut ::std::ffi::c_void;
        unsafe {
            Z3_solver_register_on_clause(c, s, user_ctx, Some(callbacks::clause_eh::<U>));
        }
    }
}

impl<'ctx> From<Solver<'ctx>> for UPSolver<'ctx, '_> {
    fn from(solver: Solver<'ctx>) -> Self {
        Self::new(solver)
    }
}

impl<'ctx> std::ops::Deref for UPSolver<'ctx, '_> {
    type Target = Solver<'ctx>;

    fn deref(&self) -> &Self::Target {
        &self.solver
    }
}

// =========================================================
// =============== implementation details ==================
// =========================================================

/// Does all the z3 calls to register a new [`UserPropagator`].
///
/// At this point `z3_slv` effectively borrows `up`. I need
/// [`super::UPSolver`] to solver the liftetime problems, hence why to
/// function is `unsafe`.
pub(crate) unsafe fn z3_user_propagator_init<'ctx, U: UserPropagator<'ctx>>(
    up: Pin<&U>,
    z3_slv: Z3_solver,
) {
    let z3_ctx = up.get_context().z3_ctx;
    debug!("Z3_solver_propagate_init");
    Z3_solver_propagate_init(
        z3_ctx,
        z3_slv,
        up.get_ref() as *const _ as *mut ::std::ffi::c_void,
        Some(callbacks::push_eh::<U>),
        Some(callbacks::pop_eh::<U>),
        Some(callbacks::fresh_eh::<U>),
    );
    // we register all callbacks
    // fixed
    debug!("Z3_solver_propagate_fixed");
    Z3_solver_propagate_fixed(z3_ctx, z3_slv, Some(callbacks::fixed_eh::<U>));
    // eq
    debug!("Z3_solver_propagate_eq");
    Z3_solver_propagate_eq(z3_ctx, z3_slv, Some(callbacks::eq_eh::<U>));
    // eq
    debug!("Z3_solver_propagate_diseq");
    Z3_solver_propagate_diseq(z3_ctx, z3_slv, Some(callbacks::neq_eh::<U>));
    // final
    debug!("Z3_solver_propagate_final");
    Z3_solver_propagate_final(z3_ctx, z3_slv, Some(callbacks::final_eh::<U>));
    // created
    debug!("Z3_solver_propagate_created");
    Z3_solver_propagate_created(z3_ctx, z3_slv, Some(callbacks::created_eh::<U>));
    // decide
    debug!("Z3_solver_propagate_decide");
    Z3_solver_propagate_decide(z3_ctx, z3_slv, Some(callbacks::decide_eh::<U>));
}

/// all the callbacks used in this file
mod callbacks {
    use crate::{
        ast::{Ast, Dynamic},
        user_propagator::{CallBack, OnClause, UserPropagator},
    };
    use log::debug;
    use std::convert::TryInto;
    use z3_sys::*;

    /// Turns a `void*` into a `&mut Self`.
    ///
    /// This is highly unsafe! It panics if the pointer is `null`, no other checks are made!
    unsafe fn mut_from_user_context<'ctx, 'b, U: UserPropagator<'ctx>>(
        ptr: *mut ::std::ffi::c_void,
    ) -> &'b mut U {
        (ptr as *mut U).as_mut().unwrap()
    }

    pub(crate) extern "C" fn push_eh<'ctx, U: UserPropagator<'ctx>>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
    ) {
        debug!("push_eh");
        let up = unsafe { mut_from_user_context::<U>(ctx) };
        up.push(&CallBack::new(cb, up.get_context()));
    }

    pub(crate) extern "C" fn pop_eh<'ctx, U: UserPropagator<'ctx>>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        num_scopes: ::std::os::raw::c_uint,
    ) {
        debug!("pop_eh");
        let up = unsafe { mut_from_user_context::<U>(ctx) };
        up.pop(&CallBack::new(cb, up.get_context()), num_scopes);
    }

    // TODO: figure out how to make this work
    #[allow(unused_variables)]
    #[allow(clippy::extra_unused_type_parameters)]
    pub(crate) extern "C" fn fresh_eh<'ctx, U: UserPropagator<'ctx>>(
        ctx: *mut ::std::ffi::c_void,
        new_context: Z3_context,
    ) -> *mut ::std::ffi::c_void {
        ::std::ptr::null_mut()
    }

    pub(crate) extern "C" fn fixed_eh<'ctx, U: UserPropagator<'ctx>>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        var: Z3_ast,
        value: Z3_ast,
    ) {
        debug!("fixed_eh");
        let up = unsafe { mut_from_user_context::<U>(ctx) };
        let var = unsafe { Dynamic::wrap(up.get_context(), var) };
        let value = unsafe { Dynamic::wrap(up.get_context(), value) };
        up.fixed(&CallBack::new(cb, up.get_context()), &var, &value);
    }

    pub(crate) extern "C" fn eq_eh<'ctx, U: UserPropagator<'ctx>>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        x: Z3_ast,
        y: Z3_ast,
    ) {
        debug!("eq_eh");
        let up = unsafe { mut_from_user_context::<U>(ctx) };
        let x = unsafe { Dynamic::wrap(up.get_context(), x) };
        let y = unsafe { Dynamic::wrap(up.get_context(), y) };
        up.eq(&CallBack::new(cb, up.get_context()), &x, &y);
    }

    pub(crate) extern "C" fn neq_eh<'ctx, U: UserPropagator<'ctx>>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        x: Z3_ast,
        y: Z3_ast,
    ) {
        debug!("neq_eh");
        let up = unsafe { mut_from_user_context::<U>(ctx) };
        let x = unsafe { Dynamic::wrap(up.get_context(), x) };
        let y = unsafe { Dynamic::wrap(up.get_context(), y) };
        up.neq(&CallBack::new(cb, up.get_context()), &x, &y);
    }

    pub(crate) extern "C" fn final_eh<'ctx, U: UserPropagator<'ctx>>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
    ) {
        debug!("final_eh");
        let up = unsafe { mut_from_user_context::<U>(ctx) };
        up.final_(&CallBack::new(cb, up.get_context()));
    }

    pub(crate) extern "C" fn created_eh<'ctx, U: UserPropagator<'ctx>>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        e: Z3_ast,
    ) {
        debug!("created_eh");
        let up = unsafe { mut_from_user_context::<U>(ctx) };
        let e = unsafe { Dynamic::wrap(up.get_context(), e) };
        up.created(&CallBack::new(cb, up.get_context()), &e);
    }

    pub(crate) extern "C" fn decide_eh<'ctx, U: UserPropagator<'ctx>>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        val: Z3_ast,
        bit: ::std::os::raw::c_uint,
        is_pos: bool,
    ) {
        debug!("decide_eh");
        let up = unsafe { mut_from_user_context::<U>(ctx) };
        let val = unsafe { Dynamic::wrap(up.get_context(), val) };
        up.decide(&CallBack::new(cb, up.get_context()), &val, bit, is_pos);
    }

    pub(crate) unsafe extern "C" fn clause_eh<'ctx, U: OnClause<'ctx>>(
        ctx: *mut ::std::ffi::c_void,
        proof_hint: Z3_ast,
        n: ::std::os::raw::c_uint,
        deps: *const ::std::os::raw::c_uint,
        literals: Z3_ast_vector,
    ) {
        debug!("clause_eh {n} {deps:?}");
        let oc = (ctx as *mut U).as_mut().unwrap();
        let n: usize = n.try_into().unwrap();
        let deps = if n == 0 {
            &[]
        } else {
            std::slice::from_raw_parts(deps, n)
        };
        let literals: Vec<_> = (0..Z3_ast_vector_size(oc.get_ctx().get_z3_context(), literals))
            .map(|i| {
                Dynamic::wrap(
                    oc.get_ctx(),
                    Z3_ast_vector_get(oc.get_ctx().get_z3_context(), literals, i),
                )
            })
            .collect();
        let proof_hint = Dynamic::wrap(oc.get_ctx(), proof_hint);
        oc.on_clause(&proof_hint, deps, &literals);
    }
}

#[cfg(test)]
mod test {
    use std::convert::TryInto;

    use crate::{
        ast::{self, Ast, Dynamic},
        user_propagator::{CallBack, ClausureOnClause, UPSolver, UserPropagator},
        Config, Context, FuncDecl, Solver, Sort,
    };

    #[test]
    fn on_clause() {
        let _ = env_logger::try_init();
        let mut cfg = Config::default();
        cfg.set_model_generation(true);
        cfg.set_proof_generation(true);
        let ctx = Context::new(&cfg);
        let s_sort = Sort::uninterpreted(&ctx, "S".into());
        let f = FuncDecl::new(&ctx, "f", &[&s_sort], &s_sort);
        let g = FuncDecl::new(&ctx, "g", &[&s_sort], &Sort::bool(&ctx));
        let x = FuncDecl::new(&ctx, "x", &[], &s_sort).apply(&[]);
        let mut s = UPSolver::new(Solver::new(&ctx));

        let on_clause = Box::pin(ClausureOnClause::new(&ctx, |proof_hint, deps, literals| {
            println!("on_clause:\n\tproof_hint: {proof_hint:}\n\tdeps: {deps:?}\n\tliteral: {literals:?}")
        }));
        s.register_on_clause(on_clause.as_ref());

        let gx = g.apply(&[&x]).as_bool().unwrap();
        let gxx = g.apply(&[&f.apply(&[&f.apply(&[&x])])]).as_bool().unwrap();

        s.assert(&!(&gx & &gxx));
        s.assert(&(&gx | &gxx));
        s.assert(&f.apply(&[&x])._eq(&x));
        s.check();
        println!("result: {:?}", s.check());
        println!("{:?}", s.get_model());
    }

    #[test]
    fn user_propagator() {
        /* proves f(f(f(f(x)))) = f(x) with a up that rewrites f(f(x)) into f(x) */
        let _ = env_logger::try_init();
        let mut cfg = Config::default();
        cfg.set_model_generation(true);
        let ctx = Context::new(&cfg);
        let s_sort = Sort::uninterpreted(&ctx, "S".into());
        let f = FuncDecl::new_up(&ctx, "f", &[&s_sort], &s_sort);
        let x = FuncDecl::new(&ctx, "x", &[], &s_sort).apply(&[]);
        let s = Solver::new(&ctx);

        #[derive(Debug)]
        struct UP<'ctx> {
            pub f: &'ctx FuncDecl<'ctx>,
            pub ctx: &'ctx Context,
        }

        impl<'ctx> UP<'ctx> {
            fn generate_next_term(&self, e: &Dynamic<'ctx>) -> Option<Dynamic<'ctx>> {
                let f1 = e.safe_decl().ok()?;
                (f1.name() == self.f.name()).then_some(())?; // exits if f1 != f
                let [arg1] = e.children().try_into().ok()?;
                let f2 = e.safe_decl().ok()?;
                (f2.name() == self.f.name()).then_some(())?;
                let [arg2] = arg1.children().try_into().ok()?;

                let nt = self.f.apply(&[&arg2]);
                println!("propagating: {e} = {nt}");
                Some(nt)
            }
        }

        impl<'ctx> UserPropagator<'ctx> for UP<'ctx> {
            fn eq(&self, upw: &CallBack<'ctx>, x: &Dynamic<'ctx>, y: &Dynamic<'ctx>) {
                println!("eq: {x} = {y}");
                for e in [x, y] {
                    let Some(nt) = self.generate_next_term(e) else {
                        continue;
                    };
                    upw.propagate_one(&[], &e._eq(&nt));
                }
            }

            fn neq(&self, upw: &CallBack<'ctx>, x: &Dynamic<'ctx>, y: &Dynamic<'ctx>) {
                println!("neq: {x} != {y}");
                for e in [x, y] {
                    let Some(nt) = self.generate_next_term(e) else {
                        continue;
                    };
                    upw.propagate_one(&[], &e._eq(&nt));
                }
            }

            fn created(&self, _: &CallBack<'ctx>, e: &ast::Dynamic<'ctx>) {
                println!("created: {e}")
            }

            fn pop(&self, _: &CallBack<'ctx>, num_scopes: u32) {
                println!("pop: {num_scopes:}")
            }

            fn push(&self, _: &CallBack<'ctx>) {
                println!("push")
            }

            fn decide(&self, _: &CallBack<'ctx>, val: &ast::Dynamic<'ctx>, bit: u32, is_pos: bool) {
                println!("decide: {val}, {bit:} {is_pos}")
            }

            fn fixed(&self, _: &CallBack<'ctx>, id: &ast::Dynamic<'ctx>, e: &ast::Dynamic<'ctx>) {
                println!("fixed: {id} {e}")
            }

            fn final_(&self, _: &CallBack<'ctx>) {
                println!("final")
            }

            fn get_context(&self) -> &'ctx Context {
                self.ctx
            }
        }

        let mut s = UPSolver::new(s);
        let up = Box::pin(UP { f: &f, ctx: &ctx });
        s.register_user_propagator(up.as_ref());
        s.assert(
            &f.apply(&[&f.apply(&[&f.apply(&[&f.apply(&[&x])])])])
                ._eq(&f.apply(&[&x]))
                .not(),
        );
        println!("result: {:?}", s.check());
    }
}
