//! Z3's [User Propagator](https://microsoft.github.io/z3guide/programming/Example%20Programs/User%20Propagator/) API

// I am following quite closly this: https://z3prover.github.io/api/html/classz3_1_1user__propagator__base.html

use crate::{
    ast::Ast,
    ast::{self, Dynamic},
    Context, Solver,
};
use log::debug;
use std::{cell::RefCell, convert::TryInto, default, fmt::Debug, pin::Pin, rc::Weak};
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
pub trait UserPropagator: Debug {
    fn get_context(&self) -> &Context;

    /// Called when z3 case splits
    fn push(&mut self, cb: &CallBack) {}

    /// Called when z3 backtracks `num_scopes` times
    fn pop(&mut self, cb: &CallBack, num_scopes: u32) {}

    /// Called when `id` is fixed to value `e`
    fn fixed(&mut self, cb: &CallBack, id: &Dynamic, e: &Dynamic) {}

    /// Called when `x` and `y` are equated.
    ///
    /// This can be somewhat unreliable as z3 may call this less time than you'd
    /// expect.
    ///
    /// See:
    /// <https://microsoft.github.io/z3guide/programming/Example%20Programs/User%20Propagator/#equality-callbacks>
    fn eq(&mut self, cb: &CallBack, x: &Dynamic, y: &Dynamic) {}

    /// Same as [eq] be on negated equalities
    fn neq(&mut self, cb: &CallBack, x: &Dynamic, y: &Dynamic) {}

    /// During the final check stage, all propagations have been processed. This
    /// is an opportunity for the user-propagator to delay some analysis that
    /// could be expensive to perform incrementally. It is also an opportunity
    /// for the propagator to implement branch and bound optimization.
    fn final_(&mut self, cb: &CallBack) {}

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
    fn created(&mut self, cb: &CallBack, e: &Dynamic) {}

    fn decide(&mut self, cb: &CallBack, val: &Dynamic, bit: u32, is_pos: bool) {}

    /// Generate a new subsolver using the new `ctx`.
    /// 
    /// The garabage collection of said context will be handeled by [UPSolver].
    fn fresh<'a>(
        &mut self,
        ctx: Context,
    ) -> Option<Box<dyn UserPropagator + 'a>> where Self: 'a {
        None
    }
}


#[derive(Debug)]
pub struct CallBack{
    cb: Z3_solver_callback,
    ctx: Context,
}

impl CallBack {
    pub fn new(cb: Z3_solver_callback, ctx: &Context) -> Self {
        Self { cb, ctx: ctx.clone() }
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
    pub fn next_split(&self, expr: &ast::Bool, idx: u32, phase: Option<bool>) -> bool {
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
    pub fn add(&self, expr: &impl Ast) {
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
        conseq: &'b ast::Bool,
    ) -> bool
    where
        I: IntoIterator<Item = &'b ast::Bool>,
        J: IntoIterator<Item = &'b A>,
        A: Ast + 'b,
    {
        /* using generics because I need to map on the arguments anyway and it will turn
        the other functions defined from `propagate` into the same things as the C++
        API this is based on */
        fn into_vec_and_check< 'b, A: Ast + 'b>(
            ctx: &Context,
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
    pub fn conflict_on(&self, fixed: &[&ast::Bool]) -> bool {
        self.propagate::<_, _, ast::Bool>(
            fixed.iter().copied(),
            [],
            [],
            &ast::Bool::from_bool(false),
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
        fixed: &[&ast::Bool],
        lhs: &[&ast::Dynamic],
        rhs: &[&ast::Dynamic],
    ) -> bool {
        self.propagate(
            fixed.iter().copied(),
            lhs.iter().copied(),
            rhs.iter().copied(),
            &ast::Bool::from_bool(false),
        )
    }

    /// Propagate `conseq`
    ///
    /// Equivalent to [`self.propagate(fixed, [], [], conseq)`](Self::propagate)
    ///
    /// panics if not called from a callback.
    pub fn propagate_one(&self, fixed: &[&ast::Bool], conseq: &ast::Bool) -> bool {
        self.propagate::<_, _, ast::Bool>(fixed.iter().copied(), [], [], conseq)
    }

    pub fn get_ctx(&self) -> &Context {
        &self.ctx
    }

    fn z3_ctx(&self) -> Z3_context {
        self.get_ctx().z3_ctx.0
    }
}

/// The `on_clause` callback
///
/// a callback that is invoked by when a clause is
/// - asserted to the CDCL engine (corresponding to an input clause after pre-processing)
/// - inferred by CDCL(T) using either a SAT or theory conflict/propagation
/// - deleted by the CDCL(T) engine
pub trait OnClause: Debug {
    fn get_ctx(&self) -> &Context;
    /// the callback
    fn on_clause(&mut self, proof_hint: &Dynamic, deps: &[u32], literals: &[Dynamic]);
}

/// A quick way to implement [`OnClause`] using a clausure
struct ClausureOnClause<F>
where
    F: FnMut(&Dynamic, &[u32], &[Dynamic]),
{
    ctx: Context,
    f: F,
}

impl<'ctx, F> ClausureOnClause< F>
where
    F: FnMut(&Dynamic, &[u32], &[Dynamic]),
{
    pub fn new(ctx: Context, f: F) -> Self {
        Self { ctx, f }
    }
}
impl<'ctx, F> Debug for ClausureOnClause< F>
where
    F: FnMut(&Dynamic, &[u32], &[Dynamic]),
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ClausureOnClause")
            .field("ctx", &self.ctx)
            .field("f", &std::any::type_name::<F>())
            .finish()
    }
}

impl<'ctx, F> OnClause for ClausureOnClause<F>
where
    F: FnMut(&Dynamic, &[u32], &[Dynamic]),
{
    fn get_ctx(&self) -> &Context {
        &self.ctx
    }

    fn on_clause(&mut self, proof_hint: &Dynamic, deps: &[u32], literals: &[Dynamic]) {
        (self.f)(proof_hint, deps, literals)
    }
}

#[derive(Debug)]
struct PropagatorWrapper<'a, U: ?Sized> {
    parent: Weak<RefCell<Pin<Box<Self>>>>,
    propagator: U
}

/// Wrapper around a solver to ensure the [`UserPropagator`]s live long enough
///
/// `'ctx` is the liftime of the [Context] and `'a` the commun liftime of the
/// [`UserPropagator`]s
///
/// [Context]: crate::Context
#[derive(Debug)]
pub struct UPSolver<'a> {
    solver: Solver,
    user_propagators: Vec<Pin<Box<dyn UserPropagator + 'a>>>,
    on_clause_propagators: Vec<Pin<Box<dyn OnClause + 'a>>>,
}

impl<'ctx, 'a> UPSolver<'a> {
    pub fn new(solver: Solver) -> Self {
        Self {
            solver,
            user_propagators: Default::default(),
            on_clause_propagators: Default::default(),
        }
    }

    pub fn solver(&self) -> &Solver {
        &self.solver
    }

    /// Add an expression to be tracked by all [`UserPropagator`]s registered to this solver
    pub fn add(&self, expr: &impl Ast) {
        let z3_ctx = self.solver().get_context().z3_ctx.0;
        let z3_slv = self.solver().z3_slv;
        unsafe { Z3_solver_propagate_register(z3_ctx, z3_slv, expr.get_z3_ast()) }
    }

    /// Registers a [`UserPropagator`] to [`Self::solver`]
    pub fn register_user_propagator<U: UserPropagator + 'a>(&mut self, up: U) {
        let pin = Box::pin(up);
        unsafe { z3_user_propagator_init(pin.as_ref(), self.solver().z3_slv) }
        self.user_propagators.push(pin);
    }

    pub fn register_on_clause<U: OnClause + 'a>(&mut self, up: U) {
        let pin = Box::pin(up);
        let s = self.z3_slv;
        let c = self.ctx.z3_ctx.0;
        let user_ctx = pin.as_ref().get_ref() as *const _ as *mut ::std::ffi::c_void;
        unsafe {
            Z3_solver_register_on_clause(c, s, user_ctx, Some(callbacks::clause_eh::<U>));
        }
        self.on_clause_propagators.push(pin);
    }

    pub fn quick_register_on_clause<F>(&mut self, f: F)
    where
        F: FnMut(&Dynamic, &[u32], &[Dynamic]) + 'a,
        'ctx: 'a,
    {
        let ctx= self.solver().get_context();
        // let up: ClausureOnClause<'ctx, F> = ;
        self.register_on_clause(ClausureOnClause::new(ctx.clone(), f));
    }
}

impl From<Solver> for UPSolver<'_> {
    fn from(solver: Solver) -> Self {
        Self::new(solver)
    }
}

impl std::ops::Deref for UPSolver< '_> {
    type Target = Solver;

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
/// [`super::UPSolver`] to solve the liftetime problems, hence why to
/// function is `unsafe`.
#[allow(unsafe_op_in_unsafe_fn)] // <- litterally everything is unsafe in it
pub(crate) unsafe fn z3_user_propagator_init<'ctx, U: UserPropagator>(
    up: Pin<&U>,
    z3_slv: Z3_solver,
) {
    let z3_ctx = up.get_context().z3_ctx.0;
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
        Context, ast::{Ast, Dynamic}, user_propagator::{CallBack, OnClause, UserPropagator}
    };
    use log::debug;
    use std::convert::TryInto;
    use z3_sys::*;

    /// Turns a `void*` into a `&mut Self`.
    ///
    /// This is highly unsafe! It panics if the pointer is `null`, no other checks are made!
    unsafe fn mut_from_user_context<'ctx, 'b, U: UserPropagator>(
        ptr: *mut ::std::ffi::c_void,
    ) -> Option<&'b mut U> {
        unsafe { (ptr as *mut U).as_mut() }
    }

    pub(crate) extern "C" fn push_eh<'ctx, U: UserPropagator>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
    ) {
        debug!("push_eh");
        if let Some(up) = unsafe { mut_from_user_context::<U>(ctx) } {
            up.push(&CallBack::new(cb, up.get_context()));
        }
    }

    pub(crate) extern "C" fn pop_eh<'ctx, U: UserPropagator>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        num_scopes: ::std::os::raw::c_uint,
    ) {
        debug!("pop_eh");
        if let Some(up) = unsafe { mut_from_user_context::<U>(ctx) } {
        up.pop(&CallBack::new(cb, up.get_context()), num_scopes);}
    }

    #[allow(unused_variables)]
    #[allow(clippy::extra_unused_type_parameters)]
    pub(crate) extern "C" fn fresh_eh<'ctx, U: UserPropagator>(
        ctx: *mut ::std::ffi::c_void,
        new_context: Z3_context,
    ) -> *mut ::std::ffi::c_void {
        if let Some(up) = unsafe { mut_from_user_context::<U>(ctx) } {
            let ctx = unsafe { Context::from_raw(new_context) }; // hopefully it doesn't die...
            let ret = up.fresh(ctx);
            // match ret {
            //     Some(nup) => 
            //     None => ::std::ptr::null_mut(),
            // }
            todo!()

        } else {
        ::std::ptr::null_mut()
        }
    }

    pub(crate) extern "C" fn fixed_eh<'ctx, U: UserPropagator>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        var: Z3_ast,
        value: Z3_ast,
    ) {
        debug!("fixed_eh");
        if let Some(up) = unsafe { mut_from_user_context::<U>(ctx) } {
        let var = unsafe { Dynamic::wrap(up.get_context(), var) };
        let value = unsafe { Dynamic::wrap(up.get_context(), value) };
        up.fixed(&CallBack::new(cb, up.get_context()), &var, &value);
        }
    }

    pub(crate) extern "C" fn eq_eh<'ctx, U: UserPropagator>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        x: Z3_ast,
        y: Z3_ast,
    ) {
        debug!("eq_eh");
        if let Some(up) = unsafe { mut_from_user_context::<U>(ctx) } {
        let x = unsafe { Dynamic::wrap(up.get_context(), x) };
        let y = unsafe { Dynamic::wrap(up.get_context(), y) };
        up.eq(&CallBack::new(cb, up.get_context()), &x, &y);
        }
    }

    pub(crate) extern "C" fn neq_eh<'ctx, U: UserPropagator>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        x: Z3_ast,
        y: Z3_ast,
    ) {
        debug!("neq_eh");
        if let Some(up) = unsafe { mut_from_user_context::<U>(ctx) } {
        let x = unsafe { Dynamic::wrap(up.get_context(), x) };
        let y = unsafe { Dynamic::wrap(up.get_context(), y) };
        up.neq(&CallBack::new(cb, up.get_context()), &x, &y);
        }
    }

    pub(crate) extern "C" fn final_eh<'ctx, U: UserPropagator>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
    ) {
        debug!("final_eh");
        if let Some(up) = unsafe { mut_from_user_context::<U>(ctx) } {
        up.final_(&CallBack::new(cb, up.get_context()));
        }
    }

    pub(crate) extern "C" fn created_eh<'ctx, U: UserPropagator>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        e: Z3_ast,
    ) {
        debug!("created_eh");
        if let Some(up) = unsafe { mut_from_user_context::<U>(ctx) } {
        let e = unsafe { Dynamic::wrap(up.get_context(), e) };
        up.created(&CallBack::new(cb, up.get_context()), &e);
        }
    }

    pub(crate) extern "C" fn decide_eh<'ctx, U: UserPropagator>(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        val: Z3_ast,
        bit: ::std::os::raw::c_uint,
        is_pos: bool,
    ) {
        debug!("decide_eh");
        if let Some(up) = unsafe { mut_from_user_context::<U>(ctx) } {
        let val = unsafe { Dynamic::wrap(up.get_context(), val) };
        up.decide(&CallBack::new(cb, up.get_context()), &val, bit, is_pos);
        }
    }

    pub(crate) unsafe extern "C" fn clause_eh<U: OnClause>(
        ctx: *mut ::std::ffi::c_void,
        proof_hint: Z3_ast,
        n: ::std::os::raw::c_uint,
        deps: *const ::std::os::raw::c_uint,
        literals: Z3_ast_vector,
    ) {
        debug!("clause_eh {n} {deps:?}");
        let oc = unsafe {(ctx as *mut U).as_mut()}.unwrap();
        let n: usize = n.try_into().unwrap();
        let deps = if n == 0 {
            &[]
        } else {
            unsafe { std::slice::from_raw_parts(deps, n) }
        };
        let literals: Vec<_> = unsafe{0..Z3_ast_vector_size(oc.get_ctx().get_z3_context(), literals)}
            .map(|i| {
                unsafe { Dynamic::wrap(
                    oc.get_ctx(),
                    Z3_ast_vector_get(oc.get_ctx().get_z3_context(), literals, i).unwrap(),
                ) }
            })
            .collect();
        let proof_hint = unsafe { Dynamic::wrap(oc.get_ctx(), proof_hint) };
        oc.on_clause(&proof_hint, deps, &literals);
    }
}

#[cfg(test)]
mod test {
    use std::convert::TryInto;

    use crate::{
        ast::{self, Ast, Dynamic},
        user_propagator::{CallBack, UPSolver, UserPropagator},
        Config, Context, FuncDecl, Solver, Sort,
    };

    #[test]
    fn on_clause() {
        let _ = env_logger::try_init();
        let mut cfg = Config::default();
        cfg.set_model_generation(true);
        cfg.set_proof_generation(true);
        let ctx = Context::new(&cfg);
        let s_sort = Sort::uninterpreted( "S".into());
        let f = FuncDecl::new( "f", &[&s_sort], &s_sort);
        let g = FuncDecl::new( "g", &[&s_sort], &Sort::bool());
        let x = FuncDecl::new( "x", &[], &s_sort).apply(&[]);

        let mut y: String = "I am a non-static lifetime check".to_owned();
        {
            let mut s = UPSolver::new(Solver::new());

            s.quick_register_on_clause(|proof_hint, deps, literals| {
                println!("on_clause:\n\tproof_hint: {proof_hint:}\n\tdeps: {deps:?}\n\tliteral: {literals:?}");
                y = "check successfull".to_owned();
            });

            let gx = g.apply(&[&x]).as_bool().unwrap();
            let gxx = g.apply(&[&f.apply(&[&f.apply(&[&x])])]).as_bool().unwrap();

            s.assert(&!(&gx & &gxx));
            s.assert(&(&gx | &gxx));
            s.assert(&f.apply(&[&x]).eq(&x));
            s.check();
            println!("result: {:?}", s.check());
            println!("{:?}", s.get_model());
        }
        assert_eq!(&y, "check successfull")
    }

    #[test]
    fn user_propagator() {
        /* proves f(f(f(f(x)))) = f(x) with a up that rewrites f(f(x)) into f(x) */
        let _ = env_logger::try_init();
        let mut cfg = Config::default();
        cfg.set_model_generation(true);
        let ctx = Context::new(&cfg);
        let s_sort = Sort::uninterpreted( "S".into());
        let f = FuncDecl::new_up( "f", &[&s_sort], &s_sort);
        let x = FuncDecl::new( "x", &[], &s_sort).apply(&[]);
        let s = Solver::new();

        #[derive(Debug)]
        struct UP<'a> {
            pub f:  &'a FuncDecl,
            pub ctx:  Context,
        }

        impl<'a> UP<'a> {
            fn generate_next_term(&self, e: &Dynamic) -> Option<Dynamic> {
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

        impl<'a> UserPropagator for UP<'a> {
            fn eq(&mut self, upw: &CallBack, x: &Dynamic, y: &Dynamic) {
                println!("eq: {x} = {y}");
                for e in [x, y] {
                    let Some(nt) = self.generate_next_term(e) else {
                        continue;
                    };
                    upw.propagate_one(&[], &e._eq(&nt));
                }
            }

            fn neq(&mut self, upw: &CallBack, x: &Dynamic, y: &Dynamic) {
                println!("neq: {x} != {y}");
                for e in [x, y] {
                    let Some(nt) = self.generate_next_term(e) else {
                        continue;
                    };
                    upw.propagate_one(&[], &e._eq(&nt));
                }
            }

            fn created(&mut self, _: &CallBack, e: &ast::Dynamic) {
                println!("created: {e}")
            }

            fn pop(&mut self, _: &CallBack, num_scopes: u32) {
                println!("pop: {num_scopes:}")
            }

            fn push(&mut self, _: &CallBack) {
                println!("push")
            }

            fn decide(
                &mut self,
                _: &CallBack,
                val: &ast::Dynamic,
                bit: u32,
                is_pos: bool,
            ) {
                println!("decide: {val}, {bit:} {is_pos}")
            }

            fn fixed(
                &mut self,
                _: &CallBack,
                id: &ast::Dynamic,
                e: &ast::Dynamic,
            ) {
                println!("fixed: {id} {e}")
            }

            fn final_(&mut self, _: &CallBack) {
                println!("final")
            }

            fn get_context(&self) -> &Context {
                &self.ctx
            }
        }

        let mut s = UPSolver::new(s);
        // let up = Box::pin(UP { f: &f, ctx: &ctx });
        s.register_user_propagator(UP { f:& f, ctx: ctx.clone() });
        s.assert(
            f.apply(&[&f.apply(&[&f.apply(&[&f.apply(&[&x])])])])
                .eq(f.apply(&[&x]))
                .not(),
        );
        println!("result: {:?}", s.check());
    }
}
