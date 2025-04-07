//! Z3's [User Propagator](https://microsoft.github.io/z3guide/programming/Example%20Programs/User%20Propagator/) API

// I am following quite closly this: https://z3prover.github.io/api/html/classz3_1_1user__propagator__base.html

use std::{convert::TryInto, fmt::Debug, pin::Pin, ptr::NonNull, rc::Rc, usize};

use crate::{
    ast::{self, Ast, Dynamic},
    Context, FuncDecl, Solver, Sort, Symbol,
};
use log::debug;
use z3_sys::*;

#[allow(unused_variables)] // default implementation is a no-op, but variable names are usefull for documentation
pub trait UserPropagator<'ctx>: Debug {
    fn push(&self, upw: &UPHandle<'ctx>) {}
    fn pop(&self, upw: &UPHandle<'ctx>, num_scopes: u32) {}
    fn fixed(&self, upw: &UPHandle<'ctx>, id: &Dynamic<'ctx>, e: &Dynamic<'ctx>) {}
    fn eq(&self, upw: &UPHandle<'ctx>, x: &Dynamic<'ctx>, y: &Dynamic<'ctx>) {}
    fn neq(&self, upw: &UPHandle<'ctx>, x: &Dynamic<'ctx>, y: &Dynamic<'ctx>) {}

    /// During the final check stage, all propagations have been processed. This
    /// is an opportunity for the user-propagator to delay some analysis that
    /// could be expensive to perform incrementally. It is also an opportunity
    /// for the propagator to implement branch and bound optimization.
    fn final_(&self, upw: &UPHandle<'ctx>) {}
    fn created(&self, upw: &UPHandle<'ctx>, e: &Dynamic<'ctx>) {}
    fn decide(&self, upw: &UPHandle<'ctx>, val: &Dynamic<'ctx>, bit: u32, is_pos: bool) {}

    // /// `self` is responsible for garbage collecting the sub-solver
    // fn fresh<'a>(
    //     upw: &'a UserPropagatorWrapper<'ctx>,
    //     ctx: &'a Context,
    // ) -> Option<&'a dyn UserPropagator<'a>> {
    //     None
    // }
}

#[derive(Debug)]
struct CallBackTracker {
    /// can be null
    cb: Z3_solver_callback,
    depth: usize,
}

impl Default for CallBackTracker {
    fn default() -> Self {
        Self {
            cb: ::std::ptr::null_mut(),
            depth: 0,
        }
    }
}

impl CallBackTracker {
    pub fn incr(&mut self, cb: Z3_solver_callback) {
        self.cb = cb;
        self.depth += 1;
    }

    pub fn decr(&mut self) {
        self.depth -= 1;
    }

    pub fn is_null(&self) -> bool {
        self.cb.is_null()
    }
}

#[derive(Debug)]
pub struct UPSolver<'ctx> {
    solver: Solver<'ctx>,
    handles: Vec<Pin<Box<UPHandle<'ctx>>>>,
}

impl<'ctx> std::ops::Deref for UPSolver<'ctx> {
    type Target = Solver<'ctx>;

    fn deref(&self) -> &Self::Target {
        &self.solver
    }
}

impl<'ctx> UPSolver<'ctx> {
    pub fn new(solver: Solver<'ctx>) -> Self {
        Self {
            solver,
            handles: vec![],
        }
    }

    pub fn solver(&self) -> &Solver<'ctx> {
        &self.solver
    }

    pub fn add(&self, expr: &impl Ast<'ctx>) {
        let z3_ctx = self.solver().get_context().z3_ctx;
        let z3_slv = self.solver().z3_slv;
        unsafe { Z3_solver_propagate_register(z3_ctx, z3_slv, expr.get_z3_ast()) }
    }

    pub fn register_up<U: UserPropagator<'ctx> + 'ctx>(&mut self, up: U) -> usize {
        let up_handle = UPHandle::new(up, self.solver());
        let i = self.handles.len();
        self.handles.push(up_handle);
        return i;
    }

    pub fn len(&self) -> usize {
        self.handles.len()
    }

    pub fn get(&self, i: usize) -> &dyn UserPropagator<'ctx> {
        self.handles[i].inner()
    }
}

impl<'ctx> UPSolver<'ctx> {}

#[derive(Debug)]
pub struct UPHandle<'s> {
    inner: Box<dyn UserPropagator<'s> + 's>,
    ctx: &'s Context,
    cb: CallBackTracker,
}

impl<'s> UPHandle<'s> {
    fn new(up: impl UserPropagator<'s> + 's, solver: &Solver<'s>) -> Pin<Box<Self>> {
        let upw = Box::pin(Self {
            inner: Box::new(up),
            ctx: solver.get_context(),
            // subcontexts: vec![],
            cb: Default::default(),
        });
        upw.init_z3(solver);
        upw
    }

    fn init_z3(&self, solver: &Solver<'s>) {
        let z3_slv = solver.z3_slv;
        unsafe {
            debug!("Z3_solver_propagate_init");
            Z3_solver_propagate_init(
                self.context().get_z3_context(),
                z3_slv,
                self.get_user_context(),
                Some(Self::push_eh),
                Some(Self::pop_eh),
                Some(Self::fresh_eh),
            );
        }
        // we register all callbacks. They do nothing by default
        unsafe {
            // fixed
            debug!("Z3_solver_propagate_fixed");
            Z3_solver_propagate_fixed(self.z3_ctx(), z3_slv, Some(Self::fixed_eh));
        }
        unsafe {
            // eq
            debug!("Z3_solver_propagate_eq");
            Z3_solver_propagate_eq(self.z3_ctx(), z3_slv, Some(Self::eq_eh));
        }
        unsafe {
            // eq
            debug!("Z3_solver_propagate_diseq");
            Z3_solver_propagate_diseq(self.z3_ctx(), z3_slv, Some(Self::neq_eh));
        }
        unsafe {
            // final
            debug!("Z3_solver_propagate_final");
            Z3_solver_propagate_final(self.z3_ctx(), z3_slv, Some(Self::final_eh));
        }
        unsafe {
            // created
            debug!("Z3_solver_propagate_created");
            Z3_solver_propagate_created(self.z3_ctx(), z3_slv, Some(Self::created_eh));
        }
        unsafe {
            // decide
            debug!("Z3_solver_propagate_decide");
            Z3_solver_propagate_decide(self.z3_ctx(), z3_slv, Some(Self::decide_eh));
        }
    }

    // callbacks

    extern "C" fn push_eh(ctx: *mut ::std::ffi::c_void, cb: Z3_solver_callback) {
        debug!("push_eh");
        unsafe { Self::mut_from_user_context(ctx) }.scoped_do(cb, |s| {
            s.inner();
        });
    }

    extern "C" fn pop_eh(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        num_scopes: ::std::ffi::c_uint,
    ) {
        debug!("pop_eh");
        unsafe { Self::mut_from_user_context(ctx) }.scoped_do(cb, |s| {
            s.inner().pop(s, num_scopes);
        });
    }

    #[allow(unused_variables)]
    extern "C" fn fresh_eh(
        ctx: *mut ::std::ffi::c_void,
        new_context: Z3_context,
    ) -> *mut ::std::ffi::c_void {
        // debug!("fresh_eh");
        // let mself = unsafe { Self::mut_from_user_context(ctx) }; // `ctx` should be a pointer to us
        // Vec::push(
        //     &mut mself.subcontexts,
        //     Context {
        //         z3_ctx: new_context,
        //     },
        // );
        // let sub_ctx = mself.subcontexts.last().unwrap();
        // let sub_up = U::fresh(mself, sub_ctx)
        //     .map(|up| up.get_user_context())
        //     .unwrap_or(::std::ptr::null_mut());
        // sub_up
        ::std::ptr::null_mut()
    }

    extern "C" fn fixed_eh(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        var: Z3_ast,
        value: Z3_ast,
    ) {
        debug!("fixed_eh");
        unsafe { Self::mut_from_user_context(ctx) }.scoped_do(cb, |upw| {
            upw.inner()
                .fixed(upw, &upw.mk_dynamic(var), &upw.mk_dynamic(value));
        })
    }

    extern "C" fn eq_eh(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        x: Z3_ast,
        y: Z3_ast,
    ) {
        debug!("eq_eh");
        unsafe { Self::mut_from_user_context(ctx) }.scoped_do(cb, |upw| {
            upw.inner().eq(upw, &upw.mk_dynamic(x), &upw.mk_dynamic(y));
        })
    }

    extern "C" fn neq_eh(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        x: Z3_ast,
        y: Z3_ast,
    ) {
        debug!("neq_eh");
        unsafe { Self::mut_from_user_context(ctx) }.scoped_do(cb, |upw| {
            upw.inner().neq(upw, &upw.mk_dynamic(x), &upw.mk_dynamic(y));
        })
    }

    extern "C" fn final_eh(ctx: *mut ::std::ffi::c_void, cb: Z3_solver_callback) {
        debug!("final_eh");
        unsafe { Self::mut_from_user_context(ctx) }.scoped_do(cb, |upw| {
            upw.inner().final_(upw);
        })
    }

    extern "C" fn created_eh(ctx: *mut ::std::ffi::c_void, cb: Z3_solver_callback, e: Z3_ast) {
        debug!("created_eh");
        unsafe { Self::mut_from_user_context(ctx) }.scoped_do(cb, |upw| {
            upw.inner().created(upw, &upw.mk_dynamic(e));
        });
        debug!("exit created")
    }

    extern "C" fn decide_eh(
        ctx: *mut ::std::ffi::c_void,
        cb: Z3_solver_callback,
        val: Z3_ast,
        bit: ::std::ffi::c_uint,
        is_pos: bool,
    ) {
        debug!("decide_eh");
        unsafe { Self::mut_from_user_context(ctx) }.scoped_do(cb, |upw| {
            upw.inner().decide(upw, &upw.mk_dynamic(val), bit, is_pos);
        })
    }
    // private usefull stuff

    fn z3_ctx(&self) -> Z3_context {
        self.context().z3_ctx
    }

    fn scoped_do<F, V>(&mut self, cb: Z3_solver_callback, f: F) -> V
    where
        F: for<'a> FnOnce(&'a mut Self) -> V,
    {
        self.cb.incr(cb);
        let ret = f(self);
        self.cb.decr();
        ret
    }

    fn mk_dynamic(&self, z3_ast: Z3_ast) -> Dynamic<'s> {
        unsafe { Dynamic::wrap(self.context(), z3_ast) }
    }

    fn get_user_context(&self) -> *mut ::std::ffi::c_void {
        self as *const _ as *mut ::std::ffi::c_void
    }

    unsafe fn dump_self(ptr: *mut Self) {
        dbg!(ptr);
        let l = std::alloc::Layout::new::<Self>();
        let l = std::alloc::Layout::array::<u8>(l.size()).unwrap();
        let ptr = NonNull::new(ptr).unwrap();
        let ptr = ptr.cast::<u8>();
        let ptr = NonNull::slice_from_raw_parts(ptr, l.size());
        for b in ptr.as_ref() {
            print!("{b:2x}")
        }
        println!("  done")
    }

    unsafe fn mut_from_user_context<'a>(ptr: *mut ::std::ffi::c_void) -> &'a mut Self {
        (ptr as *mut Self).as_mut().unwrap()
    }

    /// returns [None] iff `self.cb.cb` is `null`
    fn get_cb(&self) -> Option<Z3_solver_callback> {
        if self.cb.is_null() {
            None
        } else {
            Some(self.cb.cb)
        }
    }

    // public API

    pub fn context(&self) -> &'s Context {
        &self.ctx
    }

    fn inner(&self) -> &dyn UserPropagator<'s> {
        self.inner.as_ref()
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
    /// see [Z3_solver_next_split]
    pub fn next_split(&self, expr: &ast::Bool<'s>, idx: u32, phase: Option<bool>) -> bool {
        let cb = self.get_cb().expect("you're not in a callback!");
        let phase = match phase {
            Some(true) => Z3_L_TRUE,
            Some(false) => Z3_L_FALSE,
            None => Z3_L_UNDEF,
        };
        unsafe { Z3_solver_next_split(self.z3_ctx(), cb, expr.get_z3_ast(), idx, phase) }
    }

    /// Tracks `expr` with ([UserPropagator::fixed()] or [UserPropagator::eq()])
    ///
    /// If `expr` is a Boolean or Bit-vector, the [UserPropagator::fixed()]
    /// callback gets invoked when `expr` is bound to a value.a Equalities
    /// between registered expressions  are reported thought
    /// [UserPropagator::eq()]. A consumer can use the [Self::propagate] or
    /// [Self::conflict] functions to invoke propagations or conflicts as a
    /// consequence of these callbacks. These functions take a list of
    /// identifiers for registered expressions that have been fixed. The list of
    /// identifiers must correspond to already fixed values. Similarly, a list
    /// of propagated equalities can be supplied. These must correspond to
    /// equalities that have been registered during a callback.
    ///
    /// see [Z3_solver_propagate_register_cb] and [Z3_solver_propagate_register]
    pub fn add(&self, expr: &impl Ast<'s>) {
        let cb = self
            .get_cb()
            .expect("you're not in a callback! Maybe you mean `UPSolver::add`");
        unsafe { Z3_solver_propagate_register_cb(self.z3_ctx(), cb, expr.get_z3_ast()) };

        // if let Some(cb) = self.get_cb() {
        //     unsafe {
        //         Z3_solver_propagate_register_cb(self.z3_ctx(), cb, expr.get_z3_ast());
        //     }
        // } else {
        //     unsafe { Z3_solver_propagate_register(self.z3_ctx(), self.z3_slv(), expr.get_z3_ast()) }
        // }
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
    /// see [Z3_solver_propagate_consequence]
    pub fn propagate<'a, I, J, A>(
        &'a self,
        fixed: I,
        lhs: J,
        rhs: J,
        conseq: &'a ast::Bool<'s>,
    ) -> bool
    where
        I: IntoIterator<Item = &'a ast::Bool<'s>>,
        J: IntoIterator<Item = &'a A>,
        A: Ast<'s> + 'a,
    {
        /* using generics because I need to map on the arguments anyway and it will turn
        the other functions defined from `propagate` into the same things as the C++
        API this is based on */
        let cb = self.get_cb().expect("you're not in a callback!");
        let fixed: Vec<_> = fixed.into_iter().map(|e| e.get_z3_ast()).collect();
        let lhs: Vec<_> = lhs.into_iter().map(|e| e.get_z3_ast()).collect();
        let rhs: Vec<_> = rhs.into_iter().map(|e| e.get_z3_ast()).collect();
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
                cb,
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
    pub fn conflict_on(&self, fixed: &[&ast::Bool<'s>]) -> bool {
        self.propagate::<_, _, ast::Bool<'s>>(
            fixed.iter().copied(),
            [],
            [],
            &ast::Bool::from_bool(self.context(), false),
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
        fixed: &[&ast::Bool<'s>],
        lhs: &[&ast::Dynamic<'s>],
        rhs: &[&ast::Dynamic<'s>],
    ) -> bool {
        self.propagate(
            fixed.iter().copied(),
            lhs.iter().copied(),
            rhs.iter().copied(),
            &ast::Bool::from_bool(self.context(), false),
        )
    }

    /// Propagate `conseq`
    ///
    /// Equivalent to [`self.propagate(fixed, [], [], conseq)`](Self::propagate)
    ///
    /// panics if not called from a callback.
    pub fn propagate_one(&self, fixed: &[&ast::Bool<'s>], conseq: &ast::Bool<'s>) -> bool {
        self.propagate::<_, _, ast::Bool>(fixed.iter().copied(), [], [], conseq)
    }
}

/// Declare a function to be propagated to all the [UserPropagator]s
pub fn declare_up_function<'s, S: Into<Symbol>>(
    ctx: &'s Context,
    name: S,
    domain: &[&Sort<'s>],
    range: &Sort<'s>,
) -> FuncDecl<'s> {
    assert!(domain.iter().all(|s| s.ctx.z3_ctx == ctx.z3_ctx));
    assert_eq!(ctx.z3_ctx, range.ctx.z3_ctx);

    let domain: Vec<_> = domain.iter().map(|s| s.z3_sort).collect();

    unsafe {
        FuncDecl::wrap(
            ctx,
            Z3_solver_propagate_declare(
                ctx.z3_ctx,
                name.into().as_z3_symbol(ctx),
                domain.len().try_into().unwrap(),
                domain.as_ptr(),
                range.z3_sort,
            ),
        )
    }
}

#[cfg(test)]
mod test {
    use std::convert::TryInto;

    use log::debug;

    use crate::{
        ast::{self, Ast, Bool, Dynamic},
        user_propagator::{declare_up_function, UPHandle, UPSolver, UserPropagator},
        Config, Context, FuncDecl, SatResult, Solver, Sort,
    };

    #[test]
    fn test_up() {
        let _ = env_logger::try_init();
        let mut cfg = Config::default();
        cfg.set_model_generation(true);
        let ctx = Context::new(&cfg);
        let s_sort = Sort::uninterpreted(&ctx, "S".into());
        let f = declare_up_function(&ctx, "f", &[&s_sort], &s_sort);
        let x = FuncDecl::new(&ctx, "x", &[], &s_sort).apply(&[]);
        let s = Solver::new(&ctx);

        #[derive(Debug)]
        struct UP<'ctx> {
            pub f: &'ctx FuncDecl<'ctx>,
        }

        impl<'ctx> UP<'ctx> {
            fn gen_nt(&self, e: &Dynamic<'ctx>) -> Option<Dynamic<'ctx>> {
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
            fn eq(&self, upw: &UPHandle<'ctx>, x: &Dynamic<'ctx>, y: &Dynamic<'ctx>) {
                println!("eq: {x} = {y}");
                for e in [x, y] {
                    let Some(nt) = self.gen_nt(e) else {
                        continue;
                    };
                    upw.propagate_one(&[], &e._eq(&nt));
                }
            }

            fn neq(&self, upw: &UPHandle<'ctx>, x: &Dynamic<'ctx>, y: &Dynamic<'ctx>) {
                println!("neq: {x} != {y}");
                for e in [x, y] {
                    let Some(nt) = self.gen_nt(e) else {
                        continue;
                    };
                    upw.propagate_one(&[], &e._eq(&nt));
                }
            }

            fn created(&self, _: &UPHandle<'ctx>, e: &ast::Dynamic<'ctx>) {
                println!("created: {e}")
            }

            fn pop(&self, _: &UPHandle<'ctx>, num_scopes: u32) {
                println!("pop: {num_scopes:}")
            }

            fn push(&self, _: &UPHandle<'ctx>) {
                println!("push")
            }

            fn decide(&self, _: &UPHandle<'ctx>, val: &ast::Dynamic<'ctx>, bit: u32, is_pos: bool) {
                println!("decide: {val}, {bit:} {is_pos}")
            }

            fn fixed(&self, _: &UPHandle<'ctx>, id: &ast::Dynamic<'ctx>, e: &ast::Dynamic<'ctx>) {
                println!("fixed: {id} {e}")
            }

            fn final_(&self, _: &UPHandle<'ctx>) {
                println!("final")
            }
        }

        // let u = UPHandle::new(UP { f: &f }, s);
        // let s = u.solver();
        let mut s = UPSolver::new(s);
        s.register_up(UP { f: &f });
        s.assert(
            &f.apply(&[&f.apply(&[&f.apply(&[&f.apply(&[&x])])])])
                ._eq(&f.apply(&[&x]))
                .not(),
        );
        assert_eq!(s.check(), SatResult::Unsat);
    }
}
