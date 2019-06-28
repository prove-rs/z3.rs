use ast;
use z3_sys::*;
use Config;
use Context;
use FuncDecl;
use Sort;
use Symbol;
use Z3_MUTEX;

impl Context {
    pub fn new(cfg: &Config) -> Context {
        Context {
            z3_ctx: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let p = Z3_mk_context_rc(cfg.z3_cfg);
                debug!("new context {:p}", p);
                p
            },
        }
    }

    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    ///
    /// This method can be invoked from a thread different from the one executing the
    /// interruptible procedure.
    pub fn interrupt(&self) {
        unsafe {
            Z3_interrupt(self.z3_ctx);
        }
    }

    // Helpers for common constructions

    pub fn bool_sort(&self) -> Sort {
        Sort::bool(self)
    }

    pub fn int_sort(&self) -> Sort {
        Sort::int(self)
    }

    pub fn real_sort(&self) -> Sort {
        Sort::real(self)
    }

    pub fn bitvector_sort(&self, sz: u32) -> Sort {
        Sort::bitvector(self, sz)
    }

    pub fn array_sort<'ctx>(&'ctx self, domain: &Sort<'ctx>, range: &Sort<'ctx>) -> Sort<'ctx> {
        Sort::array(self, domain, range)
    }

    pub fn set_sort<'ctx>(&'ctx self, elt: &Sort<'ctx>) -> Sort<'ctx> {
        Sort::set(self, elt)
    }

    /// Create an enumeration sort.
    ///
    /// Creates a Z3 enumeration sort with the given `name`.
    /// The enum variants will have the names in `enum_names`.
    /// Three things are returned:
    /// - the created `Sort`,
    /// - constants to create the variants,
    /// - and testers to check if a value is equal to a variant.
    ///
    /// # Examples
    /// ```
    /// # use z3::{Config, Context, Solver, Symbol};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// let (colors, color_consts, color_testers) = ctx.enumeration_sort(
    ///     Symbol::String("Color".to_owned()),
    ///     &[
    ///         Symbol::String("Red".to_owned()),
    ///         Symbol::String("Green".to_owned()),
    ///         Symbol::String("Blue".to_owned()),
    ///     ],
    /// );
    ///
    /// let red_const = color_consts[0].apply(&[]);
    /// let red_tester = &color_testers[0];
    /// let eq = red_tester.apply(&[&red_const]);
    ///
    /// assert!(solver.check());
    /// let model = solver.get_model();
    ///
    /// assert!(model.eval(&eq).unwrap().as_bool().unwrap().as_bool().unwrap());
    /// ```
    pub fn enumeration_sort<'ctx>(
        &'ctx self,
        name: Symbol,
        enum_names: &[Symbol],
    ) -> (Sort<'ctx>, Vec<FuncDecl<'ctx>>, Vec<FuncDecl<'ctx>>) {
        Sort::enumeration(self, name, enum_names)
    }

    pub fn named_bool_const(&self, s: &str) -> ast::Bool {
        ast::Bool::new_const(self, Symbol::String(s.to_owned()))
    }

    pub fn numbered_bool_const(&self, i: u32) -> ast::Bool {
        ast::Bool::new_const(self, Symbol::Int(i))
    }

    pub fn fresh_bool_const<'ctx>(&'ctx self, prefix: &str) -> ast::Bool<'ctx> {
        ast::Bool::fresh_const(self, prefix)
    }

    pub fn named_int_const(&self, s: &str) -> ast::Int {
        ast::Int::new_const(self, Symbol::String(s.to_owned()))
    }

    pub fn numbered_int_const(&self, i: u32) -> ast::Int {
        ast::Int::new_const(self, Symbol::Int(i))
    }

    pub fn fresh_int_const<'ctx>(&'ctx self, prefix: &str) -> ast::Int<'ctx> {
        ast::Int::fresh_const(self, prefix)
    }

    pub fn named_real_const(&self, s: &str) -> ast::Real {
        ast::Real::new_const(self, Symbol::String(s.to_owned()))
    }

    pub fn numbered_real_const(&self, i: u32) -> ast::Real {
        ast::Real::new_const(self, Symbol::Int(i))
    }

    pub fn fresh_real_const<'ctx>(&'ctx self, prefix: &str) -> ast::Real<'ctx> {
        ast::Real::fresh_const(self, prefix)
    }

    pub fn named_bitvector_const(&self, s: &str, sz: u32) -> ast::BV {
        ast::BV::new_const(self, Symbol::String(s.to_owned()), sz)
    }

    pub fn numbered_bitvector_const(&self, i: u32, sz: u32) -> ast::BV {
        ast::BV::new_const(self, Symbol::Int(i), sz)
    }

    pub fn fresh_bitvector_const<'ctx>(&'ctx self, prefix: &str, sz: u32) -> ast::BV<'ctx> {
        ast::BV::fresh_const(self, prefix, sz)
    }

    #[allow(clippy::wrong_self_convention)]
    pub fn from_bool(&self, b: bool) -> ast::Bool {
        ast::Bool::from_bool(self, b)
    }

    #[deprecated(
        note = "Context::from_u64 is ambiguous; prefer ast::Int::from_u64() or ast::BV::from_u64()"
    )]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_u64(&self, u: u64) -> ast::Int {
        ast::Int::from_u64(self, u)
    }
    #[deprecated(
        note = "Context::from_i64 is ambiguous; prefer ast::Int::from_i64() or ast::BV::from_i64()"
    )]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_i64(&self, i: i64) -> ast::Int {
        ast::Int::from_i64(self, i)
    }

    #[allow(clippy::wrong_self_convention)]
    pub fn from_real(&self, num: i32, den: i32) -> ast::Real {
        ast::Real::from_real(self, num, den)
    }

    pub fn func_decl<'ctx>(
        &'ctx self,
        name: Symbol,
        domain: &[&Sort<'ctx>],
        range: &Sort<'ctx>,
    ) -> FuncDecl<'ctx> {
        FuncDecl::new(self, name, domain, range)
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
    /// let forall: ast::Dynamic = ctx.forall_const(&[&x.clone().into()], &(x._eq(&f_x)).into());
    /// solver.assert(&forall.try_into().unwrap());
    ///
    /// assert!(solver.check());
    /// let model = solver.get_model();
    ///
    /// let f_f_3: ast::Int = f.apply(&[&f.apply(&[&ctx.from_u64(3).into()])]).try_into().unwrap();
    /// assert_eq!(3, model.eval(&f_f_3).unwrap().as_u64().unwrap());
    /// ```
    pub fn forall_const<'ctx>(
        &'ctx self,
        bounds: &[&ast::Dynamic<'ctx>],
        body: &ast::Dynamic<'ctx>,
    ) -> ast::Dynamic<'ctx> {
        ast::forall_const(self, bounds, body)
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { Z3_del_context(self.z3_ctx) };
    }
}
