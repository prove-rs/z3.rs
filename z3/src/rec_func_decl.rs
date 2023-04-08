use ast;
use ast::Ast;
use std::convert::TryInto;
use std::ffi::CStr;
use std::fmt;
use z3_sys::*;
use {Context, RecFuncDecl, Sort, Symbol};

impl<'ctx> RecFuncDecl<'ctx> {
    pub(crate) unsafe fn wrap(ctx: &'ctx Context, z3_func_decl: Z3_func_decl) -> Self {
        Z3_inc_ref(ctx.z3_ctx, Z3_func_decl_to_ast(ctx.z3_ctx, z3_func_decl));
        Self { ctx, z3_func_decl }
    }

    pub fn new<S: Into<Symbol>>(
        ctx: &'ctx Context,
        name: S,
        domain: &[&Sort<'ctx>],
        range: &Sort<'ctx>,
    ) -> Self {
        assert!(domain.iter().all(|s| s.ctx.z3_ctx == ctx.z3_ctx));
        assert_eq!(ctx.z3_ctx, range.ctx.z3_ctx);

        let domain: Vec<_> = domain.iter().map(|s| s.z3_sort).collect();

        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_rec_func_decl(
                    ctx.z3_ctx,
                    name.into().as_z3_symbol(ctx),
                    domain.len().try_into().unwrap(),
                    domain.as_ptr(),
                    range.z3_sort,
                ),
            )
        }
    }

    /// Adds the body to a recursive function.
    ///
    /// ```
    /// # use z3::{Config, Context, RecFuncDecl, Solver, Sort, Symbol, ast::Int, SatResult};
    /// # use std::convert::TryInto;
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let mut f = RecFuncDecl::new(
    ///     &ctx,
    ///     "f",
    ///     &[&Sort::int(&ctx)],
    ///     &Sort::int(&ctx));
    /// let n = Int::new_const(&ctx, "n");
    /// f.add_def(
    ///     &[&n.clone().into()],
    ///     &Int::add(&ctx, &[&n, &Int::from_i64(&ctx, 1)])
    /// );
    ///
    /// let f_of_n = &f.apply(&[&n.clone()]);
    ///
    /// let solver = Solver::new(&ctx);
    /// let forall: z3::ast::Bool = z3::ast::forall_const(
    ///         &ctx,
    ///         &[&n],
    ///         &[],
    ///         &n.lt(&f_of_n.as_int().unwrap())
    ///     ).try_into().unwrap();
    ///
    /// solver.assert(&forall);
    /// let res = solver.check();
    /// assert_eq!(res, SatResult::Sat);
    /// ```
    ///
    /// Note that `args` should have the types corresponding to the `domain` of the `RecFuncDecl`.
    pub fn add_def(&self, args: &[&ast::Dynamic<'ctx>], body: &impl Ast<'ctx>) {
        assert!(args.iter().all(|arg| arg.ctx == body.get_ctx()));
        assert_eq!(self.ctx, body.get_ctx());

        let mut args: Vec<_> = args.iter().map(|s| s.get_z3_ast()).collect();
        unsafe {
            assert_eq!(
                body.get_sort().z3_sort,
                Z3_get_range(self.ctx.z3_ctx, self.z3_func_decl)
            );

            Z3_add_rec_def(
                self.ctx.z3_ctx,
                self.z3_func_decl,
                self.arity() as u32,
                args.as_mut_ptr(),
                body.get_z3_ast(),
            );
        }
    }

    /// Return the number of arguments of a function declaration.
    ///
    /// If the function declaration is a constant, then the arity is `0`.
    ///
    /// ```
    /// # use z3::{Config, Context, RecFuncDecl, Solver, Sort, Symbol};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let f = RecFuncDecl::new(
    ///     &ctx,
    ///     "f",
    ///     &[&Sort::int(&ctx), &Sort::real(&ctx)],
    ///     &Sort::int(&ctx));
    /// assert_eq!(f.arity(), 2);
    /// ```
    pub fn arity(&self) -> usize {
        unsafe { Z3_get_arity(self.ctx.z3_ctx, self.z3_func_decl) as usize }
    }

    /// Create a constant (if `args` has length 0) or function application (otherwise).
    ///
    /// Note that `args` should have the types corresponding to the `domain` of the `RecFuncDecl`.
    pub fn apply(&self, args: &[&dyn ast::Ast<'ctx>]) -> ast::Dynamic<'ctx> {
        assert!(args.iter().all(|s| s.get_ctx().z3_ctx == self.ctx.z3_ctx));

        let args: Vec<_> = args.iter().map(|a| a.get_z3_ast()).collect();

        unsafe {
            ast::Dynamic::wrap(self.ctx, {
                Z3_mk_app(
                    self.ctx.z3_ctx,
                    self.z3_func_decl,
                    args.len().try_into().unwrap(),
                    args.as_ptr(),
                )
            })
        }
    }

    /// Return the `DeclKind` of this `RecFuncDecl`.
    pub fn kind(&self) -> DeclKind {
        unsafe { Z3_get_decl_kind(self.ctx.z3_ctx, self.z3_func_decl) }
    }

    /// Return the name of this `RecFuncDecl`.
    ///
    /// Strings will return the `Symbol`.  Ints will have a `"k!"` prepended to
    /// the `Symbol`.
    pub fn name(&self) -> String {
        unsafe {
            let z3_ctx = self.ctx.z3_ctx;
            let symbol = Z3_get_decl_name(z3_ctx, self.z3_func_decl);
            match Z3_get_symbol_kind(z3_ctx, symbol) {
                SymbolKind::String => CStr::from_ptr(Z3_get_symbol_string(z3_ctx, symbol))
                    .to_string_lossy()
                    .into_owned(),
                SymbolKind::Int => format!("k!{}", Z3_get_symbol_int(z3_ctx, symbol)),
            }
        }
    }
}

impl<'ctx> fmt::Display for RecFuncDecl<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_func_decl_to_string(self.ctx.z3_ctx, self.z3_func_decl) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for RecFuncDecl<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for RecFuncDecl<'ctx> {
    fn drop(&mut self) {
        unsafe {
            Z3_dec_ref(
                self.ctx.z3_ctx,
                Z3_func_decl_to_ast(self.ctx.z3_ctx, self.z3_func_decl),
            );
        }
    }
}
