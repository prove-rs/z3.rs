use std::convert::TryInto;
use std::ffi::CStr;
use std::fmt;

use z3_sys::*;

use crate::{Context, FuncDecl, Sort, Symbol, ast, ast::Ast};

impl FuncDecl {
    pub(crate) unsafe fn wrap(ctx: &Context, z3_func_decl: Z3_func_decl) -> Self {
        unsafe {
            Z3_inc_ref(ctx.z3_ctx.0, Z3_func_decl_to_ast(ctx.z3_ctx.0, z3_func_decl));
        }
        Self { ctx: ctx.clone(), z3_func_decl }
    }

    pub fn new<S: Into<Symbol>>(
        ctx: &Context,
        name: S,
        domain: &[&Sort],
        range: &Sort,
    ) -> Self {
        assert!(domain.iter().all(|s| s.ctx.z3_ctx == ctx.z3_ctx));
        assert_eq!(ctx.z3_ctx, range.ctx.z3_ctx);

        let domain: Vec<_> = domain.iter().map(|s| s.z3_sort).collect();
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_func_decl(
                    ctx.z3_ctx.0,
                    name.into().as_z3_symbol(ctx),
                    domain.len().try_into().unwrap(),
                    domain.as_ptr(),
                    range.z3_sort,
                ),
            )
        }
    }

    /// Return the number of arguments of a function declaration.
    ///
    /// If the function declaration is a constant, then the arity is `0`.
    ///
    /// ```
    /// # use z3::{Config, Context, FuncDecl, Solver, Sort, Symbol};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let f = FuncDecl::new(
    ///     &ctx,
    ///     "f",
    ///     &[&Sort::int(&ctx), &Sort::real(&ctx)],
    ///     &Sort::int(&ctx));
    /// assert_eq!(f.arity(), 2);
    /// ```
    pub fn arity(&self) -> usize {
        unsafe { Z3_get_arity(self.ctx.z3_ctx.0, self.z3_func_decl) as usize }
    }

    /// Create a constant (if `args` has length 0) or function application (otherwise).
    ///
    /// Note that `args` should have the types corresponding to the `domain` of the `FuncDecl`.
    pub fn apply(&self, args: &[&dyn ast::Ast]) -> ast::Dynamic {
        assert!(args.iter().all(|s| s.get_ctx().z3_ctx == self.ctx.z3_ctx));

        let args: Vec<_> = args.iter().map(|a| a.get_z3_ast()).collect();

        unsafe {
            ast::Dynamic::wrap(&self.ctx, {
                Z3_mk_app(
                    self.ctx.z3_ctx.0,
                    self.z3_func_decl,
                    args.len().try_into().unwrap(),
                    args.as_ptr(),
                )
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

impl fmt::Display for FuncDecl {
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

impl fmt::Debug for FuncDecl {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl Drop for FuncDecl {
    fn drop(&mut self) {
        unsafe {
            Z3_dec_ref(
                self.ctx.z3_ctx.0,
                Z3_func_decl_to_ast(self.ctx.z3_ctx.0, self.z3_func_decl),
            );
        }
    }
}
