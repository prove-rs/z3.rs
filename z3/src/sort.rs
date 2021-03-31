use std::convert::TryInto;
use std::ffi::CStr;
use std::fmt;
use z3_sys::*;
use Context;
use FuncDecl;
use Sort;
use SortDiffers;
use Symbol;
use Z3_MUTEX;

impl<'ctx> Sort<'ctx> {
    pub(crate) fn new(ctx: &'ctx Context, z3_sort: Z3_sort) -> Sort<'ctx> {
        let guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort)) };
        Sort { ctx, z3_sort }
    }

    pub fn uninterpreted(ctx: &'ctx Context, name: Symbol) -> Sort<'ctx> {
        Sort::new(ctx, unsafe {
            Z3_mk_uninterpreted_sort(ctx.z3_ctx, name.as_z3_symbol(ctx))
        })
    }

    pub fn bool(ctx: &Context) -> Sort {
        Sort::new(ctx, unsafe { Z3_mk_bool_sort(ctx.z3_ctx) })
    }

    pub fn int(ctx: &Context) -> Sort {
        Sort::new(ctx, unsafe { Z3_mk_int_sort(ctx.z3_ctx) })
    }

    pub fn real(ctx: &Context) -> Sort {
        Sort::new(ctx, unsafe { Z3_mk_real_sort(ctx.z3_ctx) })
    }

    pub fn float(ctx: &Context, ebits: u32, sbits: u32) -> Sort {
        Sort::new(ctx, unsafe { Z3_mk_fpa_sort(ctx.z3_ctx, ebits, sbits) })
    }

    pub fn float32(ctx: &Context) -> Sort {
        Sort::new(ctx, unsafe { Z3_mk_fpa_sort(ctx.z3_ctx, 8, 24) })
    }

    pub fn double(ctx: &Context) -> Sort {
        Sort::new(ctx, unsafe { Z3_mk_fpa_sort(ctx.z3_ctx, 11, 53) })
    }

    pub fn string(ctx: &'ctx Context) -> Sort<'ctx> {
        Sort::new(ctx, unsafe { Z3_mk_string_sort(ctx.z3_ctx) })
    }

    pub fn bitvector(ctx: &Context, sz: u32) -> Sort {
        Sort::new(ctx, unsafe {
            Z3_mk_bv_sort(ctx.z3_ctx, sz as ::std::os::raw::c_uint)
        })
    }

    pub fn array(ctx: &'ctx Context, domain: &Sort<'ctx>, range: &Sort<'ctx>) -> Sort<'ctx> {
        Sort::new(ctx, unsafe {
            Z3_mk_array_sort(ctx.z3_ctx, domain.z3_sort, range.z3_sort)
        })
    }

    pub fn set(ctx: &'ctx Context, elt: &Sort<'ctx>) -> Sort<'ctx> {
        Sort::new(ctx, unsafe { Z3_mk_set_sort(ctx.z3_ctx, elt.z3_sort) })
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
    /// # use z3::{Config, Context, SatResult, Solver, Sort, Symbol};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// let (colors, color_consts, color_testers) = Sort::enumeration(
    ///     &ctx,
    ///     "Color".into(),
    ///     &[
    ///         "Red".into(),
    ///         "Green".into(),
    ///         "Blue".into(),
    ///     ],
    /// );
    ///
    /// let red_const = color_consts[0].apply(&[]);
    /// let red_tester = &color_testers[0];
    /// let eq = red_tester.apply(&[&red_const]);
    ///
    /// assert_eq!(solver.check(), SatResult::Sat);
    /// let model = solver.get_model().unwrap();;
    ///
    /// assert!(model.eval(&eq).unwrap().as_bool().unwrap().as_bool().unwrap());
    /// ```
    pub fn enumeration(
        ctx: &'ctx Context,
        name: Symbol,
        enum_names: &[Symbol],
    ) -> (Sort<'ctx>, Vec<FuncDecl<'ctx>>, Vec<FuncDecl<'ctx>>) {
        let enum_names: Vec<_> = enum_names.iter().map(|s| s.as_z3_symbol(ctx)).collect();
        let mut enum_consts = vec![std::ptr::null_mut(); enum_names.len()];
        let mut enum_testers = vec![std::ptr::null_mut(); enum_names.len()];

        let sort = Sort::new(ctx, unsafe {
            Z3_mk_enumeration_sort(
                ctx.z3_ctx,
                name.as_z3_symbol(ctx),
                enum_names.len().try_into().unwrap(),
                enum_names.as_ptr(),
                enum_consts.as_mut_ptr(),
                enum_testers.as_mut_ptr(),
            )
        });

        // increase ref counts
        for i in &enum_consts {
            unsafe {
                Z3_inc_ref(ctx.z3_ctx, *i as Z3_ast);
            }
        }
        for i in &enum_testers {
            unsafe {
                Z3_inc_ref(ctx.z3_ctx, *i as Z3_ast);
            }
        }

        // convert to Rust types
        let enum_consts: Vec<_> = enum_consts
            .iter()
            .map(|z3_func_decl| FuncDecl {
                ctx,
                z3_func_decl: *z3_func_decl,
            })
            .collect();
        let enum_testers: Vec<_> = enum_testers
            .iter()
            .map(|z3_func_decl| FuncDecl {
                ctx,
                z3_func_decl: *z3_func_decl,
            })
            .collect();

        (sort, enum_consts, enum_testers)
    }

    pub fn kind(&self) -> SortKind {
        unsafe { Z3_get_sort_kind(self.ctx.z3_ctx, self.z3_sort) }
    }

    /// Returns `Some(e)` where `e` is the number of exponent bits if the sort
    /// is a `FloatingPoint` and `None` otherwise.
    pub fn float_exponent_size(&self) -> Option<u32> {
        if self.kind() == SortKind::FloatingPoint {
            Some(unsafe { Z3_fpa_get_ebits(self.ctx.z3_ctx, self.z3_sort) })
        } else {
            None
        }
    }

    /// Returns `Some(s)` where `s` is the number of significand bits if the sort
    /// is a `FloatingPoint` and `None` otherwise.
    pub fn float_significand_size(&self) -> Option<u32> {
        if self.kind() == SortKind::FloatingPoint {
            Some(unsafe { Z3_fpa_get_sbits(self.ctx.z3_ctx, self.z3_sort) })
        } else {
            None
        }
    }

    /// Return if this Sort is for an `Array` or a `Set`.
    ///
    /// # Examples
    /// ```
    /// # use z3::{Config, Context, Sort, ast::Ast, ast::Int, ast::Bool};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let bool_sort = Sort::bool(&ctx);
    /// let int_sort = Sort::int(&ctx);
    /// let array_sort = Sort::array(&ctx, &int_sort, &bool_sort);
    /// let set_sort = Sort::set(&ctx, &int_sort);
    /// assert!(array_sort.is_array());
    /// assert!(set_sort.is_array());
    /// assert!(!int_sort.is_array());
    /// assert!(!bool_sort.is_array());
    /// ```
    pub fn is_array(&self) -> bool {
        self.kind() == SortKind::Array
    }

    /// Return the `Sort` of the domain for `Array`s of this `Sort`.
    ///
    /// If this `Sort` is an `Array` or `Set`, it has a domain sort, so return it.
    /// If this is not an `Array` or `Set` `Sort`, return `None`.
    /// # Examples
    /// ```
    /// # use z3::{Config, Context, Sort, ast::Ast, ast::Int, ast::Bool};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let bool_sort = Sort::bool(&ctx);
    /// let int_sort = Sort::int(&ctx);
    /// let array_sort = Sort::array(&ctx, &int_sort, &bool_sort);
    /// let set_sort = Sort::set(&ctx, &int_sort);
    /// assert_eq!(array_sort.array_domain().unwrap(), int_sort);
    /// assert_eq!(set_sort.array_domain().unwrap(), int_sort);
    /// assert!(int_sort.array_domain().is_none());
    /// assert!(bool_sort.array_domain().is_none());
    /// ```
    pub fn array_domain(&self) -> Option<Sort> {
        if self.is_array() {
            let domain_sort = unsafe { Z3_get_array_sort_domain(self.ctx.z3_ctx, self.z3_sort) };
            if domain_sort.is_null() {
                None
            } else {
                Some(Sort::new(self.ctx, domain_sort))
            }
        } else {
            None
        }
    }

    /// Return the `Sort` of the range for `Array`s of this `Sort`.
    ///
    /// If this `Sort` is an `Array` it has a range sort, so return it.
    /// If this `Sort` is a `Set`, it has an implied range sort of `Bool`.
    /// If this is not an `Array` or `Set` `Sort`, return `None`.
    /// # Examples
    /// ```
    /// # use z3::{Config, Context, Sort, ast::Ast, ast::Int, ast::Bool};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let bool_sort = Sort::bool(&ctx);
    /// let int_sort = Sort::int(&ctx);
    /// let array_sort = Sort::array(&ctx, &int_sort, &bool_sort);
    /// let set_sort = Sort::set(&ctx, &int_sort);
    /// assert_eq!(array_sort.array_range().unwrap(), bool_sort);
    /// assert_eq!(set_sort.array_range().unwrap(), bool_sort);
    /// assert!(int_sort.array_range().is_none());
    /// assert!(bool_sort.array_range().is_none());
    /// ```
    pub fn array_range(&self) -> Option<Sort> {
        if self.is_array() {
            let range_sort = unsafe { Z3_get_array_sort_range(self.ctx.z3_ctx, self.z3_sort) };
            if range_sort.is_null() {
                None
            } else {
                Some(Sort::new(self.ctx, range_sort))
            }
        } else {
            None
        }
    }
}

impl<'ctx> Clone for Sort<'ctx> {
    fn clone(&self) -> Self {
        Sort::new(self.ctx, self.z3_sort)
    }
}

impl<'ctx> fmt::Display for Sort<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_sort_to_string(self.ctx.z3_ctx, self.z3_sort) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for Sort<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> PartialEq<Sort<'ctx>> for Sort<'ctx> {
    fn eq(&self, other: &Sort<'ctx>) -> bool {
        unsafe { Z3_is_eq_sort(self.ctx.z3_ctx, self.z3_sort, other.z3_sort) }
    }
}

impl<'ctx> Eq for Sort<'ctx> {}

impl<'ctx> Drop for Sort<'ctx> {
    fn drop(&mut self) {
        unsafe {
            Z3_dec_ref(
                self.ctx.z3_ctx,
                Z3_sort_to_ast(self.ctx.z3_ctx, self.z3_sort),
            );
        }
    }
}

impl<'ctx> SortDiffers<'ctx> {
    pub fn new(left: Sort<'ctx>, right: Sort<'ctx>) -> Self {
        Self { left, right }
    }

    pub fn left(&self) -> &Sort {
        &self.left
    }

    pub fn right(&self) -> &Sort {
        &self.right
    }
}

impl<'ctx> fmt::Display for SortDiffers<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "Can not compare nodes, Sort does not match.  Nodes contain types {} and {}",
            self.left, self.right
        )
    }
}
