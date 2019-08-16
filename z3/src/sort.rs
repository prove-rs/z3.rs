use z3_sys::*;
use Context;
use Sort;

impl Sort {
    pub fn as_z3_sort(&self, ctx: &Context) -> Z3_sort {
        unsafe {
            match self {
                Sort::Uninterpreted(name) => {
                    Z3_mk_uninterpreted_sort(ctx.z3_ctx, name.as_z3_symbol(ctx))
                }
                Sort::Bool => Z3_mk_bool_sort(ctx.z3_ctx),
                Sort::Int => Z3_mk_int_sort(ctx.z3_ctx),
                Sort::Real => Z3_mk_real_sort(ctx.z3_ctx),
                Sort::BitVector(sz) => Z3_mk_bv_sort(ctx.z3_ctx, *sz as ::std::os::raw::c_uint),
                Sort::Set(elt) => Z3_mk_set_sort(ctx.z3_ctx, elt.as_z3_sort(ctx)),
                _ => unimplemented!(),
            }
        }
    }

    /*
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
        /// let model = solver.get_model();
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
    */
}
