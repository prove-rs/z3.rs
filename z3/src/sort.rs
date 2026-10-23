use std::convert::TryInto;
use std::ffi::CStr;
use std::fmt;
use std::marker::PhantomData;
use std::ptr::NonNull;
use z3_sys::*;

use crate::ast::{Array, Ast, BV, Bool, Char, Dynamic, Float, Int, Real, Seq, Set, SortMarker};
use crate::{Context, FuncDecl, Sort, SortDiffers, Symbol};

impl<A> Sort<A> {
    pub(crate) unsafe fn wrap(ctx: &Context, z3_sort: Z3_sort) -> Sort<A> {
        unsafe {
            Z3_inc_ref(
                ctx.z3_ctx.as_ptr(),
                Z3_sort_to_ast(ctx.z3_ctx.as_ptr(), z3_sort).unwrap(),
            );
        }
        Sort {
            ctx: ctx.clone(),
            z3_sort,
            phantom: PhantomData,
        }
    }

    pub fn get_z3_sort(&self) -> Z3_sort {
        self.z3_sort
    }

    /// Erase the static sort marker, yielding a dynamically-typed `Sort<Dynamic>`.
    pub fn as_dyn(&self) -> Sort<Dynamic> {
        unsafe { Sort::wrap(&self.ctx, self.z3_sort) }
    }

    pub fn kind(&self) -> SortKind {
        unsafe { Z3_get_sort_kind(self.ctx.z3_ctx.0, self.z3_sort) }
    }

    /// Attempt to narrow this `Sort` to a specific parameterization `T`, e.g.
    /// `Sort<Array<Int, Bool>>` or `Sort<Float>`, checking the actual runtime shape of the
    /// sort (including, for parameterized `T`, its domain/range/element sorts) rather than
    /// just trusting a phantom marker.
    ///
    /// This is the only way to reach the type-specific accessors that live on a concrete
    /// `Sort<Array<D, R>>` (`domain`/`range`) or `Sort<Float>` (`exponent_size`/
    /// `significand_size`) starting from a `Sort<Dynamic>`.
    ///
    /// # Examples
    /// ```
    /// # use z3::{Sort, ast::{Array, Bool, Int}};
    /// let sort = Sort::array(&Sort::int(), &Sort::bool()).as_dyn();
    /// assert!(sort.narrow::<Array<Int, Bool>>().is_some());
    /// assert!(sort.narrow::<Array<Bool, Int>>().is_none());
    /// ```
    pub fn narrow<T: SortMarker>(&self) -> Option<Sort<T>> {
        T::sort_matches(&self.as_dyn()).then(|| unsafe { Sort::wrap(&self.ctx, self.z3_sort) })
    }
}

impl<D: Ast, R: Ast> Sort<Array<D, R>> {
    /// Return the `Sort` of the domain for `Array`s of this `Sort`.
    ///
    /// # Examples
    /// ```
    /// # use z3::Sort;
    /// let array_sort = Sort::array(&Sort::int(), &Sort::bool());
    /// assert_eq!(array_sort.domain(), Sort::int());
    /// ```
    pub fn domain(&self) -> Sort<D> {
        unsafe {
            Sort::wrap(
                &self.ctx,
                Z3_get_array_sort_domain(self.ctx.z3_ctx.0, self.z3_sort).unwrap(),
            )
        }
    }

    /// Return the `Sort` of the range for `Array`s of this `Sort`.
    ///
    /// # Examples
    /// ```
    /// # use z3::Sort;
    /// let array_sort = Sort::array(&Sort::int(), &Sort::bool());
    /// assert_eq!(array_sort.range(), Sort::bool());
    /// ```
    pub fn range(&self) -> Sort<R> {
        unsafe {
            Sort::wrap(
                &self.ctx,
                Z3_get_array_sort_range(self.ctx.z3_ctx.0, self.z3_sort).unwrap(),
            )
        }
    }
}

impl<Elt: Ast> Sort<Set<Elt>> {
    /// Return the `Sort` of the elements of `Set`s of this `Sort`.
    ///
    /// # Examples
    /// ```
    /// # use z3::Sort;
    /// let set_sort = Sort::set(&Sort::int());
    /// assert_eq!(set_sort.domain(), Sort::int());
    /// ```
    pub fn domain(&self) -> Sort<Elt> {
        unsafe {
            Sort::wrap(
                &self.ctx,
                Z3_get_array_sort_domain(self.ctx.z3_ctx.0, self.z3_sort).unwrap(),
            )
        }
    }
}

impl Sort<Float> {
    /// Return the number of exponent bits of this `FloatingPoint` `Sort`.
    ///
    /// # Examples
    /// ```
    /// # use z3::Sort;
    /// assert_eq!(Sort::double().exponent_size(), 11);
    /// ```
    pub fn exponent_size(&self) -> u32 {
        unsafe { Z3_fpa_get_ebits(self.ctx.z3_ctx.0, self.z3_sort) }
    }

    /// Return the number of significand bits of this `FloatingPoint` `Sort`.
    ///
    /// # Examples
    /// ```
    /// # use z3::Sort;
    /// assert_eq!(Sort::double().significand_size(), 53);
    /// ```
    pub fn significand_size(&self) -> u32 {
        unsafe { Z3_fpa_get_sbits(self.ctx.z3_ctx.0, self.z3_sort) }
    }
}

impl Sort<Dynamic> {
    pub fn uninterpreted(name: Symbol) -> Sort<Dynamic> {
        let ctx = &Context::thread_local();

        unsafe {
            Sort::wrap(
                ctx,
                Z3_mk_uninterpreted_sort(ctx.z3_ctx.as_ptr(), name.as_z3_symbol()).unwrap(),
            )
        }
    }

    pub fn bool() -> Sort<Bool> {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_bool_sort(ctx.z3_ctx.as_ptr()).unwrap())
        }
    }

    pub fn int() -> Sort<Int> {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_int_sort(ctx.z3_ctx.as_ptr()).unwrap())
        }
    }

    pub fn real() -> Sort<Real> {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_real_sort(ctx.z3_ctx.as_ptr()).unwrap())
        }
    }

    pub fn float(ebits: u32, sbits: u32) -> Sort<Float> {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(
                ctx,
                Z3_mk_fpa_sort(ctx.z3_ctx.as_ptr(), ebits, sbits).unwrap(),
            )
        }
    }

    pub fn float32() -> Sort<Float> {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_fpa_sort(ctx.z3_ctx.as_ptr(), 8, 24).unwrap())
        }
    }

    pub fn double() -> Sort<Float> {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_fpa_sort(ctx.z3_ctx.as_ptr(), 11, 53).unwrap())
        }
    }

    pub fn string() -> Sort<crate::ast::String> {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_string_sort(ctx.z3_ctx.as_ptr()).unwrap())
        }
    }

    pub fn char() -> Sort<Char> {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_char_sort(ctx.z3_ctx.as_ptr()).unwrap())
        }
    }

    pub fn bitvector(sz: u32) -> Sort<BV> {
        let ctx = &Context::thread_local();

        unsafe {
            Sort::wrap(
                ctx,
                Z3_mk_bv_sort(ctx.z3_ctx.as_ptr(), sz as ::std::os::raw::c_uint).unwrap(),
            )
        }
    }

    pub fn array<D, R>(domain: &Sort<D>, range: &Sort<R>) -> Sort<Array<D, R>> {
        let ctx = &Context::thread_local();

        unsafe {
            Sort::wrap(
                ctx,
                Z3_mk_array_sort(ctx.z3_ctx.as_ptr(), domain.z3_sort, range.z3_sort).unwrap(),
            )
        }
    }

    pub fn set<Elt>(elt: &Sort<Elt>) -> Sort<Set<Elt>> {
        let ctx = &Context::thread_local();

        unsafe {
            Sort::wrap(
                ctx,
                Z3_mk_set_sort(ctx.z3_ctx.as_ptr(), elt.z3_sort).unwrap(),
            )
        }
    }

    pub fn seq<Elt>(elt: &Sort<Elt>) -> Sort<Seq<Elt>> {
        let ctx = &Context::thread_local();

        unsafe {
            Sort::wrap(
                ctx,
                Z3_mk_seq_sort(ctx.z3_ctx.as_ptr(), elt.z3_sort).unwrap(),
            )
        }
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
    /// # use z3::ast::Dynamic;
    /// # let cfg = Config::new();
    /// # let solver = Solver::new();
    /// let (colors, color_consts, color_testers) = Sort::enumeration(
    ///     "Color".into(),
    ///     &[
    ///         "Red".into(),
    ///         "Green".into(),
    ///         "Blue".into(),
    ///     ],
    /// );
    ///
    /// let red_const = color_consts[0].apply(vec![]);
    /// let red_tester = &color_testers[0];
    /// let eq = red_tester.apply(vec![Dynamic::from_ast(&red_const)]);
    ///
    /// assert_eq!(solver.check(), SatResult::Sat);
    /// let model = solver.get_model().unwrap();;
    ///
    /// assert!(model.eval(&eq, true).unwrap().as_bool().unwrap().as_bool().unwrap());
    /// ```
    pub fn enumeration(
        name: Symbol,
        enum_names: &[Symbol],
    ) -> (Sort<Dynamic>, Vec<FuncDecl>, Vec<FuncDecl>) {
        let ctx = &Context::thread_local();
        let enum_names: Vec<_> = enum_names.iter().map(|s| s.as_z3_symbol()).collect();
        let mut enum_consts = vec![std::ptr::null_mut::<_Z3_func_decl>(); enum_names.len()];
        let mut enum_testers = vec![std::ptr::null_mut::<_Z3_func_decl>(); enum_names.len()];

        let sort = unsafe {
            Sort::wrap(
                ctx,
                Z3_mk_enumeration_sort(
                    ctx.z3_ctx.as_ptr(),
                    name.as_z3_symbol(),
                    enum_names.len().try_into().unwrap(),
                    enum_names.as_ptr(),
                    enum_consts.as_mut_ptr() as *mut Z3_func_decl,
                    enum_testers.as_mut_ptr() as *mut Z3_func_decl,
                )
                .unwrap(),
            )
        };

        // increase ref counts
        for i in &enum_consts {
            unsafe {
                Z3_inc_ref(
                    ctx.z3_ctx.as_ptr(),
                    Z3_func_decl_to_ast(ctx.z3_ctx.as_ptr(), NonNull::new(*i).unwrap()).unwrap(),
                );
            }
        }
        for i in &enum_testers {
            unsafe {
                Z3_inc_ref(
                    ctx.z3_ctx.as_ptr(),
                    Z3_func_decl_to_ast(ctx.z3_ctx.as_ptr(), NonNull::new(*i).unwrap()).unwrap(),
                );
            }
        }

        // convert to Rust types
        let enum_consts: Vec<_> = enum_consts
            .into_iter()
            .map(|z3_func_decl| unsafe { FuncDecl::wrap(ctx, NonNull::new(z3_func_decl).unwrap()) })
            .collect();
        let enum_testers: Vec<_> = enum_testers
            .into_iter()
            .map(|z3_func_decl| unsafe { FuncDecl::wrap(ctx, NonNull::new(z3_func_decl).unwrap()) })
            .collect();

        (sort, enum_consts, enum_testers)
    }
}

impl<A> Clone for Sort<A> {
    fn clone(&self) -> Self {
        unsafe { Self::wrap(&self.ctx, self.z3_sort) }
    }
}

impl<A> fmt::Display for Sort<A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_sort_to_string(self.ctx.z3_ctx.as_ptr(), self.z3_sort) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{s}"),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<A> fmt::Debug for Sort<A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

// Sort equality reflects Z3's own runtime sort identity, independent of the phantom marker,
// so comparisons across differently-typed `Sort<A>`/`Sort<B>` are allowed.
impl<A, B> PartialEq<Sort<B>> for Sort<A> {
    fn eq(&self, other: &Sort<B>) -> bool {
        unsafe { Z3_is_eq_sort(self.ctx.z3_ctx.as_ptr(), self.z3_sort, other.z3_sort) }
    }
}

impl<A> Eq for Sort<A> {}

impl<A> Drop for Sort<A> {
    fn drop(&mut self) {
        unsafe {
            Z3_dec_ref(
                self.ctx.z3_ctx.as_ptr(),
                Z3_sort_to_ast(self.ctx.z3_ctx.as_ptr(), self.z3_sort).unwrap(),
            );
        }
    }
}

impl<A, B> SortDiffers<A, B> {
    pub fn new(left: Sort<A>, right: Sort<B>) -> Self {
        Self { left, right }
    }

    pub fn left(&self) -> &Sort<A> {
        &self.left
    }

    pub fn right(&self) -> &Sort<B> {
        &self.right
    }
}

impl<A, B> fmt::Display for SortDiffers<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "Can not compare nodes, Sort does not match.  Nodes contain types {} and {}",
            self.left, self.right
        )
    }
}
