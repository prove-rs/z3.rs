use std::convert::TryInto;
use std::ffi::CStr;
use std::{fmt, mem};
use std::marker::PhantomData;
use z3_sys::*;

use crate::ast::{Array, BV, Bool, Dynamic, Float, Int, Real, Seq, Set};
use crate::{Context, FuncDecl, Sort, SortDiffers, Symbol};

impl<A> Sort<A> {
    pub(crate) unsafe fn wrap(ctx: &Context, z3_sort: Z3_sort) -> Sort<A> {
        unsafe {
            Z3_inc_ref(ctx.z3_ctx.0, Z3_sort_to_ast(ctx.z3_ctx.0, z3_sort));
        }
        Sort {
            ctx: ctx.clone(),
            z3_sort,
            phantom: PhantomData::default(),
        }
    }

    pub fn get_z3_sort(&self) -> Z3_sort {
        self.z3_sort
    }

    pub fn uninterpreted(name: Symbol) -> Sort<Dynamic> {
        let ctx = &Context::thread_local();

        unsafe {
            Sort::wrap(
                ctx,
                Z3_mk_uninterpreted_sort(ctx.z3_ctx.0, name.as_z3_symbol()),
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
    /// let red_const = color_consts[0].apply(&[]);
    /// let red_tester = &color_testers[0];
    /// let eq = red_tester.apply(&[&red_const]);
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
        let mut enum_consts = vec![std::ptr::null_mut(); enum_names.len()];
        let mut enum_testers = vec![std::ptr::null_mut(); enum_names.len()];

        let sort = unsafe {
            Sort::wrap(
                ctx,
                Z3_mk_enumeration_sort(
                    ctx.z3_ctx.0,
                    name.as_z3_symbol(),
                    enum_names.len().try_into().unwrap(),
                    enum_names.as_ptr(),
                    enum_consts.as_mut_ptr(),
                    enum_testers.as_mut_ptr(),
                ),
            )
        };

        // increase ref counts
        for i in &enum_consts {
            unsafe {
                Z3_inc_ref(ctx.z3_ctx.0, *i as Z3_ast);
            }
        }
        for i in &enum_testers {
            unsafe {
                Z3_inc_ref(ctx.z3_ctx.0, *i as Z3_ast);
            }
        }

        // convert to Rust types
        let enum_consts: Vec<_> = enum_consts
            .iter()
            .map(|z3_func_decl| FuncDecl {
                ctx: ctx.clone(),
                z3_func_decl: *z3_func_decl,
            })
            .collect();
        let enum_testers: Vec<_> = enum_testers
            .iter()
            .map(|z3_func_decl| FuncDecl {
                ctx: ctx.clone(),
                z3_func_decl: *z3_func_decl,
            })
            .collect();

        (sort, enum_consts, enum_testers)
    }

    pub fn kind(&self) -> SortKind {
        unsafe { Z3_get_sort_kind(self.ctx.z3_ctx.0, self.z3_sort) }
    }

    /// Returns `Some(e)` where `e` is the number of exponent bits if the sort
    /// is a `FloatingPoint` and `None` otherwise.
    pub fn float_exponent_size(&self) -> Option<u32> {
        if self.kind() == SortKind::FloatingPoint {
            Some(unsafe { Z3_fpa_get_ebits(self.ctx.z3_ctx.0, self.z3_sort) })
        } else {
            None
        }
    }

    /// Returns `Some(s)` where `s` is the number of significand bits if the sort
    /// is a `FloatingPoint` and `None` otherwise.
    pub fn float_significand_size(&self) -> Option<u32> {
        if self.kind() == SortKind::FloatingPoint {
            Some(unsafe { Z3_fpa_get_sbits(self.ctx.z3_ctx.0, self.z3_sort) })
        } else {
            None
        }
    }

    /// Return if this Sort is for an `Array` or a `Set`.
    ///
    /// # Examples
    /// ```
    /// # use z3::{Config, Context, Sort, ast::Ast, ast::Int, ast::Bool};
    /// let bool_sort = Sort::bool();
    /// let int_sort = Sort::int();
    /// let array_sort = Sort::array(&int_sort, &bool_sort);
    /// let set_sort = Sort::set(&int_sort);
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
    /// let bool_sort = Sort::bool();
    /// let int_sort = Sort::int();
    /// let array_sort = Sort::array(&int_sort, &bool_sort);
    /// let set_sort = Sort::set(&int_sort);
    /// assert_eq!(array_sort.array_domain().unwrap(), int_sort);
    /// assert_eq!(set_sort.array_domain().unwrap(), int_sort);
    /// assert!(int_sort.array_domain().is_none());
    /// assert!(bool_sort.array_domain().is_none());
    /// ```
    pub fn array_domain(&self) -> Option<Sort<Dynamic>> {
        if self.is_array() {
            unsafe {
                let domain_sort = Z3_get_array_sort_domain(self.ctx.z3_ctx.0, self.z3_sort);
                if domain_sort.is_null() {
                    None
                } else {
                    Some(Sort::wrap(&self.ctx, domain_sort))
                }
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
    /// let bool_sort = Sort::bool();
    /// let int_sort = Sort::int();
    /// let array_sort = Sort::array(&int_sort, &bool_sort);
    /// let set_sort = Sort::set(&int_sort);
    /// assert_eq!(array_sort.array_range().unwrap(), bool_sort);
    /// assert_eq!(set_sort.array_range().unwrap(), bool_sort);
    /// assert!(int_sort.array_range().is_none());
    /// assert!(bool_sort.array_range().is_none());
    /// ```
    pub fn array_range(&self) -> Option<Sort<Dynamic>> {
        if self.is_array() {
            unsafe {
                let range_sort = Z3_get_array_sort_range(self.ctx.z3_ctx.0, self.z3_sort);
                if range_sort.is_null() {
                    None
                } else {
                    Some(Sort::wrap(&self.ctx, range_sort))
                }
            }
        } else {
            None
        }
    }
}

impl Sort<Bool>{
    pub fn bool() -> Self {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_bool_sort(ctx.z3_ctx.0))
        }
    }
}

impl Sort<Int>{
    pub fn int() -> Self {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_int_sort(ctx.z3_ctx.0))
        }
    }
}

impl Sort<Real>{
    pub fn real() -> Sort<Real> {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_real_sort(ctx.z3_ctx.0))
        }
    }
}

impl Sort<Float>{
    pub fn float(ebits: u32, sbits: u32) -> Sort<Float> {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_fpa_sort(ctx.z3_ctx.0, ebits, sbits))
        }
    }

    pub fn float32() -> Sort<Float> {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_fpa_sort(ctx.z3_ctx.0, 8, 24))
        }
    }
    pub fn double() -> Sort<Float> {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_fpa_sort(ctx.z3_ctx.0, 11, 53))
        }
    }

}

impl Sort<BV>{
    pub fn bitvector(sz: u32) -> Sort<BV> {
        let ctx = &Context::thread_local();

        unsafe {
            Sort::wrap(
                ctx,
                Z3_mk_bv_sort(ctx.z3_ctx.0, sz as ::std::os::raw::c_uint),
            )
        }
    }
}

impl Sort<String>{
    pub fn string() -> Sort<crate::ast::String> {
        unsafe {
            let ctx = &Context::thread_local();
            Sort::wrap(ctx, Z3_mk_string_sort(ctx.z3_ctx.0))
        }
    }
}

impl Sort<Seq>{
    pub fn seq<B>(elt: &Sort<B>) -> Sort<Seq> {
        let ctx = &Context::thread_local();

        unsafe { Sort::wrap(ctx, Z3_mk_seq_sort(ctx.z3_ctx.0, elt.z3_sort)) }
    }
}

impl Sort<Set>{
    pub fn set<B>(elt: &Sort<B>) -> Sort<Set> {
        let ctx = &Context::thread_local();

        unsafe { Sort::wrap(ctx, Z3_mk_set_sort(ctx.z3_ctx.0, elt.z3_sort)) }
    }
}

impl Sort<Array>{
    pub fn array<B, C>(domain: &Sort<B>, range: &Sort<C>) -> Sort<Array> {
        let ctx = &Context::thread_local();

        unsafe {
            Sort::wrap(
                ctx,
                Z3_mk_array_sort(ctx.z3_ctx.0, domain.z3_sort, range.z3_sort),
            )
        }
    }
}

impl<A> Sort<A>{
    pub(crate) fn as_dyn(&self) -> Sort<Dynamic>{
        Sort{
            ctx: self.ctx.clone(),
            z3_sort: self.z3_sort,
            phantom: PhantomData::default(),
        }
    }
}
macro_rules! into_dynamic_sort {
    ($t:ty) => {
        impl From<Sort<$t>> for Sort<Dynamic>{
            fn from(value: Sort<$t>) -> Self {
                Self{
                    ctx: value.ctx.clone(),
                    z3_sort: value.z3_sort,
                    phantom: PhantomData::default(),
                }
            }
        }
    };
}

into_dynamic_sort!(Bool);
into_dynamic_sort!(Int);
into_dynamic_sort!(Real);
into_dynamic_sort!(Float);
into_dynamic_sort!(BV);
into_dynamic_sort!(String);
into_dynamic_sort!(Seq);
into_dynamic_sort!(Set);
into_dynamic_sort!(Array);


impl<A> Clone for Sort<A> {
    fn clone(&self) -> Self {
        unsafe { Self::wrap(&self.ctx, self.z3_sort) }
    }
}

impl<A> fmt::Display for Sort<A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_sort_to_string(self.ctx.z3_ctx.0, self.z3_sort) };
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

impl<A> PartialEq<Sort<A>> for Sort<A> {
    fn eq(&self, other: &Sort<A>) -> bool {
        unsafe { Z3_is_eq_sort(self.ctx.z3_ctx.0, self.z3_sort, other.z3_sort) }
    }
}

impl<A> Eq for Sort<A> {}

impl<A> Drop for Sort<A> {
    fn drop(&mut self) {
        unsafe {
            Z3_dec_ref(
                self.ctx.z3_ctx.0,
                Z3_sort_to_ast(self.ctx.z3_ctx.0, self.z3_sort),
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
