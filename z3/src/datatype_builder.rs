//! Helpers for building custom [datatype sorts](DatatypeSort).
//! The main entry point is [create_datatypes](create_datatypes) which returns a
//! list of sorts(more than one for the case that you are defining a set of
//! mutually recursive data types)
//!
//!
//! # Example
//!
//! If you just want to define a single recursive datatype, you can do so with
//! the standard [DatatypeBuilder](DatatypeBuilder) as so.
//!
//! ```rust
//! use z3::{Sort, DatatypeAccessor, DatatypeBuilder, Symbol};
//! let dt = DatatypeBuilder::new("my_datatype")
//!     .variant("case1", vec![("field1", DatatypeAccessor::sort(Sort::int()))])
//!     .variant("case2", vec![("field2", DatatypeAccessor::datatype("my_datatype"))])
//!     .finish();
//! ```
//!
//! For mutually recursive types, you must use [create_datatypes](create_datatypes)
//!
//! ```rust
//! use z3::{Sort, DatatypeAccessor, DatatypeBuilder, Symbol, datatype_builder::create_datatypes};
//! let my_tree = DatatypeBuilder::new("my_tree")
//!     .variant("leaf", vec![])
//!     .variant("node", vec![("children", DatatypeAccessor::datatype("my_list"))]);
//!
//! let my_list = DatatypeBuilder::new("my_list")
//!     .variant("nil", vec![])
//!     .variant("cons", vec![("hd", DatatypeAccessor::datatype("my_tree")), ("tl", DatatypeAccessor::datatype("my_list"))]);
//!
//! let dts = create_datatypes(vec![my_tree, my_list]);
//! ```
//!

use std::{convert::TryInto, ptr::null_mut};
use z3_sys::*;

use crate::{Context, DatatypeBuilder, DatatypeSort, DatatypeVariant, FuncDecl, Sort, Symbol};
impl DatatypeBuilder {
    pub fn new<S: Into<Symbol>>(name: S) -> Self {
        let ctx = &Context::thread_local();
        Self {
            ctx: ctx.clone(),
            name: name.into(),
            constructors: Vec::new(),
        }
    }

    pub fn variant(mut self, name: &str, fields: Vec<(&str, DatatypeAccessor)>) -> Self {
        let mut accessor_vec: Vec<(String, DatatypeAccessor)> = Vec::new();
        for (accessor_name, accessor) in fields {
            accessor_vec.push((accessor_name.to_string(), accessor));
        }

        self.constructors.push((name.to_string(), accessor_vec));

        self
    }

    pub fn finish(self) -> DatatypeSort {
        let mut dtypes = create_datatypes(vec![self]);
        dtypes.remove(0)
    }
}

pub fn create_datatypes(datatype_builders: Vec<DatatypeBuilder>) -> Vec<DatatypeSort> {
    let num = datatype_builders.len();
    assert!(num > 0, "At least one DatatypeBuilder must be specified");

    // todo: should we check that all the contexts are the same? (Currently
    // not necessary since one can only use the thread local to construct a
    // datatype builder)
    let ctx: Context = datatype_builders[0].ctx.clone();
    let mut names: Vec<Z3_symbol> = Vec::with_capacity(num);

    let mut raw_sorts: Vec<Z3_sort> = Vec::with_capacity(num);
    let mut clists: Vec<Z3_constructor_list> = Vec::with_capacity(num);

    // Collect all the `Z3_constructor`s that we create in here so that we can
    // free them later, once we've created the associated `FuncDecl`s and don't
    // need the raw constructor anymore.
    let mut ctors: Vec<Z3_constructor> = Vec::with_capacity(num * 2);

    for d in datatype_builders.iter() {
        names.push(d.name.as_z3_symbol());
        let num_cs = d.constructors.len();
        let mut cs: Vec<Z3_constructor> = Vec::with_capacity(num_cs);

        for (cname, fs) in &d.constructors {
            let mut rname: String = "is-".to_string();
            rname.push_str(cname);

            let cname_symbol: Z3_symbol = Symbol::String(cname.clone()).as_z3_symbol();
            let rname_symbol: Z3_symbol = Symbol::String(rname).as_z3_symbol();

            let num_fs = fs.len();
            let mut field_names: Vec<Z3_symbol> = Vec::with_capacity(num_fs);
            let mut field_sorts: Vec<Z3_sort> = Vec::with_capacity(num_fs);
            let mut sort_refs: Vec<::std::os::raw::c_uint> = Vec::with_capacity(num_fs);

            for (fname, accessor) in fs {
                field_names.push(Symbol::String(fname.clone()).as_z3_symbol());
                match accessor {
                    DatatypeAccessor::Datatype(dtype_name) => {
                        field_sorts.push(null_mut());

                        let matching_names: Vec<_> = datatype_builders
                            .iter()
                            .enumerate()
                            .filter(|&(_, x)| &x.name == dtype_name)
                            .collect();

                        assert_eq!(
                            1,
                            matching_names.len(),
                            "One and only one occurrence of each datatype is expected."
                        );

                        let (sort_ref, _) = matching_names[0];
                        sort_refs.push(sort_ref as u32);
                    }
                    DatatypeAccessor::Sort(sort) => {
                        field_sorts.push(sort.z3_sort);
                        sort_refs.push(0);
                    }
                }
            }

            let constructor = unsafe {
                Z3_mk_constructor(
                    ctx.z3_ctx.0,
                    cname_symbol,
                    rname_symbol,
                    num_fs.try_into().unwrap(),
                    field_names.as_ptr(),
                    field_sorts.as_ptr(),
                    sort_refs.as_mut_ptr(),
                )
            };
            cs.push(constructor);
        }
        assert!(!cs.is_empty());

        let clist = unsafe {
            Z3_mk_constructor_list(ctx.z3_ctx.0, num_cs.try_into().unwrap(), cs.as_mut_ptr())
        };
        clists.push(clist);
        ctors.extend(cs);
    }

    assert_eq!(num, names.len());
    assert_eq!(num, clists.len());

    unsafe {
        Z3_mk_datatypes(
            ctx.z3_ctx.0,
            num.try_into().unwrap(),
            names.as_ptr(),
            raw_sorts.as_mut_ptr(),
            clists.as_mut_ptr(),
        );
        raw_sorts.set_len(num);
    };

    let mut datatype_sorts: Vec<DatatypeSort> = Vec::with_capacity(raw_sorts.len());
    for (z3_sort, datatype_builder) in raw_sorts.into_iter().zip(&datatype_builders) {
        let num_cs = datatype_builder.constructors.len();

        unsafe { Z3_inc_ref(ctx.z3_ctx.0, Z3_sort_to_ast(ctx.z3_ctx.0, z3_sort)) };
        let sort = Sort {
            ctx: ctx.clone(),
            z3_sort,
        };

        let mut variants: Vec<DatatypeVariant> = Vec::with_capacity(num_cs);

        for (j, (_cname, fs)) in datatype_builder.constructors.iter().enumerate() {
            let num_fs = fs.len();

            let raw_constructor: Z3_func_decl = unsafe {
                Z3_get_datatype_sort_constructor(ctx.z3_ctx.0, z3_sort, j.try_into().unwrap())
            };
            let constructor: FuncDecl = unsafe { FuncDecl::wrap(&ctx, raw_constructor) };

            let tester_func: Z3_func_decl = unsafe {
                Z3_get_datatype_sort_recognizer(ctx.z3_ctx.0, z3_sort, j.try_into().unwrap())
            };
            let tester = unsafe { FuncDecl::wrap(&ctx, tester_func) };

            let mut accessors: Vec<FuncDecl> = Vec::new();
            for k in 0..num_fs {
                let accessor_func: Z3_func_decl = unsafe {
                    Z3_get_datatype_sort_constructor_accessor(
                        ctx.z3_ctx.0,
                        z3_sort,
                        j.try_into().unwrap(),
                        k.try_into().unwrap(),
                    )
                };

                accessors.push(unsafe { FuncDecl::wrap(&ctx, accessor_func) });
            }

            variants.push(DatatypeVariant {
                constructor,
                tester,
                accessors,
            });
        }

        datatype_sorts.push(DatatypeSort { sort, variants });
    }

    for ctor in ctors {
        unsafe {
            Z3_del_constructor(ctx.z3_ctx.0, ctor);
        }
    }

    for clist in clists {
        unsafe {
            Z3_del_constructor_list(ctx.z3_ctx.0, clist);
        }
    }

    datatype_sorts
}

/// Wrapper which can point to a sort (by value) or to a custom datatype (by name).
#[derive(Debug)]
pub enum DatatypeAccessor {
    Sort(Sort),
    Datatype(Symbol),
}

impl DatatypeAccessor {
    pub fn sort<S: Into<Sort>>(s: S) -> Self {
        Self::Sort(s.into())
    }

    pub fn datatype<S: Into<Symbol>>(s: S) -> Self {
        Self::Datatype(s.into())
    }
}
