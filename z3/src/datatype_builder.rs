use std::mem;
use std::{convert::TryInto, ptr::null_mut};
use z3_sys::*;
use {
    Context, DatatypeAccessor, DatatypeBuilder, DatatypeSort, DatatypeVariant, DtypeBuilder,
    FuncDecl, Sort, Symbol,
};

impl<'ctx> DatatypeBuilder<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            ctx,
            variants: Vec::new(),
        }
    }

    pub fn variant(mut self, name: &str, fields: &[(&str, &Sort)]) -> Self {
        let recognizer_name_sym = Symbol::String(format!("is-{}", name)).as_z3_symbol(self.ctx);
        let name_sym = Symbol::String(name.to_string()).as_z3_symbol(self.ctx);

        assert!(fields
            .iter()
            .all(|(name, sort)| sort.ctx.z3_ctx == self.ctx.z3_ctx));

        let mut field_names: Vec<Z3_symbol> = Vec::with_capacity(fields.len());
        let mut field_sorts = Vec::with_capacity(fields.len());

        for (name, sort) in fields {
            field_names.push(Symbol::String(name.to_string()).as_z3_symbol(self.ctx));
            field_sorts.push(sort.z3_sort);
        }

        // This is unused.
        // Z3 expects sort_refs in Z3_mk_constructor to be valid, so create it here.
        let mut sort_refs = Vec::new();
        sort_refs.resize(fields.len(), 0);

        let constructor = unsafe {
            Z3_mk_constructor(
                self.ctx.z3_ctx,
                name_sym,
                recognizer_name_sym,
                fields.len().try_into().unwrap(),
                field_names.as_ptr(),
                field_sorts.as_ptr(),
                sort_refs.as_mut_ptr(),
            )
        };

        self.variants.push((fields.len(), constructor));
        self
    }

    pub fn finish(self, name: impl Into<Symbol>) -> DatatypeSort<'ctx> {
        let mut constructors: Vec<_> = self.variants.iter().map(|i| i.1).collect();
        let name_sym = name.into().as_z3_symbol(self.ctx);

        let sort = unsafe {
            let s = Z3_mk_datatype(
                self.ctx.z3_ctx,
                name_sym,
                constructors.len().try_into().unwrap(),
                constructors.as_mut_ptr(),
            );
            Z3_inc_ref(self.ctx.z3_ctx, Z3_sort_to_ast(self.ctx.z3_ctx, s));
            Sort {
                ctx: self.ctx,
                z3_sort: s,
            }
        };

        // create independent fields
        let (ctx, variants) = (self.ctx, self.variants);

        let variants = variants
            .into_iter()
            .map(|(num_fields, constructor)| {
                let mut constructor_func: Z3_func_decl = null_mut();
                let mut tester: Z3_func_decl = null_mut();
                let mut accessors: Vec<Z3_func_decl> = Vec::new();
                accessors.resize(num_fields, null_mut());

                unsafe {
                    // fill fields
                    Z3_query_constructor(
                        ctx.z3_ctx,
                        constructor,
                        num_fields.try_into().unwrap(),
                        &mut constructor_func,
                        &mut tester,
                        accessors.as_mut_ptr(),
                    );

                    // We don't need the raw constructor now that we have
                    // converted it into a func decl.
                    Z3_del_constructor(ctx.z3_ctx, constructor);

                    // convert to Rust types
                    let constructor = FuncDecl::from_raw(ctx, constructor_func);
                    let tester = FuncDecl::from_raw(ctx, tester);
                    let accessors = accessors
                        .iter()
                        .map(|f| FuncDecl::from_raw(ctx, *f))
                        .collect();

                    DatatypeVariant {
                        constructor,
                        tester,
                        accessors,
                    }
                }
            })
            .collect();

        DatatypeSort {
            ctx: self.ctx,
            sort,
            variants,
        }
    }
}

impl<'ctx> DtypeBuilder<'ctx> {
    pub fn new<S: Into<Symbol>>(ctx: &'ctx Context, name: S) -> Self {
        Self {
            ctx,
            name: name.into(),
            constructors: Vec::new(),
        }
    }

    pub fn variant(&mut self, name: &str, fields: &'ctx [(&str, DatatypeAccessor<'ctx>)]) {
        let mut accessor_vec: Vec<(String, &DatatypeAccessor<'ctx>)> = Vec::new();
        for (accessor_name, accessor) in fields {
            accessor_vec.push((accessor_name.to_string(), accessor));
        }

        self.constructors.push((name.to_string(), accessor_vec));
    }

    pub fn finish(&self) -> DatatypeSort<'ctx> {
        let mut dtypes = create_datatypes(&[self]);
        dtypes.remove(0)
    }
}

pub fn create_datatypes<'ctx>(ds: &[&DtypeBuilder<'ctx>]) -> Vec<DatatypeSort<'ctx>> {
    let ctx: &'ctx Context = ds[0].ctx;
    let num = ds.len();

    assert!(num > 0, "input ds empty");
    let mut names: Vec<Z3_symbol> = Vec::with_capacity(num);
    let out: Vec<Z3_sort> = Vec::with_capacity(num);
    let mut out = mem::ManuallyDrop::new(out);
    let mut clists: Vec<Z3_constructor_list> = Vec::with_capacity(num);

    for d in ds.iter() {
        names.push(d.name.as_z3_symbol(ctx));
        let num_cs = d.constructors.len();
        let mut cs: Vec<Z3_constructor> = Vec::with_capacity(num_cs);

        for (cname, fs) in &d.constructors {
            let mut rname: String = "is-".to_string();
            rname.push_str(cname);

            let cname_symbol: Z3_symbol = Symbol::String(cname.clone()).as_z3_symbol(ctx);
            let rname_symbol: Z3_symbol = Symbol::String(rname).as_z3_symbol(ctx);

            let num_fs = fs.len();
            let mut field_names: Vec<Z3_symbol> = Vec::with_capacity(num_fs);
            let mut field_sorts: Vec<Z3_sort> = Vec::with_capacity(num_fs);
            let mut sort_refs: Vec<::std::os::raw::c_uint> = Vec::with_capacity(num_fs);

            for (fname, accessor) in fs {
                field_names.push(Symbol::String(fname.clone()).as_z3_symbol(ctx));
                match accessor {
                    DatatypeAccessor::Datatype(dtype_name) => {
                        field_sorts.push(std::ptr::null_mut());

                        let matching_names: Vec<_> = ds
                            .iter()
                            .enumerate()
                            .filter(|&(i, x)| &x.name == dtype_name)
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
                    ctx.z3_ctx,
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
        assert!(cs.len() > 0, "Empty cs vec");

        let clist = unsafe {
            Z3_mk_constructor_list(ctx.z3_ctx, num_cs.try_into().unwrap(), cs.as_mut_ptr())
        };
        clists.push(clist);
    }
    assert!(clists.len() > 0, "Empty clist vec");

    assert!(num == names.len());
    assert!(num == clists.len());
    unsafe {
        Z3_mk_datatypes(
            ctx.z3_ctx,
            num.try_into().unwrap(),
            names.as_ptr(),
            out.as_mut_ptr(),
            clists.as_mut_ptr(),
        );
    };

    println!("returned from z3_mk_datatypes");

    let rebuilt = unsafe { Vec::from_raw_parts(out.as_mut_ptr(), num, num) };

    assert!(rebuilt.len() > 0, "empty rebuilt vec.");

    let mut datatype_sorts: Vec<DatatypeSort<'ctx>> = Vec::with_capacity(rebuilt.len());
    for i in 0..rebuilt.len() {
        let s = rebuilt[i];
        let d = &ds[i];
        let num_cs = d.constructors.len();

        unsafe { Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, s)) };
        let sort = Sort { ctx, z3_sort: s };

        let mut variants: Vec<DatatypeVariant<'ctx>> = Vec::with_capacity(num_cs as usize);

        for (j, (cname, fs)) in d.constructors.iter().enumerate() {
            let num_fs = fs.len();
            let constructor: FuncDecl<'ctx> = unsafe {
                let f: Z3_func_decl =
                    Z3_get_datatype_sort_constructor(ctx.z3_ctx, s, j.try_into().unwrap());
                FuncDecl::from_raw(ctx, f)
            };
            let tester = unsafe {
                let f: Z3_func_decl =
                    Z3_get_datatype_sort_recognizer(ctx.z3_ctx, s, j.try_into().unwrap());
                FuncDecl::from_raw(ctx, f)
            };
            let mut accessors: Vec<FuncDecl<'ctx>> = Vec::new();
            for k in 0..num_fs {
                accessors.push(unsafe {
                    let f: Z3_func_decl = Z3_get_datatype_sort_constructor_accessor(
                        ctx.z3_ctx,
                        s,
                        j.try_into().unwrap(),
                        k.try_into().unwrap(),
                    );

                    FuncDecl::from_raw(ctx, f)
                })
            }

            variants.push(DatatypeVariant {
                constructor,
                tester,
                accessors,
            });
        }

        datatype_sorts.push(DatatypeSort {
            ctx,
            sort,
            variants,
        })
    }

    datatype_sorts
}
