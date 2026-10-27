use std::fmt;
use std::{ffi::CStr, iter::FusedIterator};
use z3_sys::*;

use crate::{
    AstVector, Context, FuncDecl, FuncInterp, Interp, Model, Optimize, Solver, Sort, Translate,
    ast::{Ast, Dynamic},
};

impl Model {
    /// A new instance of an *empty* model, not tied to any particular solver. Internally used
    /// by [`Optimize::set_model_handler`].
    ///
    /// Note: [`Model::of_optimize`] cannot be used here because it assumes the solver already
    /// has a model, whereas [`Optimize::set_model_handler`] registers before the solver
    /// has found any model at all.
    pub(crate) fn new_empty(ctx: &Context) -> Model {
        unsafe {
            let m = Z3_mk_model(ctx.z3_ctx.as_ptr()).expect("Cannot allocate new Z3_model.");
            Self::wrap(ctx, m)
        }
    }

    /// Creates a new, empty model, not tied to any particular solver.
    ///
    /// Interpretations can be added with [`Model::add_const_interp`] and
    /// [`Model::add_func_interp`], and the model can then be queried with e.g.
    /// [`Model::eval`].
    ///
    /// # Examples
    /// ```
    /// # use z3::{Model, ast::{Ast, Int}};
    /// let x = Int::new_const("x");
    /// let model = Model::new();
    /// model.add_const_interp(&x.decl(), &Int::from_i64(3));
    /// assert_eq!(model.eval(&(&x + 1), true).unwrap().as_i64(), Some(4));
    /// ```
    pub fn new() -> Model {
        Self::new_empty(&Context::thread_local())
    }

    unsafe fn wrap(ctx: &Context, z3_mdl: Z3_model) -> Model {
        unsafe {
            Z3_model_inc_ref(ctx.z3_ctx.as_ptr(), z3_mdl);
        }
        Model {
            ctx: ctx.clone(),
            z3_mdl,
        }
    }

    pub fn of_solver(slv: &Solver) -> Option<Model> {
        unsafe {
            let m = Z3_solver_get_model(slv.ctx.z3_ctx.as_ptr(), slv.z3_slv);
            Some(Self::wrap(&slv.ctx, m?))
        }
    }

    pub fn of_optimize(opt: &Optimize) -> Option<Model> {
        unsafe {
            let m = Z3_optimize_get_model(opt.ctx.z3_ctx.as_ptr(), opt.z3_opt);
            Some(Self::wrap(&opt.ctx, m?))
        }
    }

    /// Returns the interpretation of the given `ast` in the `Model`
    /// Returns `None` if there is no interpretation in the `Model`
    pub fn get_const_interp<T: Ast>(&self, ast: &T) -> Option<T> {
        let func = ast.safe_decl().ok()?;

        let ret = unsafe {
            Z3_model_get_const_interp(self.ctx.z3_ctx.as_ptr(), self.z3_mdl, func.z3_func_decl)
        };
        Some(unsafe { T::wrap(&self.ctx, ret?) })
    }

    /// Returns the interpretation of the given `f` in the `Model`, regardless of whether
    /// `f` is a constant (arity 0) or a function (arity > 0).
    ///
    /// The variant is determined by arity alone: arity-0 declarations always yield
    /// [`Interp::Const`] and others always yield [`Interp::Func`]. An array-sorted
    /// constant may be returned as an "as-array" value such as `(_ as-array k!0)`; this is
    /// still a valid array value (usable with `select` or [`Model::eval`]). Use
    /// [`Model::get_func_interp`] to resolve it to the underlying function table.
    ///
    /// Returns `None` if there is no interpretation in the `Model`. Z3 uses this to mean that
    /// the value of `f` does not matter; [`Model::eval`] with `model_completion` set will
    /// still produce a value for it.
    pub fn get_interp(&self, f: &FuncDecl) -> Option<Interp> {
        if f.arity() == 0 {
            let ret = unsafe {
                Z3_model_get_const_interp(self.ctx.z3_ctx.as_ptr(), self.z3_mdl, f.z3_func_decl)
            }?;
            Some(Interp::Const(unsafe { Dynamic::wrap(&self.ctx, ret) }))
        } else {
            let ret = unsafe {
                Z3_model_get_func_interp(self.ctx.z3_ctx.as_ptr(), self.z3_mdl, f.z3_func_decl)
            }?;
            Some(Interp::Func(unsafe { FuncInterp::wrap(&self.ctx, ret) }))
        }
    }

    /// Returns the function-table interpretation of the given `f` in the `Model`.
    ///
    /// If `f` is an array-sorted constant whose value is an "as-array" alias for another
    /// function declaration (e.g. `(_ as-array k!0)`), the interpretation of that aliased
    /// function is returned. Note that mutating the result (via [`FuncInterp::add_entry`]
    /// or [`FuncInterp::set_else`]) then mutates the aliased function's interpretation.
    ///
    /// Returns `None` if `f` has no interpretation in the `Model`, or if its interpretation
    /// is not a function table (see [`Model::get_interp`] and [`Model::get_const_interp`]
    /// for that case).
    pub fn get_func_interp(&self, f: &FuncDecl) -> Option<FuncInterp> {
        match self.get_interp(f)? {
            Interp::Func(func_interp) => Some(func_interp),
            Interp::Const(value) => {
                let fd = value.as_array()?.as_array_func_decl()?;
                self.get_func_interp(&fd)
            }
        }
    }

    /// Returns `true` if the `Model` assigns an interpretation to `f`, regardless of its
    /// arity.
    pub fn has_interp(&self, f: &FuncDecl) -> bool {
        unsafe { Z3_model_has_interp(self.ctx.z3_ctx.as_ptr(), self.z3_mdl, f.z3_func_decl) }
    }

    /// Assigns `value` as the interpretation of the constant `f` in the `Model`, replacing
    /// any existing interpretation.
    ///
    /// # Panics
    ///
    /// Panics if `f` does not have arity 0, or if the sort of `value` is not the range of `f`.
    pub fn add_const_interp<T: Ast>(&self, f: &FuncDecl, value: &T) {
        assert!(f.ctx.z3_ctx == self.ctx.z3_ctx && value.get_ctx().z3_ctx == self.ctx.z3_ctx);
        assert_eq!(
            f.arity(),
            0,
            "add_const_interp requires an arity-0 FuncDecl"
        );
        assert!(
            value.get_sort() == self.range_sort(f),
            "add_const_interp: value sort does not match the FuncDecl's range"
        );
        unsafe {
            Z3_add_const_interp(
                self.ctx.z3_ctx.as_ptr(),
                self.z3_mdl,
                f.z3_func_decl,
                value.get_z3_ast(),
            );
        }
    }

    /// Creates a new, empty function interpretation for `f` in the `Model` with
    /// `default_value` as its else value, replacing any existing interpretation.
    ///
    /// Entries can be added to the returned [`FuncInterp`] with [`FuncInterp::add_entry`];
    /// changes to it are reflected in the `Model`.
    ///
    /// # Panics
    ///
    /// Panics if `f` has arity 0, or if the sort of `default_value` is not the range of `f`.
    pub fn add_func_interp<T: Ast>(&self, f: &FuncDecl, default_value: &T) -> FuncInterp {
        assert!(
            f.ctx.z3_ctx == self.ctx.z3_ctx && default_value.get_ctx().z3_ctx == self.ctx.z3_ctx
        );
        assert!(
            f.arity() > 0,
            "add_func_interp requires a FuncDecl with arity > 0"
        );
        assert!(
            default_value.get_sort() == self.range_sort(f),
            "add_func_interp: default value sort does not match the FuncDecl's range"
        );
        unsafe {
            FuncInterp::wrap(
                &self.ctx,
                Z3_add_func_interp(
                    self.ctx.z3_ctx.as_ptr(),
                    self.z3_mdl,
                    f.z3_func_decl,
                    default_value.get_z3_ast(),
                )
                .unwrap(),
            )
        }
    }

    fn range_sort(&self, f: &FuncDecl) -> Sort {
        unsafe {
            Sort::wrap(
                &self.ctx,
                Z3_get_range(self.ctx.z3_ctx.as_ptr(), f.z3_func_decl).unwrap(),
            )
        }
    }

    /// Evaluates an expression `ast` in the current model.
    /// When `model_completion` is true it will assign an interpretation for constants and functions that do not have an interpretation in the model.
    /// This function may fail (return [None]) if the argument contains quantifiers or if it is not well-sorted.
    pub fn eval<T>(&self, ast: &T, model_completion: bool) -> Option<T>
    where
        T: Ast,
    {
        let mut tmp: Z3_ast = ast.get_z3_ast();
        let res = {
            unsafe {
                Z3_model_eval(
                    self.ctx.z3_ctx.as_ptr(),
                    self.z3_mdl,
                    ast.get_z3_ast(),
                    model_completion,
                    &mut tmp,
                )
            }
        };
        if res {
            Some(unsafe { T::wrap(&self.ctx, tmp) })
        } else {
            None
        }
    }

    fn len(&self) -> u32 {
        unsafe {
            Z3_model_get_num_consts(self.ctx.z3_ctx.as_ptr(), self.z3_mdl)
                + Z3_model_get_num_funcs(self.ctx.z3_ctx.as_ptr(), self.z3_mdl)
        }
    }

    pub fn iter<'a>(&'a self) -> ModelIter<'a> {
        self.into_iter()
    }

    /// Returns the number of uninterpreted sorts that the model assigns an interpretation to.
    pub fn num_sorts(&self) -> u32 {
        unsafe { Z3_model_get_num_sorts(self.ctx.z3_ctx.as_ptr(), self.z3_mdl) }
    }

    /// Returns the i-th uninterpreted sort that the model assigns an interpretation to,
    /// or `None` if `i >= self.num_sorts()`.
    pub fn get_sort(&self, i: u32) -> Option<Sort> {
        let z3_sort = unsafe { Z3_model_get_sort(self.ctx.z3_ctx.as_ptr(), self.z3_mdl, i) }?;
        Some(unsafe { Sort::wrap(&self.ctx, z3_sort) })
    }

    /// Returns the universe of the given sort (the finite set of values Z3 assigned to it),
    /// or `None` if the sort has no interpretation in the model.
    pub fn get_sort_universe(&self, sort: &Sort) -> Option<AstVector> {
        let z3_av = unsafe {
            Z3_model_get_sort_universe(self.ctx.z3_ctx.as_ptr(), self.z3_mdl, sort.z3_sort)
        }?;
        Some(unsafe { AstVector::wrap(&self.ctx, z3_av) })
    }

    /// Returns an iterator over the uninterpreted sorts the model assigns an interpretation to.
    pub fn sorts(&self) -> SortIter<'_> {
        SortIter {
            model: self,
            idx: 0,
            len: self.num_sorts(),
        }
    }

    /// Returns an iterator over each uninterpreted sort and its universe in the model.
    pub fn sort_universes(&self) -> impl Iterator<Item = (Sort, AstVector)> + '_ {
        self.sorts().filter_map(|s| {
            let u = self.get_sort_universe(&s)?;
            Some((s, u))
        })
    }
}

impl Default for Model {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_model_to_string(self.ctx.z3_ctx.as_ptr(), self.z3_mdl) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{s}"),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl fmt::Debug for Model {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl Drop for Model {
    fn drop(&mut self) {
        unsafe { Z3_model_dec_ref(self.ctx.z3_ctx.as_ptr(), self.z3_mdl) };
    }
}

#[derive(Debug)]
/// <https://z3prover.github.io/api/html/classz3py_1_1_model_ref.html#a7890b7c9bc70cf2a26a343c22d2c8367>
pub struct ModelIter<'a> {
    model: &'a Model,
    idx: u32,
    len: u32,
}

impl<'a> IntoIterator for &'a Model {
    type Item = FuncDecl;
    type IntoIter = ModelIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        ModelIter {
            model: self,
            idx: 0,
            len: self.len(),
        }
    }
}

impl Iterator for ModelIter<'_> {
    type Item = FuncDecl;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.len {
            None
        } else {
            let num_consts = unsafe {
                Z3_model_get_num_consts(self.model.ctx.z3_ctx.as_ptr(), self.model.z3_mdl)
            };
            if self.idx < num_consts {
                let const_decl = unsafe {
                    Z3_model_get_const_decl(
                        self.model.ctx.z3_ctx.as_ptr(),
                        self.model.z3_mdl,
                        self.idx,
                    )
                    .unwrap()
                };
                self.idx += 1;
                Some(unsafe { FuncDecl::wrap(&self.model.ctx, const_decl) })
            } else {
                let func_decl = unsafe {
                    Z3_model_get_func_decl(
                        self.model.ctx.z3_ctx.as_ptr(),
                        self.model.z3_mdl,
                        self.idx - num_consts,
                    )
                    .unwrap()
                };
                self.idx += 1;
                Some(unsafe { FuncDecl::wrap(&self.model.ctx, func_decl) })
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = (self.len - self.idx) as usize;
        (len, Some(len))
    }
}

#[derive(Debug)]
pub struct SortIter<'a> {
    model: &'a Model,
    idx: u32,
    len: u32,
}

impl Iterator for SortIter<'_> {
    type Item = Sort;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.len {
            return None;
        }
        let sort = self.model.get_sort(self.idx)?;
        self.idx += 1;
        Some(sort)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = (self.len - self.idx) as usize;
        (len, Some(len))
    }
}

impl FusedIterator for SortIter<'_> {}
impl ExactSizeIterator for SortIter<'_> {}

unsafe impl Translate for Model {
    fn translate(&self, dest: &Context) -> Model {
        unsafe {
            Model::wrap(
                dest,
                Z3_model_translate(self.ctx.z3_ctx.as_ptr(), self.z3_mdl, dest.z3_ctx.as_ptr())
                    .unwrap(),
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Solver;
    use crate::ast::Bool;

    #[test]
    fn test_unsat() {
        use crate::SatResult;
        let solver = Solver::new();
        solver.assert(Bool::from_bool(false));
        assert_eq!(solver.check(), SatResult::Unsat);
        assert!(solver.get_model().is_none());
    }

    #[test]
    fn test_sort_universes() {
        use crate::SatResult;
        use crate::{Sort, Symbol, ast::Dynamic};

        let s = Sort::uninterpreted(Symbol::String("S".to_string()));
        let x = Dynamic::new_const("x", &s);
        let y = Dynamic::new_const("y", &s);

        let solver = Solver::new();
        solver.assert(x.eq(&y).not());
        assert_eq!(solver.check(), SatResult::Sat);

        let model = solver.get_model().unwrap();

        // Individual access
        assert_eq!(model.num_sorts(), 1);
        let sort = model.get_sort(0).unwrap();
        assert!(model.get_sort(1).is_none());

        let universe = model.get_sort_universe(&sort).unwrap();
        assert!(universe.len() >= 2);

        // Iterator access
        let sorts: Vec<_> = model.sorts().collect();
        assert_eq!(sorts.len(), 1);

        // Convenience iterator
        let pairs: Vec<_> = model.sort_universes().collect();
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].1.len(), universe.len());
    }
}
