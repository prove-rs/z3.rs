use std::cmp::{Eq, PartialEq};
use std::ffi::CString;
use std::fmt;
use std::hash::{Hash, Hasher};
use z3_sys::*;
use Ast;
use Context;
use Sort;
use Symbol;
use Z3_MUTEX;

macro_rules! unop {
    ( $f:ident, $z3fn:ident ) => {
        pub fn $f(&self) -> Ast<'ctx> {
            Ast::new(self.ctx, unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                $z3fn(self.ctx.z3_ctx, self.z3_ast)
            })
    }
    };
}

macro_rules! binop {
    ( $f:ident, $z3fn:ident ) => {
        pub fn $f(&self, other: &Ast<'ctx>) -> Ast<'ctx> {
            Ast::new(self.ctx, unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                $z3fn(self.ctx.z3_ctx, self.z3_ast, other.z3_ast)
            })
    }
    };
}

macro_rules! trinop {
    ( $f:ident, $z3fn:ident ) => {
        pub fn $f(&self, a: &Ast<'ctx>, b: &Ast<'ctx>) -> Ast<'ctx> {
            Ast::new(self.ctx, unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                $z3fn(self.ctx.z3_ctx, self.z3_ast, a.z3_ast, b.z3_ast)
            })
    }
    };
}

macro_rules! varop {
    ( $f:ident, $z3fn:ident ) => {
        pub fn $f(&self, other: &[&Ast<'ctx>]) -> Ast<'ctx> {
            Ast::new(self.ctx, unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let mut tmp = vec![self.z3_ast];
                for a in other {
                    tmp.push(a.z3_ast)
                }
                assert!(tmp.len() <= 0xffff_ffff);
                $z3fn(self.ctx.z3_ctx, tmp.len() as u32, tmp.as_ptr())
            })
    }
    };
}

impl<'ctx> Ast<'ctx> {
    pub fn new(ctx: &Context, ast: Z3_ast) -> Ast {
        assert!(!ast.is_null());
        Ast {
            ctx,
            z3_ast: unsafe {
                debug!("new ast {:p}", ast);
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_inc_ref(ctx.z3_ctx, ast);
                ast
            },
        }
    }

    pub fn new_const(sym: &Symbol<'ctx>, sort: &Sort<'ctx>) -> Ast<'ctx> {
        Ast::new(sym.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_const(sym.ctx.z3_ctx, sym.z3_sym, sort.z3_sort)
        })
    }

    pub fn fresh_const(ctx: &'ctx Context, prefix: &str, sort: &Sort<'ctx>) -> Ast<'ctx> {
        Ast::new(ctx, unsafe {
            let pp = CString::new(prefix).unwrap();
            let p = pp.as_ptr();
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_fresh_const(ctx.z3_ctx, p, sort.z3_sort)
        })
    }

    pub fn from_bool(ctx: &'ctx Context, b: bool) -> Ast<'ctx> {
        Ast::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            if b {
                Z3_mk_true(ctx.z3_ctx)
            } else {
                Z3_mk_false(ctx.z3_ctx)
            }
        })
    }

    pub fn from_i64(ctx: &'ctx Context, i: i64) -> Ast<'ctx> {
        Ast::new(ctx, unsafe {
            let sort = ctx.int_sort();
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_int64(ctx.z3_ctx, i, sort.z3_sort)
        })
    }

    pub fn from_u64(ctx: &'ctx Context, u: u64) -> Ast<'ctx> {
        Ast::new(ctx, unsafe {
            let sort = ctx.int_sort();
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_unsigned_int64(ctx.z3_ctx, u, sort.z3_sort)
        })
    }

    pub fn from_real(ctx: &'ctx Context, num: i32, den: i32) -> Ast<'ctx> {
        Ast::new(ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_real(
                ctx.z3_ctx,
                num as ::std::os::raw::c_int,
                den as ::std::os::raw::c_int,
            )
        })
    }

    pub fn as_bool(&self) -> Option<bool> {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            match Z3_get_bool_value(self.ctx.z3_ctx, self.z3_ast) {
                Z3_L_TRUE => Some(true),
                Z3_L_FALSE => Some(false),
                _ => None,
            }
        }
    }

    pub fn as_i64(&self) -> Option<i64> {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            let mut tmp: ::std::os::raw::c_longlong = 0;
            if Z3_TRUE == Z3_get_numeral_int64(self.ctx.z3_ctx, self.z3_ast, &mut tmp) {
                Some(tmp)
            } else {
                None
            }
        }
    }

    pub fn as_u64(&self) -> Option<u64> {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            let mut tmp: ::std::os::raw::c_ulonglong = 0;
            if Z3_TRUE == Z3_get_numeral_uint64(self.ctx.z3_ctx, self.z3_ast, &mut tmp) {
                Some(tmp)
            } else {
                None
            }
        }
    }

    pub fn as_real(&self) -> Option<(i64, i64)> {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            let mut num: i64 = 0;
            let mut den: i64 = 0;
            if Z3_TRUE == Z3_get_numeral_small(self.ctx.z3_ctx, self.z3_ast, &mut num, &mut den) {
                Some((num, den))
            } else {
                None
            }
        }
    }

    varop!(distinct, Z3_mk_distinct);

    // Boolean ops
    trinop!(ite, Z3_mk_ite);
    binop!(iff, Z3_mk_iff);
    binop!(implies, Z3_mk_implies);
    binop!(xor, Z3_mk_xor);
    varop!(and, Z3_mk_and);
    varop!(or, Z3_mk_or);
    varop!(add, Z3_mk_add);
    varop!(sub, Z3_mk_sub);
    varop!(mul, Z3_mk_mul);
    unop!(not, Z3_mk_not);

    // Numeric ops
    binop!(div, Z3_mk_div);
    binop!(rem, Z3_mk_rem);
    binop!(modulo, Z3_mk_mod);
    binop!(power, Z3_mk_power);
    unop!(minus, Z3_mk_unary_minus);
    binop!(lt, Z3_mk_lt);
    binop!(le, Z3_mk_le);
    binop!(_eq, Z3_mk_eq);
    binop!(ge, Z3_mk_ge);
    binop!(gt, Z3_mk_gt);
    unop!(int2real, Z3_mk_int2real);
    unop!(real2int, Z3_mk_real2int);
    unop!(is_int, Z3_mk_is_int);

    // Bitvector ops
    unop!(bvnot, Z3_mk_bvnot);
    unop!(bvneg, Z3_mk_bvneg);
    unop!(bvredand, Z3_mk_bvredand);
    unop!(bvredor, Z3_mk_bvredor);
    binop!(bvand, Z3_mk_bvand);
    binop!(bvor, Z3_mk_bvor);
    binop!(bvxor, Z3_mk_bvxor);
    binop!(bvnand, Z3_mk_bvnand);
    binop!(bvnor, Z3_mk_bvnor);
    binop!(bvxnor, Z3_mk_bvxnor);
    binop!(bvadd, Z3_mk_bvadd);
    binop!(bvsub, Z3_mk_bvsub);
    binop!(bvmul, Z3_mk_bvmul);
    binop!(bvudiv, Z3_mk_bvudiv);
    binop!(bvsdiv, Z3_mk_bvsdiv);
    binop!(bvurem, Z3_mk_bvurem);
    binop!(bvsrem, Z3_mk_bvsrem);
    binop!(bvsmod, Z3_mk_bvsmod);
    binop!(bvult, Z3_mk_bvult);
    binop!(bvslt, Z3_mk_bvslt);
    binop!(bvule, Z3_mk_bvule);
    binop!(bvsle, Z3_mk_bvsle);
    binop!(bvuge, Z3_mk_bvuge);
    binop!(bvsge, Z3_mk_bvsge);
    binop!(bvugt, Z3_mk_bvugt);
    binop!(bvsgt, Z3_mk_bvsgt);
    binop!(concat, Z3_mk_concat);
    binop!(bvshl, Z3_mk_bvshl);
    binop!(bvlshr, Z3_mk_bvlshr);
    binop!(bvashr, Z3_mk_bvashr);

    // Array ops
    binop!(select, Z3_mk_select);
    trinop!(store, Z3_mk_store);

    // Set ops
    binop!(set_add, Z3_mk_set_add);
    binop!(set_del, Z3_mk_set_del);
    varop!(set_union, Z3_mk_set_union);
    varop!(set_intersect, Z3_mk_set_intersect);
    binop!(set_member, Z3_mk_set_member);
    binop!(set_subset, Z3_mk_set_subset);
    unop!(set_complement, Z3_mk_set_complement);
}

impl<'ctx> fmt::Display for Ast<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p =
            unsafe { CString::from_raw(Z3_ast_to_string(self.ctx.z3_ctx, self.z3_ast) as *mut i8) };
        if p.as_ptr().is_null() {
            return Result::Err(fmt::Error);
        }
        match p.into_string() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => return Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> Drop for Ast<'ctx> {
    fn drop(&mut self) {
        unsafe {
            debug!("drop ast {:p}", self.z3_ast);
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_dec_ref(self.ctx.z3_ctx, self.z3_ast);
        }
    }
}

impl<'ctx> Hash for Ast<'ctx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        unsafe {
            let u = Z3_get_ast_hash(self.ctx.z3_ctx, self.z3_ast);
            u.hash(state);
        }
    }
}

impl<'ctx> PartialEq<Ast<'ctx>> for Ast<'ctx> {
    fn eq(&self, other: &Ast<'ctx>) -> bool {
        unsafe { Z3_TRUE == Z3_is_eq_ast(self.ctx.z3_ctx, self.z3_ast, other.z3_ast) }
    }
}

impl<'ctx> Eq for Ast<'ctx> {}
