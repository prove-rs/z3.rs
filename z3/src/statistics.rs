use std::ffi::CStr;
use std::fmt;

use z3_sys::*;
use Context;
use Statistics;
use Z3_MUTEX;

/// The value for a key in [`Statistics`].
///
/// # See also:
///
/// - [`StatisticsEntry`]
/// - [`Statistics::value`]
#[derive(Clone, Debug)]
pub enum StatisticsValue {
    UInt(u32),
    Double(f64),
}

/// A key, value entry within [`Statistics`].
///
/// # See also:
///
/// - [`Statistics::entries`]
#[derive(Clone, Debug)]
pub struct StatisticsEntry {
    pub key: String,
    pub value: StatisticsValue,
}

impl<'ctx> Statistics<'ctx> {
    /// Wrap a raw [`Z3_stats`], managing refcounts.
    pub(crate) unsafe fn wrap(ctx: &'ctx Context, z3_stats: Z3_stats) -> Statistics<'ctx> {
        Z3_stats_inc_ref(ctx.z3_ctx, z3_stats);
        Statistics { ctx, z3_stats }
    }

    /// Get the statistics value at the given index.
    ///
    /// # Safety:
    ///
    /// This assumes that `idx` is a valid index.
    unsafe fn value_at_idx(&self, idx: u32) -> StatisticsValue {
        if Z3_stats_is_uint(self.ctx.z3_ctx, self.z3_stats, idx) {
            StatisticsValue::UInt(Z3_stats_get_uint_value(self.ctx.z3_ctx, self.z3_stats, idx))
        } else {
            StatisticsValue::Double(Z3_stats_get_double_value(
                self.ctx.z3_ctx,
                self.z3_stats,
                idx,
            ))
        }
    }

    /// Get the statistics value for the given `key`.
    pub fn value(&self, key: &str) -> Option<StatisticsValue> {
        unsafe {
            let size = Z3_stats_size(self.ctx.z3_ctx, self.z3_stats);
            for idx in 0..size {
                let k = CStr::from_ptr(Z3_stats_get_key(self.ctx.z3_ctx, self.z3_stats, idx));
                if k.to_str().unwrap() == key {
                    return Some(self.value_at_idx(idx));
                }
            }
            None
        }
    }

    /// Iterate over all of the entries in this set of statistics.
    pub fn entries(&self) -> impl Iterator<Item = StatisticsEntry> + '_ {
        let p = unsafe { Z3_stats_size(self.ctx.z3_ctx, self.z3_stats) };
        (0..p).into_iter().map(move |n| unsafe {
            let t = Z3_stats_get_key(self.ctx.z3_ctx, self.z3_stats, n);
            StatisticsEntry {
                key: CStr::from_ptr(t).to_str().unwrap().to_owned(),
                value: self.value_at_idx(n),
            }
        })
    }
}

impl<'ctx> Clone for Statistics<'ctx> {
    fn clone(&self) -> Self {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Self::wrap(self.ctx, self.z3_stats) }
    }
}

impl<'ctx> fmt::Display for Statistics<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "<z3.stats>")
    }
}

impl<'ctx> fmt::Debug for Statistics<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let mut s = f.debug_struct("Statistics");
        for e in self.entries() {
            match e.value {
                StatisticsValue::UInt(v) => s.field(&e.key, &v),
                StatisticsValue::Double(v) => s.field(&e.key, &v),
            };
        }
        s.finish()
    }
}

impl<'ctx> Drop for Statistics<'ctx> {
    fn drop(&mut self) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            Z3_stats_dec_ref(self.ctx.z3_ctx, self.z3_stats);
        }
    }
}
