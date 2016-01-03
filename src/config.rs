use z3_sys::*;
use Config;
use Z3_MUTEX;
use std::ffi::CString;

impl Config {
    pub fn new() -> Config {
        Config {
            kvs: Vec::new(),
            z3_cfg: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let p = Z3_mk_config();
                debug!("new config {:p}", p);
                p
            }
        }
    }
    pub fn set_param_value(&mut self, k: &str, v: &str) {
        let ks = CString::new(k).unwrap();
        let vs = CString::new(v).unwrap();
        self.kvs.push((ks, vs));
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_set_param_value(self.z3_cfg,
                               self.kvs.last().unwrap().0.as_ptr(),
                               self.kvs.last().unwrap().1.as_ptr());
        }
    }

    pub fn set_bool_param_value(&mut self, k: &str, v: bool) {
        self.set_param_value(k, if v { "true" } else { "false" });
    }

    // Helpers for common parameters
    pub fn set_proof_generation(&mut self, b: bool)
    {
        self.set_bool_param_value("proof", b);
    }

    pub fn set_model_generation(&mut self, b: bool)
    {
        self.set_bool_param_value("model", b);
    }

    pub fn set_debug_ref_count(&mut self, b: bool)
    {
        self.set_bool_param_value("debug_ref_count", b);
    }

    pub fn set_timeout_msec(&mut self, ms: u64)
    {
        self.set_param_value("timeout", &format!("{}", ms));
    }
}

impl Drop for Config {
    fn drop(&mut self) {
        unsafe {
            debug!("drop config {:p}", self.z3_cfg);
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_del_config(self.z3_cfg);
        }
    }
}
