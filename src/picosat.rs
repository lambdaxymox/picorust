use libc::{c_char, c_int, c_void, c_double, size_t};
use std::ffi::CStr;
use std::str;


const PICOSAT_VERSION: isize = 965;

const PICOSAT_UNKNOWN: isize       = 0;
const PICOSAT_SATISFIABLE: isize   = 10;
const PICOSAT_UNSATISFIABLE: isize = 20;

#[repr(C)]
struct C_PicoSAT {}

extern {
    fn picosat_version()   -> *const c_char;
    fn picosat_config()    -> *const c_char;
    fn picosat_copyright() -> *const c_char;
    fn picosat_init()      -> *mut C_PicoSAT;

    fn picosat_reset(picosat: *mut C_PicoSAT) -> c_void;

    fn picosat_inc_max_var(picosat: *mut C_PicoSAT) -> c_int;

    fn picosat_push(picosat: *mut C_PicoSAT) -> c_int;

    fn picosat_failed_context(picosat: *mut C_PicoSAT, lit: c_int) -> c_int;
    fn picosat_context(picosat: *const C_PicoSAT) -> c_int;
    fn picosat_pop(picosat: *mut C_PicoSAT) -> c_int;
    fn picosat_simplify(picosat: *mut C_PicoSAT) -> c_void;
    fn picosat_adjust(picosat: *mut C_PicoSAT, max_idx: c_int) -> c_void;

    fn picosat_variables(picosat: *const C_PicoSAT) -> c_int;
    fn picosat_added_original_clauses(picosat: *const C_PicoSAT) -> c_int;
    fn picosat_max_bytes_allocated(picosat: *const C_PicoSAT) -> size_t;
    fn picosat_time_stamp() -> c_double;
    fn picosat_stats(picosat: *const C_PicoSAT) -> c_void;
    fn picosat_seconds(picosat: *const C_PicoSAT) -> c_double;
}

pub fn copyright() -> &'static str {
    let c_buf: *const c_char = unsafe { picosat_copyright() };
    let c_str: &CStr = unsafe { CStr::from_ptr(c_buf) };
    let buf: &[u8] = c_str.to_bytes();
    let str_slice: &str = str::from_utf8(buf).unwrap();

    str_slice
}

/// 
/// We cannot access C preprocessor definitions from Rust FFI.
/// See the stackoverflow thread
/// https://stackoverflow.com/questions/21485655/how-do-i-use-c-preprocessor-macros-with-rusts-ffi
///
enum Status {
    Unknown       = PICOSAT_UNKNOWN,
    Satisfiable   = PICOSAT_SATISFIABLE,
    Unsatisfiable = PICOSAT_UNSATISFIABLE,
}

pub struct PicoSAT {
    ptr: Box<C_PicoSAT>,
}

impl PicoSAT {
    fn new(picosat: *mut C_PicoSAT) -> PicoSAT {
        let ptr = unsafe { Box::from_raw(picosat) };

        PicoSAT {
            ptr: ptr,
        }
    }
}

pub fn init() -> PicoSAT {
    unsafe {
        let picosat = picosat_init();

        PicoSAT::new(&mut *picosat)
    }
}

pub fn reset(picosat: &mut PicoSAT) {
    unsafe {
        picosat_reset(&mut *picosat.ptr);
    }
}

pub fn inc_max_var(picosat: &mut PicoSAT) -> i32 {
    unsafe {
        picosat_inc_max_var(&mut *picosat.ptr)
    }
}

pub fn push(picosat: &mut PicoSAT) -> i32 {
    unsafe {
        picosat_push(&mut *picosat.ptr)
    }
}

pub fn failed_context(picosat: &mut PicoSAT, lit: i32) -> i32 {
    unsafe {
        picosat_failed_context(&mut *picosat.ptr, lit)
    }
}

pub fn context(picosat: &PicoSAT) -> i32 {
    unsafe {
        picosat_context(&*picosat.ptr)
    }
}

pub fn pop(picosat: &mut PicoSAT) -> i32 {
    unsafe {
        picosat_pop(&mut *picosat.ptr)
    }
}

pub fn simplify (picosat: &mut PicoSAT) {
    unsafe {
        picosat_simplify(&mut *picosat.ptr);
    }
}

pub fn adjust(picosat: &mut PicoSAT, max_idx: i32) {
    unsafe {
        picosat_adjust(&mut *picosat.ptr, max_idx);
    }
}

pub fn variables(picosat: &PicoSAT) -> i32 {
    unsafe {
        picosat_variables(&*picosat.ptr)
    }
}

pub fn added_original_clauses(picosat: &PicoSAT) -> i32 {
    unsafe {
        picosat_added_original_clauses(&*picosat.ptr)
    }
}

pub fn max_bytes_allocated(picosat: &PicoSAT) -> usize {
    unsafe {
        picosat_max_bytes_allocated(&*picosat.ptr)
    }
}

pub fn time_stamp() -> f64 {
    unsafe {
        picosat_time_stamp()
    }
}

pub fn stats(picosat: &PicoSAT) {
    unsafe {
        picosat_stats(&*picosat.ptr);
    }
}

pub fn seconds(picosat: &PicoSAT) -> f64 {
    unsafe {
        picosat_seconds(&*picosat.ptr)
    }
}
