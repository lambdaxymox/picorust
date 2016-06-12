use libc::{c_char, c_int, c_void, c_double, size_t, c_uint};
use libc;
use std::ffi::{CStr, CString};
use std::str;
use std::fs::File;
use std::os::unix::io::AsRawFd;


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

    fn picosat_set_output(picosat: *mut C_PicoSAT, file: *mut libc::FILE) -> c_void;

    fn picosat_measure_all_calls(picosat: *const C_PicoSAT) -> c_void;

    fn picosat_set_prefix(picosat: *mut C_PicoSAT, prefix: *const c_char) -> c_void;
    fn picosat_set_verbosity(picosat: *mut C_PicoSAT, new_verbosity_level: c_int) -> c_void;
    fn picosat_set_plain(picosat: *mut C_PicoSAT, new_plain_value: c_int) -> c_void;
    fn picosat_set_global_default_phase(picosat: *mut C_PicoSAT, phase: c_int) -> c_void;
    fn picosat_set_default_phase_lit(picosat: *mut C_PicoSAT, lit: c_int, phase: c_int) -> c_void;
    fn picosat_reset_phases(picosat: *mut C_PicoSAT) -> c_void;
    fn picosat_reset_scores(picosat: *mut C_PicoSAT) -> c_void;
    fn picosat_remove_learned(picosat: *mut C_PicoSAT, percentage: c_uint) -> c_void;

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
} // end C function FFI declarations.

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

pub fn set_output(picosat: &mut PicoSAT, file: &mut File) {
    unsafe {
        let fd = file.as_raw_fd();
        let c_mode = CString::new("rw").unwrap();
        let c_mode_ptr = c_mode.as_ptr();
        let c_file = libc::fdopen(fd, c_mode_ptr);

        picosat_set_output(&mut *picosat.ptr, c_file);
    }
}

pub fn measure_all_calls(picosat: &PicoSAT) {
    unsafe {
        picosat_measure_all_calls(&*picosat.ptr);
    }
}

pub fn set_prefix(picosat: &mut PicoSAT, prefix: &[u8]) {
    unsafe {
        let c_prefix = CStr::from_bytes_with_nul_unchecked(prefix);
        let c_ptr    = c_prefix.as_ptr();

        picosat_set_prefix(&mut *picosat.ptr, c_ptr);
    }
}

pub fn set_verbosity(picosat: &mut PicoSAT, new_verbosity_level: i32) {
    unsafe {
        picosat_set_verbosity(&mut *picosat.ptr, new_verbosity_level);
    }
}

pub fn set_plain(picosat: &mut PicoSAT, new_plain_value: i32) {
    unsafe {
        picosat_set_plain(&mut *picosat.ptr, new_plain_value);
    }
}

pub fn set_global_default_phase(picosat: &mut PicoSAT, phase: i32) {
    unsafe {
        picosat_set_global_default_phase(&mut *picosat.ptr, phase);
    }
}

pub fn set_default_phase_lit(picosat: &mut PicoSAT, lit: i32, phase: i32) {
    unsafe {
        picosat_set_default_phase_lit(&mut *picosat.ptr, lit, phase);
    }
}

pub fn reset_phases(picosat: &mut PicoSAT) {
    unsafe {
        picosat_reset_phases(&mut *picosat.ptr);
    }
}

pub fn remove_learned(picosat: &mut PicoSAT, percentage: u32) {
    unsafe {
        picosat_remove_learned(&mut *picosat.ptr, percentage);
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
