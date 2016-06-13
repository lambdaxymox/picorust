#![allow(dead_code)]
use libc::{c_char, c_int, c_void, c_double, size_t, c_uint, c_ulonglong};
use libc;
use std::ffi::{CStr, CString};
use std::str;
use std::fs::File;
use std::os::unix::io::AsRawFd;


const PICOSAT_VERSION: isize = 965;

const PICOSAT_UNKNOWN: isize       = 0;
const PICOSAT_SATISFIABLE: isize   = 10;
const PICOSAT_UNSATISFIABLE: isize = 20;

const DEFAULT_FILE_MODE: &'static str = "rw";

#[repr(C)]
struct C_PicoSAT {}

pub type PicosatMalloc  = extern fn(*mut c_void, size_t) -> *mut c_void;
pub type PicosatRealloc = extern fn(*mut c_void, *mut c_void, size_t, size_t) -> *mut c_void;
pub type PicosatFree    = extern fn(*mut c_void, *mut c_void, size_t) -> c_void;

extern "C" {
    fn picosat_version()   -> *const c_char;
    fn picosat_config()    -> *const c_char;
    fn picosat_copyright() -> *const c_char;
    fn picosat_init()      -> *mut C_PicoSAT;
    fn picosat_minit(state: *mut c_void, picosat_malloc: PicosatMalloc,
                     picosat_realloc: PicosatRealloc,
                     picosat_free: PicosatFree) -> *mut C_PicoSAT;

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

    fn picosat_set_more_important_lit(picosat: *mut C_PicoSAT, lit: c_int) -> c_void;
    fn picosat_set_less_important_lit(picosat: *mut C_PicoSAT, lit: c_int) -> c_void;

    fn picosat_message(picosat: *mut C_PicoSAT, verbosity_level: c_int, fmt: *const c_char, ...) -> c_void;

    fn picosat_set_seed(picosat: *mut C_PicoSAT, random_number_generator_seed: c_uint) -> c_void;
    fn picosat_enable_trace_generation(picosat: *mut C_PicoSAT) -> c_int;

    fn picosat_set_incremental_rup_file(picosat: *mut C_PicoSAT, file: *const libc::FILE, m: c_int, n: c_int) -> c_void;
    fn picosat_save_original_clauses(picosat: *mut C_PicoSAT) -> c_void;
    fn picosat_set_interrupt(picosat: *mut C_PicoSAT, 
                             external_state: *const c_void,
                             interrupted: extern fn(external_state: *const c_void) -> c_int) -> c_void;

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
    fn picosat_add(picosat: *mut C_PicoSAT, lit: c_int) -> c_int;
    fn picosat_add_arg(picosat: *mut C_PicoSAT, ...) -> c_int;
    fn picosat_add_lits(picosat: *mut C_PicoSAT, lits: *mut c_int) -> c_int;
    fn picosat_print(picosat: *mut C_PicoSAT, file: *mut libc::FILE) -> c_void;
    fn picosat_assume(picosat: *mut C_PicoSAT, lit: c_int) -> c_void;
    fn picosat_add_ado_lit(picosat: *mut C_PicoSAT, lit: c_int) -> c_void;
    fn picosat_sat(picosat: *mut C_PicoSAT, decision_limit: c_int) -> c_int;
    fn picosat_set_propagation_limit(picosat: *mut C_PicoSAT, limit: c_ulonglong) -> c_void;
    fn picosat_res(picosat: *mut C_PicoSAT);
    fn picosat_deref(picosat: *mut C_PicoSAT, lit: c_int) -> c_int;
    fn picosat_deref_toplevel(picosat: *mut C_PicoSAT, lit: c_int) -> c_int;
    fn picosat_deref_partial(picosat: *mut C_PicoSAT, lit: c_int) -> c_int;
    fn picosat_inconsistent(picosat: *mut C_PicoSAT) -> c_int;
    fn picosat_failed_assumption(picosat: *mut C_PicoSAT, lit: c_int) -> c_int;
    fn picosat_failed_assumptions(picosat: *mut C_PicoSAT) -> *const c_int;
    fn picosat_mus_assumptions(picosat: *mut C_PicoSAT, state: *mut c_void,
                               cb: extern fn(*mut c_void, *const c_int) -> c_void, 
                               assumptions: c_int) -> *const c_int;
    fn picosat_maximal_satisfiable_subset_of_assumptions(picosat: *mut C_PicoSAT) -> *const c_int;
    fn picosat_next_maximal_satisfiable_subset_of_assumptions(picosat: *mut C_PicoSAT) -> *const c_int;
    fn picosat_next_minimal_correcting_subset_of_assumptions(picosat: *mut C_PicoSAT) -> *const c_int;

    fn picosat_changed(picosat: *mut C_PicoSAT) -> c_int;
    fn picosat_coreclause(picosat: *mut C_PicoSAT, i: c_int) -> c_int;
    fn picosat_corelit(picosat: *mut C_PicoSAT, lit: c_int) -> c_int;
    fn picosat_write_clausal_core(picosat: *mut C_PicoSAT, core_file: *mut libc::FILE) -> c_void;
    fn picosat_write_compact_trace(picosat: *mut C_PicoSAT, trace_file: *mut libc::FILE) -> c_void;
    fn picosat_write_extended_trace(picosat: *mut C_PicoSAT, trace_file: *mut libc::FILE) -> c_void;
    fn picosat_write_rup_trace(picosat: *mut C_PicoSAT, trace_file: *mut libc::FILE) -> c_void;
    fn picosat_usedlit(picosat: *mut C_PicoSAT, lit: c_int) -> c_int;
    fn picosat_humus(picosat: *mut C_PicoSAT,
                     callback: extern fn(state: *mut c_void, nmcs: c_int, nhumus: c_int) -> c_void,
                     state: *mut c_void) -> *const c_int;
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

pub fn minit(state: *mut c_void, picosat_malloc: PicosatMalloc,
                     picosat_realloc: PicosatRealloc,
                     picosat_free: PicosatFree) -> PicoSAT 
{
    unsafe {
        PicoSAT::new(picosat_minit(state, picosat_malloc, picosat_realloc, picosat_free))
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
        let c_mode = CString::new(DEFAULT_FILE_MODE).unwrap();
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

// TODO: make a messages function?
pub fn message(picosat: &mut PicoSAT, verbosity_level: i32, fmt: &[u8], string: &[u8]) {
    unsafe {
        let c_str = CStr::from_bytes_with_nul_unchecked(fmt);
        let c_fmt = c_str.as_ptr();
        let new_str = CStr::from_bytes_with_nul_unchecked(string);
        let new_ptr = new_str.as_ptr();

        picosat_message(&mut *picosat.ptr, verbosity_level, c_fmt, new_ptr);
    }
}

pub fn set_more_important_lit(picosat: &mut PicoSAT, lit: i32) {
    unsafe {
        picosat_set_more_important_lit(&mut *picosat.ptr, lit);
    }
}

pub fn set_less_important_lit(picosat: &mut PicoSAT, lit: i32) {
    unsafe {
        picosat_set_less_important_lit(&mut *picosat.ptr, lit);
    }
}

pub fn set_seed(picosat: &mut PicoSAT, random_number_generator_seed: u32) {
    unsafe {
        picosat_set_seed(&mut *picosat.ptr, random_number_generator_seed);
    }
}

pub fn enable_trace_generation(picosat: &mut PicoSAT) -> i32 {
    unsafe {
        picosat_enable_trace_generation(&mut *picosat.ptr)
    }
}

pub fn set_incremental_rup_file(picosat: &mut PicoSAT, file: &File, m: i32, n: i32) {
    unsafe {
        let raw_fd = file.as_raw_fd();
        let c_mode = CString::new(DEFAULT_FILE_MODE).unwrap();
        let c_mode_ptr = c_mode.as_ptr();
        let fd = libc::fdopen(raw_fd, c_mode_ptr);

        picosat_set_incremental_rup_file(&mut *picosat.ptr, &*fd, m, n);
    }
}

pub fn save_original_clauses(picosat: &mut PicoSAT) {
    unsafe {
        picosat_save_original_clauses(&mut *picosat.ptr);
    }
}

pub fn set_interrupt(picosat: &mut PicoSAT, 
                     external_state: *const c_void,
                     interrupted: extern fn(external_state: *const c_void) -> i32) 
{
    unsafe {
        picosat_set_interrupt(&mut *picosat.ptr, external_state, interrupted);
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

pub fn add(picosat: &mut PicoSAT, lit: i32) -> i32 {
    unsafe {
        picosat_add(&mut *picosat.ptr, lit)
    }
}

pub fn add_arg(picosat: &mut PicoSAT, clause: &[i32]) -> i32 {
    let mut i = 0;
    loop {
        if i >= clause.len() {
            break;
        }

        let lit = clause[i];

        if lit == 0 {
            break;
        }

        add(picosat, lit);
        i += 1;
    }
    // Terminate the clause in picosat.
    add(picosat, 0)
}

pub fn add_lits(picosat: &mut PicoSAT, lits: &mut [i32]) -> i32 {
    unsafe {
        picosat_add_lits(&mut *picosat.ptr, lits.as_mut_ptr())
    }
}

pub fn print(picosat: &mut PicoSAT, file: &mut File) {
    unsafe {
        let raw_fd = file.as_raw_fd();
        let c_mode = CString::new(DEFAULT_FILE_MODE).unwrap();
        let c_mode_ptr = c_mode.as_ptr();
        let fd = libc::fdopen(raw_fd, c_mode_ptr);

        picosat_print(&mut *picosat.ptr, fd);
    }
}

pub fn assume(picosat: &mut PicoSAT, lit: i32) {
    unsafe {
        picosat_assume(&mut *picosat.ptr, lit);
    }
}

pub fn add_ado_lit(picosat: &mut PicoSAT, lit: i32) {
    unsafe {
        picosat_add_ado_lit(&mut *picosat.ptr, lit);
    }
}

pub fn sat(picosat: &mut PicoSAT, decision_limit: i32) -> i32 {
    unsafe {
        picosat_sat(&mut *picosat.ptr, decision_limit)
    }
}

pub fn set_propagation_limit(picosat: &mut PicoSAT, limit: u64) {
    unsafe {
        picosat_set_propagation_limit(&mut *picosat.ptr, limit);
    }
}

pub fn res(picosat: &mut PicoSAT) {
    unsafe {
        picosat_res(&mut *picosat.ptr);
    }
}

pub fn deref(picosat: &mut PicoSAT, lit: i32) -> i32 {
    unsafe {
        picosat_deref(&mut *picosat.ptr, lit)
    }
}

pub fn deref_toplevel(picosat: &mut PicoSAT, lit: i32) -> i32 {
    unsafe {
        picosat_deref_toplevel(&mut *picosat.ptr, lit)
    }
}

pub fn deref_partial(picosat: &mut PicoSAT, lit: i32) -> i32 {
    unsafe {
        picosat_deref_partial(&mut *picosat.ptr, lit)
    }
}

pub fn inconsistent(picosat: &mut PicoSAT) -> i32 {
    unsafe {
        picosat_inconsistent(&mut *picosat.ptr)
    }
}

pub fn failed_assumption(picosat: &mut PicoSAT, lit: i32) -> i32 {
    unsafe {
        picosat_failed_assumption(&mut *picosat.ptr, lit)
    }
}

unsafe fn zero_terminated_list_to_vec(ptr: *const i32) -> Vec<i32> {
    let mut vec = Vec::new();
    let mut i = 0;

    if ptr.is_null() {
        return vec;
    }

    loop {
        let pti = (ptr as i32 + i) as *const i32;
        vec.push(*pti);

        // Terminate at zero.
        if *pti == 0 {
            break;
        }

        i += 1;
    } 

    vec
}

pub fn failed_assumptions(picosat: &mut PicoSAT) -> Vec<i32> {
    unsafe {
        let failed_assumptions: *const i32 = 
                picosat_failed_assumptions(&mut *picosat.ptr);
        
        zero_terminated_list_to_vec(failed_assumptions)
    }
}

pub fn mus_assumptions(picosat: &mut PicoSAT, state: *mut c_void,
                       cb: extern fn(*mut c_void, *const c_int) -> c_void, 
                       assumptions: i32) -> Vec<i32> 
{
    unsafe {
        let failed_assumptions: *const i32 = 
                picosat_mus_assumptions(&mut *picosat.ptr, state, cb, assumptions);

        zero_terminated_list_to_vec(failed_assumptions)                      
    }
}

pub fn maximal_satisfiable_subset_of_assumptions(picosat: &mut PicoSAT) -> Vec<i32> {
    unsafe {
        let ptr: *const i32 = 
            picosat_maximal_satisfiable_subset_of_assumptions(&mut *picosat.ptr);

        zero_terminated_list_to_vec(ptr)
    }
}

pub fn next_maximal_satisfiable_subset_of_assumptions(picosat: &mut PicoSAT) -> Vec<i32> {
    unsafe {
        let ptr: *const i32 = 
            picosat_next_maximal_satisfiable_subset_of_assumptions(&mut *picosat.ptr);

        zero_terminated_list_to_vec(ptr)
    }
}

pub fn next_minimal_correcting_subset_of_assumptions(picosat: &mut PicoSAT) -> Vec<i32> {
    unsafe {
        let ptr: *const i32 =
            picosat_next_minimal_correcting_subset_of_assumptions(&mut *picosat.ptr);

        zero_terminated_list_to_vec(ptr)
    }
}

// TODO: picosat_humus here

pub fn changed(picosat: &mut PicoSAT) -> i32 {
    unsafe {
        picosat_changed(&mut *picosat.ptr)
    }
}

pub fn coreclause(picosat: &mut PicoSAT, i: c_int) -> i32 {
    unsafe {
        picosat_coreclause(&mut *picosat.ptr, i)
    }
}

pub fn corelit(picosat: &mut PicoSAT, lit: i32) -> i32 {
    unsafe {
        picosat_corelit(&mut *picosat.ptr, lit)
    }
}

pub fn write_clausal_core(picosat: &mut PicoSAT, core_file: &mut File) {
    unsafe {
        let raw_fd = core_file.as_raw_fd();
        let c_mode = CString::new(DEFAULT_FILE_MODE).unwrap();
        let c_mode_ptr = c_mode.as_ptr();
        let core_fd = libc::fdopen(raw_fd, c_mode_ptr);
        
        picosat_write_clausal_core(&mut *picosat.ptr, core_fd);
    }
}

pub fn write_compact_trace(picosat: &mut PicoSAT, trace_file: &mut File) {
    unsafe {
        let raw_fd = trace_file.as_raw_fd();
        let c_mode = CString::new(DEFAULT_FILE_MODE).unwrap();
        let c_mode_ptr = c_mode.as_ptr();
        let trace_fd = libc::fdopen(raw_fd, c_mode_ptr);

        picosat_write_compact_trace(&mut *picosat.ptr, trace_fd);
    }
}

pub fn write_extended_trace(picosat: &mut PicoSAT, trace_file: &mut File) {
    unsafe {
        let raw_fd = trace_file.as_raw_fd();
        let c_mode = CString::new(DEFAULT_FILE_MODE).unwrap();
        let c_mode_ptr = c_mode.as_ptr();
        let trace_fd = libc::fdopen(raw_fd, c_mode_ptr);

        picosat_write_extended_trace(&mut *picosat.ptr, trace_fd);
    }
}

pub fn write_rup_trace(picosat: &mut PicoSAT, trace_file: &mut File) {
    unsafe {
        let raw_fd = trace_file.as_raw_fd();
        let c_mode = CString::new(DEFAULT_FILE_MODE).unwrap();
        let c_mode_ptr = c_mode.as_ptr();
        let trace_fd = libc::fdopen(raw_fd, c_mode_ptr);

        picosat_write_rup_trace(&mut *picosat.ptr, trace_fd);
    }
}

pub fn usedlit(picosat: &mut PicoSAT, lit: i32) -> i32 {
    unsafe {
        picosat_usedlit(&mut *picosat.ptr, lit)
    }
}

pub fn humus(picosat: &mut PicoSAT,
             callback: extern fn(state: *mut c_void, nmcs: i32, nhumus: i32) -> c_void,
             state: *mut c_void) -> Vec<i32>
{
    unsafe {
        let ptr: *const i32 = picosat_humus(&mut *picosat.ptr, callback, state);

        zero_terminated_list_to_vec(ptr)        
    }
}