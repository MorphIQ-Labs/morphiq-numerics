use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
struct Observed;
static ENABLED: AtomicBool = AtomicBool::new(false);
static ALLOCS: AtomicU64 = AtomicU64::new(0);
unsafe impl GlobalAlloc for Observed {
    unsafe fn alloc(&self,l:Layout)->*mut u8 {if ENABLED.load(Ordering::Relaxed){ALLOCS.fetch_add(1,Ordering::Relaxed);} unsafe{System.alloc(l)}}
    unsafe fn dealloc(&self,p:*mut u8,l:Layout){unsafe{System.dealloc(p,l)}}
    unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8 {if ENABLED.load(Ordering::Relaxed){ALLOCS.fetch_add(1,Ordering::Relaxed);}unsafe{System.realloc(p,l,n)}}
    unsafe fn alloc_zeroed(&self,l:Layout)->*mut u8 {if ENABLED.load(Ordering::Relaxed){ALLOCS.fetch_add(1,Ordering::Relaxed);}unsafe{System.alloc_zeroed(l)}}
}
#[global_allocator] static OBSERVED:Observed=Observed;
#[unsafe(no_mangle)] pub extern "C" fn strong_exp(x:f64)->f64 {morphiq_numerics::elementary::exp(x)}
#[unsafe(no_mangle)] pub extern "C" fn strong_erfcx(x:f64)->f64 {morphiq_numerics::normal::erfcx(x)}
#[unsafe(no_mangle)] pub extern "C" fn strong_cdf(x:f64)->f64 {morphiq_numerics::normal::norm_cdf(x)}
/// The caller owns valid, disjoint input/output arrays of n elements; mode is 0..3.
#[unsafe(no_mangle)] pub unsafe extern "C" fn observe_allocations(mode:u32,x:*const f64,y:*mut f64,n:usize)->u64 {
    let xs=unsafe{std::slice::from_raw_parts(x,n)};let ys=unsafe{std::slice::from_raw_parts_mut(y,n)};
    ALLOCS.store(0,Ordering::Relaxed);ENABLED.store(true,Ordering::Relaxed);
    match mode {0=>morphiq_numerics::fast::elementary::exp_slice(xs,ys),1=>morphiq_numerics::fast::normal::erfcx_slice(xs,ys),2=>morphiq_numerics::fast::normal::norm_cdf_slice(xs,ys),_=>{}}
    ENABLED.store(false,Ordering::Relaxed);ALLOCS.load(Ordering::Relaxed)
}
