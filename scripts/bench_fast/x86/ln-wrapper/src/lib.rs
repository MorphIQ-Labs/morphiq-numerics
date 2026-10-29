#[unsafe(no_mangle)] pub extern "C" fn prod_ln(x:f64)->f64 {morphiq_numerics::fast::elementary::ln(x)}
#[unsafe(no_mangle)] pub unsafe extern "C" fn prod_ln_slice(x:*const f64,y:*mut f64,n:usize) { unsafe {morphiq_numerics::fast::elementary::ln_slice(std::slice::from_raw_parts(x,n),std::slice::from_raw_parts_mut(y,n));} }
#[unsafe(no_mangle)] pub extern "C" fn control_ln(x:f64)->f64 {morphiq_numerics::elementary::ln(x)}
#[unsafe(no_mangle)] pub unsafe extern "C" fn control_ln_slice(x:*const f64,y:*mut f64,n:usize) { unsafe {morphiq_numerics::elementary::ln_slice(std::slice::from_raw_parts(x,n),std::slice::from_raw_parts_mut(y,n));} }
