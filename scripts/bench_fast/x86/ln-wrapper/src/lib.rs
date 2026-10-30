#[unsafe(no_mangle)] pub extern "C" fn prod_ln(x:f64)->f64 {morphiq_numerics::fast::elementary::ln(x)}
#[unsafe(no_mangle)] pub unsafe extern "C" fn prod_ln_slice(x:*const f64,y:*mut f64,n:usize) { unsafe {morphiq_numerics::fast::elementary::ln_slice(std::slice::from_raw_parts(x,n),std::slice::from_raw_parts_mut(y,n));} }
#[unsafe(no_mangle)] pub extern "C" fn control_ln(x:f64)->f64 {morphiq_numerics::elementary::ln(x)}
#[unsafe(no_mangle)] pub unsafe extern "C" fn control_ln_slice(x:*const f64,y:*mut f64,n:usize) { unsafe {morphiq_numerics::elementary::ln_slice(std::slice::from_raw_parts(x,n),std::slice::from_raw_parts_mut(y,n));} }
#[unsafe(no_mangle)] pub extern "C" fn prod_ln_exp(x:f64)->f64 {morphiq_numerics::fast::elementary::exp(morphiq_numerics::fast::elementary::ln(x))}
#[unsafe(no_mangle)] pub extern "C" fn control_ln_exp(x:f64)->f64 {morphiq_numerics::elementary::exp(morphiq_numerics::elementary::ln(x))}
#[unsafe(no_mangle)] pub extern "C" fn control_log2(x:f64)->f64 {morphiq_numerics::elementary::log2(x)}
#[unsafe(no_mangle)] pub extern "C" fn control_log10(x:f64)->f64 {morphiq_numerics::elementary::log10(x)}
#[unsafe(no_mangle)] pub extern "C" fn control_ln_1p(x:f64)->f64 {morphiq_numerics::elementary::ln_1p(x)}
#[unsafe(no_mangle)] pub unsafe extern "C" fn control_ln_1p_slice(x:*const f64,y:*mut f64,n:usize) { unsafe {morphiq_numerics::elementary::ln_1p_slice(std::slice::from_raw_parts(x,n),std::slice::from_raw_parts_mut(y,n));} }
