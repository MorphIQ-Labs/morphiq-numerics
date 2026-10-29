#[unsafe(no_mangle)] pub extern "C" fn prod_exp(x:f64)->f64 {morphiq_numerics::fast::elementary::exp(x)}
#[unsafe(no_mangle)] pub unsafe extern "C" fn prod_exp_slice(x:*const f64,y:*mut f64,n:usize) { unsafe {morphiq_numerics::fast::elementary::exp_slice(std::slice::from_raw_parts(x,n),std::slice::from_raw_parts_mut(y,n));} }
#[unsafe(no_mangle)] pub extern "C" fn prod_erfcx(x:f64)->f64 {morphiq_numerics::fast::normal::erfcx(x)}
#[unsafe(no_mangle)] pub unsafe extern "C" fn prod_erfcx_slice(x:*const f64,y:*mut f64,n:usize) { unsafe {morphiq_numerics::fast::normal::erfcx_slice(std::slice::from_raw_parts(x,n),std::slice::from_raw_parts_mut(y,n));} }
#[unsafe(no_mangle)] pub extern "C" fn prod_norm_cdf(x:f64)->f64 {morphiq_numerics::fast::normal::norm_cdf(x)}
#[unsafe(no_mangle)] pub unsafe extern "C" fn prod_norm_cdf_slice(x:*const f64,y:*mut f64,n:usize) { unsafe {morphiq_numerics::fast::normal::norm_cdf_slice(std::slice::from_raw_parts(x,n),std::slice::from_raw_parts_mut(y,n));} }

#[unsafe(no_mangle)] pub extern "C" fn control_exp(x:f64)->f64 {morphiq_numerics::elementary::exp(x)}
#[unsafe(no_mangle)] pub unsafe extern "C" fn control_exp_slice(x:*const f64,y:*mut f64,n:usize) { unsafe {morphiq_numerics::elementary::exp_slice(std::slice::from_raw_parts(x,n),std::slice::from_raw_parts_mut(y,n));} }

#[unsafe(no_mangle)] pub extern "C" fn control_erfcx(x:f64)->f64 {morphiq_numerics::normal::erfcx(x)}
#[unsafe(no_mangle)] pub unsafe extern "C" fn control_erfcx_slice(x:*const f64,y:*mut f64,n:usize) { unsafe {morphiq_numerics::normal::erfcx_slice(std::slice::from_raw_parts(x,n),std::slice::from_raw_parts_mut(y,n));} }

#[unsafe(no_mangle)] pub extern "C" fn control_norm_cdf(x:f64)->f64 {morphiq_numerics::normal::norm_cdf(x)}
#[unsafe(no_mangle)] pub unsafe extern "C" fn control_norm_cdf_slice(x:*const f64,y:*mut f64,n:usize) { unsafe {morphiq_numerics::normal::norm_cdf_slice(std::slice::from_raw_parts(x,n),std::slice::from_raw_parts_mut(y,n));} }
