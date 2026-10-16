from pathlib import Path
import subprocess,os
import sys
root=Path(sys.argv[1]).resolve()
for variant in ['original','before','after']:
 dest=root/variant
 p=dest/'crates/morphiq-numerics/src/lanes/mod.rs'
 text=p.read_text()
 if '// Native measurement wrappers.' not in text:
  text+='\n// Native measurement wrappers.\n'
  for f,kernel in [('ln','crate::ln::lanes::Ln'),('ln_1p','crate::ln::lanes::Ln1p'),('log_norm_cdf','crate::normal_distribution::lanes::Normal<4>')]:
   for backend,token in [('sse2','Sse2'),('avx2','Avx2'),('avx512','Avx512')]:
    name=f'host_{f}_{backend}'
    text+=f'pub fn {name}(xs: &[f64], out: &mut [f64]) {{ let k=morphiq_numerics_arch::{token}::try_new().unwrap(); let done=chunks::<{kernel},_>(k,xs,out); for (o,&x) in out[done..].iter_mut().zip(&xs[done..]) {{ *o=<{kernel} as Kernel>::scalar(x); }} }}\n'
    lib=dest/'crates/morphiq-numerics/src/lib.rs'
    with lib.open('a') as stream:stream.write(f'\npub use lanes::{name};\n')
  p.write_text(text)
 subprocess.run(['cargo','build','--release','--locked','-p','morphiq-numerics','--features','simd,std'],cwd=dest,env=dict(os.environ,CARGO_TARGET_DIR=str(dest/'target'),RUSTFLAGS=''),check=True)
source=Path(__file__).with_name('paired.rs').read_text()
for backend in ['sse2','avx2','avx512']:
 s=source
 for f in ['ln','ln_1p','log_norm_cdf']:
  module='normal' if f=='log_norm_cdf' else 'elementary'
  s=s.replace(f'::{module}::{f}_slice',f'::host_{f}_{backend}')
 p=root/f'{backend}.rs';p.write_text(s)
 cmd=['rustc','-O','--edition=2024',str(p)]
 for v in ['original','before','after']:cmd+=['--extern',f'{v}={root}/{v}/target/release/libnumerics_{v}.rlib','-L',f'dependency={root}/{v}/target/release/deps']
 subprocess.run(cmd+['-o',str(root/backend)],check=True)
