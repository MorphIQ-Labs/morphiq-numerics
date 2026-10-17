from pathlib import Path
import subprocess,tarfile,io,sys,os
repo=Path.cwd();root=Path(sys.argv[1] if len(sys.argv)>1 else 'target/tail-paired').resolve();root.mkdir(parents=True,exist_ok=True)
for name,rev in [('before','2f5ae140'),('after','503a7ea')]:
 dest=root/name;dest.mkdir(exist_ok=True)
 blob=subprocess.check_output(['git','archive',rev],cwd=repo)
 with tarfile.open(fileobj=io.BytesIO(blob)) as tf:tf.extractall(dest,filter='data')
 p=dest/'crates/morphiq-numerics/Cargo.toml';p.write_text(p.read_text()+'\n[lib]\nname = "numerics_'+name+'"\n')
 p=dest/'crates/morphiq-numerics-arch/Cargo.toml';p.write_text(p.read_text().replace('name = "morphiq-numerics-arch"','name = "morphiq-numerics-arch-'+name+'"'))
 p=dest/'crates/morphiq-numerics/Cargo.toml';p.write_text(p.read_text().replace('morphiq-numerics-arch = {','morphiq-numerics-arch = { package = "morphiq-numerics-arch-'+name+'",'))
 p=dest/'Cargo.lock';p.write_text(p.read_text().replace('"morphiq-numerics-arch"','"morphiq-numerics-arch-'+name+'"'))
 subprocess.run(['cargo','build','--release','--locked','-p','morphiq-numerics','--features','simd,std'],cwd=dest,env=dict(os.environ,CARGO_TARGET_DIR=str(dest/"target"),RUSTFLAGS=""),check=True)

subprocess.run(['rustc','-O','-C','target-feature=-fma','--edition=2024',str(Path(__file__).with_name('paired.rs')),'--extern','before='+str(root/'before/target/release/libnumerics_before.rlib'),'--extern','after='+str(root/'after/target/release/libnumerics_after.rlib'),'-L','dependency='+str(root/'before/target/release/deps'),'-L','dependency='+str(root/'after/target/release/deps'),'-o',str(root/'paired')],check=True)
