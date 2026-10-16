# Native x86 cold-dispatch comparison

Intel Core i9-10920X, Rust 1.97.1, CPU 14, performance governor.
Variants are original `76825af`, parent #165 `d14a580`, and #187 `741586b`.
The candidate retains one output buffer through scalar `ln_1p` completion;
returning successive arrays had introduced unnecessary copies on x86.
No numerical operation or rounding decision changes.

The paired executable links three distinct library/arch identities and
rotates their order. Each fixed-seed pool contains 4,096 inputs. Three
processes retain 11 rounds each after warm-up, with samples lasting at least
5 ms: 33 samples per cell. Results are checked bit for bit before timing.
Lengths 2, 8 and 4,096 cover short and long dispatch. The forced-backend
subdirectories repeat the same experiment through SSE2, AVX2 and AVX-512.
Their build script injects measurement-only wrappers around the existing
`chunks` helper and scalar remainder; it does not change kernel arithmetic.

| Dispatch, 4,096 values | Original ns | Parent ns | Candidate ns |
| --- | ---: | ---: | ---: |
| ln common | 7.761 | 3.574 | 3.574 |
| ln near one | 182.683 | 41.625 | 41.891 |
| ln1p exp-negative | 3.924 | 3.928 | 3.922 |
| ln1p huge | 193.458 | 30.165 | 31.997 |
| ln1p screened | 11.478 | 11.911 | 11.365 |
| ln1p mixed | 8.885 | 9.447 | 8.938 |
| log-CDF central | 95.923 | 95.243 | 94.005 |

The reported screened/mixed regression is removed. Forced-backend long
mixed/screened cases and central log-CDF are within about 1% of the original
baseline. SSE2 huge ln1p is 69.00 → 68.38 ns; AVX2 is 282.08 → 45.08 ns;
AVX-512 is 193.79 → 32.64 ns. Small differences do not establish speedups.

`native-sweep/` also retains three independent-process runs of every length
1–17, 32, 64, 256, 4,096 and 65,536 for the selected affected workloads,
including forced backends, dispatch, scalar and dependency chains. Its
0.5 ms samples show substantial between-process noise, including apparent
regressions in unchanged scalar remainder cells. The paired experiments
resolve those observations without treating separate-process timings as
proof of a kernel regression.

Other CI jobs shared this host. Environment and sampled CPU load are
included; CPU 2 is CPU 14's sibling. These are local comparisons under
recorded load, not idle-host or fastest-alternative claims.

Reproduce from the repository root (finish compilation before timing):

```sh
python3 crates/reference/measurements/lanes-cold-dispatch-x86-i9-10920x/build_paired.py target/cold-paired
python3 crates/reference/measurements/lanes-cold-dispatch-x86-i9-10920x/force_backends.py target/cold-paired
for run in 0 1 2; do
  for mode in paired sse2 avx2 avx512; do
    taskset -c 14 target/cold-paired/$mode > "$mode-$run.csv"
  done
done
python3 crates/reference/measurements/lanes-cold-dispatch-x86-i9-10920x/summarize.py target/cold-summary paired-0.csv paired-1.csv paired-2.csv
```

Native release tests and the lane code-generation gate pass. The latter
checks 27 AVX2 and 27 AVX-512 kernels for out-of-line SIMD arithmetic.
