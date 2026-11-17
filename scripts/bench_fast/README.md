# Native fast primitive benchmarks

This is the reusable methodology from #194/#240: public scalar and slice calls
for exp, erfcx and normal CDF, same-host pinned references, independent accuracy
observations, unchanged controls, and separate diagnostics. It preserves the
ARM and x86 campaign harnesses as source instead of keeping generated runs in
Git. Results and landing decisions belong in the owning issue/PR.

## Native hosts and dependencies

Use an otherwise idle Apple Silicon Mac for `arm-macos`, or native x86-64 Linux
with SSE2, AVX2/FMA and AVX-512F for the full `x86-linux` matrix. Do not emulate
an ISA or compare timings from different hosts. Record CPU model/ISA, OS, power
mode, thermal/frequency state, affinity and competing load. Keep those settings
consistent across runs; declare any difference. Do not kill unrelated work.

Use the repository's pinned Rust toolchain, a C compiler, CMake and Ninja. Record
`rustc -Vv`, `cc --version`, `cmake --version`, Python version and `pip freeze`
with the run. Python dependencies are pinned in `requirements.txt`:

```sh
python3 -m venv target/bench-fast-venv
. target/bench-fast-venv/bin/activate
python -m pip install -r scripts/bench_fast/requirements.txt
```

Build the following references separately under `target/bench-fast-refs`.
They are black-box comparators, not library dependencies or vendored kernels.
Keep their license notices with the local builds.

| Reference | Repository | Exact revision |
| --- | --- | --- |
| CORE-MATH | https://gitlab.inria.fr/core-math/core-math.git | `c7100a07428584639defdd64409e3621884c362b` |
| SLEEF 3.9.0 | https://github.com/shibatch/sleef.git | `906ca7512ee483296780a81a21b9ca715d40dfe1` |
| libcerf | https://jugit.fz-juelich.de/mlz/lib/cerf.git | `7e6b637031b5c6cbc89a5f7220bf4ef07518d035` |

Clone each repository into `core-math`, `sleef`, or `libcerf` inside that directory,
then check out its exact revision. From `target/bench-fast-refs`, build:

```sh
mkdir -p bin
cmake -S sleef -B sleef-build -G Ninja -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_SHARED_LIBS=ON -DCMAKE_POSITION_INDEPENDENT_CODE=ON \
  -DSLEEF_BUILD_TESTS=OFF -DSLEEF_BUILD_SCALAR_LIB=ON \
  -DSLEEF_BUILD_GNUABI_LIBS=OFF -DSLEEF_ENABLE_TLFLOAT=OFF
cmake --build sleef-build -j4
cmake -S libcerf -B cerf-build -G Ninja -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_SHARED_LIBS=ON -DCMAKE_POSITION_INDEPENDENT_CODE=ON \
  -DBUILD_TESTING=OFF -DLIB_MAN=OFF -DLIB_RUN=OFF -DCERF_CPP=OFF
cmake --build cerf-build --target cerf -j2
```

On macOS, build CORE-MATH with:

```sh
cc -O3 -fPIC -dynamiclib -mcpu=apple-m1 -frounding-math -ffp-contract=off \
  core-math/src/binary64/exp/exp.c -o bin/libcoreexp.dylib
```

On Linux, use:

```sh
cc -O3 -fPIC -shared -frounding-math -ffp-contract=off \
  core-math/src/binary64/exp/exp.c -lm -o bin/libcoreexp.so
```

Copy the built SLEEF and libcerf shared libraries (including their versioned
symlinks) into `bin/`. The Mac harness expects `libsleef.3.9.0.dylib`,
`libsleef.3.dylib`, `libcerf.3.1.dylib`; Linux expects `libsleef.so.3`,
`libsleef.so`, `libcerf.so`. Keep dependent shared libraries resolvable by the
native loader. Do not silently substitute another reference revision.

## Prepare and observe

From a clean committed repository checkout, use a fresh output directory under
`target/`. Preparation compiles only the standalone benchmark wrappers and
native timers; it does not run repository CI or a benchmark campaign.

ARM:

```sh
python scripts/bench_fast/prepare.py --platform arm-macos \
  --out target/bench-fast-arm \
  --reference-bin target/bench-fast-refs/bin \
  --sleef-include target/bench-fast-refs/sleef-build/include
python target/bench-fast-arm/observe.py
python target/bench-fast-arm/observe-references.py
python target/bench-fast-arm/diagnostics.py
```

x86 (replace `/path/to/clean-baseline` with a clean checkout of the declared
control revision, which must expose the same wrapper APIs; record that SHA):

```sh
python scripts/bench_fast/prepare.py --platform x86-linux \
  --out target/bench-fast-x86 --reference-bin target/bench-fast-refs/bin \
  --control-source /path/to/clean-baseline --cpu 2
python target/bench-fast-x86/observe.py
```

Select an allowed CPU with an idle SMT sibling. `prepare.py` builds separate
SSE2, AVX2, AVX-512 and runtime-dispatch products with explicit feature flags;
`commands.json` records the build commands. Inspect generated manifests and
observations before timing. Independent mpmath observations and scalar/slice
identity must pass. Sampled accuracy does not prove a whole-domain bound;
existing certificates, fixtures and CI remain the correctness authority.
The ARM diagnostics report allocations, fallback identity and compositions
outside the timed loops. x86 observations cover generated banks and controls;
use the repository's existing allocation/code-generation checks separately.

## Freeze, measure, decide

The generators create exact binary64 banks from recipes, including ordinary,
boundary, tail, mixed and fallback-heavy cases, short/remainder slices,
dependency latency and composition/control workloads. ARM declares 163 cells
(125 parity-required); x86 declares 500 (430 parity-required). Review any change
to that matrix before collecting results.

Record host/tool versions and baseline SHA in a text file in the run directory,
then freeze the source, harness, generated inputs and reference binaries:

```sh
python scripts/bench_fast/freeze.py target/bench-fast-arm
python target/bench-fast-arm/run-qualified.py
python scripts/bench_fast/freeze.py target/bench-fast-arm --verify
```

For x86 replace the directory with `target/bench-fast-x86` and use
`run-qualification.py`. Do not modify frozen files between these steps.
Verify hashes again after any post-timing diagnostics.

Every x86 cell process, calibration included, places its buffers identically:
the input on a page boundary and the output 2 KiB modulo 4 KiB past the input's
end. Allocator state otherwise differs between processes, and a short slice's
speed depends on the output's 4 KiB offset from its input (store-to-load
aliasing; up to 1.8x on Sapphire Rapids, #243). Each process records the
placement in its metadata. The ARM harness allocates in native code and has not
yet been given a declared placement.

Calibration uses only the current host, not counts from a previous run. It
retains every pilot, targets 600 ms per timed sample, and only increases counts.
Every accepted timed sample must be at least 250 ms. Each cell has ten independent
processes, two paired rounds per process, alternating comparison order and
warmups. Keep all measurements, including failures. Do not trim outliers or
retry until passing. An interrupted/invalid attempt remains recorded; investigate
and predeclare a new complete run when needed.

The decision uses per-process paired log ratios and a one-sided 95% Student-t
upper bound (9 degrees of freedom, critical value 1.8331129326536335). Every
required cell must have an upper ratio at most 1.0 and valid durations. Report
spread and drift alongside the decision. Diagnostic cells do not establish
parity; missing or failing required cells leave qualification incomplete.
ARM writes `qualification-summary.json`; x86 writes `qualification/result.json`
and summary JSON/CSV. No timing claim is established by running CI.

Keep profiles outside timing: use macOS `sample` on a dedicated cell process or
Linux `perf record` around a separate cell invocation, with its profile outputs
under `target/`. Record wrapper/library sizes and exported symbols with the
platform's `size`/`nm` tools. Profiling runs never replace uninstrumented samples.

## Review a measured hotspot

Use this checklist when investigating an optimization; record findings in the
owning numerical decision/PR. The engineering requirements live in
[`AGENTS.md`](../../AGENTS.md#hotspot-optimization-review).

1. Identify the hot call and its share of consumer runtime from a profile.
   Set a stopping condition before investigating alternatives.
2. Inspect the exact compiled wrapper and caller used by the workload, including
   inlined code. Record source revision, compiler, target features, optimization
   and LTO flags, symbol/caller and disassembly command. Use the platform's
   disassembler on the built binary; check dependency chains, widened arithmetic,
   constant loads, spills and scalar/SIMD dispatch. Keep generated assembly under
   `target/`, and preserve its reproduction commands in the review.
3. Look for established constants and bounded indices that permit work to move
   out of the runtime path. Derive the specialized expression and establish its
   rounding, overflow and boundary behavior before substitution. Test the
   transitions and domain extremes against an independent reference. Preserve
   the existing behavior for inputs outside the specialized domain.
4. Measure independent throughput and dependent latency separately where both
   affect the consumer, on native ARM and x86 as applicable. Inspect the emitted
   dependency chain to ensure the compiler has not removed the intended
   dependency. Qualify the real consumer before choosing between conflicting
   microbenchmark winners. Assembly inspection explains measurements; it does
   not replace them.
5. Apply an exact-result improvement to existing APIs whose full contracts it
   preserves. Qualify affected strong and fast call sites. Add target-specific
   variants only when their measured value warrants the maintenance cost.

Ben Joffe's [constant signed floor-division study](https://www.benjoffe.com/fast-floordiv)
illustrates compiler-sensitive formulations and differing throughput/latency
winners. It is a methodological reference, not evidence of a speedup in this
library. In particular, inspect existing power-of-two reductions before assuming
that a general constant-division technique improves them. Consumer timestamp or
fixed-point operations warrant investigation only when profiling identifies cost.

## Retention and scope

Commit recipes, comparator pins, harness source, acceptance rules and changes to
them. Keep raw samples, logs, host snapshots, built libraries and profiles in
ignored `target/` or temporary review artifacts, available until review ends.
Record source/host, conclusions, failed attempts and limitations in the issue/PR.
Permanent raw data retention is optional; do not add generated archives to Git.
Historical records remain in Git history. This policy does not remove correctness
fixtures, worst-case witnesses, mathematical proof inputs or certified constants.
Reproduction means regenerating a comparable experiment, not identical timings.

## Focused logarithm comparison

The `x86/prepare-ln.py` adapter uses the same timers, calibration and
ten-process paired runner for three explicit cells: scalar throughput,
dependent latency, and the automatic 52-value slice. Inputs are exact
binary64 values formed by `.5 + 1.5*i/51`, `i=0..51`. The references are
the pinned SLEEF scalar FMA u10 log and AVX-512 u10 log with scalar remainders.
Each cell requires an upper 95% paired ratio at most one; all samples and
failed cells remain recorded. This scoped comparison does not establish
the broader ln workload/backend/ARM or consumer qualification.

From a clean committed candidate on native x86 with AVX-512F and FMA:

```sh
python scripts/bench_fast/x86/prepare-ln.py --cpu 2 \
  --reference-bin target/bench-fast-refs/bin --out target/ln-ordinary-001
```

Before timing, run the independent `fast_ln` reference tests, inspect
`objdump -d -C --disassemble=prod_ln` on the generated wrapper library,
record host conditions, and finish all builds/proofs/oracle work. The
manifest records the input, product and reference binary hashes and source
revision; preserve the pinned reference build receipt too. Freeze and run:

```sh
python scripts/bench_fast/freeze.py target/ln-ordinary-001
python target/ln-ordinary-001/run-qualification.py
python scripts/bench_fast/freeze.py target/ln-ordinary-001 --verify
```

Use a new output directory for every changed candidate. The adapter keeps
its ln wrapper separate from the historical matrix's control wrapper, so
building pre-ln strong controls does not require a nonexistent fast API.

## Full logarithm matrix

`x86/prepare-ln.py --full` also prepares the ln campaign on native x86 Linux
or Apple Silicon macOS. The shared timer and runner support both; the directory
name is historical. Supply the clean control checkout at the declared baseline,
and build pinned CORE-MATH's `src/binary64/log/log.c` with the same command above,
substituting `log/log.c` and `libcorelog.so` (or `.dylib`). On x86 the reference
build may use `-march=native`; record it in the reference receipt. Keep the
SLEEF reference build receipt and exact binary hashes with the run.

```sh
python scripts/bench_fast/x86/prepare-ln.py --full --platform x86-linux \
  --control-source /path/to/clean-baseline --cpu 2 \
  --reference-bin target/bench-fast-refs/bin --out target/ln-full-001
python target/ln-full-001/observe-ln.py
```

On Apple Silicon substitute `--platform arm-macos` and add
`--sleef-include target/bench-fast-refs/sleef-build/include`. macOS records the
power configuration and uses USER_INITIATED QoS; it cannot pin this process to
a CPU. Record the actual core scheduling, thermal/power conditions and competing
load with the returned run. An x86 result does not fill an ARM cell.

The versioned `x86/ln-matrix.py` declares 394 x86 cells (244 parity-required)
and 142 ARM cells (94 required). It covers automatic dispatch plus x86 builds
with a static SSE2, AVX2/FMA or AVX-512 ceiling; public wrappers can select a
narrower width on short inputs. Ordinary and exponent-spanning inputs cover
lengths 0–17 and large batches, with additional automatic-dispatch boundaries.
Every build covers near-one cancellation, subnormals, reduction/table boundaries,
and mixed positive packets at lengths 52 and 4096. Scalar throughput and dependent
latency compare against SLEEF u10 and correctly rounded CORE-MATH. SLEEF u10 is a
selected diagnostic accuracy reference with a looser worst-case guarantee than
the mixed ln bound; observations report its error against that bound without
claiming equal guarantees. NaN-payload differences make special/mixed-special
comparisons diagnostic, with no parity claim. Strong ln, log2, log10 and ln_1p before/after controls
are separately reviewed, never silently treated as accepted regressions.

The exact input banks, their hashes and all cell settings are emitted before
measurement. Independent observations check the public mixed bound, exact
`ln(1)=+0`, existing special semantics, every timed slice/remainder against
scalar bits, and shared strong paths against the baseline. CORE-MATH scalar
outputs are checked for nearest-even equality to the high-precision observation.
The reference uncertainty allowance is reported separately from observed error;
these observations supplement the existing proofs and independent fixtures.

The synthetic `exp(ln(x))` composition uses positive normal inputs with binary
exponents from -900 to 900. If `d = 2^-53*|ln(x)| + 2^-65`, its relative error
bound is `expm1(d)*(1+2^-51) + 2^-51`, using the fast exp bound on this range.
It has separate scalar throughput/latency cells and strong composition controls.
It does not qualify a consumer's distinct composed error or workload budget.

Use `screen-ln.py` before qualification for a one-process exploratory screen:
150 ms calibration target, two alternating paired rounds, all samples retained.
It never establishes parity. Stop tuning a candidate when a required cell misses
materially, investigate the measured cost, and retain that attempt. No repeated
unchanged-candidate runs to obtain a favorable result. Finish all builds,
observations, code inspection and allocation/profile diagnostics before timing.

Freeze and run `run-qualification.py` with the same ten-process, two-block,
600 ms protocol above. Every required cell must meet the upper-95% ratio rule;
there is no aggregation across cells. This matrix stops on its first completed
required failure and records incomplete qualification explicitly. Preserve the
entire failed attempt before changing source or predeclaring another campaign.

On native Linux, observe the same final ln binaries for heap allocations before
freezing/timing, using gperftools heap hooks (record the installed version and
library hash). This reuses the public-call probe from the native fast campaign:

```sh
cc -O2 -fPIC -shared scripts/bench_fast/x86/allocation-probe.c \
  -o target/ln-full-001/bin/allocation-probe.so
LD_PRELOAD=/path/to/libtcmalloc.so.4 \
  python scripts/bench_fast/x86/observe-ln-allocations.py \
  target/ln-full-001 target/ln-full-001/bin/allocation-probe.so
```

The probe checks scalar/slice calls for every built backend over ordinary,
wide, near-one, subnormal and mixed populations at lengths 1, 9, 52 and 4096.
It verifies output bits against the uninstrumented scalar entry and requires a
71-byte positive allocation control. Retain the raw heap profiles and summary;
this instrumentation is separate from timing and does not establish macOS
allocation behavior. The published crates' no-alloc dependency boundary remains
the structural guarantee on every platform.


The ln x86 matrix declares two execution groups before qualification. The
first contains the observed short-call/bulk boundary cases and scalar
CORE-MATH comparisons near parity; the second contains every remaining cell.
Each group completes two full blocks of five fresh processes per cell, with
the same 600 ms calibration target, 250 ms minimum sample, paired order and
confidence rule. The runner rejects missing, duplicated or unknown cell IDs.
A required failure stops the entire campaign. Staging changes execution order
only: acceptance still requires all 394 cells measured and all 244 required
cells passing. Native ARM and manifests without groups retain the original
single-group schedule.

## Far-tail CDF change qualification

`prepare-cdf-far.py` builds candidate and pre-change baseline CDF wrappers with
matching flags and stages the existing paired timer. On x86 it builds automatic
dispatch (`simd,std`, `x86-64-v3`), static AVX2/FMA (`simd`, `x86-64-v3`) and
static AVX-512 (`simd`, `x86-64-v4`). Apple Silicon uses `simd,std` and NEON.
Run on native hardware; CPU affinity is available on Linux, while the Mac timer
requests user-initiated QoS. Record Mac power mode and thermal/load conditions.
On each host, run `cargo test --workspace --all-features --locked` and
`./scripts/check_fma.sh` before timing. Finish these checks and the linked-product
oracle observations before starting any performance process.

On x86 hosts affected by Intel's JCC microcode mitigation, code placement can
change decoded-cache usage even when instruction sequences match. Inspect the
actual caller and use hardware counters outside timing to investigate this.
`--x86-jcc-mitigation` stages a separate diagnostic build with LLVM's
`--x86-branches-within-32B-boundaries` flag on candidate, baseline and composition
products alike. Retain default-build results separately; this option does not
establish their performance or change the acceptance rule. See
[Intel's JCC guidance](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/best-practices/mitigation-strategies-jcc-microcode.html).

```sh
git worktree add --detach target/cdf-far-baseline f29d59b
python3 scripts/bench_fast/prepare-cdf-far.py --cpu 2 \
  --baseline target/cdf-far-baseline --out target/cdf-far-001
python scripts/bench_fast/observe-cdf-far.py target/cdf-far-001  # pinned mpmath environment
python3 target/cdf-far-001/screen-ln.py --limit 63  # 21 priority cells per x86 build
```

The shared screen retains its historical filename; it reads the staged matrix.
Use `--limit 21` for the single Mac/NEON build. A screen is exploratory: one
process, two alternating paired rounds, 150 ms calibration target. Investigate
material costs before qualification; retain every attempt. Build and validate
before timing, with no concurrent profiling or oracle work on the timed host.

Each backend has 120 required before/after cells: twelve banks, scalar throughput
and dependent latency on 52 values, and slice lengths 1/2/4/8/13/52/53/4096.
Banks cover negative far tails, two signed mixtures, the positive-tail control, unchanged
pricing/body/lower/upper/wide domains, seam neighbours, mixed near/far/fallback
lanes and previously all-fallback packets. The seam bank includes the generated positive
saturation threshold and both neighbours. Exact input words, hashes, strong-call
fallback counts and exact endpoint counts are retained; the historical
`positive_fallback` bank name remains for before/after comparison. Exact endpoint
completion retains the strong result and does not extend the approximation domain. Nine consumer-composition comparisons and three unchanged strong
controls are diagnostics. The composition has an unsplit exponent and a weaker
error guarantee; it cannot establish comparable-contract parity. The independent
fixture check and exact-bit observations run outside timing on the linked products.
Its separate cost/spread rule in the far-tail decision record still requires
review; classifying it as a diagnostic does not waive that acceptance obligation.

Before qualification, record the matrix, pinned baseline, host and decision in
the owning issue/PR, and commit methodology/source changes. Then use `freeze.py`,
the staged `run-qualification.py`, and `freeze.py --verify` as above. Every
required cell must pass the shared ten-process upper-95% ratio rule; the runner
stops at its first completed required failure. Review strong controls separately.
Qualification completes seven regression-sensitive cells per backend first:
positive-tail scalar throughput, dependent latency and 4096-value slices;
pricing scalar and 8-value slices; body scalar; and lower-domain latency.
That group uses the same two blocks of five processes before the remaining
cells. The groups partition the complete matrix; no cell or acceptance rule
is removed. This exposes a required failure without first timing every bank.
This focused change matrix does not replace the broader competitor matrix or
consumer end-to-end qualification. Native x86 results leave ARM cells open.
Remove the clean baseline worktree after the comparison; retain linked binaries,
raw samples, failed attempts and logs under ignored `target/` through review.

### Canonical CDF references

`build-cdf-references.py` builds QuantLib 1.44 at revision
`ab4cb476d35f7275834bc05b47d1324403d1823b`, Boost.Math 1.86.0 with both its
default policy and `promote_double<false>`, and the pinned SLEEF 3.9.0 `erfc_u15`
composition. It fetches QuantLib's compatible license before its selected
sources. Supply the pinned Boost headers and SLEEF source/build; used headers,
licenses, compiler commands and linked products are hashed in `references.json`.
The supplied Boost tree is identified by its used headers; the manifest does
not claim verification against the published archive unless it was performed.

QuantLib and Boost use scalar loops for slices. SLEEF uses AVX-512, AVX2 or NEON
with scalar remainders. The SLEEF composition is
`0.5 * erfc(x * -RN(1/sqrt(2)))`; an `erfc` ULP claim does not establish a CDF
relative bound after argument rounding. Boost's internal promotion policy also
does not recover precision already lost in the distribution's argument scaling.
The C adapters catch C++ domain exceptions, count them, and return NaN; the
accuracy record reports these adaptations and special-value results explicitly.

```sh
python3 scripts/bench_fast/build-cdf-references.py --out target/cdf-references-001 \
  --boost /path/to/boost_1_86_0 --sleef-source target/bench-fast-refs/sleef \
  --sleef-build target/bench-fast-refs/sleef-build
python scripts/bench_fast/observe-cdf-references.py --run target/cdf-far-001 \
  --references target/cdf-references-001  # pinned mpmath environment
python3 scripts/bench_fast/stage-cdf-references.py --run target/cdf-far-001 \
  --references target/cdf-references-001 --out target/cdf-canonical-001
python3 target/cdf-canonical-001/screen-ln.py
```

The observer checks the complete CDF against mpmath at 200/400 bits on the
existing exact input banks and independent CDF fixture inputs. It records
absolute and negative normal-output relative maxima, exact witnesses, scalar
versus slice differences, and exceptional results. These are observations, not
proofs of reference bounds. The staged cells compare independent scalar
throughput, dependent latency, and 4096-value slices on the negative far tail
and unchanged pricing domain. They are separate diagnostics; baseline controls,
comparable-contract acceptance, native ARM and consumer qualification retain
their requirements. Finish all builds, oracles and profiles before timing.

## Focused log-CDF comparison

The `x86/prepare-log-cdf.py` adapter times the bounded `log_norm_cdf`
against Risk's own `log_norm_cdf` (Cody rational erfcx with the platform
logarithm), built from a pinned `morphiq-risk-rs` checkout as a C-ABI library
with the same symbol names, so the runner's `--reference-product` path pairs
the two in one process. Three 52-value populations, exact values off the
dyadic grid: ordinary `[-3, 3]`, wide `[-8, 8]` and negative tail `[-22, -8]`,
each with scalar throughput, dependent latency and the automatic slice (Risk
has no log-CDF slice: its packet entry is the scalar loop it would run), plus
the unchanged strong `normal::log_norm_cdf` slice as a drift control. The
native timers are compiled with `-DNO_SLEEF`; `qualify-cell.py` also offers
SciPy `log_ndtr` (`--reference scipy_log_ndtr`) as a diagnostic. The manifest
records both source revisions, whether the Risk checkout was dirty, and the
product and reference library hashes.

```sh
python scripts/bench_fast/x86/prepare-log-cdf.py --cpu 2 \
  --risk ../morphiq-risk-rs --out target/issue-192/logcdf-001
python scripts/bench_fast/freeze.py target/issue-192/logcdf-001
python target/issue-192/logcdf-001/run-qualification.py
python scripts/bench_fast/freeze.py target/issue-192/logcdf-001 --verify
```

The same host, duration, pairing and retention rules apply. This scoped
comparison does not establish the broader #192 workload/length/ARM matrix,
mixed or fallback-heavy banks, or consumer qualification.

## Focused Linux exp latency comparison

`x86/prepare-exp-latency.py` runs on native x86-64 or AArch64 Linux. It
stages the existing paired runner around already
built C-ABI wrappers exporting `prod_exp`, `prod_exp_slice`, `prod_norm_cdf_slice`
and `control_exp`. Build baseline and candidate with the same release profile
(thin LTO, one codegen unit, `simd,std`, no ambient Rust flags), using the
`x86/matrix-wrapper/src/lib.rs` adapter and `prepare.py` build procedure.
Keep the baseline binary before rebuilding the candidate. To time
`fast::elementary::exp_coarse` against `exp` from one source tree, build the
candidate from a copy of the adapter whose `prod_exp` and `prod_exp_slice` call
`exp_coarse` and `exp_coarse_slice`, and the baseline from the unmodified
adapter. Supply the existing
`native-matrix.c` and `native-cache.c` shared timers and pinned CORE-MATH/SLEEF
binaries. `glibc_exp` resolves the system libm through its public ABI; no glibc
source is needed. Record the distribution's glibc version and libm binary hash
alongside the comparator build receipts.

```sh
python scripts/bench_fast/x86/prepare-exp-latency.py \
  --out target/exp-latency-001 --cpu 3 \
  --product /path/to/candidate.so --baseline /path/to/baseline.so \
  --native /path/to/native-matrix.so --native-cache /path/to/native-cache.so \
  --core-math /path/to/libcoreexp.so --sleef /path/to/libsleef.so.3
python scripts/bench_fast/freeze.py target/exp-latency-001
python target/exp-latency-001/run-qualification.py
python scripts/bench_fast/freeze.py target/exp-latency-001 --verify
```

Finish builds, proofs and oracle checks before timing. Twenty-two cells separate
dependent latency, scalar throughput, slice lengths 1/8/52/53/4096, mixed
fallback packets, wide inputs and unchanged CDF/strong-exp controls. Three
latency cells must independently improve against the baseline under the shared
ten-process confidence rule. Other cells are regression/comparator diagnostics;
a successful required-cell result alone is not competitor or release acceptance.
Review throughput and controls separately. Discount/density inputs are declared
synthetic pricing-domain banks, not captured consumer frequencies. Report each measured architecture separately; one host cannot establish speed
on another. This adapter does not establish an end-to-end pricing/IV budget.

On AArch64 Linux, compile both Rust wrappers natively with the same manifest
profile and `simd,std`; the slice entry selects NEON. Build pinned SLEEF 3.9
with its scalar library enabled, GNUABI and tests disabled, and CORE-MATH
with `-O3 -fPIC -shared -march=native -frounding-math -ffp-contract=off`.
The shared timer is portable: compile `x86/native-matrix.c` with
`-O3 -fPIC -shared -ffp-contract=off -I/path/to/sleef/include`, link that
host’s `libsleef.so.3`, and give the loader its library directory. Compile
`x86/native-cache.c` with `-O3 -fPIC -shared`. Pass those native binaries
to the same adapter. Before timing, run the release reference suite and the
fast scalar/slice tests on that host, including its determinism digest.
Retain OS/glibc, CPU, compiler and binary hashes; Linux/ARM measurements do
not establish macOS/Apple-libm performance.
