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

## Retention and scope

Commit recipes, comparator pins, harness source, acceptance rules and changes to
them. Keep raw samples, logs, host snapshots, built libraries and profiles in
ignored `target/` or temporary review artifacts, available until review ends.
Record source/host, conclusions, failed attempts and limitations in the issue/PR.
Permanent raw data retention is optional; do not add generated archives to Git.
Historical records remain in Git history. This policy does not remove correctness
fixtures, worst-case witnesses, mathematical proof inputs or certified constants.
Reproduction means regenerating a comparable experiment, not identical timings.
