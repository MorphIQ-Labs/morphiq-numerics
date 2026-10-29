# Native x86 matrix, 28 October 2026

Measured source: `fe6af5609433ed9fa5d383e816c4c6f856fcbd3b`. All 500 declared cases completed; 430/430 individually required parity cases pass the predeclared one-sided 95% upper paired-time-ratio criterion of <=1.0. The historical 3% absolute-spread gate is retired. No samples are deleted and no average across cases hides a loss.

The raw-data audit checks 20,000 timed samples, frozen counts, alternating order, source/input/binary identities and CPU-2 affinity. The shortest timed sample is 271.015 ms; 0 are below the 250 ms minimum. CPU 14, the SMT sibling, has recorded busy ticks in 0 process windows. The host is an Intel i9-10920X on Fedora 44; performance governor and turbo are enabled. Other-core Anvil CI activity is recorded and owner-authorized. All experiment builds, proofs, accuracy observations and profiling run outside uninstrumented timing windows.

Each row below reports the worst upper ratio among its required cases. Ratios below one favor Numerics. The full per-case results, raw samples and descriptive spread are retained in the archives.

| Build | Primitive | Required cases | Failed | Worst upper ratio |
| --- | --- | ---: | ---: | ---: |
| auto | cdf | 72 | 0 | 0.996412 |
| auto | erfcx | 36 | 0 | 0.950670 |
| auto | exp | 76 | 0 | 0.977459 |
| avx2 | cdf | 40 | 0 | 0.535036 |
| avx2 | erfcx | 2 | 0 | 0.718489 |
| avx2 | exp | 40 | 0 | 0.855085 |
| avx512 | cdf | 40 | 0 | 0.891939 |
| avx512 | erfcx | 2 | 0 | 0.711739 |
| avx512 | exp | 40 | 0 | 0.938642 |
| sse2 | cdf | 40 | 0 | 0.157975 |
| sse2 | erfcx | 2 | 0 | 0.708239 |
| sse2 | exp | 40 | 0 | 0.597466 |

Selected ordinary 52-value calls through the automatic build:

| Primitive/interface | Reference | Median ns/call (ours / reference) | Paired geometric mean ratio | Upper 95% ratio |
| --- | --- | ---: | ---: | ---: |
| exp/vector | sleef_exp_avx512 | 58.371 / 84.165 | 0.688360 | 0.698535 |
| erfcx/vector | libcerf_erfcx | 274.916 / 397.137 | 0.691765 | 0.699580 |
| cdf/vector | sleef_cdf_avx512 | 419.365 / 753.716 | 0.559924 | 0.566002 |
| exp/scalar | core_math_exp | 165.071 / 339.075 | 0.486370 | 0.489059 |
| exp/latency | core_math_exp | 692.987 / 840.719 | 0.824724 | 0.828151 |
| exp/scalar | sleef_exp_scalar_fma | 162.117 / 300.609 | 0.539038 | 0.541636 |
| exp/latency | sleef_exp_scalar_fma | 687.843 / 877.871 | 0.781168 | 0.788488 |
| erfcx/scalar | libcerf_erfcx | 279.449 / 387.326 | 0.719619 | 0.723019 |
| erfcx/latency | libcerf_erfcx | 906.890 / 1385.695 | 0.653941 | 0.654743 |
| cdf/scalar | scipy_ndtr | 411.817 / 558.421 | 0.756412 | 0.781489 |
| cdf/latency | scipy_ndtr | 1074.797 / 1183.712 | 0.901561 | 0.914532 |

The independent medians are descriptive. The decision uses paired log ratios; dividing those medians is not the reported statistic. The ordinary erfcx bank includes zero, which invokes the strong owner, so its rows are diagnostic. Dependency-chain calls include the same two floating-point dependency operations for both implementations.

Unchanged strong-API controls compare against the retained `5aa5d4a` binary:

| Control | Paired geometric mean ratio | Lower / upper one-sided 95% endpoints |
| --- | ---: | ---: |
| auto-exp-scalar-strong-control-ordinary-52 | 1.003337 | 0.999142 / 1.007550 |
| auto-exp-scalar-strong-control-ordinary-4096 | 0.995942 | 0.990632 / 1.001280 |
| auto-exp-vector-strong-control-ordinary-52 | 1.007097 | 1.003830 / 1.010374 |
| auto-exp-vector-strong-control-ordinary-4096 | 1.006088 | 1.004015 / 1.008165 |
| auto-erfcx-scalar-strong-control-ordinary-52 | 0.999718 | 0.996026 / 1.003424 |
| auto-erfcx-scalar-strong-control-ordinary-4096 | 0.994964 | 0.992831 / 0.997102 |
| auto-erfcx-vector-strong-control-ordinary-52 | 0.998670 | 0.991940 / 1.005445 |
| auto-erfcx-vector-strong-control-ordinary-4096 | 1.000775 | 0.988062 / 1.013651 |
| auto-cdf-scalar-strong-control-ordinary-52 | 1.000180 | 0.999140 / 1.001221 |
| auto-cdf-scalar-strong-control-ordinary-4096 | 0.999563 | 0.998879 / 1.000248 |
| auto-cdf-vector-strong-control-ordinary-52 | 1.000997 | 0.988869 / 1.013274 |
| auto-cdf-vector-strong-control-ordinary-4096 | 1.001169 | 0.986102 / 1.016466 |

Controls and screened/strong-fallback populations are diagnostic comparisons; they are not weaker-contract parity gates for the strong owners. Their complete timings and intervals are in `qualification-final-audit.json`. Screen/fallback counts are recorded per exact input bank in the manifest; these adversarial populations do not claim to represent consumer frequencies.

The source revision, complete runtime source hashes, four binary hashes, harness
hashes and exact-input banks are in `qualification-v8-manifest.json`. Production
builds use Rust 1.97.1, release optimization, thin LTO and one codegen unit.
Build logs and `qualification-v8-builds.json` record every feature/target flag.
Automatic dispatch uses simd+std; static SSE2/AVX2/AVX-512 builds use simd without
runtime detection. These settings change speed, never the selected API's bits.
The control binary is the retained 5aa5d4a build with identical public wrappers.

The predeclared matrix has 500 cells, 430 requiring individual comparable-contract
parity. There are ten fresh processes per cell. The original 500-cell campaign has
two complete blocks of five processes. Its static AVX-512 eight/nine-value exp
cases failed three confidence decisions. After the dispatch fix, all 84 cells
for that changed binary have two fresh 84-cell blocks of five processes. The
other 416 cells reuse their full original measurements: their final-source
release binaries are byte-for-byte identical, as independently rebuilt and
recorded in `qualification-v8-binary-reuse.json`. The original failed campaign
is retained in full; final per-cell selection is in `qualification-final/`. Every process takes two paired rounds, alternating
order. Counts are frozen after excluded calibration targeting 350 ms, with an
excluded half-count warmup before each timed sample. Every timed sample must
last at least 250 ms. All raw samples, process metadata, calibration and warmups
are retained. Invalid attempts are not retried automatically or mixed into a
valid campaign. No outliers are removed. Absolute spread is descriptive; the
owner retired the historical 3% absolute-spread gate.

Per process, take the median of its two paired log-time ratios. Across the ten
processes, exponentiate the mean and the one-sided 95% Student-t upper endpoint
(t9=1.8331129326536335). Each required upper ratio must be <=1.0. This is a
cellwise decision with local host/workload scope, not a simultaneous 95% family
confidence assertion or a claim of globally optimal performance. No average
across cells hides a loss. Zero-length dispatch, screened/fallback populations
and unchanged strong controls are reported separately from comparable fast
contract parity.

The hardware references remain pinned: CORE-MATH
c7100a07428584639defdd64409e3621884c362b, SLEEF 3.9.0
906ca7512ee483296780a81a21b9ca715d40dfe1, libcerf 3.3
7e6b637031b5c6cbc89a5f7220bf4ef07518d035, SciPy 1.16.3 / NumPy 2.3.4.
mpmath 1.3.0 provides the independent 256-bit observations; worst witnesses
are recalculated at 512 bits. Rounded-oracle observations are not interval
certificates or whole-domain proofs. Product bounds are separately proved in
Coq/Gappa and bound to source.

`qualification-observations/` covers all exact timed banks. Final-binary output identity is recorded in `qualification-v8-identity/`; its 5,518,032 checks connect these observations to the four final binary hashes. Each backend's
public scalar and slice values are compared bitwise to automatic scalar values,
including NaN payloads, signed zeros, fallback inputs and every remainder length.
Strong scalar/slice outputs are compared to the retained unchanged control.
`cubic-proof-result.json` identifies the focused entry/assumption receipts;
full oracle, extraction, determinism and assurance checks remain GitHub CI.

The native C timer measures calls through equal opaque function pointers and
writes the same output buffers. Allocations occur before timing. Wrapper/FFI
and loop overhead is included symmetrically, not subtracted. Public automatic
slice measurements include dispatch and remainder costs; static builds isolate
backend selection. Scalar references run their scalar public loop. CDF SIMD
references evaluate 0.5*erfc(-x/sqrt(2)) in the declared binary64 operation order.
Dependency-chain measurements preserve an output dependency through
(previous-previous)+input; the retained timer disassembly shows the subtraction,
addition and indirect call. These two extra operations are included equally.

The rotating-buffer cells use identical 52-value packets and output storage at
128 slots (106,496 bytes) and 4096 slots (3,407,872 bytes), exceeding private
32 KiB L1d and 1 MiB L2 respectively. They measure cache-capacity pressure from
input/output traversal, not adversarial eviction of a specific coefficient
line. Common buffer-indexing overhead is included. The ordinary/wide 65,536-value
cells separately measure large streaming calls. No cache flushing or PMU
instrumentation occurs inside the uninstrumented qualification campaign.

Public fast slice kernels perform one input traversal and one output traversal;
coefficient reads are additional, and mixed screened packets can reread their
small packet before scalar fallback. CDF fuses its exp/erfcx composition without
materializing intermediate arrays. The SLEEF CDF wrapper also fuses its arithmetic
into one traversal. Consumer-specific compositions, derivatives, inverses and
end-to-end pricing remain separate qualification obligations.

`qualification-v8-auto-allocations/` and `qualification-v8-static-allocations/`
use installed gperftools 2.18.1 heap profiling,
not a custom allocator. The profiler starts inside the native probe after
loading libraries and allocating input/output buffers, includes the first call
and 10,000 subsequent calls, dumps, then stops before Python resumes. Its
positive control detects one 71-byte allocation and free; all 90 final-binary public
scalar/slice ordinary/mixed/fallback populations have zero allocation events.
This includes 8-, 9-, 10- and 52-value static calls and 52-value automatic calls.
Earlier allocation scripts loaded the earlier cubic auto binary; those records
are retained as historical observations, not final-binary allocation evidence.
The library's no_std/dependency boundary independently excludes an allocator.
The profiler uses a substituted allocator only for this observation, never for
timing. Documentation: https://github.com/gperftools/gperftools/blob/master/docs/heapprofile.adoc
Two failed attempts to load the unavailable native glibc malloc-debug library
are preserved; they establish no allocation result.

The scalar-load gather, exponent prebias, normal reconstruction and CDF domain
ownership fixes apply to both scalar and lane arithmetic where relevant.
The new constrained cubic uses the same operation sequence in each backend.
The 1024-entry high table costs 8 KiB rather than the prior 4 KiB. `qualification-v8-footprints/` confirms one shared copy in each linked binary; its per-kernel text sizes exclude unattributable inlined/shared callees. Static AVX packet kernels are outlined to avoid dispatcher register-save costs. Fixed-packet validation starts with the first vector mask, removing a redundant all-true comparison and mask operation without changing domain selection. The cubic
saves two multiplications and one addition; it preserves u(0)=0 and the public
relative 4u error budget. `docs/fast.md` gives its independent minimax derivation,
whole-domain certificates and finite-work fallback contract. Allocation, PMU
profiles, code/table footprints and oracle work are all outside timing windows.

These measurements establish x86 performance only. ARM correctness in CI cannot establish native ARM speed; the native ARM protocol and release/adoption obligations are recorded in #194.

The reference test uses 7,058 independent high/low fixtures evaluated at 600 and 1000 bits, with uncertainty `abs(high)*2^-104 + 2^-1074`. Exact integer comparisons keep this uncertainty separate from the public bound. `ci-rounded-oracle-witness.json` retains the valid near-bound input that the former half-ULP reference estimate could not resolve; `high-low-oracle-observations.json` records all final-binary observations. The expected digest is `e454da537b20b961babd4309b52febf346a4b5afbadf79366d4b819eba78198b`.

The final static dispatch routes one-vector SSE2/AVX2/AVX-512 packets and short scalar remainders directly to fixed-size entries before bulk dispatch. This removes the bulk register saves, variable-length remainder setup and packet-selection cost without changing arithmetic. The originally proposed output/table alias explanation was not confirmed by the retained controlled address sweeps and hardware counters; it is not presented as the root cause. The predeclared follow-up and all candidate screens remain retained.


The unchanged strong exp slice controls show paired increases of 0.710% (52 values,
95% endpoints +0.383% to +1.037%) and 0.609% (4096 values, +0.402% to +0.816%).
These small measured increases are retained, not called noise or hidden behind a
3% allowance. Review against the retained control found no changes to the strong
exp algorithm, reduction, fallback, table or lane arithmetic; the architecture
change removes a gather override used only by bounded exp. The own-code review
in `strong-control-code-review.json` finds unchanged opcode counts for the scalar
entry, fallback, AVX2/AVX-512 lane loops and public wrappers. This excludes added
instruction work in those reviewed functions, not all microarchitectural causes.
Binary layout and placement differ; their causal contribution is unestablished.
The review accepts the measured sub-percent control cost for this fast-API change,
with unchanged strong numerical behavior and no identified additional algorithmic
work. It makes no universal no-slowdown claim and creates no general tolerance.

`native-shim-reconstruction.json` records reproducible C timer build commands:
GCC 16.2.1, `-O3 -fPIC -shared -ffp-contract=off`, linking the matrix shim to the
pinned SLEEF library with its recorded runpath, and no additional library for the
cache shim. Rebuilding these commands after timing produces the exact measured
ELF hashes. An initial reconstruction with unnecessary `-lm` produced a different
dynamic-dependency table and is retained as a failed reconstruction attempt;
removing it reproduces the original matrix binary exactly.


The unchanged numerical arithmetic passed all 30 GitHub checks at predecessor `a8cc587`, including [the full CI run](https://github.com/MorphIQ-Labs/morphiq-numerics/actions/runs/40794501939). Full-source checks for the final dispatch and evidence revision are attached to [PR #240](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/240/checks). Evidence-only commits after the measured revision do not change its runtime. The owning qualification and native ARM handoff remain in [#194](https://github.com/MorphIQ-Labs/morphiq-numerics/issues/194).

`qualification.tar.gz` retains the final campaign, exact inputs, observations, executed harness/build scripts, source and binary hashes, CI/proof receipts, reference pins/notices and host records. `diagnostics.tar.gz` retains rejected candidates, pilots, exploratory screens and their raw measurements; it also contains historical footprint measurements. Final footprints are in the qualification archive. These historical attempts are not substitutes for the final qualification. Both archives contain a `SHA256SUMS` and binary inventory. No external implementation source, executable or build directory is bundled. `archives.json` binds the compressed artifacts.

The executed scripts retain their original absolute paths. To reproduce, rebuild the pinned public libraries and the four wrapper variants, relocate those paths explicitly, verify exact input hashes, and freeze a new manifest and counts on the new native host. Do not overwrite this campaign or expect byte-identical binaries after path/toolchain changes. The x86 wrappers need explicit NEON/platform adaptation for the separate ARM campaign described in #194.
