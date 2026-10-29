# Reusable native comparison campaigns

This controller bootstraps and runs the existing `bench_fast` matrix, or declared
subsets of it, on native x86 Linux or
Apple Silicon macOS. It records pinned canonical references, candidate/control
commits, commands, host conditions, raw attempts, comparisons and checksums.
Python 3.11 or newer is required. It adds no Rust dependencies and changes no
numerical implementation, timing loop, statistical rule or numerical contract.

This is the Numerics workload adapter for the shared benchmarking program.
The canonical program and shared GCP cost tooling are owned by
[ai-program](https://gitlab.com/prophetizo/morphiq-labs/org/ai-program/-/blob/925c77178941ec86bdfe5eb13c4c666890b46ce6/BENCHMARKING.md), with provider implementation tracked in
[ai-program #17](https://gitlab.com/prophetizo/morphiq-labs/org/ai-program/-/issues/17).
That private repository is optional organizational tooling: these public native
runners and their correctness evidence remain independently usable.
[Architecture](../../docs/adr/0001-native-benchmark-campaigns.md) records the
adapter boundary; [#245](https://github.com/MorphIQ-Labs/morphiq-numerics/issues/245)
tracks Numerics adoption. Provisioning, fresh-VM bootstrap, verified upload and
teardown are not implemented here. GCP ARM Linux cannot run the macOS harness.

## Canonical comparisons

| Participant | Pin | Timed interface | Interpretation |
| --- | --- | --- | --- |
| CORE-MATH | `c7100a07428584639defdd64409e3621884c362b` | Native scalar `cr_exp` | Correct rounding is a stronger guarantee than the fast exp bound. |
| SLEEF 3.9.0 | `906ca7512ee483296780a81a21b9ca715d40dfe1` | Scalar FMA exp; SSE2/AVX2/AVX-512 or NEON exp and composed CDF packets | Selected u10 exp/u15 erfc; composition does not inherit an unproved bound automatically. |
| libcerf | `7e6b637031b5c6cbc89a5f7220bf4ef07518d035` | Scalar `erfcx`, including scalar-in-a-batch | Whole-domain proved equivalence is not established by this harness. |
| SciPy 1.16.3 | Installed distribution files hashed | Native Cython `ndtr` capsule, not a Python call loop | Whole-domain proved equivalence and cross-target determinism are not established here. |

The matrix's domains, populations, scalar/slice interfaces and backends travel
with each result. `references.json` describes the reference contracts and
special-value limitations; the native runner defines exact symbols and flags.
Reference accuracy observations are separate from product proofs. These are
black-box comparison tools; their numerical source is not copied into the
library. Preserve licenses alongside the local reference builds.

The current matrix covers **fast** exp, erfcx and normal CDF versus canonical
references. x86 also has unchanged strong-path baseline controls. It does not
supply a complete strong-versus-canonical matrix for all primitives, or a general
fast-before/after comparison. Adding those workloads requires explicit cells and
acceptance rules; this controller must not relabel existing cells as coverage.

## Prepare the host and reference lock

Use a clean committed checkout containing these scripts. Follow
[the native runner instructions](../bench_fast/README.md) to install the pinned
Rust/Python/C toolchain and build reference libraries under ignored `target/`.
Keep a command log with the actual source checkout, compiler version, CMake
options and compiler flags for every reference. The lock checks clean reference
checkout SHAs and hashes libraries and that log; it does not attest that an
arbitrary binary was built from the declared source. Review the build log.

For x86, from the repository root and the pinned Python environment:

```sh
python scripts/bench_campaign/campaign.py lock-references \
  --platform x86-linux \
  --reference-bin target/bench-fast-refs/bin \
  --core-math-source target/bench-fast-refs/core-math \
  --sleef-source target/bench-fast-refs/sleef \
  --libcerf-source target/bench-fast-refs/libcerf \
  --build-log target/bench-fast-refs/build-commands.log \
  --out target/bench-fast-refs/lock.json
```

The lock includes SciPy/NumPy/mpmath version and installed-file identities;
changing the Python environment invalidates it. Re-locking or running never
overwrites an existing attempt. Resolve changed dependencies explicitly.

Record power mode, frequency/thermal observations, background load, CPU/SMT
sibling availability and unavailable telemetry in `target/host-notes.txt`.
The full x86 runner requires SSE2, AVX2/FMA and AVX-512F. Select an allowed CPU
with an idle sibling; no controller kills unrelated work or reserves a host.
The controller captures system/tool versions and process snapshots outside the
timing interval. These records support review, not an automatic idle-host proof.

## Bootstrap once, choose the scope per run

Substitute exact committed candidate/control SHAs and the baseline checkout.
Bootstrap compiles the complete set of wrappers, generates the full input/cell
matrix and freezes identities. It does not run observations or timing. The host
still needs the toolchain and reference builds above; this is not OS provisioning.
Choose the bootstrap timeout explicitly; there is no eight-hour requirement.

```sh
python scripts/bench_campaign/campaign.py bootstrap \
  --platform x86-linux --cpu 2 \
  --commit "$CANDIDATE_SHA" \
  --control-source "$BASELINE_CHECKOUT" --control-commit "$BASELINE_SHA" \
  --reference-bin target/bench-fast-refs/bin \
  --reference-lock target/bench-fast-refs/lock.json \
  --host-notes target/host-notes.txt \
  --timeout-hours "$BOOTSTRAP_BUDGET_HOURS" \
  --out target/bootstraps/release-001
```

The same bootstrap can supply fresh smoke, subset and full attempts. The run
inherits its source/platform/reference configuration and verifies hashes. It
copies prepared files, including build outputs, into a new attempt, then runs
observations and freezes the selected scope before timing. It never reuses old
samples or calibration counts. Keep the bootstrap and its source/reference
checkouts available: native loader paths, especially on macOS, may still refer
to the original build. Copies use disk space; clean completed attempts after
review. This is local reuse on the same configured host, not a portable cache.

Preview the exact cell IDs, exclusions and timed-work target without executing
any workload:

```sh
python scripts/bench_campaign/campaign.py plan \
  --prepared target/bootstraps/release-001 --suite smoke
python scripts/bench_campaign/campaign.py plan \
  --prepared target/bootstraps/release-001 --suite subset \
  --primitive exp --backend avx2
```

| Suite | Selection | Meaning of a successful result |
| --- | --- | --- |
| `full` (default) | Every original cell; filters forbidden | All required cells in the full native matrix passed. |
| `smoke` | One ordinary 52-element cell for each canonical family; x86 also includes an unchanged strong exp control | The smoke selection passed; full qualification remains unestablished. |
| `subset` | Explicit primitives, x86 backends and/or exact cell IDs | Only the declared selection passed; excluded cells remain listed. |

The smoke preset exercises scalar CORE-MATH exp, vector SLEEF exp, batched
libcerf erfcx and scalar SciPy CDF. It has five cells on x86 and four on macOS.
At the current protocol's target duration, those contain 120 and 96 seconds of
timed work respectively, **excluding** warmups, calibration, copies, hashing and
observations. Smoke keeps the existing per-cell sampling protocol; it is smaller
coverage, not a shortcut to a full qualification decision.

```sh
python scripts/bench_campaign/campaign.py run \
  --prepared target/bootstraps/release-001 --suite smoke \
  --host-notes target/host-notes.txt --timeout-hours 0.5 \
  --out target/campaigns/smoke-001
python scripts/bench_campaign/campaign.py run \
  --prepared target/bootstraps/release-001 --suite subset \
  --primitive exp --backend avx2 \
  --host-notes target/host-notes.txt --timeout-hours "$SUBSET_BUDGET_HOURS" \
  --out target/campaigns/exp-avx2-001
python scripts/bench_campaign/campaign.py run \
  --prepared target/bootstraps/release-001 --suite full \
  --host-notes target/host-notes.txt --timeout-hours "$FULL_BUDGET_HOURS" \
  --out target/campaigns/full-001
```

Repeat `--primitive`, `--backend` or `--cell` to select several values. Values
within one filter are ORed; different filters are ANDed. Unknown values, empty
selections, filters on `full`/`smoke`, and an unspecified subset are errors.
A primitive/backend selection includes every existing reference/control cell
matching those filters. Exact IDs permit deliberately narrower experiments.
The original full matrix and all excluded IDs remain in the evidence. Subset
results cannot silently become full qualification, even if their filters happen
to select every cell. Use `--suite full` for that decision.

`run` also accepts all bootstrap configuration arguments directly, instead of
`--prepared`, to build and run in one command. Every output path must be new and
under this repository's `target/`. A previous timing attempt cannot be supplied
as a bootstrap. The full native matrices retain 500 x86 cells / 430 required and
163 macOS ARM cells / 125 required with their established confidence rule.

On macOS use `--platform arm-macos` when locking references and bootstrapping,
add `--sleef-include target/bench-fast-refs/sleef-build/include`, and omit x86
control options. macOS has no x86-style affinity or separate backend selector;
use primitive/cell filters. ARM groups preserve original cell IDs. Its runner
can stop at a failed group, leaving selected later cells missing. ARM product
bank observations remain comprehensive even for a selected timing subset.

`--timeout-hours` bounds subprocess stages. Copies, hashing, final receipts and
cleanup happen outside that deadline; it is not a provider billing cap. Timeout,
SIGTERM or Ctrl-C kills the stage process group and retains failure evidence.
SIGKILL, host loss or disk failure can prevent final receipts; `running` is not
success. No automatic retry, continuation or outlier deletion is supported.

## Evidence and checks

Each attempt retains:

- `campaign.json`: source/control identity, reference lock, host notes/snapshots,
  stage commands/status, configuration, selection, verification and outcome.
  `selected_passed` covers the chosen cells; `qualification_passed` can be true
  only for a successful `full` run. A successful bootstrap is `prepared`, with
  both performance flags false. Exit zero means that the requested operation
  succeeded, not necessarily full qualification.
- `comparisons.json`: every declared cell, canonical/control label, contract,
  native measurements, failed required cells, missing selected cells and
  deliberately excluded cells.
- `native/matrix-full.json` and `native/selection.json`: original full cells,
  their hash, requested filters, selected/excluded IDs and timed-work target.
- `native/`: build command records, exact input banks, observation output, frozen
  source hashes and all native raw/calibration/failed attempts.
- Stage logs, the reference build log, and `artifacts.json` with SHA-256 identities
  of files in the attempt. External references also have hashes in the lock and
  frozen receipt; a reference directory symlink is not a portable binary bundle.

Keep evidence available through review in ignored storage. An artifact inventory
is a local integrity record, not a signed attestation or verified cloud upload.
Hash scans and diagnostics stay outside uninstrumented timing. Native speed and
reference equivalence require actual measurements and contract review.

```sh
python3 -m unittest scripts.bench_campaign.test_campaign -v
```

These focused tests use synthetic subprocesses for lifecycle, timeout cleanup,
reference coverage, evidence tampering and cost arithmetic. They establish no
native speed claim. Full repository checks remain in GitHub CI.
