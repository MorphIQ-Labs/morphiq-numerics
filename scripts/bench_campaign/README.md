# Reusable native comparison campaigns

This controller runs the existing `bench_fast` matrix on native x86 Linux or
Apple Silicon macOS. It records pinned canonical references, candidate/control
commits, commands, host conditions, raw attempts, comparisons and checksums.
Python 3.11 or newer is required. It adds no Rust dependencies and changes no
numerical implementation, timing loop, statistical rule or numerical contract.

The cloud component currently provides an offline cost estimate. Provisioning,
bootstrap on a fresh VM, verified upload and teardown are not implemented.
[Architecture](../../docs/adr/0001-native-benchmark-campaigns.md) records the PKB
lifecycle boundary; [#245](https://github.com/MorphIQ-Labs/morphiq-numerics/issues/245)
tracks delivery. GCP ARM Linux cannot run the macOS harness.

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

## Run one complete campaign

Substitute the exact committed candidate/control SHAs and baseline checkout.
The output must be a new directory under this repository's `target/`:

```sh
python scripts/bench_campaign/campaign.py run \
  --platform x86-linux --cpu 2 \
  --commit "$CANDIDATE_SHA" \
  --control-source "$BASELINE_CHECKOUT" --control-commit "$BASELINE_SHA" \
  --reference-bin target/bench-fast-refs/bin \
  --reference-lock target/bench-fast-refs/lock.json \
  --host-notes target/host-notes.txt \
  --timeout-hours 12 \
  --out target/campaigns/x86-release-001
```

The command prepares native wrappers and exact input banks, runs independent
observations, freezes files, executes the complete native matrix, verifies
identities and writes `comparisons.json`. It invokes all declared canonical
comparisons; there is no switch that silently drops a slow comparator. The
native runners retain their 500 x86 cells / 430 required and 163 macOS ARM cells /
125 required, calibration, alternating pairing and one-sided confidence rule.
The controller fails closed for missing mandatory families, missing measurements,
invalid durations, changed files or a failed stage. A zero exit code means the
native matrix completed and all its required cells passed, not that all library
contracts or consumer workloads have been qualified.

On macOS use `--platform arm-macos` for both commands and supply
`--sleef-include target/bench-fast-refs/sleef-build/include` to `run`; omit the
x86 control options. macOS does not provide the x86 CPU-affinity behavior.
The ARM runner can stop at a failed group; unmeasured later cells remain missing.

`--timeout-hours` bounds subprocess stages including preparation and observations.
Hashing, final receipts and process cleanup happen outside that deadline; this
is not a provider billing cap. Timeout, SIGTERM or Ctrl-C kills the stage process
group, retains evidence and returns failure. SIGKILL, host loss or disk failure
can prevent final receipts; the last `running` state is not success. There is no
automatic retry, continuation or outlier deletion.

## Evidence and checks

Each attempt retains:

- `campaign.json`: source/control identity, reference lock, host notes/snapshots,
  stage commands/status, verification and qualification outcome.
- `comparisons.json`: every declared cell, canonical/control label, contract,
  native measurements, failed required cells and missing cells.
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
