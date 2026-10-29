# Native benchmark campaigns and cloud lifecycle ownership

## Decision

The numerical runners in `scripts/bench_fast` own input generation, timing,
calibration, pairing and qualification statistics. `scripts/bench_campaign`
adds source/reference identities, stage execution, evidence receipts and an
independent cost estimate. It does not introduce a second timing or statistics
engine. Every canonical participant runs on the same native machine as Numerics.

For cloud lifecycle, adopt external
[PerfKit Benchmarker](https://github.com/GoogleCloudPlatform/PerfKitBenchmarker/tree/50bbc173d75696c867dc0be5a742e9906445f5e9)
at commit `50bbc173d75696c867dc0be5a742e9906445f5e9`. PKB supplies VM provisioning,
remote preparation, execution and teardown through provider tools. Keep its
Apache-2.0 implementation outside this dual-licensed repository and outside
published crates. A domain adapter may invoke the local campaign command and
transfer its evidence; it must not become another VM manager or scheduler.

The implemented boundary is local execution and offline costing. There is no
cloud launcher, upload verifier or paid pilot in this tree. Delivery and the
remaining acceptance evidence are tracked in
[#245](https://github.com/MorphIQ-Labs/morphiq-numerics/issues/245), with numerical
methodology owned by #150 and release qualification by #243.

## Alternatives and rationale

PKB already models temporary benchmark machines and lifecycle stages. Terraform
or OpenTofu would provide declarative infrastructure but require a separate
execution and evidence lifecycle for each campaign. A hand-written gcloud
provision/poll/delete loop would duplicate ownership that PKB already provides.
Google Benchmark, Criterion and pyperf can measure workloads but do not replace
the existing exact-input, native paired comparison protocol or cloud lifecycle.
Adopt PKB for infrastructure; retain the established numerical runners.

## Experiment identity

A campaign declares the candidate and baseline commit, canonical source pins and
binary hashes, Python reference/oracle versions and installed-file hashes,
build commands, exact input bits, native platform, allowed CPU, toolchain and
host conditions. Preparation and independent observations precede the frozen
measurement interval. Instrumented diagnostics never supply timing observations.
A reference's numerical guarantee and calling interface are distinct from the
product's. Missing proof of contract equivalence remains explicit.

The local adapter preserves each declared cell, including failed and missing
comparisons. Baseline strong-path controls and canonical fast-path comparisons
have separate labels. Missing mandatory reference families are rejected. No
average across functions can hide an absent or failing required cell, and no
new global 3% spread tolerance is introduced.

## Cloud adapter contract

The deployment boundary requires explicit project, zone, exact image (not a
moving image family), machine type, disk configuration, service account,
artifact bucket/prefix, campaign identity and maximum VM lifetime. An initial
x86 profile is C3; C4A is the ARM costing profile, not a supported ARM Linux
benchmark adapter. Verify actual CPU/ISA on arrival and compare only within the
same instance. A machine SKU does not promise bare-metal isolation or control
of physical frequency, thermal state or host contention.

Bootstrap builds pinned black-box references and the declared source before
measurement. PKB retries and repeated run stages must not repeat a failed
qualification into a passing result. Each deliberate new attempt gets a fresh
identity and retains the previous failure. Source bundles and manifests are
trusted executable inputs; private consumer code and artifacts stay private.

Evidence must be copied and checksum-verified before normal teardown. Failure,
interruption, upload failure and controller loss need explicit receipts and
cleanup tests; missing artifacts never become a successful campaign. Provider
[maximum runtime with deletion](https://docs.cloud.google.com/compute/docs/instances/limit-vm-runtime)
and boot-disk auto-delete bound an orphan VM's lifetime independently of the
controller. They do not delete bucket data or make a billing budget a hard cap.
PKB's timeout metadata alone is not evidence of that provider-side limit. A
provider integration must demonstrate the limit on the actual created VM.

Only after bootstrap, successful and failed runs, upload verification, teardown
and resource inventory have been exercised can the cloud process be called
operational. Correctness CI remains separate from native performance evidence.
