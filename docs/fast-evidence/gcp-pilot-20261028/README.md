# GCP repeatability pilot, 28 October 2026

The fixed-configuration x86 pilot **failed its predeclared stability gate**.
Six of twelve primitive/interface cells exceeded the allowed 3% range of
process medians. All twelve block-median drifts stayed below 3%, but both
conditions were required. This is retained negative evidence, not completed
performance qualification or a claim that GCP cannot support reliable timing.

The source revision was `1581511e6c8ef6546d7f4711ab23900e5ee020ea`.
The host was `c4-standard-4` in `us-central1-a`, Intel Emerald Rapids, with
the exact Debian image `debian-12-bookworm-v20261027`, Rust 1.97.1,
`simd,std`, no compiler flag override, `ALL_CORE_MAX`, one thread per core,
standard PMU, and the benchmark pinned to guest CPU 0. The VM exposed two
physical cores; the provisioned shape has four vCPUs with SMT enabled.

The public `bench-fast-primitives` runner used its original fixed 52-value
packets. One process warmed up, then two blocks of five processes ran with
30 seconds between blocks. Each process supplied four alternating samples
per cell, each timing 10,000 calls. The decision used each process's median:
both absolute block-median drift and the total process-median range divided
by the overall median had to be at most 3%. These pilot criteria were recorded
in PR #240 before execution. They are not permitted regression thresholds.

| Primitive | Mode | Median ns / 52 values | Process-median range | Block drift | Stable |
| --- | --- | ---: | ---: | ---: | --- |
| exp | strong scalar | 256.22 | 0.91% | 0.02% | yes |
| exp | fast scalar | 180.21 | 6.12% | 2.73% | no |
| exp | strong slice | 167.13 | 1.49% | 0.27% | yes |
| exp | fast slice | 156.01 | 106.28% | 0.15% | no |
| erfcx | strong scalar | 773.10 | 1.93% | 0.05% | yes |
| erfcx | fast scalar | 568.31 | 0.21% | 0.01% | yes |
| erfcx | strong slice | 550.56 | 12.12% | 0.21% | no |
| erfcx | fast slice | 505.19 | 20.54% | 1.14% | no |
| CDF | strong scalar | 1870.31 | 1.07% | 0.01% | yes |
| CDF | fast scalar | 945.44 | 2.26% | 0.04% | yes |
| CDF | strong slice | 1018.91 | 7.19% | 0.47% | no |
| CDF | fast slice | 589.57 | 13.39% | 2.38% | no |

The fast-exp slice outlier occurred in process 6 (319.4 ns per call versus
roughly 154–157 ns in the other processes). Guest CPU 0 reported no stolen
ticks over any measured process. The observed instability's cause was not
established. The shortest samples lasted roughly 1.6 ms; this limits the
runner's ability to average short disturbances. No samples were dropped and
the gate was not relaxed. These medians are diagnostic, not accepted speedup
claims.

The archived independent fixture replay reported no bound failures. It ran
after timings. A separate `perf stat` run reported approximately 3.083 GHz,
2.77 instructions per cycle, three context switches and one CPU migration
over the whole process (including initial affinity setup and untimed work).
Those counters do not identify which timed sample was disturbed. No cloud
maintenance operation was recorded in the instance operation history.

The VM had a server-enforced one-hour deletion deadline and was deleted much
earlier: creation started at 00:12:50.677 UTC and deletion completed at
00:15:56.049 UTC. The VM, boot disk, ephemeral address, firewall, subnet and
network were removed. At the recorded published fixed-resource rates this
interval implies approximately $0.011, excluding small outbound transfer;
this is an estimate, not an invoice. The $5 allowance was not consumed by
keeping an idle host. No CI ran on the measurement VM; it ran only the release benchmark build,
measurements, numerical observations and separate PMU run. GitHub CI remained
separate.

The rate estimate uses Google's published [compute pricing](https://cloud.google.com/products/compute/pricing/general-purpose?hl=en),
[disk pricing](https://cloud.google.com/compute/disks-image-pricing) and
[IPv4 pricing](https://cloud.google.com/vpc/network-pricing), checked for this
pilot. The retained VM configuration records its automatic deletion deadline.

`observations.tar.gz` contains all raw runs (including the outlier), process
medians, conditions, build/toolchain/package records, binary/source hashes,
the observation replay and the measurement/startup scripts. Personal home
paths are replaced with placeholders; numerical results are unchanged.
`manifest.json` records hashes, configuration, lifecycle and cleanup checks.
The artifact does not include executables or build outputs. Reproduction
starts from the recorded source revision and the PR's benchmark handoff.
