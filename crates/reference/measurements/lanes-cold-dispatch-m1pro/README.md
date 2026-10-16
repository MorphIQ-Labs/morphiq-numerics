# Native ARM cold-path comparison

Apple M1 Pro; environment in `environment.txt`. This compares main at
`76825af` (variant 0), #165 at `d14a580` (variant 1), and the candidate
`f8f572e` (variant 2). Three processes each provide 11 retained rounds,
after one warmup, with variant order rotated per round. Each sample runs
for at least 5 ms. The 4,096-element pool is split into calls of 2, 8 or
4,096 elements. Each output is checked before timing. Inputs are fixed-seed
and represent the workload families used by the existing lane sweep; their
seed differs, so absolute times are not compared across harnesses.

`build_paired.py` archives the revisions and renames only the library and
arch crate identities in the benchmark copies, allowing all three to link
in one process. The numerical source is unchanged. Run it from the repo root:

```sh
python3 crates/reference/measurements/lanes-cold-dispatch-m1pro/build_paired.py
```

Raw samples and their median/min/max summary are versioned. For length
4,096, candidate/#165 ratios are: ordinary ln 1.000, near-one ln 1.001,
ln1p exp-negative 0.999, huge 1.004, mixed 1.003, screened 0.991, and central
log-CDF 0.999. These small differences do not establish a speedup. Other sessions share
the host and their load was not sampled continuously. The
screened ARM slowdown in an earlier scalar-prefix candidate is no longer
observed after retaining the existing two-lane boundary. Compared with main,
#165's ordinary and near-one ln gains remain present.

This host cannot validate the AVX2 scalar-prefix or native AVX-512 mask
performance changes. The reported x86 regressions remain unestablished until
native same-host measurements repeat the original affected workloads and
backend/length cells. SDE and CI timings are not native performance evidence.
