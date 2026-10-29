# GCP campaign cost model

Prices checked **2026-10-29**, USD public on-demand list prices in
**Iowa (`us-central1`)**, before tax, credits or discounts. Refresh the checked-in
[`rates.json`](rates.json) against its official source URLs before paid runs.
The estimator is offline and provisions nothing. No cloud pilot or measured
campaign duration is implied by these estimates.

## Profiles and rates

| Profile | CPU/RAM | VM/hour | Disk used in estimate |
| --- | --- | ---: | --- |
| `c3-standard-8` | 8 vCPUs, 32 GiB | $0.403216 | 100 GiB balanced Persistent Disk |
| `c4a-standard-4` | 4 vCPUs, 16 GiB | $0.179600 | 100 GiB Hyperdisk Balanced |

These rates include CPU and RAM. The C3 x86 and C4A ARM machines are separate
qualification profiles, not equivalent cores or comparable cross-host timings.
Disabling SMT does not reduce billed machine size. Use on-demand instances for
qualification; Spot interruptions and pricing changes complicate complete paired
campaigns. ARM Linux needs its own runnable adapter before the C4A estimate can
become a qualification run. [Compute rates](https://cloud.google.com/products/compute/pricing/general-purpose),
[billing rules](https://cloud.google.com/products/compute/pricing).

Balanced Persistent Disk costs $0.000136986/GiB-hour; Hyperdisk Balanced space
costs $0.000109589/GiB-hour. Explicitly configure Hyperdisk at 3,000 IOPS and
140 MiB/s, its included baseline. Provider defaults can provision more and cost
extra. Delete the boot disk with the VM. [Disk rates](https://cloud.google.com/compute/disks-image-pricing),
[Hyperdisk baseline](https://docs.cloud.google.com/compute/docs/disks/hd-types/hyperdisk-balanced#baseline_performance).

The model includes one ephemeral IPv4 at $0.005/hour. It assumes a same-region
Standard bucket, $0.000027397/GiB-hour, 100 Class A and 100 Class B operations per
campaign ($0.005 and $0.0004 per thousand). Optional artifact download is
$0.12/GiB for the first 10 TiB/month to destinations excluding China/Australia.
No free-tier credit is assumed. [Network](https://cloud.google.com/vpc/network-pricing),
[storage, operations and transfer](https://cloud.google.com/storage/pricing).

## Example budgets

All examples include 100 GiB boot disks, one IPv4 per VM, 1 GiB evidence per
architecture stored for 30 days **including any soft-delete retention**, and the
operations above. No downloads; existing local controller has zero incremental
cloud charge. Add `--controller-usd` if a paid controller is used. Hours cover
bootstrap, compilation, observations, warmups/calibration, measurements, artifact
transfer and teardown, not just the inner timing loop.

| Scenario | x86 | ARM | Combined |
| --- | ---: | ---: | ---: |
| One-hour smoke allocation on each profile | $0.44 | $0.22 | $0.66 |
| 8-hour x86 + 4-hour ARM allocation | $3.40 | $0.80 | $4.20 |
| Same, plus one failed one-hour attempt on each | $3.82 | $1.00 | $4.82 |
| 20 complete allocations/month, each 8h + 4h | $67.91 | $16.05 | $83.96 |
| Both machines left running for 24 hours | $10.15 | $4.71 | $14.86 |

These are allocation scenarios, not ETAs. The present x86 matrix alone has
500 cells × 10 processes × 2 rounds × 2 implementations × 0.6 seconds =
**3.33 hours of target-duration timed work**; ARM's 163 cells imply **1.09 hours**.
Warmups, pilots, build time, observations and host variability add runtime.
A one-hour allocation cannot complete the full x86 matrix. Canonical participants
are already included in those cell counts; extra strong/fast baseline or new
canonical matrices add cells and cost. Duration overruns remain failed attempts.

```sh
python scripts/bench_campaign/cost.py --machine c3-standard-8 --hours 8
python scripts/bench_campaign/cost.py --machine c4a-standard-4 --hours 4
python scripts/bench_campaign/cost.py --machine c3-standard-8 --hours 8 \
  --failed-hours 1 --campaigns 20 --budget-usd 80
```

Compute is billed with a one-minute minimum per modeled attempt, then by time;
disk/IP follow allocated lifetime. Evidence cost is size × retained hours ×
storage rate, plus operations and explicit download volume. `--failed-hours`
models one additional failed attempt per campaign; it does not enable retries.
Size/operations must include failed evidence. Each extra downloaded GiB adds
$0.12 in the stated tier. Each extra retained GiB for 30 days adds about $0.02.

Budget checks compare modeled totals only. They do not control a cloud account.
An independent provider maximum-runtime/delete policy, boot-disk auto-delete,
post-teardown inventory and explicit bucket retention are needed to bound
unexpected resource lifetime. Retained snapshots, extra IOPS/throughput, NAT,
cross-region traffic, VM internet egress, premium OS images, paid logging,
support and tax are excluded; price them separately if selected. A cleanup
failure can exceed any scenario, and a longer retention/soft-delete setting
continues storage charges after a run ends.
