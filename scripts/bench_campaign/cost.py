#!/usr/bin/env python3
"""Offline GCP campaign estimate, including failed-attempt runtime and retained evidence."""
import argparse
import json
import math
from pathlib import Path

RATES = json.loads(Path(__file__).with_name('rates.json').read_text())


def estimate(machine, hours, *, disk_gib=100, artifact_gib=1, retention_days=30,
             download_gib=0, class_a=100, class_b=100, failed_hours=0,
             campaigns=1, controller_usd=0):
    values = [hours, disk_gib, artifact_gib, retention_days, download_gib,
              class_a, class_b, failed_hours, campaigns, controller_usd]
    if any(not math.isfinite(x) or x < 0 for x in values) or hours <= 0 or campaigns < 1:
        raise ValueError('Costs require finite nonnegative quantities, positive hours and at least one campaign')
    if any(x != int(x) for x in [class_a, class_b, campaigns]):
        raise ValueError('Operations and campaign counts must be integers')
    spec = RATES['machines'][machine]
    # Successful and failed VM attempts each have a one-minute compute minimum.
    billed_hours = max(hours, 1 / 60) + (max(failed_hours, 1 / 60) if failed_hours else 0)
    components = {
        'compute': spec['hour'] * billed_hours,
        'boot_disk': RATES['disk_gib_hour'][spec['disk']] * disk_gib * (hours + failed_hours),
        'external_ipv4': RATES['ipv4_hour'] * (hours + failed_hours),
        'evidence_storage': RATES['storage_gib_hour'] * artifact_gib * retention_days * 24,
        'storage_operations': (class_a * RATES['class_a_per_1000'] + class_b * RATES['class_b_per_1000']) / 1000,
        'evidence_download': RATES['download_gib'] * download_gib,
        'controller': controller_usd,
    }
    return {'rate_date': RATES['as_of'], 'currency': RATES['currency'], 'region': RATES['region'],
            'machine': machine, 'hours_per_attempt': hours, 'failed_attempt_hours': failed_hours,
            'assumptions': {'disk_gib': disk_gib, 'artifact_gib_including_failures': artifact_gib,
                            'retention_days_including_soft_delete': retention_days, 'download_gib': download_gib,
                            'class_a_operations': class_a, 'class_b_operations': class_b,
                            'hyperdisk_iops': 3000, 'hyperdisk_mib_per_second': 140},
            'components_usd_per_campaign': components, 'per_campaign_usd': sum(components.values()),
            'campaigns': campaigns, 'total_usd': sum(components.values()) * campaigns,
            'sources': RATES['sources'], 'provisions_resources': False,
            'exclusions': ['tax, support and negotiated billing', 'premium OS licences',
                           'NAT, extra disk IOPS/throughput, snapshots and orphaned resources',
                           'cross-region traffic and VM internet egress',
                           'logging/monitoring beyond local artifacts'],
            'network_assumption': 'VM and Standard bucket in us-central1; download rate for first 10 TiB/month to destinations excluding China/Australia.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--machine', choices=RATES['machines'], required=True)
    ap.add_argument('--hours', type=float, required=True, help='Entire VM lifetime: bootstrap, checks, timing, upload, teardown')
    ap.add_argument('--failed-hours', type=float, default=0, help='One additional failed attempt per campaign; no retries implied')
    ap.add_argument('--campaigns', type=int, default=1)
    ap.add_argument('--disk-gib', type=float, default=100)
    ap.add_argument('--artifact-gib', type=float, default=1)
    ap.add_argument('--retention-days', type=float, default=30)
    ap.add_argument('--download-gib', type=float, default=0)
    ap.add_argument('--class-a', type=int, default=100)
    ap.add_argument('--class-b', type=int, default=100)
    ap.add_argument('--controller-usd', type=float, default=0)
    ap.add_argument('--budget-usd', type=float, help='Reject a modeled total above this amount; not a billing cap')
    args = vars(ap.parse_args())
    budget = args.pop('budget_usd')
    try:
        if budget is not None and (not math.isfinite(budget) or budget < 0):
            raise ValueError('Budget must be finite and nonnegative')
        result = estimate(**args)
    except ValueError as exc:
        ap.error(str(exc))
    result['within_estimated_budget'] = budget is None or result['total_usd'] <= budget
    print(json.dumps(result, indent=2, allow_nan=False))
    return 0 if result['within_estimated_budget'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
