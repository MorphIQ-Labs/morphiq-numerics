#!/usr/bin/env python3
"""Check the exact planned set of successful formal-family receipts."""
import argparse
import json
from pathlib import Path


def receipt(plan, family, kernel_reports, certificate_reports):
    unit = plan["families"][family]
    if kernel_reports != len(unit["kernel_entries"]) or certificate_reports != len(unit["certificates"]):
        raise ValueError("actual audit counts differ from the family plan")
    return dict(family=family, cache_key=unit["cache_key"], inputs=plan["inputs"],
                kernel_entries=unit["kernel_entries"], certificates=unit["certificates"],
                base_audit=unit["base_audit"], base_entries=plan["base_entries"] if unit["base_audit"] else 0,
                extractions=unit["extractions"])


def aggregate(plan, receipts):
    selected = plan["selected"]
    if not selected or len(selected) != len(set(selected)) or not set(selected) <= plan["families"].keys():
        raise ValueError("invalid or empty formal selection")
    actual = [r.get("family") for r in receipts]
    if len(actual) != len(set(actual)) or set(actual) != set(selected):
        raise ValueError("missing, duplicate or unselected family receipt")
    for result in receipts:
        family = result["family"]
        unit = plan["families"][family]
        if result != receipt(plan, family, len(unit["kernel_entries"]), len(unit["certificates"])):
            raise ValueError(f"stale or incomplete formal receipt: {family}")
    return dict(families=len(receipts), kernel_entries=sum(len(r["kernel_entries"]) for r in receipts),
                base_entries=sum(r["base_entries"] for r in receipts),
                certificates=sum(len(r["certificates"]) for r in receipts),
                extractions=sum(len(r["extractions"]) for r in receipts))


def check_status(hygiene, planner, affected, families):
    if hygiene != "success" or planner != "success":
        raise ValueError("formal prerequisites did not succeed")
    expected = {"true": "success", "false": "skipped"}
    if affected not in expected or families != expected[affected]:
        raise ValueError("formal selection or selected execution did not complete")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    status = sub.add_parser("status")
    for name in ["hygiene", "planner", "affected", "families"]:
        status.add_argument("--" + name, required=True)
    one = sub.add_parser("receipt")
    one.add_argument("--plan", type=Path, required=True)
    one.add_argument("--family", required=True)
    one.add_argument("--kernel-reports", type=int, required=True)
    one.add_argument("--certificate-reports", type=int, required=True)
    one.add_argument("--out", type=Path, required=True)
    all_checks = sub.add_parser("aggregate")
    all_checks.add_argument("--plan", type=Path, required=True)
    all_checks.add_argument("--receipts", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "status":
        check_status(args.hygiene, args.planner, args.affected, args.families)
        return
    plan = json.loads(args.plan.read_text())
    if args.command == "receipt":
        result = receipt(plan, args.family, args.kernel_reports, args.certificate_reports)
        args.out.parent.mkdir(parents=True, exist_ok=True)
        with args.out.open("x") as handle:
            handle.write(json.dumps(result, indent=2) + "\n")
    else:
        results = [json.loads(p.read_text()) for p in sorted(args.receipts.glob("*.json"))]
        print("formal aggregate: " + json.dumps(aggregate(plan, results), sort_keys=True))


if __name__ == "__main__":
    main()
