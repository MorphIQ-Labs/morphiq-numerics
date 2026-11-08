#!/usr/bin/env python3
"""Choose formal execution and check its exact source-bound completion evidence."""
import argparse
import hashlib
import json
from pathlib import Path


def execution(plan):
    selected = plan["selected"]
    if not selected or len(selected) != len(set(selected)) or not set(selected) <= plan["families"].keys():
        raise ValueError("invalid or empty formal selection")
    return "full" if set(selected) == plan["families"].keys() else "families"


def matrix(plan):
    if execution(plan) == "full":
        keys = {name: unit["cache_key"] for name, unit in plan["families"].items()}
        key = hashlib.sha256(json.dumps(keys, sort_keys=True).encode()).hexdigest()
        return {"include": [dict(name="full", family="", cache="formal-build", key=key)]}
    return {"include": [dict(name=name, family=name, cache="formal-family-" + name,
                             key=plan["families"][name]["cache_key"]) for name in plan["selected"]]}


def receipt(plan, family, kernel_reports, certificate_reports):
    unit = plan["families"][family]
    if kernel_reports != len(unit["kernel_entries"]) or certificate_reports != len(unit["certificates"]):
        raise ValueError("actual audit counts differ from the family plan")
    return dict(family=family, cache_key=unit["cache_key"], inputs=plan["inputs"],
                kernel_entries=unit["kernel_entries"], certificates=unit["certificates"],
                base_audit=unit["base_audit"], base_entries=plan["base_entries"] if unit["base_audit"] else 0,
                extractions=unit["extractions"])


def full_receipt(plan, kernel_reports, certificate_reports):
    if execution(plan) != "full":
        raise ValueError("full completion requires every family selected")
    families = {name: receipt(plan, name, len(unit["kernel_entries"]), len(unit["certificates"]))
                for name, unit in plan["families"].items()}
    if kernel_reports != sum(len(r["kernel_entries"]) for r in families.values()) or \
            certificate_reports != sum(len(r["certificates"]) for r in families.values()):
        raise ValueError("actual audit counts differ from the full plan")
    return dict(execution="full", families=families)


def aggregate(plan, receipts):
    mode = execution(plan)
    if mode == "full":
        expected = full_receipt(plan, sum(len(u["kernel_entries"]) for u in plan["families"].values()),
                                sum(len(u["certificates"]) for u in plan["families"].values()))
        if receipts != [expected]:
            raise ValueError("missing, stale or incomplete full formal receipt")
        receipts = list(receipts[0]["families"].values())
    selected = plan["selected"]
    actual = [r.get("family") for r in receipts]
    if len(actual) != len(set(actual)) or set(actual) != set(selected):
        raise ValueError("missing, duplicate or unselected family receipt")
    for result in receipts:
        family = result["family"]
        unit = plan["families"][family]
        if result != receipt(plan, family, len(unit["kernel_entries"]), len(unit["certificates"])):
            raise ValueError(f"stale or incomplete formal receipt: {family}")
    return dict(execution=mode, families=len(receipts), kernel_entries=sum(len(r["kernel_entries"]) for r in receipts),
                base_entries=sum(r["base_entries"] for r in receipts),
                certificates=sum(len(r["certificates"]) for r in receipts),
                extractions=sum(len(r["extractions"]) for r in receipts))


def check_status(hygiene, planner, affected, execution):
    if hygiene != "success" or planner != "success":
        raise ValueError("formal prerequisites did not succeed")
    expected = {"true": "success", "false": "skipped"}
    if affected not in expected or execution != expected[affected]:
        raise ValueError("formal selection or selected execution did not complete")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    status = sub.add_parser("status")
    for name in ["hygiene", "planner", "affected", "execution"]:
        status.add_argument("--" + name, required=True)
    routing = sub.add_parser("matrix")
    routing.add_argument("--plan", type=Path, required=True)
    one = sub.add_parser("receipt")
    one.add_argument("--plan", type=Path, required=True)
    one.add_argument("--family")
    one.add_argument("--kernel-reports", type=int, required=True)
    one.add_argument("--certificate-reports", type=int, required=True)
    one.add_argument("--out", type=Path, required=True)
    all_checks = sub.add_parser("aggregate")
    all_checks.add_argument("--plan", type=Path, required=True)
    all_checks.add_argument("--receipts", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "status":
        check_status(args.hygiene, args.planner, args.affected, args.execution)
        return
    plan = json.loads(args.plan.read_text())
    if args.command == "matrix":
        print(json.dumps(matrix(plan), sort_keys=True))
        return
    if args.command == "receipt":
        result = (receipt(plan, args.family, args.kernel_reports, args.certificate_reports) if args.family else
                  full_receipt(plan, args.kernel_reports, args.certificate_reports))
        args.out.parent.mkdir(parents=True, exist_ok=True)
        with args.out.open("x") as handle:
            handle.write(json.dumps(result, indent=2) + "\n")
    else:
        results = [json.loads(p.read_text()) for p in sorted(args.receipts.glob("*.json"))]
        print("formal aggregate: " + json.dumps(aggregate(plan, results), sort_keys=True))


if __name__ == "__main__":
    main()
