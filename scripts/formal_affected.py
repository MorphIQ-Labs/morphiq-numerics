#!/usr/bin/env python3
"""Which kernel-audit entries a change can affect.

The kernel audit (formal/audit/KernelAudit.v) prints the global assumptions of
about 600 theorems and takes most of the formal lane. An entry's assumptions are
a function of its module and the modules it depends on, so after a change only
the entries of a changed module, or of one that depends on it, can differ from
the audit that passed at the base commit. This script computes that set from
`coqdep` over the assembled source tree, and writes the audit file restricted
to it.

It chooses everything (the whole audit) whenever it is not sure: a path under
formal/ it does not know, a change to the shared developments, the lane's own
scripts or the toolchain pins, a changed module it cannot find in the graph, an
entry whose module it cannot find. The whole audit also runs on every push to
the default branch, so a mistake here cannot reach a release unaudited.

usage: formal_affected.py --coqdep-output FILE --changed FILE --audit FILE --base-audit FILE --out FILE
"""
import argparse
import os
import re
import sys

# A change to any of these can change the assumptions of anything.
EVERYTHING = (
    "formal/binary64/",
    "formal/double-word/",
    "formal/two-prod/",
    "formal/q/",
    "formal/gappa/",
    "formal/extraction/",
    "formal/audit/Audit.v",
    "formal/axioms",
    "scripts/check_formal",
    "scripts/formal_",
    "scripts/write_gappa_proofs.sh",
    ".cargo/coq-",
    ".github/workflows/ci.yml",
)
# Not read by the kernel audit; the manifest is checked in full on every run.
IGNORED = ("formal/binding.sha256",)
KERNEL_DIRS = ("exp", "ln", "erfcx", "normal", "asin", "asinh", "atan2", "bivariate")
ENTRY = re.compile(r"^Print Assumptions ([A-Za-z0-9_.']+)\.$")


def parse_coqdep(text):
    """Module key (path without .vo) -> the keys it depends on."""
    graph = {}
    for statement in text.replace("\\\n", " ").split("\n"):
        if ":" not in statement:
            continue
        targets, deps = statement.split(":", 1)
        compiled = [t for t in targets.split() if t.endswith(".vo")]
        if not compiled:
            continue
        graph[compiled[0][:-3]] = {d[:-3] for d in deps.split() if d.endswith(".vo")}
    return graph


def dependents_closure(graph, roots):
    """The roots and every module that depends on one, directly or not."""
    reverse = {}
    for module, deps in graph.items():
        for dep in deps:
            reverse.setdefault(dep, set()).add(module)
    seen = set(roots)
    pending = list(roots)
    while pending:
        for user in reverse.get(pending.pop(), ()):
            if user not in seen:
                seen.add(user)
                pending.append(user)
    return seen


def changed_modules(paths, graph):
    """The module keys a list of changed paths touches, or None for everything."""
    modules = set()
    for path in paths:
        path = path.strip()
        if not path or path in IGNORED:
            continue
        if path.startswith(EVERYTHING):
            return None
        parts = path.split("/")
        if parts[0] == "formal":
            if len(parts) != 3 or parts[1] not in KERNEL_DIRS:
                return None
            name, extension = os.path.splitext(parts[2])
            if extension == ".v":
                key = "gappa/" + name
            elif extension == ".g":
                # The certificate's proof is the module `<dir>_<name>`.
                key = "gappa/" + parts[1] + "_" + name
            else:
                return None
            if key not in graph:
                return None
            modules.add(key)
    return modules


def entry_module(line):
    """The module of a `Print Assumptions Mod.name.` line, or None."""
    match = ENTRY.match(line)
    if not match:
        return None
    parts = match.group(1).split(".")
    return parts[-2] if len(parts) >= 2 else None


def module_key(name, graph):
    """The unique graph key whose file is `name`, or None."""
    keys = [k for k in graph if k.rsplit("/", 1)[-1] == name]
    return keys[0] if len(keys) == 1 else None


def select(audit_lines, base_audit_lines, graph, changed):
    """The audit's lines with the entries a change can affect; None for all.

    `changed` is the set of changed module keys. An entry is kept if its module
    is in the dependents' closure of the changed modules, or the entry line is
    new or edited against the base audit.
    """
    affected = dependents_closure(graph, changed)
    base = {line for line in base_audit_lines if ENTRY.match(line)}
    kept = []
    for line in audit_lines:
        if not line.startswith("Print Assumptions "):
            kept.append(line)
            continue
        module = entry_module(line)
        key = module_key(module, graph) if module else None
        if key is None:
            return None
        if key in affected or line not in base:
            kept.append(line)
    return kept


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--changed", required=True)
    parser.add_argument("--audit", required=True)
    parser.add_argument("--base-audit", required=True)
    parser.add_argument("--out", required=True)
    parser.add_argument("--coqdep-output", required=True)
    args = parser.parse_args()
    graph = parse_coqdep(open(args.coqdep_output).read())
    with open(args.audit) as handle:
        audit_lines = handle.read().split("\n")
    with open(args.base_audit) as handle:
        base_lines = handle.read().split("\n")
    with open(args.changed) as handle:
        paths = handle.read().split("\n")
    changed = changed_modules(paths, graph)
    kept = None if changed is None else select(audit_lines, base_lines, graph, changed)
    if kept is None:
        with open(args.out, "w") as handle:
            handle.write("\n".join(audit_lines))
        print("formal audit: everything")
        return 0
    with open(args.out, "w") as handle:
        handle.write("\n".join(kept))
    total = sum(1 for line in audit_lines if line.startswith("Print Assumptions "))
    chosen = sum(1 for line in kept if line.startswith("Print Assumptions "))
    print(f"formal audit: {chosen} of {total} entries affected by {len(changed)} changed modules")
    return 0


if __name__ == "__main__":
    sys.exit(main())
