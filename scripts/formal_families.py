#!/usr/bin/env python3
"""Own formal checks once and derive their build/selection closures with coqdep.

The public and internal extraction drivers intentionally remain composite units.
This planner never infers Coq dependencies from Rust paths or theorem names.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

from formal_affected import parse_coqdep

KERNELS = ("fast", "exp", "ln", "erfcx", "normal", "asin", "asinh", "atan2", "bivariate", "trig")
CERTIFICATE_FAMILIES = {"exp2": "exp", "expm1": "exp", "log2": "ln"}
BASES = ("double-word", "two-prod", "binary64", "q")
EXTRACTIONS = {
    "Crosscheck": ("crosscheck", "driver.ml"),
    "InternalCrosscheck": ("internal-crosscheck", "internaldriver.ml"),
    "BvnCrosscheck": ("bivariate", "bvndriver.ml"),
}
MAPPINGS = ["-R", "double-word", "Double", "-R", "two-prod", "",
            "-R", "binary64", "Binary64", "-R", "q", "Q", "-R", "gappa", "",
            "-R", "audit", "", "-R", "extraction", ""]


def uncomment(text):
    """Coq comments nest; a regexp deleting through the first terminator cannot."""
    parts = re.split(r"(\(\*|\*\))", text)
    depth = 0
    result = []
    for part in parts:
        if part == "(*":
            depth += 1
        elif part == "*)":
            depth -= 1
            if depth < 0:
                raise ValueError("unmatched Coq comment terminator")
            if not depth:
                result.append(" ")
        elif not depth:
            result.append(part)
    if depth:
        raise ValueError("unterminated Coq comment")
    return "".join(result)


def audit_entries(text):
    """Accept only imports and explicit, qualified Print Assumptions commands."""
    statements = re.split(r"\.(?=\s|$)", uncomment(text))
    entries = []
    for statement in statements:
        statement = " ".join(statement.split())
        if not statement:
            continue
        match = re.fullmatch(r"Print Assumptions ([A-Za-z0-9_'.]+)", statement)
        if match:
            entries.append(match[1])
        elif not re.fullmatch(r"(?:From [\w.]+ )?Require (?:Import |Export )?[\w. ]+", statement):
            raise ValueError(f"unsupported audit statement: {statement}")
    # Preserve multiplicity: the canonical audit currently repeats some
    # theorems. Partitioning must preserve its report count, not deduplicate it.
    return entries


def closure(graph, roots):
    seen = set()
    pending = list(roots)
    while pending:
        key = pending.pop()
        if key in seen:
            continue
        if key not in graph:
            raise ValueError(f"coqdep did not resolve local module {key}")
        seen.add(key)
        # coqdep also reports absolute paths for installed libraries. Those
        # belong to the pinned toolchain, never to a project family.
        pending.extend(dep for dep in graph[key] if not Path(dep).is_absolute())
    return seen


def logical_name(key):
    directory, name = key.rsplit("/", 1)
    prefix = {"double-word": "Double.", "binary64": "Binary64.", "q": "Q."}.get(directory, "")
    return prefix + name


def make_plan(root, src, graph):
    owners = {}
    origins = {}

    def own(key, family, origin):
        if key in owners:
            raise ValueError(f"ambiguous module ownership: {key}")
        if key not in graph:
            raise ValueError(f"missing coqdep module: {key}")
        owners[key] = family
        origins[key] = origin

    for directory in BASES:
        for file in sorted((root / "formal" / directory).glob("*.v")):
            own(f"{directory}/{file.stem}", "shared", str(file.relative_to(root)))
    own("gappa/Hints", "shared", "formal/gappa/Hints.v")
    for family in KERNELS:
        for file in sorted((root / "formal" / family).glob("*.v")):
            own(f"gappa/{file.stem}", family, str(file.relative_to(root)))
    certificates = []
    for file in sorted((root / "formal").glob("*/*.g")):
        directory = file.parent.name
        family = CERTIFICATE_FAMILIES.get(directory, directory)
        if family not in KERNELS and family not in BASES:
            raise ValueError(f"unowned certificate: {file}")
        key = f"gappa/{directory}_{file.stem}"
        own(key, family if family in KERNELS else "shared", str(file.relative_to(root)))
        certificates.append(key)
    own("audit/Audit", "shared", "formal/audit/Audit.v")
    for module, (family, _) in EXTRACTIONS.items():
        own(f"extraction/{module}", family, f"formal/extraction/{module}.v")
    expected_extractions = {f"{module}.v" for module in EXTRACTIONS}
    if {p.name for p in (root / "formal/extraction").glob("*.v")} != expected_extractions:
        raise ValueError("extraction ownership is incomplete")
    generated_audits = {"gappa/KernelAudit", "gappa/CertificateAudit"}
    if set(graph) != set(owners) | generated_audits:
        raise ValueError(f"unowned or missing modules: {sorted(set(graph) ^ (set(owners) | generated_audits))}")

    families = {name: dict(roots=[], kernel_entries=[], kernel_imports=[], certificates=[], extractions=[])
                for name in sorted(set(owners.values()))}
    for key, family in owners.items():
        families[family]["roots"].append(key)
    entries = audit_entries((src / "gappa/KernelAudit.v").read_text())
    for entry in entries:
        module = entry.rsplit(".", 1)[0]
        candidates = [key for key in owners if module in (logical_name(key), key.rsplit("/", 1)[-1])]
        if len(candidates) != 1:
            raise ValueError(f"unowned or ambiguous audit entry: {entry}")
        families[owners[candidates[0]]]["kernel_entries"].append(entry)
        families[owners[candidates[0]]]["kernel_imports"].append(logical_name(candidates[0]))
    for key in certificates:
        families[owners[key]]["certificates"].append(key)
    if Counter(audit_entries((src / "gappa/CertificateAudit.v").read_text())) != Counter(
            logical_name(key) + ".l1" for key in certificates):
        raise ValueError("certificate audit does not cover every generated certificate")
    for module, (family, driver) in EXTRACTIONS.items():
        families[family]["extractions"].append(dict(module=module, driver=driver))
    if Counter(x for f in families.values() for x in f["kernel_entries"]) != Counter(entries):
        raise ValueError("family audits do not partition the complete kernel audit")
    controls = ["scripts/check_formal.sh", "scripts/formal_families.py", "scripts/formal_affected.py",
                ".cargo/coq-image", ".cargo/coq-packages", "scripts/formal_deps.sh"]
    controls += [str(p.relative_to(root)) for p in sorted((root / "formal").glob("axioms*.expected"))]
    for name, family in families.items():
        keys = closure(graph, family["roots"])
        family["closure"] = sorted(keys)
        family["sources"] = sorted({origins[key] for key in keys})
        family["base_audit"] = name == "shared"
        family["kernel_imports"] = sorted(set(family["kernel_imports"]))
        digest = hashlib.sha256()
        inputs = {f"assembled/{key}.v": (src / f"{key}.v").read_bytes() for key in keys}
        inputs.update({path: (root / path).read_bytes() for path in controls})
        for extraction in family["extractions"]:
            path = "formal/extraction/" + extraction["driver"]
            family["sources"].append(path)
            inputs[path] = (root / path).read_bytes()
        inputs["kernel-audit-entries"] = json.dumps(family["kernel_entries"]).encode()
        for path, data in sorted(inputs.items()):
            digest.update(path.encode() + b"\0" + hashlib.sha256(data).digest())
        family["cache_key"] = digest.hexdigest()
    return dict(version=1, families=families, kernel_entries=len(entries),
                # The base audit is kept intact (including any local helper
                # definitions); its Coq output and exact axiom set remain the
                # authority. Match the full gate's existing report counter.
                base_entries=len(re.findall(r"(?m)^Print Assumptions", (src / "audit/Audit.v").read_text())),
                certificates=len(certificates), extractions=sorted(EXTRACTIONS))


def select(plan, paths):
    """Only known family proof/certificate paths narrow selection; else all."""
    families = plan["families"]
    if paths is None:
        return sorted(families)
    selected = set()
    known = {p for family in families.values() for p in family["sources"]}
    for path in paths:
        if not path:
            continue
        parts = Path(path).parts
        # A binding manifest is checked globally even in a selected run.
        if path == "formal/binding.sha256":
            continue
        if len(parts) == 3 and parts[0] == "formal" and parts[1] in (*KERNELS, *CERTIFICATE_FAMILIES) and path in known:
            selected.update(name for name, family in families.items() if path in family["sources"])
        else:
            return sorted(families)
    # A manifest-only or empty/renamed change must not create a green empty gate.
    return sorted(selected or families)


def apply_family(plan, family, src):
    unit = plan["families"][family]
    mappings = [line for line in (src / "_CoqProject").read_text().splitlines() if line.startswith("-")]
    files = [key + ".v" for key in unit["closure"] if not key.startswith(("audit/", "extraction/"))]
    (src / "_CoqProject").write_text("\n".join(mappings + files) + "\n")
    for name, entries in [("KernelAudit", unit["kernel_entries"]),
                          ("CertificateAudit", [logical_name(k) + ".l1" for k in unit["certificates"]])]:
        imports = unit["kernel_imports"] if name == "KernelAudit" else sorted({entry.rsplit(".", 1)[0] for entry in entries})
        body = [f"Require {module}." for module in imports]
        body += [f"Print Assumptions {entry}." for entry in entries]
        (src / f"gappa/{name}.v").write_text("\n".join(body) + "\n")
    if not unit["base_audit"]:
        (src / "audit/Audit.v").unlink()
    keep = {e["module"] for e in unit["extractions"]}
    for module in EXTRACTIONS:
        if module not in keep:
            (src / f"extraction/{module}.v").unlink()
    retained = set(unit["closure"]) | {"gappa/KernelAudit", "gappa/CertificateAudit"}
    for path in src.rglob("*.v"):
        if str(path.relative_to(src).with_suffix("")) not in retained:
            path.unlink()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--src", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--changed", type=Path)
    parser.add_argument("--family")
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--internal-corpus", type=Path, required=True)
    args = parser.parse_args()
    src, root = args.src.resolve(), args.root.resolve()
    files = sorted(str(p.relative_to(src)) for p in src.rglob("*.v"))
    result = subprocess.run(["coqdep", *MAPPINGS, *files], cwd=src, text=True, capture_output=True, check=True)
    if result.stderr.strip():
        raise ValueError(f"coqdep did not produce a clean dependency graph: {result.stderr}")
    plan = make_plan(root, src, parse_coqdep(result.stdout))
    plan["inputs"] = {"binding": hashlib.sha256((root / "formal/binding.sha256").read_bytes()).hexdigest(),
                      "public": hashlib.sha256(args.corpus.read_bytes()).hexdigest(),
                      "internal": hashlib.sha256(args.internal_corpus.read_bytes()).hexdigest()}
    plan["selected"] = select(plan, args.changed.read_text().splitlines() if args.changed else None)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(plan, indent=2) + "\n")
    if args.family:
        if args.family not in plan["families"]:
            parser.error(f"unknown family {args.family}")
        apply_family(plan, args.family, src)
    print("formal families: " + ", ".join(plan["selected"]))


if __name__ == "__main__":
    main()
