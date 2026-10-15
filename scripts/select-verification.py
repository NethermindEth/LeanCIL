#!/usr/bin/env python3
"""Conservative PR suite selection; shared or unknown inputs run every suite."""

import argparse
import json
import math
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def schedule(suites, root=ROOT):
    """Start the measured longest jobs first; never remove or duplicate a suite."""
    data = json.loads((root / "scripts/verification-durations.json").read_text(encoding="utf-8"))
    durations = data["seconds"]
    if not durations or any(not isinstance(value, (int, float)) or isinstance(value, bool)
                            or not math.isfinite(value) or value <= 0
                            for value in durations.values()):
        raise ValueError("Suite durations must be positive numbers")
    # New suites have no measured duration. Run them first instead of silently
    # putting an unknown potentially long job at the tail of the queue.
    return sorted(suites, key=lambda name: (-durations.get(name, max(durations.values()) + 1), name))


def suite_inputs(root=ROOT):
    runner = (root / "scripts/Test.cs").read_text(encoding="utf-8")
    entries = dict(re.findall(r'\["([a-z]+)"\] = \("(Tests/[^"\n]+\.cs)"', runner))
    if not entries or "unsafe" not in entries:
        raise ValueError("Could not read verification suite registry")
    inputs = {name: {path} for name, path in entries.items()}
    inputs["core"] = {
        "Examples/Verify.cs", "Examples/Hardware/Hardware.cs", "scripts/Verify.cs",
        "Tests/LibraryCache.cs", "Tests/InitializedTypes.cs", "Tests/ConsumerVerification.cs",
        "Tests/MethodSelectors.cs", "Tests/MetadataMutator.cs", "Tests/Semantics.lean",
        "Tests/Automation.lean", "Tests/BatchVerification.cs", "Tests/VerificationCache.cs",
        "Tests/VerificationReuse.cs",
    }
    inputs["core"].update(f"Examples/Proofs/{name}.lean" for name in (
        "Add", "Choose", "Calls", "Alias", "Struct", "StructCopy", "LargeStruct",
        "PastEnd", "WrongAdd", "Escape", "Hardware", "StaticData"))
    inputs["evidence"].update(f"Tests/{name}.cs" for name in (
        "LayoutEvidence", "ParameterEvidence", "GenericEvidence", "FeatureEvidence", "TranslationAudit"))
    inputs["evidence"].update(f"Tests/{name}.lean" for name in (
        "ExtractionLayout", "ExtractionParameters", "FeatureEvidence", "LayoutCoverage"))
    inputs["unsafe"].add("Tests/SkipInitialization.cs")

    # Follow literal source paths, file-based includes and Lean imports. Dynamic
    # or new paths absent from this graph fall back to the full matrix below.
    for paths in inputs.values():
        pending = list(paths)
        while pending:
            path = pending.pop()
            source = root / path
            if not source.is_file():
                continue
            text = source.read_text(encoding="utf-8")
            references = set(re.findall(r'"((?:Tests|Examples)/[^"{}\n]+\.(?:cs|lean))"', text))
            for pattern in re.findall(r'"(Examples/Proofs/[^"\n]*\{[^"\n]+\.lean)"', text):
                # A dynamically selected proof may be used without a literal path.
                # Include all matches rather than guessing C# runtime values.
                glob = re.sub(r'\{[^}]+\}', '*', pattern)
                references.update(path.relative_to(root).as_posix() for path in root.glob(glob))
            references.update(name.replace(".", "/") + ".lean"
                              for name in re.findall(r'^import\s+([\w.]+)', text, re.MULTILINE))
            references.update(name.replace(".", "/") + ".lean"
                              for name in re.findall(r'"(Tests\.[\w.]+)"', text))
            for relative in re.findall(r'^#:include\s+(\S+)', text, re.MULTILINE):
                references.add((source.parent / relative).resolve().relative_to(root.resolve()).as_posix())
            for reference in references - paths:
                paths.add(reference)
                pending.append(reference)
    return inputs


def select(paths, event="pull_request", root=ROOT):
    inputs = suite_inputs(root)
    all_suites = sorted(inputs)
    if event != "pull_request":
        return all_suites
    selected = set()
    for path in paths:
        # Documentation cannot change compiled code or the verification runner.
        if path.endswith(".md") or path == "LICENSE":
            continue
        # Every suite compiles the shared fixture project and consumes the framework.
        if path.startswith(("CIL/", "Extractor/", "Examples/Assembly/", "Examples/FSharp/")) or path == "Examples/Support.lean":
            return all_suites
        owners = {suite for suite, files in inputs.items() if path in files}
        if not owners:
            return all_suites
        selected.update(owners)
    return sorted(selected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--event", required=True)
    parser.add_argument("--base")
    parser.add_argument("--head")
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    paths = []
    if args.event == "pull_request":
        if not args.base or not args.head:
            parser.error("PR selection requires base and head commits")
        # Include both sides of renames/deletions; use the PR merge-base diff.
        changed = subprocess.check_output(
            ["git", "diff", "--name-only", "--no-renames", "-z", f"{args.base}...{args.head}"], cwd=ROOT)
        paths = [path for path in changed.decode("utf-8").split("\0") if path]
    suites = schedule(select(paths, args.event))
    print(json.dumps({"changed": paths, "suites": suites}, indent=2))
    with open(args.output, "a", encoding="utf-8") as output:
        # GitHub validates the matrix even when its job is skipped.
        output.write("matrix=" + json.dumps({"suite": suites or ["core"]}) + "\n")
        output.write("has-suites=" + str(bool(suites)).lower() + "\n")


if __name__ == "__main__":
    main()
