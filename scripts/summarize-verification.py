#!/usr/bin/env python3
"""Summarize completed verification stages while retaining every original record."""

import argparse
from collections import defaultdict
import html
import json
import math
import os
from pathlib import Path


def collect(root):
    records = []
    for path in sorted(root.rglob("*.jsonl")):
        for line_number, line in enumerate(path.read_text(encoding="utf-8-sig").splitlines(), 1):
            if not line.strip():
                continue
            try:
                record = json.loads(line)
                duration = record["durationSeconds"]
                valid = (isinstance(duration, (int, float)) and not isinstance(duration, bool)
                         and math.isfinite(duration) and duration >= 0
                         and isinstance(record["exitCode"], int) and not isinstance(record["exitCode"], bool)
                         and isinstance(record["stage"], str) and isinstance(record["transcript"], str)
                         and (record.get("suite") is None or isinstance(record["suite"], str))
                         and isinstance(record["command"], list)
                         and all(isinstance(part, str) for part in record["command"]))
                if not valid:
                    raise ValueError("Invalid stage record")
            except (ValueError, KeyError, TypeError) as error:
                raise ValueError(f"{path}:{line_number}: invalid timing record: {error}") from error
            records.append({**record, "suite": record.get("suite") or "local",
                            "traceFile": path.relative_to(root).as_posix(), "traceLine": line_number})
    return records


def summarize(records):
    groups = defaultdict(lambda: {"count": 0, "durationSeconds": 0.0, "maxSeconds": 0.0, "failures": 0})
    for record in records:
        group = groups[(record["suite"], record["stage"])]
        group["count"] += 1
        group["durationSeconds"] += record["durationSeconds"]
        group["maxSeconds"] = max(group["maxSeconds"], record["durationSeconds"])
        group["failures"] += record["exitCode"] != 0
    return sorted(({"suite": suite, "stage": stage, **group} for (suite, stage), group in groups.items()),
                  key=lambda group: (-group["durationSeconds"], group["suite"], group["stage"]))


def markdown(groups, count):
    def cell(value):
        return html.escape(value).replace("|", "\\|").replace("\n", " ").replace("\r", " ")

    lines = ["## Verification stage timings", "",
             f"{count} completed stages. Durations are inclusive: parent suite commands overlap child stages, "
             "so these totals must not be added to estimate wall time.", "",
             "Full command transcripts and all timing records are retained in the verification artifacts. Combined reports include retained rerun attempts; each record identifies its source artifact."]
    if groups:
        lines += ["", "Longest accumulated stages (up to 20):", "",
                  "| Suite | Stage | Calls | Inclusive seconds | Longest call | Nonzero exits |",
                  "| --- | --- | ---: | ---: | ---: | ---: |"]
        for group in groups[:20]:
            lines.append(f"| {cell(group['suite'])} | {cell(group['stage'])} | {group['count']} | "
                         f"{group['durationSeconds']:.1f} | {group['maxSeconds']:.1f} | {group['failures']} |")
        lines += ["", "Nonzero exits include intentionally rejected negative tests; the suite job result determines success."]
    else:
        lines += ["", "No completed stage timings were available; inspect the job log and any partial transcripts."]
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--markdown", type=Path, required=True)
    parser.add_argument("--github-summary", action="store_true")
    args = parser.parse_args()
    records = collect(args.root)
    groups = summarize(records)
    report = markdown(groups, len(records))
    for path in (args.output, args.markdown):
        path.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"durationSemantics": "inclusive, possibly overlapping", "stages": groups,
                                      "records": records}, indent=2) + "\n", encoding="utf-8")
    args.markdown.write_text(report, encoding="utf-8")
    if args.github_summary and os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as stream:
            stream.write(report)
    print(f"Recorded {len(records)} completed stages in {args.output}")


if __name__ == "__main__":
    main()
