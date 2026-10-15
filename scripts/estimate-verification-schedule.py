#!/usr/bin/env python3
"""Compare queue schedules using recorded job durations, without running or skipping tests."""

import heapq
import json
from pathlib import Path


def elapsed(order, durations, workers):
    available = [0] * workers
    for suite in order:
        heapq.heapreplace(available, available[0] + durations[suite])
    return max(available)


def main():
    measured = json.loads(Path(__file__).with_name("verification-durations.json").read_text(encoding="utf-8"))
    durations = measured["seconds"]
    alphabetical = sorted(durations)
    longest = sorted(durations, key=lambda suite: (-durations[suite], suite))
    print(json.dumps({
        "measurementRun": measured["workflowRun"],
        "assumptions": "Fixed measured job durations; immediate dispatch when a worker is free. "
                       "Excludes the new preparation job, artifact transfer, runner queueing and library-reuse savings. "
                       "This is a scheduling estimate, not a measured optimized workflow run.",
        "suiteCount": len(durations), "totalMeasuredJobSeconds": sum(durations.values()),
        "estimatedSeconds": {
            "alphabetical4": elapsed(alphabetical, durations, 4),
            **{f"longestFirst{workers}": elapsed(longest, durations, workers) for workers in (4, 8, 12)},
        },
        "order": longest,
    }, indent=2))


if __name__ == "__main__":
    main()
