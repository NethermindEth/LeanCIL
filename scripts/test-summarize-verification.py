import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("timings", Path(__file__).with_name("summarize-verification.py"))
timings = importlib.util.module_from_spec(spec)
spec.loader.exec_module(timings)


class TimingTests(unittest.TestCase):
    def record(self, stage="Proof", seconds=2, exit_code=0, suite="loops"):
        return {"stage": stage, "durationSeconds": seconds, "exitCode": exit_code,
                "suite": suite, "transcript": "command.log", "command": ["lean", "Proof.lean"]}

    def test_preserves_all_records_and_aggregates_by_suite_and_stage(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            values = [self.record(), self.record(seconds=3, exit_code=1), self.record(suite="core")]
            (root / "stages.jsonl").write_text("\n".join(map(json.dumps, values)), encoding="utf-8")
            records = timings.collect(root)
            self.assertEqual(len(records), 3)
            self.assertEqual([record["command"] for record in records], [["lean", "Proof.lean"]] * 3)
            self.assertEqual(records[1]["traceLine"], 2)
            groups = timings.summarize(records)
            self.assertEqual((groups[0]["suite"], groups[0]["durationSeconds"], groups[0]["failures"]), ("loops", 5, 1))

    def test_nested_stages_do_not_claim_wall_time(self):
        groups = timings.summarize([self.record("Suite loops", 20), self.record("Proof", 10)])
        report = timings.markdown(groups, 2)
        self.assertIn("overlap", report)
        self.assertIn("must not be added", report)
        self.assertIn("intentionally rejected", report)

    def test_missing_stages_are_not_reported_as_success(self):
        self.assertIn("No completed stage timings", timings.markdown([], 0))

    def test_corrupt_or_invalid_records_fail_explicitly(self):
        for value in ("{", json.dumps(self.record(seconds=-1)), json.dumps(self.record(seconds=float("nan"))),
                      json.dumps(self.record(seconds=True)), json.dumps({"stage": "Proof"})):
            with self.subTest(value=value), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "stages.jsonl").write_text(value, encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "stages.jsonl:1"):
                    timings.collect(root)

    def test_summary_is_bounded_without_dropping_structured_stages(self):
        records = [self.record(stage=f"Proof {index}") for index in range(40)]
        groups = timings.summarize(records)
        self.assertEqual(len(groups), 40)
        self.assertEqual(timings.markdown(groups, 40).count("| loops |"), 20)


if __name__ == "__main__":
    unittest.main()
