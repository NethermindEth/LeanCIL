import importlib.util
import heapq
import itertools
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import textwrap
import unittest

spec = importlib.util.spec_from_file_location("selection", Path(__file__).with_name("select-verification.py"))
selection = importlib.util.module_from_spec(spec)
spec.loader.exec_module(selection)


class SelectionTests(unittest.TestCase):
    def test_longest_first_preserves_selection(self):
        selected = selection.select(["Tests/Loops.cs", "Tests/UnsafeLayouts.cs", "Tests/IntegerMath.cs"])
        self.assertEqual(selection.schedule(selected), ["unsafe", "math", "loops"])
        self.assertEqual(set(selection.schedule(selection.suite_inputs())), set(selection.suite_inputs()))
        self.assertEqual(selection.schedule(["loops", "newlongsuite"]), ["newlongsuite", "loops"])
        self.assertEqual(selection.schedule([]), [])

    def test_measured_schedule_reduces_estimated_tail_without_skipping_jobs(self):
        durations = json.loads((selection.ROOT / "scripts/verification-durations.json").read_text())["seconds"]
        def makespan(order, workers):
            available = [0] * workers
            for name in order:
                heapq.heapreplace(available, available[0] + durations[name])
            return max(available)
        old = makespan(sorted(selection.suite_inputs()), 4)
        new = makespan(selection.schedule(selection.suite_inputs()), 8)
        self.assertLess(new, old)

    def test_docs_only(self):
        self.assertEqual(selection.select(["README.md", "docs/design.md"]), [])

    def test_main_and_manual_always_full(self):
        for event in ("push", "workflow_dispatch"):
            self.assertEqual(selection.select(["README.md"], event), sorted(selection.suite_inputs()))

    def test_test_entry_point(self):
        self.assertEqual(selection.select(["Tests/Loops.cs"]), ["loops"])
        self.assertEqual(selection.select(["Tests/SkipInitialization.cs"]), ["unsafe"])
        self.assertEqual(selection.select(["Tests/BatchVerification.cs"]), ["core"])
        self.assertEqual(selection.select(["Tests/VerificationCache.cs"]), ["core"])
        self.assertEqual(selection.select(["Tests/VerificationReuse.cs"]), ["core"])

    def test_proof_and_transitive_import(self):
        self.assertEqual(selection.select(["Examples/Proofs/Countdown.lean"]), ["contracts", "fsharp", "loops"])
        self.assertEqual(selection.select(["Examples/Support.lean"]), sorted(selection.suite_inputs()))
        self.assertEqual(selection.select(["Tests/SkipInitEvidence.lean"]), ["unsafe"])

    def test_dynamic_proof_paths(self):
        self.assertIn("integer", selection.select(["Examples/Proofs/Negate64.lean"]))
        self.assertIn("contracts", selection.select(["Examples/Proofs/GenericIdentity.lean"]))
        self.assertIn("fsharp", selection.select(["Examples/Proofs/ConstructorValue.lean"]))

    def test_shared_unknown_and_workflow(self):
        for path in ("CIL/Safety/Memory.lean", "Extractor/UnsafeModels.cs", "global.json",
                     "Examples/Assembly/SkipInitialization.cs", "Tests/NewTest.cs",
                     ".github/workflows/verification.yml", "scripts/select-verification.py"):
            self.assertEqual(selection.select([path]), sorted(selection.suite_inputs()), path)

    def test_multiple_changes_and_deleted_paths(self):
        self.assertEqual(selection.select(["README.md", "Tests/Loops.cs", "Tests/Division.cs"]),
                         ["division", "loops"])
        self.assertEqual(selection.select(["Tests/Deleted.cs"]), sorted(selection.suite_inputs()))

    def test_every_registered_suite_has_its_entry_point(self):
        runner = (selection.ROOT / "scripts/Test.cs").read_text(encoding="utf-8")
        accepted = re.search(r'\["--suite", (.*?)\] =>', runner).group(1)
        self.assertEqual(set(re.findall(r'"([a-z]+)"', accepted)) - {"all"}, set(selection.suite_inputs()))
        for suite, inputs in selection.suite_inputs().items():
            self.assertTrue(inputs, suite)

    def test_required_gate(self):
        bash = "C:/Program Files/Git/bin/bash.exe" if os.name == "nt" else shutil.which("bash")
        if not bash or not Path(bash).is_file():
            self.skipTest("bash is required to test the workflow gate")
        workflow = (selection.ROOT / ".github/workflows/verification.yml").read_text(encoding="utf-8")
        gate = textwrap.dedent(workflow.rsplit("        run: |\n", 1)[1])
        statuses = ("success", "failure", "cancelled", "skipped")
        for planned, selected, prepared, result in itertools.product(statuses, ("true", "false", ""), statuses, statuses):
            env = dict(os.environ, SELECT_RESULT=planned, HAS_SUITES=selected, PREPARE_RESULT=prepared, SUITES_RESULT=result)
            result_code = subprocess.run([bash, "-e", "-c", gate], env=env).returncode
            expected = planned == "success" and ((selected, prepared, result) in {
                ("true", "success", "success"), ("false", "skipped", "skipped")})
            self.assertEqual(result_code == 0, expected, (planned, selected, prepared, result))

    def test_same_run_certified_library_binding_and_observability(self):
        workflow = (selection.ROOT / ".github/workflows/verification.yml").read_text(encoding="utf-8")
        self.assertIn("needs: [select, prepare]", workflow)
        self.assertIn("needs: [select, prepare, suites]", workflow)
        self.assertEqual(workflow.count("name: certified-library-${{ github.run_id }}-${{ github.run_attempt }}"), 1)
        self.assertIn("LEANCIL_CERTIFIED_LIBRARY_SHA256: ${{ needs.prepare.outputs.manifest-sha256 }}", workflow)
        self.assertIn("artifact-ids: ${{ needs.prepare.outputs.artifact-id }}", workflow)
        self.assertIn("artifact-id: ${{ steps.library-artifact.outputs.artifact-id }}", workflow)
        self.assertIn("name: verification-results-${{ matrix.suite }}-${{ github.run_attempt }}", workflow)
        self.assertIn("include-hidden-files: true", workflow)
        self.assertIn("max-parallel: 8", workflow)
        self.assertIn("artifacts/verification-traces/", workflow)


if __name__ == "__main__":
    unittest.main()
