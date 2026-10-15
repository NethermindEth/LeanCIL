import importlib.util
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
    def test_docs_only(self):
        self.assertEqual(selection.select(["README.md", "docs/design.md"]), [])

    def test_main_and_manual_always_full(self):
        for event in ("push", "workflow_dispatch"):
            self.assertEqual(selection.select(["README.md"], event), sorted(selection.suite_inputs()))

    def test_test_entry_point(self):
        self.assertEqual(selection.select(["Tests/Loops.cs"]), ["loops"])
        self.assertEqual(selection.select(["Tests/SkipInitialization.cs"]), ["unsafe"])

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
        for planned, selected, result in (
            ("success", "true", "success"), ("success", "false", "skipped"),
            ("success", "true", "failure"), ("success", "true", "cancelled"),
            ("success", "true", "skipped"), ("success", "false", "failure"),
            ("failure", "false", "skipped"), ("cancelled", "false", "skipped"),
            ("skipped", "false", "skipped"), ("success", "", "skipped"),
        ):
            env = dict(os.environ, SELECT_RESULT=planned, HAS_SUITES=selected, SUITES_RESULT=result)
            result_code = subprocess.run([bash, "-e", "-c", gate], env=env).returncode
            expected = planned == "success" and ((selected, result) in {("true", "success"), ("false", "skipped")})
            self.assertEqual(result_code == 0, expected, (planned, selected, result))


if __name__ == "__main__":
    unittest.main()
