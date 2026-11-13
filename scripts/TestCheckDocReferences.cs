#!/usr/bin/env dotnet
#:property PublishAot=false
#:include Documentation.cs

// Each stale or unshipped citation must fail the reference check with its reason, and the same
// document with the citation fixed, or addressed to maintainers where that is allowed, must pass.
var root = Path.Combine(Path.GetTempPath(), $"leancil-doc-references-{Guid.NewGuid():N}");
var checks = 0;
const string WideSource =
    "theorem wide_source : CIL.sample = 1 := rfl -- an example line wider than the documentation lets an excerpt be";
const string WrappedSource = "theorem wrapped_source : CIL.sample = 1 :=\n  rfl";
try
{
    Write("CIL/Sample.lean", """
        namespace CIL
        def sample : Nat := 1
        syntax "bind_entry " ident : command
        end CIL
        """);
    Write("Examples/Proofs/Sample.lean", $$"""
        import Extracted
        theorem sample_holds : CIL.sample = 1 := by
          rfl
        {{WideSource}}
        theorem wrapped_source : CIL.sample = 1 :=
          rfl
        """);
    Write("Tests/Fixture.lean", "def helper : Nat := 0\n");
    Write("Examples/Assembly/Methods.cs", """
        public static class Arithmetic
        {
            public static ulong Add(ulong x, ulong y) => unchecked(x + y);
            public static ulong Twice(ulong x) => x + x;
            public static ulong Twice(uint x) => x + x;
        }
        """);

    Passes("a checked snippet, an excerpt and shipped citations", """
        See `CIL/Sample.lean`, [the example](../Examples/Proofs/Sample.lean) and [`CIL.sample`](../CIL/Sample.lean).

        ```lean
        import CIL.Sample
        example : CIL.sample = 1 := rfl
        ```

        ```lean excerpt Examples/Proofs/Sample.lean
        import Extracted
        theorem sample_holds : CIL.sample = 1 := by
        ```

        ```lean extracted
        bind_entry entry := Extracted.method0 with [] from CIL.Safety.Memory.empty
        ```
        """);
    Passes("a maintainers document citing a test", """
        <!-- audience: maintainers -->

        `Tests/Fixture.lean` and [its source](../Tests/Fixture.lean) check `Tests.Fixture.helper`.
        """);

    Passes("a walkthrough of commands, their output and an edit", """
        ```sh run
        dotnet build Examples/Assembly -c Release
        leancil extract Examples/Assembly/bin/Examples.dll "Arithmetic::Add(ulong,ulong)" artifacts/Add
        ```

        ```text stdout
        Extracted 1 reachable method into artifacts/Add/Extracted.lean
        ```

        ```csharp edit Examples/Assembly/Methods.cs
        public static ulong Add(ulong x, ulong y) => unchecked(x - y);
        ```

        ```sh run fails
        leancil verify artifacts/Add
        ```

        ```text stderr
        Invalid: Lean could not prove the selected theorem.
        ```

        ```sh
        dotnet tool update --global Nethermind.LeanCIL
        ```
        """);
    Fails("a misspelt walkthrough marker", "```sh runs\nleancil list a.dll\n```", "unknown `sh` block marker");
    Fails("a misspelt output marker", "```text output\nVerified\n```", "unknown `text` block marker");
    Fails("a run block with a command the suite does not run", "```sh run\nrm -rf artifacts\n```",
        "runs only `leancil`");
    Fails("an empty run block", "```sh run\n```", "holds no command");
    Fails("an output block before any command", "```text stdout\nVerified\n```", "follows no `sh run` block");
    Fails("an edit of a file outside the examples", "```csharp edit CIL/Sample.lean\ndef a => b\n```",
        "is not a file under Examples/");
    Fails("an edit that names no member", "```csharp edit Examples/Assembly/Methods.cs\nreturn 1;\n```",
        "is not an expression-bodied member");
    Fails("an edit of a member the file does not declare",
        "```csharp edit Examples/Assembly/Methods.cs\npublic static ulong Sub(ulong x) => x;\n```",
        "is declared on 0 lines");

    // Output is compared whole, with `...` for any lines and positions and hashes named, not spelt.
    var hash = new string('a', 64);
    OutputPasses("the whole standard output", "```text stdout\nVerified: T\n  Proof: P.lean:3:0\n  Key: " +
        new string('b', 64) + "\n```", new(0, $"Verified: T\r\n  Proof: P.lean:15:2\r\n  Key: {hash}\r\n", ""));
    OutputPasses("an elided run of lines", "```text stdout\nVerified: T\n...\n  Statement:\n    x = x\n```",
        new(0, "Verified: T\n  Axioms: none\n  Report: r\n  Statement:\n    x = x\n", ""));
    OutputPasses("error lines in a row", "```text stderr\nInvalid: no\n  Stage: proof checking\n```",
        new(1, "", "Checking Proof\nInvalid: no\n  Stage: proof checking\n  Next: read\n"), fails: true);
    OutputFails("a documented line the command does not print",
        "```text stdout\nVerified: T\n  Entry: m\n  Axioms: none\n```",
        new(0, "Verified: T\n  Subject: m\n  Axioms: none\n", ""),
        "docs/Case.md:9: documented `  Entry: m`, but the command prints `  Subject: m`");
    OutputFails("a printed line the document lacks", "```text stdout\nVerified: T\n```",
        new(0, "Verified: T\n  Subject: m\n", ""), "docs/Case.md:8: the command prints more");
    OutputFails("a printed line fewer than documented", "```text stdout\nVerified: T\n  Subject: m\n```",
        new(0, "Verified: T\n", ""), "docs/Case.md:9: documented `  Subject: m`, but the command prints nothing more");
    OutputFails("lines after an elision that are not printed", "```text stdout\nVerified: T\n...\n  Report: r\n```",
        new(0, "Verified: T\n  Axioms: none\n", ""), "docs/Case.md:10: documented `  Report: r`");
    OutputFails("error lines that are not in a row",
        "```text stderr\nInvalid: no\n  Next: read\n```", new(1, "", "Invalid: no\n  Stage: s\n  Next: read\n"),
        "docs/Case.md:9: documented `  Next: read`", fails: true);
    OutputFails("a command that fails undocumented", "```text stdout\nVerified: T\n```", new(1, "", "Error: no\n"),
        "docs/Case.md:4: `leancil verify artifacts/Add` exited with 1");
    OutputFails("a command documented to fail that succeeds", "```text stdout\nVerified: T\n```",
        new(0, "Verified: T\n", ""), "is documented to fail and succeeded", fails: true);

    const string Unshipped = "Tests/ is not shipped";
    Fails("a user document citing a test path", "`Tests/Fixture.lean` shows the API.", Unshipped);
    Fails("a user document linking a test", "See [the fixture](../Tests/Fixture.lean).", Unshipped);
    Fails("a user document naming a test module", "`Tests.Fixture.helper` shows the API.", Unshipped);
    Fails("a repository link to a test",
        "See [it](https://github.com/NethermindEth/LeanCIL/blob/main/Tests/Fixture.lean).", Unshipped);
    Fails("an excerpt of a test", "```lean excerpt Tests/Fixture.lean\ndef helper : Nat := 0\n```", Unshipped);
    Fails("a missing repository path", "`CIL/Missing.lean` defines it.", "does not exist");
    Fails("a missing link target", "See [missing](Missing.md).", "does not exist");
    // Windows resolves these, but the case-sensitive CI file system does not.
    Fails("a path in another case", "`CIL/sample.lean` defines it.", "does not exist");
    Fails("a link in another case", "See [it](../cil/Sample.lean).", "does not exist");
    Fails("a placeholder path", "Paths such as `CIL/...` must exist.", "does not exist");
    Fails("a renamed heading", "## Kept heading\n\nSee [it](#removed-heading).", "names no heading");
    Passes("anchors of headings with code and repeats", """
        ## The `Kept` heading, again

        ## The `Kept` heading, again

        See [first](#the-kept-heading-again) and [second](Case.md#the-kept-heading-again-1).
        """);
    Fails("a renamed declaration", "[`CIL.removed`](../CIL/Sample.lean)", "no Lean declaration");
    Fails("a line citation", "[sample](../CIL/Sample.lean#L2)", "cites a source line");
    Fails("an unknown audience", "<!-- audience: everyone -->", "audience must be");

    const string Extraction = "needs an extraction";
    Fails("an unmarked block importing the extraction", "```lean\nimport Extracted\n```", Extraction);
    // A proof imports its method's keyed module, which exists only beside an extraction.
    Fails("an unmarked block importing a keyed extraction", "```lean\nimport Extracted.Loops_Count_0123abcd\n```",
        Extraction);
    Passes("a marked block importing a keyed extraction",
        "```lean extracted\nimport Extracted.Loops_Count_0123abcd\n```");
    Fails("an unmarked block naming the extraction",
        "```lean\nexample : Extracted.program.length = 1 := rfl\n```", Extraction);
    Fails("a variant Lean info string", "```lean4\nexample : True := trivial\n```", "info string as `lean`");
    Fails("an unknown marker","```lean maybe\nexample : True := trivial\n```", "unknown Lean block marker");
    Fails("a missing library module", "```lean\nimport CIL.Missing\n```", "names no library module");
    Fails("an unshipped module", "```lean\nimport Tests.Fixture\n```", "is not a library module");
    Fails("a removed command", "```lean illustrative\nbind_entri entry := body\n```", "is not a LeanCIL command");
    Fails("a removed command in prose", "Use `cil_removed` here.", "is not a LeanCIL command");
    Fails("an excerpt that no longer matches",
        "```lean excerpt Examples/Proofs/Sample.lean\ntheorem sample_holds : CIL.sample = 2 := by\n```",
        "is not in `Examples/Proofs/Sample.lean`");
    // An excerpt is a contiguous range of whole lines: an elided or cut line could hide a hypothesis.
    const string Drifted = "does not follow the previous ones in `Examples/Proofs/Sample.lean`";
    Fails("an excerpt out of order",
        """
        ```lean excerpt Examples/Proofs/Sample.lean
        theorem sample_holds : CIL.sample = 1 := by
        import Extracted
        ```
        """,
        Drifted);
    Fails("an excerpt eliding a line",
        "```lean excerpt Examples/Proofs/Sample.lean\nimport Extracted\n  rfl\n```", Drifted);
    Fails("an excerpt cutting a line short",
        "```lean excerpt Examples/Proofs/Sample.lean\ntheorem sample_holds : CIL.sample = 1\n```",
        "is not in `Examples/Proofs/Sample.lean`");
    Fails("an excerpt changing a line's relative indentation",
        "```lean excerpt Examples/Proofs/Sample.lean\ntheorem sample_holds : CIL.sample = 1 := by\nrfl\n```",
        Drifted);
    Fails("an excerpt inserting a blank line",
        "```lean excerpt Examples/Proofs/Sample.lean\nimport Extracted\n\n" +
        "theorem sample_holds : CIL.sample = 1 := by\n```",
        Drifted);
    Passes("a contiguous excerpt of indented lines, dedented as a block",
        "```lean excerpt Examples/Proofs/Sample.lean\n    theorem sample_holds : CIL.sample = 1 := by\n      rfl\n```");
    Passes("an excerpt of one indented line", "```lean excerpt Examples/Proofs/Sample.lean\nrfl\n```");
    Fails("an unclosed fence", "```lean\nexample : True := trivial\n", "never closed");

    // Lean style caps lines at 100 characters; an excerpt complies only once its source is wrapped.
    var atLimit = $"theorem wide : {new string('x', 100 - "theorem wide : ".Length)}";
    const string TooLong = "the Lean line has 101 characters";
    Passes("Lean lines of exactly 100 characters", $"```lean extracted\n{atLimit}\n```\n\n```lean\n{atLimit}\n```");
    Fails("an extracted Lean line over 100 characters", $"```lean extracted\n{atLimit}y\n```", TooLong);
    Fails("a checked Lean line over 100 characters", $"```lean\n{atLimit}y\n```", TooLong);
    Fails("an illustrative Lean line over 100 characters", $"```lean illustrative\n{atLimit}y\n```", TooLong);
    Fails("an excerpt of a source line over 100 characters",
        $"```lean excerpt Examples/Proofs/Sample.lean\n{WideSource}\n```", "characters; wrap it within 100");
    Passes("an excerpt of a wrapped source line",
        $"```lean excerpt Examples/Proofs/Sample.lean\n{WrappedSource}\n```");

    // A proof that unfolds the interpreter in a simp list breaks when its dispatch changes, in a
    // document as in an example; a hypothesis of the same name, and the name outside a simp list, pass.
    const string Internal = "is an evaluator internal";
    Fails("a documentation simp list naming the step function",
        "```lean extracted\nexample : True := by\n  simp [CIL.Safety.step, h]\n```",
        "`CIL.Safety.step`, which " + Internal);
    Fails("a simp only list naming an internal by its last component",
        "```lean illustrative\n  simp only [calculation,\n    checkedValue] at h\n```",
        "`checkedValue`, which " + Internal);
    Fails("a documentation simp list unfolding checked memory dispatch",
        "```lean illustrative\n  simp only [checkedAt, storeValue, memoryInstruction]\n```",
        "`checkedAt`, which " + Internal);
    ExampleFails("an example simp list unfolding monad evaluation",
        "theorem ran : True := by\n  simp only [Except.bind, Bind.bind, Pure.pure]\n#print axioms ran\n",
        "`Except.bind`, which " + Internal);
    ExampleFails("an example simp list unfolding unspecified-value checks",
        "theorem known : True := by\n  simp [CIL.Value.hasUnspecified]\n#print axioms known\n",
        "`CIL.Value.hasUnspecified`, which " + Internal);
    Passes("a simp list naming a hypothesis called step",
        "```lean illustrative\n  have step : a = b := rfl\n  simp [step]\n```");
    Passes("an internal named outside a simp list",
        "```lean illustrative\n  have ran : CIL.Safety.run program 3 0 0 args frame [] memory = result := by\n" +
        "    rw [fact]\n```");
    ExampleFails("an example simp list naming the run function",
        "theorem ran : True := by\n  simpa [run, Extracted.program] using trivial\n#print axioms ran\n", Internal);
    ExampleFails("an example theorem whose axioms are not printed",
        "theorem first : True := trivial\ntheorem second : True := trivial\n#print axioms first\n",
        "theorem `second` has no `#print axioms` line");
    ExamplePasses("an example printing each theorem's axioms and naming only facts in its simp lists",
        "theorem first : True := by\n  rw [fact]\n\n#print axioms first\n" +
        "private theorem second : True := by\n  simp [fact, Nat.add_comm]\n#print axioms second\n");

    PublicProofCheck("public semantic terms and named evidence",
        "import CIL\nexample : run program fuel method pc args frame stack memory = result := by\n" +
        "  have post := result.post\n  have formed := preserved.formed\n  exact checked\n");
    PublicProofCheck("a direct implementation import", "import CIL.Safety.SymbolicExecution\n",
        "must import only `CIL`");
    PublicProofCheck("an additional internal import", "import CIL\nimport CIL.Safety.StepComposition\n",
        "must import only `CIL`");
    PublicProofCheck("a missing public import", "example : True := trivial\n", "exactly one `import CIL`");
    PublicProofCheck("a dispatcher used outside a simp list",
        "import CIL\nexample := CIL.Safety.instruction body opcode pc args frame stack memory\n",
        "is an implementation helper");
    PublicProofCheck("an unqualified checker dependency",
        "import CIL\nexample := checkedValue value\n", "is an implementation helper");
    PublicProofCheck("two imports on one line", "import CIL\nimport CIL Lean\n", "must import only `CIL`");
    PublicProofCheck("a public fixture unfolding semantic execution",
        "import CIL\nexample : True := by simp [run]\n", "is an evaluator internal");
    PublicProofCheck("a public fixture missing its axiom check",
        "import CIL\ntheorem unchecked : True := trivial\n", "has no `#print axioms`");

    // A shell that expands a backtick escape leaves a form feed, NUL or backspace where the backtick belonged.
    ControlsPass("text with tabs, line feeds and carriage returns", "def a := 1\r\n\tdef b := 2\n");
    ControlsFail("a form feed in a docstring", "/-- Opens \f this -/\ndef a := 1\n",
        "Control.lean:1: control byte 0x0C");
    ControlsFail("a NUL on a later line", "def a := 1\n\ndef b := \0\n", "Control.lean:3: control byte 0x00");
    ControlsFail("a backspace after a carriage return", "def a := 1\r\n/-- \b -/\r\n",
        "Control.lean:2: control byte 0x08");
    Write("Control.bin", "\0");
    Write("Missing.lean", "def a := 1\n");
    File.Delete(Path.Combine(root, "Missing.lean"));
    if (Documentation.ControlCharacterProblems(root, ["Control.bin", "Missing.lean"]).Count != 0)
        throw new InvalidOperationException("A binary file or a path that is no longer on disk was reported.");
    checks++;
    Console.WriteLine("PASS binary files and removed paths are not scanned");

    // A suite the runner gained without a row would be invisible to anyone choosing what to run.
    const string Table = "## Suites\n\n| Suite | Checks |\n| --- | --- |\n";
    SuitesPass("a suite table listing every suite", Table + "| `core` | runner checks |\n| `loops` | loops |");
    SuitesFail("a suite table missing a suite", Table + "| `core` | runner checks |", "suite `loops` is missing");
    SuitesFail("a suite table naming no suite", Table + "| `core` | a |\n| `loops` | b |\n| `gone` | c |",
        "`gone` is not a suite");
    SuitesFail("a suite listed twice", Table + "| `core` | a |\n| `loops` | b |\n| `core` | c |", "listed twice");
    SuitesFail("a row under a later heading",
        Table + "| `core` | a |\n\n## Other\n\n| `loops` | b |", "suite `loops` is missing");
    SuitesFail("no suite table", "| `core` | a |\n| `loops` | b |", "no `## Suites` table");
    Console.WriteLine($"All {checks} documentation reference checks passed.");
    return 0;
}
finally
{
    if (Directory.Exists(root)) Directory.Delete(root, true);
}

void Write(string relative, string text)
{
    var path = Path.Combine(root, relative);
    Directory.CreateDirectory(Path.GetDirectoryName(path)!);
    File.WriteAllText(path, text);
}

List<string> Check(string text)
{
    Write("docs/Case.md", $"# Case\n\n{text}\n");
    var page = Documentation.Read(root, Path.Combine(root, "docs", "Case.md"));
    return Documentation.CheckReferences(root, [page]).Failures;
}

// The failures of a document running one command, with `result` as what it exits with and prints.
List<string> OutputCheck(string output, CommandResult result, bool fails)
{
    var marker = fails ? "sh run fails" : "sh run";
    Write("docs/Case.md", $"# Case\n\n```{marker}\nleancil verify artifacts/Add\n```\n\n{output}\n");
    var page = Documentation.Read(root, Path.Combine(root, "docs", "Case.md"));
    return Documentation.RunWalkthrough(page, _ => result, _ => { });
}

void OutputPasses(string name, string output, CommandResult result, bool fails = false)
{
    var failures = OutputCheck(output, result, fails);
    if (failures.Count != 0)
        throw new InvalidOperationException($"{name} was rejected:\n{string.Join('\n', failures)}");
    checks++;
    Console.WriteLine($"PASS {name}");
}

void OutputFails(string name, string output, CommandResult result, string reason, bool fails = false)
{
    var failures = OutputCheck(output, result, fails);
    if (!failures.Any(failure => failure.Contains(reason, StringComparison.Ordinal)))
        throw new InvalidOperationException($"{name} did not fail with `{reason}`:\n{string.Join('\n', failures)}");
    checks++;
    Console.WriteLine($"PASS {name} fails");
}

void Passes(string name, string text)
{
    var failures = Check(text);
    if (failures.Count != 0)
        throw new InvalidOperationException($"{name} was rejected:\n{string.Join('\n', failures)}");
    checks++;
    Console.WriteLine($"PASS {name}");
}

List<string> SuiteCheck(string text)
{
    Write(Documentation.SuiteDocument, $"# Validation\n\n{text}\n");
    var page = Documentation.Read(root, Path.Combine(root, Documentation.SuiteDocument));
    return Documentation.CheckSuiteTable(root, page, ["core", "loops"]);
}

void SuitesPass(string name, string text)
{
    var failures = SuiteCheck(text);
    if (failures.Count != 0)
        throw new InvalidOperationException($"{name} was rejected:\n{string.Join('\n', failures)}");
    checks++;
    Console.WriteLine($"PASS {name}");
}

void SuitesFail(string name, string text, string reason)
{
    var failures = SuiteCheck(text);
    if (!failures.Any(failure => failure.Contains(reason, StringComparison.Ordinal)))
        throw new InvalidOperationException($"{name} did not fail with `{reason}`:\n{string.Join('\n', failures)}");
    checks++;
    Console.WriteLine($"PASS {name} fails");
}

List<string> ControlCheck(string text)
{
    Write("Control.lean", text);
    return Documentation.ControlCharacterProblems(root, ["Control.lean"]);
}

void ControlsPass(string name, string text)
{
    var failures = ControlCheck(text);
    if (failures.Count != 0)
        throw new InvalidOperationException($"{name} was rejected:\n{string.Join('\n', failures)}");
    checks++;
    Console.WriteLine($"PASS {name}");
}

void ControlsFail(string name, string text, string reason)
{
    var failures = ControlCheck(text);
    if (!failures.Any(failure => failure.Contains(reason, StringComparison.Ordinal)))
        throw new InvalidOperationException($"{name} did not fail with `{reason}`:\n{string.Join('\n', failures)}");
    checks++;
    Console.WriteLine($"PASS {name} fails");
}

// The failures of one example proof beside the fixtures; the others print their axioms.
List<string> ExampleCheck(string text)
{
    Write($"{Documentation.ExampleProofs}/Linted.lean", text);
    var failures = Documentation.CheckExamples(root)
        .Where(failure => failure.StartsWith($"{Documentation.ExampleProofs}/Linted.lean:", StringComparison.Ordinal))
        .ToList();
    File.Delete(Path.Combine(root, Documentation.ExampleProofs, "Linted.lean"));
    return failures;
}

void ExamplePasses(string name, string text)
{
    var failures = ExampleCheck(text);
    if (failures.Count != 0)
        throw new InvalidOperationException($"{name} was rejected:\n{string.Join('\n', failures)}");
    checks++;
    Console.WriteLine($"PASS {name}");
}

void ExampleFails(string name, string text, string reason)
{
    var failures = ExampleCheck(text);
    if (!failures.Any(failure => failure.Contains(reason, StringComparison.Ordinal)))
        throw new InvalidOperationException($"{name} did not fail with `{reason}`:\n{string.Join('\n', failures)}");
    checks++;
    Console.WriteLine($"PASS {name} fails");
}

void Fails(string name, string text, string reason)
{
    var failures = Check(text);
    if (!failures.Any(failure => failure.Contains(reason, StringComparison.Ordinal)))
        throw new InvalidOperationException($"{name} did not fail with `{reason}`:\n{string.Join('\n', failures)}");
    checks++;
    Console.WriteLine($"PASS {name} fails");
}

// The source boundary complements elaboration, which checks the actual continuation and goal forms.
void PublicProofCheck(string name, string source, string? reason = null)
{
    Write(Documentation.PublicProofFixture, source);
    var failures = Documentation.CheckExamples(root)
        .Where(failure => failure.StartsWith(Documentation.PublicProofFixture + ":", StringComparison.Ordinal))
        .ToList();
    File.Delete(Path.Combine(root, Documentation.PublicProofFixture));
    var accepted = reason is null ? failures.Count == 0 :
        failures.Any(failure => failure.Contains(reason, StringComparison.Ordinal));
    if (!accepted)
        throw new InvalidOperationException($"{name} had unexpected diagnostics:\n{string.Join('\n', failures)}");
    checks++;
    Console.WriteLine($"PASS {name}");
}
