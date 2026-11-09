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

void Fails(string name, string text, string reason)
{
    var failures = Check(text);
    if (!failures.Any(failure => failure.Contains(reason, StringComparison.Ordinal)))
        throw new InvalidOperationException($"{name} did not fail with `{reason}`:\n{string.Join('\n', failures)}");
    checks++;
    Console.WriteLine($"PASS {name} fails");
}
