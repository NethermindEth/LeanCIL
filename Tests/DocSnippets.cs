#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/Documentation.cs

using System.Diagnostics;

// Every unmarked Lean block in the documentation must elaborate with exactly its own imports, and every
// library name the rest of the documentation cites must still exist; a stale copy must fail at its line.
// Every `sh run` command must exit as documented and print the output documented below it.
using var verification = new Program();
var output = At("artifacts/DocSnippets");
Directory.CreateDirectory(output);
var leanPath = verification.CheckoutLeanPath();

// The diagnostics of the snippet and name batches for the documents under `root`, by document line.
// Each import set is its own Lean process, so the batches run concurrently.
List<string> Elaborate(string root, string name, out int snippets, out int names)
{
    var pages = Documentation.Documents(root).Select(path => Documentation.Read(root, path)).ToArray();
    var snippetBatches = Documentation.Snippets(pages);
    var nameBatch = Documentation.Names(Root, pages);
    var batches = snippetBatches.Select((batch, index) => ($"{name}Snippets{index}", batch))
        .Append(($"{name}Names", nameBatch)).ToArray();
    foreach (var stale in Directory.EnumerateFiles(output, $"{name}*.lean")) File.Delete(stale);
    var results = batches.AsParallel().AsOrdered().WithDegreeOfParallelism(Environment.ProcessorCount)
        .Select(entry =>
        {
            var path = Path.Combine(output, $"{entry.Item1}.lean");
            File.WriteAllText(path, entry.Item2.Text);
            var result = Execute([verification.LeanExecutable, path], leanPath: leanPath);
            var found = Documentation.Diagnostics(entry.Item2, Documentation.Relative(Root, path), result.Output);
            if (result.Code != 0 && found.Count == 0) found.Add($"Lean exited with {result.Code}: {result.Output}");
            return found;
        }).ToArray();
    (snippets, names) = (snippetBatches.Sum(batch => batch.Count), nameBatch.Count);
    return results.SelectMany(found => found).ToList();
}

var elapsed = Stopwatch.StartNew();
var failures = Elaborate(Root, "Documentation", out var snippets, out var names);
if (failures.Count != 0)
{
    Console.Error.WriteLine($"Documentation snippets that do not elaborate ({failures.Count}):");
    foreach (var failure in failures) Console.Error.WriteLine("  " + failure);
    Console.Error.WriteLine("Fix the snippet, or mark it as docs/CI.md describes; never mark code to hide an error.");
    return 1;
}
var seconds = elapsed.Elapsed.TotalSeconds;
Console.WriteLine($"PASS {snippets} Lean snippets and {names} cited library names ({seconds:F1}s)");

// Stale forms must each fail at their own document line: a pre-Except `invoke` result, removed or
// renamed names, a removed tactic and a block missing an import; their current forms must pass.
var stale = Path.Combine(output, "Stale");
if (Directory.Exists(stale)) Directory.Delete(stale, true);
Directory.CreateDirectory(Path.Combine(stale, "docs"));
const string Identity = """
    import CIL

    open CIL.Safety
    open CIL (W64 Method)
    @[cil_code] def identity : Method := { code := [.arg 0, .ret], locals := [], returnsValue := true }
    """;
var document = $$"""
    # Stale

    Run it with `CIL.Safety.invokeChecked`, not `CIL.Safety.invoke`.

    Store a field with `LoopFrame.store_fieldX`.

    Advance with `cil_loop_advanceX`.

    Store with `LoopFrame.store_field` and `cil_loop_advance`, close with `invoke_loop_induction`.

    `List.set`, `BitVec.toNat`, `get_Item`, `X86.Aes.Encrypt` and `rfl` cite nothing of the library.

    ```lean
    {{Identity}}
    example (x : W64) (memory : Memory) :
        invoke [identity] 4 0 [.scalar (.i64 x)] memory = .ok (memory, [.scalar (.i64 x)]) := by
      cil_checked_steps
    ```

    ```lean
    {{Identity}}
    example (x : W64) (memory : Memory) :
        invoke [identity] 4 0 [.i64 x] memory = some (memory, [.i64 x]) := by
      cil_checked_steps
    ```

    ```lean
    import CIL.Types

    def withoutImport : CIL.Safety.Memory := CIL.Safety.Memory.empty
    ```

    ```lean
    import CIL.Safety.Memory

    def withImport : CIL.Safety.Memory := CIL.Safety.Memory.empty
    ```

    ```lean illustrative
    theorem shape : CIL.Safety.Ensures.removedField = 0
    ```
    """;
File.WriteAllText(Path.Combine(stale, "docs", "Stale.md"), document);
var documentLines = document.ReplaceLineEndings("\n").Split('\n');
// The document lines holding `text`, so the assertions follow the fixture as it is edited.
int[] LinesOf(string text) => documentLines.Select((line, index) => (line, index + 1))
    .Where(entry => entry.line.Contains(text, StringComparison.Ordinal)).Select(entry => entry.Item2).ToArray();
var rejected = Elaborate(stale, "Stale", out _, out _);
const string StalePrefix = "docs/Stale.md:";
var rejectedLines = rejected.Where(failure => failure.StartsWith(StalePrefix, StringComparison.Ordinal))
    .Select(failure => int.Parse(failure[StalePrefix.Length..].Split(':')[0])).ToHashSet();
var currentBlock = Enumerable.Range(LinesOf("```lean")[0], Identity.Split('\n').Length + 4).ToArray();
foreach (var (lines, what) in new[] { (currentBlock, "current invoke form"),
             (LinesOf("`LoopFrame.store_field`"), "current prose names"),
             (LinesOf("`List.set`"), "names outside the library"), (LinesOf("withImport"), "block with its import") })
    if (lines.FirstOrDefault(rejectedLines.Contains) is var line and > 0)
        throw new InvalidOperationException($"""
            The {what} was rejected at docs/Stale.md:{line}:
            {string.Join('\n', rejected)}
            """);
foreach (var (line, what) in new[] { (LinesOf("invokeChecked")[0], "removed prose name"),
             (LinesOf("store_fieldX")[0], "renamed prose name"), (LinesOf("cil_loop_advanceX")[0], "removed tactic"),
             (LinesOf("invoke [identity] 4 0 [.i64 x]")[0], "pre-Except invoke form"),
             (LinesOf("withoutImport")[0], "name from a module the block does not import"),
             (LinesOf("removedField")[0], "removed name in an illustrative block") })
    if (!rejected.Any(failure => failure.StartsWith($"{StalePrefix}{line}: error", StringComparison.Ordinal)))
        throw new InvalidOperationException($"""
            The {what} was not reported at docs/Stale.md:{line}:
            {string.Join('\n', rejected)}
            """);
Console.WriteLine("PASS stale snippets, missing imports and removed names fail at their document lines");

// Each document's commands run from a copy of the example sources they name, so an edit a walkthrough
// makes never touches the checkout. The copy is at one path for every document: builds are then identical.
verification.EnsureExtractorBuilt();
var workspace = Path.Combine(output, "Walkthrough");
var transcripts = new Dictionary<string, List<CommandResult>>(StringComparer.Ordinal);
var walkthroughs = Documentation.Documents(Root).Select(path => Documentation.Read(Root, path))
    .Where(page => page.Walkthrough.Length != 0).ToArray();
var commandCount = 0;
elapsed.Restart();
foreach (var page in walkthroughs)
{
    if (Directory.Exists(workspace)) DeleteTree(workspace);
    Directory.CreateDirectory(workspace);
    var transcript = transcripts[Documentation.Relative(Root, page.Path)] = [];
    var problems = Documentation.RunWalkthrough(page, command =>
    {
        var words = Words(command);
        foreach (var word in words) Mirror(word);
        string[] started = words[0] == "leancil" ? ["dotnet", ExtractorPath, .. words[1..]] : words;
        var result = Execute(started, workspace);
        transcript.Add(new(result.Code, result.Stdout, result.Stderr));
        return transcript[^1];
    }, block =>
    {
        Mirror(block.Source!);
        var path = Path.Combine(workspace, block.Source!);
        File.WriteAllLines(path, Documentation.Edited(File.ReadAllLines(path), block, out var reason)
            ?? throw new InvalidOperationException($"{block.Document}:{block.Line}: {reason}"));
    });
    commandCount += transcript.Count;
    if (problems.Count == 0) continue;
    Console.Error.WriteLine($"Documented commands that do not behave as documented ({problems.Count}):");
    foreach (var problem in problems) Console.Error.WriteLine("  " + problem);
    Console.Error.WriteLine("Correct the document to what the tool prints, or the tool; docs/CI.md lists the markers.");
    return 1;
}
Console.WriteLine($"PASS {commandCount} documented commands of {walkthroughs.Length} documents exit and print " +
    $"as documented ({elapsed.Elapsed.TotalSeconds:F1}s)");

// A documented output that drifts from the tool must fail at its line: a line the tool does not print, a
// line it prints that the document lacks, and an error line it does not print. The unchanged document
// replays its transcript without a failure, so each rejection below is the mutation's.
const string Walked = "docs/GETTING-STARTED.md";
var walked = File.ReadAllText(At(Walked)).ReplaceLineEndings("\n");
List<string> Replayed(string text)
{
    var replayRoot = Path.Combine(output, "StaleOutput");
    Directory.CreateDirectory(Path.Combine(replayRoot, "docs"));
    var path = Path.Combine(replayRoot, Walked);
    File.WriteAllText(path, text);
    var next = 0;
    return Documentation.RunWalkthrough(Documentation.Read(replayRoot, path),
        _ => transcripts[Walked][next++], _ => { });
}
int LineIn(string text, string line) => Array.FindIndex(text.Split('\n'), candidate =>
    candidate.StartsWith(line, StringComparison.Ordinal)) + 1;
if (Replayed(walked) is { Count: > 0 } unchanged)
    throw new InvalidOperationException($"The replayed {Walked} was rejected:\n{string.Join('\n', unchanged)}");
const string SubjectLabel = "  Subject: ";
const string AxiomsLabel = "  Axioms: ";
const string StageLine = "  Stage: proof checking";
foreach (var (what, drifted, line) in new[]
    {
        ("a label the tool does not print", walked.Replace(SubjectLabel, "  Entry: "), LineIn(walked, SubjectLabel)),
        // The line after the removed one is where the document and the tool part.
        ("a line of the tool's output the document lacks", string.Join('\n', walked.Split('\n').Where(text =>
            !text.StartsWith(AxiomsLabel, StringComparison.Ordinal))), LineIn(walked, AxiomsLabel)),
        ("an error line the tool does not print", walked.Replace(StageLine, "  Stage: proof"),
            LineIn(walked, StageLine))
    })
{
    if (line == 0 || drifted == walked)
        throw new InvalidOperationException($"{Walked} no longer documents the line mutated as {what}.");
    var found = Replayed(drifted);
    if (!found.Any(failure => failure.StartsWith($"{Walked}:{line}: ", StringComparison.Ordinal)))
        throw new InvalidOperationException($"""
            {Walked} with {what} was not rejected at line {line}:
            {string.Join('\n', found)}
            """);
}
Console.WriteLine("PASS documented output that drifts from the tool fails at its document line");
return 0;

// The words of a documented command, without the quotes a shell would remove.
static string[] Words(string command) => [.. DocCommands.Word().Matches(command)
    .Select(match => match.Value.Trim('"', '\''))];

// Copies the example source a command names into the workspace, once: a project directory's own sources, or
// a file. Build outputs are not sources, and a copy the walkthrough edited is kept.
void Mirror(string word)
{
    if (!word.StartsWith("Examples/", StringComparison.Ordinal) || word.Contains("/bin/") || word.Contains("/obj/"))
        return;
    var source = At(word);
    string[] files = File.Exists(source) ? [source]
        : Directory.Exists(source) ? [.. Directory.EnumerateFiles(source).Where(path =>
            Path.GetExtension(path) is ".cs" or ".csproj" or ".lean")]
        : [];
    foreach (var file in files)
    {
        var copy = Path.Combine(workspace, Path.GetRelativePath(Root, file));
        if (File.Exists(copy)) continue;
        Directory.CreateDirectory(Path.GetDirectoryName(copy)!);
        File.Copy(file, copy);
    }
}

static partial class DocCommands
{
    [System.Text.RegularExpressions.GeneratedRegex("""
        "[^"]*"|'[^']*'|\S+
        """, System.Text.RegularExpressions.RegexOptions.IgnorePatternWhitespace)]
    internal static partial System.Text.RegularExpressions.Regex Word();
}
