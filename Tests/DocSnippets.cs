#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/Documentation.cs

using System.Diagnostics;

// Every unmarked Lean block in the documentation must elaborate against the current library, and every
// `CIL.` name the rest of the documentation cites must still exist; a stale copy must fail at its line.
using var verification = new Program();
var output = At("artifacts/DocSnippets");
Directory.CreateDirectory(output);
var leanPath = verification.CheckoutLeanPath();

// The diagnostics of the snippet and name batches for the documents under `root`, by document line.
List<string> Elaborate(string root, string name, out int snippets, out int names)
{
    var pages = Documentation.Documents(root).Select(path => Documentation.Read(root, path)).ToArray();
    var batches = new[] { ("Snippets", Documentation.Snippets(pages)), ("Names", Documentation.Names(Root, pages)) };
    var failures = new List<string>();
    foreach (var (kind, batch) in batches)
    {
        var path = Path.Combine(output, $"{name}{kind}.lean");
        File.WriteAllText(path, batch.Text);
        var result = Execute([verification.LeanExecutable, path], leanPath: leanPath);
        var found = Documentation.Diagnostics(batch, Documentation.Relative(Root, path), result.Output);
        if (result.Code != 0 && found.Count == 0) found.Add($"Lean exited with {result.Code}: {result.Output}");
        failures.AddRange(found);
    }
    (snippets, names) = (batches[0].Item2.Count, batches[1].Item2.Count);
    return failures;
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

// The pre-Except `invoke` result and removed names must each fail at their own document line, while
// the same statement in the current form, in the same batch, elaborates.
var stale = Path.Combine(output, "Stale");
if (Directory.Exists(stale)) Directory.Delete(stale, true);
Directory.CreateDirectory(Path.Combine(stale, "docs"));
const string Identity = """
    open CIL.Safety
    open CIL (W64 Method)
    @[cil_code] def identity : Method := { code := [.arg 0, .ret], locals := [], returnsValue := true }
    """;
File.WriteAllText(Path.Combine(stale, "docs", "Stale.md"), $$"""
    # Stale

    Run it with `CIL.Safety.invokeChecked`, not `CIL.Safety.invoke`.

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

    ```lean illustrative
    theorem shape : CIL.Safety.Ensures.removedField = 0
    ```
    """);
var rejected = Elaborate(stale, "Stale", out _, out _);
const string StalePrefix = "docs/Stale.md:";
var rejectedLines = rejected.Where(failure => failure.StartsWith(StalePrefix, StringComparison.Ordinal))
    .Select(failure => int.Parse(failure[StalePrefix.Length..].Split(':')[0])).ToHashSet();
if (rejectedLines.Any(line => line is >= 6 and <= 11))
    throw new InvalidOperationException($"""
        The current invoke form was rejected:
        {string.Join('\n', rejected)}
        """);
foreach (var (line, what) in new[] { (3, "removed prose name"), (19, "pre-Except invoke form"),
             (24, "removed name in an illustrative block") })
    if (!rejected.Any(failure => failure.StartsWith($"{StalePrefix}{line}: error", StringComparison.Ordinal)))
        throw new InvalidOperationException($"""
            The {what} was not reported at docs/Stale.md:{line}:
            {string.Join('\n', rejected)}
            """);
Console.WriteLine("PASS stale snippets and removed names fail at their document lines");
return 0;
