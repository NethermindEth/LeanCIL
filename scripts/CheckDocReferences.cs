#!/usr/bin/env dotnet
#:property PublishAot=false
#:include Documentation.cs
#:include ExportVerificationSuites.cs
#:include VerificationSuites.cs

using System.Runtime.CompilerServices;

// Citations in the documentation must still resolve: linked files and repository paths exist, named
// links name a declaration the file still has, user documents cite nothing from the unshipped Tests/,
// commands are ones the library declares and excerpts still match their source. Line-number
// citations drift silently, so they fail too. Snippet elaboration needs Lean and runs in the docs suite.
// The validation guide's suite table must list exactly the suites the runner accepts. The example proofs
// are what users copy, so each prints the axioms of its theorems and names no evaluator internal in a
// simp list, and neither does a Lean block of the documentation. No tracked text file holds a control
// byte other than tab and line ends.
var root = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(SourcePath())!, ".."));
var pages = Documentation.Documents(root).Select(path => Documentation.Read(root, path)).ToArray();
var (failures, references, blocks) = Documentation.CheckReferences(root, pages);
var suitePage = pages.Single(page => Documentation.Relative(root, page.Path) == Documentation.SuiteDocument);
failures.AddRange(Documentation.CheckSuiteTable(root, suitePage, VerificationSuites.Names()));
failures.AddRange(Documentation.CheckExamples(root));
failures.AddRange(Documentation.ControlCharacterProblems(root, TrackedFiles(root)));
if (failures.Count != 0)
{
    Console.Error.WriteLine($"Stale documentation references ({failures.Count}):");
    foreach (var failure in failures) Console.Error.WriteLine("  " + failure);
    Console.Error.WriteLine("Fix the citation where it stands; see docs/CI.md for the markers and audiences.");
    return 1;
}
Console.WriteLine($"PASS {references} code references and {blocks} Lean blocks in {pages.Length} documents");
return 0;

// The files git tracks, relative to the root; an untracked build output is not source.
static string[] TrackedFiles(string root)
{
    var start = new System.Diagnostics.ProcessStartInfo("git") { RedirectStandardOutput = true };
    foreach (var argument in new[] { "-C", root, "ls-files", "-z" }) start.ArgumentList.Add(argument);
    using var git = System.Diagnostics.Process.Start(start)!;
    var listing = git.StandardOutput.ReadToEnd();
    git.WaitForExit();
    return git.ExitCode == 0 ? listing.Split('\0', StringSplitOptions.RemoveEmptyEntries)
        : throw new InvalidOperationException("git ls-files failed in " + root);
}

static string SourcePath([CallerFilePath] string path = "") => path;
