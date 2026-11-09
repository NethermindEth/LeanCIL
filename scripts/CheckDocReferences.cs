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
// The validation guide's suite table must list exactly the suites the runner accepts.
var root = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(SourcePath())!, ".."));
var pages = Documentation.Documents(root).Select(path => Documentation.Read(root, path)).ToArray();
var (failures, references, blocks) = Documentation.CheckReferences(root, pages);
var suitePage = pages.Single(page => Documentation.Relative(root, page.Path) == Documentation.SuiteDocument);
failures.AddRange(Documentation.CheckSuiteTable(root, suitePage, VerificationSuites.Names()));
if (failures.Count != 0)
{
    Console.Error.WriteLine($"Stale documentation references ({failures.Count}):");
    foreach (var failure in failures) Console.Error.WriteLine("  " + failure);
    Console.Error.WriteLine("Fix the citation where it stands; see docs/CI.md for the markers and audiences.");
    return 1;
}
Console.WriteLine($"PASS {references} code references and {blocks} Lean blocks in {pages.Length} documents");
return 0;

static string SourcePath([CallerFilePath] string path = "") => path;
