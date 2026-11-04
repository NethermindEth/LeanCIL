#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

// The certified library is bound to the lakefile it is built from, so editing a test library must
// not rebuild CIL, while every setting that can change the CIL build or its auditor must.
var checkout = File.ReadAllText(At("lakefile.toml")).ReplaceLineEndings("\n");
var library = LibraryLakefile(checkout);
const string cilLibrary = "[[lean_lib]]\nname = \"CIL\"\n";
Require(library.Contains(cilLibrary, StringComparison.Ordinal) &&
    library.Contains("[[lean_exe]]\nname = \"leancil-audit\"\nroot = \"CIL.OleanAudit\"\n",
        StringComparison.Ordinal) &&
    library.StartsWith("name = \"leancil\"\n", StringComparison.Ordinal) &&
    library.Contains("defaultTargets = [\"CIL\"]\n", StringComparison.Ordinal),
    "Library lakefile lost the package, CIL or auditor configuration:\n" + library);
Require(!library.Contains("Tests.", StringComparison.Ordinal), "Library lakefile declares a test library");
Console.WriteLine("PASS library lakefile keeps the package, CIL and auditor and omits test libraries");

const string added = "\n[[lean_lib]]\nname = \"Tests.Added\"\n";
const string firstTest = "[[lean_lib]]\nname = \"Tests.Support\"\n\n";
Require(checkout.Contains(firstTest, StringComparison.Ordinal), "Fixture lakefile moved");
foreach (var (label, edited) in new[]
{
    ("an appended test library", checkout + added),
    ("a test library before CIL", checkout.Replace(cilLibrary, added.TrimStart('\n') + "\n" + cilLibrary)),
    ("a removed test library", checkout.Replace(firstTest, "")),
    ("a comment", checkout + "\n# A note on the test libraries\n"),
    ("CRLF line endings", checkout.ReplaceLineEndings("\r\n")),
})
{
    Require(edited != checkout, "Mutation did not apply: " + label);
    Require(LibraryLakefile(edited) == library, "Library lakefile changed for " + label);
}
Console.WriteLine("PASS test library additions, removals, comments and line endings keep the library lakefile");

foreach (var (label, edited) in new[]
{
    ("a package version", checkout.Replace("version = \"0.1.0\"", "version = \"0.2.0\"")),
    ("a package Lean option",
        checkout.Replace("defaultTargets", "moreLeanArgs = [\"-Dlinter.all=true\"]\ndefaultTargets")),
    ("a package option table", checkout + "\n[leanOptions]\nautoImplicit = false\n"),
    ("the CIL library", checkout.Replace(cilLibrary, cilLibrary + "precompileModules = true\n")),
    ("the auditor", checkout.Replace("root = \"CIL.OleanAudit\"", "root = \"CIL.Replay\"")),
    ("a library under CIL", checkout + "\n[[lean_lib]]\nname = \"CIL.Extra\"\n"),
    ("a test library with roots", checkout + "\n[[lean_lib]]\nname = \"Tests.Rooted\"\nroots = [\"CIL\"]\n"),
    ("a default test target", checkout.Replace("defaultTargets = [\"CIL\"]", "defaultTargets = [\"Tests.Support\"]")),
    ("a dependency", checkout + "\n[[require]]\nname = \"other\"\npath = \"../other\"\n"),
    ("a multi-line string", checkout + "\ndescription = \"\"\"\n[[lean_lib]]\n\"\"\"\n"),
})
{
    Require(edited != checkout, "Mutation did not apply: " + label);
    Require(LibraryLakefile(edited) != library, "Library lakefile ignored " + label);
}
Require(LibraryLakefile(checkout.Replace("defaultTargets = [\"CIL\"]", "defaultTargets = [\"Tests.Support\"]"))
    .Contains("name = \"Tests.Support\"", StringComparison.Ordinal), "A default target lost its declaration");
Console.WriteLine("PASS package, CIL, auditor, dependency and CIL-claiming library edits change the library lakefile");

// Checkout identities, such as session cache keys, still see the complete lakefile.
var common = CommonInputs();
Require(common[CheckoutLakefileInput] == Sha(At("lakefile.toml")) &&
    common["lakefile.toml"] == ContentKey(LibraryLakefile(File.ReadAllText(At("lakefile.toml")))) &&
    !LibrarySources(common).ContainsKey(CheckoutLakefileInput),
    "Checkout and library lakefile inputs are not separated");
Console.WriteLine("PASS checkout inputs hash the complete lakefile and library sources its library view");

static void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}
