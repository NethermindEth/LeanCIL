#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/FullModuleResolution.cs

using Program paths = new();
string root = At("artifacts/FullModuleResolution-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
string library = Path.GetFullPath(Path.Combine(paths.Toolchain, "lib", "lean"));
SortedDictionary<string, string> accepted = new(StringComparer.Ordinal)
{
    ["Init"] = Path.Combine(library, "Init.olean"),
    ["Lean.Elab"] = Path.Combine(library, "Lean", "Elab.olean")
};
// Lean joins search roots verbatim, so the root's spelling (separators, "." segments, drive case) must not matter.
string spelled = paths.Toolchain + "/lib/./lean";
paths.CheckFullResolution(root, spelled, accepted);
Console.WriteLine("PASS full-verification resolution accepts the same files under another root spelling");

SortedDictionary<string, string> swapped = new(StringComparer.Ordinal) { ["Init"] = accepted["Lean.Elab"] };
string? rejection = null;
try { paths.CheckFullResolution(root, spelled, swapped); }
catch (InvalidOperationException error) { rejection = error.Message; }
if (rejection?.Contains("Full-verification resolved module path changed: Init", StringComparison.Ordinal) != true)
    throw new InvalidOperationException("Full-verification resolution accepted a module loaded from a different file: " + rejection);
Console.WriteLine("PASS full-verification resolution rejects a module loaded from a different file");
