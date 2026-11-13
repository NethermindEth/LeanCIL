#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.RegularExpressions;

// An edit to one method moves things in the image that other methods' evidence could pick up: a longer body moves
// every later body, and a changed name moves heap entries, whose order the image fixes by a hash or a suffix sort.
// The evidence of the other methods must not notice. The fixture has the shape of the workspace test, whose refresh
// of only the edited method rests on this: a static class, a second one and a struct with a static constructor.
var directory = At("artifacts/IncrementalEvidence");
string Build(string name, string method, string body)
{
    var source = Path.Combine(directory, name);
    // An earlier run's sources would join the build and shift every token.
    if (Directory.Exists(source)) Directory.Delete(source, true);
    Directory.CreateDirectory(source);
    File.WriteAllText(Path.Combine(source, "Incremental.csproj"), """
        <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup></Project>
        """);
    File.WriteAllText(Path.Combine(source, "Arith.cs"), $$"""
        namespace Workspace;
        public static class Arith
        {
            public static ulong {{method}}(ulong x) => {{body}};
        }
        """);
    File.WriteAllText(Path.Combine(source, "Third.cs"), """
        namespace Workspace;
        public static class Third
        {
            public static ulong Thrice(ulong x) => x + x + x;
        }
        """);
    File.WriteAllText(Path.Combine(source, "Wide.cs"), """
        namespace Workspace;
        public readonly struct Wide(ulong u0, ulong u1, ulong u2, ulong u3)
        {
            public static readonly Wide Zero = default;
            public static readonly Wide One = new(1, 0, 0, 0);
            readonly ulong u0 = u0, u1 = u1, u2 = u2, u3 = u3;
            public bool IsZeroOrOne => ((u0 >> 1) | u1 | u2 | u3) == 0;
        }
        """);
    Run(["dotnet", "build", Path.Combine(source, "Incremental.csproj"), "-c", "Release"]);
    return Path.Combine(source, "bin/Incremental.dll");
}
var baseline = Build("Baseline", "Twice", "x + x");
var longer = Build("Longer", "Twice", "x + x + x + x + x + x");
var renamed = Build("Renamed", "Doubled", "x + x");
string Evidence(string assembly, string selector, string name)
{
    var output = Path.Combine(directory, name);
    Run([.. Extract("extract", assembly, "Incremental", selector, output), "--assume-initialized", "Workspace.Wide"]);
    var text = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var lines = Regex.Matches(text, @"(?m)^(?:def (?:assembly|module)\d+(?:Metadata|Tables) |def method0Body ).*$")
        .Select(match => match.Value).ToArray();
    if (lines.Length != 4)
        throw new InvalidOperationException("Expected the assembly and module metadata, tables and body: " + name);
    if (Regex.IsMatch(string.Concat(lines), @"\brva\b"))
        throw new InvalidOperationException("Evidence holds a body address: " + name);
    return string.Join('\n', lines);
}
foreach (var (method, label) in new[] { ("Workspace.Third::Thrice(ulong)", "Thrice"),
    ("Workspace.Wide::get_IsZeroOrOne()", "Wide") })
{
    var expected = Evidence(baseline, method, "Baseline" + label);
    if (expected != Evidence(longer, method, "Longer" + label))
        throw new InvalidOperationException(
            $"Lengthening Twice changed the evidence of {label}: the incremental refresh would redo it.");
    if (expected != Evidence(renamed, method, "Renamed" + label))
        throw new InvalidOperationException(
            $"Renaming Twice changed the evidence of {label}: the image's heap order must not reach the evidence.");
}
Console.WriteLine("PASS lengthening or renaming one method leaves the metadata, tables and body evidence of the other methods byte-identical");
