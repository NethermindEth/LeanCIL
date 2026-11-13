#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.RegularExpressions;

// A method's evidence, its metadata slice, lookup tables, body and validity theorems, must be a function of the
// method and its assemblies and of nothing else in the extraction or the image. An edit to one method moves things
// in the image that another method's evidence could pick up (a longer body moves every later body, a changed name
// moves heap entries, whose order the image fixes by a hash or a suffix sort), and extracting a different entry
// method changes which other methods the extraction holds. The fixture has the shape of the workspace test, whose
// refresh of only the edited method rests on this, with a helper that two entry methods share.
var directory = At("artifacts/IncrementalEvidence");
string Build(string name, string method, string body)
{
    var source = Path.Combine(directory, name);
    // An earlier run's sources would join the build and shift every token.
    if (Directory.Exists(source)) Directory.Delete(source, true);
    Directory.CreateDirectory(source);
    File.WriteAllText(Path.Combine(source, "Incremental.csproj"), """
        <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
        <Optimize>true</Optimize></PropertyGroup></Project>
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
    File.WriteAllText(Path.Combine(source, "Shared.cs"), """
        namespace Workspace;
        public static class Shared
        {
            public static ulong Helper(ulong x) => x * 7UL + 1UL;
            public static ulong EntryA(ulong x) => Helper(x) + 1UL;
            public static ulong EntryB(ulong x) => Helper(x) ^ 3UL;
            public static ulong Size<T>(ulong x) where T : unmanaged =>
                x + (ulong)System.Runtime.CompilerServices.Unsafe.SizeOf<T>();
            public static ulong EntryGenericA(ulong x) => Size<ulong>(x) + Size<uint>(x);
            public static ulong EntryGenericB(ulong x) => Size<uint>(x) ^ Size<ulong>(x);
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

string Extracted(string assembly, string selector, string name)
{
    var output = Path.Combine(directory, name);
    Run([.. Extract("extract", assembly, "Incremental", selector, output), "--assume-initialized", "Workspace.Wide"]);
    return File.ReadAllText(Path.Combine(output, "Extracted.lean"));
}
// The assembly block and every definition and theorem of one method's component.
string Component(string text, int method, string name)
{
    var lines = Regex.Matches(text, @"(?m)^(?:def assembly\d+Metadata |(?:@\[[^\r\n]*\] )?(?:def|theorem) method" +
            method + @"(?![0-9]))[^\n]*$").Select(match => match.Value.TrimEnd('\r'))
        // The composed theorem names the method's position in the whole program, which is not part of its component.
        .Where(line => !line.Contains("_evidence_validated", StringComparison.Ordinal)).ToArray();
    // A closed instantiation of a generic method shares its open definition's slice, which another component holds.
    var ownSlice = lines.Any(line => line.Contains($"metadata := method{method}Metadata,", StringComparison.Ordinal));
    foreach (var required in (ownSlice
        ? new[] { $"def method{method}Metadata :", $"def method{method}Tables :",
            $"theorem method{method}_tables_valid :" }
        : []).Concat([$"def method{method}Body :", $"theorem method{method}_body_validated :"]))
        if (!lines.Any(line => line.StartsWith(required, StringComparison.Ordinal)))
            throw new InvalidOperationException($"No `{required}` in the component of method {method}: {name}");
    if (Regex.IsMatch(string.Concat(lines), @"\brva\b"))
        throw new InvalidOperationException("Evidence holds a body address: " + name);
    return string.Join('\n', lines);
}

foreach (var (method, label) in new[] { ("Workspace.Third::Thrice(ulong)", "Thrice"),
    ("Workspace.Wide::get_IsZeroOrOne()", "Wide") })
{
    var expected = Component(Extracted(baseline, method, "Baseline" + label), 0, label);
    if (expected != Component(Extracted(longer, method, "Longer" + label), 0, label))
        throw new InvalidOperationException(
            $"Lengthening Twice changed the evidence of {label}: the incremental refresh would redo it.");
    if (expected != Component(Extracted(renamed, method, "Renamed" + label), 0, label))
        throw new InvalidOperationException(
            $"Renaming Twice changed the evidence of {label}: the image's heap order must not reach the evidence.");
}
Console.WriteLine("PASS lengthening or renaming one method leaves the evidence of the other methods byte-identical");

// Two entry methods that share a helper: the helper's whole component is the same in both extractions, so a
// consumer that verified it once reuses it.
var entryA = Extracted(baseline, "Workspace.Shared::EntryA(ulong)", "EntryA");
var entryB = Extracted(baseline, "Workspace.Shared::EntryB(ulong)", "EntryB");
string HelperIndex(string text) => Regex.Match(text,
    @"(?m)^def method(\d+)Signature : String := ""[^""]*Shared::Helper\(").Groups[1].Value;
var (helperA, helperB) = (HelperIndex(entryA), HelperIndex(entryB));
if (helperA.Length == 0 || helperA != helperB)
    throw new InvalidOperationException($"Expected the helper at one index in both extractions: {helperA} {helperB}");
if (Component(entryA, int.Parse(helperA), "EntryA") != Component(entryB, int.Parse(helperB), "EntryB"))
    throw new InvalidOperationException(
        "The helper's component differs between two extractions that share it: its evidence depends on the entry.");
Console.WriteLine("PASS a helper's metadata, tables, body and validity theorems are identical in two " +
    "extractions that share it");

// A generic helper closed twice: the second instantiation names the first one's metadata, which is a function of the
// open definition and the assembly, so both components are the same in two extractions that hold the same helper.
// The two entries close the helper in opposite orders, so each instantiation has another index in the second
// extraction: the component, with its own index named `#`, must be the same text.
var genericA = Extracted(baseline, "Workspace.Shared::EntryGenericA(ulong)", "EntryGenericA");
var genericB = Extracted(baseline, "Workspace.Shared::EntryGenericB(ulong)", "EntryGenericB");
string Instantiation(string text, string argument, string name)
{
    var index = Regex.Match(text, @"(?m)^def method(\d+)Signature : String := ""[^""]*Shared::Size\\u003C" + argument +
        @"\\u003E").Groups[1].Value;
    if (index.Length == 0) throw new InvalidOperationException($"No Size<{argument}> in {name}.");
    return Regex.Replace(Component(text, int.Parse(index), name), "method" + index + "(?![0-9])", "method#");
}
const string UIntSignature = @"(?m)^def method(\d+)Signature[^\r\n]*Size\\u003CSystem.UInt32";
var (uintIndexA, uintIndexB) = (Regex.Match(genericA, UIntSignature).Groups[1].Value,
    Regex.Match(genericB, UIntSignature).Groups[1].Value);
if (uintIndexA == uintIndexB)
    throw new InvalidOperationException(
        "The two extractions close the helper in the same order; the case tests nothing.");
foreach (var argument in new[] { "System.UInt32", "System.UInt64" })
    if (Instantiation(genericA, argument, "EntryGenericA") != Instantiation(genericB, argument, "EntryGenericB"))
        throw new InvalidOperationException(
            $"The component of Size<{argument}> differs between two extractions that close the helper " +
            "in another order.");
Console.WriteLine("PASS a generic helper's instantiations have identical components in extractions " +
    "that close it in opposite orders");
