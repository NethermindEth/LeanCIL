#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.RegularExpressions;

// An edit to one method body moves every later body in the image. The evidence of the other methods must not
// notice: the carried rows have the body address masked and no generated definition holds it, so two builds that
// differ only in the length of the first method's body emit identical metadata and tables for the second.
var directory = At("artifacts/IncrementalEvidence");
string Build(string name, string firstBody)
{
    var source = Path.Combine(directory, name);
    Directory.CreateDirectory(source);
    File.WriteAllText(Path.Combine(source, "Incremental.csproj"), """
        <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup></Project>
        """);
    File.WriteAllText(Path.Combine(source, "Incremental.cs"), $$"""
        public static class Incremental
        {
            public static ulong First(ulong x) => {{firstBody}};
            public static ulong Second(ulong x) => x + 2UL;
            public static ulong Third(ulong x) => x * 3UL;
        }
        """);
    Run(["dotnet", "build", Path.Combine(source, "Incremental.csproj"), "-c", "Release"]);
    return Path.Combine(source, "bin/Incremental.dll");
}
var short_ = Build("Short", "x + 1UL");
var long_ = Build("Long", "x + 1UL + 2UL + 3UL + 4UL + 5UL");
string Evidence(string assembly, string method, string name)
{
    var output = Path.Combine(directory, name);
    Run(Extract("extract", assembly, "Incremental", $"Incremental::{method}(ulong)", output));
    var text = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var lines = Regex.Matches(text, @"(?m)^(?:def module\d+(?:Metadata|Tables) |def method0Body ).*$")
        .Select(match => match.Value).ToArray();
    if (lines.Length != 3) throw new InvalidOperationException("Expected the module metadata, tables and body: " + name);
    if (Regex.IsMatch(string.Concat(lines), @"\brva\b"))
        throw new InvalidOperationException("Evidence holds a body address: " + name);
    return string.Join('\n', lines);
}
foreach (var method in new[] { "Second", "Third" })
    if (Evidence(short_, method, "Short" + method) != Evidence(long_, method, "Long" + method))
        throw new InvalidOperationException(
            $"Lengthening the body of First changed the evidence of {method}: the incremental refresh would redo it.");
Console.WriteLine("PASS lengthening one body leaves the metadata, tables and body evidence of the other methods byte-identical");
