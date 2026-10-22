#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;
using System.Xml.Linq;

string root = At("artifacts/ExceptionLint");
Directory.CreateDirectory(root);
string assembly = At("Examples/Assembly/bin/Examples.dll");
string output = Path.Combine(root, "extraction");
string documentation = Path.Combine(root, "Examples.xml");
string reportPath = Path.Combine(output, "exception-lint.json");
string[] cli = ["dotnet", ExtractorPath];

void Extract(string selector) => Run([.. cli, "extract", assembly, selector, output]);
void Document(string member, params string[] exceptions)
{
    XDocument document = new(new XElement("doc", new XElement("assembly", new XElement("name", "Examples")),
        new XElement("members", new XElement("member", new XAttribute("name", member),
            exceptions.Select(exception => new XElement("exception", new XAttribute("cref", "T:" + exception), "Untrusted condition"))))));
    document.Save(documentation);
}
JsonElement Lint()
{
    Run([.. cli, "lint-exceptions", output, "--documentation", documentation]);
    if (File.Exists(Path.Combine(output, "verified.json"))) throw new InvalidOperationException("Lint must not certify a proof.");
    return JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(reportPath));
}
void Reject(string diagnostic)
{
    (int Code, string Output, string Stdout, string Stderr) result = Execute([.. cli, "lint-exceptions", output, "--documentation", documentation]);
    if (result.Code == 0 || !result.Output.Contains(diagnostic, StringComparison.Ordinal) || File.Exists(reportPath))
        throw new InvalidOperationException("Expected lint rejection without a stale report: " + diagnostic + "\n" + result.Output);
}
string[] Potential(JsonElement report) => report.GetProperty("potentialModeled").EnumerateArray().Select(value => value.GetString()!).ToArray();

Extract("Examples.Throws::Quotient(uint,uint)");
const string quotient = "M:Examples.Throws.Quotient(System.UInt32,System.UInt32)";
Document(quotient, "System.DivideByZeroException");
JsonElement matching = Lint();
if (!Potential(matching).SequenceEqual(["System.DivideByZeroException"]) || matching.GetProperty("findings").GetArrayLength() != 0 ||
    !matching.GetProperty("sites").EnumerateArray().Any(site => site.GetProperty("origin").GetString() == "folded throw"))
    throw new InvalidOperationException("Entry lint must include the reachable helper throw and divide without duplicate drift.");
Document(quotient, "System.InvalidOperationException");
JsonElement drift = Lint();
if (!Potential(drift).SequenceEqual(Potential(matching)) || drift.GetProperty("findings").GetArrayLength() != 2 ||
    !drift.GetProperty("findings").EnumerateArray().Select(value => value.GetProperty("message").GetString()).Order().SequenceEqual(
        new[] { "documented exception not found in the model", "potential modelled exception not documented" }.Order()))
    throw new InvalidOperationException("Documentation must not add model evidence; both drift directions must be distinct.");
Document(quotient);
if (Lint().GetProperty("findings").GetArrayLength() != 1) throw new InvalidOperationException("Undocumented potential must be reported.");

Extract("Examples.Throws::Percent(uint)");
Document("M:Examples.Throws.Percent(System.UInt32)", "System.ArgumentOutOfRangeException");
if (!Potential(Lint()).SequenceEqual(["System.ArgumentOutOfRangeException"]))
    throw new InvalidOperationException("Explicit folded exception name was lost.");

string compilerDocumentation = Path.ChangeExtension(assembly, ".xml");
foreach ((string Selector, string[] Expected) item in new (string, string[])[]
{
    ("Examples.ExceptionDocumentation::Divide(long,long)", ["System.DivideByZeroException", "System.OverflowException"]),
    ("Examples.ExceptionDocumentation::UnsignedDivide(ulong,ulong)", ["System.DivideByZeroException"]),
    ("Examples.ExceptionDocumentation::Absolute(int)", ["System.OverflowException"]),
    ("Examples.ExceptionDocumentation::Clamp(int,int,int)", []),
    ("Examples.ExceptionDocumentation::Profile(uint)", []),
    ("Examples.ExceptionDocumentation::Reference(ulong&)", [])
})
{
    Extract(item.Selector);
    File.Copy(compilerDocumentation, documentation, true);
    JsonElement report = Lint();
    if (!Potential(report).SequenceEqual(item.Expected))
        throw new InvalidOperationException("Wrong modeled exception set: " + item.Selector);
    bool expectedDrift = item.Selector.Contains("Clamp", StringComparison.Ordinal) || item.Selector.Contains("Profile", StringComparison.Ordinal);
    if (report.GetProperty("findings").GetArrayLength() != (expectedDrift ? 1 : 0))
        throw new InvalidOperationException("Compiler XML matching or separate invalid-bounds/profile exclusion failed: " + item.Selector);
}
Extract("Examples.Throws::Percent(uint)");

foreach ((string Name, string Xml, string Diagnostic) item in new (string, string, string)[]
{
    ("wrong-assembly", "<doc><assembly><name>Other</name></assembly><members/></doc>", "assembly name"),
    ("missing-member", "<doc><assembly><name>Examples</name></assembly><members/></doc>", "exactly one member"),
    ("duplicate-member", "<doc><assembly><name>Examples</name></assembly><members><member name=\"M:Examples.Throws.Percent(System.UInt32)\"/><member name=\"M:Examples.Throws.Percent(System.UInt32)\"/></members></doc>", "exactly one member"),
    ("unresolved-cref", "<doc><assembly><name>Examples</name></assembly><members><member name=\"M:Examples.Throws.Percent(System.UInt32)\"><exception cref=\"!:Missing\"/></member></members></doc>", "resolved type cref"),
    ("inherited", "<doc><assembly><name>Examples</name></assembly><members><member name=\"M:Examples.Throws.Percent(System.UInt32)\"><inheritdoc/></member></members></doc>", "expanded documentation"),
    ("dtd", "<!DOCTYPE doc [<!ENTITY test SYSTEM 'file:///unused'>]><doc/>", "DTD")
})
{
    File.WriteAllText(documentation, item.Xml);
    File.WriteAllText(reportPath, "old report");
    Reject(item.Diagnostic);
    Console.WriteLine("PASS exception lint rejection: " + item.Name);
}
Document("M:Examples.Throws.Percent(System.UInt32)");
File.AppendAllText(Path.Combine(output, "Extracted.lean"), "\n");
Reject("current admitted extraction");
Console.WriteLine("PASS diagnostic exception lint, helper closure, XML separation and stale rejection");
