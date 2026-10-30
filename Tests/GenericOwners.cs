#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Reflection;
using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/GenericOwners");
Directory.CreateDirectory(root);
// Foreign owners cannot be serialized as distinct CLI slots; check the in-memory metadata boundary.
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var caller = module.Types.Single(type => type.Name == "GenericOwners").Methods
        .Single(method => method.Name == "Identity");
    var target = (MethodReference)caller.Body.Instructions.Single(instruction =>
        instruction.OpCode.Code == Code.Call).Operand;
    var foreignOwner = module.Types.Single(type => type.Name == "OwnerOuter`1");
    target.Resolve().Body.Variables.Add(new VariableDefinition(foreignOwner.GenericParameters[0]));
    var specialization = Assembly.LoadFrom(ExtractorPath).GetType("Nethermind.LeanCIL.MethodSpecialization")!;
    var instance = Activator.CreateInstance(specialization, BindingFlags.Instance | BindingFlags.Public |
        BindingFlags.NonPublic, null, [module, "scalar"], null)!;
    try
    {
        specialization.GetMethod("Instantiate", BindingFlags.Instance | BindingFlags.NonPublic)!
            .Invoke(instance, [target]);
        throw new InvalidOperationException("Foreign generic owner was accepted");
    }
    catch (TargetInvocationException error) when (error.InnerException is InvalidDataException invalid &&
        invalid.Message.Contains("Foreign generic parameter owner", StringComparison.Ordinal))
    {
        Console.WriteLine("PASS rejected foreign generic parameter owner");
    }
}
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution");
var evidence = new GeneratedEvidence(root);
var rejected = new RejectedEvidence(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.GenericOwners")!;

string ChangeDefinition(string source, string name, Func<string, string> change)
{
    var matches = Regex.Matches(source, @"(?m)^def " + Regex.Escape(name) + @" : [^\r\n]+\r?$");
    if (matches.Count != 1) throw new InvalidOperationException("Missing unique definition: " + name);
    var match = matches[0];
    var replacement = change(match.Value);
    if (replacement == match.Value) throw new InvalidOperationException("Mutation did not change " + name);
    return source[..match.Index] + replacement + source[(match.Index + match.Length)..];
}

foreach (var name in new[] { "Identity", "Combined", "Nested", "Repeated", "Address" })
{
    var expected = name == "Repeated" ? 84u : 42u;
    if (!Equals(runtime.GetMethod(name)!.Invoke(null, [42u]), expected))
        throw new InvalidOperationException("Unexpected CLR generic-owner result: " + name);
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"GenericOwners::{name}(uint)", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    if (Regex.Matches(source, @"(?m)^def method\d+ : Method :=").Count != 2)
        throw new InvalidOperationException("Closed specialization was duplicated: " + name);
    var proof = source + $$"""

        /-- The compiled closed-owner call agrees with the CLR, including repeated cached calls. -/
        theorem generic_owner_result :
            (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i32 42)]
              { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩,
                views := [], nextIdentity := 0 }).map Prod.snd = .ok [.scalar (.i32 {{expected}})] := rfl
        #print axioms generic_owner_result
        """;
    if (name == "Combined")
    {
        var specialization = NarrowEvidence(source, "method1_specialization_validated");
        var calls = NarrowEvidence(source, "method0_calls_validated");
        proof += "\n" + CheckedEvidenceControl(source, specialization, ["method1_specialization_validated"], 0);
        proof += "\n" + CheckedEvidenceControl(source, calls, ["method0_calls_validated"], 1);
        var cases = new (string Name, string Source)[]
        {
            ("swapped", ChangeDefinition(specialization, "method1TypeArgumentsRaw", line =>
                line.Replace("System.UInt32", "TemporaryType", StringComparison.Ordinal)
                    .Replace("System.UInt64", "System.UInt32", StringComparison.Ordinal)
                    .Replace("TemporaryType", "System.UInt64", StringComparison.Ordinal))),
            ("omitted", ChangeDefinition(specialization, "method1TypeArgumentsRaw", line =>
                line.Replace(", .atom Extraction.runtimeScope \"System.UInt64\"", "", StringComparison.Ordinal))),
            ("arity", ChangeDefinition(calls, "method0Closed", line =>
                line.Replace("ownerArgumentCount := 1", "ownerArgumentCount := 0", StringComparison.Ordinal))),
            ("owner", ChangeDefinition(calls, "method0Closed", line =>
                line.Replace("Examples.OwnerHelper", "Examples.OwnerOuter", StringComparison.Ordinal)))
        };
        foreach (var mutation in cases)
        {
            var path = Path.Combine(root, mutation.Name + ".lean");
            File.WriteAllText(path, mutation.Source);
            rejected.Add(path, "PASS independently rejected generic owner evidence: " + mutation.Name);
        }
    }
    var proofPath = Path.Combine(root, name + ".lean");
    File.WriteAllText(proofPath, proof);
    evidence.Add(proofPath, "PASS closed generic owner: " + name);
}

// Generic helpers call span members on owners built from their own parameters: `!!0` in
// SpanHelpers, `!0` in OwnerHelper<T> and `!1` in OwnerOuter<T>.Inner<U>. Byte i holds i.
var words = Enumerable.Range(0, 32).Select(index => (byte)index).ToArray();
string Word(int index) =>
    BitConverter.ToUInt64(words, index * 8).ToString(System.Globalization.CultureInfo.InvariantCulture);
const string spanMemory = """

    /-- Readable caller storage whose byte at offset `i` is `i`. -/
    def spanMemory : CIL.Safety.Memory :=
      { allocations := fun identity => if identity == 0 then
          some ⟨.callerStack, ⟨32, 8, []⟩, true, [32]⟩ else none
        cells := fun _ offset => ⟨BitVec.ofNat 8 offset, true⟩
        views := [⟨0, 0, 32, true, true⟩], nextIdentity := 1 }
    """;
var spanCases = new (string Name, string Result)[]
{
    ("SpanFirst", ".i64 " + Word(0)), ("SpanCount", ".i32 4"), ("SpanSecond", ".i64 " + Word(1)),
    ("OwnerSpanFirst", ".i64 " + Word(0)), ("NestedSpanFirst", ".i64 " + Word(0))
};
var spanSources = new Dictionary<string, string>();
foreach (var (name, result) in spanCases)
{
    var output = Path.Combine(root, name);
    var parameter = "System.ReadOnlySpan`1<ulong>" + (name == "SpanFirst" ? "&" : "");
    Run(["dotnet", ExtractorPath, "extract", assembly, $"GenericOwners::{name}({parameter})", output]);
    var source = spanSources[name] = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = source + spanMemory + $$"""

        /-- The specialized helper reads the caller's four-word readonly view. -/
        theorem generic_span_result :
            (CIL.Safety.invoke Extracted.program 64 0 [.bufferSpan ⟨.address ⟨0, 0⟩, 4, 8, false⟩]
              spanMemory).map Prod.snd = .ok [.scalar ({{result}})] := by rfl
        #print axioms generic_span_result
        """;
    var proofPath = Path.Combine(root, name + ".lean");
    File.WriteAllText(proofPath, proof);
    evidence.Add(proofPath, "PASS generic span member call: " + name);
}

// Forged call targets must fail instantiation itself, not a later obligation.
Dictionary<string, string> Identities(string source) => Regex.Matches(source,
        @"(?m)^def (externalIdentity\d+)Bytes : ByteArray := ⟨#\[([0-9, ]*)\]⟩")
    .ToDictionary(match => match.Groups[1].Value, match => System.Text.Encoding.UTF8.GetString(
        match.Groups[2].Value.Split(", ").Select(byte.Parse).ToArray()));
string Target(string source, string text) =>
    Identities(source).Single(identity => identity.Value.Contains(text, StringComparison.Ordinal)).Key;
// Replace a target reference with a literal copy of its identity, edited in one place.
string Forge(string source, string line, string text, string from, string to)
{
    var target = Target(source, text);
    return line.Replace(target, System.Text.Json.JsonSerializer.Serialize(
        Identities(source)[target].Replace(from, to, StringComparison.Ordinal)), StringComparison.Ordinal);
}
const string closedItem = "<System.UInt64>::get_Item(";
var targetCases = new List<(string Name, string Fixture, string Definition, Func<string, string, string> Change)>
{
    ("unsubstituted", "SpanSecond", "method1Closed", (source, line) => line.Replace(
        Target(source, closedItem), Target(source, "<!!0>::get_Item("), StringComparison.Ordinal)),
    ("instantiation", "SpanSecond", "method1Closed", (source, line) =>
        Forge(source, line, closedItem, "<System.UInt64>", "<System.UInt32>")),
    ("member", "SpanSecond", "method1Closed", (source, line) => line
        .Replace(Target(source, closedItem), "SwappedTarget", StringComparison.Ordinal)
        .Replace(Target(source, "<System.UInt64>::Slice("), Target(source, closedItem), StringComparison.Ordinal)
        .Replace("SwappedTarget", Target(source, "<System.UInt64>::Slice("), StringComparison.Ordinal)),
    ("owner", "SpanSecond", "method1Closed", (source, line) =>
        Forge(source, line, closedItem, "System.ReadOnlySpan`1<", "System.Span`1<")),
    // An owner parameter spelling cannot stand for the method's own parameter.
    ("open-spelling", "SpanSecond", "method1Original", (source, line) =>
        Forge(source, line, "<!!0>::get_Item(", "<!!0>", "<!0>")),
    ("owner-argument", "OwnerSpanFirst", "method1Closed", (source, line) =>
        Forge(source, line, closedItem, "<System.UInt64>", "<System.UInt32>")),
    // `!1` is Inner's U = ulong; the outer owner's T = uint must not be substituted.
    ("nested-position", "NestedSpanFirst", "method1Closed", (source, line) =>
        Forge(source, line, closedItem, "<System.UInt64>", "<System.UInt32>"))
};
foreach (var (name, fixture, definition, change) in targetCases)
{
    var narrowed = NarrowEvidence(spanSources[fixture], "method1_specialization_validated");
    var path = Path.Combine(root, "target-" + name + ".lean");
    File.WriteAllText(path, ChangeDefinition(narrowed, definition, line => change(narrowed, line)));
    rejected.Add(path, "PASS rejected generic span call target: " + name, "Extraction.instantiateMethod");
}
evidence.Check();
rejected.Check();
