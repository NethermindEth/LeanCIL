#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

var output = At("artifacts/GenericEvidence");
Directory.CreateDirectory(output);
Run(["lake", "build", "CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution"]);
var assembly = At("Examples/Assembly/bin/Examples.dll");
var samples = new[]
{
    "Identity64(ulong)", "Nested(ulong)", "Repeated(ulong)", "Mixed(int,byte)",
    "Select(bool,ulong,ulong)", "PackedSize()", "VectorSize()", "Swap32(int&,int&)",
    "SwapRecord(Examples.PackedLeaf&,Examples.PackedLeaf&)", "EnumIdentity(Examples.Signed8)",
    "NativeIdentity(nint)", "TwoTypes(ulong,uint)", "ClearPacked(uint)",
    "NextPacked(Examples.PackedLeaf&,int)", "Instance(ulong)"
};
foreach (var (selector, index) in samples.Select((selector, index) => (selector, index)))
{
    var folder = Path.Combine(output, index.ToString());
    Run(Extract("extract", assembly, "Examples", "GenericMethods::" + selector, folder));
    Run(["lake", "env", "lean", Path.Combine(folder, "Extracted.lean")]);
    Console.WriteLine("PASS structural specialization " + selector);
}

Run(["lake", "env", "lean", "Tests/ExtractionGenerics.lean"]);
string ChangeDefinition(string source, string name, Func<string, string> change)
{
    var start = source.IndexOf("def " + name + " :", StringComparison.Ordinal);
    if (start < 0) throw new InvalidOperationException("Missing definition " + name);
    var end = source.IndexOf('\n', start);
    return source[..start] + change(source[start..end]) + source[end..];
}
void Reject(int sample, string name, Func<string, string> mutate)
{
    var baseline = File.ReadAllText(Path.Combine(output, sample.ToString(), "Extracted.lean"));
    var source = mutate(baseline);
    if (source == baseline) throw new InvalidOperationException("Mutation did not change source: " + name);
    var path = Path.Combine(output, name + ".lean");
    File.WriteAllText(path, source);
    var result = Execute(["lake", "env", "lean", path]);
    if (result.Code == 0 || !result.Output.Contains("decide", StringComparison.Ordinal))
        throw new InvalidOperationException("Invalid specialization was not rejected: " + name + "\n" + result.Output);
    Console.WriteLine("PASS generic evidence rejects " + name);
}
Reject(0, "wrong-type-argument", source => ChangeDefinition(source, "method1TypeArgumentsRaw", line => line.Replace("System.UInt64", "System.UInt32")));
Reject(0, "wrong-closed-signature", source => ChangeDefinition(source, "method1Closed", line => line.Replace("System.UInt64", "System.UInt32")));
Reject(7, "wrong-closed-local", source => ChangeDefinition(source, "method1Closed", line => line.Replace("locals := [.atom", "locals := [.byref (.atom").Replace("], initLocals", ")], initLocals")));
Reject(12, "wrong-type-operand", source => ChangeDefinition(source, "method1Closed", line => line.Replace("operand := .type (.aggregate", "operand := .type (.byref (.aggregate").Replace(" 0) }", " 0)) }")));
Reject(0, "altered-opcode", source => ChangeDefinition(source, "method1Closed", line => line.Replace("opcode := 2,", "opcode := 3,")));
Reject(4, "altered-branch", source => ChangeDefinition(source, "method1Closed", line => line.Replace("operand := .target 4", "operand := .target 3")));
Reject(0, "wrong-managed-target", source => source.Replace(".call 1 1", ".call 0 1"));
Console.WriteLine("PASS original-metadata generic substitution, complete managed-call binding and malformed evidence rejection");
Reject(0, "omitted-method-evidence", source => ChangeDefinition(source, "methodEvidence", _ => "def methodEvidence : List Extraction.MethodEvidence := []"));
Reject(0, "reordered-method-evidence", source => ChangeDefinition(source, "methodEvidence", line => line.Replace("method0", "swapped").Replace("method1", "method0").Replace("swapped", "method1")));
Reject(0, "wrong-emitted-return", source => ChangeDefinition(source, "method1", line => line.Replace("returnsValue := true", "returnsValue := false")).Replace("method1.returnsValue = (true)", "method1.returnsValue = (false)"));
Reject(7, "wrong-local-initializer", source => source.Replace("[.i32 0]", "[.i32 1]"));
Reject(7, "wrong-initlocals-flag", source => source.Replace("initLocals := true", "initLocals := false"));
Reject(9, "missing-return-narrowing", source => source.Replace(".ret (some .signed8)", ".ret none"));
Reject(9, "wrong-return-signedness", source => source.Replace(".ret (some .signed8)", ".ret (some .unsigned8)"));
