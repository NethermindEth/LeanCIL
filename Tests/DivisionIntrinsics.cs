#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using System.Runtime.Intrinsics.X86;
using Mono.Cecil;

using Program verification = new();
string assembly = At("Examples/Assembly/bin/Examples.dll");
using ModuleDefinition metadata = ModuleDefinition.ReadModule(assembly);
Dictionary<string, string> selectors = metadata.GetType("Examples.DivisionIntrinsics").Methods
    .ToDictionary(method => method.Name, method => method.FullName);
Type runtime = Assembly.LoadFile(assembly).GetType("Examples.DivisionIntrinsics")!;
string root = At("artifacts/DivisionIntrinsics");

foreach ((string name, ulong left, ulong right, ulong expected, bool wide) in new (string, ulong, ulong, ulong, bool)[]
{
    ("And", 13, 6, 4, false), ("Or", 13, 6, 15, false),
    ("Xor", 13, 6, 11, false), ("AndNot", 1, 3, 2, false),
    ("ShiftLeft", 1, 63, 1UL << 63, false), ("ShiftLeft", 1, 64, 0, false),
    ("ShiftLeft", 1, 256, 0, false), ("ShiftRight", ulong.MaxValue, 1, ulong.MaxValue >> 1, false),
    ("ShiftRight", ulong.MaxValue, ulong.MaxValue, 0, false),
    ("Less", 1, 1UL << 63, 255, true), ("Less", 1UL << 63, 1, 0, true),
    ("Greater", 1UL << 63, 1, 255, true), ("Greater", 1, 1, 0, true)
})
{
    string output = Path.Combine(root, name + "-" + right + "-" + left);
    Directory.CreateDirectory(output);
    string proof = Path.Combine(output, "Proof.lean");
    string word = wide ? "i32" : "i64";
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
        "theorem correctness : (CIL.Safety.invoke Extracted.program 256 0 [.scalar (.i64 " + left +
        "), .scalar (.i64 " + right + ")] Examples.empty).map Prod.snd = .ok [.scalar (." + word + " " + expected +
        ")] := by decide +kernel\nend ExampleProof\n");
    verification.Verify(assembly, "Examples", selectors[name], proof, output,
        profile: wide ? "x64-avx512dqvl" : "x64-avx2-bmi2");
    if (wide ? Avx512DQ.IsSupported && Avx512F.IsSupported : Avx2.IsSupported)
    {
        object result = runtime.GetMethod(name)!.Invoke(null, [left, right])!;
        ulong actual = wide ? (ulong)(int)result : (ulong)result;
        if (actual != expected) throw new InvalidOperationException("Runtime mismatch: " + name);
    }
    Console.WriteLine("PASS compiled division intrinsic: " + name);
}

string rejectedEncoding = Path.Combine(root, "Reject-Vector512Encoding");
Directory.CreateDirectory(rejectedEncoding);
string malformedAssembly = Path.Combine(rejectedEncoding, "Examples.dll");
using (ModuleDefinition module = ModuleDefinition.ReadModule(assembly))
{
    MethodDefinition less = module.GetType("Examples.DivisionIntrinsics").Methods.Single(method => method.Name == "Less");
    MethodReference combine = less.Body.Instructions.Select(instruction => instruction.Operand).OfType<MethodReference>()
        .First(method => method.DeclaringType.FullName == "System.Runtime.Intrinsics.Vector512");
    ((GenericInstanceType)combine.ReturnType).IsValueType = false;
    module.Write(malformedAssembly);
}
File.Delete(Path.Combine(rejectedEncoding, "Extracted.lean"));
(int Code, string Output, string Stdout, string Stderr) rejected = Execute(
    Extract("extract", malformedAssembly, "Examples", selectors["Less"], rejectedEncoding, "x64-avx512dqvl"));
if (rejected.Code == 0 || File.Exists(Path.Combine(rejectedEncoding, "Extracted.lean")) ||
    !rejected.Output.Contains("Unsupported vector type encoding", StringComparison.Ordinal))
    throw new InvalidOperationException("Malformed Vector512 signature was not rejected by the raw metadata check: " + rejected.Output);
Console.WriteLine("PASS malformed Vector512 signature rejection");
