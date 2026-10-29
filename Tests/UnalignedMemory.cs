#!/usr/bin/env dotnet
#:property PublishAot=false
#:property AllowUnsafeBlocks=true
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Numerics;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/UnalignedMemory");
Directory.CreateDirectory(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.UnalignedMemory")!;
using var metadata = ModuleDefinition.ReadModule(assembly);
var methods = metadata.GetType("Examples.UnalignedMemory").Methods.ToDictionary(method => method.Name);
var queue = new GeneratedQueue(verification, assembly);
var rejected = new RejectedEvidence(Path.Combine(root, "RejectedEvidence"));
var alignedOnly = args.Contains("--aligned-only", StringComparer.Ordinal);
foreach (var (suffix, width, shape, alignment) in new[]
{
    ("Signed", 1, "", 1), ("Half", 2, "", 1), ("Word", 8, "", 1),
    ("Aggregate", 32, "aggregate", 1), ("128", 16, "v128", 1), ("512", 64, "v512", 1),
    ("PointerWord", 8, "", 1), ("PointerAggregate", 32, "aggregate", 1),
    ("AlignedWord", 8, "", 8), ("AlignedAggregate", 32, "aggregate", 8), ("Aligned128", 16, "v128", 16)
}.Where(item => !alignedOnly || item.Item1.StartsWith("Aligned", StringComparison.Ordinal)))
{
    var runtimeRead = runtime.GetMethod("Read" + suffix)!;
    var type = runtimeRead.ReturnType;
    var readValue = typeof(Program).GetMethod(nameof(RuntimeRead), BindingFlags.Static | BindingFlags.NonPublic)!
        .MakeGenericMethod(type).Invoke(null, [runtimeRead, width, alignment])!;
    var bits = readValue switch
    {
        sbyte value => new BigInteger(unchecked((uint)value)),
        short value => new BigInteger(unchecked((uint)value)),
        ulong value => new BigInteger(value),
        _ => new BigInteger(Enumerable.Repeat((byte)255, width).ToArray(), isUnsigned: true)
    };
    typeof(Program).GetMethod(nameof(RuntimeWrite), BindingFlags.Static | BindingFlags.NonPublic)!
        .MakeGenericMethod(type).Invoke(null, [runtime.GetMethod("Write" + suffix)!, width, alignment]);
    foreach (var read in new[] { true, false })
    {
        var name = (read ? "Read" : "Write") + suffix;
        var output = Path.Combine(root, name);
        Directory.CreateDirectory(output);
        var proof = Path.Combine(output, "Proof.lean");
        var valueBits = read ? bits : new BigInteger(Enumerable.Repeat((byte)9, width).ToArray(), isUnsigned: true);
        var value = shape == "aggregate" ? $".aggregate (List.replicate {width} {(read ? 255 : 9)})" :
            $".{(shape == "" ? width == 8 ? "i64" : "i32" : shape)} {valueBits}";
        var arguments = read ? $"[.readOnlyReference (.address ⟨0, {alignment}⟩)]" :
            $"[.reference (.address ⟨0, {alignment}⟩), .scalar ({value})]";
        var claim = read
            ? $"({{RUN}}).map Prod.snd = .ok [.scalar ({value})]"
            : $"({{RUN}}).map (fun result => (result.2, " +
                $"(CIL.Safety.read result.1 ⟨0, 0⟩ {width + alignment + 1} 1).toOption)) = " +
                $".ok ([], some (List.replicate {alignment} 255 ++ List.replicate {width} 9 ++ [255]))";
        var invocation = $"CIL.Safety.invoke Extracted.program 32 0 {arguments} memory";
        var boundaries = name switch
        {
            "ReadAlignedWord" => """
                /-- Natural alignment is required independently of byte permissions and bounds. -/
                theorem misaligned : (CIL.Safety.invoke Extracted.program 32 0
                    [.reference (.address ⟨0, 1⟩)] memory) =
                    .error ⟨0, 1, .memory .alignment (.address ⟨0, 1⟩) 8⟩ := by rfl
                #print axioms misaligned
                """,
            "ReadPointerWord" => """
                /-- Numeric addresses cannot acquire pointer provenance at the call boundary. -/
                theorem numericPointer : (CIL.Safety.invoke Extracted.program 32 0
                    [.scalar (.i64 1)] memory).toOption = none := by rfl
                #print axioms numericPointer
                """,
            "ReadWord" => """
                /-- Scalar loads require initialized bytes. -/
                theorem unreadable : CIL.Safety.invoke Extracted.program 32 0
                    [.readOnlyReference (.address ⟨0, 1⟩)]
                    { memory with cells := fun _ _ => ⟨255, false⟩ } =
                    .error ⟨0, 1, .memory .uninitialized (.address ⟨0, 1⟩) 8⟩ := by rfl
                #print axioms unreadable
                /-- Byte alignment does not remove allocation bounds. -/
                theorem extent : CIL.Safety.invoke Extracted.program 32 0
                    [.reference (.address ⟨0, 3⟩)] memory =
                    .error ⟨0, 1, .memory .outsideAllocation (.address ⟨0, 3⟩) 8⟩ := by rfl
                #print axioms extent
                """,
            "WriteWord" or "WriteAlignedWord" => $$"""
                /-- Readonly references cannot acquire write authority. -/
                theorem readonly : CIL.Safety.invoke Extracted.program 32 0
                    [.readOnlyReference (.address ⟨0, {{alignment}}⟩), .scalar (.i64 0)] memory =
                    .error ⟨0, 2, .memory .unwritable (.address ⟨0, {{alignment}}⟩) 8⟩ := by rfl
                #print axioms readonly
                /-- Stores do not require read permission for the overwritten bytes. -/
                theorem writeOnly : (CIL.Safety.invoke Extracted.program 32 0
                    [.reference (.address ⟨0, {{alignment}}⟩), .scalar (.i64 0)]
                    { memory with views := [⟨0, 0, {{width + alignment + 1}}, false, true⟩] }).map Prod.snd =
                    .ok [] := by rfl
                #print axioms writeOnly
                """,
            "Read128" or "ReadAggregate" => $$"""
                /-- Snapshot transfers preserve uninitialized bytes. -/
                theorem partialSnapshot : (CIL.Safety.invoke Extracted.program 32 0
                    [.readOnlyReference (.address ⟨0, 1⟩)]
                    { memory with cells := fun _ _ => ⟨255, false⟩ }).map Prod.snd =
                    .ok [.scalar (.snapshot {{(shape == "aggregate" ? "(.aggregate 32)" : ".vector128")}}
                      (List.replicate {{width}} (255, false)))] := by rfl
                #print axioms partialSnapshot
                """,
            _ => ""
        };
        File.WriteAllText(proof, $$"""
            import Extracted
            import Examples.Support
            namespace ExampleProof
            /-- A successful observable result determines the execution result. -/
            private theorem result_of_toOption {error value : Type} {result : Except error value}
                {expected : value} (observed : result.toOption = some expected) :
                result = .ok expected := by
              cases result <;> simp_all [Except.toOption]
            #print axioms result_of_toOption
            def memory : CIL.Safety.Memory := { Examples.empty with
              allocations := fun identity => if identity == 0 then
                some ⟨.callerStack, ⟨{{width + alignment + 1}}, {{alignment}}, []⟩, true,
                  [{{width + alignment + 1}}]⟩ else none
              cells := fun _ _ => ⟨255, true⟩
              views := [⟨0, 0, {{width + alignment + 1}}, true, true⟩]
              nextIdentity := 1 }
            /-- The exact runtime value and caller-visible footprint agree. -/
            theorem correctness : {{claim.Replace("{RUN}", invocation, StringComparison.Ordinal)}} := by
              apply result_of_toOption
              decide +kernel
            #print axioms correctness
            {{boundaries}}
            end ExampleProof
            """);
        queue.Add(new(methods[name].FullName, proof, output),
            () => Console.WriteLine("PASS unaligned runtime, certificate and checked transfer: " + name));
    }
}
queue.Flush();
var rejectedIndex = 0;
foreach (var (name, theorem, before, after) in new[]
{
    ("ReadHalf", "method0_unsafe_validated", ".loadScalar 2 true", ".loadScalar 2 false"),
    ("ReadWord", "method0_unsafe_validated", ".loadScalar 8 false", ".loadScalar 4 false"),
    ("Read128", "method0_unsafe_validated", ".memory .load128", ".memory .load256"),
    ("Write512", "method0_unsafe_validated", ".memory .store512", ".memory .store256"),
    ("ReadAggregate", "method0_layouts_validated", ".loadAggregate 32", ".loadAggregate 16"),
    ("WriteAggregate", "method0_coverage_validated", ".size 2 0 .store", ".size 2 0 .load"),
    ("ReadWord", "method0_unsafe_validated", "target := .external externalIdentity0", "target := .external \"forged\""),
    ("ReadPointerWord", "method0_unsafe_validated", "target := .external externalIdentity0", "target := .external \"forged\""),
    ("ReadPointerAggregate", "method0_layouts_validated", ".loadAggregate 32", ".loadAggregate 16"),
    ("ReadAlignedWord", "method0_unsafe_validated", ".pointerTransfer (.scalar 8 false) 8 false",
        ".pointerTransfer (.scalar 8 false) 1 false"),
    ("ReadAlignedWord", "method0_unsafe_validated", ".pointerTransfer (.scalar 8 false) 8 false",
        ".pointerTransfer (.scalar 8 false) 8 true"),
    ("ReadAlignedAggregate", "method0_layouts_validated", ".pointerTransfer (.snapshot (.aggregate 32)) 8 false",
        ".pointerTransfer (.snapshot (.aggregate 32)) 4 false"),
    ("ReadAligned128", "method0_unsafe_validated", ".pointerTransfer (.snapshot .vector128) 16 false",
        ".pointerTransfer (.snapshot .vector128) 8 false")
}.Where(item => !alignedOnly || item.Item1.Contains("Aligned", StringComparison.Ordinal)))
{
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")), theorem);
    if (!source.Contains(before, StringComparison.Ordinal))
        throw new InvalidOperationException("Missing unaligned mutation target: " + name + "/" + before);
    var path = Path.Combine(root, name, "Rejected-" + theorem + "-" + rejectedIndex++ + ".lean");
    File.WriteAllText(path, source.Replace(before, after, StringComparison.Ordinal));
    rejected.Add(path, "PASS unaligned evidence rejection: " + name + "/" + theorem,
        theorem == "method0_unsafe_validated" ? "UnsafeCallsValid" :
        theorem == "method0_layouts_validated" ? "MethodLayoutsValid" : "LayoutUsesComplete");
}
rejected.Check();

partial class Program
{
    delegate T Reader<T>(in byte source);
    delegate void Writer<T>(ref byte destination, T value);
    unsafe delegate T PointerReader<T>(byte* source);
    unsafe delegate void PointerWriter<T>(byte* destination, T value);

    static unsafe int AlignedOffset(byte* buffer, int alignment) =>
        1 + (int)(((nuint)alignment - (nuint)(buffer + 1) % (nuint)alignment) % (nuint)alignment);

    static unsafe object RuntimeRead<T>(MethodInfo method, int width, int alignment) where T : struct
    {
        var bytes = Enumerable.Repeat((byte)255, width + alignment + 1).ToArray();
        T value;
        int offset;
        fixed (byte* buffer = bytes)
        {
            offset = AlignedOffset(buffer, alignment);
            value = method.GetParameters()[0].ParameterType.IsPointer
                ? method.CreateDelegate<PointerReader<T>>()(buffer + offset)
                : method.CreateDelegate<Reader<T>>()(in bytes[offset]);
        }
        var actual = MemoryMarshal.AsBytes(MemoryMarshal.CreateReadOnlySpan(ref value, 1));
        if (!actual.SequenceEqual(bytes.AsSpan(offset, width))) throw new Exception("Runtime read differs");
        return value;
    }

    static unsafe void RuntimeWrite<T>(MethodInfo method, int width, int alignment) where T : struct
    {
        var bytes = Enumerable.Repeat((byte)255, width + alignment + 1).ToArray();
        var valueBytes = Enumerable.Repeat((byte)9, width).ToArray();
        var value = Unsafe.ReadUnaligned<T>(ref valueBytes[0]);
        int offset;
        fixed (byte* buffer = bytes)
        {
            offset = AlignedOffset(buffer, alignment);
            if (method.GetParameters()[0].ParameterType.IsPointer)
                method.CreateDelegate<PointerWriter<T>>()(buffer + offset, value);
            else method.CreateDelegate<Writer<T>>()(ref bytes[offset], value);
        }
        if (bytes.Take(offset).Any(value => value != 255) || bytes.Skip(offset + width).Any(value => value != 255) ||
            !bytes.AsSpan(offset, width).SequenceEqual(valueBytes))
            throw new Exception("Runtime write footprint differs");
    }
}
