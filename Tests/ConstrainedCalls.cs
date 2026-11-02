#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs
#:include TailCallFixtures.cs

using System.Text;
using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/ConstrainedCalls");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root);
var rejected = new RejectedEvidence(root);
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution", "Tests.ConstrainedEvidence",
    "Tests.ConstantCalls");

// Keep the exact emitted definitions and constrained obligations; unrelated certificates
// are covered by the complete positive extraction, not recomputed for each mutation.
static string Narrowed(string source, out string control)
{
    var obligations = Regex.Matches(source,
        @"(?m)^theorem method\d+_constrained_validated : [^\r\n]+\r?$");
    var methodCount = Regex.Matches(source, @"(?m)^def method\d+ : Method :=").Count;
    if (methodCount == 0 || obligations.Count != methodCount)
        throw new Exception("Unexpected constrained obligation count");
    var declarations = Regex.Replace(source,
        @"(?m)^(?:@\[[^\r\n]*\] )?theorem [^\r\n]*(?:\r?\n[ \t]+[^\r\n]*)*\r?\n", "");
    declarations = Regex.Replace(declarations, @"(?m)^#print axioms [^\r\n]*\r?\n", "");
    var names = obligations.Select(match => Regex.Match(match.Value, @"theorem (\w+)").Groups[1].Value).ToArray();
    var narrowed = declarations.Replace("end Extracted", string.Join("\n", obligations.Zip(names).Select(pair =>
        pair.First.Value + "\n#print axioms " + pair.Second)) + "\nend Extracted", StringComparison.Ordinal);
    control = CheckedEvidenceControl(source, narrowed, names, 0);
    return narrowed;
}

var directAssembly = Path.Combine(root, "direct-generic.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.ConstrainedCalls").Methods.Single(method => method.Name == "DirectGeneric");
    var call = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Call);
    var target = (MethodReference)call.Operand;
    method.Body.GetILProcessor().InsertBefore(call, Instruction.Create(OpCodes.Constrained, target.DeclaringType));
    call.OpCode = OpCodes.Callvirt;
    module.Write(directAssembly);
}

foreach (var (name, type, expected) in new[]
{
    ("Implicit", "CounterValue", 42),
    ("Explicit", "ExplicitCounterValue", 43),
    ("Mutating", "CounterValue", 43),
    ("MutatingExplicit", "ExplicitCounterValue", 44),
    ("Generic", "GenericCounterValue`1<System.Int32>", 42),
    ("GenericExplicit", "ExplicitGenericCounterValue`1<System.Int32>", 44),
    ("DirectGeneric", "GenericCounterValue`1<System.Int32>", 42),
    ("ClosedBoth", "ClosedInterfaceCounter", 85),
    ("ClosedGeneric", "GenericInterfaceCounter`1<System.Int32>", 42)
})
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", name == "DirectGeneric" ? directAssembly : assembly,
        $"ConstrainedCalls::{name}(Examples.{type}&)", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    var extent = type.Contains('`') ? 8 : 4;
    File.WriteAllText(proof, source + $$"""

        private def inputMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨{{extent}}, 1, []⟩, true, []⟩ else none
          cells := fun _ offset => ⟨if offset == 0 then 42 else 0, true⟩
          views := [⟨0, 0, {{extent}}, true, true⟩]
          nextIdentity := 1 }
        theorem constrained_result :
            (CIL.Safety.invoke Extracted.program 32 0 [.reference (.address ⟨0, 0⟩)]
              inputMemory).map Prod.snd = .ok [.scalar (.i32 {{expected}})] := rfl
        #print axioms constrained_result
        """);

    var call = name == "DirectGeneric" ? ".call 1 2" : ".call 2 1";
    if (!source.Contains(call, StringComparison.Ordinal)) throw new Exception("Missing constrained call mutation target");
    var forged = Path.Combine(root, name + "-wrong-target.lean");
    var narrowed = Narrowed(source, out var control);
    File.AppendAllText(proof, "\n" + control);
    evidence.Add(proof, "PASS compiled constrained call, certificate and obligation eligibility: " + name);
    if (!type.Contains('`') && !name.StartsWith("Closed", StringComparison.Ordinal))
    {
        File.WriteAllText(forged, narrowed.Replace(call, ".call 0 1", StringComparison.Ordinal));
        rejected.Add(forged, "PASS forged constrained target: " + name, "ConstrainedCallsValid");
    }
    if (type.Contains('`'))
    {
        const string arguments = "ownerArguments := [.atom Extraction.runtimeScope \"System.Int32\"]";
        if (!narrowed.Contains(arguments, StringComparison.Ordinal))
            throw new Exception("Missing generic dispatch owner mutation target");
        var wrongOwner = Path.Combine(root, name + "-wrong-owner.lean");
        File.WriteAllText(wrongOwner, narrowed.Replace(arguments,
            "ownerArguments := [.atom Extraction.runtimeScope \"System.Int64\"]", StringComparison.Ordinal));
        rejected.Add(wrongOwner, "PASS forged constrained owner specialization: " + name, "ConstrainedCallsValid");
    }
    if (name == "ClosedBoth")
    {
        var forgedOwner = Path.Combine(root, name + "-wrong-interface.lean");
        var overrides = Regex.Match(narrowed, @"overrides := \[\(\d+, \.apply \([^\r\n]+?System.Int32""\)\)\]");
        if (!overrides.Success) throw new Exception("Missing closed interface override mutation target");
        File.WriteAllText(forgedOwner, narrowed.Replace(overrides.Value,
            overrides.Value.Replace("System.Int32", "System.Int64", StringComparison.Ordinal),
            StringComparison.Ordinal));
        rejected.Add(forgedOwner, "PASS wrong closed interface override with identical signature",
            "ConstrainedCallsValid");
    }
}

var twoOwners = Path.Combine(root, "TwoGenericOwners");
Run(["dotnet", ExtractorPath, "extract", assembly,
    "ConstrainedCalls::TwoGenericOwners(Examples.GenericCounterValue`1<System.Int32>&," +
    "Examples.GenericCounterValue`1<System.Int64>&)", twoOwners]);
var twoOwnerProof = Path.Combine(root, "TwoGenericOwners.lean");
File.WriteAllText(twoOwnerProof, File.ReadAllText(Path.Combine(twoOwners, "Extracted.lean")) + """

    private def twoOwnerMemory : CIL.Safety.Memory := {
      allocations := fun identity => if identity == 0 then
        some ⟨.callerStack, ⟨24, 1, []⟩, true, []⟩ else none
      cells := fun _ offset => ⟨if offset == 0 || offset == 8 then 42 else 0, true⟩
      views := [⟨0, 0, 24, true, true⟩]
      nextIdentity := 1 }
    theorem distinct_owner_results :
        (CIL.Safety.invoke Extracted.program 64 0
          [.reference (.address ⟨0, 0⟩), .reference (.address ⟨0, 8⟩)]
          twoOwnerMemory).map Prod.snd = .ok [.scalar (.i32 84)] := rfl
    #print axioms distinct_owner_results
    """);
evidence.Add(twoOwnerProof, "PASS distinct constrained owner specializations");

// `in` interface members and their explicit implementations carry modreq(InAttribute) on the reference.
// Words at 0, 8 and 16 hold 40, 1 and 1: Add yields 41 and Sum 42 only when every operand is read.
const string inAttribute = " modreq(System.Runtime.InteropServices.InAttribute)";
const string inMemory = """

    private def inMemory : CIL.Safety.Memory := {
      allocations := fun identity => if identity == 0 then
        some ⟨.callerStack, ⟨24, 8, []⟩, true, []⟩ else none
      cells := fun _ offset => ⟨if offset == 0 then 40 else if offset == 8 || offset == 16 then 1 else 0, true⟩
      views := [⟨0, 0, 24, true, true⟩]
      nextIdentity := 1 }
    """;
foreach (var (name, selector, claim) in new[]
{
    ("InExplicitAdd", "Examples.InWord::Examples.IInWord<Examples.InWord>.Add(Examples.InWord&" + inAttribute +
        ",Examples.InWord&)", """
        theorem in_result : ((CIL.Safety.invoke Extracted.program 32 0
            [.reference (.address ⟨0, 0⟩), .reference (.address ⟨0, 8⟩), .reference (.address ⟨0, 16⟩)]
            inMemory).map fun result => ((result.1.cells 0 16).bits, result.2)) = .ok (41, []) := rfl
        """),
    ("InExplicitSum", "Examples.InWord::Examples.IInWord<Examples.InWord>.Sum(System.ReadOnlySpan<ulong>&" +
        inAttribute + ")", """
        theorem in_result : (CIL.Safety.invoke Extracted.program 32 0
            [.reference (.address ⟨0, 0⟩), .bufferSpan ⟨.address ⟨0, 8⟩, 2, 8, false⟩]
            inMemory).map Prod.snd = .ok [.scalar (.i64 42)] := rfl
        """),
    // The specialized helper forwards its readonly span reference through the constrained slot.
    ("InConstrainedSum", "InParameters::ConstrainedSum(Examples.InWord&,System.ReadOnlySpan<ulong>)", """
        theorem in_result : (CIL.Safety.invoke Extracted.program 32 0
            [.reference (.address ⟨0, 0⟩), .bufferSpan ⟨.address ⟨0, 8⟩, 2, 8, false⟩]
            inMemory).map Prod.snd = .ok [.scalar (.i64 42)] := rfl
        """),
    ("InConstrained", "InParameters::Constrained(Examples.InWord&,Examples.InWord&)", """
        theorem in_result : (CIL.Safety.invoke Extracted.program 32 0
            [.reference (.address ⟨0, 0⟩), .reference (.address ⟨0, 8⟩)]
            inMemory).map Prod.snd = .ok [.scalar (.i64 41)] := rfl
        """)
})
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, selector, output]);
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, File.ReadAllText(Path.Combine(output, "Extracted.lean")) + inMemory + "\n" + claim +
        "#print axioms in_result\n");
    evidence.Add(proof, "PASS in-modifier reference parameter: " + name);
}

// Static interface slots dispatch through the closed operation and flag structs, as the runtime does.
var staticInterfaces = System.Reflection.Assembly.Load(File.ReadAllBytes(assembly))
    .GetType("Examples.StaticInterfaces")!;
foreach (var name in new[] { "AddCounted", "XorPlain" })
{
    var output = Path.Combine(root, "Static-" + name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"StaticInterfaces::{name}(ulong,ulong)", output]);
    var claims = new[] { (0UL, 0UL), (5UL, 7UL), (ulong.MaxValue, 1UL), (1UL << 63, ulong.MaxValue) }
        .Select(input => (input,
            result: (ulong)staticInterfaces.GetMethod(name)!.Invoke(null, [input.Item1, input.Item2])!))
        .Select(pair => $"(CIL.Safety.invoke Extracted.program 32 0 [.scalar (.i64 {pair.input.Item1}), " +
            $".scalar (.i64 {pair.input.Item2})] CIL.Safety.Memory.empty).map Prod.snd = " +
            $".ok [.scalar (.i64 {pair.result})]").ToArray();
    var proof = Path.Combine(root, "Static-" + name + ".lean");
    File.WriteAllText(proof, File.ReadAllText(Path.Combine(output, "Extracted.lean")) +
        "\ntheorem static_result :\n    " + string.Join(" ∧\n    ", claims) +
        " :=\n  ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\n#print axioms static_result\n");
    evidence.Add(proof, "PASS static interface dispatch: " + name);
}

// A flag getter whose body is a constant return prunes the block it guards, so the process clock read
// there is never extracted; results match the runtime, which runs neither read for these flags.
var constantFlags = staticInterfaces.Assembly.GetType("Examples.ConstantFlags")!;
foreach (var name in new[] { "TraceOff", "CountOn" })
{
    var output = Path.Combine(root, "Flags-" + name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"ConstantFlags::{name}(ulong)", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    if (!source.Contains(".unsupported \"Unreachable under selected profile\"", StringComparison.Ordinal))
        throw new Exception("Constant flag block was not pruned: " + name);
    var claims = new[] { 0UL, 5UL, ulong.MaxValue, 1UL << 63 }
        .Select(input => (input, result: (ulong)constantFlags.GetMethod(name)!.Invoke(null, [input])!))
        .Select(pair => $"(CIL.Safety.invoke Extracted.program 32 0 [.scalar (.i64 {pair.input})] " +
            $"CIL.Safety.Memory.empty).map Prod.snd = .ok [.scalar (.i64 {pair.result})]").ToArray();
    var proof = Path.Combine(root, "Flags-" + name + ".lean");
    File.WriteAllText(proof, source + "\ntheorem flag_result :\n    " + string.Join(" ∧\n    ", claims) +
        " :=\n  ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\n#print axioms flag_result\n");
    evidence.Add(proof, "PASS constant flag pruning: " + name);
}

// The caller's certificate is rechecked against the called getter: pointing the call at the other
// getter, claiming the other word or changing the getter's loaded word each fail feature flow.
var flagsOutput = Path.Combine(root, "Flags-TraceThenCount");
Run(["dotnet", ExtractorPath, "extract", assembly, "ConstantFlags::TraceThenCount(ulong)", flagsOutput]);
var flags = File.ReadAllText(Path.Combine(flagsOutput, "Extracted.lean"));
var offCaller = Regex.Match(flags, @"(?m)^def method(\d+)Signature : String := ""[^""]+Trace\\u003CExamples\.StepOff");
var offGetter = Regex.Match(flags, @"(?m)^def method(\d+)Signature : String := ""[^""]+StepOff::get_IsActive");
var onGetter = Regex.Match(flags, @"(?m)^def method(\d+)Signature : String := ""[^""]+StepOn::get_IsActive");
if (!offCaller.Success || !offGetter.Success || !onGetter.Success)
    throw new Exception("Missing constant flag mutation targets");
var (callerIndex, offIndex, onIndex) =
    (offCaller.Groups[1].Value, offGetter.Groups[1].Value, onGetter.Groups[1].Value);
var offCall = $".call {offIndex} 0";
var callerStates = Regex.Match(flags, $@"(?m)^def method{callerIndex}FeatureStates : [^\r\n]+");
var offBody = Regex.Match(flags, $@"(?m)^def method{offIndex}Closed : [^\r\n]+");
const string offWord = "stack := [some (BitVec.ofInt 32 (0))]";
const string offLoad = "{ offset := 0, opcode := 22, operand := .none }";
if (!flags.Contains(offCall, StringComparison.Ordinal) ||
    !callerStates.Value.Contains(offWord, StringComparison.Ordinal) ||
    !offBody.Value.Contains(offLoad, StringComparison.Ordinal))
    throw new Exception("Missing constant flag mutation sites");
foreach (var (mutation, forgedSource) in new[]
{
    ("swapped-callee", flags.Replace(offCall, $".call {onIndex} 0", StringComparison.Ordinal)),
    ("forged-word", flags.Replace(callerStates.Value, new Regex(Regex.Escape(offWord)).Replace(
        callerStates.Value, "stack := [some (BitVec.ofInt 32 (1))]", 1), StringComparison.Ordinal)),
    ("callee-word", flags.Replace(offBody.Value, offBody.Value.Replace(offLoad,
        "{ offset := 0, opcode := 21, operand := .none }", StringComparison.Ordinal), StringComparison.Ordinal))
})
{
    var forged = Path.Combine(root, "Flags-" + mutation + ".lean");
    File.WriteAllText(forged, forgedSource);
    rejected.Add(forged, "PASS forged constant flag: " + mutation,
        $"Extraction.FeatureFlowValid rawLayouts.toArray specializedMethods method{callerIndex}Closed");
}

// Extraction keeps the guarded block, and so rejects its clock read, whenever the flag is live or the
// getter is anything but an exact constant return, even one that still evaluates to false.
const string clockRejection = "Contract imports from framework assemblies are not supported";
foreach (var (mutation, selector) in new[]
{
    ("live-flag", "TraceOn"), ("swapped-flag", "TraceOff"), ("computed-flag", "TraceOff")
})
{
    var dll = assembly;
    if (mutation != "live-flag")
    {
        dll = Path.Combine(root, "flags-" + mutation + ".dll");
        using var module = ModuleDefinition.ReadModule(assembly);
        var getter = module.GetType("Examples.StepOff").Methods.Single(method => method.Name == "get_IsActive");
        var body = getter.Body.GetILProcessor();
        var load = getter.Body.Instructions[0];
        if (mutation == "swapped-flag") load.OpCode = OpCodes.Ldc_I4_1;
        else
        {
            body.InsertAfter(load, Instruction.Create(OpCodes.Ldc_I4_0));
            body.InsertAfter(load.Next, Instruction.Create(OpCodes.Or));
        }
        module.Write(dll);
    }
    var result = Execute(["dotnet", ExtractorPath, "extract", dll, $"ConstantFlags::{selector}(ulong)",
        Path.Combine(root, "Reject-flags-" + mutation)]);
    if (result.Code == 0 || !result.Output.Contains(clockRejection, StringComparison.Ordinal))
        throw new Exception("Incorrect live constant flag rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS live constant flag rejection: " + mutation);
}

// A generic static virtual slot runs the interface default for a struct without an override and the
// override otherwise; the balance left behind (less the price or twice it) tells them apart.
var examples = System.Reflection.Assembly.Load(File.ReadAllBytes(assembly));
var defaultNarrowed = new Dictionary<string, string>();
foreach (var (name, type) in new[] { ("SpendDefault", "Allowance"), ("SpendOverride", "DoublingAllowance") })
{
    var output = Path.Combine(root, "Static-" + name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"StaticVirtualDefaults::{name}(Examples.{type}&)", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var receiverType = examples.GetType("Examples." + type)!;
    var left = receiverType.GetField("Left")!;
    var memories = new StringBuilder();
    var claims = new[] { 42UL, 6UL, 5UL, 0UL }.Select(balance =>
    {
        var receiver = Activator.CreateInstance(receiverType)!;
        left.SetValue(receiver, balance);
        object[] arguments = [receiver];
        var result = (ulong)examples.GetType("Examples.StaticVirtualDefaults")!.GetMethod(name)!
            .Invoke(null, arguments)!;
        memories.Append($$"""

            private def memory{{balance}} : CIL.Safety.Memory := {
              allocations := fun identity => if identity == 0 then
                some ⟨.callerStack, ⟨8, 8, []⟩, true, []⟩ else none
              cells := fun _ offset => ⟨if offset == 0 then {{balance}} else 0, true⟩
              views := [⟨0, 0, 8, true, true⟩]
              nextIdentity := 1 }
            """);
        return $"((CIL.Safety.invoke Extracted.program 32 0 [.reference (.address ⟨0, 0⟩)] memory{balance}).map " +
            $"fun result => ((result.1.cells 0 0).bits, result.2)) = " +
            $".ok ({left.GetValue(arguments[0])}, [.scalar (.i64 {result})])";
    }).ToArray();
    var proof = Path.Combine(root, "Static-" + name + ".lean");
    File.WriteAllText(proof, source + memories + "\n\ntheorem default_result :\n    " +
        string.Join(" ∧\n    ", claims) + " :=\n  ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\n" +
        "#print axioms default_result\n");
    defaultNarrowed[name] = Narrowed(source, out var control);
    File.AppendAllText(proof, "\n" + control);
    evidence.Add(proof, "PASS static virtual default dispatch: " + name);
}

// The emitted call must name the resolved instance: another method, a hidden override or a changed
// method type argument each leave the caller's constrained obligation unprovable.
var (spendDefault, spendOverride) = (defaultNarrowed["SpendDefault"], defaultNarrowed["SpendOverride"]);
var defaultSite = Regex.Match(spendDefault, @"target := \.managed (\d+), typeArguments := \[(\.aggregate ""[^""]+" +
    @"TriplePrice"" \d+), (\.aggregate ""[^""]+Allowance"" \d+)\], ownerArgumentCount := 1");
var overrideSite = Regex.Match(spendOverride, @"target := \.managed (\d+), typeArguments := \[\.aggregate ""[^""]+" +
    @"TriplePrice"" \d+, \.aggregate ""[^""]+DoublingAllowance"" \d+\], ownerArgumentCount := 1");
var hiddenOverride = overrideSite.Success ? Regex.Match(spendOverride,
    @"overrides := \[\(" + overrideSite.Groups[1].Value + @", [^\r\n]+?DoublingAllowance"" \d+\)\)\]") : Match.Empty;
var defaultBody = Regex.Match(spendDefault, @"def method(\d+)Original : Extraction.RawMethod := " +
    @"\{ token := \d+, owner := ""[^""]+::Examples.IAllowance\\u00601""");
var defaultCalls = Regex.Matches(spendDefault, @"(?m)^  \.call " + defaultBody.Groups[1].Value + @" 1,\r?$");
if (!defaultSite.Success || !hiddenOverride.Success || !defaultBody.Success || defaultCalls.Count != 1)
    throw new Exception("Missing static virtual default mutation target");
foreach (var (mutation, forgedSource) in new[]
{
    ("wrong-target", spendDefault.Replace(defaultCalls[0].Value, "  .call 0 1,", StringComparison.Ordinal)),
    ("hidden-override", spendOverride.Replace(hiddenOverride.Value, "overrides := []", StringComparison.Ordinal)),
    ("method-argument", spendDefault.Replace(defaultSite.Value, defaultSite.Value.Replace(
        defaultSite.Groups[2].Value + ", ", defaultSite.Groups[3].Value + ", ", StringComparison.Ordinal),
        StringComparison.Ordinal))
})
{
    var forged = Path.Combine(root, "Static-default-" + mutation + ".lean");
    File.WriteAllText(forged, forgedSource);
    rejected.Add(forged, "PASS forged static virtual default dispatch: " + mutation, "ConstrainedCallsValid");
}

AddTailCallFixtures(assembly, root, evidence, rejected);
evidence.Check();
rejected.Check();

// A static slot needs `call` and a unique static implementation on the receiver.
foreach (var (mutation, marker) in new[]
{
    ("static-callvirt", "Unsupported constrained method slot"),
    ("static-implementation", "has no unique struct implementation")
})
{
    var dll = Path.Combine(root, mutation + ".dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var step = module.GetType("Examples.StaticInterfaces").Methods.Single(method => method.Name == "Step");
        var flag = step.Body.Instructions.First(instruction => instruction.OpCode.Code == Code.Constrained).Next;
        if (mutation == "static-callvirt") flag.OpCode = OpCodes.Callvirt;
        else
        {
            // Roslyn records even an implicit static implementation as an explicit override.
            var getter = module.GetType("Examples.StepOn").Methods.Single(method => method.Name == "get_IsActive");
            getter.Overrides.Clear();
            getter.Name = "get_Inactive";
        }
        module.Write(dll);
    }
    var staticRejection = Execute(["dotnet", ExtractorPath, "extract", dll,
        "StaticInterfaces::AddCounted(ulong,ulong)", Path.Combine(root, "Reject-" + mutation)]);
    if (staticRejection.Code == 0 || !staticRejection.Output.Contains(marker, StringComparison.Ordinal))
        throw new Exception("Incorrect static constrained rejection: " + mutation + "\n" + staticRejection.Output);
    Console.WriteLine("PASS static constrained extraction rejection: " + mutation);
}

// The runtime runs a derived interface's re-implementation (price less one), not the default body, so
// extraction must not select the default for that receiver.
var refunding = examples.GetType("Examples.RefundingAllowance")!;
var refundingReceiver = Activator.CreateInstance(refunding)!;
refunding.GetField("Left")!.SetValue(refundingReceiver, 42UL);
object[] refundingArguments = [refundingReceiver];
examples.GetType("Examples.StaticVirtualDefaults")!.GetMethod("SpendRefunding")!.Invoke(null, refundingArguments);
if ((ulong)refunding.GetField("Left")!.GetValue(refundingArguments[0])! != 40)
    throw new Exception("Derived interface re-implementation did not run");
var shadowed = Execute(["dotnet", ExtractorPath, "extract", assembly,
    "StaticVirtualDefaults::SpendRefunding(Examples.RefundingAllowance&)",
    Path.Combine(root, "Reject-shadowed-default")]);
if (shadowed.Code == 0 ||
    !shadowed.Output.Contains("Another interface of the receiver re-implements", StringComparison.Ordinal))
    throw new Exception("Incorrect shadowed default rejection\n" + shadowed.Output);
Console.WriteLine("PASS static default extraction rejection: derived interface re-implementation");

// An abstract generic slot has no fallback, and an unrecorded same-signature struct method beside a
// default body is ambiguous: neither may resolve to the interface body.
// A receiver interface from another assembly cannot be checked for a re-implementation, so it fails closed.
foreach (var (mutation, marker) in new[]
{
    ("abstract-generic-slot", "has no unique struct implementation"),
    ("unrecorded-implementation", "has no unique struct implementation"),
    ("external-interface", "requires every interface of the receiver")
})
{
    var dll = Path.Combine(root, mutation + ".dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var slot = module.GetType("Examples.IAllowance`1").Methods
            .Single(method => method.Name == "Spend" && method.HasGenericParameters);
        if (mutation == "abstract-generic-slot")
        {
            slot.Body = null;
            slot.Attributes |= MethodAttributes.Abstract;
        }
        else if (mutation == "external-interface")
            module.GetType("Examples.Allowance").Interfaces.Add(
                new InterfaceImplementation(module.ImportReference(typeof(IDisposable))));
        else
        {
            var receiver = module.GetType("Examples.Allowance");
            var unrecorded = new MethodDefinition("Spend", MethodAttributes.Public | MethodAttributes.Static |
                MethodAttributes.HideBySig, slot.ReturnType);
            unrecorded.GenericParameters.Add(new GenericParameter("TPrice", unrecorded));
            unrecorded.Parameters.Add(new ParameterDefinition(new ByReferenceType(receiver)));
            unrecorded.Body.GetILProcessor().Append(Instruction.Create(OpCodes.Ldc_I4_0));
            unrecorded.Body.GetILProcessor().Append(Instruction.Create(OpCodes.Ret));
            receiver.Methods.Add(unrecorded);
        }
        module.Write(dll);
    }
    var defaultRejection = Execute(["dotnet", ExtractorPath, "extract", dll,
        "StaticVirtualDefaults::SpendDefault(Examples.Allowance&)", Path.Combine(root, "Reject-" + mutation)]);
    if (defaultRejection.Code == 0 ||
        !defaultRejection.Output.Contains(marker, StringComparison.Ordinal))
        throw new Exception("Incorrect static default rejection: " + mutation + "\n" + defaultRejection.Output);
    Console.WriteLine("PASS static default extraction rejection: " + mutation);
}

foreach (var (mutation, marker) in new[]
{
    ("prefix", "adjacent concrete constrained receiver"),
    ("branch", "Branch bypasses constrained receiver prefix"),
    ("constraint", "Unsupported generic method constraints")
})
{
    var dll = Path.Combine(root, mutation + ".dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.ConstrainedCalls").Methods.Single(method => method.Name == "Read");
        var prefix = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Constrained);
        if (mutation == "prefix") { prefix.OpCode = OpCodes.Nop; prefix.Operand = null; }
        else if (mutation == "branch")
            method.Body.GetILProcessor().InsertBefore(prefix, Instruction.Create(OpCodes.Br, prefix.Next));
        else module.GetType("Examples.CounterValue").Interfaces.Clear();
        module.Write(dll);
    }
    var extractionRejection = Execute(["dotnet", ExtractorPath, "extract", dll,
        "ConstrainedCalls::Implicit(Examples.CounterValue&)", Path.Combine(root, "Reject-" + mutation)]);
    if (extractionRejection.Code == 0 || !extractionRejection.Output.Contains(marker, StringComparison.Ordinal))
        throw new Exception("Incorrect constrained rejection: " + mutation + "\n" + extractionRejection.Output);
    Console.WriteLine("PASS constrained extraction rejection: " + mutation);
}

// Only System.Runtime's modreq(InAttribute) directly on a by-reference parameter is admitted.
const string modifierRejection = "except System.Runtime's modreq(InAttribute) directly on a by-reference parameter";
MethodDefinition InAdd(ModuleDefinition module) => module.GetType("Examples.InWord").Methods
    .Single(method => method.Name.EndsWith(".Add", StringComparison.Ordinal));
foreach (var mutation in new[] { "modopt", "other-modreq", "by-value", "nested", "versioned-scope", "foreign-scope" })
{
    var dll = Path.Combine(root, "in-" + mutation + ".dll");
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = InAdd(module);
        var modified = (RequiredModifierType)method.Parameters[0].ParameterType;
        var reference = (ByReferenceType)modified.ElementType;
        var runtime = (AssemblyNameReference)modified.ModifierType.Scope;
        TypeReference Forged(AssemblyNameReference scope) =>
            new(modified.ModifierType.Namespace, modified.ModifierType.Name, module, scope);
        method.Parameters[0].ParameterType = mutation switch
        {
            "modopt" => new OptionalModifierType(modified.ModifierType, reference),
            "other-modreq" => new RequiredModifierType(
                new TypeReference("System.Runtime.CompilerServices", "IsVolatile", module, runtime), reference),
            "by-value" => new RequiredModifierType(modified.ModifierType, reference.ElementType),
            "nested" => new ByReferenceType(new RequiredModifierType(modified.ModifierType, reference.ElementType)),
            "versioned-scope" => new RequiredModifierType(Forged(new AssemblyNameReference(runtime.Name,
                new Version(9, 0, 0, 0)) { PublicKeyToken = runtime.PublicKeyToken }), reference),
            _ => new RequiredModifierType(Forged(new AssemblyNameReference("Forged", runtime.Version)), reference)
        };
        selector = method.FullName;
        module.Write(dll);
    }
    var result = Execute(["dotnet", ExtractorPath, "extract", dll, selector,
        Path.Combine(root, "Reject-in-" + mutation)]);
    if (result.Code == 0 || !result.Output.Contains(modifierRejection, StringComparison.Ordinal))
        throw new Exception("Incorrect in-modifier rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS in-modifier rejection: " + mutation);
}

// A slot reference without the modifier names a different signature, so it cannot reach the `in` member.
var plainSlot = Path.Combine(root, "in-plain-slot.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var call = (MethodReference)module.GetType("Examples.InParameters").Methods.Single(method => method.Name == "Add")
        .Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Callvirt).Operand;
    call.Parameters[0].ParameterType = ((RequiredModifierType)call.Parameters[0].ParameterType).ElementType;
    module.Write(plainSlot);
}
var plainSlotResult = Execute(["dotnet", ExtractorPath, "extract", plainSlot,
    "InParameters::Constrained(Examples.InWord&,Examples.InWord&)", Path.Combine(root, "Reject-in-plain-slot")]);
if (plainSlotResult.Code == 0 ||
    !plainSlotResult.Output.Contains("Unsupported constrained method slot", StringComparison.Ordinal))
    throw new Exception("Incorrect plain slot rejection\n" + plainSlotResult.Output);
Console.WriteLine("PASS in-modifier rejection: plain slot reference");

// Signatures differing only in the modifier are rejected: the certificate erases it.
var twin = Path.Combine(root, "in-twin.dll");
string inSelector, plainSelector;
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = InAdd(module);
    var copy = new MethodDefinition(method.Name, MethodAttributes.Private | MethodAttributes.HideBySig,
        method.ReturnType);
    var plain = ((RequiredModifierType)method.Parameters[0].ParameterType).ElementType;
    copy.Parameters.Add(new ParameterDefinition(plain));
    copy.Parameters.Add(new ParameterDefinition(method.Parameters[1].ParameterType));
    foreach (var instruction in method.Body.Instructions)
    {
        var cloned = Instruction.Create(OpCodes.Nop);
        cloned.OpCode = instruction.OpCode;
        cloned.Operand = instruction.Operand;
        copy.Body.Instructions.Add(cloned);
    }
    if (method.Body.Instructions.Any(instruction =>
        instruction.Operand is Instruction or Instruction[] or ParameterDefinition))
        throw new Exception("In-modifier twin requires a straight-line body with short argument loads");
    method.DeclaringType.Methods.Add(copy);
    (inSelector, plainSelector) = (method.FullName, copy.FullName);
    module.Write(twin);
}
foreach (var (selector, index) in new[] { (inSelector, 0), (plainSelector, 1) })
{
    var result = Execute(["dotnet", ExtractorPath, "extract", twin, selector,
        Path.Combine(root, "in-twin-" + index)]);
    if (result.Code == 0 || !result.Output.Contains("Ambiguous in-parameter twin", StringComparison.Ordinal) ||
        !result.Output.Contains("cannot distinguish modifier-only overloads", StringComparison.Ordinal))
        throw new Exception("Incorrect in-modifier twin rejection: " + selector + "\n" + result.Output);
}
Console.WriteLine("PASS in-modifier rejection: modifier-only twins");

// A `ref readonly` return carries the same modifier, which is admitted only on parameters.
var readOnlyReturn = Path.Combine(root, "in-return.dll");
string returnSelector;
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.InWord").Methods
        .Single(method => method.Name.EndsWith(".Sum", StringComparison.Ordinal));
    var modifier = ((RequiredModifierType)method.Parameters[0].ParameterType).ModifierType;
    method.ReturnType = new RequiredModifierType(modifier, new ByReferenceType(method.ReturnType));
    returnSelector = method.FullName;
    module.Write(readOnlyReturn);
}
var returnResult = Execute(["dotnet", ExtractorPath, "extract", readOnlyReturn, returnSelector,
    Path.Combine(root, "Reject-in-return")]);
const string returnRejection = "Custom modifiers are unsupported in typed contract signatures: System.UInt64& modreq(";
if (returnResult.Code == 0 || !returnResult.Output.Contains(returnRejection, StringComparison.Ordinal))
    throw new Exception("Incorrect in-modifier return rejection\n" + returnResult.Output);
Console.WriteLine("PASS in-modifier rejection: ref readonly return");
