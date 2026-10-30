#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs
#:include TailCallFixtures.cs

using System.Text.Json;
using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/ConstrainedCalls");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root);
var rejected = new RejectedEvidence(root);
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution", "Tests.ConstrainedEvidence");

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
    // Keep the exact emitted definitions and constrained obligations; unrelated certificates
    // are covered by the complete positive extraction above, not recomputed for each mutation.
    var obligations = Regex.Matches(source,
        @"(?m)^theorem method\d+_constrained_validated : [^\r\n]+\r?$");
    var methodCount = Regex.Matches(source, @"(?m)^def method\d+ : Method :=").Count;
    if (methodCount == 0 || obligations.Count != methodCount)
        throw new Exception("Unexpected constrained obligation count");
    var declarations = Regex.Replace(source,
        @"(?m)^(?:@\[[^\r\n]*\] )?theorem [^\r\n]*(?:\r?\n[ \t]+[^\r\n]*)*\r?\n", "");
    declarations = Regex.Replace(declarations, @"(?m)^#print axioms [^\r\n]*\r?\n", "");
    var narrowed = declarations.Replace("end Extracted", string.Join("\n", obligations.Select(match =>
        match.Value + "\n#print axioms " + Regex.Match(match.Value, @"theorem (\w+)").Groups[1].Value)) +
        "\nend Extracted", StringComparison.Ordinal);
    var control = CheckedEvidenceControl(source, narrowed, obligations.Select(match =>
        Regex.Match(match.Value, @"theorem (\w+)").Groups[1].Value), 0);
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

AddTailCallFixtures(assembly, root, evidence, rejected);
evidence.Check();
rejected.Check();

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
