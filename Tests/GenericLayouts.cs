#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs
#:include PinnedMetadata.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/GenericLayouts");
Directory.CreateDirectory(root);
var extractor = Assembly.LoadFrom(ExtractorPath);
if (!LayoutVisits() || args.Contains("--layout-visits-only", StringComparer.Ordinal)) return;

bool LayoutVisits()
{
    const BindingFlags members = BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static;
    using var pinned = new PinnedMetadata(extractor, assembly);
    var module = pinned.Module;
    var box = module.GetType("Examples.IndirectValues/Box`1");
    var method = new MethodDefinition("LayoutVisits", Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
    module.GetType("Examples.IndirectValues").Methods.Add(method);
    var validation = extractor.GetType("Nethermind.LeanCIL.MetadataValidation", true)!;
    var context = validation.GetNestedType("LayoutContext", members)!;
    var emitter = extractor.GetType("Nethermind.LeanCIL.LeanEmitter", true)!;
    var collect = emitter.GetMethod("LayoutTypes", members)!;
    var signatures = pinned.Context.GetType().GetProperty("Signatures", members)!.GetValue(pinned.Context)!;
    var visits = signatures.GetType().GetProperty("NodeVisits", members)!;
    long Count() => (long)visits.GetValue(signatures)!;
    bool passed = true;
    foreach (int depth in new[] { 8, 16, 32 })
    {
        TypeReference nested = module.TypeSystem.UInt64;
        for (int index = 0; index < depth; index++)
        {
            var instance = new GenericInstanceType(box);
            instance.GenericArguments.Add(nested);
            nested = instance;
        }
        method.Body.Variables.Clear();
        method.Body.Variables.Add(new VariableDefinition(nested));
        var layouts = Activator.CreateInstance(context, members | BindingFlags.Public, null, [module, "scalar"], null);
        long before = Count();
        var rows = (TypeReference[])collect.Invoke(null, [new[] { method }, layouts])!;
        long observed = Count() - before;
        // Each application, the shared Box constructor and the UInt64 leaf are distinct nodes.
        int distinct = depth + 2;
        Console.WriteLine($"Layout depth {depth}: {rows.Length} rows, {observed} visits, {distinct} distinct nodes");
        passed &= rows.Length == depth && observed == distinct;
    }
    if (!passed) Environment.ExitCode = 1;
    return passed;
}

// Identities are read from metadata rows, so the same-named definition is written into an image.
var shadowImage = Path.Combine(root, "Shadowed.dll");
using (var source = ModuleDefinition.ReadModule(assembly))
{
    var shadow = new TypeDefinition("System", "UInt64", Mono.Cecil.TypeAttributes.Public |
        Mono.Cecil.TypeAttributes.Sealed | Mono.Cecil.TypeAttributes.SequentialLayout,
        source.GetType("Examples.GenericPair`1").BaseType);
    shadow.Fields.Add(new FieldDefinition("First", Mono.Cecil.FieldAttributes.Public, source.TypeSystem.UInt64));
    shadow.Fields.Add(new FieldDefinition("Second", Mono.Cecil.FieldAttributes.Public, source.TypeSystem.UInt64));
    source.Types.Add(shadow);
    var pair = source.GetType("Examples.GenericPair`1");
    var closed = new GenericInstanceType(pair);
    var word = source.TypeSystem.UInt64;
    closed.GenericArguments.Add(word);
    var scope = ((AssemblyNameReference)word.Scope).FullName;
    var literal = new TypeDefinition(pair.Namespace, $"{pair.Name}<{scope}::{word.FullName}>",
        pair.Attributes, pair.BaseType);
    foreach (var field in pair.Fields.Where(field => !field.IsStatic))
        literal.Fields.Add(new FieldDefinition(field.Name, field.Attributes, word));
    source.Types.Add(literal);
    // Both locals have the same physical layout. Their metadata identities must still be distinguishable.
    var method = new MethodDefinition("AmbiguousLocals", Mono.Cecil.MethodAttributes.Static, source.TypeSystem.Void);
    source.GetType("Examples.GenericLayouts").Methods.Add(method);
    method.Body.Variables.Add(new VariableDefinition(closed));
    method.Body.Variables.Add(new VariableDefinition(literal));
    method.Body.GetILProcessor().Emit(OpCodes.Ret);
    source.Write(shadowImage);
}
var ambiguous = Execute(["dotnet", ExtractorPath, "extract", shadowImage, "GenericLayouts::AmbiguousLocals()",
    Path.Combine(root, "AmbiguousLocals")]);
if (ambiguous.Code == 0 || !ambiguous.Output.Contains("Ambiguous layout identity:", StringComparison.Ordinal))
    throw new InvalidOperationException($"Expected a refusal for the ambiguous layout spelling: {ambiguous.Output}");
Console.WriteLine("PASS extraction refuses distinct layout identities with the same spelling");
using (var pinned = new PinnedMetadata(extractor, shadowImage))
{
    var module = pinned.Module;
    var owner = module.GetType("Examples.GenericPair`1");
    var shadow = module.GetType("System.UInt64") ??
        throw new InvalidOperationException("Missing same-named definition in the written image");
    var genuine = new GenericInstanceType(owner);
    genuine.GenericArguments.Add(module.TypeSystem.UInt64);
    var shadowed = new GenericInstanceType(owner);
    shadowed.GenericArguments.Add(shadow);
    var validation = extractor.GetType("Nethermind.LeanCIL.MetadataValidation")!;
    var context = validation.GetNestedType("LayoutContext", BindingFlags.NonPublic)!;
    var instance = Activator.CreateInstance(context, BindingFlags.Instance | BindingFlags.Public |
        BindingFlags.NonPublic, null, [module, "scalar"], null)!;
    var size = context.GetMethod("Size", BindingFlags.Instance | BindingFlags.NonPublic)!;
    if (genuine.FullName != shadowed.FullName || !Equals(size.Invoke(instance, [genuine]), 16) ||
        !Equals(size.Invoke(instance, [shadowed]), 32) || !Equals(size.Invoke(instance, [genuine]), 16))
        throw new InvalidOperationException("Generic layout cache lost an argument's assembly scope");
    var specializations = extractor.GetType("Nethermind.LeanCIL.MethodSpecialization")!;
    var methods = Activator.CreateInstance(specializations, BindingFlags.Instance | BindingFlags.Public |
        BindingFlags.NonPublic, null, [module, "scalar"], null)!;
    var instantiate = specializations.GetMethod("Instantiate", BindingFlags.Instance | BindingFlags.NonPublic)!;
    var getter = owner.Methods.Single(method => method.Name == "GetSecond");
    var genuineGetter = new MethodReference(getter.Name, getter.ReturnType, genuine) { HasThis = true };
    var shadowGetter = new MethodReference(getter.Name, getter.ReturnType, shadowed) { HasThis = true };
    var first = instantiate.Invoke(methods, [genuineGetter]);
    var second = instantiate.Invoke(methods, [shadowGetter]);
    if (ReferenceEquals(first, second) || !ReferenceEquals(first, instantiate.Invoke(methods, [genuineGetter])))
        throw new InvalidOperationException("Generic method cache lost an argument's assembly scope");
    Console.WriteLine("PASS generic layout cache distinguishes equal names in different scopes");
}
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution");
var evidence = new GeneratedEvidence(root);
var rejected = new RejectedEvidence(root);
var dottedImage = Path.Combine(root, "DottedDeclarations.dll");
using (var source = ModuleDefinition.ReadModule(assembly))
{
    foreach (var type in new[] { source.GetType("Examples.Packet"), source.GetType("Examples.GenericPair`1") })
    {
        type.Name = type.FullName;
        type.Namespace = "";
    }
    source.Write(dottedImage);
}
foreach (var (label, image, otherSpace, otherName) in new[]
{
    ("QualifiedPacket", assembly, "", "Examples.Packet"), ("DottedPacket", dottedImage, "Examples", "Packet")
})
{
    var output = Path.Combine(root, label);
    Run(["dotnet", ExtractorPath, "extract", image, "Arithmetic::Struct(ulong)", output]);
    var path = Path.Combine(output, "Extracted.lean");
    File.AppendAllText(path, $$"""

        namespace Extracted
        open CIL CIL.Extraction
        /-- The token carried by the first initobj instruction in this method. -/
        private def initobjToken : Option Nat := do
          let instruction := method0Body.bytes.drop 14
          guard (instruction.take 2 == [0xfe, 0x15])
          return (← readLittle 4 (instruction.drop 2)).1
        /-- A layout with identical display spelling and different namespace and simple name columns. -/
        private def swappedLayouts := rawLayouts.map fun row =>
          { row with declaration := [⟨name!"{{otherSpace}}", name!"{{otherName}}"⟩] }
        /-- The verifier rejects the swapped columns at the physical initobj operand. -/
        theorem swapped_declaration_rejected :
            (match checkBody { method0Body with layoutDeclarations := layoutDeclarations swappedLayouts }
                method0Original method0TypeArgumentsRaw with
             | .error (.metadata (.operandMismatch token)) => some token
             | _ => none) = initobjToken ∧ initobjToken.isSome = true := by
          constructor <;> cil_kernel_rfl
        #print axioms swapped_declaration_rejected
        end Extracted
        """);
    evidence.Add(path, "PASS initobj binds the namespace and simple name in " + label, "swapped_declaration_rejected");

    var nested = Path.Combine(root, label + "Nested");
    Run(["dotnet", ExtractorPath, "extract", image, "GenericLayouts::Nested(uint,uint)", nested]);
    var nestedProof = Path.Combine(nested, "Extracted.lean");
    var otherGenericName = otherSpace.Length == 0 ? "Examples.GenericPair`1" : "GenericPair`1";
    File.AppendAllText(nestedProof, $$"""

        namespace Extracted
        open CIL CIL.Extraction

        /-- The alternative metadata declaration has the same scoped display spelling. -/
        private def otherPair : List TypeLevel := [⟨name!"{{otherSpace}}", name!"{{otherGenericName}}"⟩]

        /-- Checking the nested return signature fails at this physical MethodDef. -/
        private def rejectsReturn (change : RawLayout → RawLayout) : Bool :=
          let rows := rawLayouts.modify 1 change
          match checkBody { method0Body with layoutDeclarations := layoutDeclarations rows }
              method0Original method0TypeArgumentsRaw with
          | .error (.metadata (.methodMismatch token)) => token == method0Original.token
          | _ => false

        /-- Change just the argument list of the outer generic application. -/
        private def changeInner (change : String → List TypeLevel → LayoutArguments → LayoutArgument)
            (row : RawLayout) : RawLayout :=
          match row.genericArguments with
          | some (.cons (.instanceType scope levels args) .nil) =>
            { row with genericArguments := some (.cons (change scope levels args) .nil) }
          | _ => row

        /-- Equal display names cannot replace the outer constructor, inner constructor or UInt32 code. -/
        theorem nested_identity_checked :
            rejectsReturn (fun row => { row with declaration := otherPair }) = true ∧
            rejectsReturn (changeInner fun scope _ args => .instanceType scope otherPair args) = true ∧
            rejectsReturn (changeInner fun scope levels _ => .instanceType scope levels
              (.cons (.named runtimeScope [⟨name!"System", name!"UInt32"⟩]) .nil)) = true := by
          exact ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩
        #print axioms nested_identity_checked
        end Extracted
        """);
    evidence.Add(nestedProof, "PASS nested generic identity in " + label, "nested_identity_checked");
}
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.GenericLayouts")!;
foreach (var (name, signature) in new[]
{
    ("Roundtrip", "ulong,ulong"), ("Composed", "ulong,ulong"), ("Nested", "uint,uint"),
    ("Field", "Examples.GenericPair`1<ulong>&"), ("VectorSize", ""), ("TupleSize", "")
})
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"GenericLayouts::{name}({signature})", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = source;
    if (name is "VectorSize" or "TupleSize")
    {
        if (!Equals(runtime.GetMethod(name)!.Invoke(null, []), 32))
            throw new InvalidOperationException("Unexpected CLR nested generic layout");
        proof += $$"""

            /-- Nested generic storage has the same size as the CLR value type. -/
            theorem generic_size_{{name}} :
                (CIL.Safety.invoke Extracted.program 8 0 []
                  { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩,
                    views := [], nextIdentity := 0 }).map Prod.snd = .ok [.scalar (.i32 32)] := by rfl
            #print axioms generic_size_{{name}}
            """;
    }
    if (name is "Roundtrip" or "Composed")
    {
        var expected = name == "Roundtrip" ? 11UL : 22UL;
        if (!Equals(runtime.GetMethod(name)!.Invoke(null, [11UL, 22UL]), expected))
            throw new InvalidOperationException("Unexpected CLR generic-layout result: " + name);
        proof += $$"""

            /-- Closed instance calls and nested fields agree with compiled CLR execution. -/
            theorem generic_layout_{{name}} :
                (CIL.Safety.invoke Extracted.program 128 0 [.scalar (.i64 11), .scalar (.i64 22)]
                  { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩,
                    views := [], nextIdentity := 0 }).map Prod.snd =
                      .ok [.scalar (.i64 {{expected}})] := rfl
            #print axioms generic_layout_{{name}}
            """;
    }
    if (name == "Composed")
    {
        var narrow = NarrowEvidence(source, "layouts_validated");
        proof += "\n" + CheckedEvidenceControl(source, narrow, ["layouts_validated"], 0);
        foreach (var (label, before, after) in new[]
        {
            ("owner-arity", "arity := 1", "arity := 2"),
            ("argument-scope", "arguments := [.atom Extraction.runtimeScope", "arguments := [.atom \"Forged\""),
            ("original-field", "fields := [.parameter 0, .parameter 0]",
                "fields := [.atom Extraction.runtimeScope \"System.UInt32\", .parameter 0]"),
            ("reference-constraint", "constraints := [(24,", "constraints := [(28,"),
            ("unbound-field", "fields := [.parameter 0, .parameter 0]", "fields := [.parameter 1, .parameter 0]"),
            ("explicit-layout", "explicit := false", "explicit := true")
        })
        {
            var changed = narrow.Replace(before, after, StringComparison.Ordinal);
            if (changed == narrow) throw new InvalidOperationException("Ineffective generic layout mutation: " + label);
            var path = Path.Combine(root, label + ".lean");
            File.WriteAllText(path, changed);
            rejected.Add(path, "PASS independently rejected generic layout: " + label, "LayoutsValid");
        }
    }
    var proofPath = Path.Combine(root, name + ".lean");
    File.WriteAllText(proofPath, proof);
    evidence.Add(proofPath, "PASS closed generic layout: " + name);
}
foreach (var closedInterface in new[] { false, true })
{
    var name = closedInterface ? "ClosedInterfaceOwner" : "InterfaceOwner";
    var dll = Path.Combine(root, name + ".dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        TypeReference constraint = module.GetType("Examples.ICounterValue");
        TypeReference argument = module.GetType("Examples.CounterValue");
        if (closedInterface)
        {
            var genericConstraint = new GenericInstanceType(module.GetType("Examples.IClosedCounter`1"));
            genericConstraint.GenericArguments.Add(module.TypeSystem.Int32);
            constraint = genericConstraint;
            var genericArgument = new GenericInstanceType(module.GetType("Examples.GenericInterfaceCounter`1"));
            genericArgument.GenericArguments.Add(module.TypeSystem.Int32);
            argument = genericArgument;
        }
        var template = module.GetType("Examples.GenericPair`1");
        var owner = new TypeDefinition("Examples", "InterfacePair`1", template.Attributes, template.BaseType);
        var parameter = new GenericParameter("T", owner) { Attributes = template.GenericParameters[0].Attributes };
        foreach (var inherited in template.GenericParameters[0].Constraints)
            parameter.Constraints.Add(new GenericParameterConstraint(inherited.ConstraintType));
        parameter.Constraints.Add(new GenericParameterConstraint(constraint));
        owner.GenericParameters.Add(parameter);
        owner.Fields.Add(new FieldDefinition("First", Mono.Cecil.FieldAttributes.Public, parameter));
        owner.Fields.Add(new FieldDefinition("Second", Mono.Cecil.FieldAttributes.Public, parameter));
        module.Types.Add(owner);
        var method = module.GetType("Examples.GenericLayouts").Methods.Single(method => method.Name == "VectorSize");
        var call = (GenericInstanceMethod)method.Body.Instructions.Single(instruction =>
            instruction.OpCode.Code == Code.Call).Operand;
        var closedOwner = new GenericInstanceType(owner);
        closedOwner.GenericArguments.Add(argument);
        call.GenericArguments[0] = closedOwner;
        module.Write(dll);
        argument.Resolve().Interfaces.Clear();
        module.Write(Path.Combine(root, name + "-invalid.dll"));
    }
    var failure = Execute(["dotnet", ExtractorPath, "extract", Path.Combine(root, name + "-invalid.dll"),
        "GenericLayouts::VectorSize()", Path.Combine(root, name + "-invalid")]);
    if (failure.Code == 0 || !failure.Output.Contains("Unsupported generic struct constraint type"))
        throw new InvalidOperationException("Unsatisfied generic struct constraint accepted: " + failure.Output);
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", dll, "GenericLayouts::VectorSize()", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var narrow = NarrowEvidence(source, "layouts_validated");
    var expected = closedInterface ? 16 : 8;
    if (!Equals(Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.GenericLayouts")!
        .GetMethod("VectorSize")!.Invoke(null, []), expected))
        throw new InvalidOperationException("Interface-constrained layout differs from the CLR");
    var path = Path.Combine(root, name + ".lean");
    File.WriteAllText(path, narrow + $$"""

        /-- A closed interface constraint retains the concrete argument's checked storage size. -/
        theorem interface_owner_size :
            (CIL.Safety.invoke Extracted.program 8 0 []
              { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩,
                views := [], nextIdentity := 0 }).map Prod.snd = .ok [.scalar (.i32 {{expected}})] := by rfl
        #print axioms interface_owner_size
        """);
    evidence.Add(path, "PASS generic owner with direct interface constraint: " + name, "layouts_validated");
    var invalid = Path.Combine(root, name + "-missing-interface.lean");
    // Same-assembly generic interface identities spell each argument with its assembly scope.
    const string runtimeScope = "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a";
    var marker = closedInterface ? $"::Examples.IClosedCounter`1<{runtimeScope}::System.Int32>"
        : "::Examples.ICounterValue";
    marker = System.Text.Json.JsonSerializer.Serialize(marker)[1..^1];
    var start = narrow.IndexOf("interfaces := [", StringComparison.Ordinal);
    var interfaces = narrow.IndexOf(marker, start, StringComparison.Ordinal);
    var end = narrow.IndexOf(']', start);
    if (start < 0 || interfaces < 0 || interfaces > end)
        throw new InvalidOperationException("Missing interface evidence");
    // Change only the argument's interface list, retaining the constraint's original identity.
    var changed = narrow[..start] + "interfaces := []" + narrow[(end + 1)..];
    File.WriteAllText(invalid, changed);
    rejected.Add(invalid, "PASS rejected unsatisfied generic owner constraint: " + name, "LayoutsValid");
    var constraintStart = narrow.LastIndexOf("constraints := [", StringComparison.Ordinal);
    var constraintIdentity = narrow.IndexOf(marker, constraintStart, StringComparison.Ordinal);
    if (constraintIdentity < 0) throw new InvalidOperationException("Missing owner constraint identity");
    var forgedIdentity = closedInterface ? marker.Replace("System.Int32", "System.Int64", StringComparison.Ordinal)
        : "ForgedScope" + marker;
    var wrongIdentity = narrow[..constraintIdentity] + forgedIdentity +
        narrow[(constraintIdentity + marker.Length)..];
    var wrongPath = Path.Combine(root, name + "-wrong-identity.lean");
    File.WriteAllText(wrongPath, wrongIdentity);
    rejected.Add(wrongPath, "PASS rejected wrong owner constraint identity: " + name, "LayoutsValid");
}
evidence.Check();
rejected.Check();
