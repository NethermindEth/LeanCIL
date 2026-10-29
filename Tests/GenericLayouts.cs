#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Reflection;
using Mono.Cecil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/GenericLayouts");
Directory.CreateDirectory(root);
var extractor = Assembly.LoadFrom(ExtractorPath);
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var owner = module.GetType("Examples.GenericPair`1");
    var shadow = new TypeDefinition("System", "UInt64", Mono.Cecil.TypeAttributes.Public |
        Mono.Cecil.TypeAttributes.Sealed | Mono.Cecil.TypeAttributes.SequentialLayout, owner.BaseType);
    shadow.Fields.Add(new FieldDefinition("First", Mono.Cecil.FieldAttributes.Public, module.TypeSystem.UInt64));
    shadow.Fields.Add(new FieldDefinition("Second", Mono.Cecil.FieldAttributes.Public, module.TypeSystem.UInt64));
    module.Types.Add(shadow);
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
                    views := [], nextIdentity := 0 }).map Prod.snd = .ok [.scalar (.i32 32)] := rfl
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
evidence.Check();
rejected.Check();
