#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include PinnedMetadata.cs

using System.Reflection;
using System.Diagnostics;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using Mono.Cecil;
using Mono.Cecil.Cil;

var root = Path.GetFullPath("artifacts/StructuralSignatures");
Directory.CreateDirectory(root);
var extractor = Assembly.LoadFrom(Path.GetFullPath("Extractor/bin/Nethermind.LeanCIL.dll"));
const BindingFlags Instance = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;
const BindingFlags Static = BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic;
void Require(bool condition, string message)
{
    if (!condition) throw new Exception(message);
}

string path = Path.Combine(root, "Collision.dll");
object? escapedSignature = null;
using (var assembly = AssemblyDefinition.CreateAssembly(new("Collision", new(1, 0)), "Collision", ModuleKind.Dll))
{
    var module = assembly.MainModule;
    var runtime = new AssemblyNameReference("System.Runtime", new(11, 0, 0, 0))
    {
        PublicKeyToken = Convert.FromHexString("b03f5f7f11d50a3a")
    };
    module.AssemblyReferences.Add(runtime);
    string argument = module.TypeSystem.Int32.Scope is AssemblyNameReference primitiveScope
        ? primitiveScope.FullName + "::System.Int32" : throw new Exception("Primitive scope must be an assembly");
    foreach (string name in new[] { "G`1", "G`1<" + argument + ">" })
    {
        var type = new TypeDefinition("Fixture", name,
            Mono.Cecil.TypeAttributes.Public | Mono.Cecil.TypeAttributes.Sealed |
            Mono.Cecil.TypeAttributes.SequentialLayout,
            new TypeReference("System", "ValueType", module, runtime));
        if (name == "G`1")
        {
            type.GenericParameters.Add(new GenericParameter("T", type));
            var member = new MethodDefinition("ConstantOwner", Mono.Cecil.MethodAttributes.Public |
                Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Int32);
            type.Methods.Add(member);
            member.GenericParameters.Add(new GenericParameter("U", member));
            member.Body.Instructions.Add(Instruction.Create(OpCodes.Ldc_I4_1));
            member.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
        }
        module.Types.Add(type);
    }
    var owner = new TypeDefinition("Fixture", "Methods", Mono.Cecil.TypeAttributes.Public);
    module.Types.Add(owner);
    foreach (var (space, name) in new[] { ("A.B", "C"), ("A", "B.C"), ("Raw", "BadAX"), ("Raw", "BadBX") })
        module.Types.Add(new TypeDefinition(space, name, Mono.Cecil.TypeAttributes.Public));
    owner.Fields.Add(new FieldDefinition("Value", Mono.Cecil.FieldAttributes.Public, module.Types[^4]));
    var outer = new TypeDefinition("Fixture", "Outer", Mono.Cecil.TypeAttributes.Public);
    outer.NestedTypes.Add(new TypeDefinition("", "Inner", Mono.Cecil.TypeAttributes.NestedPublic));
    outer.NestedTypes.Add(new TypeDefinition("", "Sibling", Mono.Cecil.TypeAttributes.NestedPublic));
    module.Types.Add(outer);
    module.Types.Add(new TypeDefinition("Fixture", "Outer/Inner", Mono.Cecil.TypeAttributes.Public));
    var genuine = new TypeReference("System", "Int32", module, module.TypeSystem.Int32.Scope);
    owner.Fields.Add(new FieldDefinition("NamedPrimitive", Mono.Cecil.FieldAttributes.Public, genuine));
    var foreign = new AssemblyNameReference("Foreign", new(11, 0, 0, 0));
    module.AssemblyReferences.Add(foreign);
    owner.Fields.Add(new FieldDefinition("ForeignPrimitive", Mono.Cecil.FieldAttributes.Public,
        new TypeReference("System", "Int32", module, foreign)));
    foreach (var (label, scope) in new[]
    {
        ("RuntimeVersion", new AssemblyNameReference("System.Runtime", new(9, 0, 0, 0))
            { PublicKeyToken = runtime.PublicKeyToken }),
        ("CoreLibrary", new AssemblyNameReference("System.Private.CoreLib", new(11, 0, 0, 0))
            { PublicKeyToken = runtime.PublicKeyToken }),
        ("AbsentKey", new AssemblyNameReference("Signing", new(1, 0, 0, 0))),
        ("ZeroKey", new AssemblyNameReference("Signing", new(1, 0, 0, 0)) { PublicKeyToken = new byte[8] }),
        ("CultureA", new AssemblyNameReference("Culture", new(1, 0, 0, 0)) { Culture = "CultAX" }),
        ("CultureB", new AssemblyNameReference("Culture", new(1, 0, 0, 0)) { Culture = "CultBX" })
    })
    {
        module.AssemblyReferences.Add(scope);
        owner.Fields.Add(new FieldDefinition(label, Mono.Cecil.FieldAttributes.Public,
            new TypeReference("System", "Int32", module, scope)));
    }
    var method = new MethodDefinition("Constant", Mono.Cecil.MethodAttributes.Public |
        Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Int32);
    owner.Methods.Add(method);
    method.GenericParameters.Add(new GenericParameter("T", method));
    method.Body.Instructions.Add(Instruction.Create(OpCodes.Ldc_I4_1));
    method.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
    assembly.Write(path);
}
using (var pinned = new PinnedMetadata(extractor, path))
{
    var generic = new GenericInstanceType(pinned.Module.GetType("Fixture.G`1"));
    generic.GenericArguments.Add(pinned.Module.TypeSystem.Int32);
    TypeReference[] types = [generic, pinned.Module.Types.Single(type => type.Name.StartsWith("G`1<"))];
    var method = pinned.Module.GetType("Fixture.Methods").Methods.Single();
    var specialization = extractor.GetType("Nethermind.LeanCIL.MethodSpecialization", true)!;
    var session = Activator.CreateInstance(specialization, Instance, null, [pinned.Module, "scalar"], null)!;
    var instantiate = specialization.GetMethod("Instantiate", Instance)!;
    MethodDefinition Close(TypeReference argument)
    {
        var reference = new GenericInstanceMethod(method);
        reference.GenericArguments.Add(argument);
        try { return (MethodDefinition)instantiate.Invoke(session, [reference])!; }
        catch (TargetInvocationException error) { throw error.InnerException!; }
    }
    var first = Close(types[0]);
    var second = Close(types[1]);
    Require(!ReferenceEquals(first, second), "Distinct raw columns reused one specialization clone");
    Require(ReferenceEquals(first, Close(types[0])) && ReferenceEquals(second, Close(types[1])),
        "Each exact specialization must reuse its own clone");
    var arguments = specialization.GetMethod("Arguments", Static)!;
    Require(ReferenceEquals(((IReadOnlyList<TypeReference>)arguments.Invoke(null, [first])!)[0], types[0]) &&
        ReferenceEquals(((IReadOnlyList<TypeReference>)arguments.Invoke(null, [second])!)[0], types[1]),
        "Specializations must retain their respective arguments");

    var signatures = pinned.Context.GetType().GetProperty("Signatures", Instance)!.GetValue(pinned.Context)!;
    var signatureType = signatures.GetType();
    var snapshot = signatureType.GetMethod("Type", Instance)!;
    object Signature(TypeReference type)
    {
        try { return snapshot.Invoke(signatures, [type])!; }
        catch (TargetInvocationException error) { throw error.InnerException!; }
    }
    void Equal(TypeReference left, TypeReference right, bool expected, string label) =>
        Require(Signature(left).Equals(Signature(right)) == expected, label);
    void Reject(Action action, string label)
    {
        try { action(); }
        catch (InvalidDataException) { return; }
        catch (BadImageFormatException) { return; }
        throw new Exception(label);
    }
    var module = pinned.Module;
    var split = module.Types.Where(type => type.Namespace is "A.B" or "A").ToArray();
    Equal(split[0], split[1], false, "Namespace/name columns were flattened");
    Equal(module.GetType("Fixture.Outer").NestedTypes[0],
        module.Types.Single(type => type.Name == "Outer/Inner"), false, "Nesting was flattened");
    var owner = module.GetType("Fixture.Methods");
    var fieldCheck = extractor.GetType("Nethermind.LeanCIL.MetadataValidation", true)!
        .GetMethod("InstanceFieldOf", Static)!;
    void Field(TypeReference type)
    {
        try { fieldCheck.Invoke(null, [new FieldReference("Value", type, owner)]); }
        catch (TargetInvocationException error) { throw error.InnerException!; }
    }
    Field(split[0]);
    Reject(() => Field(split[1]), "Colliding field types passed member/definition validation");
    var constrained = extractor.GetType("Nethermind.LeanCIL.ConstrainedCalls", true)!;
    var indexType = constrained.GetNestedType("TargetIndex", Static)!;
    var genericOwnerMethod = generic.ElementType.Resolve().Methods.Single();
    var otherOwner = new GenericInstanceType(generic.ElementType);
    otherOwner.GenericArguments.Add(module.TypeSystem.UInt32);
    MethodDefinition CloseOwner(GenericInstanceType declaring)
    {
        var member = new MethodReference(genericOwnerMethod.Name, genericOwnerMethod.ReturnType, declaring)
        {
            CallingConvention = genericOwnerMethod.CallingConvention
        };
        member.GenericParameters.Add(new GenericParameter("U", member));
        var reference = new GenericInstanceMethod(member);
        reference.GenericArguments.Add(module.TypeSystem.Int64);
        try { return (MethodDefinition)instantiate.Invoke(session, [reference])!; }
        catch (TargetInvocationException error) { throw error.InnerException!; }
    }
    var firstOwner = CloseOwner(generic);
    var secondOwner = CloseOwner(otherOwner);
    Require(!ReferenceEquals(firstOwner, secondOwner), "Distinct owner arguments reused one specialization clone");
    Require(ReferenceEquals(firstOwner, CloseOwner(generic)) && ReferenceEquals(secondOwner, CloseOwner(otherOwner)),
        "Closed owners did not retain their respective specialization clones");
    var targetIndex = Activator.CreateInstance(indexType, Instance, null,
        [new[] { first, second, firstOwner, secondOwner }], null)!;
    var resolutionType = constrained.GetNestedType("Resolution", Static)!;
    foreach (var (argument, expected) in new[] { (types[0], first), (types[1], second) })
    {
        var resolution = Activator.CreateInstance(resolutionType, Instance, null,
            [owner, method, method, owner, new[] { argument }], null)!;
        Require(ReferenceEquals(indexType.GetMethod("Find", Instance)!.Invoke(targetIndex, [resolution]), expected),
            "Constrained lookup disagrees with specialization identity");
    }
    foreach (var (declaring, expected) in new[] { (generic, firstOwner), (otherOwner, secondOwner) })
    {
        var resolution = Activator.CreateInstance(resolutionType, Instance, null,
            [generic.ElementType.Resolve(), genericOwnerMethod, genericOwnerMethod, declaring,
                new[] { module.TypeSystem.Int64 }], null)!;
        Require(ReferenceEquals(indexType.GetMethod("Find", Instance)!.Invoke(targetIndex, [resolution]), expected),
            "Constrained lookup merged different closed generic owners");
        var retained = (IReadOnlyList<TypeReference>)specialization.GetMethod("OwnerArguments", Static)!
            .Invoke(null, [expected])!;
        Require(retained.Count == 1 && ReferenceEquals(retained[0], declaring.GenericArguments[0]),
            "Specialized owner arguments were not retained");
    }
    var namedPrimitive = owner.Fields.Single(field => field.Name == "NamedPrimitive").FieldType;
    Equal(module.TypeSystem.Int32, namedPrimitive, true, "Equal scoped primitive rows differ");
    Equal(module.TypeSystem.Int32, owner.Fields.Single(field => field.Name == "ForeignPrimitive").FieldType,
        false, "Primitive scope was erased");
    foreach (string label in new[] { "RuntimeVersion", "CoreLibrary" })
        Equal(namedPrimitive, owner.Fields.Single(field => field.Name == label).FieldType, false,
            "Runtime scopes were unified");
    Equal(owner.Fields.Single(field => field.Name == "AbsentKey").FieldType,
        owner.Fields.Single(field => field.Name == "ZeroKey").FieldType, false, "Absent and zero signing keys agree");
    Reject(() => Signature(new TypeReference("System", "Int32", module, module.TypeSystem.Int32.Scope)),
        "Unregistered RID-zero primitive was accepted");
    object immutable = Signature(split[0]);
    split[0].Namespace = "Mutated";
    split[0].Name = "Name";
    Require(immutable.Equals(Signature(split[0])), "Raw row identity followed mutable names");
    object primitiveIdentity = Signature(module.TypeSystem.Int32);
    var primitiveScope = module.TypeSystem.Int32.Scope;
    var primitiveToken = module.TypeSystem.Int32.MetadataToken;
    module.TypeSystem.Int32.Name = "Edited";
    module.TypeSystem.Int32.Namespace = "Edited";
    module.TypeSystem.Int32.Scope = foreignScope();
    module.TypeSystem.Int32.MetadataToken = new MetadataToken(TokenType.TypeRef, 12345);
    Require(primitiveIdentity.Equals(Signature(module.TypeSystem.Int32)), "Registered primitive identity changed");
    module.TypeSystem.Int32.Name = "Int32";
    module.TypeSystem.Int32.Namespace = "System";
    module.TypeSystem.Int32.Scope = primitiveScope;
    module.TypeSystem.Int32.MetadataToken = primitiveToken;
    IMetadataScope foreignScope() => owner.Fields.Single(field => field.Name == "ForeignPrimitive").FieldType.Scope;
    var vector = new ArrayType(split[0]);
    var bounded = new ArrayType(split[0], 1);
    bounded.Dimensions[0] = new ArrayDimension(0, 9);
    Equal(vector, bounded, false, "Vector and bounded array agree");
    var otherBounds = new ArrayType(split[0], 1);
    otherBounds.Dimensions[0] = new ArrayDimension(0, 10);
    Equal(bounded, otherBounds, false, "Array bounds were erased");
    Equal(new RequiredModifierType(split[0], split[1]), new OptionalModifierType(split[0], split[1]),
        false, "Modifier kind was erased");
    Equal(new RequiredModifierType(split[0], split[1]), new RequiredModifierType(split[1], split[0]),
        false, "Modifier columns were reordered");
    var pointer = new FunctionPointerType { ReturnType = split[0] };
    var otherPointer = new FunctionPointerType { ReturnType = split[0] };
    Equal(pointer, otherPointer, true, "Equal function pointers differ");
    var standalone = new CallSite(split[0]);
    var callable = signatureType.GetMethod("Callable", Instance)!;
    object Callable(IMethodSignature signature) => callable.Invoke(signatures, [signature])!;
    Require(Callable(standalone).Equals(Signature(pointer)), "Call site and pointer type have different keys");
    var pointers = extractor.GetType("Nethermind.LeanCIL.ManagedPointers", true)!;
    var same = pointers.GetMethod("SameSignature", Static)!;
    bool Matches(IMethodSignature right) => (bool)same.Invoke(null, [standalone, right])!;
    Require(Matches(pointer), "Equivalent managed signatures failed to match");
    standalone.Parameters.Add(new ParameterDefinition(new ByReferenceType(module.TypeSystem.UInt32)));
    Require(!Matches(pointer), "A missing managed reference parameter matched");
    pointer.Parameters.Add(new ParameterDefinition(new ByReferenceType(module.TypeSystem.UInt32)));
    Require(Matches(pointer) && Callable(standalone).Equals(Signature(pointer)),
        "Equivalent managed reference parameters failed to match");
    pointer.Parameters.Clear();
    otherPointer.HasThis = true;
    Equal(pointer, otherPointer, false, "Function pointer flags were erased");
    otherPointer.HasThis = false;
    otherPointer.CallingConvention = MethodCallingConvention.C;
    Equal(pointer, otherPointer, false, "Function pointer convention was erased");
    var wrapper = new GenericInstanceType(generic.ElementType);
    wrapper.GenericArguments.Add(split[0]);
    object before = Signature(wrapper);
    wrapper.GenericArguments[0] = split[1];
    Require(!before.Equals(Signature(wrapper)), "Wrapper mutation was hidden by a cache");
    Equal(method.GenericParameters[0], generic.ElementType.GenericParameters[0], false,
        "Method and type parameter positions were merged");
    var otherParameterOwner = new MethodReference("Other", module.TypeSystem.Void, owner);
    otherParameterOwner.GenericParameters.Add(new GenericParameter("DifferentName", otherParameterOwner));
    Equal(method.GenericParameters[0], otherParameterOwner.GenericParameters[0], true,
        "Positional parameters depend on their owner objects or names");
    var cycle = new GenericInstanceType(generic.ElementType);
    cycle.GenericArguments.Add(cycle);
    Reject(() => Signature(cycle), "Cyclic signature was accepted");
    var invalid = new TypeReference("Any", "Name", module, module) { MetadataToken = new(TokenType.TypeRef, 999999) };
    Reject(() => Signature(invalid), "Out-of-range type row was accepted");
    invalid.MetadataToken = new MetadataToken(TokenType.Method, 1);
    Reject(() => Signature(invalid), "Wrong token kind was accepted");
    var copy = new TypeReference("Ignored", "Ignored", module, module)
    {
        MetadataToken = split[0].MetadataToken
    };
    Equal(copy, split[0], true, "Distinct wrappers of the same raw row differ");
    using (var nested = new PinnedMetadata(extractor, path))
    {
        Reject(() => Signature(copy), "Inactive session accepted a signature query");
        var nestedSignatures = nested.Context.GetType().GetProperty("Signatures", Instance)!.GetValue(nested.Context)!;
        object nestedValue = snapshot.Invoke(nestedSignatures, [nested.Module.GetType("A.B.C")])!;
        Reject(() => nestedValue.Equals(immutable), "Cross-session handles compared successfully");
    }
    Require(immutable.Equals(Signature(copy)), "Restoring a nested session lost existing identities");
    var register = pinned.Context.GetType().GetMethod("RegisterIdentityImage", Instance)!;
    var unregister = pinned.Context.GetType().GetMethod("UnregisterIdentityImage", Instance)!;
    var keyQuery = signatureType.GetMethod("Specialization", Instance)!;
    TypeReference removedType;
    GenericParameter removedParameter;
    using (var imported = ModuleDefinition.ReadModule(path))
    {
        register.Invoke(pinned.Context, [imported, File.ReadAllBytes(path)]);
        var importedType = imported.Types.Single(type => type.Namespace == "A.B");
        removedType = importedType;
        var importedMethod = imported.GetType("Fixture.Methods").Methods.Single();
        removedParameter = importedMethod.GenericParameters[0];
        Equal(method.GenericParameters[0], removedParameter, true,
            "Live parameter modules changed positional identity");
        _ = keyQuery.Invoke(signatures, [importedMethod, importedMethod.DeclaringType, new[] { importedType }]);
        Equal(copy, importedType, true, "Equal rows in separate images differ");
        try { register.Invoke(pinned.Context, [imported, File.ReadAllBytes(path)]); }
        catch (TargetInvocationException error) when (error.InnerException is InvalidDataException) { }
        Equal(copy, importedType, true, "Duplicate registration corrupted a live module");
        unregister.Invoke(pinned.Context, [imported]);
        Reject(() => Signature(importedType), "Removed module retained a usable signature cache");
        Reject(() => Signature(removedParameter), "Generic-only query bypassed module unregistration");
        try
        {
            keyQuery.Invoke(signatures, [importedMethod, importedMethod.DeclaringType, new[] { importedType }]);
            throw new Exception("Removed module retained a usable specialization key");
        }
        catch (TargetInvocationException error) when (error.InnerException is InvalidDataException) { }
    }
    using (var reopened = ModuleDefinition.ReadModule(path))
    {
        register.Invoke(pinned.Context, [reopened, File.ReadAllBytes(path)]);
        Equal(copy, reopened.Types.Single(type => type.Namespace == "A.B"), true,
            "Reopened image has a different raw identity");
        Reject(() => Signature(removedType), "Reopening revived an earlier module object");
        Reject(() => Signature(removedParameter), "Reopening revived an earlier generic parameter owner");
        unregister.Invoke(pinned.Context, [reopened]);
    }
    using (var rejected = ModuleDefinition.ReadModule(path))
    {
        var originalScope = rejected.TypeSystem.Object.Scope;
        rejected.TypeSystem.Object.Scope = new AssemblyNameReference("Fabricated", new(1, 0));
        try
        {
            register.Invoke(pinned.Context, [rejected, File.ReadAllBytes(path)]);
            throw new Exception("Registration accepted an unproven primitive scope");
        }
        catch (TargetInvocationException error) when (error.InnerException is InvalidDataException) { }
        Reject(() => Signature(rejected.TypeSystem.Int32), "Failed preparation published primitive objects");
        Require(immutable.Equals(Signature(copy)), "Failed registration damaged an existing module");
        rejected.TypeSystem.Object.Scope = originalScope;
        register.Invoke(pinned.Context, [rejected, File.ReadAllBytes(path)]);
        unregister.Invoke(pinned.Context, [rejected]);
    }

    TypeReference Diamond(int depth, TypeReference leaf)
    {
        for (int index = 0; index < depth; index++)
        {
            var node = new GenericInstanceType(generic.ElementType);
            node.GenericArguments.Add(leaf);
            node.GenericArguments.Add(leaf);
            leaf = node;
        }
        return leaf;
    }
    long Counter(string name) => (long)signatureType.GetProperty(name, Instance)!.GetValue(signatures)!;
    var orderedQuery = signatureType.GetMethod("Ordered", Instance)!;
    var rootSets = new[] { 64, 256, 1024 }.Select(size => Enumerable.Range(0, size)
        .Select(_ => (TypeReference)new RequiredModifierType(split[0], new ArrayType(split[1]))).ToArray()).ToArray();
    foreach (var roots in rootSets) orderedQuery.Invoke(signatures, [roots]);
    long previousWork = 0;
    long previousAllocation = 0;
    for (int index = 0; index < rootSets.Length; index++)
    {
        long nodes = Counter("NodeVisits"), edges = Counter("EdgeVisits"), probes = Counter("TrieProbes");
        long start = GC.GetAllocatedBytesForCurrentThread();
        orderedQuery.Invoke(signatures, [rootSets[index]]);
        long allocated = GC.GetAllocatedBytesForCurrentThread() - start;
        long work = Counter("NodeVisits") - nodes + Counter("EdgeVisits") - edges + Counter("TrieProbes") - probes;
        Require(previousWork == 0 || work <= previousWork * 6,
            "Independent ordered signatures have superlinear traversal growth");
        Require(previousAllocation == 0 || allocated <= previousAllocation * 5 + 16384,
            "Independent ordered signatures have superlinear allocation growth");
        Console.WriteLine($"Ordered {rootSets[index].Length}: {work} visits and probes, {allocated} bytes/pass");
        previousWork = work;
        previousAllocation = allocated;
    }
    foreach (int size in new[] { 64, 256, 1024 })
    {
        var left = Diamond(size, split[0]);
        var right = Diamond(size, split[0]);
        long nodes = Counter("NodeVisits"), edges = Counter("EdgeVisits"), probes = Counter("TrieProbes");
        long allocated = GC.GetAllocatedBytesForCurrentThread();
        var timer = Stopwatch.StartNew();
        Equal(left, right, true, "Independently allocated equal DAGs differ");
        timer.Stop();
        Require(Counter("NodeVisits") - nodes == 2 * (size + 2), "DAG nodes were revisited");
        Require(Counter("EdgeVisits") - edges == 6 * size, "DAG edges were expanded");
        Require(Counter("TrieProbes") - probes <= 12 * size + 30, "Signature interning expanded a DAG");
        Equal(left, Diamond(size, split[1]), false, "Unequal DAG leaf was erased");
        var differentSharing = new GenericInstanceType(generic.ElementType);
        differentSharing.GenericArguments.Add(Diamond(size - 1, split[0]));
        differentSharing.GenericArguments.Add(Diamond(size - 1, split[0]));
        Require(!ReferenceEquals(differentSharing.GenericArguments[0], differentSharing.GenericArguments[1]),
            "Different-sharing fixture reused its child objects");
        Equal(left, differentSharing, true, "Canonical identity depends on DAG sharing");
        differentSharing.GenericArguments[1] = Diamond(size - 1, split[1]);
        Equal(left, differentSharing, false, "Different-sharing comparison erased an unequal leaf");
        var wide = new GenericInstanceType(generic.ElementType);
        for (int index = 0; index < size; index++) wide.GenericArguments.Add(left);
        long wideNodes = Counter("NodeVisits"), wideEdges = Counter("EdgeVisits");
        _ = Signature(wide);
        Require(Counter("NodeVisits") - wideNodes == size + 3 &&
            Counter("EdgeVisits") - wideEdges == 4 * size + 1, "Wide shared arguments were expanded");
        var ordered = signatureType.GetMethod("Ordered", Instance)!;
        long parameterNodes = Counter("NodeVisits"), parameterEdges = Counter("EdgeVisits");
        object orderedTypes = ordered.Invoke(signatures, [Enumerable.Repeat(left, size)])!;
        Require(Counter("NodeVisits") - parameterNodes == size + 2 &&
            Counter("EdgeVisits") - parameterEdges == 3 * size, "Shared parameter roots were traversed repeatedly");
        Require(orderedTypes.Equals(ordered.Invoke(signatures, [Enumerable.Repeat(right, size)])),
            "Equal ordered parameters differ");
        Console.WriteLine($"DAG {size}: {timer.Elapsed.TotalMilliseconds:F3} ms, " +
            $"{GC.GetAllocatedBytesForCurrentThread() - allocated} bytes");
    }
    var foreignOwner = new MethodDefinition("Foreign", Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
    foreignOwner.GenericParameters.Add(new GenericParameter("T", foreignOwner));
    method.Body.Variables.Add(new VariableDefinition(foreignOwner.GenericParameters[0]));
    var freshSpecializations = Activator.CreateInstance(specialization, Instance, null, [module, "scalar"], null)!;
    var foreignBody = new GenericInstanceMethod(method);
    foreignBody.GenericArguments.Add(types[0]);
    try
    {
        instantiate.Invoke(freshSpecializations, [foreignBody]);
        throw new Exception("Foreign generic parameter owner was substituted");
    }
    catch (TargetInvocationException error) when (error.InnerException is InvalidDataException failure &&
        failure.Message.Contains("Foreign generic parameter owner", StringComparison.Ordinal)) { }
    method.Body.Variables.Clear();
    escapedSignature = Signature(copy);
}
try
{
    escapedSignature!.Equals(escapedSignature);
    throw new Exception("Disposed signature session remained usable");
}
catch (InvalidDataException) { }

foreach (int size in new[] { 64, 256, 1024 })
{
    string nestingPath = Path.Combine(root, $"Nesting{size}.dll");
    using (var assembly = AssemblyDefinition.CreateAssembly(new("Nesting", new(1, 0)), "Nesting", ModuleKind.Dll))
    {
        var module = assembly.MainModule;
        var parent = new TypeDefinition("Fixture", "Root", Mono.Cecil.TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(parent);
        for (int index = 1; index < size; index++)
        {
            var child = new TypeDefinition("", "Child", Mono.Cecil.TypeAttributes.NestedPublic,
                module.TypeSystem.Object);
            parent.NestedTypes.Add(child);
            parent = child;
        }
        assembly.Write(nestingPath);
    }
    using var pinned = new PinnedMetadata(extractor, nestingPath);
    var signatures = pinned.Context.GetType().GetProperty("Signatures", Instance)!.GetValue(pinned.Context)!;
    var snapshot = signatures.GetType().GetMethod("Type", Instance)!;
    var pending = new Stack<TypeDefinition>(pinned.Module.Types.Skip(1));
    var levels = new List<TypeDefinition>();
    while (pending.TryPop(out var type))
    {
        levels.Add(type);
        foreach (var child in type.NestedTypes) pending.Push(child);
    }
    foreach (var type in levels.AsEnumerable().Reverse()) snapshot.Invoke(signatures, [type]);
    long rows = (long)signatures.GetType().GetProperty("RawRows", Instance)!.GetValue(signatures)!;
    Require(rows == size, "All nesting prefixes repeatedly decoded their ancestors");
    Console.WriteLine($"Nesting {size}: {rows} raw row visits");
}

byte[] invalidNames = File.ReadAllBytes(path);
foreach (var (name, replacement) in new[] { ("BadAX", (byte)0xc0), ("BadBX", (byte)0xc1),
    ("CultAX", (byte)0xc0), ("CultBX", (byte)0xc1) })
{
    int offset = invalidNames.AsSpan().IndexOf(System.Text.Encoding.UTF8.GetBytes(name));
    Require(offset >= 0, "Raw name fixture entry is absent");
    invalidNames[offset + name.Length - 2] = replacement;
}
string invalidPath = Path.Combine(root, "InvalidNames.dll");
File.WriteAllBytes(invalidPath, invalidNames);
using (var pinned = new PinnedMetadata(extractor, invalidPath))
{
    var types = pinned.Module.Types.Where(type => type.Namespace == "Raw").ToArray();
    Require(types[0].FullName == types[1].FullName, "Invalid UTF-8 displays must collide");
    var signatures = pinned.Context.GetType().GetProperty("Signatures", Instance)!.GetValue(pinned.Context)!;
    var snapshot = signatures.GetType().GetMethod("Type", Instance)!;
    Require(!snapshot.Invoke(signatures, [types[0]])!.Equals(snapshot.Invoke(signatures, [types[1]])),
        "Distinct raw UTF-8 names were merged");
    var fields = pinned.Module.GetType("Fixture.Methods").Fields;
    var cultureA = fields.Single(field => field.Name == "CultureA").FieldType;
    var cultureB = fields.Single(field => field.Name == "CultureB").FieldType;
    Require(cultureA.Scope.ToString() == cultureB.Scope.ToString(), "Invalid culture displays must collide");
    Require(!snapshot.Invoke(signatures, [cultureA])!.Equals(snapshot.Invoke(signatures, [cultureB])),
        "Distinct raw culture bytes were merged");
}

foreach (bool duplicate in new[] { true, false })
{
    byte[] malformed = File.ReadAllBytes(path);
    using (var pe = new PEReader(new MemoryStream(malformed)))
    {
        var reader = System.Reflection.Metadata.PEReaderExtensions.GetMetadataReader(pe);
        int start = pe.PEHeaders.MetadataStartOffset + reader.GetTableMetadataOffset(TableIndex.NestedClass);
        int width = reader.GetTableRowSize(TableIndex.NestedClass) / 2;
        malformed.AsSpan(start, width).CopyTo(malformed.AsSpan(start + (duplicate ? width * 2 : width), width));
    }
    string malformedPath = Path.Combine(root, duplicate ? "DuplicateNesting.dll" : "CyclicNesting.dll");
    File.WriteAllBytes(malformedPath, malformed);
    using var pinned = new PinnedMetadata(extractor, malformedPath);
    var signatures = pinned.Context.GetType().GetProperty("Signatures", Instance)!.GetValue(pinned.Context)!;
    var snapshot = signatures.GetType().GetMethod("Type", Instance)!;
    var nested = new TypeReference("Ignored", "Ignored", pinned.Module, pinned.Module)
    {
        MetadataToken = new MetadataToken(TokenType.TypeDef, 8)
    };
    using (var pe = new PEReader(new MemoryStream(malformed)))
    {
        var reader = System.Reflection.Metadata.PEReaderExtensions.GetMetadataReader(pe);
        int start = pe.PEHeaders.MetadataStartOffset + reader.GetTableMetadataOffset(TableIndex.NestedClass);
        int width = reader.GetTableRowSize(TableIndex.NestedClass) / 2;
        uint row = width == 2 ? BitConverter.ToUInt16(malformed, start) : BitConverter.ToUInt32(malformed, start);
        nested.MetadataToken = new MetadataToken(TokenType.TypeDef, row);
    }
    for (int attempt = 0; attempt < 2; attempt++)
    {
        try { snapshot.Invoke(signatures, [nested]); }
        catch (TargetInvocationException error) when (error.InnerException is InvalidDataException) { continue; }
        throw new Exception("Malformed nesting was accepted on a repeated query");
    }
}

foreach (int size in new[] { 64, 256, 1024 })
{
    string suffixPath = Path.Combine(root, $"Suffix{size}.dll");
    using (var assembly = AssemblyDefinition.CreateAssembly(new("Suffix", new(1, 0)), "Suffix", ModuleKind.Dll))
    {
        for (int index = 0; index < size; index++)
            assembly.MainModule.Types.Add(new TypeDefinition("Suffix", new string('x', size - index) + "z",
                Mono.Cecil.TypeAttributes.Public, assembly.MainModule.TypeSystem.Object));
        assembly.Write(suffixPath);
    }
    using var stream = File.OpenRead(suffixPath);
    using var pe = new PEReader(stream);
    var reader = System.Reflection.Metadata.PEReaderExtensions.GetMetadataReader(pe);
    int[] offsets = reader.TypeDefinitions.Select(handle =>
        MetadataTokens.GetHeapOffset(reader.GetTypeDefinition(handle).Name))
        .Skip(1).ToArray();
    Require(offsets.Max() - offsets.Min() == size - 1, "Fixture heap does not contain overlapping suffixes");
    using var pinned = new PinnedMetadata(extractor, suffixPath);
    var signatures = pinned.Context.GetType().GetProperty("Signatures", Instance)!.GetValue(pinned.Context)!;
    var snapshot = signatures.GetType().GetMethod("Type", Instance)!;
    foreach (var type in pinned.Module.Types.Skip(1)) snapshot.Invoke(signatures, [type]);
    long visits = (long)signatures.GetType().GetProperty("HeapBytes", Instance)!.GetValue(signatures)!;
    Require(visits <= size + 32, "Overlapping string suffixes were copied repeatedly");
    Console.WriteLine($"Suffix {size}: {visits} heap-byte visits");
}

foreach (int size in new[] { 64, 256, 1024 })
{
    string keyPath = Path.Combine(root, $"SharedKey{size}.dll");
    using (var assembly = AssemblyDefinition.CreateAssembly(new("SharedKey", new(1, 0)), "SharedKey", ModuleKind.Dll))
    {
        var module = assembly.MainModule;
        var owner = new TypeDefinition("Fixture", "Keys", Mono.Cecil.TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(owner);
        for (int index = 0; index < size; index++)
        {
            var scope = new AssemblyNameReference("Key" + index, new(1, 0, 0, 0)) { PublicKey = new byte[size] };
            module.AssemblyReferences.Add(scope);
            owner.Fields.Add(new FieldDefinition("F" + index, Mono.Cecil.FieldAttributes.Public,
                new TypeReference("Fixture", "Value", module, scope)));
        }
        assembly.Write(keyPath);
    }
    using var pinned = new PinnedMetadata(extractor, keyPath);
    object image = pinned.Context.GetType().GetMethod("IdentityMetadata", Instance)!.Invoke(pinned.Context,
        [pinned.Module])!;
    var reader = (System.Reflection.Metadata.MetadataReader)image.GetType().GetProperty("Reader", Instance)!
        .GetValue(image)!;
    var keyHandles = reader.AssemblyReferences.Select(reader.GetAssemblyReference)
        .Where(reference => reader.GetString(reference.Name).StartsWith("Key", StringComparison.Ordinal))
        .Select(reference => reference.PublicKeyOrToken).ToArray();
    Require(keyHandles.Length == size && keyHandles.Distinct().Count() == 1, "Signing blobs were not shared");
    long Count(string name) => (long)image.GetType().GetProperty(name, Instance)!.GetValue(image)!;
    long bytes = Count("SigningBytes"), reads = Count("SigningReads");
    var signatures = pinned.Context.GetType().GetProperty("Signatures", Instance)!.GetValue(pinned.Context)!;
    var snapshot = signatures.GetType().GetMethod("Type", Instance)!;
    foreach (var field in pinned.Module.GetType("Fixture.Keys").Fields) snapshot.Invoke(signatures, [field.FieldType]);
    Require(Count("SigningBytes") - bytes == size && Count("SigningReads") - reads == 1,
        "Shared signing blob was repeatedly decoded or hashed");
    var signingKey = image.GetType().GetMethod("SigningKey", Instance)!;
    object invalid = signingKey.Invoke(image, [keyHandles[0], false])!;
    Require(!(bool)invalid.GetType().GetProperty("Valid", Instance)!.GetValue(invalid)!,
        "Full public key was accepted as an eight-byte token");
    Require(ReferenceEquals(invalid, signingKey.Invoke(image, [keyHandles[0], false])),
        "Invalid key width was decoded again");
    Require(Count("SigningBytes") - bytes == 2 * size && Count("SigningReads") - reads == 2,
        "Signing interpretation modes shared an invalid normalization or repeated work");
    Console.WriteLine($"Shared key {size}: {size} bytes, one normalization");
}
Console.WriteLine("Structural signature checks passed");
