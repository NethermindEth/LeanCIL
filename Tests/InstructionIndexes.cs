#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

var extractor = Assembly.LoadFrom(ExtractorPath);
var indexType = extractor.GetType("Nethermind.LeanCIL.InstructionIndex", true)!;
var position = indexType.GetMethod("Position", BindingFlags.Instance | BindingFlags.NonPublic)!;
var isTarget = indexType.GetMethod("IsTarget", BindingFlags.Instance | BindingFlags.NonPublic)!;
var validate = extractor.GetType("Nethermind.LeanCIL.Arrays", true)!
    .GetMethod("ValidateReadOnly", BindingFlags.Static | BindingFlags.NonPublic)!;
object Index(MethodDefinition method) => Activator.CreateInstance(indexType,
    BindingFlags.Instance | BindingFlags.NonPublic, null, [method], null)!;
using var module = ModuleDefinition.CreateModule("Indexes", ModuleKind.Dll);
var method = new MethodDefinition("Body", Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
var first = Instruction.Create(OpCodes.Nop);
var prefix = Instruction.Create(OpCodes.Readonly);
var address = Instruction.Create(OpCodes.Ldelema, module.TypeSystem.Int32);
var branch = Instruction.Create(OpCodes.Br, prefix);
foreach (var instruction in new[] { first, branch, prefix, address, Instruction.Create(OpCodes.Ret) })
    method.Body.Instructions.Add(instruction);
var index = Index(method);
for (var offset = 0; offset < method.Body.Instructions.Count; offset++)
    if ((int)position.Invoke(index, [method.Body.Instructions[offset]])! != offset)
        throw new Exception("Instruction position used byte offsets instead of identity");
if ((int)position.Invoke(index, [Instruction.Create(OpCodes.Nop)])! != -1)
    throw new Exception("Foreign instruction was admitted");
validate.Invoke(null, [index, prefix]);
foreach (var switched in new[] { false, true })
{
    branch.OpCode = switched ? OpCodes.Switch : OpCodes.Br;
    branch.Operand = switched ? new[] { address, address } : address;
    index = Index(method);
    if (!(bool)isTarget.Invoke(index, [address])!) throw new Exception("Missing prefix-bypass target");
    try
    {
        validate.Invoke(null, [index, prefix]);
        throw new Exception("Accepted a branch bypassing readonly");
    }
    catch (TargetInvocationException error) when (error.InnerException is InvalidDataException rejected &&
        rejected.Message.Contains("Branch enters an array address", StringComparison.Ordinal)) { }
}
method.Body.Instructions.Insert(0, Instruction.Create(OpCodes.Nop));
if ((int)position.Invoke(Index(method), [first])! != 1)
    throw new Exception("Fresh traversal retained stale instruction positions");
Console.WriteLine("PASS instruction identity, missing targets, fresh indexes and readonly branch/switch rejection");

var owner = new TypeDefinition("", "Methods", Mono.Cecil.TypeAttributes.Public, module.TypeSystem.Object);
module.Types.Add(owner);
var caller = new MethodDefinition("Caller", Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
var callee = new MethodDefinition("Callee", Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
owner.Methods.Add(caller);
owner.Methods.Add(callee);
callee.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
var call = Instruction.Create(OpCodes.Call, callee);
caller.Body.Instructions.Add(call);
caller.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
var translate = extractor.GetType("Nethermind.LeanCIL.InstructionTranslation", true)!
    .GetMethod("Translate", BindingFlags.Static | BindingFlags.NonPublic)!;
var methods = new Dictionary<MethodDefinition, int> { [caller] = 0, [callee] = 1 };
string Translate(Instruction instruction) => (string)translate.Invoke(null,
    [instruction, caller, methods, 0, Index(caller), null, null, null, null, null])!;
if (Translate(call) != ".call 1 0") throw new Exception("Incorrect call index");
methods.Remove(callee);
try
{
    Translate(call);
    throw new Exception("Unresolved method was assigned a call index");
}
catch (TargetInvocationException error) when (error.InnerException is InvalidDataException rejected &&
    rejected.Message.Contains("Unsupported or unresolved call", StringComparison.Ordinal)) { }
methods.Add(callee, 1);
caller.Body.Instructions.Clear();
var destination = Instruction.Create(OpCodes.Ret);
var choose = Instruction.Create(OpCodes.Switch, [destination, destination]);
caller.Body.Instructions.Add(Instruction.Create(OpCodes.Ldc_I4_0));
caller.Body.Instructions.Add(choose);
caller.Body.Instructions.Add(destination);
if (Translate(choose) != ".switch [2, 2]") throw new Exception("Switch target order or duplicates changed");
Console.WriteLine("PASS translated method indexes reject missing callees and preserve switch target order");
var runtimeScope = AssemblyNameReference.Parse(
    "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a");
module.TypeSystem.UInt64.Scope = runtimeScope;
var valueType = new TypeReference("System", "ValueType", module, runtimeScope);
var inner = new TypeDefinition("Fixture", "ZInner", Mono.Cecil.TypeAttributes.Public |
    Mono.Cecil.TypeAttributes.Sealed | Mono.Cecil.TypeAttributes.SequentialLayout,
    valueType);
inner.Fields.Add(new FieldDefinition("Value", Mono.Cecil.FieldAttributes.Public, module.TypeSystem.UInt64));
module.Types.Add(inner);
var outer = new TypeDefinition("Fixture", "AOuter", Mono.Cecil.TypeAttributes.Public |
    Mono.Cecil.TypeAttributes.Sealed | Mono.Cecil.TypeAttributes.SequentialLayout,
    valueType);
outer.Fields.Add(new FieldDefinition("Inner", Mono.Cecil.FieldAttributes.Public, inner));
module.Types.Add(outer);
var contextType = extractor.GetType("Nethermind.LeanCIL.MetadataValidation+LayoutContext", true)!;
object Context(ModuleDefinition owner, string architecture) => Activator.CreateInstance(contextType,
    BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic, null, [owner, architecture], null)!;
var context = Context(module, "scalar");
var layoutType = extractor.GetType("Nethermind.LeanCIL.LayoutEvidence", true)!;
var layouts = Activator.CreateInstance(layoutType, BindingFlags.Instance | BindingFlags.NonPublic,
    null, [new TypeReference[] { outer, inner }, context], null)!;
var layoutIndex = layoutType.GetMethod("Index", BindingFlags.Instance | BindingFlags.NonPublic)!;
if ((int)layoutIndex.Invoke(layouts, [inner])! != 0 || (int)layoutIndex.Invoke(layouts, [outer])! != 1 ||
    (int)layoutIndex.Invoke(layouts, [module.TypeSystem.String])! != -1)
    throw new Exception("Layout index lost topological order or admitted an absent type");
var emitted = new System.Text.StringBuilder();
layoutType.GetMethod("EmitLayouts", BindingFlags.Instance | BindingFlags.NonPublic)!.Invoke(layouts, [emitted]);
if (!emitted.ToString().Contains("computedLayouts : Array Extraction.ComputedLayout := #[⟨layout1, 8⟩, ⟨layout0, 8⟩]",
    StringComparison.Ordinal))
    throw new Exception("Raw layout order was confused with emitted layout order");
Console.WriteLine("PASS layout indexes distinguish emitted and topological order and reject missing types");

var metadataType = extractor.GetType("Nethermind.LeanCIL.MetadataValidation", true)!;
var aggregateLayout = metadataType.GetMethod("AggregateLayout", BindingFlags.Static | BindingFlags.NonPublic,
    null, [typeof(TypeReference), typeof(ModuleDefinition), typeof(string)], null)!;
object Layout(TypeReference type) => aggregateLayout.Invoke(null, [type, module, "scalar"])!;
void RejectLayout(TypeReference type, string diagnostic)
{
    try { Layout(type); }
    catch (TargetInvocationException error) when (error.InnerException is InvalidDataException invalid &&
        invalid.Message.StartsWith(diagnostic, StringComparison.Ordinal)) { return; }
    throw new Exception("Invalid aggregate metadata was accepted: " + diagnostic);
}
var duplicateField = new FieldDefinition("Value", Mono.Cecil.FieldAttributes.Public |
    Mono.Cecil.FieldAttributes.Static, module.TypeSystem.UInt64);
inner.Fields.Add(duplicateField);
RejectLayout(outer, "Invalid field layout: ");
inner.Fields.Remove(duplicateField);
Layout(outer);
var duplicateType = new TypeDefinition(inner.Namespace, inner.Name, inner.Attributes, inner.BaseType);
module.Types.Add(duplicateType);
RejectLayout(outer, "Unsupported aggregate layout: ");
module.Types.Remove(duplicateType);
inner.Fields.Add(new FieldDefinition("Second", Mono.Cecil.FieldAttributes.Public, module.TypeSystem.UInt64));
var changedLayout = Layout(outer);
if ((int)changedLayout.GetType().GetProperty("Size")!.GetValue(changedLayout)! != 16)
    throw new Exception("Aggregate indexes were reused after metadata changed");
Console.WriteLine("PASS aggregate name indexes preserve duplicate rejection and fresh-call mutation visibility");

var contextLayout = contextType.GetMethod("AggregateLayout", BindingFlags.Instance | BindingFlags.NonPublic)!;
var contextFields = contextType.GetMethod("Fields", BindingFlags.Instance | BindingFlags.NonPublic)!;
var contextFieldIndex = contextType.GetMethod("FieldIndex", BindingFlags.Instance | BindingFlags.NonPublic)!;
var freshContext = Context(module, "scalar");
var firstLayout = contextLayout.Invoke(freshContext, [outer])!;
if (!ReferenceEquals(firstLayout, contextLayout.Invoke(freshContext, [outer])) ||
    (int)firstLayout.GetType().GetProperty("Size")!.GetValue(firstLayout)! != 16)
    throw new Exception("The fresh context did not reuse the current nested layout");
if (!ReferenceEquals(contextFields.Invoke(freshContext, [inner]), contextFields.Invoke(freshContext, [inner])) ||
    (int)contextFieldIndex.Invoke(freshContext, [inner, inner.Fields[1], false])! != 1 ||
    (int)contextFieldIndex.Invoke(freshContext, [inner, duplicateField, false])! != -1)
    throw new Exception("Field snapshots lost field identity or instance order");
var intrinsicsScope = AssemblyNameReference.Parse(
    "System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51");
var vector = new GenericInstanceType(new TypeReference("System.Runtime.Intrinsics", "Vector256`1",
    module, intrinsicsScope, true));
vector.GenericArguments.Add(module.TypeSystem.UInt64);
var vectorOwner = new TypeDefinition("Fixture", "VectorOwner", outer.Attributes, valueType);
module.Types.Add(vectorOwner);
module.TypeSystem.Byte.Scope = runtimeScope;
vectorOwner.Fields.Add(new FieldDefinition("Tag", Mono.Cecil.FieldAttributes.Public, module.TypeSystem.Byte));
vectorOwner.Fields.Add(new FieldDefinition("Vector", Mono.Cecil.FieldAttributes.Public, vector));
int ContextSize(object selected, TypeReference type)
{
    var result = contextLayout.Invoke(selected, [type])!;
    return (int)result.GetType().GetProperty("Size")!.GetValue(result)!;
}
if (ContextSize(Context(module, "x64"), vectorOwner) != 64 ||
    ContextSize(Context(module, "arm64"), vectorOwner) != 48)
    throw new Exception("Layout results leaked between architectures");
var chain = new List<TypeDefinition>();
for (var depth = 0; depth < 129; depth++)
{
    var nested = new TypeDefinition("Fixture", "Depth" + depth, outer.Attributes, valueType);
    nested.Fields.Add(new FieldDefinition("Child", Mono.Cecil.FieldAttributes.Public,
        depth == 0 ? module.TypeSystem.UInt64 : chain[^1]));
    module.Types.Add(nested);
    chain.Add(nested);
}
var deepContext = Context(module, "scalar");
ContextSize(deepContext, chain[64]);
try
{
    ContextSize(deepContext, chain[^1]);
    throw new Exception("A cached child bypassed the aggregate nesting limit");
}
catch (TargetInvocationException error) when (error.InnerException is InvalidDataException invalid &&
    invalid.Message.StartsWith("Recursive or excessively nested aggregate layout:", StringComparison.Ordinal)) { }
Console.WriteLine("PASS layout contexts preserve architecture and nesting-validation boundaries");

var kind = extractor.GetType("Nethermind.LeanCIL.LeanEmitter", true)!
    .GetMethod("Kind", BindingFlags.Static | BindingFlags.NonPublic)!;
try
{
    kind.Invoke(null, [vectorOwner, module, "x64", Context(module, "arm64")]);
    throw new Exception("A mismatched layout context was accepted by emission");
}
catch (TargetInvocationException error) when (error.InnerException is InvalidDataException invalid &&
    invalid.Message == "Layout context does not match module or architecture.") { }
Console.WriteLine("PASS context-taking emission rejects mismatched architecture");
