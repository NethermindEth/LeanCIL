#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PinnedMetadata.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

using System.Reflection;
using System.Text.RegularExpressions;
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
using var pinned = new PinnedMetadata(extractor, At("Examples/Assembly/bin/Examples.dll"));
var module = pinned.Module;
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
string Lean(object operation) => (string)operation.GetType()
    .GetMethod("ToLean", BindingFlags.Instance | BindingFlags.NonPublic | BindingFlags.Public, Type.EmptyTypes)!
    .Invoke(operation, null)!;
object Operation(Instruction instruction) => translate.Invoke(null,
    [instruction, caller, methods, 0, Index(caller), null, null, null, null, null, null])!;
string Translate(Instruction instruction) => Lean(Operation(instruction));
string? Link(Instruction instruction)
{
    var operation = Operation(instruction);
    return (string?)operation.GetType().GetMethod("Link", BindingFlags.Instance | BindingFlags.NonPublic |
        BindingFlags.Public)!.Invoke(operation, [(Func<int, string>)(index => $"{index}")]);
}
if (Translate(call) != ".call 1 0") throw new Exception("Incorrect call index");
// The link is read from the same operation as the instruction, so the two cannot name different callees.
if (Link(call) != ".direct 1") throw new Exception("Incorrect call link");
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
if (Link(choose) is not null) throw new Exception("A branch carries a call link");
Console.WriteLine("PASS translated method indexes reject missing callees and preserve switch target order");
var runtimeScope = module.AssemblyReferences.Single(reference => reference.Name == "System.Runtime");
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
var intrinsicsScope = module.AssemblyReferences.Single(reference => reference.Name == "System.Runtime.Intrinsics");
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

var indexHomes = extractor.GetType("Nethermind.LeanCIL.ParameterStorage", true)!
    .GetMethod("IndexHomes", BindingFlags.Static | BindingFlags.NonPublic)!
    .CreateDelegate<Func<IEnumerable<int>, Dictionary<int, int>>>();
var homePositions = indexHomes([2, 1, 2]);
if (homePositions[2] != 0 || homePositions[1] != 1 || homePositions.ContainsKey(0))
    throw new Exception("Home positions lost first-match or missing-argument behavior");
var argumentMethod = new MethodDefinition("Arguments", Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
owner.Methods.Add(argumentMethod);
for (var argument = 0; argument < 3; argument++)
    argumentMethod.Parameters.Add(new ParameterDefinition("p" + argument,
        Mono.Cecil.ParameterAttributes.None, module.TypeSystem.Int32));
argumentMethod.Body.Variables.Add(new VariableDefinition(module.TypeSystem.Int32));
argumentMethod.Body.Variables.Add(new VariableDefinition(module.TypeSystem.Int32));
var storeArgument = Instruction.Create(OpCodes.Starg, argumentMethod.Parameters[1]);
var loadArgument = Instruction.Create(OpCodes.Ldarg, argumentMethod.Parameters[1]);
var addressArgument = Instruction.Create(OpCodes.Ldarga, argumentMethod.Parameters[1]);
foreach (var instruction in new[] { Instruction.Create(OpCodes.Ldc_I4_0), storeArgument, loadArgument,
    Instruction.Create(OpCodes.Pop), addressArgument, Instruction.Create(OpCodes.Pop), Instruction.Create(OpCodes.Ret) })
    argumentMethod.Body.Instructions.Add(instruction);
string TranslateArgument(Instruction instruction, Dictionary<int, int> positions) => Lean(translate.Invoke(null,
    [instruction, argumentMethod, new Dictionary<MethodDefinition, int> { [argumentMethod] = 0 },
        0, Index(argumentMethod), null, null, positions, null, null, null])!);
if (TranslateArgument(storeArgument, homePositions) != ".starg 1" ||
    TranslateArgument(loadArgument, homePositions) != ".ldarg 1" ||
    TranslateArgument(addressArgument, homePositions) != ".ldarga 1")
    throw new Exception("A homed argument's store, load or address no longer names the argument");
if (TranslateArgument(loadArgument, []) != ".ldarg 1")
    throw new Exception("Unhomed loads no longer use the original argument");
try
{
    TranslateArgument(storeArgument, []);
    throw new Exception("A store without a home was admitted");
}
catch (TargetInvocationException error) when (error.InnerException is InvalidDataException rejected &&
    rejected.Message == "Missing parameter storage") { }
try
{
    TranslateArgument(addressArgument, []);
    throw new Exception("An address without a home was admitted");
}
catch (TargetInvocationException error) when (error.InnerException is InvalidDataException rejected &&
    rejected.Message == "Missing parameter storage") { }
Console.WriteLine("PASS home lookup preserves first positions, argument indexes and missing-home rejection");

// The typed operation model: the cases the outline generators branch on keep the spellings they are told apart by.
const BindingFlags Declared = BindingFlags.Instance | BindingFlags.Static | BindingFlags.Public |
    BindingFlags.NonPublic;
Type Model(string name) => extractor.GetType("Nethermind.LeanCIL." + name, true)!;
object Make(string name, params object?[] arguments) => Activator.CreateInstance(Model(name), arguments)!;
object Named(string type, string value) => Enum.Parse(Model(type), value);
object Property(object value, string name) => value.GetType().GetProperty(name, Declared)!.GetValue(value)!;
var bodyType = extractor.GetType("Nethermind.LeanCIL.ProofOutline", true)!.GetNestedType("Body",
    BindingFlags.NonPublic)!;
Array Operations(params object[] operations)
{
    var array = Array.CreateInstance(Model("Operation"), operations.Length);
    for (var at = 0; at < operations.Length; at++) array.SetValue(operations[at], at);
    return array;
}
object Body(params object[] operations) => Activator.CreateInstance(bodyType, Declared, null,
    [Operations(operations)], null)!;
int Loops(object body) => ((System.Collections.IList)bodyType.GetMethod("Loops", Declared)!.Invoke(body, null)!).Count;
// An argument read is pure only when its declared type is no narrow integer: (int, byte) below.
var mixedArguments = new MethodDefinition("Mixed", Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Int32);
mixedArguments.Parameters.Add(new ParameterDefinition("word", Mono.Cecil.ParameterAttributes.None,
    module.TypeSystem.Int32));
mixedArguments.Parameters.Add(new ParameterDefinition("small", Mono.Cecil.ParameterAttributes.None,
    module.TypeSystem.Byte));
owner.Methods.Add(mixedArguments);
bool Pure(object operation, bool plainReturn = true) =>
    (bool)bodyType.GetMethod("Pure", Declared, [Model("Operation"), typeof(MethodDefinition), typeof(bool)])!
        .Invoke(null, [operation, mixedArguments, plainReturn])!;
var nop = Make("StackOperation", Named("StackOpcode", "Nop"));
var backEdge = Make("Jump", Named("JumpKind", "Less"), 0);
if (Loops(Body(nop, nop, backEdge)) != 1)
    throw new Exception("A conditional back edge is not found as a loop");
if (!Pure(Make("Arg", 0)) || Pure(Make("Arg", 1)) ||
    !Pure(Make("Return")) || Pure(Make("Return"), plainReturn: false) ||
    Pure(Make("Call", Named("CallKind", "Tail"), 1, 0)))
    throw new Exception("The pure operations are no longer exactly the admitted unnarrowed ones");
if (Lean(Make("Arg", 1)) != ".ldarg 1")
    throw new Exception("An argument load no longer renders as the decoded ldarg");
if (Lean(Make("LoadScalar", 4, false)) != ".loadScalar 4" ||
    Lean(Make("LoadScalar", 4, Named("LoadSign", "UnsignedSpelled"))) != ".loadScalar 4 false" ||
    Lean(Make("LoadScalar", 1, true)) != ".loadScalar 1 true" ||
    !Make("LoadScalar", 1, true).Equals(Make("LoadScalar", 1, Named("LoadSign", "Signed"))))
    throw new Exception("Scalar loads lost the spelling that tells the unaligned load from the aligned one");
if (Lean(Make("AddOffset", ulong.MaxValue - 7, true)) != "(.add 18446744073709551608 true)")
    throw new Exception("A negative stride lost its two's complement spelling");
var tail = Make("Call", Named("CallKind", "Tail"), 3, 0);
var renumbered = tail.GetType().GetMethod("Renumber", Declared)!.Invoke(tail, [(Func<int, int>)(_ => 1)])!;
if (!((IEnumerable<int>)Property(tail, "Methods")).SequenceEqual([3]) || Lean(renumbered) != ".tailCall 1 0")
    throw new Exception("A tail call does not expose and renumber its callee");
try
{
    Make("Constant", 32, -1L, true);
    throw new Exception("A negative numeral constant was admitted");
}
catch (TargetInvocationException error) when (error.InnerException is ArgumentOutOfRangeException) { }
// A `with` copy sets one member of an existing constant, so each member checks the other as well.
void Assign(object value, string property, object newValue) =>
    value.GetType().GetProperty(property, Declared)!.SetValue(value, newValue);
foreach (var (constant, property, newValue) in new (object, string, object)[]
{
    (Make("Constant", 32, 5L, true), "Value", -1L), (Make("Constant", 32, -1L, false), "Numeral", true)
})
    try
    {
        Assign(constant, property, newValue);
        throw new Exception("Changing " + property + " made a negative numeral constant");
    }
    catch (TargetInvocationException error) when (error.InnerException is ArgumentOutOfRangeException) { }
Console.WriteLine("PASS typed operations keep the spellings and shapes the outline generators branch on");

// The extractor's narrowing table, which the outline readers refuse arguments by, states for every primitive
// head the narrowing Lean's declaredNarrow gives it (pinned in Tests/ResolutionFacts.lean); an admitted enum
// narrows as its underlying type on both sides.
var narrowOf = extractor.GetType("Nethermind.LeanCIL.LeanEmitter", true)!
    .GetMethod("Narrow", BindingFlags.Static | BindingFlags.NonPublic)!;
string? NarrowName(TypeReference type) => narrowOf.Invoke(null, [type])?.ToString();
var system = module.TypeSystem;
foreach (var (head, narrowing) in new (TypeReference, string?)[]
{
    (system.Boolean, "Unsigned8"), (system.Char, "Unsigned16"), (system.SByte, "Signed8"), (system.Byte, "Unsigned8"),
    (system.Int16, "Signed16"), (system.UInt16, "Unsigned16"), (system.Int32, null), (system.UInt32, null),
    (system.Int64, null), (system.UInt64, null), (system.IntPtr, null), (system.UIntPtr, null),
    (system.Single, null), (system.Double, null)
})
    if (NarrowName(head) != narrowing)
        throw new Exception(
            $"{head.FullName} narrows as {NarrowName(head) ?? "nothing"}, not {narrowing ?? "nothing"}");
var enums = module.Types.Where(type => type.IsEnum).ToArray();
if (enums.Length == 0) throw new Exception("The examples declare no enum to compare narrowing on");
foreach (var enumeration in enums)
{
    var storage = enumeration.Fields.Single(field => !field.IsStatic).FieldType;
    if (NarrowName(enumeration) != NarrowName(storage))
        throw new Exception($"{enumeration.FullName} does not narrow as its underlying {storage.FullName}");
}
Console.WriteLine(
    $"PASS argument narrowing agrees with declaredNarrow on 14 primitive heads and {enums.Length} enums");

// A stage learns an instruction's category, callee and target from the typed Operation, never from the Lean text
// that renders it. Each place that reads generated Lean text is listed here with what it reads.
var sourceFiles = Directory.GetFiles(At("Extractor"), "*.cs").Concat(Directory.GetFiles(At("scripts"), "*.cs")
    .Where(path => !Path.GetFileName(path).StartsWith("Test", StringComparison.Ordinal)))
    .ToDictionary(path => Path.GetRelativePath(Root, path).Replace('\\', '/'), File.ReadAllText);
var constructors = RenderedLeanReaders.Constructors(sourceFiles["Extractor/Operation.cs"]);
foreach (var rendered in new[] { "ret", "ldloc", "switch", "br", "brtrue", "call", "callInstance", "tailCall" })
    if (!constructors.Contains(rendered)) throw new Exception("Operation no longer renders ." + rendered);
var readers = RenderedLeanReaders.Scan(sourceFiles, constructors);
(string File, int Reads, string Reason)[] allowedReaders =
[
    ("Extractor/ProofGates.cs", 2, "compares whole method definitions and signatures of two extractions"),
    ("scripts/ConsumerVerification.cs", 3, "the component splitter cuts module text at declaration boundaries"),
    ("scripts/VerifyReports.cs", 1, "reads the source location table of Symbols.lean, not an instruction"),
    ("scripts/BenchmarkExternalIdentities.cs", 1, "reads identity byte arrays from baseline extractions"),
];
var actualReaders = readers.Where(finding => finding.Kind == "reads generated Lean")
    .GroupBy(finding => finding.File).Select(group => (group.Key, group.Count())).Order().ToArray();
var expectedReaders = allowedReaders.Select(entry => (entry.File, entry.Reads)).Order().ToArray();
if (!actualReaders.SequenceEqual(expectedReaders) || readers.Any(finding => finding.Kind != "reads generated Lean"))
    throw new Exception("Stages read generated Lean text outside the allowed list:\n" +
        string.Join("\n", readers.Select(finding => $"{finding.File}:{finding.Line}: {finding.Kind}")));
// Each rule must fail on a scratch source, so that a weakened pattern cannot pass unnoticed.
foreach (var (scratchFile, scratchText, rule) in new (string, string, string)[]
{
    ("Extractor/Scratch.cs", "var calls = Regex.Matches(emitted, @\"^\\s*\\.call \\d+\");",
        "reads generated Lean"),
    ("Extractor/Scratch.cs", "if (line.StartsWith(\".ret\", StringComparison.Ordinal)) returns++;",
        "reads generated Lean"),
    ("Extractor/Scratch.cs", "var bodies = Regex.Matches(module, @\"^def method\\d+ : Method := \");",
        "reads generated Lean"),
    ("Extractor/Scratch.cs", "var text = op.ToLean(); // parsed below",
        "renders an operation outside emission and messages"),
    ("Extractor/ProofOutlineLoops.cs", "if (op.ToLean().StartsWith(\".br\")) return Stop(\"x\");",
        "renders an operation outside emission and messages"),
    ("Extractor/LeanEmitter.cs", "var first = ops.Select(op => op.ToLean()).First(text => text.Contains(\"x\"));",
        "searches a rendered operation"),
})
    if (!RenderedLeanReaders.Scan(new Dictionary<string, string> { [scratchFile] = scratchText }, constructors)
            .Any(finding => finding.Kind == rule))
        throw new Exception("Not found as " + rule + ": " + scratchText);
if (RenderedLeanReaders.Scan(new Dictionary<string, string> { ["Extractor/Scratch.cs"] =
        "var calls = operations.Count(operation => operation is Call);" }, constructors).Count != 0)
    throw new Exception("A typed read of calls was reported");
Console.WriteLine("PASS no stage reads opcode, call or target information back from generated Lean text");

/// <summary>Finds code that reads generated Lean text or reads back what an Operation renders.</summary>
static partial class RenderedLeanReaders
{
    internal sealed record Finding(string File, int Line, string Kind);

    /// <summary>Files that write an operation into the generated module.</summary>
    static readonly string[] Emitters = ["Extractor/LeanEmitter.cs", "Extractor/TemplateEmitter.cs"];

    /// <summary>Files that quote an operation in a message that stops an outline or reports a lint.</summary>
    static readonly string[] Messengers =
    [
        "Extractor/ExceptionLint.cs", "Extractor/ProofOutlineGenerate.cs", "Extractor/ProofOutlineLoops.cs",
        "Extractor/ProofOutlineObjects.cs", "Extractor/ProofOutlineStructLoops.cs", "Extractor/ProofOutlineStructs.cs"
    ];

    [GeneratedRegex("\"\\.([a-z][A-Za-z0-9]*)")]
    private static partial Regex RenderedConstructor();

    [GeneratedRegex(@"(?:Contains|StartsWith|EndsWith|IndexOf|Split|Matches|Replace|IsMatch|Match|" +
        @"GeneratedRegex|new Regex)\((?<rest>.*)$")]
    private static partial Regex SearchCall();

    [GeneratedRegex(@"""[^""]*(?:\b(?:def|theorem|lemma|namespace|structure|instance)\s*\(?[A-Za-z.]|" +
        @"method\\?d|method\[0-9\])[^""]*""")]
    private static partial Regex GeneratedDeclaration();

    [GeneratedRegex(@"\b(?:op|operation|ops\[\w+\]|values\[\w+\])\.ToLean\(|\bop\.Link\(|" +
        @"new Unsupported\(.*\)\.ToLean\(")]
    private static partial Regex RenderedOperation();

    [GeneratedRegex(@"\$""[^""]*\{(?:op|ops\[\w+\])\.ToLean\(\)\}|""\s*\+\s*operation\.ToLean\(\)")]
    private static partial Regex OperationInMessage();

    /// <summary>The Lean constructor names that Operation.cs renders, without their dot.</summary>
    internal static string[] Constructors(string operationSource) =>
        [.. RenderedConstructor().Matches(operationSource).Select(match => match.Groups[1].Value).Distinct()];

    /// <summary>One finding per line that reads generated Lean or misuses a rendered operation.</summary>
    internal static List<Finding> Scan(IReadOnlyDictionary<string, string> files, string[] constructors)
    {
        var constructor = new Regex("\"[^\"]*(?<![\\w.])\\\\?\\.(?:" + string.Join("|", constructors) +
            @")\b[^""]*""");
        var found = new List<Finding>();
        foreach (var (file, text) in files)
        {
            if (file == "Extractor/Operation.cs") continue;
            var lines = text.Split('\n');
            for (var index = 0; index < lines.Length; index++)
            {
                var line = lines[index];
                var search = SearchCall().Match(line);
                var searched = search.Success && (GeneratedDeclaration().IsMatch(search.Groups["rest"].Value) ||
                    constructor.IsMatch(search.Groups["rest"].Value));
                if (searched) found.Add(new(file, index + 1, "reads generated Lean"));
                if (!RenderedOperation().IsMatch(line)) continue;
                var allowed = Emitters.Contains(file) ||
                    (Messengers.Contains(file) && OperationInMessage().IsMatch(line));
                if (!allowed) found.Add(new(file, index + 1, "renders an operation outside emission and messages"));
                else if (search.Success) found.Add(new(file, index + 1, "searches a rendered operation"));
            }
        }
        return found;
    }
}
