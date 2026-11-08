#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include RejectedEvidence.cs

using Mono.Cecil;
using Mono.Cecil.Cil;
using System.Text.RegularExpressions;

// Class instances on the checked heap: proofs about identity, presence, scalar, class-typed and opaque fields,
// instance receivers, calls framed across objects, construction against the heap budget and fields of base
// classes, and the named rejection of every class shape or access the model does not represent.
using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Objects");
Directory.CreateDirectory(root);

foreach (var (proof, entry) in new[]
{
    ("SameObject", "Objects::Same(Examples.Account,Examples.Account)"),
    ("NullObject", "Objects::IsNull(Examples.Account)"),
    ("PresentObject", "Objects::IsPresent(Examples.Account)"),
    ("FirstPresentObject", "Objects::FirstPresent(Examples.Account,Examples.Account)"),
    ("BalanceField", "Objects::BalanceOf(Examples.Account)"),
    ("ReplaceField", "Objects::Replace(Examples.Account,System.UInt64)"),
    ("LimitField", "Objects::SetLimit(Examples.Account,System.UInt32)"),
    ("HeadroomReceiver", "Account::get_Headroom()"),
    ("BumpBoth", "Objects::BumpBoth(Examples.Account,Examples.Account,System.UInt64)"),
    ("FreshObject", "Objects::Fresh(System.UInt32)"),
    ("DepositBoth", "Objects::DepositBoth(Examples.Account,Examples.Account,System.UInt64)"),
    ("DepositTimes", "Objects::DepositTimes(Examples.Account,System.UInt64,System.UInt32)"),
    ("TwoMarkers", "Objects::TwoMarkers()"),
    ("LinkedNodes", "Objects::LinkedValue(Examples.Node,Examples.Node)"),
    ("OpaqueTag", "Objects::CopyTag(Examples.Tagged,Examples.Tagged)"),
    ("BaseField", "Objects::IdOf(Examples.Shape)"),
    ("DerivedObject", "Objects::Describe(System.UInt64,System.UInt64)"),
    ("AnimalLegs", "VirtualCalls::LegsOf(Examples.Animal)"),
    ("AnimalLoudness", "VirtualCalls::LoudnessOf(Examples.Animal)"),
    ("FreshDogLegs", "VirtualCalls::DogLegs()"),
    ("DogTest", "ClassTests::IsDog(Examples.Animal)"),
    ("DogCast", "ClassTests::AsDog(Examples.Animal)")
})
{
    verification.Verify(assembly, "Examples", entry, At($"Examples/Proofs/{proof}.lean"), Path.Combine(root, proof));
    Console.WriteLine($"PASS {proof}: {entry}");
}

// Each named field is checked against the operation it names, so a view with another offset or
// width fails its own theorem instead of naming storage the code never touches.
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution",
    "CIL.Safety.ObjectFields");
var forgedViews = new RejectedEvidence(root);
var linked = File.ReadAllText(Path.Combine(root, "LinkedNodes", "Extracted.lean"));
foreach (var (name, view, forged, marker) in new[]
{
    ("offset", "def Next : Safety.ReferenceField := ⟨type, 8⟩", "def Next : Safety.ReferenceField := ⟨type, 0⟩",
        "Next.accessedBy"),
    ("width", "def Value : Safety.WordField 8 := ⟨type, 0⟩", "def Value : Safety.WordField 4 := ⟨type, 0⟩",
        "Value.accessedBy")
})
{
    if (!linked.Contains(view, StringComparison.Ordinal))
        throw new InvalidOperationException("The extraction does not name the field view: " + view);
    var path = Path.Combine(root, $"ForgedView-{name}.lean");
    File.WriteAllText(path, linked.Replace(view, forged, StringComparison.Ordinal));
    forgedViews.Add(path, $"PASS forged field view rejected: {name}", marker);
}
// Lean re-resolves every dispatch table entry from the catalog and requires every concrete class
// deriving from the slot's class, so a table that swaps bodies or omits a class fails its check.
var dispatched = File.ReadAllText(Path.Combine(root, "AnimalLegs", "Extracted.lean"));
const string animalScope = "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null";
var birdEntry = $"(.object \"{animalScope}\" \"Examples.Bird\", ";
var dogEntry = $"(.object \"{animalScope}\" \"Examples.Dog\", ";
var table = Regex.Match(dispatched, @"\.callVirtual \[\(.*?\)\] 1").Value;
var entries = Regex.Matches(table, @"(\(\.object [^)]*?, )(\d+)\)").Select(entry => entry.Groups).ToArray();
if (entries.Length != 2 || !table.Contains(birdEntry + entries[0][2].Value, StringComparison.Ordinal) ||
    !table.Contains(dogEntry + entries[1][2].Value, StringComparison.Ordinal))
    throw new InvalidOperationException("The extraction does not list Bird and Dog in its dispatch table: " + table);
foreach (var (name, forged) in new[]
{
    ("swapped", $".callVirtual [{birdEntry}{entries[1][2].Value}), {dogEntry}{entries[0][2].Value})] 1"),
    ("omitted", $".callVirtual [{dogEntry}{entries[1][2].Value})] 1")
})
{
    var path = Path.Combine(root, $"ForgedTable-{name}.lean");
    File.WriteAllText(path, dispatched.Replace(table, forged, StringComparison.Ordinal));
    forgedViews.Add(path, $"PASS forged dispatch table rejected: {name}",
        "Extraction.ConstrainedCallsValid method0DispatchTypes");
}
// Lean binds a type test to its raw opcode and class, so an emitted test of another class or with
// the other outcome for a failed cast fails the scalar flow check.
var cast = File.ReadAllText(Path.Combine(root, "DogCast", "Extracted.lean"));
var castTest = $".objectTest ({dogEntry.TrimStart('(').TrimEnd(',', ' ')}) true";
if (!cast.Contains(castTest, StringComparison.Ordinal))
    throw new InvalidOperationException("The extraction does not test the cast against Dog: " + castTest);
foreach (var (name, forged) in new[]
{
    ("class", castTest.Replace("Examples.Dog", "Examples.Bird", StringComparison.Ordinal)),
    ("outcome", castTest[..^" true".Length] + " false")
})
{
    var path = Path.Combine(root, $"ForgedCast-{name}.lean");
    File.WriteAllText(path, cast.Replace(castTest, forged, StringComparison.Ordinal));
    forgedViews.Add(path, $"PASS forged type test rejected: {name}", "Extraction.ScalarFlowValid");
}
forgedViews.Check();

// The entry's call proof simplifies with the constructor's closed body; without it the proof
// falls back to a whole-method kernel decision.
var constructed = File.ReadAllLines(Path.Combine(root, "FreshObject", "Extracted.lean"));
var construction = constructed.Single(line => line.StartsWith("  .newObject ", StringComparison.Ordinal));
var constructor = construction.Split(' ', StringSplitOptions.RemoveEmptyEntries)[1];
var entryCalls = constructed.Single(line =>
    line.StartsWith("theorem method0_calls_validated ", StringComparison.Ordinal));
if (!entryCalls.Contains("by cil_managed_calls [", StringComparison.Ordinal) ||
    !entryCalls.Contains($"method{constructor}Closed", StringComparison.Ordinal))
    throw new InvalidOperationException("The constructing method's call proof omits the constructor:\n" + entryCalls);
Console.WriteLine("PASS construction call proof names the constructor");

foreach (var mutation in new[]
{
    "abstract", "base", "baseRejected", "explicit", "finalizer", "interface", "byref", "address", "reference",
    "fieldType", "receiverAddress", "opaqueRead"
})
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string expected;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var account = module.GetType("Examples.Account");
        var method = module.GetType("Examples.Objects").Methods.Single(candidate => candidate.Name == "IsNull");
        var getter = account.Methods.Single(candidate => candidate.Name == "get_Headroom");
        var runtime = module.TypeSystem.Object.Scope;
        switch (mutation)
        {
            case "abstract": module.GetType("Examples.Tally").IsAbstract = true; break;
            case "base": account.BaseType = new TypeReference("System", "Exception", module, runtime); break;
            case "baseRejected":
                var shape = module.GetType("Examples.Shape");
                shape.IsAutoLayout = false;
                shape.IsExplicitLayout = true;
                account.BaseType = shape;
                break;
            case "explicit":
                account.IsAutoLayout = false;
                account.IsExplicitLayout = true;
                foreach (var field in account.Fields) field.Offset = 0;
                break;
            case "finalizer":
                var finalizer = new MethodDefinition("Finalize", MethodAttributes.Family | MethodAttributes.Virtual |
                    MethodAttributes.HideBySig, module.TypeSystem.Void);
                finalizer.Body.GetILProcessor().Emit(OpCodes.Ret);
                account.Methods.Add(finalizer);
                break;
            case "interface":
                method.Parameters[0].ParameterType = module.GetType("Examples.ICounterValue");
                break;
            case "byref":
                method.Parameters[0].ParameterType = new ByReferenceType(account);
                break;
            case "address":
                var receiver = method.Body.Instructions[0];
                var processor = method.Body.GetILProcessor();
                processor.InsertAfter(receiver, processor.Create(OpCodes.Ldind_U4));
                processor.InsertAfter(receiver, processor.Create(OpCodes.Ldflda,
                    account.Fields.Single(field => field.Name == "Limit")));
                processor.Replace(method.Body.Instructions[3], processor.Create(OpCodes.Ldc_I4_0));
                break;
            case "reference":
                var owner = new FieldDefinition("Owner", FieldAttributes.Public,
                    new OptionalModifierType(module.TypeSystem.Object, module.TypeSystem.String));
                account.Fields.Add(owner);
                method.Body.GetILProcessor().InsertAfter(method.Body.Instructions[0],
                    Instruction.Create(OpCodes.Ldfld, owner));
                break;
            case "opaqueRead":
                var tagged = module.GetType("Examples.Objects").Methods.Single(candidate => candidate.Name == "HasTag");
                var load = tagged.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Ldfld);
                var reads = tagged.Body.GetILProcessor();
                var length = new MethodReference("get_Length", module.TypeSystem.Int32, module.TypeSystem.String)
                    { HasThis = true };
                reads.InsertAfter(load, reads.Create(OpCodes.Pop));
                reads.InsertAfter(load, reads.Create(OpCodes.Callvirt, length));
                reads.InsertAfter(load, reads.Create(OpCodes.Dup));
                break;
            case "fieldType":
                var rate = new FieldDefinition("Rate", FieldAttributes.Public, module.TypeSystem.Double);
                account.Fields.Add(rate);
                var first = method.Body.Instructions[0];
                var editor = method.Body.GetILProcessor();
                editor.InsertAfter(first, editor.Create(OpCodes.Ldarg_0));
                editor.InsertAfter(first, editor.Create(OpCodes.Pop));
                editor.InsertAfter(first, editor.Create(OpCodes.Ldfld, rate));
                break;
            case "receiverAddress":
                var body = getter.Body.GetILProcessor();
                body.InsertBefore(getter.Body.Instructions[0], body.Create(OpCodes.Pop));
                body.InsertBefore(getter.Body.Instructions[0],
                    body.Create(OpCodes.Ldarga_S, getter.Body.ThisParameter));
                break;
        }
        expected = mutation switch
        {
            "abstract" => "Unsupported construction of an abstract class: Examples.Tally\n" +
                "  newobj of an abstract class fails at run time",
            "base" => "Unsupported class instance type: Examples.Account\n  Only classes deriving from System.Object " +
                "through admitted classes are modelled; System.Exception is not one.",
            "baseRejected" => "Unsupported class instance type: Examples.Account\n  Its base class is not admitted: " +
                "Unsupported class instance type: Examples.Shape\n    Explicit class layout",
            "explicit" => "Unsupported class instance type: Examples.Account\n  Explicit class layout",
            "finalizer" => "Unsupported class instance type: Examples.Account\n  A finalizer",
            "interface" => "Unsupported class instance type: Examples.ICounterValue\n  Interface-typed values",
            "byref" => "Unsupported by-reference class instance: Examples.Account&",
            "address" => "Unsupported field address on a class instance: System.UInt32 Examples.Account::Limit",
            "reference" => "Unsupported reference-typed field: System.String modopt(System.Object) " +
                "Examples.Account::Owner\n  Only fields holding class instances are modelled",
            "opaqueRead" => "callvirt requires an adjacent concrete constrained receiver",
            "fieldType" => "Unsupported class instance field type: System.Double Examples.Account::Rate",
            "receiverAddress" =>
                "Unsupported address of a class instance receiver: System.UInt64 Examples.Account::get_Headroom()",
            _ => throw new InvalidOperationException("Unknown class rejection fixture: " + mutation)
        };
        module.Write(dll);
    }
    var selector = mutation switch
    {
        "abstract" => "Objects::Fresh(System.UInt32)",
        "interface" => "Objects::IsNull(Examples.ICounterValue)",
        "byref" => "Objects::IsNull(Examples.Account&)",
        "receiverAddress" => "Account::get_Headroom()",
        "opaqueRead" => "Objects::HasTag(Examples.Tagged)",
        _ => "Objects::IsNull(Examples.Account)"
    };
    var result = Execute(["dotnet", ExtractorPath, "extract", dll, selector, output]);
    if (result.Code != 1 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        !result.Output.Replace("\r\n", "\n").Contains(expected, StringComparison.Ordinal))
        throw new InvalidOperationException($"Incorrect class rejection: {mutation}\n{result.Output}");
    Console.WriteLine($"PASS class rejection: {mutation}");
}
// A dispatch table must cover every class whose instances can reach the call, with the body the runtime selects;
// each hierarchy the extraction cannot close or resolve is rejected by name.
foreach (var mutation in new[] { "librarySlot", "unadmittedSubclass", "newSlotHiding", "reabstraction", "explicit" })
{
    var output = Path.Combine(root, "RejectDispatch-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var animal = module.GetType("Examples.Animal");
        var birdLegs = module.GetType("Examples.Bird").Methods.Single(candidate => candidate.Name == "Legs");
        switch (mutation)
        {
            case "librarySlot":
                var legsOf = module.GetType("Examples.VirtualCalls").Methods.Single(candidate =>
                    candidate.Name == "LegsOf");
                var editor = legsOf.Body.GetILProcessor();
                var call = legsOf.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Callvirt);
                editor.InsertAfter(call, editor.Create(OpCodes.Conv_U8));
                editor.Replace(call, editor.Create(OpCodes.Callvirt,
                    module.ImportReference(typeof(object).GetMethod("GetHashCode"))));
                break;
            case "unadmittedSubclass":
                module.Types.Add(new TypeDefinition("Examples", "Fish",
                    TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.ExplicitLayout, animal));
                break;
            case "newSlotHiding": birdLegs.IsNewSlot = true; break;
            case "reabstraction":
                birdLegs.IsAbstract = true;
                birdLegs.Body = null;
                break;
            case "explicit":
                module.GetType("Examples.Dog").Methods.Single(candidate => candidate.Name == "Legs").Overrides
                    .Add(animal.Methods.Single(candidate => candidate.Name == "Legs"));
                break;
        }
        module.Write(dll);
    }
    var expected = mutation switch
    {
        "librarySlot" => "Unsupported virtual call: System.Int32 System.Object::GetHashCode()\n" +
            "  Caller: System.UInt64 Examples.VirtualCalls::LegsOf(Examples.Animal) at IL_0001\n" +
            "  The slot is declared outside the extracted assemblies",
        "unadmittedSubclass" => "Examples.Fish derives from Examples.Animal but is not an admitted class",
        "newSlotHiding" => "System.UInt64 Examples.Bird::Legs() hides the slot with a new virtual method",
        "reabstraction" => "System.UInt64 Examples.Bird::Legs() re-abstracts the slot for Examples.Bird.",
        "explicit" => "System.UInt64 Examples.Dog::Legs() overrides by an explicit MethodImpl",
        _ => throw new InvalidOperationException("Unknown dispatch rejection fixture: " + mutation)
    };
    if (mutation != "librarySlot")
        expected = "Unsupported virtual call: System.UInt64 Examples.Animal::Legs()\n" +
            "  Caller: System.UInt64 Examples.VirtualCalls::LegsOf(Examples.Animal) at IL_0001\n  " + expected;
    var result = Execute(["dotnet", ExtractorPath, "extract", dll, "VirtualCalls::LegsOf(Examples.Animal)", output]);
    if (result.Code != 1 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        !result.Output.Replace("\r\n", "\n").Contains(expected, StringComparison.Ordinal))
        throw new InvalidOperationException($"Incorrect dispatch rejection: {mutation}\n{result.Output}");
    Console.WriteLine($"PASS dispatch rejection: {mutation}");
}

// An instance records only its own and its admitted base classes, so a type test against anything
// else is rejected by name.
foreach (var mutation in new[] { "interface", "root", "library", "unadmitted" })
{
    var output = Path.Combine(root, "RejectCast-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string target;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var test = module.GetType("Examples.ClassTests").Methods.Single(candidate => candidate.Name == "AsDog")
            .Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Castclass);
        TypeReference replaced;
        switch (mutation)
        {
            case "interface": replaced = module.GetType("Examples.ICounterValue"); break;
            case "root": replaced = module.TypeSystem.Object; break;
            case "library": replaced = module.TypeSystem.String; break;
            default:
                var fish = new TypeDefinition("Examples", "Fish", TypeAttributes.Public | TypeAttributes.Sealed |
                    TypeAttributes.ExplicitLayout, module.GetType("Examples.Animal"));
                module.Types.Add(fish);
                replaced = fish;
                break;
        }
        test.Operand = replaced;
        target = replaced.FullName;
        module.Write(dll);
    }
    var expected = $"Unsupported type test: castclass {target}\n  " + mutation switch
    {
        "interface" => "Interface type tests need the interfaces an instance implements",
        "root" => "Every instance is a System.Object, which the model does not record.",
        "library" => "Only classes of the pinned assemblies are tested",
        _ => "Unsupported class instance type: Examples.Fish\n    Explicit class layout"
    };
    var result = Execute(["dotnet", ExtractorPath, "extract", dll, "ClassTests::AsDog(Examples.Animal)", output]);
    if (result.Code != 1 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        !result.Output.Replace("\r\n", "\n").Contains(expected, StringComparison.Ordinal))
        throw new InvalidOperationException($"Incorrect type test rejection: {mutation}\n{result.Output}");
    Console.WriteLine($"PASS type test rejection: {mutation}");
}

// A virtual method's own body is an entry like any instance method: the theorem is about that body,
// whichever call reaches it.
var virtualOutput = Path.Combine(root, "VirtualBody");
Directory.CreateDirectory(virtualOutput);
var virtualDll = Path.Combine(virtualOutput, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var getter = module.GetType("Examples.Account").Methods.Single(candidate => candidate.Name == "get_Headroom");
    getter.IsVirtual = true;
    getter.IsNewSlot = true;
    module.Write(virtualDll);
}
verification.Verify(virtualDll, "Examples", "Account::get_Headroom()", At("Examples/Proofs/HeadroomReceiver.lean"),
    Path.Combine(virtualOutput, "Proof"));
Console.WriteLine("PASS virtual method body proved as an entry");

Console.WriteLine("PASS objects: identity, presence, scalar and reference field, receiver, framed call " +
    "construction, base class field, virtual dispatch and type test proofs, " +
    "and named rejection of unmodelled class shapes, field accesses, calls, dispatch tables and type tests");
