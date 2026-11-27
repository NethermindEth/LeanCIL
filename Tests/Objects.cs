#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BatchVerification.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include PreparedLeanFixtures.cs
#:include RejectedEvidence.cs
#:include GeneratedEvidence.cs
#:include ContractVariants.cs

using Mono.Cecil;
using Mono.Cecil.Cil;
using System.Text.RegularExpressions;

// Class instances on the checked heap: proofs about identity, presence, scalar, class-typed and opaque fields,
// instance receivers, calls framed across objects, construction against the heap budget, fields of base
// classes, arrays of class references and value-array fields, and the named rejection of every class shape or
// access the model does not represent.
using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Objects");
Directory.CreateDirectory(root);

VerifyClassIdentity(verification, assembly, root);

// One batch elaborates, replays and audits every proof; a pass is reported only after the whole batch is certified.
var queue = new GeneratedQueue(verification, assembly);
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
    ("AnimalLoudness", "VirtualCalls::LoudnessOf(Examples.Animal)"),
    ("FreshDogLegs", "VirtualCalls::DogLegs()"),
    ("DogTest", "ClassTests::IsDog(Examples.Animal)"),
    ("DogCast", "ClassTests::AsDog(Examples.Animal)"),
    ("NodePair", "NodeArrays::Pair(Examples.Node,Examples.Node)"),
    ("ArrayElement", "NodeArrays::At(Examples.Node[],System.Int32)"),
    ("ArrayCovariance", "NodeArrays::Put(Examples.Shape[],System.Int32,Examples.Shape)"),
    ("BucketItems", "NodeArrays::First(Examples.Bucket)"),
    ("BucketRefill", "NodeArrays::Refill(Examples.Bucket,Examples.Node[])"),
    ("TagStore", "TagArrays::Put(System.String[],System.Int32,Examples.Tagged)"),
    ("TagLoad", "TagArrays::Take(Examples.Tagged,System.String[],System.Int32)"),
    ("SampleValues", "SampleArrays::ValuesOf(Examples.Samples)"),
    ("SampleRefill", "SampleArrays::Refill(Examples.Samples,System.Int32[])"),
    ("SampleCount", "SampleArrays::Count(Examples.Samples)"),
    ("TilePairs", "TileArrays::PairsOf(Examples.Tiles)"),
    ("TilePairCount", "TileArrays::PairCount(Examples.Tiles)"),
    ("TileRelane", "TileArrays::Relane(Examples.Tiles,System.Runtime.Intrinsics.Vector128`1<System.UInt64>[])"),
    ("SampleCountAfterRefill", "SampleArrays::CountAfterRefill(Examples.Samples,Examples.Samples,System.Int32[])"),
    ("TileHold",
        "TileArrays::Hold(Examples.AggregateArrays/Pair[],System.Runtime.Intrinsics.Vector128`1<System.UInt64>[])")
})
    queue.Add(new(entry, At($"Examples/Proofs/{proof}.lean"), Path.Combine(root, proof)),
        () => Console.WriteLine($"PASS {proof}: {entry}"));
queue.Flush();

const string animalScope = "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null";
const string legsSelector = "VirtualCalls::LegsOf(Examples.Animal)";
var wrongLegs = Path.Combine(root, "TwoLeggedDog");
Directory.CreateDirectory(wrongLegs);
var wrongLegsAssembly = Path.Combine(wrongLegs, "Examples.dll");
using (var variant = ModuleDefinition.ReadModule(assembly))
{
    var dogLegs = variant.GetType("Examples.Dog").Methods.Single(method => method.Name == "Legs");
    dogLegs.Body.Instructions.Single(site => site.OpCode == OpCodes.Ldc_I4_4).OpCode = OpCodes.Ldc_I4_2;
    variant.Write(wrongLegsAssembly);
}
verification.VerifyContractVariant(assembly, "Examples", legsSelector, Path.Combine(root, "AnimalLegs"),
    wrongLegsAssembly, legsSelector, wrongLegs, $$"""
    /-- Both runtime classes have the same abstract base in the selected assembly. -/
    private def animalClass (isDog : Bool) : RuntimeType :=
      ⟨.object "{{animalScope}}" (if isDog then "Examples.Dog" else "Examples.Bird"),
        [.object "{{animalScope}}" "Examples.Animal"]⟩

    /-- The virtual call returns the leg count of its live receiver and preserves caller memory. -/
    def legs : MethodContract (Bool × Reference) W64 where
      args input := [.object (.address input.2)]
      results value := [.scalar (.i64 value)]
      pre input memory := formObject memory (.address input.2) = .ok (.object (.address input.2)) ∧
        runtimeTypeOf memory input.2 = .ok (animalClass input.1)
      footprint _ := []
      post input before after value := before = after ∧ value = (if input.1 then 4 else 2)
    """, """
    /-- Dispatch selects the corresponding override for every formed dog or bird. -/
    theorem correctness : legs.Holds Extracted.program 0 := by
      rintro ⟨isDog, receiver⟩ memory ⟨formed, typed⟩
      cases isDog
      · exact MethodContract.Holds.intro (c := legs) (input := (false, receiver)) memory 2
          (ExampleProof.bird_legs memory receiver formed typed) (Confined.refl _ _) ⟨rfl, rfl⟩
      · exact MethodContract.Holds.intro (c := legs) (input := (true, receiver)) memory 4
          (ExampleProof.dog_legs memory receiver formed typed) (Confined.refl _ _) ⟨rfl, rfl⟩
    """, """
    /-- Allocation zero contains a live dog whose virtual override the caller must select. -/
    private def dogMemory : Memory := { Memory.empty with
      allocations := fun id => if id = 0 then some
        ⟨.object (animalClass true), ⟨1, 1, []⟩, true, []⟩ else none
      nextIdentity := 1 }

    /-- The compiled caller returns two for this dog after its override is changed. -/
    theorem correctness : legs.Refuted Extracted.program 0 :=
      .of_return (input := (true, ⟨0, 0⟩)) (initial := dogMemory) ⟨rfl, rfl⟩
        (rfl : invoke Extracted.program 16 0 (legs.args (true, ⟨0, 0⟩)) dogMemory =
          .ok (dogMemory, [.scalar (.i64 2)]))
        (by rintro ⟨-, value, encoded, -, rfl⟩; revert encoded; decide)
    """, example: At("Examples/Proofs/AnimalLegs.lean"));
Console.WriteLine("PASS virtual caller contract and certified two-legged Dog override");

const string lengthSelector = "NodeArrays::Count(Examples.Node[])";
var nullLength = Path.Combine(root, "NullArrayLength");
Directory.CreateDirectory(nullLength);
var nullLengthAssembly = Path.Combine(nullLength, "Examples.dll");
using (var variant = ModuleDefinition.ReadModule(assembly))
{
    var count = variant.GetType("Examples.NodeArrays").Methods.Single(method => method.Name == "Count");
    var length = count.Body.Instructions.Single(site => site.OpCode == OpCodes.Ldlen);
    var il = count.Body.GetILProcessor();
    il.InsertBefore(length, il.Create(OpCodes.Dup));
    il.InsertBefore(length, il.Create(OpCodes.Brtrue_S, length));
    il.InsertBefore(length, il.Create(OpCodes.Pop));
    il.InsertBefore(length, il.Create(OpCodes.Ldc_I4_0));
    il.InsertBefore(length, il.Create(OpCodes.Ret));
    variant.Write(nullLengthAssembly);
}
verification.VerifyContractVariant(assembly, "Examples", lengthSelector, Path.Combine(root, "ArrayLength"),
    nullLengthAssembly, lengthSelector, nullLength, """
    /-- Every live Node array returns its length in unchanged memory. Null raises NullReferenceException. -/
    def arrayLength : OutcomeContract (Option (Reference × Nat)) W32 where
      args input := [.object (match input with | none => .null | some (nodes, _) => .address nodes)]
      results value := [.scalar (.i32 value)]
      pre input memory := match input with
        | none => True
        | some (nodes, size) => ReferenceArray.Live memory nodes
            (.object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Node") size
      footprint _ := []
      post input before after value :=
        before = after ∧ ∃ nodes size, input = some (nodes, size) ∧ value = BitVec.ofNat 32 size
      raises input _ := if input.isNone then some .nullReference else none
    """, """
    theorem correctness : arrayLength.HoldsCLR Extracted.program 0 := by
      intro input memory live
      cases input with
      | none =>
        obtain ⟨fuel, ran⟩ := ExampleProof.null_array memory
        exact ⟨fuel, _, ran, rfl⟩
      | some pair =>
        obtain ⟨nodes, size⟩ := pair
        obtain ⟨fuel, ran⟩ := ExampleProof.correctness memory nodes size live
        exact ⟨fuel, memory, _, ran, Confined.refl _ _, _, rfl, rfl, nodes, size, rfl, by simp⟩
    """, """
    /-- The modified body returns zero on null before it reaches ldlen. -/
    theorem correctness : arrayLength.RefutedCLR Extracted.program 0 :=
      .of_return (input := none) (initial := Memory.empty) trivial
        (rfl : invoke Extracted.program 16 0 [.object .null] Memory.empty =
          .ok (Memory.empty, [.scalar (.i32 0)])) trivial
    """, example: At("Examples/Proofs/ArrayLength.lean"),
    imports: "import CIL.Safety.ReferenceArrayElements\nimport CIL.Safety.RuntimeExceptions");
Console.WriteLine("PASS array length contract and certified zero return for a null array");


// The same null return also violates a contract that drops the live-array length guarantee.
// Changing the proved contract must invalidate its pairing with the original counterexample.
var lengthControl = Path.Combine(root, "ChangedArrayLengthContract");
Directory.CreateDirectory(lengthControl);
var originalLengthProof = File.ReadAllText(Path.Combine(root, "ArrayLength", "ContractVariant.lean"));
var changedLengthProof = Path.Combine(lengthControl, "ChangedLength.lean");
File.WriteAllText(changedLengthProof, originalLengthProof.Replace("value = BitVec.ofNat 32 size",
    "value = value", StringComparison.Ordinal));
var weaker = verification.Verify(assembly, "Examples", lengthSelector, changedLengthProof, lengthControl,
    theorem: "VariantProof.correctness", statement: new(Term: true));
try
{
    verification.VerifyRefutation(nullLengthAssembly, "Examples", lengthSelector,
        Path.Combine(nullLength, "ContractVariant.lean"), Path.Combine(root, "MismatchedLength"), "scalar",
        "VariantProof.correctness", weaker.statementIdentity!.term!.Value.GetRawText());
    throw new InvalidOperationException("A changed array contract accepted the original counterexample predicate.");
}
catch (InvalidOperationException mismatch) when (mismatch.Message.Contains(
    "Verified statement does not match the requested contract", StringComparison.Ordinal))
{
    Console.WriteLine("PASS changing the proved array contract rejects its previous refutation");
}

// Each named field is checked against the operation it names, so a view with another offset, width or
// element fails its own theorem instead of naming storage the code never touches.
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution",
    "CIL.Safety.ObjectFields");
var forgedViews = new RejectedEvidence(root);
foreach (var (name, proof, view, forged, marker) in new[]
{
    ("offset", "LinkedNodes", "def Next : Safety.ReferenceField := ⟨type, 8⟩",
        "def Next : Safety.ReferenceField := ⟨type, 0⟩", "Safety.ReferenceField.accessedBy_of_shape Next false"),
    ("width", "LinkedNodes", "def Value : Safety.WordField 8 := ⟨type, 0⟩",
        "def Value : Safety.WordField 4 := ⟨type, 0⟩", "Safety.WordField.accessedBy_of_shape Value false"),
    ("element", "SampleValues", "def Values : Safety.ArrayField .signed32 := ⟨type, 0⟩",
        "def Values : Safety.ArrayField .unsigned32 := ⟨type, 0⟩",
        "Safety.ArrayField.accessedBy_of_shape Values false"),
    // A struct element's width is its layout's, so a view with another width fails its own theorem.
    ("structWidth", "TilePairs", "PublicKeyToken=null::Examples.AggregateArrays/Pair\" 16)",
        "PublicKeyToken=null::Examples.AggregateArrays/Pair\" 8)", "Safety.ArrayField.accessedBy_of_shape Pairs false")
})
{
    var extracted = File.ReadAllText(Path.Combine(root, proof, "Extracted.lean"));
    if (!extracted.Contains(view, StringComparison.Ordinal))
        throw new InvalidOperationException("The extraction does not name the field view: " + view);
    var path = Path.Combine(root, $"ForgedView-{name}.lean");
    File.WriteAllText(path, extracted.Replace(view, forged, StringComparison.Ordinal));
    forgedViews.Add(path, $"PASS forged field view rejected: {name}", "Application type mismatch", marker);
}
// Lean re-resolves every dispatch table entry from the catalog and requires every concrete class
// deriving from the slot's class, so a table that swaps bodies or omits a class fails its check.
var dispatched = File.ReadAllText(Path.Combine(root, "AnimalLegs", "Extracted.lean"));
var birdEntry = $"(.object \"{animalScope}\" \"Examples.Bird\", ";
var dogEntry = $"(.object \"{animalScope}\" \"Examples.Dog\", ";
var table = DispatchPatterns.Table.Match(dispatched).Value;
var entries = DispatchPatterns.Entry.Matches(table).Select(entry => entry.Groups).ToArray();
if (entries.Length != 2 || !table.Contains(birdEntry + entries[0][2].Value, StringComparison.Ordinal) ||
    !table.Contains(dogEntry + entries[1][2].Value, StringComparison.Ordinal))
    throw new InvalidOperationException("The extraction does not list Bird and Dog in its dispatch table: " + table);
foreach (var (name, forged) in new[]
{
    ("swapped", $".virtual [{birdEntry}{entries[1][2].Value}), {dogEntry}{entries[0][2].Value})]"),
    ("omitted", $".virtual [{dogEntry}{entries[1][2].Value})]")
})
{
    var path = Path.Combine(root, $"ForgedTable-{name}.lean");
    File.WriteAllText(path, dispatched.Replace(table, forged, StringComparison.Ordinal));
    forgedViews.Add(path, $"PASS forged dispatch table rejected: {name}",
        "Extraction.ConstrainedCallsValid method0DispatchTypes");
}
// Lean binds a type test to its raw opcode and class, so an emitted test of another class or with
// the other outcome for a failed cast fails the scalar flow check. The method is defined from its decoder, so
// the forgery edits the decoder's input and leaves the closed definition the check reads.
var cast = File.ReadAllText(Path.Combine(root, "DogCast", "Extracted.lean"));
var castTest = $"opcode := 116, operand := .type ({dogEntry.TrimStart('(').TrimEnd(',', ' ')})";
foreach (var (name, forged) in new[]
{
    ("class", castTest.Replace("Examples.Dog", "Examples.Bird", StringComparison.Ordinal)),
    ("outcome", castTest.Replace("opcode := 116", "opcode := 117", StringComparison.Ordinal))
})
{
    var path = Path.Combine(root, $"ForgedCast-{name}.lean");
    File.WriteAllText(path, ForgeDecodedOriginal(cast, 0, castTest, forged));
    forgedViews.Add(path, $"PASS forged type test rejected: {name}", "Extraction.ScalarFlowValid");
}
forgedViews.Check();

foreach (var mutation in new[]
{
    "abstract", "base", "baseRejected", "explicit", "finalizer", "interface", "byref", "address", "reference",
    "fieldType", "receiverAddress", "opaqueRead", "elementAddress", "arrayAddress", "objectArray",
    "interfaceArray", "objectArrayParameter", "matrixField"
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
        var arrays = module.GetType("Examples.NodeArrays");
        var tags = module.GetType("Examples.TagArrays");
        var create = tags.Methods.Single(candidate => candidate.Name == "Create");
        var allocation = create.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Newarr);
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
            case "elementAddress":
                var at = arrays.Methods.Single(candidate => candidate.Name == "At");
                var element = at.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Ldelem_Ref);
                var elements = at.Body.GetILProcessor();
                elements.InsertAfter(element, elements.Create(OpCodes.Ldind_Ref));
                elements.Replace(element, elements.Create(OpCodes.Ldelema, module.GetType("Examples.Node")));
                break;
            // An object or interface array may hold an interface array at run time, whose covariance check
            // the model cannot decide, so neither is an array of class references.
            case "objectArray": allocation.Operand = module.TypeSystem.Object; break;
            case "interfaceArray": allocation.Operand = module.GetType("Examples.ICounterValue"); break;
            case "objectArrayParameter":
                tags.Methods.Single(candidate => candidate.Name == "Put").Parameters[0].ParameterType =
                    new ArrayType(module.TypeSystem.Object);
                break;
            // A multi-dimensional array has a shape the field's slot cannot recover from its allocation.
            case "matrixField":
                module.GetType("Examples.Samples").Fields.Single().FieldType =
                    new ArrayType(module.TypeSystem.Int32, 2);
                break;
            case "arrayAddress":
                var count = arrays.Methods.Single(candidate => candidate.Name == "Count");
                var argument = count.Body.Instructions[0];
                var counter = count.Body.GetILProcessor();
                counter.InsertAfter(argument, counter.Create(OpCodes.Ldind_Ref));
                counter.Replace(argument, counter.Create(OpCodes.Ldarga_S, count.Parameters[0]));
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
                "Examples.Account::Owner\n  Only fields holding class instances, arrays of classes or " +
                "single-dimensional arrays of reference-free value types are modelled",
            "matrixField" => "Unsupported reference-typed field: System.Int32[,] " +
                "Examples.Samples::Values\n" +
                "  Only fields holding class instances, arrays of classes or single-dimensional arrays of " +
                "reference-free value types are modelled; System.Int32[,] is another array",
            "opaqueRead" => "callvirt requires an adjacent concrete constrained receiver",
            "objectArray" => "Unsupported instruction: IL_0001: newarr System.Object",
            "interfaceArray" => "Unsupported instruction: IL_0001: newarr Examples.ICounterValue",
            "objectArrayParameter" => "Unsupported array shape or element type: System.Object[]",
            "fieldType" => "Unsupported class instance field type: System.Double Examples.Account::Rate",
            "receiverAddress" =>
                "Unsupported address of a class instance receiver: System.UInt64 Examples.Account::get_Headroom()",
            "elementAddress" =>
                "Unsupported typed element access on an array of class references: ldelema Examples.Node",
            "arrayAddress" =>
                "Address of managed-reference or array-root argument is unsupported\n" +
                "  Method: System.Int32 Examples.NodeArrays::Count(Examples.Node[])",
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
        "objectArray" or "interfaceArray" => "TagArrays::Create(System.Int32)",
        "objectArrayParameter" => "TagArrays::Put(System.Object[],System.Int32,Examples.Tagged)",
        "elementAddress" => "NodeArrays::At(Examples.Node[],System.Int32)",
        "arrayAddress" => "NodeArrays::Count(Examples.Node[])",
        "matrixField" => "SampleArrays::ValuesOf(Examples.Samples)",
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
    "construction, base class field, class reference array, value-array field, virtual dispatch and type " +
    "test proofs, and named rejection of unmodelled class shapes, field and element accesses, calls, " +
    "dispatch tables and type tests");

// Two TypeDefs in the same module spell Rows.Widget. A single body tests both physical operands.
static void VerifyClassIdentity(Program verification, string assembly, string root)
{
    var output = Path.Combine(root, "ClassIdentity");
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var parent = new TypeDefinition("Rows", "Parent", TypeAttributes.Public, module.TypeSystem.Object);
        var qualified = new TypeDefinition("Rows", "Widget", TypeAttributes.Public, parent);
        var dotted = new TypeDefinition("", "Rows.Widget", TypeAttributes.Public, parent);
        module.Types.Add(parent);
        module.Types.Add(qualified);
        module.Types.Add(dotted);
        var test = new MethodDefinition("Classify", MethodAttributes.Public | MethodAttributes.Static,
            module.TypeSystem.Int32);
        test.Parameters.Add(new ParameterDefinition(parent));
        module.GetType("Examples.Arithmetic").Methods.Add(test);
        var il = test.Body.GetILProcessor();
        void EmitTest(TypeDefinition target)
        {
            il.Emit(OpCodes.Ldarg_0);
            il.Emit(OpCodes.Isinst, target);
            il.Emit(OpCodes.Ldnull);
            il.Emit(OpCodes.Cgt_Un);
        }
        EmitTest(qualified);
        il.Emit(OpCodes.Ldc_I4_2);
        il.Emit(OpCodes.Mul);
        EmitTest(dotted);
        il.Emit(OpCodes.Add);
        il.Emit(OpCodes.Ret);

        var rootCtor = new MethodReference(".ctor", module.TypeSystem.Void, module.TypeSystem.Object)
            { HasThis = true };
        MethodDefinition Constructor(TypeDefinition owner, MethodReference baseCtor)
        {
            var ctor = new MethodDefinition(".ctor", MethodAttributes.Public | MethodAttributes.HideBySig |
                MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void);
            owner.Methods.Add(ctor);
            var body = ctor.Body.GetILProcessor();
            body.Emit(OpCodes.Ldarg_0);
            body.Emit(OpCodes.Call, baseCtor);
            body.Emit(OpCodes.Ret);
            return ctor;
        }
        var parentCtor = Constructor(parent, rootCtor);
        var fresh = new MethodDefinition("ClassifyFresh", MethodAttributes.Public | MethodAttributes.Static,
            module.TypeSystem.Int32);
        test.DeclaringType.Methods.Add(fresh);
        var build = fresh.Body.GetILProcessor();
        build.Emit(OpCodes.Newobj, Constructor(qualified, parentCtor));
        build.Emit(OpCodes.Call, test);
        build.Emit(OpCodes.Ldc_I4_S, (sbyte)10);
        build.Emit(OpCodes.Mul);
        build.Emit(OpCodes.Newobj, Constructor(dotted, parentCtor));
        build.Emit(OpCodes.Call, test);
        build.Emit(OpCodes.Add);
        build.Emit(OpCodes.Ret);
        module.Write(dll);
    }
    var image = System.Reflection.Assembly.Load(File.ReadAllBytes(dll));
    var classify = image.GetType("Examples.Arithmetic", true)!.GetMethod("Classify")!;
    var candidates = image.GetTypes().Where(type => type.FullName == "Rows.Widget").ToArray();
    foreach (var (space, expected) in new[] { ("Rows", 2), ("", 1) })
    {
        var type = candidates.Single(type => (type.Namespace ?? "") == space);
        var instance = System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(type);
        if (!Equals(classify.Invoke(null, [instance]), expected))
            throw new InvalidOperationException($"CLR isinst selected the wrong TypeDef for {type.MetadataToken:x8}");
    }
    if (!Equals(classify.DeclaringType!.GetMethod("ClassifyFresh")!.Invoke(null, null), 21))
        throw new InvalidOperationException("CLR construction did not preserve both class identities");
    verification.Verify(dll, "Examples", "Arithmetic::Classify(Rows.Parent)",
        At("Tests/Objects/ClassIdentity.lean"), Path.Combine(output, "Proof"));
    verification.Verify(dll, "Examples", "Arithmetic::ClassifyFresh()",
        At("Tests/Objects/AllocatedClassIdentity.lean"), Path.Combine(output, "Fresh"));
    Console.WriteLine("PASS CLR and certified newobj and isinst for both Rows.Widget declarations");
}

static partial class DispatchPatterns
{
    [GeneratedRegex(@"\.virtual \[\(.*?\)\]")]
    internal static partial Regex Table { get; }

    [GeneratedRegex(@"(\(\.object [^)]*?, )(\d+)\)")]
    internal static partial Regex Entry { get; }
}
