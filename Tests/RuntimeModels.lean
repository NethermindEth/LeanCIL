import CIL.Safety.Execution
import CIL.Safety.StepComposition
import CIL.Safety.BoundaryStepRenaming
import CIL.Extraction.CallAgreement
import CIL.Extraction.DecodedDefinition
import CIL.Extraction.UnsafeCalls
import CIL.Extraction.KernelEquation
import CIL.ProfileEquivalence
import Tests.Support
import Tests.LoweredCallRefusal

/-!
# Runtime model tests

A typed static span runs in `memoryInstruction`, so a runtime model's memory operation needs no
static field metadata. Each runtime model runs as the instruction the extractor emits for its
call: `runModel` on a concrete stack equals `step` on that instruction, and the model observes
as many operands as the instruction does. A model table resolves typed method references, and
the agreement check ties each call site's emission to the model its reference stands for.
-/

namespace Tests.RuntimeModels
open CIL.Safety

/-- One readable 16-byte immutable static field at allocation 0, aligned to 8, whose bytes
    are all 7. -/
private def staticMemory : Memory := {
  allocations := fun id =>
    if id = 0 then some ⟨.immutableStatic, ⟨16, 8, []⟩, true, [16]⟩ else none
  cells := fun _ _ => ⟨7, true⟩
  views := [⟨0, 0, 16, true, false⟩]
  nextIdentity := 1 }

/-- A typed span over the whole field has one element per four bytes. -/
example : memoryInstruction (.createSpan 4) [.reference (.address ⟨0, 0⟩)] staticMemory =
    .ok (staticMemory, [.span (.address ⟨0, 0⟩) 4]) := rfl

/-- A method with no code, on the scalar profile. -/
private def body : CIL.Method := { code := [], locals := [], returnsValue := false }

private def frame : Frame := { activation := 0, locals := [], owned := [] }

/-- One writable 16-byte heap allocation at 0, aligned to 8, whose bytes are all 7. -/
private def heapMemory : Memory := {
  allocations := fun id =>
    if id = 0 then some ⟨.managedHeap, ⟨16, 8, []⟩, true, []⟩ else none
  cells := fun _ _ => ⟨7, true⟩
  views := [⟨0, 0, 16, true, true⟩]
  nextIdentity := 1 }

/-- The field's start and its fourth byte, as references. -/
private def start : Value := .reference (.address ⟨0, 0⟩)
private def fourth : Value := .reference (.address ⟨0, 4⟩)

-- Each model against the instruction emitted for its call today, on a stack it accepts.
example : runModel body (.intrinsic (.scalar (.rotateLeft 32)) 2) 3 frame
      [.scalar (.i32 1), .scalar (.i32 0x80000000)] staticMemory =
    step body (.intrinsic (.scalar (.rotateLeft 32)) 2) 3 [] frame
      [.scalar (.i32 1), .scalar (.i32 0x80000000)] staticMemory := rfl
example : runModel body (.memory (.createSpan 4)) 3 frame [start] staticMemory =
    step body (.memory (.createSpan 4)) 3 [] frame [start] staticMemory := rfl
example : runModel body (.feature .avx2) 3 frame [start] staticMemory =
    step body (.feature .avx2) 3 [] frame [start] staticMemory := rfl
example : runModel body (.constant 8) 3 frame [start] staticMemory =
    step body (.ldc_i4 8) 3 [] frame [start] staticMemory := rfl
example : runModel body (.referenceCompare .same) 3 frame [fourth, start] staticMemory =
    step body .ceq 3 [] frame [fourth, start] staticMemory := rfl
example : runModel body (.referenceCompare .less) 3 frame [fourth, start] staticMemory =
    step body .clt_un 3 [] frame [fourth, start] staticMemory := rfl
example : runModel body (.referenceCompare .greater) 3 frame [fourth, start] staticMemory =
    step body .cgt_un 3 [] frame [fourth, start] staticMemory := rfl
example : runModel body .referenceSubtract 3 frame [.scalar (.i32 4), fourth] staticMemory =
    step body .sub 3 [] frame [.scalar (.i32 4), fourth] staticMemory := rfl
example : runModel body (.typedTransfer (.scalar 4 false) false) 3 frame [start] staticMemory =
    step body (.loadScalar 4 false) 3 [] frame [start] staticMemory := rfl
example : runModel body .skipInit 3 frame [start] staticMemory =
    .ok (.next 4 [] frame staticMemory) := rfl
example : runModel body .objectConstructor 3 frame [.object .null] staticMemory =
    step body .pop 3 [] frame [.object .null] staticMemory := rfl

-- Every typed transfer family runs as its typed load or store.
example : runModel body (.typedTransfer (.scalar 4 false) true) 3 frame
      [.scalar (.i32 9), start] heapMemory =
    step body (.stind .i4) 3 [] frame [.scalar (.i32 9), start] heapMemory := rfl
example : runModel body (.typedTransfer (.snapshot (.aggregate 16)) false) 3 frame [start]
      heapMemory =
    .ok (.next 4 [.scalar (.aggregate (List.replicate 16 7))] frame heapMemory) := rfl
example : runModel body (.typedTransfer (.snapshot (.aggregate 16)) true) 3 frame
      [.scalar (.aggregate (List.replicate 16 1)), start] heapMemory =
    .ok (.next 4 [] frame ((write heapMemory ⟨0, 0⟩ (List.replicate 16 1) 1).toOption.getD
      Memory.empty)) := rfl
example : runModel body (.typedTransfer (.snapshot .vector128) false) 3 frame [start]
      heapMemory =
    step body (.memory .load128) 3 [] frame [start] heapMemory := rfl
example : runModel body (.typedTransfer (.snapshot .vector128) true) 3 frame
      [.scalar (.v128 5), start] heapMemory =
    step body (.memory .store128) 3 [] frame [.scalar (.v128 5), start] heapMemory := rfl

-- The equalities above compare successes, not two copies of one fault.
example : (runModel body (.intrinsic (.scalar (.rotateLeft 32)) 2) 3 frame
    [.scalar (.i32 1), .scalar (.i32 0x80000000)] staticMemory).toBool := rfl
example : (runModel body (.memory (.createSpan 4)) 3 frame [start] staticMemory).toBool := rfl
example : (runModel body (.referenceCompare .same) 3 frame [fourth, start]
    staticMemory).toBool := rfl
example : (runModel body (.referenceCompare .less) 3 frame [fourth, start]
    staticMemory).toBool := rfl
example : (runModel body (.referenceCompare .greater) 3 frame [fourth, start]
    staticMemory).toBool := rfl
example : (runModel body .referenceSubtract 3 frame [.scalar (.i32 4), fourth]
    staticMemory).toBool := rfl
example : (runModel body (.typedTransfer (.scalar 4 false) true) 3 frame
    [.scalar (.i32 9), start] heapMemory).toBool := rfl
example : (runModel body (.typedTransfer (.snapshot (.aggregate 16)) true) 3 frame
    [.scalar (.aggregate (List.replicate 16 1)), start] heapMemory).toBool := rfl
example : (runModel body (.typedTransfer (.snapshot .vector128) false) 3 frame [start]
    heapMemory).toBool := rfl
example : (runModel body (.typedTransfer (.snapshot .vector128) true) 3 frame
    [.scalar (.v128 5), start] heapMemory).toBool := rfl
example : (runModel body .skipInit 3 frame [start] staticMemory).toBool := rfl

-- A model faults where its instruction faults.
example : runModel body .objectConstructor 3 frame [] staticMemory =
    step body .pop 3 [] frame [] staticMemory := rfl
example : runModel body .skipInit 3 frame [.scalar (.i32 0)] staticMemory =
    .error (.unsupported "Not a memory instruction") := rfl

-- The model, unlike the opcode, takes only references: scalar operands are refused.
example : runModel body (.referenceCompare .same) 3 frame [.scalar (.i32 1), .scalar (.i32 1)]
    staticMemory = .error .invalidState := rfl
example : runModel body .referenceSubtract 3 frame [.scalar (.i32 4), .scalar (.i32 9)]
    staticMemory = .error .invalidState := rfl

-- Spans outside immutable static data, or with a native length, are refused.
example : memoryInstruction (.createSpan 4) [start] heapMemory =
    .error (.unsupported "Typed span outside a whole extracted static field") := rfl
example : memoryInstruction .spanCreate [.scalar (.i32 4), start] heapMemory =
    .error (.unsupported "Span pointer constructor outside extracted static data") := rfl
example : step body (.memory .spanCreate) 3 [] frame [.scalar (.i64 4), start] staticMemory =
    .error .invalidState := rfl

-- Guarded by its observer count, a model rejects unspecified bits as its instruction does.
example : observedCall (CIL.RuntimeModel.referenceCompare .same).observerCount
      [.scalar (.v128Low64 0), start]
      (fun _ => runModel body (.referenceCompare .same) 3 frame
        [.scalar (.v128Low64 0), start] staticMemory) =
    step body .ceq 3 [] frame [.scalar (.v128Low64 0), start] staticMemory := rfl

-- A memory model is its memory instruction, so a memory step equation steps a modelled call:
-- one success and the unspecified-bits fault, each reached through `modelStep_memory`.
example : modelStep (some (.memory .isNullRef)) body 3 frame [.reference .null] staticMemory =
    .ok (.next 4 [.scalar (.i32 1)] frame staticMemory) := by
  rw [modelStep_memory (args := [])]
  rfl
example : modelStep (some (.memory .isNullRef)) body 3 frame [.scalar (.v128Low64 0)]
      staticMemory =
    .error (.unsupported "Instruction observes unspecified vector bits") := by
  rw [modelStep_memory (args := [])]
  exact step_unspecified rfl

-- Each model observes the operands its emitted instruction observes.
example : (CIL.RuntimeModel.intrinsic (.scalar (.rotateLeft 32)) 2).observerCount =
    observerCount (.intrinsic (.scalar (.rotateLeft 32)) 2) := rfl
example : (CIL.RuntimeModel.memory (.createSpan 4)).observerCount =
    observerCount (.memory (.createSpan 4)) := rfl
example : (CIL.RuntimeModel.feature .avx2).observerCount = observerCount (.feature .avx2) := rfl
example : (CIL.RuntimeModel.constant 8).observerCount = observerCount (.ldc_i4 8) := rfl
example : (CIL.RuntimeModel.referenceCompare .less).observerCount = observerCount .clt_un := rfl
example : CIL.RuntimeModel.referenceSubtract.observerCount = observerCount .sub := rfl
example : (CIL.RuntimeModel.typedTransfer (.scalar 4 false) true).observerCount =
    observerCount (.stind .i4) := rfl
example : CIL.RuntimeModel.skipInit.observerCount = 1 := rfl
example : CIL.RuntimeModel.objectConstructor.observerCount = observerCount .pop := rfl

private def element : CIL.ArrayElement := .signed32

-- The memory operations only a call reaches, then the opcode meanings, blocks among them.
example : [CIL.MemoryOp.observeView .spanEmpty, .binaryRead 4 false false false,
    .binaryWrite 4 false false, .spanReinterpret 1 4 false, .spanCopy 1 false, .spanFill 1 false,
    .arrayFill element false, .bigMul64 false, .divRemOut 32, .vector128Unsafe false false,
    .asRef, .add 1 true, .byteOffset,
    .marshalRead (.scalar 4 false) false, .marshalWrite (.scalar 4 false) false,
    .pointerTransfer (.scalar 4 false) 4 false, .bitcastByteBool,
    .bitcastValue .vector128 .vector128, .spanCreate, .spanReference, .createSpan 4,
    .spanItem 4, .spanLength, .spanEmpty 4 false, .spanFromReference 4 false,
    .spanSingleReference 4 false, .spanSlice false, .spanReadOnly,
    .arraySpan element false .whole, .nullRef, .isNullRef, .throwIfNull,
    .zeroGuard .negative 32 true, .comparisonGuard .greaterThan 32 true].all
      CIL.MemoryOp.callReached := rfl
example : [CIL.MemoryOp.copyBlock 1, .initBlock 1, .load128, .load256, .load512, .store128,
    .store256, .store512, .stringLiteral ""].any
      CIL.MemoryOp.callReached = false := rfl


namespace Table
open CIL CIL.Extraction

private def runtimeType (name : String) : TypeExpr := .atom runtimeScope name
private def word : TypeExpr := runtimeType "System.UInt64"

/-- `Math.BigMul(UInt64, UInt64, out UInt64)` as a closed call site states it. -/
private def bigMul : MethodRef :=
  { owner := runtimeType "System.Math", name := name!"BigMul", hasThis := false,
    genericArity := 0, returnType := word, parameters := [word, word, .byref word] }

private def long : TypeExpr := runtimeType "System.Int64"

/-- `Math.DivRem(Int64, Int64, out Int64)`, whose model the table below does not hold. -/
private def divRem : MethodRef :=
  { bigMul with
    name := name!"DivRem", returnType := long, parameters := [long, long, .byref long] }

/-- The signed overload `Math.BigMul(Int64, Int64, out Int64)`, which the table does not model. -/
private def signedBigMul : MethodRef :=
  { bigMul with returnType := long, parameters := [long, long, .byref long] }

/-- `Span<element>.get_Length`. -/
private def spanLength (element : TypeExpr) : MethodRef :=
  { owner := .apply (.constructor runtimeScope "System.Span`1") element,
    name := name!"get_Length", hasThis := true, genericArity := 0,
    returnType := runtimeType "System.Int32", parameters := [] }

/-- `get_Length` of every span instance, an instance method of no parameters. -/
private def spanLengthEntry : ModelEntry :=
  .single .call (.constructor runtimeScope "System.Span`1") name!"get_Length"
    (.declaration (· == { convention := 0x20, returnType := runtimeType "System.Int32" }))
    (fun _ method =>
      if method.hasThis && method.parameters.isEmpty then some (.memory .spanLength) else none)

/-- BigMul by its exact reference, and `get_Length` of every span instance. -/
private def entries : List ModelEntry :=
  [ModelEntry.exact .call bigMul (bigMul.signature 0) (.memory (.bigMul64 false)), spanLengthEntry]

/-- The table of `entries`, accounting for the wide arithmetic and span length emissions. -/
private def catalog : ModelCatalog where
  table := model_table% entries

/-- A call or `newobj` of `method`. -/
private def site (method : MethodRef) (opcode : Nat := 40)
    (declared := method.signature (if method.hasThis then 0x20 else 0)) : RawInstruction :=
  ⟨0, opcode, .call {
    method, declared, target := .external "", typeArguments := [],
    parameterCount := method.parameters.length, returnsValue := true }⟩

-- The literal table is the balanced table of its entries.
example : catalog.table = ModelTable.ofEntries entries := rfl

-- A modelled call keeps its method, including when a memory operation implements its semantics.
example : catalog.siteAgrees {} {} (site bigMul) (.memory (.bigMul64 false)) = false := by
  decide +kernel
example : catalog.siteAgrees {} {} (site bigMul) (.memory (.divRemOut 64)) = false := by
  decide +kernel
-- A call keeps its operand; `ManagedCallsValid` decides whether a model or a link enters it.
example : catalog.siteAgrees {} {} (site bigMul) (.call bigMul) = true := by decide +kernel
example : catalog.siteAgrees {} {} (site bigMul) (.memory (.bigMul64 true)) = false := by
  decide +kernel

-- An entry reached by name, opcode and owner still refuses a reference its resolve rejects.
example : catalog.table.find {} .call signedBigMul = none := by decide +kernel
example : catalog.siteAgrees {} {} (site signedBigMul) (.memory (.bigMul64 false)) = false := by
  decide +kernel
example : catalog.table.find {} .call { spanLength word with hasThis := false } = none := by
  decide +kernel

/-- A missing raw claim rejects every live emission. -/
theorem unclaimedLiveRefused (models : ModelCatalog) (environment : LayoutEnvironment)
    (profile : FeatureProfile) (raw : RawInstruction) (emitted : CIL.Instruction)
    (called : methodTokenCall raw.opcode = true)
    (missing : siteClaim environment none raw models.table.claims = .refused) :
    models.siteAgrees environment profile raw emitted none true = false := by
  simp [ModelCatalog.siteAgrees, ModelCatalog.agreesAt,
    ModelCatalog.callRequirement, called, missing,
    CallRequirement.accepts]

#print axioms unclaimedLiveRefused

/-- A retained modelled direct call names the member of its raw operand. -/
theorem retainedModelNamesMember (models : ModelCatalog) (environment : LayoutEnvironment)
    (profile : FeatureProfile) (raw : RawInstruction) (member : CallSite)
    (target : MethodRef) (prefixes : CallPrefixes)
    (called : raw.opcode = 40) (operand : raw.operand = .call member)
    (model : siteClaim environment none raw models.table.claims = .model)
    (accepted : models.siteAgrees environment profile raw (.call target prefixes) = true) :
    target = member.method := by
  simp only [ModelCatalog.siteAgrees, ModelCatalog.agreesAt,
    ModelCatalog.callRequirement, callLayouts_environment, model, operand, called,
    methodTokenCall, callOpcode?, Bool.true_or, beq_self_eq_true, ite_true] at accepted
  split at accepted <;> simp_all [CallRequirement.accepts]

#print axioms retainedModelNamesMember

-- An entry filed under another name's key is not selected for that name.
/-- A tree that files the span length entry under the key of `get_IsEmpty`. -/
private def misfiled : ModelTable := .node .leaf (name!"get_IsEmpty").code [spanLengthEntry] .leaf
private def spanIsEmpty : MethodRef :=
  { spanLength word with name := name!"get_IsEmpty", returnType := runtimeType "System.Boolean" }
example : misfiled.find {} .call spanIsEmpty = none := by decide +kernel

-- An unlinked call without a named family has no resolved instruction.
example : catalog.siteAgrees {} {} (site divRem) (.call divRem) = false := by decide +kernel
example : catalog.siteAgrees {} {} (site divRem) (.memory (.divRemOut 64)) = false := by
  decide +kernel

-- The opcode and the owner are part of the key; a generic owner matches by its head.
example : catalog.table.find {} .newobj bigMul = none := by decide +kernel
example : catalog.table.find {} .call { bigMul with owner := runtimeType "System.Maths" } =
    none := by decide +kernel
example : catalog.siteAgrees {} {} (site (spanLength word)) (.memory .spanLength) = false := by
  decide +kernel
example : catalog.table.find {} .call
    { spanLength word with owner := runtimeType "System.String" } = none := by decide +kernel
example : catalog.siteAgrees {} {} (site (spanLength (runtimeType "System.Byte")))
    (.memory .spanLength) = false := by decide +kernel
example : catalog.siteAgrees {} {} (site bigMul 115) (.memory (.bigMul64 false)) = false := by
  decide +kernel

/-- A method whose only instruction is `instruction`. -/
private def method (instruction : RawInstruction) : RawMethod :=
  { token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
    attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
    initLocals := true, maxStack := 3, genericParameters := [], code := [instruction] }

-- A dead method-token call carries the raw opcode in its hole.
example : ModelsAgree catalog {} {} (method (site bigMul)) [false] [.unadmitted 40] := by
  decide +kernel
example : ¬ ModelsAgree catalog {} {} (method (site bigMul)) [false] [.unadmitted 115] := by
  decide +kernel
example : ¬ ModelsAgree catalog {} {} (method (site bigMul)) [true] [.memory (.divRemOut 64)] := by
  decide +kernel

-- Two entries for one slot are refused when the table is built.
/-- error: model table: two entries share an opcode, owner and name -/
#guard_msgs in
example : ModelTable :=
  model_table% [ModelEntry.exact .call bigMul (bigMul.signature 0) (.memory (.bigMul64 false)),
    ModelEntry.exact .call bigMul (bigMul.signature 0) (.memory (.bigMul64 true))]

/-- A multiply member outside the runtime owner has no model. -/
private def unknown := { bigMul with owner := .atom "Fixture" "System.Math" }

-- The runtime table distinguishes the exact constructor and wide multiplication calls.
example : runtimeModel {} .call objectConstructorMethod = some .objectConstructor := by
  decide +kernel
example : runtimeModel {} .call bigMul = some (.memory (.bigMul64 false)) := by decide +kernel
example : runtimeModel {} .newobj objectConstructorMethod = none := by decide +kernel
example : runtimeModel {} .call
    { objectConstructorMethod with owner := .atom "Fixture" "System.Object" } = none := by
  decide +kernel
/-- `System.Object` as another assembly declares it. -/
private def coreObject : TypeExpr := .atom "System.Private.CoreLib" "System.Object"
example : runtimeModel {} .call { objectConstructorMethod with owner := coreObject } = none := by
  decide +kernel
example : runtimeModel {} .call { objectConstructorMethod with hasThis := false } = none := by
  decide +kernel
example : runtimeModel {} .call { objectConstructorMethod with parameters := [word] } = none := by
  decide +kernel
example : RuntimeModelsAgree (method (site unknown)) [true]
    { body with code := [.call (Tests.callee 3) {}], links := [(0, .direct 7)] } := by
  decide +kernel
example : ¬ RuntimeModelsAgree (method
    (site bigMul)) [true]
    { body with code := [.call (Tests.callee 3) {}], links := [(0, .direct 7)] } := by
  decide +kernel

-- An entry filed under `newobj` does not model a `call` of its method.
example : ModelTable.find
    (model_table% [ModelEntry.exact .newobj objectConstructorMethod
      { convention := 0x20 } .objectConstructor])
    {} .call objectConstructorMethod = none := by decide +kernel

/-- A body whose only instruction is `emitted`, with the link table `links`. -/
private def emitting (emitted : CIL.Instruction) (links : List (Nat × CIL.Link)) : CIL.Method :=
  { body with code := [emitted], links }

-- A model site keeps its call and states no link; a link there, or another emission, is refused.
example :
    ManagedCallsValid [] [] (callModelled body) (method (site objectConstructorMethod)) [true]
    (emitting (.call objectConstructorMethod {}) []) := by decide +kernel
example : ¬ ManagedCallsValid [⟨[], method (site bigMul)⟩] [] (callModelled body)
    (method (site objectConstructorMethod)) [true]
    (emitting (.call objectConstructorMethod {}) [(0, .direct 0)]) := by decide +kernel
example : ¬ ManagedCallsValid [] [] (callModelled body) (method (site objectConstructorMethod))
    [true] (emitting .pop []) := by decide +kernel
example : ¬ RuntimeModelsAgree (method (site objectConstructorMethod)) [true]
    (emitting .nop []) := by decide +kernel
example : ¬ ManagedCallsValid [] [] (callModelled body) (method (site objectConstructorMethod))
    [true] (emitting (.call objectConstructorMethod { tail := true }) []) := by decide +kernel
example : ¬ ManagedCallsValid [] [] (callModelled body) (method (site objectConstructorMethod))
    [true] (emitting (.call bigMul {}) []) := by decide +kernel

example : ¬ ManagedCallsValid [] [] (callModelled body) (method ⟨0, 40, .call {
      method := objectConstructorMethod, declared := { convention := 0x20 },
      target := .managed 0, typeArguments := [],
      parameterCount := 0, returnsValue := false }⟩) [true]
    (emitting (.call objectConstructorMethod {}) []) := by decide +kernel

/-- `Span<int>(ref int)`, a construction the runtime table models. -/
private def spanReference : MethodRef :=
  let int := runtimeType "System.Int32"
  { owner := .apply (.constructor runtimeScope "System.Span`1") int, name := name!".ctor",
    hasThis := true, genericArity := 0, returnType := .void, parameters := [.byref int] }

/-- The linked call rule at a `newobj` of `spanReference` with the given link. -/
private def constructionFits (live : Bool) (link : Option CIL.Link) : Bool :=
  validateLinkedCallWith (callModelled body) 1 (fun _ => none) (fun _ => none)
    (site spanReference 115) live link (.newobj spanReference)

-- A modelled construction keeps its newobj without a link. A link there is refused, live or dead,
-- so a forged link cannot make the construction enter a callee body.
example : callModelled body (.newobj, spanReference) ∧ constructionFits true none ∧
    constructionFits false none := by decide +kernel
example : [CIL.Link.aggregate 0 8, .object 0 [] 8, .direct 0].all fun link =>
    !constructionFits true (some link) && !constructionFits false (some link) := by decide +kernel

-- `pop` stands for no model, so a model site does not emit it, and no call site of any opcode
-- emits it, since it would drop the call.
example :
    ¬ RuntimeModelsAgree (method (site objectConstructorMethod)) [true] (emitting .pop []) := by
  decide +kernel
example : callEmitsNoPop (site objectConstructorMethod) .pop = false := by decide
example : callEmitsNoPop (site bigMul) .pop = false := by decide
example :
    callEmitsNoPop (site { objectConstructorMethod with hasThis := false } 111) .pop = false := by
  decide
example : callEmitsNoPop (site bigMul 115) .pop = false := by decide
example : callEmitsNoPop ⟨0, 38, .none⟩ .pop = true := by decide
example :
    callEmitsNoPop (site objectConstructorMethod) (.call objectConstructorMethod {}) = true := by
  decide
-- The method check applies the rule: a live call emitting `pop` fails it, the same call emitting
-- its call passes, and a raw `pop` still emits `pop`.
example : ¬ UnsafeCallsValid (method (site bigMul)) [true] [.pop] := by decide +kernel
example : UnsafeCallsValid (method (site bigMul)) [true] [.call bigMul {}] := by decide +kernel
example : ¬ UnsafeCallsValid (method (site objectConstructorMethod)) [true] [.pop] := by
  decide +kernel
example : UnsafeCallsValid (method ⟨0, 38, .none⟩) [true] [.pop] := by decide +kernel

-- An external call the table does not model needs a link.
example : ¬ ManagedCallsValid [] [] (callModelled body) (method (site unknown)) [true]
    (emitting (.call unknown {}) []) := by decide +kernel

-- The integer helpers of `System.Math` and of each integer type.
private def int : TypeExpr := runtimeType "System.Int32"
private def mathOwner : TypeExpr := runtimeType "System.Math"

/-- `owner::name` taking `arity` values of `type` and returning `result`. -/
private def helper (name : MetadataName) (type : TypeExpr) (arity : Nat)
    (result : TypeExpr := type) (owner : TypeExpr := mathOwner) : MethodRef :=
  { owner, name, hasThis := false, genericArity := 0, returnType := result,
    parameters := List.replicate arity type }

private def mathMin : MethodRef := helper name!"Min" int 2
private def mathMax : MethodRef := helper name!"Max" int 2
private def mathClamp : MethodRef := helper name!"Clamp" int 3
private def mathAbs : MethodRef := helper name!"Abs" int 1
private def mathSign : MethodRef := helper name!"Sign" (runtimeType "System.Int64") 1 int

-- Each helper resolves to its scalar intrinsic at the width and signedness of its type.
example : runtimeModel {} .call mathMin = some (.intrinsic (.scalar (.math .min 32 true)) 2) := by
  decide +kernel
example : runtimeModel {} .call mathMax = some (.intrinsic (.scalar (.math .max 32 true)) 2) := by
  decide +kernel
example : runtimeModel {} .call mathClamp =
    some (.intrinsic (.scalar (.math .clamp 32 true)) 3) := by decide +kernel
example : runtimeModel {} .call mathAbs = some (.intrinsic (.scalar (.math .abs 32 true)) 1) := by
  decide +kernel
example : runtimeModel {} .call mathSign =
    some (.intrinsic (.scalar (.math .sign 64 true)) 1) := by decide +kernel
example : runtimeModel {} .call (helper name!"Min" word 2) =
    some (.intrinsic (.scalar (.math .min 64 false)) 2) := by decide +kernel
example : runtimeModel {} .call (helper name!"Max" (runtimeType "System.IntPtr") 2) =
    some (.intrinsic (.scalar (.math .max 64 true)) 2) := by decide +kernel
example : runtimeModel {} .call (helper name!"Max" (runtimeType "System.Byte") 2) =
    some (.intrinsic (.scalar (.math .max 8 false)) 2) := by decide +kernel
-- The integer type that declares a helper is modelled like `System.Math`.
example : runtimeModel {} .call (helper name!"Max" int 2 (owner := int)) =
    some (.intrinsic (.scalar (.math .max 32 true)) 2) := by decide +kernel

-- A receiver, a generic arity or method argument, a wrong arity, mixed or unmodelled types, a
-- wrong result, an unsigned `Abs`, or another owner, assembly or opcode has no model.
example : runtimeModel {} .call { mathMax with hasThis := true } = none := by decide +kernel
example : runtimeModel {} .call { mathMax with genericArity := 1 } = none := by decide +kernel
example : runtimeModel {} .call { mathMax with methodArguments := [int] } = none := by
  decide +kernel
example : runtimeModel {} .call (helper name!"Max" int 3) = none := by decide +kernel
example : runtimeModel {} .call (helper name!"Abs" int 2) = none := by decide +kernel
example : runtimeModel {} .call { mathMax with parameters := [int, runtimeType "System.Int64"] } =
    none := by decide +kernel
example : runtimeModel {} .call (helper name!"Max" (runtimeType "System.Boolean") 2) = none := by
  decide +kernel
example : runtimeModel {} .call (helper name!"Max" (.atom "Fixture" "System.Int32") 2) = none := by
  decide +kernel
example : runtimeModel {} .call { mathMax with returnType := runtimeType "System.Int64" } =
    none := by decide +kernel
example : runtimeModel {} .call (helper name!"Sign" int 1) = some
    (.intrinsic (.scalar (.math .sign 32 true)) 1) := by decide +kernel
example : runtimeModel {} .call (helper name!"Sign" (runtimeType "System.Int16") 1) = none := by
  decide +kernel
example : runtimeModel {} .call (helper name!"Abs" word 1) = none := by decide +kernel
example : runtimeModel {} .call (helper name!"Abs" word 1 (owner := word)) = none := by
  decide +kernel
example : runtimeModel {} .call (helper name!"Max" int 2 (owner := runtimeType "System.Int64")) =
    none := by decide +kernel
example : runtimeModel {} .call
    (helper name!"Max" int 2 (owner := .atom "Fixture" "System.Math")) = none := by decide +kernel
example : runtimeModel {} .call
    (helper name!"Max" int 2 (owner := .atom "System.Private.CoreLib" "System.Math")) = none := by
  decide +kernel
example : runtimeModel {} .call (helper name!"Max" int 2 (owner := runtimeType "System.Maths")) =
    none := by decide +kernel
example : runtimeModel {} .newobj mathMax = none := by decide +kernel

-- A helper site keeps its call; the lowered intrinsic is refused there, and a call or intrinsic
-- of another helper is refused where the site calls `Min`, which a table without the helpers
-- accepted.
private def maxLowered : CIL.Instruction := .intrinsic (.scalar (.math .max 32 true)) 2
example : RuntimeModelsAgree (method (site mathMax)) [true] (emitting (.call mathMax {}) []) := by
  decide +kernel
example : ¬ RuntimeModelsAgree (method (site mathMax)) [true] (emitting maxLowered []) := by
  decide +kernel
example : ¬ RuntimeModelsAgree (method (site mathMin)) [true] (emitting maxLowered []) := by
  decide +kernel
example : ¬ ModelsAgree { table := model_table% [objectConstructorEntry] }
    {} {} (method (site mathMin)) [true] [maxLowered] := by decide +kernel
example : ManagedCallsValid [] [] (callModelled body) (method (site mathMin)) [true]
    (emitting (.call mathMin {}) []) := by decide +kernel
example : ¬ ManagedCallsValid [] [] (callModelled body) (method (site mathMin)) [true]
    (emitting (.call mathMax {}) []) := by decide +kernel
example : ¬ ManagedCallsValid [] [] (callModelled body) (method (site mathMin)) [true]
    (emitting (.call mathMin {}) [(0, .direct 0)]) := by decide +kernel

-- A modelled intrinsic must be available in the method's profile: an AVX2 entry is refused at a
-- site whose profile lacks AVX2 and accepted where it has it.
/-- `Avx2.And` on two 256-bit vectors, which a table below models. -/
private def avx2And : MethodRef :=
  { owner := runtimeType "System.Runtime.Intrinsics.X86.Avx2", name := name!"And",
    hasThis := false, genericArity := 0, returnType := word, parameters := [word, word] }
private def avx2Catalog : ModelCatalog :=
  { table := model_table% [ModelEntry.exact .call avx2And (avx2And.signature 0)
      (.intrinsic (.avx2 .band) 2)] }
example : avx2Catalog.siteAgrees {} {} (site avx2And) (.call avx2And {}) = false := by
  decide +kernel
example : avx2Catalog.siteAgrees {} { avx2 := true } (site avx2And) (.call avx2And {}) = true := by
  decide +kernel

/-- A linked pc must also satisfy the profile requirements of its resolved model. -/
theorem linkedProfileRequired :
    avx2Catalog.siteAgrees {} {} (site avx2And) (.call avx2And {}) (some (.direct 0))
      true = false := by decide +kernel

#print axioms linkedProfileRequired

-- The profile query of a call is its model's: the helpers read no flag, so every two profiles
-- agree on a program that calls one.
/-- A method that returns `Math.Max` of its two arguments. -/
private def maxProgram : CIL.Program :=
  [{ body with code := [.ldarg 0, .ldarg 1, .call mathMax {}, .ret], returnsValue := true }]
example : CIL.Program.profileReads maxProgram = [] := by decide +kernel
example : CIL.Program.ProfileAgreement maxProgram {} { avx2 := true } :=
  CIL.Program.ProfileAgreement.of_flags _ _ _ (by decide +kernel)

-- Each vector helper resolves to its intrinsic.
example : runtimeModel {} .call createScalarUnsafeMethod =
    some (.intrinsic (.vector .createScalarUnsafe64) 1) := by decide +kernel
example : runtimeModel {} .call getElement128Method =
    some (.intrinsic (.vector (.extract64 128)) 2) := by decide +kernel
example : runtimeModel {} .call getElement256Method =
    some (.intrinsic (.vector (.extract64 256)) 2) := by decide +kernel

-- A receiver, another generic arity, method argument, element type, vector width, arity or
-- result, or another assembly or opcode has no model.
/-- `Vector128<ulong>` and `Vector256<ulong>`. -/
private def vector128 : TypeExpr := ulongVectorOf "System.Runtime.Intrinsics.Vector128`1"
private def vector256 : TypeExpr := ulongVectorOf "System.Runtime.Intrinsics.Vector256`1"
example : runtimeModel {} .call { createScalarUnsafeMethod with hasThis := true } = none := by
  decide +kernel
example : runtimeModel {} .call { createScalarUnsafeMethod with parameters := [int] } = none := by
  decide +kernel
example : runtimeModel {} .call { createScalarUnsafeMethod with returnType := vector256 } =
    none := by decide +kernel
example : runtimeModel {} .call { getElement128Method with genericArity := 0 } = none := by
  decide +kernel
example : runtimeModel {} .call { getElement128Method with methodArguments := [int] } = none := by
  decide +kernel
example : runtimeModel {} .call { getElement128Method with parameters := [vector256, int] } =
    none := by decide +kernel
example : runtimeModel {} .call { getElement128Method with parameters := [vector128] } = none := by
  decide +kernel
example : runtimeModel {} .call { getElement128Method with returnType := int } = none := by
  decide +kernel
example : runtimeModel {} .call
    { getElement128Method with owner := runtimeType "System.Runtime.Intrinsics.Vector128" } =
    none := by decide +kernel
example : runtimeModel {} .call { getElement128Method with owner := getElement256Method.owner } =
    none := by decide +kernel
example : runtimeModel {} .call
    { createScalarUnsafeMethod with owner := getElement256Method.owner } = none := by
  decide +kernel
example : runtimeModel {} .call
    { createScalarUnsafeMethod with owner := runtimeType "System.Runtime.Intrinsics.Vector128" } =
    none := by decide +kernel
example : runtimeModel {} .newobj createScalarUnsafeMethod = none := by decide +kernel

/-- A call of the generic lane reader with its member declaration. -/
private def laneSite := site getElement128Method 40
  (getElementSignature "System.Runtime.Intrinsics.Vector128`1")

/-- A call of the 256-bit lane reader with its member declaration. -/
private def lane256Site := site getElement256Method 40
  (getElementSignature "System.Runtime.Intrinsics.Vector256`1")

/-- Whether the model accepts a kept call with this member declaration. -/
private def accepts (method : MethodRef) (declared : OpenSignature) : Bool :=
  runtimeCatalog.siteAgrees {} {} (site method 40 declared) (.call method {})

/-- Changing the convention alone invalidates each member declaration. -/
private def refusesConventions (method : MethodRef) (signature : OpenSignature) : Bool :=
  [0x40, 0x60, 0x01].all fun convention => !accepts method { signature with convention }

example : refusesConventions objectConstructorMethod { convention := 0x20 } := by decide +kernel
example : refusesConventions mathMin (mathMin.signature 0) := by decide +kernel
example : refusesConventions getElement128Method
    (getElementSignature "System.Runtime.Intrinsics.Vector128`1") := by decide +kernel
example : refusesConventions createScalarUnsafeMethod (createScalarUnsafeMethod.signature 0) := by
  decide +kernel

/-- The decision after the caller specializes a member whose return is its type variable. -/
private def specializedCall (catalog : ModelCatalog) (reference : MethodRef) : Option Bool := do
  let openRef := { reference with returnType := .parameter 0 }
  let operand := (site openRef 40 (openRef.signature 0)).operand
  let .call closed ← substituteOperand [reference.returnType] [] 1 operand | none
  pure (catalog.siteAgrees {} {} ⟨0, 40, .call closed⟩ (.call closed.method {}))

example : specializedCall runtimeCatalog mathMin = some false := by decide +kernel
example : specializedCall catalog bigMul = some false := by decide +kernel
example : accepts getElement128Method { getElementSignature "System.Runtime.Intrinsics.Vector128`1"
    with returnType := word } = false := by decide +kernel
example : catalog.siteAgrees {} {} (site bigMul 40
    { bigMul.signature 0 with returnType := .parameter 0 }) (.memory (.bigMul64 false)) = false :=
  by decide +kernel

-- A vector helper site keeps its call; the intrinsic it was lowered to is refused there, which a
-- table without the helpers accepted.
private def extractLowered : CIL.Instruction := .intrinsic (.vector (.extract64 128)) 2
private def createLowered : CIL.Instruction := .intrinsic (.vector .createScalarUnsafe64) 1
example : RuntimeModelsAgree (method laneSite) [true]
    (emitting (.call getElement128Method {}) []) := by decide +kernel
example : ¬ RuntimeModelsAgree (method laneSite) [true]
    (emitting extractLowered []) := by decide +kernel
example : ¬ ModelsAgree { table := model_table% [objectConstructorEntry] }
    {} {} (method laneSite) [true] [extractLowered] := by decide +kernel
example : ¬ RuntimeModelsAgree (method (site createScalarUnsafeMethod)) [true]
    (emitting createLowered []) := by decide +kernel
example : ¬ ModelsAgree { table := model_table% [objectConstructorEntry] }
    {} {} (method (site createScalarUnsafeMethod)) [true] [createLowered] := by decide +kernel
/-- Keeping a valid 256-bit call still requires its own generic member declaration. -/
example : ¬ RuntimeModelsAgree (method (site getElement256Method 40
    { getElementSignature "System.Runtime.Intrinsics.Vector256`1" with returnType := word }))
    [true] (emitting (.call getElement256Method {}) []) := by decide +kernel

example : ManagedCallsValid [] [] (callModelled body) (method lane256Site) [true]
    (emitting (.call getElement256Method {}) []) := by decide +kernel
example : ¬ ManagedCallsValid [] [] (callModelled body) (method lane256Site) [true]
    (emitting (.call getElement256Method {}) [(0, .direct 0)]) := by decide +kernel

end Table

/-- The receiver an object constructor call consumes. -/
private def receiver : Value := .object (.address ⟨0, 0⟩)

/-- A call of the `System.Object` constructor at a pc with no link steps as `pop` does. -/
example : step { body with code := [.call CIL.Extraction.objectConstructorMethod {}] }
    (.call CIL.Extraction.objectConstructorMethod {}) 0 [] frame [receiver] heapMemory =
      step body .pop 0 [] frame [receiver] heapMemory := by
  rfl

/-- The method loads its arguments, executes one unlinked runtime call and returns. -/
private def invokeCall (method : CIL.Extraction.MethodRef) (args : List Value)
    (returnsValue : Bool) : Except LocatedFault (List Value) :=
  let loads := (List.range args.length).map CIL.Instruction.ldarg
  let wrapper := { body with code := loads ++ [.call method {}, .ret], returnsValue }
  (invoke [wrapper] 8 0 args Tests.caller).map Prod.snd

example : invokeCall CIL.Extraction.objectConstructorMethod [.object .null] false =
    .ok [] := by rfl

example : invokeCall Table.mathMin [.scalar (.i32 3), .scalar (.i32 1)] true =
    .ok [.scalar (.i32 1)] := by rfl

example : invokeCall (Table.spanLength Table.word) [.span (.address ⟨0, 0⟩) 1] true =
    .ok [.scalar (.i32 1)] := by rfl

example : invokeCall Table.divRem [.scalar (.i64 7), .scalar (.i64 3), Tests.reference] true =
    .ok [.scalar (.i64 2)] := by rfl

example : invokeCall Table.divRem [.scalar (.i64 7), .scalar (.i64 0), Tests.reference] true =
    .error ⟨0, 3, .arithmetic .divideByZero⟩ := by decide

/-- The null guard accepts an object and its parameter name. -/
private def nullGuard : CIL.Extraction.MethodRef :=
  { owner := Table.runtimeType "System.ArgumentNullException", name := name!"ThrowIfNull",
    hasThis := false, genericArity := 0, returnType := .void,
    parameters := [Table.runtimeType "System.Object", .object CIL.Extraction.runtimeScope
      "System.String"] }

example : invokeCall nullGuard [.object .null, .object .null] false =
    .error ⟨0, 2, .thrown .argumentNull⟩ := by rfl

namespace ClosedMembers
open CIL CIL.Extraction

/-- The fixture has no aggregate layout rows. -/
private def layouts : LayoutEnvironment := {}

/-- Each wrapper loads the member's arguments, calls it without a link, and returns its result. -/
private def wrapper (profile : FeatureProfile) (environment : LayoutEnvironment)
    (member : MethodRef) : Option Method :=
  let count := member.parameters.length + member.hasThis.toNat
  let code := (List.range count).map Instruction.ldarg ++ [.call member {}, .ret]
  let returnsValue := member.returnType != .void
  some { body with profile, environment, code, returnsValue }

/-- The scalar invocation exposes either the returned values or the located fault. -/
private def run (method : Method) (args : List Safety.Value) (memory := Tests.caller) :=
  (Safety.invoke [method] 8 0 args memory).map Prod.snd

/-- The closed signature supplies the static member's parameters and method type arguments. -/
private def member (owner : TypeExpr) (name : MetadataName) (result : TypeExpr)
    (parameters : List TypeExpr := []) (arguments : List TypeExpr := []) : MethodRef :=
  { owner, name, hasThis := false, genericArity := arguments.length,
    returnType := result, parameters, methodArguments := arguments }

/-- The scalar element in the generic memory helpers is a runtime byte. -/
private def byte := TypeExpr.atom runtimeScope "System.Byte"

/-- The byte spans carry the closed element type in their return or parameter signature. -/
private def span (writable : Bool) := TypeExpr.apply (spanHead writable) byte

/-- The runtime helpers share the same static owner. -/
private def helpers := TypeExpr.atom runtimeScope "System.Runtime.CompilerServices.RuntimeHelpers"

cil_decoded_method platformBody := wrapper FeatureProfile.scalar layouts
  (member (.atom intrinsicsScope "System.Runtime.Intrinsics.X86.Avx2") name!"get_IsSupported"
    booleanType)

/-- The scalar profile reports AVX2 as unavailable. -/
theorem platform_result : run platformBody [] =
    .ok [.scalar (.i32 0)] := rfl

#print axioms platform_result

cil_decoded_method binaryReadBody := wrapper FeatureProfile.scalar layouts
  (member (.atom spanMemoryScope "System.Buffers.Binary.BinaryPrimitives")
    name!"ReadInt16BigEndian" (.atom runtimeScope "System.Int16") [span false])

/-- Reading the two static bytes as a big-endian Int16 gives 0x0707. -/
theorem binaryRead_result :
    run binaryReadBody [.bufferSpan ⟨.address ⟨0, 0⟩, 2, 1, false⟩] staticMemory =
    .ok [.scalar (.i32 1799)] := rfl

#print axioms binaryRead_result

cil_decoded_method vectorLaneBody := wrapper FeatureProfile.scalar layouts
  getElement128Method

/-- The vector helper reads the initialized low lane. -/
theorem vectorLane_result : run vectorLaneBody [.scalar (.v128Low64 7), .scalar (.i32 0)] =
    .ok [.scalar (.i64 7)] := rfl

#print axioms vectorLane_result

cil_decoded_method vectorBroadcastBody := wrapper FeatureProfile.scalar layouts
  broadcast256Method

/-- Broadcasting the word places it in all four lanes. -/
theorem vectorBroadcast_result : run vectorBroadcastBody [.scalar (.i64 3)] =
    .ok [.scalar (.v256 (CIL.Vector.pack256 3 3 3 3))] := rfl

#print axioms vectorBroadcast_result

cil_decoded_method populationBody := wrapper FeatureProfile.scalar layouts
  (member (.atom runtimeScope "System.Numerics.BitOperations") name!"PopCount" int32Type
    [Table.word])

/-- The population count of seven is three. -/
theorem population_result : run populationBody [.scalar (.i64 7)] =
    .ok [.scalar (.i32 3)] := rfl

#print axioms population_result

cil_decoded_method asSpanBody := wrapper FeatureProfile.scalar layouts
  (member (.atom spanMemoryScope "System.MemoryExtensions") name!"AsSpan" (span true)
    [.array byte] [byte])

/-- The whole-array extension returns an empty writable span for a null array. -/
theorem asSpan_result : run asSpanBody [.object .null] =
    .ok [.bufferSpan ⟨.null, 0, 1, true⟩] := rfl

#print axioms asSpan_result

cil_decoded_method fillArrayBody := wrapper FeatureProfile.scalar layouts
  (member (.atom runtimeScope "System.Array") name!"Fill" .void [.array byte, byte] [byte])

/-- Filling a null array faults at the call. -/
theorem fillArray_result : run fillArrayBody [.object .null, .scalar (.i32 7)] =
    .error ⟨0, 2, .thrown .argumentNull⟩ := rfl

#print axioms fillArray_result

cil_decoded_method staticSpanBody := wrapper FeatureProfile.scalar layouts
  (member helpers name!"CreateSpan" (span false) [.atom runtimeScope "System.RuntimeFieldHandle"]
    [byte])

/-- The field handle exposes sixteen static bytes. -/
theorem staticSpan_result : run staticSpanBody [Tests.reference] staticMemory =
    .ok [.span (.address ⟨0, 0⟩) 16] := rfl

#print axioms staticSpan_result

cil_decoded_method guardNullBody := wrapper FeatureProfile.scalar layouts
  nullGuard

/-- The decoded guard reports the null argument at the call. -/
theorem guardNull_result : run guardNullBody [.object .null, .object .null] =
    .error ⟨0, 2, .thrown .argumentNull⟩ := rfl

#print axioms guardNull_result

cil_decoded_method spanLengthBody := wrapper FeatureProfile.scalar layouts
  (Table.spanLength Table.word)

/-- The span getter returns the element count. -/
theorem spanLength_result : run spanLengthBody [.span (.address ⟨0, 0⟩) 2] =
    .ok [.scalar (.i32 2)] := rfl

#print axioms spanLength_result

cil_decoded_method referenceContentBody := wrapper FeatureProfile.scalar layouts
  (member helpers name!"IsReferenceOrContainsReferences" booleanType [] [byte])

/-- A byte contains no managed references. -/
theorem referenceContent_result : run referenceContentBody [] =
    .ok [.scalar (.i32 0)] := rfl

#print axioms referenceContent_result

cil_decoded_method marshalReferenceBody := wrapper FeatureProfile.scalar layouts
  (member (.atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal") name!"GetReference"
    (.byref byte) [span true] [byte])

/-- The marshal helper returns the start of the span. -/
theorem marshalReference_result :
    run marshalReferenceBody [.bufferSpan ⟨.address ⟨0, 0⟩, 1, 1, true⟩] =
    .ok [Tests.reference] := rfl

#print axioms marshalReference_result

cil_decoded_method sizeOfBody := wrapper FeatureProfile.scalar layouts
  (member unsafeOwner name!"SizeOf" int32Type [] [byte])

/-- A byte occupies one byte. -/
theorem sizeOf_result : run sizeOfBody [] =
    .ok [.scalar (.i32 1)] := rfl

#print axioms sizeOf_result

cil_decoded_method reinterpretBody := wrapper FeatureProfile.scalar layouts
  (member unsafeOwner name!"As" (.byref byte) [.byref byte] [byte, byte])

/-- Reinterpreting a byte reference preserves its address. -/
theorem reinterpret_result : run reinterpretBody [Tests.reference] =
    .ok [Tests.reference] := rfl

#print axioms reinterpret_result

cil_decoded_method nullRefBody := wrapper FeatureProfile.scalar layouts
  (member unsafeOwner name!"NullRef" (.byref byte) [] [byte])

/-- The null reference helper returns a null managed reference. -/
theorem nullRef_result : run nullRefBody [] =
    .ok [.reference .null] := rfl

#print axioms nullRef_result

cil_decoded_method offsetBody := wrapper FeatureProfile.scalar layouts
  (member unsafeOwner name!"ByteOffset" (.atom runtimeScope "System.IntPtr")
    [.byref byte, .byref byte] [byte])

/-- The two references differ by four bytes. -/
theorem offset_result : run offsetBody [start, fourth] =
    .ok [.scalar (.i64 4)] := rfl

#print axioms offset_result

cil_decoded_method loadByteBody := wrapper FeatureProfile.scalar layouts
  (member unsafeOwner name!"ReadUnaligned" byte [.byref byte] [byte])

/-- The unaligned transfer reads the initialized static byte. -/
theorem loadByte_result : run loadByteBody [Tests.reference] staticMemory =
    .ok [.scalar (.i32 7)] := rfl

#print axioms loadByte_result

cil_decoded_method blockInitBody := wrapper FeatureProfile.scalar layouts
  (member unsafeOwner name!"InitBlockUnaligned" .void
    [.byref byte, byte, .atom runtimeScope "System.UInt32"])

/-- A one-byte block initialization succeeds in writable caller memory. -/
theorem blockInit_result :
    run blockInitBody [Tests.reference, .scalar (.i32 9), .scalar (.i32 1)] = .ok [] := rfl

#print axioms blockInit_result

end ClosedMembers

-- Each helper call steps as the scalar intrinsic it was lowered to, faults included.
/-- A body whose only instruction is a call of `method`, with no link. -/
private def calling (method : CIL.Extraction.MethodRef) : CIL.Method :=
  { body with code := [.call method {}] }
private def int32 (value : Int) : Value := .scalar (.i32 (BitVec.ofInt 32 value))
example : step (calling Table.mathMin) (.call Table.mathMin {}) 0 [] frame [int32 3, int32 (-2)]
      heapMemory =
    step body (.intrinsic (.scalar (.math .min 32 true)) 2) 0 [] frame [int32 3, int32 (-2)]
      heapMemory := by rfl
example : step (calling Table.mathMax) (.call Table.mathMax {}) 0 [] frame [int32 3, int32 (-2)]
      heapMemory =
    step body (.intrinsic (.scalar (.math .max 32 true)) 2) 0 [] frame [int32 3, int32 (-2)]
      heapMemory := by rfl
example : step (calling Table.mathClamp) (.call Table.mathClamp {}) 0 [] frame
      [int32 9, int32 1, int32 5] heapMemory =
    step body (.intrinsic (.scalar (.math .clamp 32 true)) 3) 0 [] frame
      [int32 9, int32 1, int32 5] heapMemory := by rfl
example : step (calling Table.mathAbs) (.call Table.mathAbs {}) 0 [] frame [int32 (-7)]
      heapMemory =
    step body (.intrinsic (.scalar (.math .abs 32 true)) 1) 0 [] frame [int32 (-7)]
      heapMemory := by rfl
example : step (calling Table.mathSign) (.call Table.mathSign {}) 0 [] frame
      [.scalar (.i64 (BitVec.ofInt 64 (-7)))] heapMemory =
    step body (.intrinsic (.scalar (.math .sign 64 true)) 1) 0 [] frame
      [.scalar (.i64 (BitVec.ofInt 64 (-7)))] heapMemory := by rfl
example : (step (calling Table.mathMax) (.call Table.mathMax {}) 0 [] frame
    [int32 3, int32 (-2)] heapMemory).toBool := by rfl
-- Bounds out of order and the most negative `Abs` fault as the intrinsic does.
example : step (calling Table.mathClamp) (.call Table.mathClamp {}) 0 [] frame
      [int32 1, int32 5, int32 9] heapMemory =
    step body (.intrinsic (.scalar (.math .clamp 32 true)) 3) 0 [] frame
      [int32 1, int32 5, int32 9] heapMemory := by rfl
example : (step (calling Table.mathClamp) (.call Table.mathClamp {}) 0 [] frame
    [int32 1, int32 5, int32 9] heapMemory).toBool = false := by rfl
example : step (calling Table.mathAbs) (.call Table.mathAbs {}) 0 [] frame
      [int32 (-2147483648)] heapMemory =
    step body (.intrinsic (.scalar (.math .abs 32 true)) 1) 0 [] frame [int32 (-2147483648)]
      heapMemory := by rfl
-- A modelled call leaves unspecified operands to its model, so it faults as the intrinsic does.
example : step (calling Table.mathMax) (.call Table.mathMax {}) 0 [] frame
      [.scalar (.v128Low64 7), int32 1] heapMemory =
    step body (.intrinsic (.scalar (.math .max 32 true)) 2) 0 [] frame
      [.scalar (.v128Low64 7), int32 1] heapMemory := by rfl

section
open CIL.Extraction (createScalarUnsafeMethod getElement128Method getElement256Method)

-- Each vector helper call steps as its intrinsic. `GetElement` reads lane 0 of a vector known
-- only in its low lane, where the call faulted before it left its operands to its model.
example : step (calling getElement128Method) (.call getElement128Method {}) 0 [] frame
      [int32 0, .scalar (.v128Low64 7)] heapMemory =
    step body (.intrinsic (.vector (.extract64 128)) 2) 0 [] frame
      [int32 0, .scalar (.v128Low64 7)] heapMemory := by rfl
example : step (calling getElement128Method) (.call getElement128Method {}) 0 [] frame
      [int32 0, .scalar (.v128Low64 7)] heapMemory =
    .ok (.next 1 [.scalar (.i64 7)] frame heapMemory) := by rfl
example : step (calling getElement128Method) (.call getElement128Method {}) 0 [] frame
      [int32 1, .scalar (.v128Low64 7)] heapMemory =
    step body (.intrinsic (.vector (.extract64 128)) 2) 0 [] frame
      [int32 1, .scalar (.v128Low64 7)] heapMemory := by rfl
/-- A 256-bit vector whose four 64-bit lanes hold 1, 2, 3 and 4, lowest first. -/
private def lanes : BitVec 256 := CIL.Vector.pack256 1 2 3 4
example : step (calling getElement256Method) (.call getElement256Method {}) 0 [] frame
      [int32 2, .scalar (.v256 lanes)] heapMemory =
    step body (.intrinsic (.vector (.extract64 256)) 2) 0 [] frame
      [int32 2, .scalar (.v256 lanes)] heapMemory := by rfl
example : step (calling getElement256Method) (.call getElement256Method {}) 0 [] frame
      [int32 2, .scalar (.v256 lanes)] heapMemory =
    .ok (.next 1 [.scalar (.i64 3)] frame heapMemory) := by rfl
example : step (calling getElement256Method) (.call getElement256Method {}) 0 [] frame
      [int32 4, .scalar (.v256 lanes)] heapMemory =
    step body (.intrinsic (.vector (.extract64 256)) 2) 0 [] frame
      [int32 4, .scalar (.v256 lanes)] heapMemory := by rfl
example : step (calling createScalarUnsafeMethod) (.call createScalarUnsafeMethod {}) 0 [] frame
      [.scalar (.i64 7)] heapMemory =
    step body (.intrinsic (.vector .createScalarUnsafe64) 1) 0 [] frame [.scalar (.i64 7)]
      heapMemory := by rfl

/-- `GetElement(CreateScalarUnsafe(value), 0)` as two calls, as an extraction emits it. -/
private def unsafeLow : CIL.Program :=
  [{ body with
      code := [.ldarg 0, .call createScalarUnsafeMethod {}, .ldc_i4 0,
        .call getElement128Method {}, .ret],
      returnsValue := true }]
example : (invoke unsafeLow 8 0 [.scalar (.i64 7)] Memory.empty).map Prod.snd =
    .ok [.scalar (.i64 7)] := by rfl

end

section
open CIL.Extraction (ModelEntry)

-- Every memory operation's model transports under an allocation renaming: a read, a write and
-- an operation with an out operand among them.
example : (CIL.RuntimeModel.memory (.arraySpan .signed32 true .whole)).StepRenamed :=
  memory_stepRenamed _
example : (CIL.RuntimeModel.memory (.spanCopy 4 true)).StepRenamed := memory_stepRenamed _
example : (CIL.RuntimeModel.memory (.divRemOut 64)).StepRenamed := memory_stepRenamed _

/-- A family of entries that resolve only memory operations transports under every renaming,
    which is the case such a family adds to `runtimeModel_stepRenamed`. -/
theorem memoryEntries_stepRenamed (entries : List ModelEntry)
    (memoryOnly : ∀ entry ∈ entries,
      entry.Yields fun model => ∃ operation, model = .memory operation) :
    ∀ entry ∈ entries, entry.Yields CIL.RuntimeModel.StepRenamed := by
  intro entry member environment method model found
  obtain ⟨operation, rfl⟩ := memoryOnly entry member environment method model found
  exact memory_stepRenamed operation
/--
info: 'Tests.RuntimeModels.memoryEntries_stepRenamed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms memoryEntries_stepRenamed

end

open CIL CIL.Extraction

/-- A virtual call with a link belongs to the totality obligation and satisfies it. -/
theorem linkedVirtualClaim (environment : LayoutEnvironment) (link : Link) (offset : Nat)
    (site : CallSite) :
    SiteClaimTotal environment (some link) ⟨offset, 111, .call site⟩ true ∧
      siteClaim environment (some link) ⟨offset, 111, .call site⟩ = .link := by
  constructor
  · intro _ _
    simp [siteClaim, methodTokenCall]
  · rfl

#print axioms linkedVirtualClaim

/-- A live, unlinked virtual call has no claim. -/
theorem unknownVirtualRefused (environment : LayoutEnvironment) (offset : Nat) (site : CallSite) :
    ¬ SiteClaimTotal environment none ⟨offset, 111, .call site⟩ true := by
  simp [SiteClaimTotal, foldOwnsSite, siteClaim, methodTokenCall, callOpcode?]

#print axioms unknownVirtualRefused

/-- Whether a fold role fixes its entire instruction, stated per constructor: a role outside
    head, interior and result must leave a live call to the claim check. -/
private def ownsWholeSite : Option FoldRole → Bool
  | none => false
  | some .head => true
  | some .interior => true
  | some (.result _) => true
  | some (.typeBranch _) => false
  | some (.raise _) => false
  | some .argument => false
  | some .tailCall => false
  | some .blocked => false

/-- Only head, interior and result roles exempt a site from its decoder and claim check. -/
theorem foldOwnsSite_roles (role : Option FoldRole) : foldOwnsSite role = ownsWholeSite role := by
  rcases role with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> rfl

#print axioms foldOwnsSite_roles

/-- An unlinked method-token site that the table does not claim is refused. -/
theorem unclaimedSiteRefused (environment : LayoutEnvironment) (raw : RawInstruction)
    (site : CallSite) (token : methodTokenCall raw.opcode = true)
    (operand : raw.operand = .call site)
    (claims : LayoutEnvironment → CallOpcode → MethodRef → Bool)
    (unclaimed : (callOpcode? raw.opcode).any
      (fun op => claims environment op site.method) = false) :
    siteClaim environment none raw claims = .refused := by
  simp [siteClaim, token, operand, unclaimed]

#print axioms unclaimedSiteRefused

end Tests.RuntimeModels
