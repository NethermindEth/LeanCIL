import CIL.Safety.Execution
import CIL.Extraction.RuntimeModels
import CIL.Extraction.UnsafeCalls
import CIL.Extraction.KernelEquation
import CIL.ProfileEquivalence
import Tests.Support

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
    step body .skipInit 3 [] frame [start] staticMemory := rfl
example : runModel body .objectConstructor 3 frame [.object .null] staticMemory =
    step body .pop 3 [] frame [.object .null] staticMemory := rfl

-- Every typed transfer family runs as its typed load or store.
example : runModel body (.typedTransfer (.scalar 4 false) true) 3 frame
      [.scalar (.i32 9), start] heapMemory =
    step body (.storeScalar 4) 3 [] frame [.scalar (.i32 9), start] heapMemory := rfl
example : runModel body (.typedTransfer (.snapshot (.aggregate 16)) false) 3 frame [start]
      heapMemory =
    step body (.loadAggregate 16) 3 [] frame [start] heapMemory := rfl
example : runModel body (.typedTransfer (.snapshot (.aggregate 16)) true) 3 frame
      [.scalar (.aggregate (List.replicate 16 1)), start] heapMemory =
    step body (.storeAggregate 16) 3 [] frame
      [.scalar (.aggregate (List.replicate 16 1)), start] heapMemory := rfl
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
    step body .skipInit 3 [] frame [.scalar (.i32 0)] staticMemory := rfl

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
    observerCount (.storeScalar 4) := rfl
example : CIL.RuntimeModel.skipInit.observerCount = observerCount .skipInit := rfl
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
    .store256, .store512, .arrayAddress element, .stringLiteral ""].any
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
  { opcode := .call, owner := .constructor runtimeScope "System.Span`1", name := name!"get_Length",
    resolve := fun _ method =>
      if method.hasThis && method.parameters.isEmpty then some (.memory .spanLength) else none }

/-- BigMul by its exact reference, and `get_Length` of every span instance. -/
private def entries : List ModelEntry :=
  [ModelEntry.exact .call bigMul (.memory (.bigMul64 false)), spanLengthEntry]

/-- The table of `entries`, accounting for the wide arithmetic and span length emissions. -/
private def catalog : ModelCatalog where
  table := model_table% entries
  lowered
    | .memory (.bigMul64 signed) => some (.memory (.bigMul64 signed))
    | .memory (.divRemOut width) => some (.memory (.divRemOut width))
    | .memory .spanLength => some (.memory .spanLength)
    | _ => none

/-- A call or `newobj` of `method`. -/
private def site (method : MethodRef) (opcode : Nat := 40) : RawInstruction :=
  ⟨0, opcode, .call {
    method := method, target := .external "", typeArguments := [],
    parameterCount := method.parameters.length, returnsValue := true }⟩

-- The literal table is the balanced table of its entries.
example : catalog.table = ModelTable.ofEntries entries := rfl

-- A modelled call agrees only with its own model: BigMul emitted as DivRem is refused.
example : catalog.siteAgrees {} {} (site bigMul) (.memory (.bigMul64 false)) = true := by
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

-- An entry filed under another name's key is not selected for that name.
/-- A tree that files the span length entry under the key of `get_IsEmpty`. -/
private def misfiled : ModelTable := .node .leaf (name!"get_IsEmpty").code [spanLengthEntry] .leaf
private def spanIsEmpty : MethodRef :=
  { spanLength word with name := name!"get_IsEmpty", returnType := runtimeType "System.Boolean" }
example : misfiled.find {} .call spanIsEmpty = none := by decide +kernel

-- A call the table does not model keeps its call and may emit no model.
example : catalog.siteAgrees {} {} (site divRem) (.call divRem) = true := by decide +kernel
example : catalog.siteAgrees {} {} (site divRem) (.memory (.divRemOut 64)) = false := by
  decide +kernel

-- The opcode and the owner are part of the key; a generic owner matches by its head.
example : catalog.table.find {} .newobj bigMul = none := by decide +kernel
example : catalog.table.find {} .call { bigMul with owner := runtimeType "System.Maths" } =
    none := by decide +kernel
example : catalog.siteAgrees {} {} (site (spanLength word)) (.memory .spanLength) = true := by
  decide +kernel
example : catalog.table.find {} .call
    { spanLength word with owner := runtimeType "System.String" } = none := by decide +kernel
example : catalog.siteAgrees {} {} (site (spanLength (runtimeType "System.Byte")))
    (.memory .spanLength) = true := by decide +kernel
example : catalog.siteAgrees {} {} (site bigMul 115) (.memory (.bigMul64 false)) = false := by
  decide +kernel

/-- A method whose only instruction is `instruction`. -/
private def method (instruction : RawInstruction) : RawMethod :=
  { token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
    attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
    initLocals := true, maxStack := 3, genericParameters := [], code := [instruction] }

-- Only live sites are checked.
example : ModelsAgree catalog {} {} (method (site bigMul)) [false] [.memory (.divRemOut 64)] := by
  decide +kernel
example : ¬ ModelsAgree catalog {} {} (method (site bigMul)) [true] [.memory (.divRemOut 64)] := by
  decide +kernel

-- Two entries for one slot are refused when the table is built.
/-- error: model table: two entries share an opcode, owner and name -/
#guard_msgs in
example : ModelTable :=
  model_table% [ModelEntry.exact .call bigMul (.memory (.bigMul64 false)),
    ModelEntry.exact .call bigMul (.memory (.bigMul64 true))]

-- The runtime table models the exact `System.Object` constructor under `call` and nothing else.
example : runtimeModel {} .call objectConstructorMethod = some .objectConstructor := by
  decide +kernel
example : runtimeModel {} .call bigMul = none := by decide +kernel
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
example : RuntimeModelsAgree (method
    (site bigMul)) [true]
    { body with code := [.call (Tests.callee 3) {}], links := [(0, .direct 7)] } := by
  decide +kernel

-- An entry filed under `newobj` does not model a `call` of its method.
example : ModelTable.find
    (model_table% [ModelEntry.exact .newobj objectConstructorMethod .objectConstructor])
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
      method := objectConstructorMethod, target := .managed 0, typeArguments := [],
      parameterCount := 0, returnsValue := false }⟩) [true]
    (emitting (.call objectConstructorMethod {}) []) := by decide +kernel

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
example : ¬ UnsafeCallsValid [] (method (site bigMul)) [true] [.pop] := by decide +kernel
example : UnsafeCallsValid [] (method (site bigMul)) [true] [.call bigMul {}] := by decide +kernel
example : ¬ UnsafeCallsValid [] (method (site objectConstructorMethod)) [true] [.pop] := by
  decide +kernel
example : UnsafeCallsValid [] (method ⟨0, 38, .none⟩) [true] [.pop] := by decide +kernel

-- An external call the table does not model needs a link.
example : ¬ ManagedCallsValid [] [] (callModelled body) (method (site bigMul)) [true]
    (emitting (.call bigMul {}) []) := by decide +kernel

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
example : ModelsAgree { table := model_table% [objectConstructorEntry], lowered := fun _ => none }
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
  { table := model_table% [ModelEntry.exact .call avx2And (.intrinsic (.avx2 .band) 2)],
    lowered := fun _ => none }
example : avx2Catalog.siteAgrees {} {} (site avx2And) (.call avx2And {}) = false := by
  decide +kernel
example : avx2Catalog.siteAgrees {} { avx2 := true } (site avx2And) (.call avx2And {}) = true := by
  decide +kernel

-- The profile query of a call is its model's: the helpers read no flag, so every two profiles
-- agree on a program that calls one.
/-- A method that returns `Math.Max` of its two arguments. -/
private def maxProgram : CIL.Program :=
  [{ body with code := [.ldarg 0, .ldarg 1, .call mathMax {}, .ret], returnsValue := true }]
example : CIL.Program.profileReads maxProgram = [] := by decide +kernel
example : CIL.Program.ProfileAgreement maxProgram {} { avx2 := true } :=
  CIL.Program.ProfileAgreement.of_flags _ _ _ (by decide +kernel)

end Table

/-- The receiver an object constructor call consumes. -/
private def receiver : Value := .object (.address ⟨0, 0⟩)

/-- A call of the `System.Object` constructor at a pc with no link steps as `pop` does. -/
example : step { body with code := [.call CIL.Extraction.objectConstructorMethod {}] }
    (.call CIL.Extraction.objectConstructorMethod {}) 0 [] frame [receiver] heapMemory =
      step body .pop 0 [] frame [receiver] heapMemory := by
  cil_kernel_rfl

-- Each helper call steps as the scalar intrinsic it was lowered to, faults included.
/-- A body whose only instruction is a call of `method`, with no link. -/
private def calling (method : CIL.Extraction.MethodRef) : CIL.Method :=
  { body with code := [.call method {}] }
private def int32 (value : Int) : Value := .scalar (.i32 (BitVec.ofInt 32 value))
example : step (calling Table.mathMin) (.call Table.mathMin {}) 0 [] frame [int32 3, int32 (-2)]
      heapMemory =
    step body (.intrinsic (.scalar (.math .min 32 true)) 2) 0 [] frame [int32 3, int32 (-2)]
      heapMemory := by cil_kernel_rfl
example : step (calling Table.mathMax) (.call Table.mathMax {}) 0 [] frame [int32 3, int32 (-2)]
      heapMemory =
    step body (.intrinsic (.scalar (.math .max 32 true)) 2) 0 [] frame [int32 3, int32 (-2)]
      heapMemory := by cil_kernel_rfl
example : step (calling Table.mathClamp) (.call Table.mathClamp {}) 0 [] frame
      [int32 9, int32 1, int32 5] heapMemory =
    step body (.intrinsic (.scalar (.math .clamp 32 true)) 3) 0 [] frame
      [int32 9, int32 1, int32 5] heapMemory := by cil_kernel_rfl
example : step (calling Table.mathAbs) (.call Table.mathAbs {}) 0 [] frame [int32 (-7)]
      heapMemory =
    step body (.intrinsic (.scalar (.math .abs 32 true)) 1) 0 [] frame [int32 (-7)]
      heapMemory := by cil_kernel_rfl
example : step (calling Table.mathSign) (.call Table.mathSign {}) 0 [] frame
      [.scalar (.i64 (BitVec.ofInt 64 (-7)))] heapMemory =
    step body (.intrinsic (.scalar (.math .sign 64 true)) 1) 0 [] frame
      [.scalar (.i64 (BitVec.ofInt 64 (-7)))] heapMemory := by cil_kernel_rfl
example : (step (calling Table.mathMax) (.call Table.mathMax {}) 0 [] frame
    [int32 3, int32 (-2)] heapMemory).toBool := by cil_kernel_rfl
-- Bounds out of order and the most negative `Abs` fault as the intrinsic does.
example : step (calling Table.mathClamp) (.call Table.mathClamp {}) 0 [] frame
      [int32 1, int32 5, int32 9] heapMemory =
    step body (.intrinsic (.scalar (.math .clamp 32 true)) 3) 0 [] frame
      [int32 1, int32 5, int32 9] heapMemory := by cil_kernel_rfl
example : (step (calling Table.mathClamp) (.call Table.mathClamp {}) 0 [] frame
    [int32 1, int32 5, int32 9] heapMemory).toBool = false := by cil_kernel_rfl
example : step (calling Table.mathAbs) (.call Table.mathAbs {}) 0 [] frame
      [int32 (-2147483648)] heapMemory =
    step body (.intrinsic (.scalar (.math .abs 32 true)) 1) 0 [] frame [int32 (-2147483648)]
      heapMemory := by cil_kernel_rfl

end Tests.RuntimeModels
