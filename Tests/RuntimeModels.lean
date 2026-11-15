import CIL.Safety.Execution

/-!
# Runtime model tests

A typed static span runs in `memoryInstruction`, so a runtime model's memory operation needs no
static field metadata. Each runtime model runs as the instruction the extractor emits for its
call: `runModel` on a concrete stack equals `step` on that instruction, and the model observes
as many operands as the instruction does.
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

-- The memory operations a call reaches, then the opcode meanings.
example : [CIL.MemoryOp.observeView .spanEmpty, .binaryRead 4 false false false,
    .binaryWrite 4 false false, .spanReinterpret 1 4 false, .spanCopy 1 false, .spanFill 1 false,
    .arrayFill element false, .bigMul64 false, .divRemOut 32, .copyBlock 1, .initBlock 1,
    .vector128Unsafe false false, .asRef, .add 1 true, .byteOffset,
    .marshalRead (.scalar 4 false) false, .marshalWrite (.scalar 4 false) false,
    .pointerTransfer (.scalar 4 false) 4 false, .bitcastByteBool,
    .bitcastValue .vector128 .vector128, .spanCreate, .spanReference, .createSpan 4,
    .spanItem 4, .spanLength, .spanEmpty 4 false, .spanFromReference 4 false,
    .spanSingleReference 4 false, .spanSlice false, .spanReadOnly,
    .arraySpan element false .whole, .nullRef, .isNullRef, .throwIfNull,
    .zeroGuard .negative 32 true, .comparisonGuard .greaterThan 32 true].all
      CIL.MemoryOp.callReached := rfl
example : [CIL.MemoryOp.load128, .load256, .load512, .store128, .store256, .store512,
    .arrayLength, .arrayLoad 4 false, .arrayStore 4,
    .arrayAddress element, .arrayTransfer element false, .stringLiteral "",
    .objectField .void 0 4 false, .setObjectField .void 0 4, .objectReferenceField .void 0,
    .setObjectReferenceField .void 0, .referenceArrayLength, .referenceArrayLoad,
    .referenceArrayStore, .arrayField .void 0 element, .setArrayField .void 0 element].any
      CIL.MemoryOp.callReached = false := rfl

end Tests.RuntimeModels
