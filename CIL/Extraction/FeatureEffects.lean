import CIL.Instructions

/-!
# Stack effects of emitted instructions

The feature-flow check in `Features` matches most raw instructions to their emitted
counterpart only by stack effect. This file gives that effect, as `(pops, pushes)`, for
each emitted instruction that cannot disturb a tracked local; the rest have none and must
be matched exactly.
-/

namespace CIL.Extraction

/-- `(pops, pushes)` of each memory operation. -/
private def memoryFeatureEffect : MemoryOp → Nat × Nat
  | .spanCopy _ tryCopy => (2, if tryCopy then 1 else 0)
  | .spanFill _ clear => (if clear then 1 else 2, 0)
  | .arrayFill _ counted => (if counted then 4 else 2, 0)
  | .marshalRead _ trying => (if trying then 2 else 1, 1)
  | .binaryRead _ _ _ trying => (if trying then 2 else 1, 1)
  | .binaryWrite _ _ trying => (2, if trying then 1 else 0)
  | .marshalWrite _ trying => (2, if trying then 1 else 0)
  | .pointerTransfer _ _ store => if store then (2, 0) else (1, 1)
  | .bigMul64 => (3, 1)
  | .spanSlice explicitLength => (if explicitLength then 3 else 2, 1)
  | .spanFromReference .. | .byteOffset => (2, 1)
  | .spanSingleReference .. => (1, 1)
  | .spanEmpty .. => (0, 1)
  | .arraySpan _ _ range => (range.argumentCount, 1)
  | .observeView _ | .spanReinterpret .. | .spanReadOnly | .arrayLength => (1, 1)
  | .arrayLoad .. | .arrayAddress .. => (2, 1)
  | .arrayTransfer _ store => if store then (3, 0) else (2, 1)
  | .arrayStore _ => (3, 0)
  | .copyBlock _ | .initBlock _ => (3, 0)
  | .store128 | .store256 | .store512 => (2, 0)
  | .init256 | .skipInit => (1, 0)
  | .staticAddress _ | .staticValue _ | .nullRef => (0, 1)
  | .add .. | .spanCreate | .spanItem _ => (2, 1)
  | .load128 | .load256 | .load512 | .asRef | .bitcast256 | .bitcastByteBool | .bitcastValue ..
  | .createSpan _ | .spanReference | .spanLength | .isNullRef => (1, 1)

/-- Successful stack effects for instructions that cannot create a local alias or
change a local root. Control flow, returns, stores and addresses require exact
raw-instruction matching instead. No unrecognized instruction is admitted. -/
def emittedFeatureEffect (op : Op) (returnsValue : Bool) : Option (Nat × Nat) :=
  match op with
  | .managed (.address ..) => some (0, 1)
  | .managed .tableLength | .managed (.tableLoad _) => some (1, 1)
  | .managed (.tableElement _) | .managed (.tableAddress _) | .managed .tableOffset => some (2, 1)
  | .managed (.call signature _ _) =>
    some (signature.parameters.length + 1, if signature.result == .void then 0 else 1)
  | .stackAlloc _ | .newArray _ => some (1, 1)
  -- Pushes and one-operand operations.
  | .nop => some (0, 0)
  | .const32 _ | .const64 _ | .arg .. | .vectorArg _ | .local .. | .vectorLocal _ => some (0, 1)
  | .neg | .bnot | .convI1 | .convI2 | .convU2 | .convI8 | .convI4 | .convU1
  | .convU4 | .convU8 | .convU | .checkedConvert ..
  | .loadAggregate _ | .loadScalar .. | .load64 | .fieldAt .. | .fieldAddress _
  | .aggregateFieldAt .. | .lane _ | .laneAddress _ | .asRef => some (1, 1)
  -- Two-operand arithmetic and comparisons, plain or with a widened native operand.
  | .add | .sub | .mul | .band | .bor | .bxor | .shl | .shr | .shrUn
  | .lt | .ltu | .gt | .gtu | .eq | .divide .. | .checkedArithmetic .. => some (2, 1)
  | .nativeBinary operation => match operation with
    | .add | .sub | .mul | .band | .bor | .bxor | .shl | .shr | .shrUn
    | .lt | .ltu | .gt | .gtu | .eq | .divide .. | .checkedArithmetic .. => some (2, 1)
    | _ => none
  -- Stores and initialization through a reference, `pop` and `dup`.
  | .storeAggregate _ | .storeScalar _ | .store64 | .copyObject _
  | .setFieldAt .. | .setAggregateFieldAt .. | .setLane _ => some (2, 0)
  | .initAggregate _ | .skipInit | .pop => some (1, 0)
  | .dup => some (1, 2)
  -- Calls, construction, intrinsics and memory operations.
  | .call _ count | .tailCall _ count => some (count, if returnsValue then 1 else 0)
  | .newAggregate _ count _ | .newVector256 _ count => some (count, 1)
  | .intrinsic _ count => some (count, 1)
  | .memory operation => some (memoryFeatureEffect operation)
  -- Local writes, local addresses and control flow must match their raw instruction exactly.
  | .localAddr _ | .vectorLocalAddr _ | .vectorArgAddr _ | .setLocal .. | .setVectorLocal _
  | .initializeSpanLocal ..
  | .feature _ | .ret _ | .throw _ | .unsupported _ | .branch _ | .switch _ | .brzero _
  | .brnonzero _ | .bgt _ | .ble _ | .bleu _ | .bltu _ | .bgeu _ | .bgtu _ | .bge _ | .blt _
  | .beq _ | .bne _ => none

end CIL.Extraction
