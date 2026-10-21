import CIL.Instructions

namespace CIL.Extraction

private def memoryFeatureEffect : MemoryOp → Nat × Nat
  | .bigMul64 => (3, 1)
  | .copyBlock _ | .initBlock _ => (3, 0)
  | .store128 | .store256 => (2, 0)
  | .init256 | .skipInit => (1, 0)
  | .dataToken _ | .staticAddress _ => (0, 1)
  | .add .. | .spanCreate => (2, 1)
  | .load128 | .load256 | .asRef | .bitcast256 | .bitcastByteBool | .bitcastValue ..
  | .createSpan | .spanReference => (1, 1)

/-- Successful stack effects for instructions that cannot create a local alias or
change a local root. Control flow, returns, stores and addresses require exact
raw-instruction matching instead. No unrecognized instruction is admitted. -/
def emittedFeatureEffect (op : Op) (returnsValue : Bool) : Option (Nat × Nat) :=
  match op with
  | .nop => some (0, 0)
  | .const32 _ | .const64 _ | .arg .. | .vectorArg _ | .local .. | .vectorLocal _ => some (0, 1)
  | .neg | .bnot | .convI1 | .convI2 | .convU2 | .convI8 | .convI4 | .convU1
  | .convU4 | .convU8 | .convU | .checkedConvert ..
  | .loadAggregate _ | .loadScalar .. | .load64 | .fieldAt .. | .fieldAddress _
  | .aggregateFieldAt .. | .lane _ | .laneAddress _ | .asRef => some (1, 1)
  | .add | .sub | .mul | .band | .bor | .bxor | .shl | .shr | .shrUn
  | .lt | .ltu | .gt | .gtu | .eq | .divide .. | .checkedArithmetic .. => some (2, 1)
  | .nativeBinary operation => match operation with
    | .add | .sub | .mul | .band | .bor | .bxor | .shl | .shr | .shrUn
    | .lt | .ltu | .gt | .gtu | .eq | .divide .. | .checkedArithmetic .. => some (2, 1)
    | _ => none
  | .storeAggregate _ | .storeScalar _ | .store64 | .copyObject _
  | .setFieldAt .. | .setAggregateFieldAt .. | .setLane _ => some (2, 0)
  | .initAggregate _ | .skipInit | .pop => some (1, 0)
  | .dup => some (1, 2)
  | .call _ count => some (count, if returnsValue then 1 else 0)
  | .newAggregate _ count _ | .newVector256 _ count => some (count, 1)
  | .intrinsic _ count => some (count, 1)
  | .memory operation => some (memoryFeatureEffect operation)
  | .localAddr _ | .vectorLocalAddr _ | .vectorArgAddr _ | .setLocal .. | .setVectorLocal _
  | .feature _ | .ret _ | .throw _ | .unsupported _ | .branch _ | .switch _ | .brzero _ | .brnonzero _
  | .bgt _ | .ble _ | .bleu _ | .bltu _ | .bgeu _ | .bgtu _ | .bge _ | .blt _ | .beq _ | .bne _ => none

end CIL.Extraction
