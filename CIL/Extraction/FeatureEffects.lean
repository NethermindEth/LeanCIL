import CIL.Instructions

/-!
# Stack effects of emitted instructions

The feature-flow check in `Features` matches most raw instructions to their emitted
counterpart only by stack effect. This file gives that effect, as `(pops, pushes)`, for
each emitted instruction that cannot disturb a tracked local; the rest have none and must
be matched exactly. Indirect loads, stores and block operations also meet the exact rule of
`IndirectAccess`.
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
  | .vector128Unsafe store offset =>
    let pops := (if store then 2 else 1) + (if offset then 1 else 0)
    (pops, if store then 0 else 1)
  | .bigMul64 _ | .divRemOut _ => (3, 1)
  | .spanSlice explicitLength => (if explicitLength then 3 else 2, 1)
  | .spanFromReference .. | .byteOffset => (2, 1)
  | .spanSingleReference .. => (1, 1)
  | .spanEmpty .. => (0, 1)
  | .arraySpan _ _ range => (range.argumentCount, 1)
  | .observeView _ | .spanReinterpret .. | .spanReadOnly => (1, 1)
  | .copyBlock _ | .initBlock _ => (3, 0)
  | .store128 | .store256 | .store512 => (2, 0)
  | .nullRef => (0, 1)
  | .throwIfNull | .zeroGuard .. => (2, 0)
  | .comparisonGuard .. => (3, 0)
  | .add .. | .spanCreate | .spanItem _ => (2, 1)
  | .load128 | .load256 | .load512 | .asRef | .bitcastByteBool | .bitcastValue ..
  | .createSpan _ | .spanReference | .spanLength | .isNullRef => (1, 1)

/-- The raw opcode a class type test lowers from, `castclass` (116) or `isinst` (117), and the
    class it tests; `none` for any other instruction. -/
def typeTestSource : Instruction → Option (Nat × TypeExpr)
  | .castclass type => some (116, type)
  | .isinst type => some (117, type)
  | _ => none

/-- Successful stack effects for instructions that cannot create a local alias or
change a local root. Control flow, returns, stores and addresses require exact
raw-instruction matching instead. No unrecognized instruction is admitted. -/
def emittedFeatureEffect (op : Instruction) (returnsValue : Bool) : Option (Nat × Nat) :=
  match op with
  | .ldftn .. => some (0, 1)
  | .calli signature _ =>
    some (signature.parameters.length + 1, if signature.result == .void then 0 else 1)
  | .localloc | .newarr _ => some (1, 1)
  -- Pushes and one-operand operations.
  | .nop => some (0, 0)
  | .sizeof _ | .ldc_i4 _ | .ldc_i8 _ | .ldstr _ | .ldnull | .ldarg _ | .ldloc .. => some (0, 1)
  | .neg | .not | .conv_i1 | .conv_i2 | .conv_u2 | .conv_i8 | .conv_i4 | .conv_u1
  | .conv_u4 | .conv_u8 | .conv_u | .conv_i | .conv_ovf _ | .conv_ovf_un _
  | .ldobj _ | .ldind _
  | .castclass _ | .isinst _ | .ldfld _ | .ldflda _ | .ldlen => some (1, 1)
  -- Two-operand arithmetic and comparisons, plain or with a widened native operand.
  | .add | .sub | .mul | .and | .or | .xor | .shl | .shr | .shr_un
  | .clt | .clt_un | .cgt | .cgt_un | .ceq | .div | .div_un | .rem | .rem_un | .add_ovf
  | .add_ovf_un | .sub_ovf | .sub_ovf_un | .mul_ovf | .mul_ovf_un => some (2, 1)
  -- Array element loads and stores.
  | .ldelem _ | .ldelem_ref | .ldelem_any _ | .ldelema .. => some (2, 1)
  | .stelem _ | .stelem_ref | .stelem_any _ => some (3, 0)
  -- Stores and initialization through a reference, `pop` and `dup`.
  | .stind _ | .cpobj _ | .stobj _
  | .stfld _ => some (2, 0)
  | .initobj _ | .pop => some (1, 0)
  | .dup => some (1, 2)
  -- Calls, construction, intrinsics and memory operations.
  | .call method _ => some (method.argumentCount, if returnsValue then 1 else 0)
  | .callvirt method => some (method.argumentCount, if returnsValue then 1 else 0)
  | .newobj constructor => some (constructor.parameters.length, 1)
  | .memory operation => some (memoryFeatureEffect operation)
  | .ldsfld _ | .ldsflda _ | .ldtoken _ => some (0, 1)
  | .stsfld _ => some (1, 0)
  -- Local writes, local addresses and control flow must match their raw instruction exactly.
  | .ldloca _ | .stloc .. | .starg _ | .ldarga _
  | .ret | .throw _ | .unadmitted _ | .br _ | .switch _ | .brfalse _
  | .brtrue _ | .bgt _ | .ble _ | .ble_un _ | .blt_un _ | .bge_un _ | .bgt_un _ | .bge _
  | .blt _ | .beq _ | .bne_un _ => none

end CIL.Extraction
