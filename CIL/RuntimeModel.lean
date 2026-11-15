import CIL.Instructions

/-!
# Runtime models

A runtime model is the meaning the checked interpreter gives a call to a runtime library method
whose body is not extracted: an intrinsic, a checked memory helper, a hardware feature test, a
constant, a reference comparison or subtraction, an unaligned typed transfer, `Unsafe.SkipInit`
or the `System.Object` constructor. `CIL.Safety.runModel` executes a model, and
`MemoryOp.callReached` names the memory operations a model may carry.
-/

namespace CIL

/-- The opcode of a call site whose target a runtime model can stand for. -/
inductive CallOpcode where
  | call | newobj
  deriving Repr

/-- The order of two references that `Unsafe.AreSame` (`same`), `IsAddressLessThan`
    (`less`: the first below the second) and `IsAddressGreaterThan` (`greater`) test. -/
inductive ReferenceRelation where
  | same | less | greater
  deriving DecidableEq, Repr

/-- What a call to a modelled runtime method does. -/
inductive RuntimeModel where
  /-- An intrinsic taking `argc` operands, available only where the profile has it. -/
  | intrinsic (operation : Intrinsic) (argc : Nat)
  /-- A checked memory helper; `MemoryOp.callReached` holds of `operation`. -/
  | memory (operation : MemoryOp)
  /-- A hardware feature test, answered by the method's profile. -/
  | feature (feature : Feature)
  /-- A constant of the target, such as `IntPtr.Size` or `Unsafe.SizeOf<T>`. -/
  | constant (value : W32)
  /-- `Unsafe.AreSame`, `IsAddressLessThan` or `IsAddressGreaterThan`. -/
  | referenceCompare (relation : ReferenceRelation)
  /-- `Unsafe.SubtractByteOffset`: the reference moved back by a byte offset. -/
  | referenceSubtract
  /-- `Unsafe.ReadUnaligned` (`store` false) or `WriteUnaligned` of a value of `kind`. -/
  | typedTransfer (kind : TransferKind) (store : Bool)
  /-- `Unsafe.SkipInit`: its out reference must form, and nothing is written. -/
  | skipInit
  /-- The `System.Object` constructor, which only consumes its receiver. -/
  | objectConstructor
  deriving Repr

/-- Operands a model observes; the checked interpreter rejects the call when any of them has
    unspecified bits. Intrinsics count none, since they decide themselves which bits they read. -/
def RuntimeModel.observerCount : RuntimeModel → Nat
  | .intrinsic .. | .feature _ | .constant _ | .objectConstructor => 0
  | .memory operation => operation.argumentCount
  | .referenceCompare _ | .referenceSubtract => 2
  | .typedTransfer _ store => if store then 2 else 1
  | .skipInit => 1

/-- Whether a call to a runtime method can reach `operation`. The other operations are the
    meaning of opcodes; the match has no default, so each new operation is classified. -/
def MemoryOp.callReached : MemoryOp → Bool
  -- Views, spans and their observations
  | .observeView _ | .spanReinterpret .. | .spanCopy .. | .spanFill .. | .arrayFill ..
  | .spanCreate | .spanReference | .createSpan _ | .spanItem _ | .spanLength | .spanEmpty ..
  | .spanFromReference .. | .spanSingleReference .. | .spanSlice _ | .spanReadOnly
  | .arraySpan .. => true
  -- Transfers, wide arithmetic and blocks
  | .binaryRead .. | .binaryWrite .. | .marshalRead .. | .marshalWrite .. | .pointerTransfer ..
  | .vector128Unsafe .. | .bigMul64 _ | .divRemOut _ | .copyBlock _ | .initBlock _ => true
  -- References, bit casts and guards
  | .asRef | .add .. | .byteOffset | .bitcastByteBool | .bitcastValue .. | .nullRef | .isNullRef
  | .throwIfNull | .zeroGuard .. | .comparisonGuard .. => true
  -- Opcode meanings: vector loads and stores, statics, arrays and literals
  | .load128 | .load256 | .load512 | .store128 | .store256 | .store512
  | .staticAddress _ | .staticValue _ | .arrayLength | .arrayLoad .. | .arrayStore _
  | .arrayAddress .. | .arrayTransfer .. | .nullObject | .stringLiteral _
  | .referenceArrayLength | .referenceArrayLoad | .referenceArrayStore => false

end CIL
