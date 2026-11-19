import CIL.Extraction.UnsafeTransfers
import CIL.Extraction.SpanCalls
import CIL.Extraction.BinaryTransfers
import CIL.Extraction.ObjectConstruction
import CIL.Extraction.GuardCalls

/-!
# Unsafe helper calls

Live lowered calls bind their memory operations. Modelled Unsafe calls retain their operands.
-/

namespace CIL.Extraction

/-- Standalone reference and memory operations accept only raw opcodes that produce them.
    A call is the only possible origin of a pointer transfer, span transfer or view observation. -/
private def memoryCallOrigin (raw : RawInstruction) : Instruction → Bool
  | .skipInit | .memory .isNullRef | .memory .byteOffset => false
  | .memory .nullRef => raw.opcode == 20 && raw.operand == .none
  | .memory (.pointerTransfer ..) | .memory (.marshalRead ..) | .memory (.marshalWrite ..)
  | .memory (.spanReinterpret ..) | .memory (.observeView _) => raw.opcode == 40
  | _ => true

/-- A recognized call emits exactly its helper operation, which no other instruction may emit. -/
def UnsafeCallsValid (closed : RawMethod)
    (reachable : List Bool) (code : List Instruction) : Prop :=
  closed.code.length = reachable.length ∧ closed.code.length = code.length ∧
  all3 (fun instruction live emitted => !live ||
      memoryCallOrigin instruction emitted &&
      vector128UnsafeMatches instruction emitted &&
      binaryTransferMatches instruction emitted &&
      callEmitsNoPop instruction emitted &&
      guardCallMatches instruction emitted)
    closed.code reachable code = true

instance (closed : RawMethod)
    (reachable : List Bool) (code : List Instruction) :
    Decidable (UnsafeCallsValid closed reachable code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end CIL.Extraction
