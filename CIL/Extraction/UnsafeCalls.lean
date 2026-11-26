import CIL.Extraction.SpanCalls
import CIL.Extraction.ObjectConstruction

/-!
# Unsafe helper calls

Live calls retain their operands, including calls whose checked model consumes one value.
-/

namespace CIL.Extraction

/-- The reachability and code lists cover each site, and no live call is replaced by a pop. -/
def UnsafeCallsValid (closed : RawMethod)
    (reachable : List Bool) (code : List Instruction) : Prop :=
  closed.code.length = reachable.length ∧ closed.code.length = code.length ∧
  all3 (fun instruction live emitted => !live || callEmitsNoPop instruction emitted)
    closed.code reachable code = true

instance (closed : RawMethod)
    (reachable : List Bool) (code : List Instruction) :
    Decidable (UnsafeCallsValid closed reachable code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end CIL.Extraction
