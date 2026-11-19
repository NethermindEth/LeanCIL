import CIL.Extraction.OpaqueLocals
import CIL.Extraction.UnsafeCalls
import CIL.Extraction.Scalars

/-!
# Ownership of lowered call sites

Runtime ownership uses the opcode and qualified member name.
Each owner resolves the closed signature separately.
-/

namespace CIL.Extraction

/-- A checked runtime family of calls or constructions. -/
inductive LoweredFamily where
  deriving DecidableEq, Repr

/-- The family of a method-token call before inspecting its overload or layouts. -/
def loweredCallFamily (_raw : RawInstruction) : Option LoweredFamily := none

end CIL.Extraction
