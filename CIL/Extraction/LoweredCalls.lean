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
  | span
  deriving DecidableEq, Repr

/-- The family of a method-token call before inspecting its overload, layouts or fold role. -/
def loweredCallFamily (raw : RawInstruction) : Option LoweredFamily := do
  let .call site := raw.operand | none
  guard (raw.opcode == 40 && site.name == ".ctor")
  let .apply (.constructor scope owner) _ := site.declaringType | none
  guard (scope == runtimeScope && owner ∈ ["System.Span`1", "System.ReadOnlySpan`1"])
  return .span

end CIL.Extraction
