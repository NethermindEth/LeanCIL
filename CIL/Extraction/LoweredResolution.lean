import CIL.Extraction.LoweredCalls

/-!
# Resolution of lowered calls

Each named family computes its instruction from the call operand and the checked layout
environment.
-/

namespace CIL.Extraction

/-- The instruction of this raw member, or no instruction when its overload cannot resolve. -/
def LoweredFamily.resolve (family : LoweredFamily) (_environment : CallLayouts)
    (_raw : RawInstruction) : Option Instruction :=
  nomatch family

end CIL.Extraction
