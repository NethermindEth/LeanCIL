import CIL.Extraction.LoweredCalls
import CIL.Extraction.HardwareCalls

/-!
# Resolution of lowered calls

Each named family computes its instruction from the call operand, the checked layout
environment and profile, and its role in a fold of the raw method.
-/

namespace CIL.Extraction

/-- Only a nominal aggregate needs a layout-table width in the span signature matchers. -/
private def aggregateWidth (environment : CallLayouts) (type : TypeExpr) : Option Nat :=
  match type with
  | .aggregate .. => (environment.valueShape type).size?
  | _ => some 0

/-- A span call binds its element sizes and its local destination, when a fold supplies one. -/
private def spanInstruction (environment : CallLayouts) (role : Option FoldRole)
    (raw : RawInstruction) (site : CallSite) : Option Instruction := do
  if raw.opcode != 40 || site.name != ".ctor" then none else pure ()
  let some (.spanConstructor index _) := role | none
  let .apply _ element := site.declaringType | none
  let width ← aggregateWidth environment element
  return .initializeSpanLocal index (← spanLocalConstructor site width)

/-- The instruction of this raw member, or no instruction when its overload cannot resolve. -/
def LoweredFamily.resolve (family : LoweredFamily) (environment : CallLayouts)
    (profile : FeatureProfile) (role : Option FoldRole) (raw : RawInstruction) :
    Option Instruction := do
  let .call site := raw.operand | none
  match family with
  | .hardware => hardwareInstruction environment profile raw site
  | .span => spanInstruction environment role raw site

end CIL.Extraction
