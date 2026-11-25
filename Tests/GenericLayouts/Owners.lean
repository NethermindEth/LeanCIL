import Extracted
import CIL.Safety.Execution

/-! Generic calls bind the physical namespace and simple name of each constructor. -/

namespace ExampleProof
open CIL CIL.Extraction

/-- A closed class owner in the fixture assembly. -/
private def classOwner (name : ClassName) : TypeExpr :=
  .apply (.objectConstructor Extracted.assembly0.identity name) (.primitive .int32)

/-- A closed value-type owner in the fixture assembly. -/
private def valueOwner (name : ClassName) : TypeExpr :=
  .apply (.constructor Extracted.assembly0.identity name) (.primitive .int32)

/-- Changing only a call's declaring type must fail at the original MemberRef. -/
private def rejectsOwner (selected replacement : TypeExpr) : Bool := Id.run do
  let body := Extracted.method0Body
  let some (token, .call site) := body.tokens.operands.find? (fun entry => match entry.2 with
    | .call site => site.declaringType == selected
    | _ => false) | return false
  let altered := RawOperand.call { site with method.owner := replacement }
  let operands := body.tokens.operands.map fun entry =>
    if entry.1 == token then (token, altered) else entry
  return match checkBody { body with tokens := ⟨operands⟩ } Extracted.method0Original [] with
    | .error (.metadata (.operandMismatch rejected)) => rejected == token
    | _ => false

/-- Each of the four MemberRefs rejects the other declaration with the same printed name. -/
theorem physicalOwners :
    let qualifiedClass := classOwner "Rows.GenericClass`1"
    let dottedClass := classOwner ⟨[⟨name!"", name!"Rows.GenericClass`1"⟩]⟩
    let qualifiedValue := valueOwner "Rows.GenericValue`1"
    let dottedValue := valueOwner ⟨[⟨name!"", name!"Rows.GenericValue`1"⟩]⟩
    rejectsOwner qualifiedClass dottedClass = true ∧
    rejectsOwner dottedClass qualifiedClass = true ∧
    rejectsOwner qualifiedValue dottedValue = true ∧
    rejectsOwner dottedValue qualifiedValue = true ∧
    sameRuntimeType qualifiedClass dottedClass = some false ∧
    sameRuntimeType qualifiedValue dottedValue = some false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cil_kernel_rfl
#print axioms physicalOwners

/-- The four closed static calls return the digits 1, 2, 3 and 4 in CLR evaluation order. -/
theorem correctness :
    Safety.invoke Extracted.program 64 0 [] Safety.Memory.empty =
      .ok (Safety.Memory.empty, [.scalar (.i32 1234)]) := by cil_kernel_rfl
#print axioms correctness

end ExampleProof
