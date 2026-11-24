import Extracted
import CIL.Safety.Execution

/-! Overloaded enum parameters bind the namespace and simple name of each physical declaration. -/

namespace ExampleProof
open CIL CIL.Extraction

/-- An enum parameter in the fixture assembly with the given TypeDef columns. -/
private def enumParam (ns name : MetadataName) : TypeExpr :=
  .enum { assembly := ⟨name!"Examples", ⟨1, 0, 0, 0⟩, name!"", none⟩,
          typeNamespace := ns, name } (.atom runtimeScope "System.Int32")

/-- Substituting the other enum in both signatures must fail at the original call token. -/
private def rejectsParameter (selected replacement : TypeExpr) : Bool := Id.run do
  let body := Extracted.method0Body
  let some (token, .call site) := body.tokens.operands.find? (fun entry => match entry.2 with
    | .call site => site.parameterTypes == [selected]
    | _ => false) | return false
  let altered := RawOperand.call
    { site with method.parameters := [replacement], declared.parameters := [replacement] }
  let operands := body.tokens.operands.map fun entry =>
    if entry.1 == token then (token, altered) else entry
  return match checkBody { body with tokens := ⟨operands⟩ } Extracted.method0Original [] with
    | .error (.metadata (.operandMismatch rejected)) => rejected == token
    | _ => false

/-- Each overload rejects the other's enum, and their array elements retain the distinction. -/
theorem physicalParameters :
    let qualified := enumParam name!"Rows" name!"Choice"
    let dotted := enumParam name!"" name!"Rows.Choice"
    rejectsParameter qualified dotted = true ∧ rejectsParameter dotted qualified = true ∧
    sameRuntimeType qualified dotted = some false ∧
    (arrayElementType qualified == arrayElementType dotted) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cil_kernel_rfl
#print axioms physicalParameters

/-- Both overloads execute in CLR evaluation order and return their respective digits. -/
theorem correctness :
    Safety.invoke Extracted.program 64 0 [] Safety.Memory.empty =
      .ok (Safety.Memory.empty, [.scalar (.i32 12)]) := by cil_kernel_rfl
#print axioms correctness

end ExampleProof
