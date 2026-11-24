import Extracted
import CIL.Safety.HeapObjects

/-! The two class tests select different TypeDefs with the same Cecil name in the same image. -/

namespace ExampleProof
open CIL CIL.Safety CIL.Extraction

private def base : TypeExpr := .object Extracted.assembly0.identity "Rows.Parent"
private def qualified : TypeExpr :=
  .object Extracted.assembly0.identity ⟨[⟨name!"Rows", name!"Widget"⟩]⟩
private def dotted : TypeExpr :=
  .object Extracted.assembly0.identity ⟨[⟨name!"", name!"Rows.Widget"⟩]⟩

/-- The first two allocations have different derived classes and the same immediate base. -/
private def heap : Safety.Memory :=
  objectMemory (objectMemory Safety.Memory.empty ⟨qualified, [base]⟩ 0) ⟨dotted, [base]⟩ 0

/-- Replace the type resolved at one token while retaining the pinned body and metadata. -/
private def rejectsSwap (selected replacement : TypeExpr) : Bool := Id.run do
  let body := Extracted.method0Body
  let some (token, _) := body.tokens.operands.find? (fun entry => entry.2 == .type selected)
    | return false
  let operands := body.tokens.operands.map fun entry =>
    if entry.1 == token then (token, RawOperand.type replacement) else entry
  return match checkBody { body with tokens := ⟨operands⟩ } Extracted.method0Original [] with
    | .error (.metadata (.operandMismatch rejected)) => rejected == token
    | _ => false

/-- Each physical operand rejects a claim naming the other TypeDef. -/
theorem swapsRejected : rejectsSwap qualified dotted = true ∧ rejectsSwap dotted qualified = true :=
  ⟨by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms swapsRejected

/-- Both tests run on each object. The namespace-qualified class sets bit 1 and the class with
    the dotted simple name sets bit 0, in agreement with both CLR executions. -/
theorem correctness :
    invoke Extracted.program 16 0 [.object (.address ⟨0, 0⟩)] heap =
      .ok (heap, [.scalar (.i32 2)]) ∧
    invoke Extracted.program 16 0 [.object (.address ⟨1, 0⟩)] heap =
      .ok (heap, [.scalar (.i32 1)]) := ⟨by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms correctness

end ExampleProof
