import Lean
import CIL.Extraction.BodyDecoding

/-!
# Naming a body that does not decode

`cil_body_decodes` proves `bodyMatches pin body method = true` by kernel evaluation. When the kernel
refutes it, the tactic says which method failed and why: the error the body and metadata check
raises, or the field of the decoded body that differs from the emitted definition. The
check itself stays the kernel's decision; the evaluation here only words the failure.
-/

namespace CIL.Extraction

/-- The first part of a decoded body that the emitted definition does not repeat. -/
def bodyDifference (decoded : DecodedBody) (method : RawMethod) : String :=
  if decoded.maxStack != method.maxStack then "the maximum stack depth"
  else if decoded.initLocals != method.initLocals then "the init-locals flag"
  else "the instructions"

/-- The failure of `bodyMatches pin body method`, worded for the method named `signature`. -/
def describeBodyFailure (signature : String) (pin : AssemblyPin) (body : BodyEvidence)
    (method : RawMethod) : String :=
  let lead := s!"Method {signature}: the decoded method does not match its body bytes or metadata"
  match checkBody pin body method with
  | .error error => s!"{lead}: {repr error}"
  | .ok decoded => s!"{lead}: {bodyDifference decoded method} differ"

open Lean Elab Tactic Meta in
/-- Prove `bodyMatches pin body method = true` with the kernel, naming the method and the failure when
    the kernel refutes it. The body must be a constant `methodNBody` with its method's
    `methodNSignature` beside it, as extractions emit them. -/
elab "cil_body_decodes" : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  try evalTactic (← `(tactic| decide +kernel))
  catch kernelFailure =>
    let arguments := (target.getAppArgs[1]?.getD target).getAppArgs
    let some bodyName := arguments[1]?.bind (·.constName?)
      | throw kernelFailure
    let stem := bodyName.getString!
    let signatureName := Name.mkStr bodyName.getPrefix ((stem.dropEnd 4).toString ++ "Signature")
    let message ← unsafe evalExpr String (mkConst ``String)
      (mkAppN (mkConst ``describeBodyFailure)
        #[mkConst signatureName, arguments[0]!, arguments[1]!, arguments[2]!])
    throwError message

end CIL.Extraction
