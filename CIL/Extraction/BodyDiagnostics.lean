import Lean
import CIL.Extraction.BodyDecoding

/-!
# Naming a body that does not decode

`cil_body_decodes` proves `bodyMatches body method arguments = true` by kernel evaluation. When
the kernel refutes it, the tactic says which method failed and why: the error the body and
metadata check raises, or the field of the decoded body that differs from the emitted definition.
The check itself stays the kernel's decision; the evaluation here only words the failure.
-/

namespace CIL.Extraction

/-- The first field where the decoded body differs from the supplied evidence or method. -/
def bodyDifference (decoded : DecodedBody) (body : BodyEvidence) (method : RawMethod) :
    Option String :=
  if decoded.statics != body.statics then some "the recorded static field tokens"
  else if decoded.maxStack != method.maxStack then some "the maximum stack depth"
  else if decoded.initLocals != method.initLocals then some "the init-locals flag"
  else if decoded.code != method.code then some "the instructions"
  else none

/-- The decoding error, mismatching field or kernel reduction failure for the named method. -/
def describeBodyFailure (signature : String) (body : BodyEvidence) (method : RawMethod)
    (arguments : List TypeExpr) : String :=
  let lead := s!"Method {signature}: the decoded method does not match its body bytes or metadata"
  match checkBody body method arguments with
  | .error error => s!"{lead}: {repr error}"
  | .ok decoded =>
    match bodyDifference decoded body method with
    | some field => s!"{lead}: {field} differ"
    | none => s!"Method {signature}: the decoded fields agree, but kernel reduction failed"

open Lean Elab Tactic Meta in
/-- Prove `bodyMatches body method arguments = true` with the kernel, naming the method and the
    failure when the kernel refutes it. The body must be a constant `methodNBody` with its
    method's `methodNSignature` beside it, as extractions emit them. -/
elab "cil_body_decodes" : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  try evalTactic (← `(tactic| decide +kernel))
  catch kernelFailure =>
    let arguments := (target.getAppArgs[1]?.getD target).getAppArgs
    let some bodyName := arguments[0]?.bind (·.constName?)
      | throw kernelFailure
    let some typeArguments := arguments[2]?
      | throw kernelFailure
    let stem := bodyName.getString!
    let signatureName := Name.mkStr bodyName.getPrefix ((stem.dropEnd 4).toString ++ "Signature")
    let message ← unsafe evalExpr String (mkConst ``String)
      (mkAppN (mkConst ``describeBodyFailure)
        #[mkConst signatureName, arguments[0]!, arguments[1]!, typeArguments])
    throwError message

end CIL.Extraction
