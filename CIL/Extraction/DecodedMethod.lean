import CIL.Extraction.ValueDecoding
import CIL.Extraction.Translation

/-!
# Methods decoded from raw definitions

`Method.ofRaw?` gives the method a raw definition denotes at its type arguments: each
instruction of the instantiated definition as `Instruction.ofRaw?` decodes it, so a type test
names the type argument, and the frame, homes and signature from the same definition.
`Method.ofBody?` reads the code and init flag from pinned body bytes instead of the definition,
and `decodedProgram?` applies it to every evidence record.
`Method.ofBody?_of_decodes` shows that for a definition whose body check passes, the method of
the bytes is the method of the definition, so a proof about the decoded program needs no
translator output.
-/

namespace CIL.Extraction

/-- The method a raw definition denotes at `arguments`: each instruction of its instantiated
    code as `Instruction.ofRaw?` decodes it, frame and signature from the same definition,
    homes over every pc, and no static sites, opaque vector locals or links. `none` when an
    instruction, the instantiation or a local type has no decoding. -/
def _root_.CIL.Method.ofRaw? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (source : RawMethod) (arguments : List TypeExpr) : Option Method := do
  let closed ← instantiateMethod environment.rawLayouts source arguments
  let storage ← closedArguments environment.rawLayouts closed
  let code ← closed.code.mapM Instruction.ofRaw?
  let localKinds ← storage.locals.mapM (storageKind environment.layouts)
  let parameterHomes ←
    expectedHomes environment.layouts storage (storage.code.map fun _ => true)
  return {
    profile := profile, code := code, localKinds := localKinds,
    locals := localKinds.map (LocalKind.initialValue source.initLocals),
    parameterHomes := parameterHomes, declared := DeclaredSignature.ofRaw closed,
    environment := environment, returnsValue := closed.returnType != .void }

/-- The method pinned body bytes denote: `checkBody` checks the definition's metadata, and the
    code and init flag are the ones decoded from the bytes. -/
def _root_.CIL.Method.ofBody? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (body : BodyEvidence) (original : RawMethod) (arguments : List TypeExpr) :
    Option Method := do
  let decoded ← (checkBody body original arguments).toOption
  Method.ofRaw? profile environment
    { original with code := decoded.code, initLocals := decoded.initLocals } arguments

/-- The program the evidence's body bytes denote, method by method. -/
def decodedProgram? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (evidence : List MethodEvidence) : Option Program :=
  evidence.mapM fun item =>
    Method.ofBody? profile environment item.body item.original item.arguments

/-- A body that decodes to `method` passes `checkBody` with the method's own code and init flag. -/
theorem BodyDecodes.code {pins : List AssemblyPin} {pin : AssemblyPin} {body : BodyEvidence}
    {method : RawMethod} {arguments : List TypeExpr} {signature : String}
    (decodes : BodyDecodes pins pin body method arguments signature) :
    ∃ decoded, checkBody body method arguments = .ok decoded ∧
      decoded.code = method.code ∧ decoded.initLocals = method.initLocals := by
  have matched := decodes.2.2.2.2.2.2
  unfold bodyMatches at matched
  split at matched
  · next decoded checks =>
    simp only [Bool.and_eq_true, beq_iff_eq] at matched
    exact ⟨decoded, checks, matched.2, matched.1.2⟩
  · exact absurd matched Bool.false_ne_true

#print axioms BodyDecodes.code

/-- For a body that decodes to `original`, the method of the bytes is the method of the
    definition. -/
theorem _root_.CIL.Method.ofBody?_of_decodes {pins : List AssemblyPin} {pin : AssemblyPin}
    {body : BodyEvidence} {original : RawMethod} {arguments : List TypeExpr}
    {signature : String} {profile : FeatureProfile} {environment : LayoutEnvironment}
    (decodes : BodyDecodes pins pin body original arguments signature) :
    Method.ofBody? profile environment body original arguments =
      Method.ofRaw? profile environment original arguments := by
  obtain ⟨decoded, checks, sameCode, sameInit⟩ := BodyDecodes.code decodes
  unfold Method.ofBody?
  rw [checks]
  show Method.ofRaw? profile environment
    { original with code := decoded.code, initLocals := decoded.initLocals } arguments = _
  rw [sameCode, sameInit]

#print axioms Method.ofBody?_of_decodes

end CIL.Extraction
