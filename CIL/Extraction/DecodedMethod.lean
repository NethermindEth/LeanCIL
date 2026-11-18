import CIL.Extraction.ValueDecoding
import CIL.Extraction.Translation
import CIL.Extraction.Prefixes

/-!
# Methods decoded from raw definitions

`Method.ofRaw?` gives the method a raw definition denotes at its type arguments: each
instruction of the instantiated definition as `Instruction.ofRaw` decodes it after the
instruction before it, a hole where no family admits the opcode yet, a type test naming the
type argument, a field access naming the
instantiated field, a call or construction naming the instantiated method, the frame, homes and
signature from the same definition, and the link table the extraction states, which the call
check ties to each raw site.
`Method.ofBody?` reads the code and init flag from pinned body bytes instead of the definition,
and `decodedProgram?` applies it to every evidence record.
`Method.ofBody?_of_decodes` shows that for a definition whose body check passes, the method of
the bytes is the method of the definition, so a proof about the decoded program needs no
translator output.
-/

namespace CIL.Extraction

/-- The method denoted by a closed definition and its argument storage. Its code contains
    one decoded instruction per raw site. The frame requires supported local kinds, valid
    parameter homes and argument accesses, and valid prefix sequences. -/
def _root_.CIL.Method.ofClosed? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (closed : RawMethod) (storage : RawArguments) :
    Option Method := do
  let code := Instruction.ofRawCode none closed.code
  let localKinds ← storage.locals.mapM (storageKind environment.layouts)
  let reachable := storage.code.map fun _ => true
  let parameterHomes ← expectedHomes environment.layouts storage reachable
  -- An argument instruction outside the declared arguments has no frame slot or incoming value.
  let homes := requiredHomeIndices storage reachable
  unless rawPrefixesValid closed.returnType closed.code &&
      argumentInstructionsValid storage homes reachable code do none
  return {
    profile := profile, code := code, localKinds := localKinds,
    locals := localKinds.map (LocalKind.initialValue closed.initLocals),
    parameterHomes := parameterHomes, declared := DeclaredSignature.ofRaw closed,
    environment := environment, links := links, returnsValue := closed.returnType != .void }

/-- The method a raw definition denotes at its type arguments, with the supplied link table. -/
def _root_.CIL.Method.ofRaw? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (source : RawMethod) (arguments : List TypeExpr) :
    Option Method := do
  let closed ← instantiateMethod environment.rawLayouts source arguments
  let storage ← closedArguments environment.rawLayouts closed
  Method.ofClosed? profile environment links closed storage

/-- A validated specialization gives the closed definition and storage for raw decoding. -/
theorem SpecializationValid.ofRaw?_eq_ofClosed? {environment : LayoutEnvironment}
    {source closed : RawMethod} {arguments : List TypeExpr} {storage : RawArguments}
    (valid : SpecializationValid environment.rawLayouts source arguments closed storage)
    (profile : FeatureProfile) (links : List (Nat × Link)) :
    Method.ofRaw? profile environment links source arguments =
      Method.ofClosed? profile environment links closed storage := by
  simp only [Method.ofRaw?, valid.1, valid.2, bind, Option.bind]

#print axioms SpecializationValid.ofRaw?_eq_ofClosed?

/-- The method pinned body bytes denote with link table `links`: `checkBody` checks the
    definition's metadata, and the code and init flag are the ones decoded from the bytes. -/
def _root_.CIL.Method.ofBody? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (body : BodyEvidence) (original : RawMethod)
    (arguments : List TypeExpr) : Option Method := do
  let decoded ← (checkBody body original arguments).toOption
  Method.ofRaw? profile environment links
    { original with code := decoded.code, initLocals := decoded.initLocals } arguments

/-- The program the evidence's body bytes denote, method by method, each with the links its
    evidence record states. -/
def decodedProgram? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (evidence : List MethodEvidence) : Option Program :=
  evidence.mapM fun item =>
    Method.ofBody? profile environment item.links item.body item.original item.arguments

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
    exact ⟨decoded, checks, matched.1.2, matched.1.1.2⟩
  · exact absurd matched Bool.false_ne_true

#print axioms BodyDecodes.code

/-- No branch of a method whose body decodes enters the instruction after a prefix. -/
theorem BodyDecodes.prefixEntryFree {pins : List AssemblyPin} {pin : AssemblyPin}
    {body : BodyEvidence} {method : RawMethod} {arguments : List TypeExpr} {signature : String}
    (decodes : BodyDecodes pins pin body method arguments signature) :
    PrefixEntryFree method.code := by
  obtain ⟨decoded, checks, sameCode, _⟩ := BodyDecodes.code decodes
  exact sameCode ▸ checkBody_prefixEntryFree checks

#print axioms BodyDecodes.prefixEntryFree

/-- The closed code of a method's evidence has no branch into the instruction after a prefix:
    its body decodes, and instantiation keeps every opcode and branch destination. -/
theorem MethodEvidenceValid.prefixEntryFree {rawLayouts : List RawLayout}
    {layouts : Array ComputedLayout} {pins : List AssemblyPin} {all : List MethodEvidence}
    {imports : List ImportSlot} {item : MethodEvidence} {method : Method}
    (valid : MethodEvidenceValid rawLayouts layouts pins all imports item method) :
    PrefixEntryFree item.closed.code := by
  obtain ⟨specialized, -, -, -, -, -, -, -, -, -, -, -, -, -, decodes, -, -⟩ := valid
  exact instantiateMethod_prefixEntryFree specialized.1 decodes.prefixEntryFree

#print axioms MethodEvidenceValid.prefixEntryFree

/-- The instantiated code of a definition whose body the check accepts, read from that body,
    has no branch into the instruction after a prefix. -/
theorem checkBody_instantiated_prefixEntryFree {layouts : List RawLayout} {body : BodyEvidence}
    {original closed : RawMethod} {arguments : List TypeExpr} {decoded : DecodedBody}
    (checked : checkBody body original arguments = .ok decoded)
    (instantiated : instantiateMethod layouts
      { original with code := decoded.code, initLocals := decoded.initLocals } arguments =
        some closed) :
    PrefixEntryFree closed.code :=
  instantiateMethod_prefixEntryFree instantiated (checkBody_prefixEntryFree checked)

#print axioms checkBody_instantiated_prefixEntryFree

/-- For a body that decodes to `original`, the method of the bytes is the method of the
    definition. -/
theorem _root_.CIL.Method.ofBody?_of_decodes {pins : List AssemblyPin} {pin : AssemblyPin}
    {body : BodyEvidence} {original : RawMethod} {arguments : List TypeExpr}
    {signature : String} {profile : FeatureProfile} {environment : LayoutEnvironment}
    {links : List (Nat × Link)}
    (decodes : BodyDecodes pins pin body original arguments signature) :
    Method.ofBody? profile environment links body original arguments =
      Method.ofRaw? profile environment links original arguments := by
  obtain ⟨decoded, checks, sameCode, sameInit⟩ := BodyDecodes.code decodes
  unfold Method.ofBody?
  rw [checks]
  show Method.ofRaw? profile environment links
    { original with code := decoded.code, initLocals := decoded.initLocals } arguments = _
  rw [sameCode, sameInit]

#print axioms Method.ofBody?_of_decodes

/-- Closed decoding preserves exactly the instruction list decoded from the closed body. -/
theorem _root_.CIL.Method.ofClosed?_code {profile : FeatureProfile}
    {environment : LayoutEnvironment} {links : List (Nat × Link)} {closed : RawMethod}
    {storage : RawArguments} {method : Method}
    (decoded : Method.ofClosed? profile environment links closed storage = some method) :
    method.code = Instruction.ofRawCode none closed.code := by
  unfold Method.ofClosed? at decoded
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at decoded
  obtain ⟨_, _, _, _, built⟩ := decoded
  split at built
  · cases built
    rfl
  · simp at built

#print axioms Method.ofClosed?_code

/-- Each pc of a decoded method holds what `Instruction.ofRawAt` decodes at that pc of the
    instantiated definition's code, so the method has one instruction per raw instruction and a
    type test names the type argument and a field access the instantiated field. -/
theorem _root_.CIL.Method.ofRaw?_code {profile : FeatureProfile}
    {environment : LayoutEnvironment} {links : List (Nat × Link)} {source : RawMethod}
    {arguments : List TypeExpr} {method : Method}
    (decoded : Method.ofRaw? profile environment links source arguments = some method) :
    ∃ closed, instantiateMethod environment.rawLayouts source arguments = some closed ∧
      ∀ pc, method.code[pc]? = Instruction.ofRawAt closed.code pc := by
  unfold Method.ofRaw? at decoded
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at decoded
  obtain ⟨closed, instantiated, _, _, built⟩ := decoded
  refine ⟨closed, instantiated, fun pc => ?_⟩
  rw [Method.ofClosed?_code built, Instruction.ofRawCode_getElem?]

#print axioms Method.ofRaw?_code

end CIL.Extraction
