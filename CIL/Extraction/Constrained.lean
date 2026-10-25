import CIL.Extraction.Folds

/-! # Concrete constrained-call resolution from decoded type and method metadata -/

namespace CIL.Extraction

/-- A declared method and its explicit interface-slot overrides, before dispatch resolution. -/
structure DispatchMethod where
  token : Nat
  name : String
  hasThis : Bool
  isPublic : Bool
  isAbstract : Bool
  isVirtual : Bool
  hasBody : Bool
  genericArity : Nat
  explicitThis : Bool
  callingConvention : Nat
  attributes : Nat
  implementation : Nat
  returnType : TypeExpr
  parameters : List TypeExpr
  overrides : List Nat
  deriving DecidableEq, Repr

/-- Direct interfaces and declared methods of one metadata type; no inherited dispatch table. -/
structure DispatchType where
  identity : TypeExpr
  valueType : Bool
  interfaceType : Bool
  interfaces : List TypeExpr
  methods : List DispatchMethod
  deriving DecidableEq, Repr

/-- Ambiguous metadata never selects an arbitrary first candidate. -/
private def unique : List α → Option α
  | [value] => some value
  | _ => none

/-- The signature must agree before a method can implement the declared slot. -/
private def signatureMatches (method : DispatchMethod) (site : CallSite) : Bool :=
  method.hasThis && !method.explicitThis && method.callingConvention == 0 &&
    method.genericArity == 0 && method.returnType == site.returnType &&
    (method.returnType != .void) == site.returnsValue &&
    method.parameters == site.parameterTypes && method.parameters.length == site.parameterCount

/-- Restrict both sides of dispatch to one assembly identity. -/
private def sameScope (left right : TypeExpr) : Bool :=
  match namedType left, namedType right with
  | some (scope, _), some (other, _) => scope == other
  | _, _ => false

/-- Resolve a concrete value-type method or a directly implemented interface slot.
    Explicit overrides take precedence; missing, ambiguous and boxing cases fail. -/
def resolveConstrained (types : List DispatchType) (receiver : TypeExpr) (site : CallSite) :
    Option DispatchMethod := do
  let .aggregate .. := receiver | none
  if !site.hasThis || !site.typeArguments.isEmpty || !sameScope receiver site.declaringType then
    none else pure ()
  let .managed token := site.target | none
  let concrete ← unique (types.filter fun type => type.identity == receiver)
  if !concrete.valueType || concrete.interfaceType then none else pure ()
  let declaring ← unique (types.filter fun type => type.identity == site.declaringType)
  let slot ← unique (declaring.methods.filter fun method => method.token == token)
  if slot.name != site.name || !signatureMatches slot site then none else pure ()
  let target ← if receiver == declaring.identity then some slot else do
    if !declaring.interfaceType || !slot.isAbstract || !slot.isVirtual ||
        !concrete.interfaces.contains declaring.identity then none else pure ()
    let explicit := concrete.methods.filter fun method => method.overrides.contains token
    unique (if explicit.isEmpty then concrete.methods.filter fun method =>
      method.isPublic && method.name == slot.name && signatureMatches method site else explicit)
  if target.isAbstract || !target.hasBody || target.name ∈ [".ctor", ".cctor"] ||
      !signatureMatches target site then none else some target

/-- A branch cannot enter the call after skipping its constrained prefix. -/
private def branchesTo (pc : Nat) (instruction : RawInstruction) : Bool :=
  match instruction.operand with
  | .target target => target == pc
  | .targets targets => targets.contains pc
  | _ => false

/-- The selected program entry must be precisely the resolved struct implementation. -/
private def selectedImplementation (methods : List SpecializedMethod) (receiver : TypeExpr)
    (resolved : DispatchMethod) (emitted : Op) : Bool :=
  match emitted, namedType receiver with
  | .call index count, some (scope, name) => match methods[index]? with
    | none => false
    | some method =>
      method.arguments.isEmpty && method.closed.token == resolved.token &&
      method.closed.owner == String.ofList scope ++ "::" ++ String.ofList name &&
      method.closed.hasThis && !method.closed.explicitThis &&
      method.closed.callingConvention == 0 && method.closed.genericParameters.isEmpty &&
      !method.closed.code.isEmpty && method.closed.attributes == resolved.attributes &&
      method.closed.implementation == resolved.implementation &&
      method.closed.returnType == resolved.returnType &&
      method.closed.parameters == resolved.parameters && count == resolved.parameters.length + 1
  | _, _ => false

/-- Check prefix adjacency, branch integrity, metadata resolution and the emitted target. -/
def constrainedSiteValid (types : List DispatchType) (methods : List SpecializedMethod)
    (raw : RawMethod) (reachable : List Bool) (code : List Op) (pc : Nat) : Bool :=
  if reachable[pc]? != some true then true else
  match raw.code[pc]? with
  | some ⟨_, 65046, .type _⟩ =>
    (match code[pc]? with | some .nop => true | _ => false) &&
      (raw.code[pc + 1]?.map (·.opcode)) == some 111 && reachable[pc + 1]? == some true
  | some ⟨_, 111, .call site⟩ =>
    if pc == 0 || raw.code.any (branchesTo pc) then false else
    match raw.code[pc - 1]?, code[pc]? with
    | some ⟨_, 65046, .type receiver⟩, some emitted =>
      match resolveConstrained types receiver site with
      | some resolved => selectedImplementation methods receiver resolved emitted
      | none => false
    | _, _ => false
  | some ⟨_, 65046, _⟩ | some ⟨_, 111, _⟩ => false
  | _ => true

/-- Every reachable virtual call is statically resolved; no standalone prefix is admitted. -/
def ConstrainedCallsValid (types : List DispatchType) (methods : List SpecializedMethod)
    (raw : RawMethod) (reachable : List Bool) (emitted : Method) : Prop :=
  raw.code.length = reachable.length ∧ raw.code.length = emitted.code.length ∧
    (List.range raw.code.length).all
      (constrainedSiteValid types methods raw reachable emitted.code) = true

instance (types : List DispatchType) (methods : List SpecializedMethod) (raw : RawMethod)
    (reachable : List Bool) (emitted : Method) :
    Decidable (ConstrainedCallsValid types methods raw reachable emitted) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The direct-call view used by existing call-token checks after constrained-site validation.
    Raw specialization evidence keeps the original opcodes and declared interface slots. -/
def lowerConstrainedRaw (types : List DispatchType) (raw : RawMethod) : RawMethod :=
  if !(raw.code.any fun instruction => instruction.opcode == 111 || instruction.opcode == 65046)
    then raw else
  { raw with code := raw.code.zipIdx.map fun (instruction, pc) =>
    match instruction with
    | ⟨offset, 65046, _⟩ => ⟨offset, 0, .none⟩
    | ⟨offset, 111, .call site⟩ =>
      match raw.code[pc - 1]? with
      | some ⟨_, 65046, .type receiver⟩ => match resolveConstrained types receiver site with
        | some target => ⟨offset, 40, .call { site with
            target := .managed target.token, declaringType := receiver }⟩
        | none => instruction
      | _ => instruction
    | _ => instruction }

end CIL.Extraction
