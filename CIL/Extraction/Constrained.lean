import CIL.Extraction.Folds
import CIL.Extraction.FlowIndex
import Std.Data.TreeSet.Lemmas

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
private def selectedImplementation (methods : Nat → Option SpecializedMethod) (receiver : TypeExpr)
    (resolved : DispatchMethod) (emitted : Op) : Bool :=
  match emitted, namedType receiver with
  | .call index count, some (scope, name) => match methods index with
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
def constrainedSiteWindow (types : List DispatchType) (methods : Nat → Option SpecializedMethod)
    (current previous next : Option RawInstruction) (live nextLive : Option Bool)
    (emitted : Option Op) (targeted : Nat → Bool) (pc : Nat) : Bool :=
  if live != some true then true else
  match current with
  | some ⟨_, 65046, .type _⟩ =>
    (match emitted with | some .nop => true | _ => false) &&
      (next.map (·.opcode)) == some 111 && nextLive == some true
  | some ⟨_, 111, .call site⟩ =>
    if pc == 0 || targeted pc then false else
    match previous, emitted with
    | some ⟨_, 65046, .type receiver⟩, some emitted =>
      match resolveConstrained types receiver site with
      | some resolved => selectedImplementation methods receiver resolved emitted
      | none => false
    | _, _ => false
  | some ⟨_, 65046, _⟩ | some ⟨_, 111, _⟩ => false
  | _ => true

/-- The instruction window supplied through arbitrary optional lookup functions. -/
def constrainedSiteCheck (types : List DispatchType) (methods : Nat → Option SpecializedMethod)
    (rawAt : Nat → Option RawInstruction) (liveAt : Nat → Option Bool)
    (codeAt : Nat → Option Op) (targeted : Nat → Bool) (pc : Nat) : Bool :=
  constrainedSiteWindow types methods (rawAt pc) (rawAt (pc - 1)) (rawAt (pc + 1))
    (liveAt pc) (liveAt (pc + 1)) (codeAt pc) targeted pc

/-- The per-site rule stated with optional list lookups, including missing-neighbor rejection. -/
def constrainedSiteValid (types : List DispatchType) (methods : List SpecializedMethod)
    (raw : RawMethod) (reachable : List Bool) (code : List Op) (pc : Nat) : Bool :=
  constrainedSiteCheck types (methods[·]?) (raw.code[·]?) (reachable[·]?) (code[·]?)
    (fun target => raw.code.any (branchesTo target)) pc

/-- All decoded branch destinations, including switch arms and unreachable instructions. -/
def constrainedBranchTargets (raw : List RawInstruction) : List Nat :=
  raw.flatMap fun instruction => match instruction.operand with
    | .target target => [target]
    | .targets targets => targets
    | _ => []

/-- Collecting branch destinations preserves the rejection rule at every possible pc. -/
theorem constrainedBranchTargets_contains (raw : List RawInstruction) (pc : Nat) :
    (constrainedBranchTargets raw).contains pc = raw.any (branchesTo pc) := by
  induction raw with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction with
    | mk offset opcode operand =>
      change _ = (branchesTo pc ⟨offset, opcode, operand⟩ || rest.any (branchesTo pc))
      simp only [constrainedBranchTargets, List.flatMap_cons, List.contains_append]
      change (_ || (constrainedBranchTargets rest).contains pc) = _
      rw [ih]
      cases operand <;> simp [branchesTo, BEq.beq, eq_comm]

#print axioms constrainedBranchTargets_contains

/-- Traverse adjacent raw instructions and parallel state/code lists without positional lookup. -/
def constrainedSites (types : List DispatchType) (methods : Nat → Option SpecializedMethod)
    (targeted : Nat → Bool) : Nat → Option RawInstruction →
      List RawInstruction → List Bool → List Op → Bool
  | pc, previous, instruction :: raw, live :: states, emitted :: code =>
    constrainedSiteWindow types methods (some instruction) previous raw.head?
      (some live) states.head? (some emitted) targeted pc &&
        constrainedSites types methods targeted (pc + 1) (some instruction) raw states code
  | _, _, [], [], [] => true
  | _, _, _, _, _ => false

/-- Streaming windows agree with the indexed rule on equally long evidence suffixes. -/
theorem constrainedSites_eq (types : List DispatchType)
    (methods : Nat → Option SpecializedMethod) (targeted : Nat → Bool)
    (wholeRaw : List RawInstruction) (wholeStates : List Bool) (wholeCode : List Op)
    (raw : List RawInstruction) (states : List Bool) (code : List Op)
    (pc : Nat) (previous : Option RawInstruction)
    (rawSuffix : raw = wholeRaw.drop pc) (stateSuffix : states = wholeStates.drop pc)
    (codeSuffix : code = wholeCode.drop pc)
    (prior : previous = wholeRaw[pc - 1]?)
    (stateLength : raw.length = states.length) (codeLength : raw.length = code.length) :
    constrainedSites types methods targeted pc previous raw states code =
      (List.range' pc raw.length).all (constrainedSiteCheck types methods
        (wholeRaw[·]?) (wholeStates[·]?) (wholeCode[·]?) targeted) := by
  induction raw generalizing states code pc previous with
  | nil =>
    have statesEmpty : states = [] := List.length_eq_zero_iff.mp stateLength.symm
    have codeEmpty : code = [] := List.length_eq_zero_iff.mp codeLength.symm
    rw [statesEmpty, codeEmpty]
    rfl
  | cons instruction raw ih =>
    cases states with
    | nil => simp at stateLength
    | cons live states =>
      cases code with
      | nil => simp at codeLength
      | cons emitted code =>
        have rawTail : raw = wholeRaw.drop (pc + 1) := by
          simpa using congrArg List.tail rawSuffix
        have stateTail : states = wholeStates.drop (pc + 1) := by
          simpa using congrArg List.tail stateSuffix
        have codeTail : code = wholeCode.drop (pc + 1) := by
          simpa using congrArg List.tail codeSuffix
        have rawAt : wholeRaw[pc]? = some instruction := by
          simpa only [List.head?_cons, List.head?_drop] using
            (congrArg List.head? rawSuffix).symm
        have stateAt : wholeStates[pc]? = some live := by
          simpa only [List.head?_cons, List.head?_drop] using
            (congrArg List.head? stateSuffix).symm
        have codeAt : wholeCode[pc]? = some emitted := by
          simpa only [List.head?_cons, List.head?_drop] using
            (congrArg List.head? codeSuffix).symm
        simp only [constrainedSites, List.length_cons, List.range'_succ, List.all_cons]
        rw [ih states code (pc + 1) (some instruction) rawTail stateTail codeTail
          (by simpa using rawAt.symm) (by simpa using stateLength) (by simpa using codeLength)]
        congr 1
        simp only [constrainedSiteCheck, rawAt, stateAt, codeAt, prior,
          rawTail, stateTail, List.head?_drop]

#print axioms constrainedSites_eq
/-- Every reachable virtual call is statically resolved; no standalone prefix is admitted. -/
def ConstrainedCallsValid (types : List DispatchType) (methods : List SpecializedMethod)
    (raw : RawMethod) (reachable : List Bool) (emitted : Method) : Prop :=
  raw.code.length = reachable.length ∧ raw.code.length = emitted.code.length ∧
    constrainedSites types (FlowIndex.ofList methods).get?
      (Std.TreeSet.ofList (constrainedBranchTargets raw.code) compare).contains
      0 raw.code.head? raw.code reachable emitted.code = true

/-- Indexed validation is exactly the original per-pc rule, including malformed evidence. -/
theorem ConstrainedCallsValid_iff_original (types : List DispatchType)
    (methods : List SpecializedMethod) (raw : RawMethod) (reachable : List Bool)
    (emitted : Method) :
    ConstrainedCallsValid types methods raw reachable emitted ↔
      raw.code.length = reachable.length ∧ raw.code.length = emitted.code.length ∧
        (List.range raw.code.length).all
          (constrainedSiteValid types methods raw reachable emitted.code) = true := by
  unfold ConstrainedCallsValid
  by_cases stateLength : raw.code.length = reachable.length
  · by_cases codeLength : raw.code.length = emitted.code.length
    · rw [constrainedSites_eq types (FlowIndex.ofList methods).get?
        (Std.TreeSet.ofList (constrainedBranchTargets raw.code) compare).contains
        raw.code reachable emitted.code raw.code reachable emitted.code 0 raw.code.head?
        (by simp) (by simp) (by simp) (by simp [List.head?_eq_getElem?]) stateLength codeLength]
      have index : (FlowIndex.ofList methods).get? = (methods[·]?) := by
        funext pc
        exact FlowIndex.get?_ofList methods pc
      have targets : (Std.TreeSet.ofList (constrainedBranchTargets raw.code) compare).contains =
          (fun target => raw.code.any (branchesTo target)) := by
        funext pc
        rw [Std.TreeSet.contains_ofList, constrainedBranchTargets_contains]
      rw [index, targets, ← List.range_eq_range']
      rfl
    · simp [codeLength]
  · simp [stateLength]
#print axioms ConstrainedCallsValid_iff_original

instance (types : List DispatchType) (methods : List SpecializedMethod) (raw : RawMethod)
    (reachable : List Bool) (emitted : Method) :
    Decidable (ConstrainedCallsValid types methods raw reachable emitted) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Lower a constrained prefix or call using the immediately preceding raw instruction. -/
def lowerConstrainedInstruction (types : List DispatchType) (previous : Option RawInstruction)
    (instruction : RawInstruction) : RawInstruction :=
  match instruction with
  | ⟨offset, 65046, _⟩ => ⟨offset, 0, .none⟩
  | ⟨offset, 111, .call site⟩ =>
    match previous with
    | some ⟨_, 65046, .type receiver⟩ => match resolveConstrained types receiver site with
      | some target => ⟨offset, 40, .call { site with
          target := .managed target.token, declaringType := receiver }⟩
      | none => instruction
    | _ => instruction
  | _ => instruction

/-- Lower instructions in one pass, retaining the raw predecessor before rewriting it. -/
def lowerConstrainedCode (types : List DispatchType) :
    Option RawInstruction → List RawInstruction → List RawInstruction
  | _, [] => []
  | previous, instruction :: rest => lowerConstrainedInstruction types previous instruction ::
    lowerConstrainedCode types (some instruction) rest

/-- Streaming lowering agrees with positional predecessor lookup, including pc zero. -/
theorem lowerConstrainedCode_eq (types : List DispatchType) (whole raw : List RawInstruction)
    (pc : Nat) (previous : Option RawInstruction) (suffix : raw = whole.drop pc)
    (prior : previous = whole[pc - 1]?) :
    lowerConstrainedCode types previous raw = (raw.zipIdx pc).map (fun (instruction, position) =>
      lowerConstrainedInstruction types whole[position - 1]? instruction) := by
  induction raw generalizing pc previous with
  | nil => rfl
  | cons instruction raw ih =>
    have tail : raw = whole.drop (pc + 1) := by simpa using congrArg List.tail suffix
    have current : whole[pc]? = some instruction := by
      simpa only [List.head?_cons, List.head?_drop] using (congrArg List.head? suffix).symm
    simp only [lowerConstrainedCode, List.zipIdx_cons, List.map_cons]
    rw [prior, ih (pc + 1) (some instruction) tail (by simpa using current.symm)]

#print axioms lowerConstrainedCode_eq

/-- The direct-call view used by call-token checks after constrained-site validation.
    Raw specialization evidence retains its original opcodes and declared interface slots. -/
def lowerConstrainedRaw (types : List DispatchType) (raw : RawMethod) : RawMethod :=
  if !(raw.code.any fun instruction => instruction.opcode == 111 || instruction.opcode == 65046)
    then raw else
  { raw with code := lowerConstrainedCode types raw.code.head? raw.code }
/-- Streaming predecessor lookup preserves lowering even for malformed prefix sequences. -/
theorem lowerConstrainedRaw_eq_original (types : List DispatchType) (raw : RawMethod) :
    lowerConstrainedRaw types raw =
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
      | _ => instruction } := by
  simp only [lowerConstrainedRaw]
  split
  · rfl
  · rw [lowerConstrainedCode_eq types raw.code raw.code 0 raw.code.head?
      (by simp) (by simp [List.head?_eq_getElem?])]
    rfl

#print axioms lowerConstrainedRaw_eq_original

end CIL.Extraction
