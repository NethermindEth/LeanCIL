import CIL.Extraction.Dispatch

/-! Checked constrained-call instruction windows and direct-call lowering. -/

namespace CIL.Extraction

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
def constrainedSiteWindow (resolve : TypeExpr → CallSite → Option DispatchMethod)
    (methods : Nat → Option SpecializedMethod)
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
      match resolve receiver site with
      | some resolved => selectedImplementation methods receiver resolved emitted
      | none => false
    | _, _ => false
  | some ⟨_, 65046, _⟩ | some ⟨_, 111, _⟩ => false
  | _ => true

/-- The instruction window supplied through arbitrary optional lookup functions. -/
def constrainedSiteCheckWith (resolve : TypeExpr → CallSite → Option DispatchMethod)
    (methods : Nat → Option SpecializedMethod)
    (rawAt : Nat → Option RawInstruction) (liveAt : Nat → Option Bool)
    (codeAt : Nat → Option Op) (targeted : Nat → Bool) (pc : Nat) : Bool :=
  constrainedSiteWindow resolve methods (rawAt pc) (rawAt (pc - 1)) (rawAt (pc + 1))
    (liveAt pc) (liveAt (pc + 1)) (codeAt pc) targeted pc

/-- The original metadata-list rule presented through optional instruction lookups. -/
def constrainedSiteCheck (types : List DispatchType) :=
  constrainedSiteCheckWith (resolveConstrained types)
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
def constrainedSites (resolve : TypeExpr → CallSite → Option DispatchMethod)
    (methods : Nat → Option SpecializedMethod)
    (targeted : Nat → Bool) : Nat → Option RawInstruction →
      List RawInstruction → List Bool → List Op → Bool
  | pc, previous, instruction :: raw, live :: states, emitted :: code =>
    constrainedSiteWindow resolve methods (some instruction) previous raw.head?
      (some live) states.head? (some emitted) targeted pc &&
        constrainedSites resolve methods targeted (pc + 1) (some instruction) raw states code
  | _, _, [], [], [] => true
  | _, _, _, _, _ => false

/-- Streaming windows agree with the indexed rule on equally long evidence suffixes. -/
theorem constrainedSites_eq (resolve : TypeExpr → CallSite → Option DispatchMethod)
    (methods : Nat → Option SpecializedMethod) (targeted : Nat → Bool)
    (wholeRaw : List RawInstruction) (wholeStates : List Bool) (wholeCode : List Op)
    (raw : List RawInstruction) (states : List Bool) (code : List Op)
    (pc : Nat)
    (previous : Option RawInstruction)
    (rawSuffix : raw = wholeRaw.drop pc) (stateSuffix : states = wholeStates.drop pc)
    (codeSuffix : code = wholeCode.drop pc)
    (prior : previous = wholeRaw[pc - 1]?)
    (stateLength : raw.length = states.length) (codeLength : raw.length = code.length) :
    constrainedSites resolve methods targeted pc previous raw states code =
      (List.range' pc raw.length).all (constrainedSiteCheckWith resolve methods
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
        simp only [constrainedSiteCheckWith, rawAt, stateAt, codeAt, prior,
          rawTail, stateTail, List.head?_drop]

#print axioms constrainedSites_eq
/-- Every reachable virtual call is statically resolved; no standalone prefix is admitted. -/
def ConstrainedCallsValid (types : List DispatchType) (methods : List SpecializedMethod)
    (raw : RawMethod) (reachable : List Bool) (emitted : Method) : Prop :=
  raw.code.length = reachable.length ∧ raw.code.length = emitted.code.length ∧
    constrainedSites (DispatchIndex.ofTypes types).resolve (FlowIndex.ofList methods).get?
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
  have resolve : (DispatchIndex.ofTypes types).resolve = resolveConstrained types := by
    funext receiver site
    exact DispatchIndex.resolve_ofTypes types receiver site
  unfold ConstrainedCallsValid
  rw [resolve]
  by_cases stateLength : raw.code.length = reachable.length
  · by_cases codeLength : raw.code.length = emitted.code.length
    · rw [constrainedSites_eq (resolveConstrained types) (FlowIndex.ofList methods).get?
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
def lowerConstrainedInstruction (resolve : TypeExpr → CallSite → Option DispatchMethod)
    (previous : Option RawInstruction)
    (instruction : RawInstruction) : RawInstruction :=
  match instruction with
  | ⟨offset, 65046, _⟩ => ⟨offset, 0, .none⟩
  | ⟨offset, 111, .call site⟩ =>
    match previous with
    | some ⟨_, 65046, .type receiver⟩ => match resolve receiver site with
      | some target => ⟨offset, 40, .call { site with
          target := .managed target.token, declaringType := receiver }⟩
      | none => instruction
    | _ => instruction
  | _ => instruction

/-- Lower instructions in one pass, retaining the raw predecessor before rewriting it. -/
def lowerConstrainedCode (resolve : TypeExpr → CallSite → Option DispatchMethod) :
    Option RawInstruction → List RawInstruction → List RawInstruction
  | _, [] => []
  | previous, instruction :: rest => lowerConstrainedInstruction resolve previous instruction ::
    lowerConstrainedCode resolve (some instruction) rest

/-- Streaming lowering agrees with positional predecessor lookup, including pc zero. -/
theorem lowerConstrainedCode_eq (resolve : TypeExpr → CallSite → Option DispatchMethod)
    (whole raw : List RawInstruction)
    (pc : Nat)
    (previous : Option RawInstruction) (suffix : raw = whole.drop pc)
    (prior : previous = whole[pc - 1]?) :
    lowerConstrainedCode resolve previous raw = (raw.zipIdx pc).map (fun (instruction, position) =>
      lowerConstrainedInstruction resolve whole[position - 1]? instruction) := by
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
  { raw with code :=
      lowerConstrainedCode (DispatchIndex.ofTypes types).resolve raw.code.head? raw.code }
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
  have resolve : (DispatchIndex.ofTypes types).resolve = resolveConstrained types := by
    funext receiver site
    exact DispatchIndex.resolve_ofTypes types receiver site
  simp only [lowerConstrainedRaw, resolve]
  split
  · rfl
  · rw [lowerConstrainedCode_eq (resolveConstrained types) raw.code raw.code 0 raw.code.head?
      (by simp) (by simp [List.head?_eq_getElem?])]
    rfl

#print axioms lowerConstrainedRaw_eq_original

end CIL.Extraction
