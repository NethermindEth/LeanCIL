import CIL.Extraction.Dispatch
import CIL.Extraction.FeatureEffects
import CIL.Extraction.Prefixes

/-! Checked constrained-call instruction windows and direct-call lowering. -/

namespace CIL.Extraction

/-- The emitted call names the site's method under a `constrained.` prefix on `receiver`, and the
    program entry its link selects is precisely the resolved target, declared by its closed owner
    and instantiated at the site's method type arguments, with a receiver argument exactly when
    the target is an instance method. -/
private def selectedImplementation (methods : Nat → Option SpecializedMethod) (receiver : TypeExpr)
    (site : CallSite) (target : ConstrainedTarget) (emitted : Instruction) (link : Option Link) :
    Bool :=
  let resolved := target.method
  let arguments := siteMethodArguments site
  match emitted, link, namedType (ownerBase (target.declaringType receiver)) with
  | .call method prefixes, some (.direct index), some (scope, name) =>
    let count := method.argumentCount
    method == site.method && prefixes.constrained == some receiver && !prefixes.tail &&
    match methods index with
    | none => false
    | some method =>
      method.arguments == arguments ++ resolved.ownerArguments &&
      method.closed.token == resolved.token &&
      method.closed.ownerArgumentCount == resolved.ownerArguments.length &&
      method.closed.owner == String.ofList scope ++ "::" ++ String.ofList name &&
      method.closed.hasThis == resolved.hasThis && !method.closed.explicitThis &&
      method.closed.callingConvention == 0 && method.closed.genericParameters.isEmpty &&
      !method.closed.code.isEmpty && method.closed.attributes == resolved.attributes &&
      method.closed.implementation == resolved.implementation &&
      substituteType arguments resolved.returnType == some method.closed.returnType &&
      resolved.parameters.mapM (substituteType arguments) == some method.closed.parameters &&
      count == resolved.parameters.length + (if resolved.hasThis then 1 else 0)
  | _, _, _ => false

/-- Check prefix adjacency, branch integrity, metadata resolution and the emitted target, and
    that a type test comes from `castclass` or `isinst` against a `castable` class. -/
def constrainedSiteWindow (resolve : TypeExpr → CallSite → Option ConstrainedTarget)
    (virtualValid : CallSite → List (TypeExpr × Nat) → Nat → Bool) (castable : TypeExpr → Bool)
    (methods : Nat → Option SpecializedMethod)
    (current previous next : Option RawInstruction) (live nextLive : Option Bool)
    (emitted : Option Instruction) (link : Option Link) (targeted : Nat → Bool) (pc : Nat) :
    Bool :=
  if live != some true then true else
  -- A type test stays in the opcode it lowers, against a class its lineage decides.
  if let some (opcode, type) := emitted.bind typeTestSource then
    castable type && current.any fun instruction => instruction.opcode == opcode else
  match current with
  | some ⟨_, 65046, .type _⟩ =>
    (match emitted with | some .nop => true | _ => false) &&
      (match next with
        | some ⟨_, opcode, .call site⟩ => opcode == constrainedCallOpcode site
        | _ => false) && nextLive == some true
  | some ⟨_, 111, .call site⟩ =>
    match previous, emitted with
    | some ⟨_, 65046, .type receiver⟩, some emitted =>
      if pc == 0 || targeted pc || !site.hasThis then false else
      match resolve receiver site with
      | some resolved => selectedImplementation methods receiver site resolved emitted link
      | none => false
    -- Unprefixed, only a receiver-checked call, whose target the managed-call rule binds, or a
    -- virtual call whose table re-resolves against the catalog.
    | _, some (.callvirt method) => site.hasThis && method == site.method && match link with
      | some (.direct _) => true
      | some (.virtual targets) => virtualValid site targets method.argumentCount
      | _ => false
    | _, _ => false
  | some ⟨_, 40, .call site⟩ =>
    match previous with
    | some ⟨_, 65046, .type receiver⟩ =>
      if pc == 0 || targeted pc || site.hasThis then false else
      match emitted, resolve receiver site with
      | some emitted, some resolved =>
        selectedImplementation methods receiver site resolved emitted link
      | _, _ => false
    -- Unprefixed, a call carries no constrained type.
    | _ => match emitted with
      | some (.call _ prefixes) => prefixes.constrained.isNone
      | _ => true
  | some ⟨_, 65046, _⟩ | some ⟨_, 111, _⟩ => false
  | _ => true

/-- The window reads branch entry only at its own pc, and only after a `constrained.` prefix past
    the first pc, so any other target lookup agrees with it there. -/
theorem constrainedSiteWindow_unentered (resolve : TypeExpr → CallSite → Option ConstrainedTarget)
    (virtualValid : CallSite → List (TypeExpr × Nat) → Nat → Bool) (castable : TypeExpr → Bool)
    (methods : Nat → Option SpecializedMethod)
    (current previous next : Option RawInstruction) (live nextLive : Option Bool)
    (emitted : Option Instruction) (link : Option Link) (targeted other : Nat → Bool) (pc : Nat)
    (unentered : pc = 0 ∨ targeted pc = other pc ∨ previous.any (·.opcode == 65046) = false) :
    constrainedSiteWindow resolve virtualValid castable methods current previous next live nextLive
        emitted link targeted pc =
      constrainedSiteWindow resolve virtualValid castable methods current previous next live
        nextLive emitted link other pc := by
  unfold constrainedSiteWindow
  rcases unentered with rfl | agrees | unprefixed
  · repeat' split
    all_goals simp_all
  · simp only [agrees]
  · repeat' split
    all_goals simp_all

#print axioms constrainedSiteWindow_unentered

/-- A call the rule accepts at a live pc after a `constrained.` prefix has no branch entering
    it. -/
theorem constrainedSiteWindow_untargeted
    (resolve : TypeExpr → CallSite → Option ConstrainedTarget)
    (virtualValid : CallSite → List (TypeExpr × Nat) → Nat → Bool) (castable : TypeExpr → Bool)
    (methods : Nat → Option SpecializedMethod) (prefixOffset callOffset : Nat)
    (receiver : TypeExpr) (opcode : Nat) (site : CallSite) (next : Option RawInstruction)
    (nextLive : Option Bool) (emitted : Option Instruction) (link : Option Link)
    (targeted : Nat → Bool) (pc : Nat) (call : opcode = 111 ∨ opcode = 40)
    (accepted : constrainedSiteWindow resolve virtualValid castable methods
      (some ⟨callOffset, opcode, .call site⟩) (some ⟨prefixOffset, 65046, .type receiver⟩) next
      (some true) nextLive emitted link targeted pc = true) :
    targeted pc = false := by
  have typeTest : ∀ instruction opcode type, typeTestSource instruction = some (opcode, type) →
      opcode = 116 ∨ opcode = 117 := by
    intro instruction opcode type found
    cases instruction <;> simp only [typeTestSource, Option.some.injEq, Prod.mk.injEq,
      reduceCtorEq] at found
    · exact .inl found.1.symm
    · exact .inr found.1.symm
  unfold constrainedSiteWindow at accepted
  cases tested : emitted.bind typeTestSource with
  | some test =>
    rcases emitted with _ | instruction
    · simp at tested
    have := typeTest instruction test.1 test.2 (by simpa using tested)
    simp [tested] at accepted
    omega
  | none =>
    rcases call with rfl | rfl <;> simp only [tested] at accepted
    all_goals (repeat' split at accepted)
    all_goals simp_all

#print axioms constrainedSiteWindow_untargeted

/-- The instruction window supplied through arbitrary optional lookup functions. -/
def constrainedSiteCheckWith (resolve : TypeExpr → CallSite → Option ConstrainedTarget)
    (virtualValid : CallSite → List (TypeExpr × Nat) → Nat → Bool) (castable : TypeExpr → Bool)
    (methods : Nat → Option SpecializedMethod)
    (rawAt : Nat → Option RawInstruction) (liveAt : Nat → Option Bool)
    (codeAt : Nat → Option Instruction) (linkAt : Nat → Option Link) (targeted : Nat → Bool)
    (pc : Nat) : Bool :=
  constrainedSiteWindow resolve virtualValid castable methods (rawAt pc) (rawAt (pc - 1))
    (rawAt (pc + 1)) (liveAt pc) (liveAt (pc + 1)) (codeAt pc) (linkAt pc) targeted pc

/-- In a body where no branch enters the instruction after a prefix, the constrained rule's
    branch-entry checks refuse nothing, so it accepts what it accepts with no branch targets. -/
theorem constrainedSiteCheckWith_prefixEntryFree
    (resolve : TypeExpr → CallSite → Option ConstrainedTarget)
    (virtualValid : CallSite → List (TypeExpr × Nat) → Nat → Bool) (castable : TypeExpr → Bool)
    (methods : Nat → Option SpecializedMethod) {code : List RawInstruction}
    (free : PrefixEntryFree code) (liveAt : Nat → Option Bool)
    (codeAt : Nat → Option Instruction) (linkAt : Nat → Option Link) (pc : Nat) :
    constrainedSiteCheckWith resolve virtualValid castable methods (code[·]?) liveAt codeAt linkAt
        (fun target => code.any (branchesTo target)) pc =
      constrainedSiteCheckWith resolve virtualValid castable methods (code[·]?) liveAt codeAt
        linkAt (fun _ => false) pc := by
  unfold constrainedSiteCheckWith
  apply constrainedSiteWindow_unentered
  rcases pc with _ | previousPc
  · exact .inl rfl
  · have constrainedPrefix : isPrefixOpcode 65046 = true := by decide
    simp only [Nat.add_sub_cancel]
    cases previous : code[previousPc]? with
    | none => exact .inr (.inr (by simp))
    | some before =>
      by_cases constrained : before.opcode = 65046
      · exact .inr (.inl (free previousPc before previous (constrained ▸ constrainedPrefix)))
      · exact .inr (.inr (by simp [constrained]))

#print axioms constrainedSiteCheckWith_prefixEntryFree

/-- The original metadata-list rule presented through optional instruction lookups. -/
def constrainedSiteCheck (types : List DispatchType) (methods : Nat → Option SpecializedMethod) :=
  constrainedSiteCheckWith (resolveConstrained types)
    (virtualTableValid types (findDispatchType types) methods)
    (castTargetValid (findDispatchType types)) methods
/-- The per-site rule stated with optional list lookups, including missing-neighbor rejection. -/
def constrainedSiteValid (types : List DispatchType) (methods : List SpecializedMethod)
    (raw : RawMethod) (reachable : List Bool) (emitted : Method) (pc : Nat) : Bool :=
  constrainedSiteCheck types (methods[·]?) (raw.code[·]?) (reachable[·]?) (emitted.code[·]?)
    emitted.linkAt (fun target => raw.code.any (branchesTo target)) pc

/-- Traverse adjacent raw instructions and parallel state/code lists without positional lookup. -/
def constrainedSites (resolve : TypeExpr → CallSite → Option ConstrainedTarget)
    (virtualValid : CallSite → List (TypeExpr × Nat) → Nat → Bool) (castable : TypeExpr → Bool)
    (methods : Nat → Option SpecializedMethod) (linkAt : Nat → Option Link)
    (targeted : Nat → Bool) : Nat → Option RawInstruction →
      List RawInstruction → List Bool → List Instruction → Bool
  | pc, previous, instruction :: raw, live :: states, emitted :: code =>
    constrainedSiteWindow resolve virtualValid castable methods (some instruction) previous
      raw.head? (some live) states.head? (some emitted) (linkAt pc) targeted pc &&
        constrainedSites resolve virtualValid castable methods linkAt targeted (pc + 1)
          (some instruction) raw states code
  | _, _, [], [], [] => true
  | _, _, _, _, _ => false

/-- Streaming windows agree with the indexed rule on equally long evidence suffixes. -/
theorem constrainedSites_eq (resolve : TypeExpr → CallSite → Option ConstrainedTarget)
    (virtualValid : CallSite → List (TypeExpr × Nat) → Nat → Bool) (castable : TypeExpr → Bool)
    (methods : Nat → Option SpecializedMethod) (linkAt : Nat → Option Link)
    (targeted : Nat → Bool) (wholeRaw : List RawInstruction) (wholeStates : List Bool)
    (wholeCode : List Instruction)
    (raw : List RawInstruction) (states : List Bool) (code : List Instruction)
    (pc : Nat)
    (previous : Option RawInstruction)
    (rawSuffix : raw = wholeRaw.drop pc) (stateSuffix : states = wholeStates.drop pc)
    (codeSuffix : code = wholeCode.drop pc)
    (prior : previous = wholeRaw[pc - 1]?)
    (stateLength : raw.length = states.length) (codeLength : raw.length = code.length) :
    constrainedSites resolve virtualValid castable methods linkAt targeted pc previous raw states
        code =
      (List.range' pc raw.length).all
        (constrainedSiteCheckWith resolve virtualValid castable methods
          (wholeRaw[·]?) (wholeStates[·]?) (wholeCode[·]?) linkAt targeted) := by
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
/-- Every reachable virtual call is statically resolved; no standalone prefix is admitted. A
    `call` names the body its pc's link gives, read through one index of the link table. -/
def ConstrainedCallsValid (types : List DispatchType) (methods : List SpecializedMethod)
    (raw : RawMethod) (reachable : List Bool) (emitted : Method) : Prop :=
  raw.code.length = reachable.length ∧ raw.code.length = emitted.code.length ∧
    constrainedSites (DispatchIndex.ofTypes types).resolve
      (virtualTableValid types
        (fun identity => ((DispatchIndex.ofTypes types).findType identity).map (·.raw))
        (FlowIndex.ofList methods).get?)
      (castTargetValid fun identity =>
        ((DispatchIndex.ofTypes types).findType identity).map (·.raw))
      (FlowIndex.ofList methods).get? (linkIndex emitted)
      (Std.TreeSet.ofList (branchTargets raw.code) compare).contains
      0 raw.code.head? raw.code reachable emitted.code = true

/-- Indexed validation is exactly the original per-pc rule, including malformed evidence. -/
theorem ConstrainedCallsValid_iff_original (types : List DispatchType)
    (methods : List SpecializedMethod) (raw : RawMethod) (reachable : List Bool)
    (emitted : Method) :
    ConstrainedCallsValid types methods raw reachable emitted ↔
      raw.code.length = reachable.length ∧ raw.code.length = emitted.code.length ∧
        (List.range raw.code.length).all
          (constrainedSiteValid types methods raw reachable emitted) = true := by
  have resolve : (DispatchIndex.ofTypes types).resolve = resolveConstrained types := by
    funext receiver site
    exact DispatchIndex.resolve_ofTypes types receiver site
  unfold ConstrainedCallsValid
  rw [resolve, DispatchIndex.findType_raw, linkIndex_eq]
  by_cases stateLength : raw.code.length = reachable.length
  · by_cases codeLength : raw.code.length = emitted.code.length
    · rw [constrainedSites_eq (resolveConstrained types)
        (virtualTableValid types (findDispatchType types) (FlowIndex.ofList methods).get?)
        (castTargetValid (findDispatchType types)) (FlowIndex.ofList methods).get? emitted.linkAt
        (Std.TreeSet.ofList (branchTargets raw.code) compare).contains
        raw.code reachable emitted.code raw.code reachable emitted.code 0 raw.code.head?
        (by simp) (by simp) (by simp) (by simp [List.head?_eq_getElem?]) stateLength codeLength]
      have index : (FlowIndex.ofList methods).get? = (methods[·]?) := by
        funext pc
        exact FlowIndex.get?_ofList methods pc
      have targets : (Std.TreeSet.ofList (branchTargets raw.code) compare).contains =
          (fun target => raw.code.any (branchesTo target)) := by
        funext pc
        rw [Std.TreeSet.contains_ofList, branchTargets_contains]
      rw [index, targets, ← List.range_eq_range']
      rfl
    · simp [codeLength]
  · simp [stateLength]
#print axioms ConstrainedCallsValid_iff_original

instance (types : List DispatchType) (methods : List SpecializedMethod) (raw : RawMethod)
    (reachable : List Bool) (emitted : Method) :
    Decidable (ConstrainedCallsValid types methods raw reachable emitted) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The direct call to a resolved target retains its closed owner and the site's method type
    arguments, ahead of the owner's, for ordinary managed-call validation. -/
def constrainedTargetSite (receiver : TypeExpr) (site : CallSite) (target : ConstrainedTarget) :
    CallSite :=
  { site with
    target := .managed target.method.token,
    method.owner := target.declaringType receiver,
    typeArguments := siteMethodArguments site ++ target.method.ownerArguments,
    ownerArgumentCount := target.method.ownerArguments.length }

/-- Lower a constrained prefix or call using the immediately preceding raw instruction. -/
def lowerConstrainedInstruction (resolve : TypeExpr → CallSite → Option ConstrainedTarget)
    (previous : Option RawInstruction)
    (instruction : RawInstruction) : RawInstruction :=
  match instruction with
  | ⟨offset, 65046, _⟩ => ⟨offset, 0, .none⟩
  | ⟨offset, 111, .call site⟩ =>
    match previous with
    | some ⟨_, 65046, .type receiver⟩ => match resolve receiver site with
      | some target => ⟨offset, 40, .call (constrainedTargetSite receiver site target)⟩
      | none => instruction
    | _ => instruction
  | ⟨offset, 40, .call site⟩ =>
    match previous with
    | some ⟨_, 65046, .type receiver⟩ => match resolve receiver site with
      | some target => ⟨offset, 40, .call (constrainedTargetSite receiver site target)⟩
      | none => instruction
    | _ => instruction
  | _ => instruction

/-- Lower instructions in one pass, retaining the raw predecessor before rewriting it. -/
def lowerConstrainedCode (resolve : TypeExpr → CallSite → Option ConstrainedTarget) :
    Option RawInstruction → List RawInstruction → List RawInstruction
  | _, [] => []
  | previous, instruction :: rest => lowerConstrainedInstruction resolve previous instruction ::
    lowerConstrainedCode resolve (some instruction) rest

/-- Streaming lowering agrees with positional predecessor lookup, including pc zero. -/
theorem lowerConstrainedCode_eq (resolve : TypeExpr → CallSite → Option ConstrainedTarget)
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
          | some target => ⟨offset, 40, .call (constrainedTargetSite receiver site target)⟩
          | none => instruction
        | _ => instruction
      | ⟨offset, 40, .call site⟩ =>
        match raw.code[pc - 1]? with
        | some ⟨_, 65046, .type receiver⟩ => match resolveConstrained types receiver site with
          | some target => ⟨offset, 40, .call (constrainedTargetSite receiver site target)⟩
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
