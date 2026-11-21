import CIL.Extraction.OpaqueLocals
import CIL.Extraction.UnsafeCalls
import CIL.Extraction.Scalars
import CIL.Extraction.LinkIndex
import CIL.Extraction.StaticValues
import CIL.EntryIndex

/-!
# Call-site agreement

The method decoder and the literal-method validator interpret the same raw claim. A link leaves
its instruction to the managed-call checks. An unlinked site either names its exact instruction
or requires a hole, which cannot be live in a validated method.
-/

namespace CIL.Extraction

deriving instance DecidableEq for Instruction

/-- The required emission at a method-token site. A linked operation is checked with its target. -/
inductive CallRequirement where
  | linked
  | instruction (operation : Instruction)
  | hole (opcode : Nat)

/-- An occupied site preserves a resolving entry's declaration and profile requirements. -/
def ModelCatalog.linkedRequirement (catalog : ModelCatalog) (environment : CallLayouts)
    (profile : FeatureProfile) (raw : RawInstruction) : CallRequirement :=
  match raw.operand, callOpcode? raw.opcode with
  | .call site, some opcode =>
    if (catalog.table.entry? opcode site.method).any (fun entry =>
        match entry.select? site.method with
        | none => entry.ownsName
        | some overload =>
          match overload.resolve environment site.method with
          | some model => !overload.operand.bindsSite site || !model.available profile
          | none => entry.ownsName) then
      .hole raw.opcode
    else .linked
  | _, _ => .linked

/-- Decode the raw claim using the layouts and profile. -/
def ModelCatalog.callRequirement (catalog : ModelCatalog) (environment : CallLayouts)
    (profile : FeatureProfile) (link : Option Link) (raw : RawInstruction) : CallRequirement :=
  let missing := CallRequirement.hole raw.opcode
  let layouts := environment.toLayoutEnvironment
  match siteClaim layouts link raw catalog.table.claims with
  | .link => catalog.linkedRequirement environment profile raw
  | .refused => missing
  | .model =>
    match raw.operand, callOpcode? raw.opcode with
    | .call site, some opcode =>
      let overload := (catalog.table.entry? opcode site.method).bind (·.select? site.method)
      if overload.any (fun selected => selected.operand.bindsSite site &&
          (selected.resolve environment site.method).any (·.available profile)) then
        match opcode with
        | .call => .instruction (.call site.method {})
        | .newobj => .instruction (.newobj site.method)
      else missing
    | _, _ => missing

/-- The raw decoder supplies an instruction only where a link claims the site. -/
def CallRequirement.decode (otherwise : Unit → Instruction) : CallRequirement → Instruction
  | .linked => otherwise ()
  | .instruction operation => operation
  | .hole opcode => .unadmitted opcode

/-- A missing instruction has a single representation and cannot occur at a live pc. -/
def CallRequirement.accepts (live : Bool) (emitted : Instruction) : CallRequirement → Bool
  | .linked => true
  | .instruction operation => decide (emitted = operation)
  | .hole opcode => !live && decide (emitted = .unadmitted opcode)

/-- A method-token site satisfies its raw claim. At other opcodes no call obligation applies. -/
def ModelCatalog.agreesAt (catalog : ModelCatalog) (environment : CallLayouts)
    (profile : FeatureProfile) (raw : RawInstruction) (emitted : Instruction)
    (link : Option Link) (live : Bool) : Bool :=
  if methodTokenCall raw.opcode then
    (catalog.callRequirement environment profile link raw).accepts live emitted
  else true

/-- Check one emitted instruction against its method's layouts and raw claim. -/
def ModelCatalog.siteAgrees (catalog : ModelCatalog) (environment : LayoutEnvironment)
    (profile : FeatureProfile) (raw : RawInstruction) (emitted : Instruction)
    (link : Option Link := none) (live : Bool := false) : Bool :=
  catalog.agreesAt environment.callLayouts profile raw emitted link live

/-- A folded site emits its role, a live call satisfies its claim, and a dead call is a hole. -/
def ModelCatalog.emissionAgrees (catalog : ModelCatalog) (layouts : CallLayouts)
    (profile : FeatureProfile) (raw : RawInstruction) (emitted : Instruction)
    (link : Option Link) (role : Option FoldRole) (live : Bool) : Bool :=
  if live then
    if foldOwnsSite role then decide (role.bind (Instruction.ofRole? · none raw) = some emitted)
    else catalog.agreesAt layouts profile raw emitted link true
  else !methodTokenCall raw.opcode || decide (emitted = .unadmitted raw.opcode)

/-- The instruction walk checks live claims and the representation of dead calls. -/
private def modelSitesAgree (catalog : ModelCatalog) (environment : LayoutEnvironment)
    (profile : FeatureProfile) (closed : RawMethod) (reachable : List Bool)
    (code : List Instruction) (links : Array (Option Link)) : Bool :=
  let layouts := environment.callLayouts
  let roles := (foldRoles closed.code).toArray
  all3 (fun (raw, pc) live emitted =>
    catalog.emissionAgrees layouts profile raw emitted
      (indexedRead? links pc).join (indexedRead? roles pc).join live)
    closed.code.zipIdx reachable code

/-- Every live call fits its claim. Links and raw fold roles are indexed once per body. -/
def ModelsAgree (catalog : ModelCatalog) (environment : LayoutEnvironment)
    (profile : FeatureProfile) (closed : RawMethod) (reachable : List Bool)
    (code : List Instruction) (links : Array (Option Link) := #[]) : Prop :=
  closed.code.length = reachable.length ∧ closed.code.length = code.length ∧
    modelSitesAgree catalog environment profile closed reachable code links = true

instance (catalog : ModelCatalog) (environment : LayoutEnvironment) (profile : FeatureProfile)
    (closed : RawMethod) (reachable : List Bool) (code : List Instruction)
    (links : Array (Option Link)) : Decidable (ModelsAgree catalog environment profile closed
      reachable code links) :=
  decidable_of_iff (modelSitesAgree catalog environment profile closed reachable code links =
    true) <| by
    constructor
    · intro checked
      unfold modelSitesAgree at checked
      have sizes := all3_lengths checked
      exact ⟨by simpa using sizes.1, by simpa using sizes.2, checked⟩
    · exact fun agreed => agreed.2.2

/-- Every live method-token call satisfies the runtime catalog or its linked-call obligation. -/
def RuntimeModelsAgree (closed : RawMethod) (reachable : List Bool) (method : Method) : Prop :=
  ModelsAgree runtimeCatalog method.environment method.profile closed reachable method.code
    (if reachable.contains true then
      (linkReads method.links (List.range method.code.length)).toArray else #[])

instance (closed : RawMethod) (reachable : List Bool) (method : Method) :
    Decidable (RuntimeModelsAgree closed reachable method) :=
  inferInstanceAs (Decidable (ModelsAgree _ _ _ _ _ _ _))

/-- A live method-token site outside a fold has a claim. -/
def SiteClaimTotal (environment : LayoutEnvironment) (link : Option Link) (raw : RawInstruction)
    (live : Bool) (role : Option FoldRole := none) : Prop :=
  (live && !foldOwnsSite role) = true → methodTokenCall raw.opcode = true →
    siteClaim environment link raw ≠ .refused

/-- Every live method-token site outside a fold in a validated body has a raw claim. -/
theorem RuntimeModelsAgree.siteClaimTotal {closed : RawMethod} {reachable : List Bool}
    {method : Method} (agree : RuntimeModelsAgree closed reachable method)
    {pc : Nat} {raw : RawInstruction} (atRaw : closed.code[pc]? = some raw)
    (atLive : reachable[pc]? = some true) :
    SiteClaimTotal method.environment (method.linkAt pc) raw true
      ((foldRoles closed.code)[pc]?.join) := by
  intro ordinary token refused
  simp only [Bool.true_and, Bool.not_eq_true'] at ordinary
  have live := List.contains_iff_mem.mpr (List.mem_of_getElem? atLive)
  simp only [RuntimeModelsAgree, live, ite_true] at agree
  obtain ⟨_, lengthCode, checks⟩ := agree
  have inside : pc < closed.code.length := (List.getElem?_eq_some_iff.mp atRaw).1
  have inCode : pc < method.code.length := lengthCode ▸ inside
  have zipped : closed.code.zipIdx[pc]? = some (raw, pc) := by
    simp [List.getElem?_zipIdx, atRaw]
  have checked := all3_at checks zipped atLive (List.getElem?_eq_getElem inCode)
  have linkAt : (linkReads method.links (List.range method.code.length))[pc]?.join =
      method.linkAt pc := by simp [linkReads_eq, inCode, Method.linkAt]
  change siteClaim method.environment (method.linkAt pc) raw
    runtimeCatalog.table.claims = .refused at refused
  simp [ModelCatalog.emissionAgrees, ordinary, ModelCatalog.agreesAt, token, linkAt,
    ModelCatalog.callRequirement, refused,
    CallRequirement.accepts] at checked

#print axioms RuntimeModelsAgree.siteClaimTotal

/-- At a live pc that a fold owns, a validated body emits exactly the instruction the fold role
    fixes, so a call inside a fold cannot emit anything else. -/
theorem RuntimeModelsAgree.foldOwnedSite {closed : RawMethod} {reachable : List Bool}
    {method : Method} (agree : RuntimeModelsAgree closed reachable method)
    {pc : Nat} {raw : RawInstruction} {emitted : Instruction}
    (atRaw : closed.code[pc]? = some raw) (atLive : reachable[pc]? = some true)
    (atCode : method.code[pc]? = some emitted)
    (owned : foldOwnsSite ((foldRoles closed.code)[pc]?.join) = true) :
    ((foldRoles closed.code)[pc]?.join).bind (Instruction.ofRole? · none raw) =
      some emitted := by
  have live := List.contains_iff_mem.mpr (List.mem_of_getElem? atLive)
  simp only [RuntimeModelsAgree, live, ite_true] at agree
  obtain ⟨_, _, checks⟩ := agree
  have zipped : closed.code.zipIdx[pc]? = some (raw, pc) := by
    simp [List.getElem?_zipIdx, atRaw]
  have checked := all3_at checks zipped atLive atCode
  simp only [ModelCatalog.emissionAgrees, ite_true] at checked
  simpa [owned] using checked

#print axioms RuntimeModelsAgree.foldOwnedSite

/-- An ordinary static field belongs to a closed type in the method's assembly. -/
private def localStaticOwner (methodOwner : String) (owner : TypeExpr) : Bool :=
  let scope := String.ofList ((metadataChars methodOwner).takeWhile (· != ':'))
  if scope.isEmpty || !ownedBy scope methodOwner then false else
  match owner with
  | .object assembly _ | .atom assembly _ => scope == assembly
  | .aggregate identity _ => ownedBy scope identity
  | _ => false

/-- Loads and addresses bind immutable storage. A store does not decode, so its position stays
    a hole and a method with a reachable store is refused. -/
private def ordinaryStaticInstruction (environment : CallLayouts) (methodOwner : String)
    (descriptor : StaticDescriptor) (opcode : Nat) : Option Instruction := do
  let field := descriptor.field
  guard (localStaticOwner methodOwner field.owner && descriptor.alignment == 1)
  guard (staticStorageMatches field.type descriptor)
  if descriptor.scalar.isNone then
    guard (environment.valueShape field.type == .aggregate descriptor.bytes.length)
  if descriptor.opaqueValue then
    guard (opcode == 126 && initializerYields [] descriptor)
  else
    let init ← descriptor.initializer
    guard (init.literal.isNone || initializerYields [] descriptor)
  match opcode with
  | 126 => return .ldsfld field
  | 127 => return .ldsflda field
  | _ => none

/-- The raw operand names the descriptor's field. An RVA site also requires its full blob. -/
private def staticInstruction (profile : FeatureProfile) (environment : CallLayouts)
    (methodOwner : String) (site : Option StaticFieldSite) (raw : RawInstruction) :
    Option Instruction := do
  if let some word := platformField raw then
    guard (profile.littleEndian && site.isNone)
    return .ldc_i4 word
  let data ← site
  let field := data.descriptor.field
  guard (raw.operand == .field field.owner field.index field.type field.name true)
  let some size := data.rvaSize |
    return ← ordinaryStaticInstruction environment methodOwner data.descriptor raw.opcode
  guard (size > 0 && data.descriptor.bytes.length == size &&
    data.descriptor.alignment ∈ [1, 2, 4, 8] && data.descriptor.initializer.isNone &&
    data.descriptor.scalar.isNone && !data.descriptor.opaqueValue)
  match raw.opcode with
  | 127 => return .ldsflda field
  | 208 => return .ldtoken (.field field)
  | _ => none

/-- A call's raw claim determines its required instruction. Occupied pcs keep the linked
    prefixes for the managed-call checks. An unlinked lowering cannot discard a prefix. -/
def methodInstruction (profile : FeatureProfile) (environment : CallLayouts)
    (methodOwner : String) (statics : Std.TreeMap Nat StaticFieldSite) (occupied : Std.TreeSet Nat)
    (roles : Array (Option FoldRole)) (reachable : Array Bool) :
    SiteDecoder :=
  let live := fun pc => (indexedRead? reachable pc).getD false
  Instruction.withSiteDecoder roles live fun pc previous raw =>
    if !methodTokenCall raw.opcode then
      if occupied.contains pc || previous.any (isPrefixOpcode ·.opcode) then .unadmitted raw.opcode
      else (staticInstruction profile environment methodOwner statics[pc]? raw).getD
        (.unadmitted raw.opcode)
    else if occupied.contains pc then
      (runtimeCatalog.linkedRequirement environment profile raw).decode
        (fun _ => Instruction.ofRaw previous raw)
    else if previous.any (isPrefixOpcode ·.opcode) then .unadmitted raw.opcode
    else
      (runtimeCatalog.callRequirement environment profile none raw).decode
        (fun _ => Instruction.ofRaw previous raw)

/-- Decode an ordinary body using only the predecessor required by the value decoder. -/
private def plainCode (previous : Option RawInstruction) : List RawInstruction → List Instruction
  | [] => []
  | raw :: rest => Instruction.ofClosedValue previous raw :: plainCode (some raw) rest

/-- Ignoring the unused pc in an ordinary body preserves each decoded instruction. -/
private theorem plainCode_eq (code : List RawInstruction) (previous : Option RawInstruction)
    (pc : Nat) : plainCode previous code =
      Instruction.ofRawCode previous code (fun _ => Instruction.ofClosedValue) pc := by
  induction code generalizing previous pc with
  | nil => rfl
  | cons first rest ih => exact congrArg (List.cons _) (ih (some first) (pc + 1))

#print axioms plainCode_eq

/-- The closed body's instruction list, including call claims at its occupied and unlinked pcs. -/
def methodCode (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (reachable : List Bool) (closed : RawMethod) : List Instruction :=
  if plainBody closed.code reachable then plainCode none closed.code
  else
    let occupied := Std.TreeSet.ofList (links.map Prod.fst) compare
    let roles := (foldRoles closed.code).toArray
    Instruction.ofRawCode none closed.code (methodInstruction profile environment.callLayouts
      closed.owner (firstEntryIndex closed.staticFields) occupied roles reachable.toArray)

/-- Both decoding paths implement the same reachability, link and fold rule at every pc. -/
theorem methodCode_eq (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (reachable : List Bool) (closed : RawMethod) :
    methodCode profile environment links reachable closed =
      Instruction.ofRawCode none closed.code (methodInstruction profile environment.callLayouts
        closed.owner (firstEntryIndex closed.staticFields)
        (Std.TreeSet.ofList (links.map Prod.fst) compare)
        (foldRoles closed.code).toArray reachable.toArray) := by
  unfold methodCode
  split
  · rename_i plain
    rw [plainCode_eq _ _ 0]
    apply List.ext_getElem?
    intro pc
    simp only [Instruction.ofRawCode_getElem?, Instruction.ofRawAt]
    cases found : closed.code[pc]? with
    | none => rfl
    | some raw =>
      obtain ⟨live, ordinary, role⟩ := plainBody_at (closed := closed) plain found
      simp [methodInstruction, Instruction.withSiteDecoder, live, ordinary, role]
  · rfl

#print axioms methodCode_eq

private theorem decodedGetD_ne_memory {value : Option Instruction} {operation : MemoryOp}
    (opcode : Nat) (absent : value ≠ some (.memory operation)) :
    value.getD (.unadmitted opcode) ≠ .memory operation := by
  cases value <;> simp_all

private theorem role_ne_memory (role : FoldRole) (previous : Option RawInstruction)
    (raw : RawInstruction) (operation : MemoryOp) :
    Instruction.ofRole? role previous raw ≠ some (.memory operation) := by
  cases role <;> simp only [Instruction.ofRole?]
  all_goals repeat' split
  all_goals first | exact Instruction.ofRaw?_ne_memory previous raw operation | simp

private theorem static_ne_memory (profile : FeatureProfile) (environment : CallLayouts)
    (owner : String) (site : Option StaticFieldSite) (raw : RawInstruction) (operation : MemoryOp) :
    staticInstruction profile environment owner site raw ≠ some (.memory operation) := by
  have ordinary (descriptor : StaticDescriptor) (opcode : Nat) :
      ordinaryStaticInstruction environment owner descriptor opcode ≠ some (.memory operation) := by
    intro found
    unfold ordinaryStaticInstruction at found
    simp only [Option.bind_eq_bind] at found
    repeat' first
      | (rw [Option.bind_eq_some_iff] at found; obtain ⟨_, _, found⟩ := found)
      | split at found
    all_goals cases found
  intro found
  unfold staticInstruction at found
  simp only [Option.bind_eq_bind] at found
  repeat' first
    | exact ordinary _ _ found
    | (rw [Option.bind_eq_some_iff] at found; obtain ⟨_, _, found⟩ := found)
    | split at found
  all_goals cases found

private theorem methodInstruction_ne_memory (profile : FeatureProfile) (environment : CallLayouts)
    (owner : String) (statics : Std.TreeMap Nat StaticFieldSite) (occupied : Std.TreeSet Nat)
    (roles : Array (Option FoldRole)) (live : Array Bool) (pc : Nat)
    (previous : Option RawInstruction) (raw : RawInstruction) (operation : MemoryOp) :
    methodInstruction profile environment owner statics occupied roles live pc previous raw ≠
      .memory operation := by
  have plain : Instruction.ofRaw previous raw ≠ .memory operation :=
    decodedGetD_ne_memory _ (Instruction.ofRaw?_ne_memory previous raw operation)
  have linked : ((runtimeCatalog.linkedRequirement environment profile raw).decode
      (fun _ => Instruction.ofRaw previous raw)) ≠ .memory operation := by
    unfold ModelCatalog.linkedRequirement
    repeat' split
    all_goals first | exact plain | simp [CallRequirement.decode]
  have closed : Instruction.ofClosedValue previous raw ≠ .memory operation := by
    have safe (condition : Bool) :
        (if condition then Instruction.unadmitted raw.opcode else Instruction.ofRaw previous raw) ≠
          .memory operation := by cases condition <;> simp [plain]
    exact safe _
  have called : ((runtimeCatalog.callRequirement environment profile none raw).decode
      (fun _ => Instruction.ofRaw previous raw)) ≠ .memory operation := by
    unfold ModelCatalog.callRequirement
    dsimp only
    cases claim : siteClaim environment.toLayoutEnvironment none raw runtimeCatalog.table.claims with
    | link => exact linked
    | refused => simp [CallRequirement.decode]
    | model =>
      repeat' split
      all_goals first | contradiction | exact linked | simp [CallRequirement.decode]
  unfold methodInstruction Instruction.withSiteDecoder
  dsimp only
  repeat' first
    | exact closed
    | exact linked
    | exact called
    | exact decodedGetD_ne_memory _ (role_ne_memory _ previous raw operation)
    | exact decodedGetD_ne_memory _ (static_ne_memory profile environment owner _ raw operation)
    | (solve | intro impossible; contradiction)
    | split

/-- Every pc in the production method decoder excludes the general memory-operation constructor.
    Runtime memory models occur at bound calls, and byte-block transfers retain their opcodes. -/
theorem methodCode_ne_memory (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (reachable : List Bool) (closed : RawMethod)
    (pc : Nat) (operation : MemoryOp) :
    (methodCode profile environment links reachable closed)[pc]? ≠ some (.memory operation) := by
  rw [methodCode_eq, Instruction.ofRawCode_getElem? _ pc (decode := _)]
  unfold Instruction.ofRawAt
  cases found : closed.code[pc]? with
  | none => simp
  | some raw =>
    simpa using methodInstruction_ne_memory profile environment.callLayouts closed.owner
      (firstEntryIndex closed.staticFields) (Std.TreeSet.ofList (links.map Prod.fst) compare)
      (foldRoles closed.code).toArray reachable.toArray pc (rawBefore (closed.code[·]?) pc) raw operation

#print axioms methodCode_ne_memory

/-- The occupied-pc index contains precisely the positions with a link. -/
private theorem occupied_eq (links : List (Nat × Link)) (pc : Nat) :
    (Std.TreeSet.ofList (links.map Prod.fst) compare).contains pc =
      (linkLookup links pc).isSome := by
  simp only [Std.TreeSet.contains_ofList, linkLookup]
  induction links with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.map_cons, List.contains_cons, List.find?_cons]
    by_cases same : entry.1 = pc
    · simp [same]
    · simp only [beq_eq_false_iff_ne.mpr same, beq_eq_false_iff_ne.mpr (Ne.symm same),
        Bool.false_or, ih]

#print axioms occupied_eq

/-- A method-token opcode with a different operand cannot decode as a linked instruction. -/
private theorem malformedCall (previous : Option RawInstruction) (raw : RawInstruction)
    (token : methodTokenCall raw.opcode = true) (missing : (raw.operand matches .call _) = false) :
    Instruction.ofRaw previous raw = .unadmitted raw.opcode := by
  obtain ⟨offset, opcode, operand⟩ := raw
  simp only [methodTokenCall, Bool.or_eq_true, beq_iff_eq] at token
  rcases token with (rfl | rfl) | rfl <;> cases operand <;> try contradiction
  all_goals
    unfold Instruction.ofRaw Instruction.ofRaw?
    split <;> try rfl
  all_goals
    rename_i isStatic _
    cases isStatic <;> simp [Instruction.instanceField?, FieldRef.ofOperand?, Option.bind]
    all_goals repeat' split <;> rfl

#print axioms malformedCall

/-- The runtime agreement check holds at every decoded site except a live refused instruction. -/
theorem RuntimeModelsAgree.of_decoded_site {profile : FeatureProfile}
    {env : LayoutEnvironment} {links : List (Nat × Link)} {reachable : List Bool}
    {closed : RawMethod} {pc : Nat} {raw : RawInstruction} {live : Bool} {emitted : Instruction}
    (found : closed.code[pc]? = some raw) (active : reachable[pc]? = some live)
    (decoded : (methodCode profile env links reachable closed)[pc]? = some emitted)
    (admitted : live = true → ∀ opcode, emitted ≠ .unadmitted opcode) :
    runtimeCatalog.emissionAgrees env.callLayouts profile raw emitted (linkLookup links pc)
      ((foldRoles closed.code)[pc]?.join) live = true := by
  rw [methodCode_eq, Instruction.ofRawCode_getElem? closed.code pc _, Instruction.ofRawAt,
    found] at decoded
  have same := Option.some.inj decoded
  simp only [methodInstruction, Instruction.withSiteDecoder, indexedRead?_eq,
    List.getElem?_toArray, active, Option.getD_some, occupied_eq] at same
  cases live with
  | false => simp_all [ModelCatalog.emissionAgrees]
  | true =>
    generalize (foldRoles closed.code)[pc]?.join = role at *
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at same
    simp only [ModelCatalog.emissionAgrees, ite_true]
    cases owned : foldOwnsSite role
    · simp only [Bool.false_eq_true, ite_false, ModelCatalog.agreesAt]
      cases token : methodTokenCall raw.opcode
      · rfl
      · simp only [ite_true]
        simp only [boundSite, token, Bool.true_or, owned, Bool.not_false, Bool.and_true,
          ite_true, Bool.not_true, Bool.false_eq_true, ite_false] at same
        cases link : linkLookup links pc with
        | none =>
          simp only [link, Option.isSome_none, Bool.false_eq_true, ite_false] at same
          split at same
          · exact absurd same.symm (admitted rfl _)
          · cases req : runtimeCatalog.callRequirement env.callLayouts profile none raw <;>
              simp_all [CallRequirement.decode, CallRequirement.accepts]
            exact admitted _ same.symm
        | some target =>
          simp only [link, Option.isSome_some, ite_true] at same
          cases operand : raw.operand with
          | call site =>
            simp only [ModelCatalog.callRequirement, siteClaim, token, operand, Bool.not_true,
              Bool.false_eq_true, ite_false, Option.isSome_some, ite_true]
            unfold ModelCatalog.linkedRequirement at same ⊢
            rw [operand] at same ⊢
            repeat' split at same
            all_goals simp_all [CallRequirement.accepts, CallRequirement.decode]
            exact admitted _ same.symm
          | _ =>
            have hole := malformedCall (rawBefore (closed.code[·]?) pc) raw token
              (by simp [operand])
            simp [ModelCatalog.linkedRequirement, operand, CallRequirement.decode, hole] at same
            exact absurd same.symm (admitted rfl _)
    · cases role with
      | none => contradiction
      | some part =>
        cases part <;> simp_all [foldOwnsSite, Instruction.ofRole?]
        all_goals by_cases load : raw.opcode = 20 <;> by_cases valid : raw.operand = .none <;>
          simp_all [eq_comm]

#print axioms RuntimeModelsAgree.of_decoded_site

end CIL.Extraction
