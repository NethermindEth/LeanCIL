import CIL.Extraction.LoweredResolution
import CIL.Extraction.LinkIndex

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
def ModelCatalog.linkedRequirement (catalog : ModelCatalog) (environment : LayoutEnvironment)
    (profile : FeatureProfile) (raw : RawInstruction) : CallRequirement :=
  match raw.operand, callOpcode? raw.opcode with
  | .call site, some opcode =>
    if (catalog.table.entry? opcode site.method).any (fun entry =>
        (entry.resolve environment site.method).any fun model =>
          !entry.declares site.declared || !model.available profile) then
      .hole raw.opcode
    else .linked
  | _, _ => .linked

/-- Decode the raw claim using the layouts, profile and raw fold role at its pc. -/
def ModelCatalog.callRequirement (catalog : ModelCatalog) (environment : CallLayouts)
    (profile : FeatureProfile) (link : Option Link) (role : Option FoldRole)
    (raw : RawInstruction) : CallRequirement :=
  let missing := CallRequirement.hole raw.opcode
  let layouts := environment.toLayoutEnvironment
  match siteClaim loweredCallFamily layouts link raw catalog.table.find with
  | .link => catalog.linkedRequirement layouts profile raw
  | .refused => missing
  | .lowered family =>
    ((family.resolve environment profile role raw).map CallRequirement.instruction).getD missing
  | .model =>
    match raw.operand, callOpcode? raw.opcode with
    | .call site, some opcode =>
      if (catalog.table.entry? opcode site.method).any (fun entry =>
          entry.declares site.declared &&
            (entry.resolve layouts site.method).any (·.available profile)) then
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
    (link : Option Link) (role : Option FoldRole) (live : Bool) : Bool :=
  if methodTokenCall raw.opcode then
    (catalog.callRequirement environment profile link role raw).accepts live emitted
  else true

/-- Check one emitted instruction against its method's layouts and raw claim. -/
def ModelCatalog.siteAgrees (catalog : ModelCatalog) (environment : LayoutEnvironment)
    (profile : FeatureProfile) (raw : RawInstruction) (emitted : Instruction)
    (link : Option Link := none) (role : Option FoldRole := none) (live : Bool := false) : Bool :=
  catalog.agreesAt environment.callLayouts profile raw emitted link role live

/-- The instruction walk checks live claims and the representation of dead calls. -/
private def modelSitesAgree (catalog : ModelCatalog) (environment : LayoutEnvironment)
    (profile : FeatureProfile) (closed : RawMethod) (reachable : List Bool)
    (code : List Instruction) (links : Array (Option Link)) : Bool :=
  let layouts := environment.callLayouts
  let roles := (foldRoles closed.locals closed.code).toArray
  all3 (fun (raw, pc) live emitted =>
    if live then
      catalog.agreesAt layouts profile raw emitted links[pc]?.join (roles[pc]?.join) true
    else !methodTokenCall raw.opcode || decide (emitted = .unadmitted raw.opcode))
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

/-- Every live method-token site of a body accepted by the runtime catalog has a raw claim. -/
theorem RuntimeModelsAgree.siteClaimTotal {closed : RawMethod} {reachable : List Bool}
    {method : Method} (agree : RuntimeModelsAgree closed reachable method)
    {pc : Nat} {raw : RawInstruction} (atRaw : closed.code[pc]? = some raw)
    (atLive : reachable[pc]? = some true) :
    SiteClaimTotal loweredCallFamily method.environment (method.linkAt pc) raw true := by
  intro _ token refused
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
  change siteClaim loweredCallFamily method.environment (method.linkAt pc) raw
    runtimeCatalog.table.find = .refused at refused
  simp [ModelCatalog.agreesAt, token, linkAt, ModelCatalog.callRequirement, refused,
    CallRequirement.accepts] at checked

#print axioms RuntimeModelsAgree.siteClaimTotal

/-- A call's raw claim determines its required instruction. Occupied pcs keep the linked
    prefixes for the managed-call checks. An unlinked lowering cannot discard a prefix. -/
def methodInstruction (profile : FeatureProfile) (environment : CallLayouts)
    (occupied : Std.TreeSet Nat) (roles : Array (Option FoldRole)) (reachable : Array Bool) :
    CallDecoder :=
  let localKind := fun type => (environment.storage type).bind (storageKind environment.layouts)
  let live := fun pc => reachable[pc]?.getD false
  Instruction.withCallDecoder roles live localKind fun pc previous raw =>
    if occupied.contains pc then
      (runtimeCatalog.linkedRequirement environment.toLayoutEnvironment profile raw).decode
        (fun _ => Instruction.ofRaw previous raw)
    else if previous.any (isPrefixOpcode ·.opcode) then .unadmitted raw.opcode
    else (runtimeCatalog.callRequirement environment profile none (roles[pc]?.join) raw).decode
      (fun _ => Instruction.ofRaw previous raw)

/-- The closed body's instruction list, including call claims at its occupied and unlinked pcs. -/
def methodCode (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (reachable : List Bool) (closed : RawMethod) : List Instruction :=
  let occupied := Std.TreeSet.ofList (links.map Prod.fst) compare
  let roles := (foldRoles closed.locals closed.code).toArray
  Instruction.ofRawCode none closed.code (methodInstruction profile environment.callLayouts
    occupied roles reachable.toArray)

end CIL.Extraction
