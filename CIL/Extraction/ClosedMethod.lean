import CIL.Extraction.CallAgreement

/-! A closed CIL body, its storage and its reachable sites determine the executable method. -/

namespace CIL.Extraction

/-- The zero value of each local kind, used when the method zero-initializes its locals. -/
private def initialLocal : LocalKind → Value
  | .reference | .span .. | .array _ | .methodPointer _ | .methodTable _ | .object => .nullRef
  | .byte => .i8 0
  | .narrow _ | .word32 => .i32 0
  | .word64 => .i64 0
  | .vector128 => .v128 0
  | .vector256 => .v256 0
  | .vector512 => .v512 0
  | .aggregate size => .aggregate (List.replicate size.val 0)

/-- The value a local of `kind` starts with: its zero when the body initializes locals. -/
def _root_.CIL.LocalKind.initialValue (initLocals : Bool) (kind : LocalKind) : Value :=
  if initLocals then initialLocal kind else .unmodeled

/-- The declared signature a closed raw method implies: its receiver kind, parameter types,
    return type and localsinit flag. Instantiation and metadata binding refuse explicit receiver
    signatures. -/
def _root_.CIL.DeclaredSignature.ofRaw (closed : RawMethod) : DeclaredSignature where
  receiver :=
    if closed.hasThis then some (if closed.objectReceiver then .object else .reference) else none
  parameters := closed.parameters
  returnType := closed.returnType
  initLocals := closed.initLocals

/-- A closed body fails at a live opcode or cannot supply its declared frame or prefixes. -/
inductive MethodDecodeError where
  | liveHole (pc opcode : Nat)
  | invalidFrame
  | invalidPrefixes
  deriving DecidableEq, Repr

/-- The first reachable hole carries its instruction index and raw opcode. -/
def firstLiveHole : Nat → List Bool → List Instruction → Option MethodDecodeError
  | pc, live :: rest, instruction :: code =>
    match live, instruction with
    | true, .unadmitted opcode => some (.liveHole pc opcode)
    | _, _ => firstLiveHole (pc + 1) rest code
  | _, _, _ => none

/-- The method denoted by a closed definition and its argument storage. Its code contains
    one instruction per raw site and a hole carrying the opcode at each dead site. The frame
    requires supported local kinds, valid argument homes and accesses, and valid prefixes. -/
def _root_.CIL.Method.ofClosed? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (reachable : List Bool) (closed : RawMethod)
    (storage : RawArguments) : Except MethodDecodeError Method :=
  let code := methodCode profile environment links reachable closed
  if let some failure := firstLiveHole 0 reachable code then .error failure else
  match storage.locals.mapM (storageKind environment.layouts),
      expectedHomes environment.layouts storage reachable with
  | some localKinds, some parameterHomes =>
    let homes := requiredHomeIndices storage reachable
    if !rawPrefixesValid closed.returnType closed.code then .error .invalidPrefixes else
    if !argumentInstructionsValid storage homes reachable code then .error .invalidFrame else
    .ok {
      profile := profile, code := code, localKinds := localKinds,
      locals := localKinds.map (LocalKind.initialValue closed.initLocals),
      opaqueVectorLocals := rawOpaqueLocals closed reachable,
      parameterHomes := parameterHomes, declared := DeclaredSignature.ofRaw closed,
      environment := environment, links := links,
      staticSites := closed.staticDescriptors,
      returnsValue := closed.returnType != .void, handlers := closed.handlers }
  | _, _ => .error .invalidFrame

/-- Closed decoding binds the code and every static descriptor to the same raw method. -/
theorem _root_.CIL.Method.ofClosed?_fields {profile : FeatureProfile}
    {environment : LayoutEnvironment} {links : List (Nat × Link)} {reachable : List Bool}
    {closed : RawMethod} {storage : RawArguments} {method : Method}
    (decoded : Method.ofClosed? profile environment links reachable closed storage = .ok method) :
    method.code = methodCode profile environment links reachable closed ∧
      method.staticSites = closed.staticDescriptors := by
  unfold Method.ofClosed? at decoded
  cases failure : firstLiveHole 0 reachable (methodCode profile environment links reachable closed)
    <;> simp only [failure] at decoded
  repeat' split at decoded
  all_goals first | contradiction | (cases decoded; exact ⟨rfl, rfl⟩)

#print axioms Method.ofClosed?_fields

/-- Closed decoding keeps the exception clauses of the raw method. -/
theorem _root_.CIL.Method.ofClosed?_handlers {profile : FeatureProfile}
    {environment : LayoutEnvironment} {links : List (Nat × Link)} {reachable : List Bool}
    {closed : RawMethod} {storage : RawArguments} {method : Method}
    (decoded : Method.ofClosed? profile environment links reachable closed storage = .ok method) :
    method.handlers = closed.handlers := by
  unfold Method.ofClosed? at decoded
  cases failure : firstLiveHole 0 reachable (methodCode profile environment links reachable closed)
    <;> simp only [failure] at decoded
  repeat' split at decoded
  all_goals first | contradiction | (cases decoded; rfl)

#print axioms Method.ofClosed?_handlers

/-- At a reachable instruction, a hole is incompatible with a successful scan. -/
private theorem firstLiveHole_ne_none {start pc opcode : Nat} {reachable : List Bool}
    {code : List Instruction} (active : reachable[pc]? = some true)
    (hole : code[pc]? = some (.unadmitted opcode)) : firstLiveHole start reachable code ≠ none := by
  induction reachable generalizing start pc code with
  | nil => simp at active
  | cons live rest ih =>
    cases code with
    | nil => simp at hole
    | cons op ops =>
      cases pc with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at active hole
        subst live
        subst op
        simp [firstLiveHole]
      | succ pc =>
        simp only [List.getElem?_cons_succ] at active hole
        have tail := ih (start := start + 1) active hole
        unfold firstLiveHole
        split <;> simp_all

#print axioms firstLiveHole_ne_none

/-- Successful closed decoding rules out every reachable hole at its instruction index. -/
theorem _root_.CIL.Method.ofClosed?_no_live_hole {profile environment links reachable}
    {closed storage} {method : Method} {pc opcode : Nat}
    (decoded : Method.ofClosed? profile environment links reachable closed storage = .ok method)
    (active : reachable[pc]? = some true) :
    method.code[pc]? ≠ some (.unadmitted opcode) := by
  intro hole
  rw [(Method.ofClosed?_fields decoded).1] at hole
  cases found : firstLiveHole 0 reachable
      (methodCode profile environment links reachable closed) with
  | none => exact firstLiveHole_ne_none active hole found
  | some failure => simp [Method.ofClosed?, found] at decoded

#print axioms Method.ofClosed?_no_live_hole

/-- A feature-checked mask and successful decoding discharge every runtime call comparison. -/
theorem RuntimeModelsAgree.of_closed {closed storage reachable layouts constants linkAt certificate}
    {method : Method}
    (decoded : Method.ofClosed? method.profile method.environment method.links reachable closed
      storage = .ok method) (features : FeatureFlowValid layouts constants linkAt closed
      method.profile certificate reachable method.code) :
    RuntimeModelsAgree closed reachable method := by
  have maskSize : closed.code.length = reachable.length := by
    rw [features.2.2.1, List.length_map, features.1]
  have codeSize := features.2.1.symm
  refine ⟨maskSize, codeSize, ?_⟩
  apply all3_of_getElem? (by simpa using maskSize) (by simpa using codeSize)
  rintro pc ⟨raw, index⟩ live emitted zipped active found
  simp only [List.getElem?_zipIdx] at zipped
  obtain ⟨instruction, read, eq⟩ := Option.map_eq_some_iff.mp zipped
  cases eq
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have same := (Method.ofClosed?_fields decoded).1
  have modeled := RuntimeModelsAgree.of_decoded_site read active (same ▸ found)
    (fun yes opcode hole => Method.ofClosed?_no_live_hole decoded (yes ▸ active) (hole ▸ found))
  cases live with
  | false => simpa [ModelCatalog.emissionAgrees] using modeled
  | true =>
    have present := List.mem_of_getElem? active
    simpa [present, linkReads_eq, inside, Method.linkAt] using modeled

#print axioms RuntimeModelsAgree.of_closed
end CIL.Extraction
