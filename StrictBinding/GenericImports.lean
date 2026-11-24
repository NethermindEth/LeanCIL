import StrictBinding.GenericConstraints
import StrictBinding.ContractSidecar

/-! Physical generic import sites, producer definitions and published contracts. -/

namespace StrictBinding.GenericImports
open CIL CIL.Extraction StrictBinding

private def resolveScalar (arity : Nat) : SigType → Option ResolvedType
  | .primitive code => some (.primitive code)
  | .mvar n => if n < arity then some (.mvar n) else none
  | _ => none

/-- Reconstruct the open producer definition from its own PE image, then instantiate it
    with the consumer's stated arguments for comparison with its imported contract identity. -/
private def physicalSite (image : PreparedImage) (token : Nat) (args : List ResolvedType) :
    Option MethodSite := do
  let owner ← (methodDeclaringType image token).toOption
  let cell := image.layout.cell image.view token
  let stringAt := fun n => (image.layout.stringAt image.view n).toOption
  let decl := image.layout.cell image.view owner
  let name ← stringAt (← (decl 1).toOption)
  let space ← stringAt (← (decl 2).toOption)
  guard ((← (enumDefinition? image 0 [space,name]).toOption) == some (owner % 2^24))
  guard ((← (physicalTypeShape image (owner % 2^24)).toOption) == (.classType,0))
  guard (ordinaryTypeName (← spelled? space) (← spelled? name))
  let flags ← (cell 2).toOption
  guard (flags % 8 == 6 && flags &&& 0x10 != 0 && (← (cell 1).toOption) == 0 && (← (cell 0).toOption) != 0)
  let blob ← (image.layout.blobAt image.view (← (cell 4).toOption)).toOption
  let sig ← (decodeMethodSig blob).toOption
  guard (sig.convention == 0x10 && sig.genericArity == args.length && !args.isEmpty)
  let fullName := if space.isEmpty then name else space ++ [46] ++ name
  return { owner := .named { scope := bytesOf image.identity, name := fullName,
                             parts := [space,name], kind := .classType, pinned := true },
           name := ← stringAt (← (cell 3).toOption), convention := sig.convention,
           genericArity := sig.genericArity, result := ← resolveScalar sig.genericArity sig.result,
           parameters := ← sig.parameters.mapM (resolveScalar sig.genericArity),
           definition := none, methodArguments := some args }

private def primitiveArg : SigType → Option ResolvedType
  | .primitive code => some (.primitive code)
  | _ => none

/-- Follow a MethodSpec through the MemberRef and its top-level TypeRef to the physical AssemblyRef. -/
private def targetAt (prepared : List PreparedImage) (caller : PreparedImage) (env : MetadataEnv)
    (frame : Frame) (token : Nat) (slot : ImportSlot) : Option (String × List Nat × List ResolvedType) := do
  guard (token / 2^24 == Table.methodSpec)
  let spec := caller.layout.cell caller.view token
  let parent ← (spec 0).toOption
  guard (parent % 2 == 1)
  let member := caller.layout.cell caller.view (StrictBinding.tokenOf Table.memberRef (parent/2))
  let owner ← (member 0).toOption
  guard (owner % 8 == 1)
  let ty := caller.layout.cell caller.view (StrictBinding.tokenOf Table.typeRef (owner/8))
  let resolution ← (ty 0).toOption
  guard (resolution % 4 == 2)
  let scope ← (checkedReferenceScope prepared caller
    (StrictBinding.tokenOf Table.assemblyRef (resolution/4))).toOption
  let stringAt := fun n => (caller.layout.stringAt caller.view n).toOption
  let name ← stringAt (← (member 1).toOption)
  let sig ← (caller.layout.blobAt caller.view (← (member 2).toOption)).toOption
  let signature ← (decodeMethodSig sig).toOption
  let blob ← (caller.layout.blobAt caller.view (← (spec 1).toOption)).toOption
  let args ← (← (decodeMethodSpec blob).toOption).mapM primitiveArg
  let site ← (env.importMethodSite token frame slot.identity).toOption
  let .named named := site.owner | none
  guard (named.parts == [← stringAt (← (ty 2).toOption), ← stringAt (← (ty 1).toOption)] &&
    named.scope == scope && site.name == name && site.methodArguments == some args &&
    signature.convention == site.convention && signature.genericArity == site.genericArity &&
    resolveScalar site.genericArity signature.result == some site.result &&
    signature.parameters.mapM (resolveScalar site.genericArity) == some site.parameters)
  return (← spelled? scope, name, args)

/-- Resolve each import at its decoded instruction boundary against both pinned images.
    The only supported form here is a static generic method on a top-level class with primitive
    closed arguments. Tiny and fat bodies both pass through the production body decoder. -/
def resolveCalls (item : MethodEvidence) (prepared : List PreparedImage) :
    Option (List (ImportSlot × String × Nat)) := do
  if item.body.imports.calls.isEmpty then return []
  let caller ← (located prepared item.assembly.identity).toOption
  let bytes := item.body.bytes
  let _ ← (bodyBound caller item.original.token bytes).toOption
  let env ← item.body.environment.toOption
  let arity := item.original.genericParameters.length
  let ownerArity := item.original.ownerParameters.length
  let frame ← (env.frame arity ownerArity).toOption
  let decoded ← (decodeBody env arity ownerArity item.body).toOption
  let first ← bytes.head?
  let header := if first % 4 == 2 then 1 else 12
  item.body.imports.calls.mapM fun (pc, slot) => do
    let instruction ← decoded.code[pc]?
    let .call site := instruction.operand | none
    guard (instruction.opcode == 0x28 && site.target == .external slot.identity)
    let 0x28 :: a :: b :: c :: d :: _ := bytes.drop (header + instruction.offset) | none
    let (identity, name, arguments) ← targetAt prepared caller env frame (a+256*(b+256*(c+256*d))) slot
    let producer ← (located prepared identity).toOption
    -- MethodPtr indirection and metadata in linked files extend the MethodDef search space.
    guard (producer.layout.rowCount 5 == 0)
    for n in [:producer.layout.rowCount 0x26] do
      guard ((← (producer.layout.cellOfRow producer.view 0x26 (n+1) 0).toOption) == 1)
    let mut candidates := []
    for r in [:producer.layout.rowCount Table.methodDef] do
      let token := StrictBinding.tokenOf Table.methodDef (r+1)
      let nameIndex ← (producer.layout.cell producer.view token 3).toOption
      let declared ← (producer.layout.stringAt producer.view nameIndex).toOption
      if declared == name then
        let method ← physicalSite producer token arguments
        if method.contractName frame == some (bytesOf slot.identity) then
          candidates := token :: candidates
    let [token] := candidates | none
    return (slot, identity, token)

/-- The expected publication for one import, including the consumer-selected sidecar bytes.
    The independent audit binds the producer, sidecar and declaration closure digests. -/
structure Publication where
  identity : String
  producer : String
  implementation : String
  interfaceDigest : String
  profile : String
  contractName : String
  closureDigest : String
  sidecar : ImageBytes

/-- The selected public export agrees with this slot and its independently audited declaration. -/
def exportMatches (input : Publication) (slot : ImportSlot) : Bool := Id.run do
  let some root := ContractSidecar.read input.sidecar | return false
  let some (.integer 1) := ContractSidecar.field root "schema" | return false
  let some (.integer 2) := ContractSidecar.field root "formatVersion" | return false
  let some (.boolean false) := ContractSidecar.field root "isReferenceAssembly" | return false
  let some entry := ContractSidecar.member root slot.identity | return false
  let some (.array profiles) := ContractSidecar.field entry "profiles" | return false
  let some (.integer count) := ContractSidecar.field entry "parameterCount" | return false
  let some (.boolean receiver) := ContractSidecar.field entry "hasThis" | return false
  let some (.boolean result) := ContractSidecar.field entry "returnsValue" | return false
  return input.profile == "scalar" && ContractSidecar.text root "assemblyIdentity" == some input.producer &&
    ContractSidecar.text root "implementationSha256" == some input.implementation &&
    ContractSidecar.text root "interfaceDigest" == some input.interfaceDigest &&
    ContractSidecar.text entry "visibility" == some "public" &&
    ContractSidecar.text entry "kind" == some "method" &&
    ContractSidecar.text entry "contractConstant" == some input.contractName &&
    ContractSidecar.text entry "closureDigest" == some slot.closureDigest &&
    slot.closureDigest == input.closureDigest && slot.identity == input.identity &&
    count == (slot.parameterCount : Int) && receiver == slot.hasThis && result == slot.returnsValue &&
    profiles.any (fun profile => match profile with | .string name => name == input.profile | _ => false)

/-- All slots have one publication, a matching export and an exact target in the pinned producer
    at each linked use. A missing use, unsupported signature or unavailable producer is incomplete. -/
def check (images : List PinnedImage) (profile : FeatureProfile) (methods : List MethodEvidence)
    (slots : List ImportSlot) (publications : List Publication) : Except AuditError Bool := do
  if profile != FeatureProfile.scalar || slots.isEmpty || slots.length != publications.length then
    return false
  let prepared ← prepare images
  let some uses := methods.mapM (fun item => resolveCalls item prepared) | return false
  let targets := uses.flatten
  return (slots.zip publications).all (fun (slot, publication) =>
    exportMatches publication slot && targets.any (fun use =>
      use.1 == slot && use.2.1 == publication.producer)) &&
    targets.all (fun use => (slots.zip publications).any (fun (slot, publication) =>
      use.1 == slot && use.2.1 == publication.producer))

/-- Each reported publication has a matching export and at least one use in the producer that
    supplied it. Every reconstructed use belongs to one of those publications. -/
theorem physical_of_check {images profile methods slots publications}
    (checked : check images profile methods slots publications = .ok true) :
    ∃ prepared uses, prepare images = .ok prepared ∧
      methods.mapM (fun item => resolveCalls item prepared) = some uses ∧
      (∀ pair ∈ slots.zip publications, exportMatches pair.2 pair.1 = true ∧
        ∃ target ∈ uses.flatten, target.1 = pair.1 ∧ target.2.1 = pair.2.producer) ∧
      (∀ target ∈ uses.flatten, ∃ pair ∈ slots.zip publications,
        target.1 = pair.1 ∧ target.2.1 = pair.2.producer) := by
  unfold check at checked
  split at checked <;> try cases checked
  obtain ⟨prepared, pinned, rest⟩ := CIL.Safety.except_bind_ok checked
  cases read : methods.mapM (fun item => resolveCalls item prepared) with
  | none => simp [read, pure, Except.pure] at rest
  | some uses =>
    refine ⟨prepared, uses, pinned, read, ?_⟩
    simpa only [read, pure, Except.pure, Except.ok.injEq, Bool.and_eq_true, List.all_eq_true,
      List.any_eq_true, beq_iff_eq] using rest
#print axioms physical_of_check

end StrictBinding.GenericImports

namespace StrictBinding
open CIL CIL.Extraction

/-- The completeness reported for generic identities follows from the physical method resolution
    and the selected exports of the same extraction. -/
def GenericImportsChecked (images : List PinnedImage) (profile : FeatureProfile) (methods : List MethodEvidence)
    (slots : List ImportSlot) (publications : List GenericImports.Publication)
    (complete : Bool) : Prop :=
  (GenericImports.check images profile methods slots publications).toOption = some complete

instance (images : List PinnedImage) (profile : FeatureProfile) (methods : List MethodEvidence) (slots : List ImportSlot)
    (publications : List GenericImports.Publication) (complete : Bool) :
    Decidable (GenericImportsChecked images profile methods slots publications complete) :=
  inferInstanceAs (Decidable (_ = _))

end StrictBinding
