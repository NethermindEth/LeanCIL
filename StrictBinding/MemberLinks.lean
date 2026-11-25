import StrictBinding.DispatchCatalogs

/-!
# MemberRef links resolved in the pinned images

A slice carries a link from each MemberRef token whose owner a pinned assembly defines to the
MethodDef or Field row the extraction resolved it to. The certified extraction checks the link
against the rows it carries; this audit resolves the MemberRef again from the images alone. It
reads the MemberRef row, follows its parent TypeRef, TypeDef or generic TypeSpec to the defining
TypeDef through the pinned AssemblyRefs and forwarders, and requires the linked row to be a member
of that TypeDef with the MemberRef's name, kind and signature. Signature types are compared by
their defining TypeDef, or by their scoped name when neither image defines them. A form the audit
does not read, or a reference into an assembly without a supplied image, leaves the link uncovered.
-/

namespace StrictBinding.MemberLinks

open CIL.Extraction
open ClassDispatch (Reading physical referencedClass testDefinition)

/-- The first byte of a field signature (II.23.2.4). -/
def fieldSignature : Nat := 0x06

/-- The column of the first Field row of a TypeDef, before the first MethodDef row's column. -/
def methodListColumn : Nat := 5

/-- The MemberRefParent tags of II.24.2.6 that the audit resolves. -/
def parentTypeDef : Nat := 0
def parentTypeRef : Nat := 1
def parentTypeSpec : Nat := 4

/-- A link of one evidence slice: the MemberRef token of the image pinned under `source` and
    the MethodDef or Field token of the image pinned under `target` it names. -/
structure LinkClaim where
  source : String
  memberRef : Nat
  target : String
  definition : Nat
  deriving DecidableEq, Repr

/-- Every MemberRef definition link the metadata carries, each distinct claim once, in first
    occurrence order. A link to a slice the metadata does not carry is refused. -/
def linkClaims (metadata : List MethodMetadata) : Except AuditError (List LinkClaim) := do
  let mut seen : Std.TreeMap (List Nat) Unit := {}
  let mut claims := #[]
  for method in metadata do
    let slices := method.slices
    for slice in slices do
      for link in slice.links do
        unless link.kind == linkDefinition && tableOf link.source == Table.memberRef do continue
        let some linked := slices[link.slice]?
          | throw (.memberLinkMismatch slice.assembly.identity link.source)
        let claim : LinkClaim := { source := slice.assembly.identity, memberRef := link.source,
                                   target := linked.assembly.identity, definition := link.target }
        -- Identity bytes are below 256, so 256 separates the four parts of the key.
        let key := bytesOf claim.source ++ [256, claim.memberRef, 256] ++
          bytesOf claim.target ++ [256, claim.definition]
        if seen.contains key then continue
        seen := seen.insert key ()
        claims := claims.push claim
  return claims.toList

/-- The FieldList and MethodList columns of the image's TypeDef rows never decrease and stay
    within one past their tables, so each member row has exactly one owner (II.22.37). -/
def memberListsAscend (image : PreparedImage) : Except AuditError Unit := do
  let cell := image.layout.cellOfRow image.view Table.typeDef
  let fieldLimit := image.layout.rowCount Table.field + 1
  let methodLimit := image.layout.rowCount Table.methodDef + 1
  let mut previous := (1, 1)
  for index in [:image.layout.rowCount Table.typeDef] do
    let row := index + 1
    let fields ← cell row typeDefFieldListColumn
    let methods ← cell row methodListColumn
    unless previous.1 ≤ fields && fields ≤ fieldLimit && previous.2 ≤ methods &&
        methods ≤ methodLimit do
      throw (.unsortedTable Table.typeDef row)
    previous := (fields, methods)

/-- The last TypeDef row in `[low, high)` whose member list in `column` starts at or before
    `member`, by halving the range; `fuel` bounds the number of halvings. -/
def ownerSearch (image : PreparedImage) (column member : Nat) :
    Nat → Nat → Nat → Except AuditError Nat
  | 0, low, _ => pure low
  | fuel + 1, low, high =>
    if high ≤ low + 1 then pure low
    else do
      let middle := (low + high) / 2
      let first ← image.layout.cellOfRow image.view Table.typeDef middle column
      if first ≤ member then ownerSearch image column member fuel middle high
      else ownerSearch image column member fuel low middle

/-- The TypeDef row that owns member row `member` of `table` through `column`, read in
    O(log n) cells once `memberListsAscend` holds; the range is checked, not assumed. -/
def owningType (image : PreparedImage) (table column member : Nat) :
    Except AuditError Nat := do
  let count := image.layout.rowCount Table.typeDef
  let first := image.layout.cellOfRow image.view Table.typeDef
  let row ← ownerSearch image column member count 1 (count + 1)
  let stop ← if row == count then pure (image.layout.rowCount table + 1)
    else first (row + 1) column
  unless (← first row column) ≤ member && member < stop do
    throw (.memberLinkMismatch image.identity (tokenOf table member))
  return row

/-- How a signature type token is identified across images: by its defining TypeDef, or, when
    no supplied image defines it, by the scope and name chain its TypeRef spells. -/
inductive TypeKey where
  | defined (identity : String) (row : Nat)
  | named (scope : List Nat) (parts : List (List Nat))
  deriving DecidableEq, Repr

/-- The key of a TypeDef or TypeRef token of `image`. Other forms are uncovered. -/
def typeKey (prepared : List PreparedImage) (image : PreparedImage) (token : Nat) :
    Reading TypeKey := do
  if tableOf token == Table.typeDef then
    let _ ← physical (image.layout.rowAt token)
    return .defined image.identity (token % 2 ^ 24)
  guard (tableOf token == Table.typeRef)
  let (scope, parts) ←
    referencedClass prepared image (image.layout.rowCount Table.typeRef) token []
  match ← physical (testDefinition prepared image token).run with
  | some (defining, row) => return .defined defining.identity row
  | none => return .named scope parts

/-- Two signature tokens, one of each image, name one type. Different definitions, or different
    names in one scope, are a mismatch; a definition against a name, or names in different
    scopes, is uncovered. -/
def sameKey (prepared : List PreparedImage) (source target : PreparedImage)
    (mismatch : AuditError) (left right : Nat) : Reading Unit := do
  match ← typeKey prepared source left, ← typeKey prepared target right with
  | .defined first row, .defined second other =>
    unless first == second && row == other do throwThe AuditError mismatch
  | .named scope parts, .named otherScope otherParts =>
    guard (scope == otherScope)
    unless parts == otherParts do throwThe AuditError mismatch
  | _, _ => failure

/-- Two signature types, the first read in `source` and the second in `target`, are one type.
    Function pointers are uncovered; `fuel` bounds the depth. -/
def sameType (prepared : List PreparedImage) (source target : PreparedImage)
    (mismatch : AuditError) : Nat → SigType → SigType → Reading Unit
  | 0, _, _ => failure
  | fuel + 1, left, right =>
    let require (holds : Bool) : Reading Unit :=
      unless holds do throwThe AuditError mismatch
    match left, right with
    | .primitive code, .primitive other => require (code == other)
    | .named valueType token, .named otherValueType other => do
      require (valueType == otherValueType)
      sameKey prepared source target mismatch token other
    | .var index, .var other | .mvar index, .mvar other => require (index == other)
    | .byref element, .byref other | .pointer element, .pointer other
    | .szarray element, .szarray other =>
      sameType prepared source target mismatch fuel element other
    | .genericInst valueType head arguments, .genericInst otherValueType otherHead others => do
      require (valueType == otherValueType && arguments.toList.length == others.toList.length)
      sameKey prepared source target mismatch head otherHead
      for (argument, other) in arguments.toList.zip others.toList do
        sameType prepared source target mismatch fuel argument other
    | .modified required modifier element, .modified otherRequired other otherElement => do
      require (required == otherRequired)
      sameKey prepared source target mismatch modifier other
      sameType prepared source target mismatch fuel element otherElement
    | .functionPointer .., _ | _, .functionPointer .. => failure
    | _, _ => throwThe AuditError mismatch

/-- The image and TypeDef row a MemberRef parent names: a TypeDef of the source image, a TypeRef
    followed through the supplied images, or the generic head of a TypeSpec instantiation. -/
def parentDefinition (prepared : List PreparedImage) (source : PreparedImage) (coded : Nat) :
    Reading (PreparedImage × Nat) := do
  let tag := coded % 8
  let row := coded / 8
  if tag == parentTypeDef then
    testDefinition prepared source (← physical (checkedTokenOf Table.typeDef row .rowOverflow))
  else if tag == parentTypeRef then
    testDefinition prepared source (← physical (checkedTokenOf Table.typeRef row .rowOverflow))
  else if tag == parentTypeSpec then
    let token ← physical (checkedTokenOf Table.typeSpec row .rowOverflow)
    let offset ← physical (source.layout.cell source.view token 0)
    let .ok (.genericInst _ head _) := decodeTypeSpec (← physical (source.layout.blobAt
      source.view offset)) | failure
    testDefinition prepared source head
  else failure

/-- The MemberRef `memberRef` of `source` resolves to row `definition` of `target`: the row
    is a MethodDef for a method signature and a Field for a field signature, a MemberRef may bind
    it (it is not compiler-controlled, II.23.1.10 and II.23.1.5), it belongs to the TypeDef the
    MemberRef's parent resolves to, and it has the MemberRef's name and signature. -/
def memberLinkBound (prepared : List PreparedImage) (source target : PreparedImage)
    (memberRef definition : Nat) : Reading Unit := do
  let mismatch := AuditError.memberLinkMismatch source.identity memberRef
  unless tableOf memberRef == Table.memberRef do throwThe AuditError mismatch
  let reference := source.layout.cell source.view memberRef
  let parent ← physical (reference 0)
  let name ← physical (source.layout.stringAt source.view (← physical (reference 1)))
  let signature ← physical (source.layout.blobAt source.view (← physical (reference 2)))
  let isField := signature.head? == some fieldSignature
  let (table, flagsColumn, nameColumn, signatureColumn, listColumn) :=
    if isField then (Table.field, 0, 1, 2, typeDefFieldListColumn)
    else (Table.methodDef, 2, 3, 4, methodListColumn)
  unless tableOf definition == table do throwThe AuditError mismatch
  let member := target.layout.cell target.view definition
  if (← physical (member flagsColumn)) % 8 == 0 then throwThe AuditError mismatch
  let memberName ← physical (target.layout.stringAt target.view (← physical (member nameColumn)))
  unless memberName == name do throwThe AuditError mismatch
  let owner ← physical (owningType target table listColumn (definition % 2 ^ 24))
  let (declaring, row) ← parentDefinition prepared source parent
  unless declaring.identity == target.identity && row == owner do throwThe AuditError mismatch
  let other ←
    physical (target.layout.blobAt target.view (← physical (member signatureColumn)))
  let fuel := signature.length + other.length
  if isField then
    let .ok declared := decodeFieldSig signature | failure
    let .ok found := decodeFieldSig other | failure
    sameType prepared source target mismatch fuel declared found
  else
    let .ok declared := decodeMethodSig signature | failure
    let .ok found := decodeMethodSig other | failure
    unless declared.convention == found.convention &&
        declared.genericArity == found.genericArity &&
        declared.parameters.length == found.parameters.length do
      throwThe AuditError mismatch
    sameType prepared source target mismatch fuel declared.result found.result
    for (parameter, otherParameter) in declared.parameters.zip found.parameters do
      sameType prepared source target mismatch fuel parameter otherParameter

/-- Whether the claim's link resolves in the images: `true` when checked, `false` when a form
    or an image it needs is not covered; a conflicting link is an error. -/
def linkCovered (prepared : List PreparedImage) (claim : LinkClaim) : Except AuditError Bool := do
  let some source := prepared.find? (·.identity == claim.source) | return false
  let some target := prepared.find? (·.identity == claim.target) | return false
  return (← (memberLinkBound prepared source target claim.memberRef claim.definition).run).isSome

/-- The member lists of each supplied image a claim links into ascend, each image checked once. -/
def targetsAscend (prepared : List PreparedImage) (claims : List LinkClaim) :
    Except AuditError Unit := do
  let mut targets : Std.TreeMap (List Nat) Unit := {}
  for claim in claims do
    let key := bytesOf claim.target
    if targets.contains key then continue
    targets := targets.insert key ()
    if let some target := prepared.find? (·.identity == claim.target) then
      memberListsAscend target

/-- Check every distinct MemberRef link of the metadata against one preparation of the images.
    Complete when there is at least one link and each is covered. Each target image's member
    lists are checked once; each link then costs a fixed number of row reads, a logarithmic
    owner search and the resolution of its parent and signature types. -/
def checkMetadataLinks (images : List PinnedImage) (metadata : List MethodMetadata) :
    Except AuditError Bool := do
  let prepared ← prepare images
  let claims ← linkClaims metadata
  targetsAscend prepared claims
  let covered ← claims.mapM (linkCovered prepared)
  return !claims.isEmpty && covered.all id

/-- `checkMetadataLinks` over the metadata of the evidence. -/
def checkMemberLinks (images : List PinnedImage) (methods : List MethodEvidence) :
    Except AuditError Bool :=
  checkMetadataLinks images (metadataClaims methods)

end StrictBinding.MemberLinks

namespace StrictBinding
open CIL.Extraction

/-- Every MemberRef definition link of these method bodies resolves in the pinned images, and
    the completeness bit says whether every link was covered. -/
def MemberLinksChecked (images : List PinnedImage) (methods : List MethodEvidence)
    (complete : Bool) : Prop :=
  (MemberLinks.checkMemberLinks images methods).toOption = some complete

instance (images : List PinnedImage) (methods : List MethodEvidence) (complete : Bool) :
    Decidable (MemberLinksChecked images methods complete) :=
  inferInstanceAs (Decidable (_ = _))

/-- A complete check covered every link claim of the evidence: each one resolved in the images
    `linkCovered` names. -/
theorem MemberLinksChecked.physical {images : List PinnedImage} {methods : List MethodEvidence}
    (checked : MemberLinksChecked images methods true) :
    ∃ prepared claims, prepare images = .ok prepared ∧
      MemberLinks.linkClaims (metadataClaims methods) = .ok claims ∧
      ∀ claim ∈ claims, MemberLinks.linkCovered prepared claim = .ok true := by
  have run : MemberLinks.checkMetadataLinks images (metadataClaims methods) = .ok true := by
    revert checked
    unfold MemberLinksChecked MemberLinks.checkMemberLinks
    cases MemberLinks.checkMetadataLinks images (metadataClaims methods) <;> simp [Except.toOption]
  unfold MemberLinks.checkMetadataLinks at run
  obtain ⟨prepared, preparedRead, run⟩ := CIL.Safety.except_bind_ok run
  obtain ⟨claims, claimsRead, run⟩ := CIL.Safety.except_bind_ok run
  obtain ⟨_, _, run⟩ := CIL.Safety.except_bind_ok run
  obtain ⟨covered, coveredRead, run⟩ := CIL.Safety.except_bind_ok run
  refine ⟨prepared, claims, preparedRead, claimsRead, fun claim member => ?_⟩
  have every : covered.all id = true := by
    simp only [pure, Except.pure, Except.ok.injEq, Bool.and_eq_true] at run
    exact run.2
  obtain ⟨result, inCovered, read⟩ := read_member member coveredRead
  have isTrue : result = true := by simpa using List.all_eq_true.mp every result inCovered
  rw [read, isTrue]

#print axioms MemberLinksChecked.physical

end StrictBinding
