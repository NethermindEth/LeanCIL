import StrictBinding.GenericConstraints

/-! Check physical class tests and virtual slot catalogs against the pinned images. -/

namespace StrictBinding.ClassDispatch
open CIL CIL.Extraction

/-- Unsupported metadata leaves coverage partial. A conflicting supported claim is an error. -/
abbrev Reading := OptionT (Except AuditError)

/-- Structural PE errors retain the token, heap offset or column that failed. -/
def physical (action : Except AuditError α) : Reading α := liftM action

/-- An unsupported signature leaves the catalog partial. Structural errors retain their cause. -/
private def signatureValue (read : Except AuditError α) : Reading α :=
  match read with
  | .ok value => pure value
  | .error .uncoveredConstraint => failure
  | .error error => throwThe AuditError error

/-- The physical namespace and simple name of each enclosing declaration. Interfaces still
    require unambiguous spelling in the catalog's atom representation. -/
private def declarationLevels (image : PreparedImage) (isInterface : Bool) :
    Nat → Nat → Reading (List TypeLevel)
  | 0, row => throwThe AuditError (.typeDefMismatch row .nesting)
  | fuel + 1, row => do
    let cell := image.layout.cellOfRow image.view Table.typeDef row
    let name ← physical (image.layout.stringAt image.view (← physical (cell typeNameColumn)))
    let space ← physical (image.layout.stringAt image.view (← physical (cell typeNamespaceColumn)))
    let flags ← physical (cell typeDefFlagsColumn)
    let parent ← if visibilityOf flags < nestedVisibility then pure 0
      else physical (enclosingTypeRow image row flags)
    unless (← physical (enumDefinition? image parent [space, name])) == some row do failure
    if isInterface then
      let some simple := spelled? name | failure
      let some scope := spelled? space | failure
      guard (ordinaryTypeName scope simple && (parent == 0 || scope.isEmpty))
    let some simple := MetadataName.ofBytes? name | failure
    let some namespace_ := MetadataName.ofBytes? space | failure
    let level := TypeLevel.mk namespace_ simple
    if parent == 0 then return [level]
    guard ((← physical (physicalTypeShape image parent)).2 == 0)
    return (← declarationLevels image isInterface fuel parent) ++ [level]

/-- A uniquely named nongeneric class or interface from the selected image. -/
private def localName (image : PreparedImage) (row : Nat) (kind : TypeKind) :
    Reading ClassName := do
  unless (← physical (physicalTypeShape image row)) == (kind, 0) do failure
  return ⟨← declarationLevels image (kind == .interface) row row⟩

/-- A physical class identity used by the slot or its signatures. -/
private def className (image : PreparedImage) (row : Nat) : Reading TypeExpr := do
  return .object image.identity (← localName image row .classType)

/-- Follow a local TypeDef edge. The core Object, ValueType and Enum roots cannot descend
    from a local class. This lets a class hierarchy coexist with unrelated structs and enums. -/
private def parentRow (image : PreparedImage) (row : Nat) : Reading Nat := do
  let declaration := image.layout.cellOfRow image.view Table.typeDef row
  let coded ← physical (declaration typeDefExtendsColumn)
  if coded == 0 then
    unless row == 1 do
      guard ((← physical (declaration typeDefFlagsColumn)) &&& 0x20 != 0)
    return 0
  if coded % 4 == 0 then
    let token ← physical (checkedTokenOf Table.typeDef (coded / 4) .rowOverflow)
    let _ ← physical (image.layout.rowAt token)
    return coded / 4
  guard (coded % 4 == 1)
  let cell := image.layout.cellOfRow image.view Table.typeRef (coded / 4)
  let scope ← physical (cell 0)
  guard (scope % 4 == 2)
  let reference ← physical (checkedTokenOf Table.assemblyRef (scope / 4) .rowOverflow)
  guard (← physical (coreAssemblyAt image reference 0))
  guard ((← physical (image.layout.stringAt image.view (← physical (cell 2)))) == systemNamespace)
  let name ← physical (image.layout.stringAt image.view (← physical (cell 1)))
  guard ([objectName, valueTypeName, enumName].contains name)
  return 0

/-- Check the entire parent chain even when the selected root is an ancestor in a cycle. -/
private def descends (parents : Array Nat) (root : Nat) : Nat → Nat → Bool → Reading Bool
  | _, 0, found => return found
  | 0, row, _ => throwThe AuditError (.typeDefMismatch row .base)
  | fuel+1, row, found => do
    let some parent := parents[row]? | throwThe AuditError (.typeDefMismatch row .base)
    descends parents root fuel parent (found || row == root)

/-- A primitive, local class or in-range method type parameter in a catalog signature. -/
private def formalElement (image : PreparedImage) (core : Except AuditError String)
    (arity token : Nat) : SigType → Reading TypeExpr
  | .primitive 1 => throwThe AuditError (.dispatchMismatch token)
  | .primitive code => do
    signatureValue (do primitiveElement (← core) code)
  | .named false token => do
    guard (tableOf token == Table.typeDef)
    className image (token % 2^24)
  | .mvar index => do
    guard (index < arity)
    return .parameter index
  | _ => failure

/-- A managed reference in a slot signature preserves its physical element type. -/
private def formalType (image : PreparedImage) (core : Except AuditError String)
    (arity token : Nat) : SigType → Reading TypeExpr
  | .byref element => do return .byref (← formalElement image core arity token element)
  | element => formalElement image core arity token element

/-- A managed MethodDef with its physical flags, signature and type parameter declarations. -/
private def classMethod (prepared : List PreparedImage) (image : PreparedImage)
    (core : Except AuditError String) (row : Nat) : Reading DispatchMethod := do
  let cell := image.layout.cellOfRow image.view Table.methodDef row
  let implementation ← physical (cell 1)
  let attributes ← physical (cell 2)
  let some name := spelled? (← physical (image.layout.stringAt image.view (← physical (cell 3))))
    | failure
  let blob ← physical (image.layout.blobAt image.view (← physical (cell 4)))
  let .ok sig := decodeMethodSig blob | failure
  let convention := if sig.genericArity == 0 then 0 else genericFlag
  guard (sig.convention == convention || sig.convention == convention + hasThisFlag)
  guard (implementation == 0)
  let token := StrictBinding.tokenOf Table.methodDef row
  let genericParameters ← signatureValue
    (readParameterDeclarations image token sig.genericArity prepared)
  -- Method parameters are invariant. Other bits and conflicting class/struct constraints
  -- lie outside the catalog's supported declarations.
  guard (genericParameters.all fun parameter =>
    parameter.flags &&& 0x3c == parameter.flags && parameter.flags &&& 0x0c != 0x0c)
  let isAbstract := attributes &&& 0x400 != 0
  let hasBody := (← physical (cell 0)) != 0
  let hasThis := sig.convention == convention + hasThisFlag
  guard (hasBody == !isAbstract && hasThis == (attributes &&& 0x10 == 0))
  let result ← match sig.result with
    | .primitive 1 => pure .void
    | type => formalType image core sig.genericArity token type
  return {
    token, name, hasThis, isPublic := attributes % 8 == 6,
    isAbstract, isVirtual := attributes &&& virtualMethodAttribute != 0, hasBody,
    genericArity := sig.genericArity, genericParameters, explicitThis := false,
    callingConvention := convention,
    attributes, implementation, returnType := result,
    parameters := ← sig.parameters.mapM (formalType image core sig.genericArity token),
    overrides := [] }

/-- InterfaceImpl targets grouped by their physical TypeDef owner, in declaration order. -/
private def interfacesByOwner (image : PreparedImage) (count : Nat) :
    Reading (Array (Array Nat)) := do
  let mut owners := Array.replicate (count + 1) #[]
  let interfaceImpl := 0x09
  for i in [:image.layout.rowCount interfaceImpl] do
    let cell := image.layout.cellOfRow image.view interfaceImpl (i+1)
    let owner ← physical (cell 0)
    guard (owner > 0 && owner ≤ count)
    let target ← physical (cell 1)
    owners := owners.modify owner (·.push target)
  return owners

/-- A local interface implemented by a class in the selected hierarchy. -/
private def interfaceName (image : PreparedImage) (coded : Nat) : Reading TypeExpr := do
  guard (coded % 4 == 0 && coded / 4 > 0)
  let name ← localName image (coded / 4) .interface
  let some text := name.signatureName? | failure
  return .atom image.identity text

/-- Local MethodImpl rows bind the implementing MethodDef to its class and the overridden
    MethodDef to its interface. Both signatures describe the same nongeneric instance slot. -/
private def localOverrides (prepared : List PreparedImage) (image : PreparedImage)
    (core : Except AuditError String) (interfaces : Array (Array Nat)) (selected : Array Nat) :
    Reading (Array (List (Nat × TypeExpr))) := do
  let rowCount := image.layout.rowCount 0x19
  if rowCount == 0 then return #[]
  let methods := image.layout.rowCount Table.methodDef
  let mut bindings := Array.replicate (methods + 1) []
  for i in [:rowCount] do
    let cell := image.layout.cellOfRow image.view 0x19 (i+1)
    let owner ← physical (cell 0)
    let body ← physical (cell 1)
    let slot ← physical (cell 2)
    guard (body % 2 == 0)
    let bodyToken ← physical (checkedTokenOf Table.methodDef (body / 2) .rowOverflow)
    let classToken ← physical (checkedTokenOf Table.typeDef owner .rowOverflow)
    unless (← physical (methodDeclaringType image bodyToken)) == classToken do
      throwThe AuditError (.dispatchMismatch bodyToken)
    -- An unrelated class can implement an external interface. Its slots do not enter this catalog.
    unless selected.contains owner do continue
    guard (slot % 2 == 0)
    let slotToken ← physical (checkedTokenOf Table.methodDef (slot / 2) .rowOverflow)
    let interfaceToken ← physical (methodDeclaringType image slotToken)
    let some direct := interfaces[owner]? | failure
    guard (direct.contains ((interfaceToken % 2^24) * 4))
    let name ← localName image (interfaceToken % 2^24) .interface
    let some text := name.signatureName? | failure
    let slotOwner := TypeExpr.atom image.identity text
    let implementation ← classMethod prepared image core (body / 2)
    let declaration ← classMethod prepared image core (slot / 2)
    guard (implementation.genericArity == 0 && declaration.genericArity == 0)
    guard (implementation.hasThis && implementation.hasBody && implementation.isVirtual &&
      declaration.hasThis && declaration.isVirtual && declaration.isAbstract &&
      implementation.returnType == declaration.returnType &&
      implementation.parameters == declaration.parameters)
    let binding := (slotToken, slotOwner)
    guard (!bindings[body / 2]!.contains binding)
    bindings := bindings.modify (body / 2) (binding :: ·)
  return bindings.map List.reverse

/-- File rows with metadata introduce classes in other modules of the same assembly. -/
def singleModule (image : PreparedImage) : Reading Unit := do
  for i in [:image.layout.rowCount 0x26] do
    guard ((← physical (image.layout.cellOfRow image.view 0x26 (i+1) 0)) == 1)

/-- Read the namespace, outer name and nested names from the TypeRef chain, ending at
    the physical AssemblyRef. A cyclic or module-scoped reference is uncovered. -/
def referencedClass (images : List PreparedImage) (image : PreparedImage) :
    Nat → Nat → List (List Nat) → Reading (CIL.AssemblyName × List (List Nat))
  | 0, _, _ => failure
  | fuel + 1, token, nested => do
    let cell := image.layout.cell image.view token
    let scope ← physical (cell 0)
    let name ← physical (image.layout.stringAt image.view (← physical (cell typeNameColumn)))
    let space ← physical (image.layout.stringAt image.view (← physical (cell typeNamespaceColumn)))
    match scope % 4 with
    | 2 =>
      let assembly ← physical (checkedTokenOf Table.assemblyRef (scope / 4) .rowOverflow)
      return (← physical (checkedReferenceScope images image assembly), space :: name :: nested)
    | 3 =>
      guard space.isEmpty
      let enclosing ← physical (checkedTokenOf Table.typeRef (scope / 4) .rowOverflow)
      referencedClass images image fuel enclosing (space :: name :: nested)
    | _ => failure

/-- Locate a class at its TypeDef or through an AssemblyRef in the body that tests it.
    Every forwarded declaration requires the full chain of pinned images. -/
def testDefinition (prepared : List PreparedImage) (home : PreparedImage) (token : Nat) :
    Reading (PreparedImage × Nat) := do
  let _ ← physical (home.layout.rowAt token)
  if tableOf token == Table.typeDef then return (home, token % 2^24)
  guard (tableOf token == Table.typeRef)
  let (identity, parts) ← referencedClass prepared home (home.layout.rowCount Table.typeRef) token []
  let some target := prepared.find? (·.assembly == identity) | failure
  singleModule target
  match ← physical (definitionRoute prepared target parts) with
  | .defined row => return (target, row)
  | .forwarded scope =>
    for image in prepared do singleModule image
    let some destination ← physical (findPinnedDefinition prepared parts scope prepared.length) | failure
    return destination

/-- Consecutive graph indices for the TypeDef rows of one pinned module. -/
private structure ModuleRows where
  image : PreparedImage
  offset : Nat
  count : Nat

/-- Every TypeDef has its physical parent in the pinned modules or a recognized root. -/
private structure ParentGraph where
  modules : List ModuleRows
  parents : Array Nat

/-- Resolve each nonlocal parent by its physical TypeRef and every required forwarder. -/
private def parentGraph (prepared : List PreparedImage) : Reading ParentGraph := do
  let mut ranges := #[]
  let mut offset := 0
  for image in prepared do
    singleModule image
    let count := image.layout.rowCount Table.typeDef
    ranges := ranges.push (⟨image, offset, count⟩ : ModuleRows)
    offset := offset + count
  let mut parents := #[0]
  for group in ranges do
    for index in [:group.count] do
      let row := index + 1
      match ← physical (parentRow group.image row).run with
      | some parent => parents := parents.push (if parent == 0 then 0 else group.offset + parent)
      | none =>
        let coded ← physical (group.image.layout.cellOfRow group.image.view Table.typeDef row
          typeDefExtendsColumn)
        guard (coded % 4 == 1)
        let token ← physical (checkedTokenOf Table.typeRef (coded / 4) .rowOverflow)
        let (image, base) ← testDefinition prepared group.image token
        let some target := ranges.find? (·.image.assembly == image.assembly) | failure
        let _ ← className image base
        parents := parents.push (target.offset + base)
  for row in [1:parents.size] do
    let _ ← descends parents 0 offset row false
  return ⟨ranges.toList, parents⟩

/-- Read a catalog class and its methods from the module that owns its TypeDef. -/
private def readClass (prepared : List PreparedImage) (image : PreparedImage)
    (core : Except AuditError String) (interfaces : Array (Array Nat))
    (overrides : Array (List (Nat × TypeExpr))) (count row : Nat) (base : TypeExpr) :
    Reading DispatchType := do
  let cell := image.layout.cellOfRow image.view Table.typeDef row
  let flags ← physical (cell 0)
  let first ← physical (cell 5)
  let finish ← if row == count then pure (image.layout.rowCount Table.methodDef + 1)
    else physical (image.layout.cellOfRow image.view Table.typeDef (row+1) 5)
  let mut methods := #[]
  for index in [first:finish] do
    let method ← classMethod prepared image core index
    methods := methods.push { method with overrides := overrides[index]?.getD [] }
  let owned ← interfaces[row]!.toList.mapM (interfaceName image)
  guard owned.Nodup
  return {
    identity := ← className image row, valueType := false, interfaceType := false,
    assembly := ⟨image.assembly⟩, base, abstractType := flags &&& 0x80 != 0,
    interfaces := owned, methods := methods.toList }

/-- Select the declaring class and its descendants across the physically resolved graph. -/
private def hierarchy (graph : ParentGraph) (prepared : List PreparedImage)
    (home : PreparedImage) (owner : Nat) (includeDerived : Bool) : Reading (List DispatchType) := do
  let some origin := graph.modules.find? (·.image.assembly == home.assembly) | failure
  guard (owner > 0 && owner ≤ origin.count)
  let root := origin.offset + owner
  let mut types := #[]
  for group in graph.modules do
    let image := group.image
    let mut selected := #[]
    for i in [:group.count] do
      let node := group.offset + i + 1
      unless includeDerived || node == root do continue
      if ← descends graph.parents root graph.parents.size node false then
        selected := selected.push (i + 1)
    if selected.isEmpty then continue
    guard (image.layout.rowCount 5 == 0)
    let interfaces ← interfacesByOwner image group.count
    let core := primitiveScope image
    let overrides ← localOverrides prepared image core interfaces selected
    for row in selected do
      let parent := graph.parents[group.offset + row]!
      let base ← if parent == 0 then pure TypeExpr.void else do
        let some target := graph.modules.find? (fun part =>
          part.offset < parent && parent ≤ part.offset + part.count) | failure
        className target.image (parent - target.offset)
      types := types.push (← readClass prepared image core interfaces overrides group.count row base)
  return types.toList

/-- Reconstruct a class catalog from the named class and the supplied physical modules. -/
def physicalHierarchy (image : PreparedImage) (owner : Nat) (includeDerived := true)
    (prepared : List PreparedImage := []) : OptionT (Except AuditError) (List DispatchType) := do
  let pins := if prepared.isEmpty then [image] else prepared
  hierarchy (← parentGraph pins) pins image owner includeDerived

/-- Read a class-test token at its original instruction boundary and check the class in
    its defining module. -/
private def testedClass (graph : ParentGraph) (prepared : List PreparedImage) (home : PreparedImage)
    (instruction : RawInstruction) (code : Array Nat) : Reading DispatchType := do
  let .type target := instruction.operand | failure
  let #[op, a, b, c, d] := code.extract instruction.offset (instruction.offset + 5) | failure
  guard (op == instruction.opcode)
  let token := a + 256 * (b + 256 * (c + 256 * d))
  let (image, row) ← testDefinition prepared home token
  unless target == (← className image row) do throwThe AuditError (.dispatchMismatch token)
  let [entry] ← hierarchy graph prepared image row false | failure
  return entry

/-- The union of all physical class hierarchies and tested classes selected by the original body.
    Live sites must dispatch through the exact target table validated against that hierarchy. -/
private def selected (graph : ParentGraph) (prepared : List PreparedImage) (image : PreparedImage) (item : MethodEvidence)
    (methods : List SpecializedMethod) : Reading (List DispatchType) := do
  guard (item.assembly.identity == image.assembly)
  let mut code := #[]
  if item.original.code.any (fun i => i.opcode == 0x74 || i.opcode == 0x75) then
    let bytes := item.body.bytes
    physical (bodyBound image item.original.token bytes)
    let .ok env := item.body.environment | failure
    let .ok decoded := decodeBody env item.original.genericParameters.length
      item.original.ownerParameters.length item.body | failure
    unless decoded.code == item.original.code do
      throwThe AuditError (.dispatchMismatch item.original.token)
    let first :: _ := bytes | failure
    code := (bytes.drop (if first % 4 == 2 then 1 else 12)).toArray
  let mut types : List DispatchType := []
  for (instruction, pc) in item.original.code.zipIdx do
    if instruction.opcode == 0xfe16 then failure
    if instruction.opcode == 0x74 || instruction.opcode == 0x75 then
      let entry ← testedClass graph prepared image instruction code
      unless types.contains entry do types := entry :: types
      continue
    unless instruction.opcode == 0x6f do continue
    let .call site := instruction.operand
      | throwThe AuditError (.dispatchMismatch item.original.token)
    let .managed token := site.target | failure
    guard (tableOf token == Table.methodDef && image.layout.rowCount 5 == 0)
    let attr ← physical (image.layout.cell image.view token 2)
    unless attr &&& virtualMethodAttribute != 0 do continue
    let owner := (← physical (methodDeclaringType image token)) % 2^24
    let slot ← classMethod prepared image (primitiveScope image) (token % 2^24)
    unless site.declaringType == (← className image owner) && slot.name == site.name &&
        slot.hasThis && slot.returnType == site.returnType && slot.parameters == site.parameterTypes
      do throwThe AuditError (.dispatchMismatch token)
    let entries ← hierarchy graph prepared image owner true
    if item.reachable[pc]? == some true then
      let some (_, .virtual targets) := item.links.find? (·.1 == pc)
        | throwThe AuditError (.dispatchMismatch token)
      unless virtualTableValid entries (findDispatchType entries) (fun index => methods[index]?)
          site targets site.argumentCount do throwThe AuditError (.dispatchMismatch token)
    types := types ++ entries.filter (fun entry => !types.contains entry)
  return types

/-- All physical parent edges resolve in the supplied modules or end at a recognized root.
    Every chain reaches a root within the total number of TypeDefs. -/
def ParentsBound (prepared : List PreparedImage) : Prop :=
  ∃ graph, (parentGraph prepared).run = .ok (some graph)

/-- A physical catalog contains all claimed declarations with the same multiplicities.
    The order of declarations in the metadata can differ from the extractor's name order. -/
def CatalogBound (prepared : List PreparedImage) (image : PreparedImage) (item : MethodEvidence)
    (methods : List SpecializedMethod) : Prop :=
  ∃ graph actual, (parentGraph prepared).run = .ok (some graph) ∧
    (selected graph prepared image item methods).run = .ok (some actual) ∧
    actual.Perm item.dispatchTypes

/-- Whether the claimed catalog equals the physically reconstructed declarations. -/
private def checkItem (graph : ParentGraph) (prepared : List PreparedImage) (image : PreparedImage)
    (methods : List SpecializedMethod) (item : MethodEvidence) : Except AuditError Bool := do
  let some actual ← (selected graph prepared image item methods).run | return false
  if actual.Perm item.dispatchTypes then return true
  throw (.dispatchMismatch item.original.token)

/-- Every covered method has exactly the physically reconstructed declarations. -/
private theorem bound_of_checkItem {graph prepared image methods item}
    (parents : (parentGraph prepared).run = .ok (some graph))
    (checked : checkItem graph prepared image methods item = .ok true) :
    CatalogBound prepared image item methods := by
  unfold checkItem at checked
  obtain ⟨value, physical, rest⟩ := CIL.Safety.except_bind_ok checked
  cases value with
  | none => cases rest
  | some actual =>
    refine ⟨graph, actual, parents, physical, ?_⟩
    by_cases same : actual.Perm item.dispatchTypes
    · exact same
    · simp [same, throw] at rest
#print axioms bound_of_checkItem

/-- Reconstruct every selected catalog in the physical module owning its method body. -/
private def checkHome (graph : ParentGraph) (prepared : List PreparedImage)
    (methods : List SpecializedMethod) (items : List MethodEvidence) (home : PreparedImage) :
    Except AuditError Bool := do
  let localItems := items.filter (fun item => item.assembly.identity == home.assembly)
  if localItems.isEmpty then return true
  if prepared.any (·.assembly != home.assembly) then
    if ← platformAssembly home then return false
  return (← localItems.mapM (checkItem graph prepared home methods)).all id

/-- An accepted method has its physical catalog and a resolved parent graph over all pins. -/
private theorem bound_of_checkHome {graph prepared methods items home item}
    (parents : (parentGraph prepared).run = .ok (some graph))
    (mem : item ∈ items) (same : item.assembly.identity == home.assembly)
    (checked : checkHome graph prepared methods items home = .ok true) :
    CatalogBound prepared home item methods ∧
      ∀ other ∈ prepared, other.assembly ≠ home.assembly →
        platformAssembly home = .ok false ∧ ParentsBound prepared := by
  have localMem : item ∈ items.filter (fun i => i.assembly.identity == home.assembly) :=
    List.mem_filter.mpr ⟨mem, same⟩
  unfold checkHome at checked
  dsimp only at checked
  split at checked
  · rename_i empty
    simp_all
  have finish {bits : List Bool}
      (read : (items.filter (fun i => i.assembly.identity == home.assembly)).mapM
        (checkItem graph prepared home methods) = .ok bits)
      (all : bits.all id = true) : CatalogBound prepared home item methods := by
    obtain ⟨bit, member, result⟩ := read_member localMem read
    have yes : bit = true := List.all_eq_true.mp all bit member
    subst bit
    exact bound_of_checkItem parents result
  split at checked
  · obtain ⟨core, coreEq, rest⟩ := CIL.Safety.except_bind_ok checked
    cases core <;> simp only [Bool.false_eq_true, ite_false, ite_true] at rest
    · obtain ⟨bits, read, final⟩ := CIL.Safety.except_bind_ok rest
      exact ⟨finish read (Except.ok.inj final), fun _ _ _ => ⟨coreEq, graph, parents⟩⟩
    · cases rest
  · rename_i localOnly
    obtain ⟨bits, read, final⟩ := CIL.Safety.except_bind_ok checked
    refine ⟨finish read (Except.ok.inj final), ?_⟩
    intro other member different
    exact False.elim (localOnly (List.any_eq_true.mpr ⟨other, member, by simpa using different⟩))
#print axioms bound_of_checkHome

/-- Check every selected method in its declaring image. Each image containing a selected
    method must have a closed hierarchy relative to every other supplied pin. -/
def check (images : List PinnedImage) (pins : List AssemblyPin) (items : List MethodEvidence)
    (imports : List ImportSlot) : Except AuditError Bool := do
  let prepared ← prepare images
  unless (prepared.map (·.assembly)).Perm (pins.map (·.identity)) do return false
  if items.isEmpty then return false
  unless items.all (fun item =>
      prepared.any (fun image => item.assembly.identity == image.assembly)) do return false
  let some graph ← (parentGraph prepared).run | return false
  let covered ← prepared.mapM (checkHome graph prepared (specializationTable items) items)
  return covered.all id && imports.isEmpty && items.any (fun item => !item.dispatchTypes.isEmpty)

/-- Each selected catalog is reconstructed in the physical image that owns the method. -/
theorem bound_of_check {images pins items imports}
    (checked : check images pins items imports = .ok true) :
    ∃ prepared, prepare images = .ok prepared ∧
      (prepared.map (·.assembly)).Perm (pins.map (·.identity)) ∧
      ∀ item ∈ items, ∃ home ∈ prepared, item.assembly.identity = home.assembly ∧
        CatalogBound prepared home item (specializationTable items) ∧
        ∀ other ∈ prepared, other.assembly ≠ home.assembly →
          platformAssembly home = .ok false ∧ ParentsBound prepared := by
  unfold check at checked
  obtain ⟨prepared, preparedEq, rest⟩ := CIL.Safety.except_bind_ok checked
  split at rest <;> try cases rest
  split at rest <;> try cases rest
  split at rest <;> try cases rest
  rename_i present
  obtain ⟨graph, parents, found⟩ := CIL.Safety.except_bind_ok rest
  cases graph with
  | none => cases found
  | some graph =>
    obtain ⟨bits, scanned, final⟩ := CIL.Safety.except_bind_ok found
    have allBits := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Except.ok.inj final)).1).1
    refine ⟨prepared, preparedEq, by assumption, ?_⟩
    intro item mem
    obtain ⟨home, homeMem, same⟩ := List.any_eq_true.mp (List.all_eq_true.mp present item mem)
    obtain ⟨bit, member, probe⟩ := read_member homeMem scanned
    have covered : bit = true := List.all_eq_true.mp allBits bit member
    subst bit
    exact ⟨home, homeMem, eq_of_beq same, bound_of_checkHome parents mem same probe⟩
#print axioms bound_of_check


end StrictBinding.ClassDispatch

namespace StrictBinding
open CIL CIL.Extraction

/-- The consumer replays the dispatch coverage bit on the assemblies, methods and imports
    of the same certified extraction. -/
def DispatchCatalogsChecked (images : List PinnedImage) (pins : List AssemblyPin)
    (items : List MethodEvidence) (imports : List ImportSlot) (complete : Bool) : Prop :=
  (ClassDispatch.check images pins items imports).toOption = some complete

instance (images : List PinnedImage) (pins : List AssemblyPin) (items : List MethodEvidence)
    (imports : List ImportSlot) (complete : Bool) :
    Decidable (DispatchCatalogsChecked images pins items imports complete) :=
  inferInstanceAs (Decidable (_ = _))

/-- Each claimed method catalog is a permutation of its reconstructed physical declarations. -/
theorem DispatchCatalogsChecked.physical {images pins items imports}
    (checked : DispatchCatalogsChecked images pins items imports true) :
    ∃ prepared, prepare images = .ok prepared ∧
      (prepared.map (·.assembly)).Perm (pins.map (·.identity)) ∧
      ∀ item ∈ items, ∃ home ∈ prepared, item.assembly.identity = home.assembly ∧
        ClassDispatch.CatalogBound prepared home item (specializationTable items) ∧
        ∀ other ∈ prepared, other.assembly ≠ home.assembly →
          platformAssembly home = .ok false ∧ ClassDispatch.ParentsBound prepared := by
  apply ClassDispatch.bound_of_check (pins := pins) (imports := imports)
  cases result : ClassDispatch.check images pins items imports with
  | error err => simp [DispatchCatalogsChecked, result, Except.toOption] at checked
  | ok value => simpa [DispatchCatalogsChecked, result, Except.toOption] using checked
#print axioms DispatchCatalogsChecked.physical
end StrictBinding
