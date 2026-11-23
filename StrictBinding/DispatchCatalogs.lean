import StrictBinding.GenericConstraints

/-! Check physical class tests and local virtual slot catalogs against the pinned images. -/

namespace StrictBinding.ClassDispatch
open CIL CIL.Extraction

/-- Unsupported metadata leaves coverage partial. A conflicting supported claim is an error. -/
private abbrev Reading := OptionT (Except AuditError)

/-- Structural PE errors retain the token, heap offset or column that failed. -/
private def physical (action : Except AuditError α) : Reading α := liftM action

/-- The unambiguous Cecil spelling of a physical TypeDef and its enclosing declarations. -/
private def declarationName (image : PreparedImage) : Nat → Nat → Reading String
  | 0, row => throwThe AuditError (.typeDefMismatch row .nesting)
  | fuel + 1, row => do
    let cell := image.layout.cellOfRow image.view Table.typeDef row
    let name ← physical (image.layout.stringAt image.view (← physical (cell typeNameColumn)))
    let space ← physical (image.layout.stringAt image.view (← physical (cell typeNamespaceColumn)))
    let flags ← physical (cell typeDefFlagsColumn)
    let parent ← if visibilityOf flags < nestedVisibility then pure 0
      else physical (enclosingTypeRow image row flags)
    unless (← physical (enumDefinition? image parent [space, name])) == some row do failure
    let some simple := spelled? name | failure
    let some scope := spelled? space | failure
    guard (ordinaryTypeName scope simple)
    if parent == 0 then return if scope.isEmpty then simple else scope ++ "." ++ simple
    guard (scope.isEmpty && (← physical (physicalTypeShape image parent)).2 == 0)
    return (← declarationName image fuel parent) ++ "/" ++ simple

/-- A uniquely named nongeneric class or interface from the selected image. -/
private def localName (image : PreparedImage) (row : Nat) (kind : TypeKind) : Reading String := do
  unless (← physical (physicalTypeShape image row)) == (kind, 0) do failure
  declarationName image row row

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

/-- Primitive signatures and references to other supported local classes. -/
private def formalElement (image : PreparedImage) : SigType → Reading TypeExpr
  | .primitive 1 => return .void
  | .primitive code => do
    let some name := (primitiveName code).bind spelled? | failure
    return .atom runtimeScope name
  | .named false token => do
    guard (tableOf token == Table.typeDef)
    className image (token % 2^24)
  | _ => failure

/-- A managed reference in a slot signature preserves its physical element type. -/
private def formalType (image : PreparedImage) : SigType → Reading TypeExpr
  | .byref element => do
    let value ← formalElement image element
    guard (value != .void)
    return .byref value
  | element => formalElement image element

/-- A nongeneric managed MethodDef, with its physical flags, signature, and body presence. -/
private def classMethod (image : PreparedImage) (row : Nat) : Reading DispatchMethod := do
  let cell := image.layout.cellOfRow image.view Table.methodDef row
  let implementation ← physical (cell 1)
  let attributes ← physical (cell 2)
  let some name := spelled? (← physical (image.layout.stringAt image.view (← physical (cell 3))))
    | failure
  let blob ← physical (image.layout.blobAt image.view (← physical (cell 4)))
  let .ok sig := decodeMethodSig blob | failure
  guard (sig.genericArity == 0 && (sig.convention == 0 || sig.convention == 32))
  guard (implementation == 0)
  let token := StrictBinding.tokenOf Table.methodDef row
  let _ ← physical (parameterDeclarations image token [])
  let isAbstract := attributes &&& 0x400 != 0
  let hasBody := (← physical (cell 0)) != 0
  let hasThis := sig.convention == 32
  guard (hasBody == !isAbstract && hasThis == (attributes &&& 0x10 == 0))
  return {
    token, name, hasThis, isPublic := attributes % 8 == 6,
    isAbstract, isVirtual := attributes &&& virtualMethodAttribute != 0, hasBody, genericArity := 0,
    explicitThis := false, callingConvention := 0, attributes, implementation,
    returnType := ← formalType image sig.result,
    parameters := ← sig.parameters.mapM (formalType image),
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
  return .atom image.identity name

/-- Local MethodImpl rows bind the implementing MethodDef to its class and the overridden
    MethodDef to its interface. Both signatures describe the same nongeneric instance slot. -/
private def localOverrides (image : PreparedImage) (interfaces : Array (Array Nat))
    (parents : Array Nat) (root : Nat) :
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
    unless ← descends parents root (image.layout.rowCount Table.typeDef) owner false do continue
    guard (slot % 2 == 0)
    let slotToken ← physical (checkedTokenOf Table.methodDef (slot / 2) .rowOverflow)
    let interfaceToken ← physical (methodDeclaringType image slotToken)
    let some direct := interfaces[owner]? | failure
    guard (direct.contains ((interfaceToken % 2^24) * 4))
    let name ← localName image (interfaceToken % 2^24) .interface
    let slotOwner := TypeExpr.atom image.identity name
    let implementation ← classMethod image (body / 2)
    let declaration ← classMethod image (slot / 2)
    guard (implementation.hasThis && implementation.hasBody && implementation.isVirtual &&
      declaration.hasThis && declaration.isVirtual && declaration.isAbstract &&
      implementation.returnType == declaration.returnType &&
      implementation.parameters == declaration.parameters)
    let binding := (slotToken, slotOwner)
    guard (!bindings[body / 2]!.contains binding)
    bindings := bindings.modify (body / 2) (binding :: ·)
  return bindings.map List.reverse

/-- File rows with metadata introduce classes in other modules of the same assembly. -/
private def singleModule (image : PreparedImage) : Reading Unit := do
  for i in [:image.layout.rowCount 0x26] do
    guard ((← physical (image.layout.cellOfRow image.view 0x26 (i+1) 0)) == 1)

/-- Local parent edges in a single metadata module. The only external roots admitted here
    are the core Object, ValueType and Enum declarations. -/
private def localParents (image : PreparedImage) : Reading (Array Nat) := do
  singleModule image
  let count := image.layout.rowCount Table.typeDef
  let mut parents := #[0]
  for i in [:count] do parents := parents.push (← parentRow image (i+1))
  return parents

/-- The owner's physical declaration, with its MethodDefs and direct interface implementations.
    Virtual calls also require every descendant, including abstract intermediates. -/
def physicalHierarchy (image : PreparedImage) (owner : Nat) (includeDerived := true) :
    OptionT (Except AuditError) (List DispatchType) := do
  guard (image.layout.rowCount 5 == 0)
  let count := image.layout.rowCount Table.typeDef
  let interfaces ← interfacesByOwner image count
  let parents ← localParents image
  let overrides ← localOverrides image interfaces parents owner
  let mut types := #[]
  for i in [:count] do
    let row := i+1
    unless includeDerived || row == owner do continue
    unless ← descends parents owner count row false do continue
    let cell := image.layout.cellOfRow image.view Table.typeDef row
    let flags ← physical (cell 0)
    let first ← physical (cell 5)
    let finish ← if row == count then pure (image.layout.rowCount Table.methodDef + 1)
      else physical (image.layout.cellOfRow image.view Table.typeDef (row+1) 5)
    let mut methods := #[]
    for index in [first:finish] do
      let method ← classMethod image index
      methods := methods.push { method with overrides := overrides[index]?.getD [] }
    let base ← if parents[row]! == 0 then pure TypeExpr.void else className image parents[row]!
    let owned ← interfaces[row]!.toList.mapM (interfaceName image)
    guard owned.Nodup
    types := types.push {
      identity := ← className image row, valueType := false, interfaceType := false,
      assembly := {identity := image.identity}, base, abstractType := flags &&& 0x80 != 0,
      interfaces := owned, methods := methods.toList }
  return types.toList

/-- Read the namespace, outer name and nested names from the TypeRef chain, ending at
    the physical AssemblyRef. A cyclic or module-scoped reference is uncovered. -/
private def referencedClass (image : PreparedImage) : Nat → Nat → List (List Nat) →
    Reading (String × List (List Nat))
  | 0, _, _ => failure
  | fuel + 1, token, nested => do
    let cell := image.layout.cell image.view token
    let scope ← physical (cell 0)
    let name ← physical (image.layout.stringAt image.view (← physical (cell typeNameColumn)))
    let space ← physical (image.layout.stringAt image.view (← physical (cell typeNamespaceColumn)))
    match scope % 4 with
    | 2 =>
      let assembly ← physical (checkedTokenOf Table.assemblyRef (scope / 4) .rowOverflow)
      return (← physical (referenceIdentity image assembly), space :: name :: nested)
    | 3 =>
      guard space.isEmpty
      let enclosing ← physical (checkedTokenOf Table.typeRef (scope / 4) .rowOverflow)
      referencedClass image fuel enclosing (space :: name :: nested)
    | _ => failure

/-- Locate a class at its TypeDef or through an AssemblyRef in the body that tests it.
    Every forwarded declaration requires the full chain of pinned images. -/
private def testDefinition (prepared : List PreparedImage) (home : PreparedImage) (token : Nat) :
    Reading (PreparedImage × Nat) := do
  let _ ← physical (home.layout.rowAt token)
  if tableOf token == Table.typeDef then return (home, token % 2^24)
  guard (tableOf token == Table.typeRef)
  let (identity, parts) ← referencedClass home (home.layout.rowCount Table.typeRef) token []
  let some target := prepared.find? (·.identity == identity) | failure
  singleModule target
  match ← physical (definitionRoute target parts) with
  | .defined row => return (target, row)
  | .forwarded scope =>
    for image in prepared do singleModule image
    let some destination ← physical (findPinnedDefinition prepared parts scope prepared.length) | failure
    return destination

/-- Read a class-test token at its original instruction boundary and check the class in
    its defining module. -/
private def testedClass (prepared : List PreparedImage) (home : PreparedImage)
    (instruction : RawInstruction) (code : Array Nat) : Reading DispatchType := do
  let .type target := instruction.operand | failure
  let #[op, a, b, c, d] := code.extract instruction.offset (instruction.offset + 5) | failure
  guard (op == instruction.opcode)
  let token := a + 256 * (b + 256 * (c + 256 * d))
  let (image, row) ← testDefinition prepared home token
  unless target == (← className image row) do throwThe AuditError (.dispatchMismatch token)
  let [entry] ← physicalHierarchy image row false | failure
  return entry

/-- The union of all physical class hierarchies and tested classes selected by the original body.
    Live sites must dispatch through the exact target table validated against that hierarchy. -/
private def selected (prepared : List PreparedImage) (image : PreparedImage) (item : MethodEvidence)
    (methods : List SpecializedMethod) : Reading (List DispatchType) := do
  guard (item.assembly.identity == image.identity)
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
      let entry ← testedClass prepared image instruction code
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
    let slot ← classMethod image (token % 2^24)
    unless site.declaringType == (← className image owner) && slot.name == site.name &&
        slot.hasThis && slot.returnType == site.returnType && slot.parameters == site.parameterTypes
      do throwThe AuditError (.dispatchMismatch token)
    let entries ← physicalHierarchy image owner
    if item.reachable[pc]? == some true then
      let some (_, .virtual targets) := item.links.find? (·.1 == pc)
        | throwThe AuditError (.dispatchMismatch token)
      unless virtualTableValid entries (findDispatchType entries) (fun index => methods[index]?)
          site targets site.argumentCount do throwThe AuditError (.dispatchMismatch token)
    types := types ++ entries.filter (fun entry => !types.contains entry)
  return types

/-- A physical catalog contains all claimed declarations with the same multiplicities.
    The order of declarations in the metadata can differ from the extractor's name order. -/
def CatalogBound (prepared : List PreparedImage) (image : PreparedImage) (item : MethodEvidence)
    (methods : List SpecializedMethod) : Prop :=
  ∃ actual, (selected prepared image item methods).run = .ok (some actual) ∧
    actual.Perm item.dispatchTypes

/-- Whether the claimed catalog equals the physically reconstructed declarations. -/
private def checkItem (prepared : List PreparedImage) (image : PreparedImage)
    (methods : List SpecializedMethod)
    (item : MethodEvidence) : Except AuditError Bool := do
  let some actual ← (selected prepared image item methods).run | return false
  if actual.Perm item.dispatchTypes then return true
  throw (.dispatchMismatch item.original.token)

/-- Every covered method has exactly the physically reconstructed declarations. -/
private theorem bound_of_checkItem {prepared image methods item}
    (checked : checkItem prepared image methods item = .ok true) :
    CatalogBound prepared image item methods := by
  unfold checkItem at checked
  obtain ⟨value, physical, rest⟩ := CIL.Safety.except_bind_ok checked
  cases value with
  | none => cases rest
  | some actual =>
    refine ⟨actual, physical, ?_⟩
    by_cases same : actual.Perm item.dispatchTypes
    · exact same
    · simp [same, throw] at rest
#print axioms bound_of_checkItem

/-- An additional image has no class deriving from a non-core class of another assembly.
    Every declared parent chain reaches a recognized root, and no File row adds metadata. -/
private def closedParents (image : PreparedImage) : Reading Unit := do
  let parents ← localParents image
  let count := image.layout.rowCount Table.typeDef
  for i in [:count] do
    let _ ← descends parents 0 count (i+1) false

/-- Physical inheritance in a neighbour of the selected class hierarchy is closed locally. -/
def ParentsBound (image : PreparedImage) : Prop := (closedParents image).run = .ok (some ())

/-- The image of the selected slot is checked by checkMethods. Each other image must have
    a closed parent graph, and the selected slot cannot belong to a core assembly in that case. -/
private def checkNeighbour (home image : PreparedImage) : Except AuditError Bool := do
  if image.identity == home.identity then return true
  if ← platformAssembly home then return false
  let covered ← (closedParents image).run
  return covered.isSome

/-- Each method uses its own assembly's physical rows and the whole program's method indices. -/
private def checkHome (prepared : List PreparedImage) (methods : List SpecializedMethod)
    (items : List MethodEvidence) (home : PreparedImage) : Except AuditError Bool := do
  let localItems := items.filter (fun item => item.assembly.identity == home.identity)
  if localItems.isEmpty then return true
  let coverage ← localItems.mapM (checkItem prepared home methods)
  unless coverage.all id do return false
  let neighbours ← prepared.mapM (checkNeighbour home)
  return neighbours.all id

/-- A checked method has the physical catalog in its own image. No other supplied image has
    a class deriving from a non-core class in that image. -/
private theorem bound_of_checkHome {prepared methods items home item}
    (mem : item ∈ items) (same : item.assembly.identity == home.identity)
    (checked : checkHome prepared methods items home = .ok true) :
    CatalogBound prepared home item methods ∧
      ∀ other ∈ prepared, other.identity ≠ home.identity →
        platformAssembly home = .ok false ∧ ParentsBound other := by
  have localMem : item ∈ items.filter (fun i => i.assembly.identity == home.identity) :=
    List.mem_filter.mpr ⟨mem, same⟩
  unfold checkHome at checked
  dsimp only at checked
  split at checked
  · rename_i empty
    simp_all
  obtain ⟨coverage, read, rest⟩ := CIL.Safety.except_bind_ok checked
  split at rest <;> try cases rest
  rename_i all
  obtain ⟨bit, member, result⟩ := read_member localMem read
  have yes : bit = true := List.all_eq_true.mp all bit member
  subst bit
  refine ⟨bound_of_checkItem result, ?_⟩
  obtain ⟨bits, scanned, final⟩ := CIL.Safety.except_bind_ok rest
  have allBits : bits.all id = true := Except.ok.inj final
  intro other otherMem different
  obtain ⟨bit, member, probe⟩ := read_member otherMem scanned
  have full : bit = true := List.all_eq_true.mp allBits bit member
  subst bit
  unfold checkNeighbour at probe
  simp [different] at probe
  obtain ⟨core, coreEq, continued⟩ := CIL.Safety.except_bind_ok probe
  cases core <;> simp [pure, Except.pure] at continued
  obtain ⟨value, valueEq, yes⟩ := CIL.Safety.except_bind_ok continued
  cases value <;> simp at yes
  exact ⟨coreEq, valueEq⟩
#print axioms bound_of_checkHome

/-- Check every selected method in its declaring image. Each image containing a selected
    method must have a closed hierarchy relative to every other supplied pin. -/
def check (images : List PinnedImage) (pins : List AssemblyPin) (items : List MethodEvidence)
    (imports : List ImportSlot) : Except AuditError Bool := do
  unless (images.map (·.identity)).Perm (pins.map (·.identity)) do return false
  if items.isEmpty then return false
  let prepared ← prepare images
  unless items.all (fun item => prepared.any (fun image => item.assembly.identity == image.identity))
    do return false
  let covered ← prepared.mapM (checkHome prepared (specializationTable items) items)
  return covered.all id && imports.isEmpty && items.any (fun item => !item.dispatchTypes.isEmpty)

/-- Each selected catalog is reconstructed in the physical image that owns the method. -/
theorem bound_of_check {images pins items imports}
    (checked : check images pins items imports = .ok true) :
    ∃ prepared, prepare images = .ok prepared ∧
      (images.map (·.identity)).Perm (pins.map (·.identity)) ∧
      ∀ item ∈ items, ∃ home ∈ prepared, item.assembly.identity = home.identity ∧
        CatalogBound prepared home item (specializationTable items) ∧
        ∀ other ∈ prepared, other.identity ≠ home.identity →
          platformAssembly home = .ok false ∧ ParentsBound other := by
  unfold check at checked
  split at checked <;> try cases checked
  split at checked <;> try cases checked
  obtain ⟨prepared, preparedEq, rest⟩ := CIL.Safety.except_bind_ok checked
  split at rest <;> try cases rest
  rename_i present
  obtain ⟨bits, scanned, final⟩ := CIL.Safety.except_bind_ok rest
  have allBits := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Except.ok.inj final)).1).1
  refine ⟨prepared, preparedEq, by assumption, ?_⟩
  intro item mem
  obtain ⟨home, homeMem, same⟩ := List.any_eq_true.mp (List.all_eq_true.mp present item mem)
  obtain ⟨bit, member, probe⟩ := read_member homeMem scanned
  have covered : bit = true := List.all_eq_true.mp allBits bit member
  subst bit
  exact ⟨home, homeMem, eq_of_beq same, bound_of_checkHome mem same probe⟩
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
      (images.map (·.identity)).Perm (pins.map (·.identity)) ∧
      ∀ item ∈ items, ∃ home ∈ prepared, item.assembly.identity = home.identity ∧
        ClassDispatch.CatalogBound prepared home item (specializationTable items) ∧
        ∀ other ∈ prepared, other.identity ≠ home.identity →
          platformAssembly home = .ok false ∧ ClassDispatch.ParentsBound other := by
  apply ClassDispatch.bound_of_check (pins := pins) (imports := imports)
  cases result : ClassDispatch.check images pins items imports with
  | error err => simp [DispatchCatalogsChecked, result, Except.toOption] at checked
  | ok value => simpa [DispatchCatalogsChecked, result, Except.toOption] using checked
#print axioms DispatchCatalogsChecked.physical
end StrictBinding
