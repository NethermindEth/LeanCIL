import StrictBinding.GenericConstraints

/-! Check the physical catalogs of local virtual calls and class tests against pinned metadata. -/

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

/-- Local parent edges in a single metadata module. The only external roots admitted here
    are the core Object, ValueType and Enum declarations. -/
private def localParents (image : PreparedImage) : Reading (Array Nat) := do
  -- A File row with metadata introduces another module whose classes this image cannot enumerate.
  for i in [:image.layout.rowCount 0x26] do
    guard ((← physical (image.layout.cellOfRow image.view 0x26 (i+1) 0)) == 1)
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

/-- Read the token at a class-test instruction boundary in the physically bound method body. -/
private def testedClass (image : PreparedImage) (instruction : RawInstruction) (code : Array Nat) :
    Reading DispatchType := do
  let .type target := instruction.operand | failure
  let #[op, a, b, c, d] := code.extract instruction.offset (instruction.offset + 5) | failure
  guard (op == instruction.opcode)
  let token := a + 256 * (b + 256 * (c + 256 * d))
  guard (tableOf token == Table.typeDef)
  let row := token % 2^24
  let _ ← physical (image.layout.rowAt token)
  unless target == (← className image row) do throwThe AuditError (.dispatchMismatch token)
  let [entry] ← physicalHierarchy image row false | failure
  return entry

/-- The union of all physical class hierarchies and tested classes selected by the original body.
    Live sites must dispatch through the exact target table validated against that hierarchy. -/
private def selected (image : PreparedImage) (item : MethodEvidence)
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
      let entry ← testedClass image instruction code
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
def CatalogBound (image : PreparedImage) (item : MethodEvidence)
    (methods : List SpecializedMethod) : Prop :=
  ∃ actual, (selected image item methods).run = .ok (some actual) ∧ actual.Perm item.dispatchTypes

/-- Whether this method is covered and whether its instructions select any class declarations. -/
private def checkItem (image : PreparedImage) (methods : List SpecializedMethod)
    (item : MethodEvidence) : Except AuditError (Bool × Bool) := do
  let some actual ← (selected image item methods).run | return (false, false)
  if actual.Perm item.dispatchTypes then return (true, !actual.isEmpty)
  throw (.dispatchMismatch item.original.token)

/-- Every covered method has exactly the physically reconstructed declarations. -/
private theorem bound_of_checkItem {image methods item any}
    (checked : checkItem image methods item = .ok (true, any)) :
    CatalogBound image item methods := by
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

/-- Every supported method selects its complete physical class catalog. -/
private def checkMethods (image : PreparedImage) (items : List MethodEvidence)
    (imports : List ImportSlot) : Except AuditError Bool := do
  let coverage ← items.mapM (checkItem image (specializationTable items))
  return imports.isEmpty && coverage.all Prod.fst && coverage.any Prod.snd

/-- Every individual method was checked against the same physical image and program. -/
theorem bound_of_checkMethods {image items imports}
    (checked : checkMethods image items imports = .ok true) :
    ∀ item ∈ items, CatalogBound image item (specializationTable items) := by
  unfold checkMethods at checked
  obtain ⟨coverage, read, yes⟩ := CIL.Safety.except_bind_ok checked
  have all := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Except.ok.inj yes)).1).2
  intro item mem
  obtain ⟨⟨full, any⟩, member, result⟩ := read_member mem read
  have covered : full = true := List.all_eq_true.mp all (full, any) member
  subst full
  exact bound_of_checkItem result
#print axioms bound_of_checkMethods

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

/-- Every supplied pin participates in the audit. The selected class calls are local to one
    image. Other images must have no descendants that could contribute a dispatch target. -/
def check (images : List PinnedImage) (pins : List AssemblyPin) (items : List MethodEvidence)
    (imports : List ImportSlot) : Except AuditError Bool := do
  unless (images.map (·.identity)).Perm (pins.map (·.identity)) do return false
  let first :: _ := items | return false
  let prepared ← prepare images
  let some home := prepared.find? (·.identity == first.assembly.identity) | return false
  unless ← checkMethods home items imports do return false
  let covered ← prepared.mapM (checkNeighbour home)
  return covered.all id

/-- The selected pin is the physical source of every catalog. Each other supplied image has
    only local class parent chains ending at core roots. -/
theorem bound_of_check {images pins items imports}
    (checked : check images pins items imports = .ok true) :
    ∃ prepared home, prepare images = .ok prepared ∧ home ∈ prepared ∧
      (images.map (·.identity)).Perm (pins.map (·.identity)) ∧
      (∀ other ∈ prepared, other.identity ≠ home.identity →
        platformAssembly home = .ok false ∧ ParentsBound other) ∧
      ∀ item ∈ items, CatalogBound home item (specializationTable items) := by
  unfold check at checked
  split at checked <;> try cases checked
  split at checked <;> try cases checked
  obtain ⟨prepared, preparedEq, rest⟩ := CIL.Safety.except_bind_ok checked
  split at rest <;> try cases rest
  rename_i home found
  obtain ⟨localCheck, methodsEq, rest⟩ := CIL.Safety.except_bind_ok rest
  cases localCheck <;> simp only [Bool.false_eq_true, ↓reduceIte] at rest
  · cases rest
  obtain ⟨bits, scanned, all⟩ := CIL.Safety.except_bind_ok rest
  have allBits : bits.all id = true := Except.ok.inj all
  refine ⟨prepared, home, preparedEq, List.mem_of_find?_eq_some found, by assumption, ?_,
    bound_of_checkMethods methodsEq⟩
  intro other mem different
  obtain ⟨bit, member, probe⟩ := read_member mem scanned
  have full : bit = true := List.all_eq_true.mp allBits bit member
  subst bit
  unfold checkNeighbour at probe
  simp [different] at probe
  obtain ⟨core, coreEq, continued⟩ := CIL.Safety.except_bind_ok probe
  cases core <;> simp [pure, Except.pure] at continued
  obtain ⟨value, valueEq, yes⟩ := CIL.Safety.except_bind_ok continued
  cases value <;> simp at yes
  exact ⟨coreEq, valueEq⟩
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
    ∃ prepared home, prepare images = .ok prepared ∧ home ∈ prepared ∧
      (images.map (·.identity)).Perm (pins.map (·.identity)) ∧
      (∀ other ∈ prepared, other.identity ≠ home.identity →
        platformAssembly home = .ok false ∧ ClassDispatch.ParentsBound other) ∧
      ∀ item ∈ items, ClassDispatch.CatalogBound home item (specializationTable items) := by
  apply ClassDispatch.bound_of_check (pins := pins) (imports := imports)
  cases result : ClassDispatch.check images pins items imports with
  | error err => simp [DispatchCatalogsChecked, result, Except.toOption] at checked
  | ok value => simpa [DispatchCatalogsChecked, result, Except.toOption] using checked
#print axioms DispatchCatalogsChecked.physical
end StrictBinding
