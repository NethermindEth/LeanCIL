import StrictBinding.GenericConstraints

/-! Check the complete method catalogs of local, nongeneric virtual class calls in one image. -/

namespace StrictBinding.ClassDispatch
open CIL CIL.Extraction

/-- Unsupported metadata leaves coverage partial. A conflicting supported claim is an error. -/
private abbrev Reading := OptionT (Except AuditError)

/-- Structural PE errors retain the token, heap offset or column that failed. -/
private def physical (action : Except AuditError α) : Reading α := liftM action

/-- A top-level nongeneric class identified by its unique physical declaration. -/
private def className (image : PreparedImage) (row : Nat) : Reading TypeExpr := do
  let cell := image.layout.cellOfRow image.view Table.typeDef row
  let name ← physical (image.layout.stringAt image.view (← physical (cell 1)))
  let space ← physical (image.layout.stringAt image.view (← physical (cell 2)))
  unless (← physical (enumDefinition? image 0 [space, name])) == some row do failure
  unless (← physical (physicalTypeShape image row)) == (.classType, 0) do failure
  let some simple := spelled? name | failure
  let some scope := spelled? space | failure
  guard (ordinaryTypeName scope simple)
  return .object image.identity (if scope.isEmpty then simple else scope ++ "." ++ simple)

/-- Follow a local TypeDef edge. The core Object, ValueType and Enum roots cannot descend
    from a local class. This lets a class hierarchy coexist with unrelated structs and enums. -/
private def parentRow (image : PreparedImage) (row : Nat) : Reading Nat := do
  let coded ← physical (image.layout.cellOfRow image.view Table.typeDef row typeDefExtendsColumn)
  if coded == 0 then
    guard (row == 1)
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
private def formalType (image : PreparedImage) : SigType → Reading TypeExpr
  | .primitive 1 => return .void
  | .primitive code => do
    let some name := (primitiveName code).bind spelled? | failure
    return .atom runtimeScope name
  | .named false token => do
    guard (tableOf token == Table.typeDef)
    className image (token % 2^24)
  | _ => failure

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

/-- Enumerate every physical descendant, including abstract intermediates, and every MethodDef
    each one owns. MethodPtr, InterfaceImpl and MethodImpl are outside this reader's coverage. -/
def physicalHierarchy (image : PreparedImage) (owner : Nat) :
    OptionT (Except AuditError) (List DispatchType) := do
  guard (image.layout.rowCount 5 == 0 && image.layout.rowCount 9 == 0 &&
    image.layout.rowCount 25 == 0)
  -- A File row with metadata introduces another module whose classes this image cannot enumerate.
  for i in [:image.layout.rowCount 0x26] do
    guard ((← physical (image.layout.cellOfRow image.view 0x26 (i+1) 0)) == 1)
  let count := image.layout.rowCount Table.typeDef
  let mut parents := #[0]
  for i in [:count] do parents := parents.push (← parentRow image (i+1))
  let mut types := #[]
  for i in [:count] do
    let row := i+1
    unless ← descends parents owner count row false do continue
    let cell := image.layout.cellOfRow image.view Table.typeDef row
    let flags ← physical (cell 0)
    let first ← physical (cell 5)
    let finish ← if row == count then pure (image.layout.rowCount Table.methodDef + 1)
      else physical (image.layout.cellOfRow image.view Table.typeDef (row+1) 5)
    let mut methods := #[]
    for index in [first:finish] do methods := methods.push (← classMethod image index)
    let base ← if parents[row]! == 0 then pure TypeExpr.void else className image parents[row]!
    types := types.push {
      identity := ← className image row, valueType := false, interfaceType := false,
      assembly := {identity := image.identity}, base, abstractType := flags &&& 0x80 != 0,
      interfaces := [], methods := methods.toList }
  return types.toList

/-- The union of all physical class hierarchies selected by a method's original callvirt sites.
    Live sites must dispatch through the exact target table validated against that hierarchy. -/
private def selected (image : PreparedImage) (item : MethodEvidence)
    (methods : List SpecializedMethod) : Reading (List DispatchType) := do
  guard (item.assembly.identity == image.identity)
  let mut types : List DispatchType := []
  for (instruction, pc) in item.original.code.zipIdx do
    if [0xfe16, 0x74, 0x75].contains instruction.opcode then failure
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

/-- Whether this method is covered and whether it selects any virtual class hierarchy. -/
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

/-- The physical catalog of each supported method agrees in both directions with its evidence.
    Empty selections and incomplete reference, import, cast or constrained coverage stay partial. -/
def check (images : List PinnedImage) (pins : List AssemblyPin) (items : List MethodEvidence)
    (imports : List ImportSlot) : Except AuditError Bool := do
  let [pin] := pins | return false
  let [supplied] := images | return false
  unless supplied.identity == pin.identity do return false
  let image ← prepareOne supplied
  checkMethods image items imports

/-- Complete image coverage entails a physical catalog for every method of the extraction. -/
theorem bound_of_check {images pins items imports}
    (checked : check images pins items imports = .ok true) :
    ∃ supplied image, images = [supplied] ∧ prepareOne supplied = .ok image ∧
      ∀ item ∈ items, CatalogBound image item (specializationTable items) := by
  unfold check at checked
  split at checked <;> try cases checked
  split at checked <;> try cases checked
  split at checked <;> try cases checked
  obtain ⟨image, prepared, complete⟩ := CIL.Safety.except_bind_ok checked
  exact ⟨_, image, rfl, prepared, bound_of_checkMethods complete⟩
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
    ∃ supplied image, images = [supplied] ∧ prepareOne supplied = .ok image ∧
      ∀ item ∈ items, ClassDispatch.CatalogBound image item (specializationTable items) := by
  apply ClassDispatch.bound_of_check (pins := pins) (imports := imports)
  cases result : ClassDispatch.check images pins items imports with
  | error err => simp [DispatchCatalogsChecked, result, Except.toOption] at checked
  | ok value => simpa [DispatchCatalogsChecked, result, Except.toOption] using checked
#print axioms DispatchCatalogsChecked.physical
end StrictBinding
