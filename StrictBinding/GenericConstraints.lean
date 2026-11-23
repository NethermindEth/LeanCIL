import StrictBinding.PlatformKinds
import CIL.Extraction.Translation

/-! Check generic parameter declarations and the direct interfaces used to satisfy them
against the GenericParam, GenericParamConstraint and InterfaceImpl tables in pinned images. -/

namespace StrictBinding

open CIL.Extraction

/-- CLI InterfaceImpl table number. -/
private def interfaceImplTable := 0x09
/-- CLI GenericParamConstraint table number. -/
private def constraintTable := 0x2C

/-- Resolve the TypeDefOrRef coded index used in a constraint or InterfaceImpl row. -/
private def constraintTarget (image : PreparedImage) (coded : Nat) : Except AuditError Nat := do
  let some table := typeDefOrRefTags[coded % 4]? | throw (.constraintMismatch coded)
  let token ← checkedTokenOf table (coded / 4) .rowOverflow
  let _ ← image.layout.rowAt token
  return token

/-- Full assembly identity recorded in the physical AssemblyRef. -/
def referenceIdentity (image : PreparedImage) (token : Nat) :
    Except AuditError String := do
  let text ← assemblyIdentityAt image.view image.layout token 0
  return String.ofList (text.map Char.ofNat)

/-- The unambiguous core assembly used to spell primitive elements in this module. -/
private def primitiveScope (image : PreparedImage) : Except AuditError String := do
  if ← platformAssembly image then return image.identity
  let cell := image.layout.cellOfRow image.view Table.typeRef
  let mut found := none
  for index in [:image.layout.rowCount Table.typeRef] do
    let row := index + 1
    unless (← image.layout.stringAt image.view (← cell row typeNameColumn)) == bytesOf "Object" &&
      (← image.layout.stringAt image.view (← cell row typeNamespaceColumn)) == systemNamespace do
      continue
    let scope ← cell row 0
    unless scope % 4 == 2 do continue
    let token ← checkedTokenOf Table.assemblyRef (scope / 4) .rowOverflow
    unless ← coreAssemblyAt image token 0 do continue
    let identity ← referenceIdentity image token
    if found.any (· != identity) then throw .uncoveredConstraint
    found := some identity
  let some core := found | throw .uncoveredConstraint
  return core

/-- A top-level simple name cannot include a namespace separator or a constructed type suffix. -/
def ordinaryTypeName (space name : String) : Bool :=
  let component := fun (c : Char) => c.isAlphanum || c == '_' || c == '`'
  !name.isEmpty && (metadataChars name).all component &&
    (metadataChars space).all (fun c => component c || c == '.')

/-- A top-level TypeDef or AssemblyRef-scoped TypeRef with its physical assembly identity. -/
private def constraintTypeParts (image : PreparedImage) (token : Nat) :
    Except AuditError (String × String) := do
  let cell := image.layout.cell image.view token
  let space ← image.layout.stringAt image.view (← cell typeNamespaceColumn)
  let name ← image.layout.stringAt image.view (← cell typeNameColumn)
  let some namespaceText := spelled? space | throw (.constraintMismatch token)
  let some nameText := spelled? name | throw (.constraintMismatch token)
  unless ordinaryTypeName namespaceText nameText do throw .uncoveredConstraint
  let scope ← match tableOf token with
    | 2 => do
      if visibilityOf (← cell typeDefFlagsColumn) ≥ nestedVisibility then
        throw .uncoveredConstraint
      unless (← enumDefinition? image 0 [space, name]) == some (token % 2^24) do
        throw (.constraintMismatch token)
      pure image.identity
    | 1 => do
      let coded ← cell 0
      unless coded % 4 == 2 do throw .uncoveredConstraint
      referenceIdentity image (← checkedTokenOf Table.assemblyRef (coded / 4) .rowOverflow)
    | _ => throw .uncoveredConstraint
  let fullName := if namespaceText.isEmpty then nameText else namespaceText ++ "." ++ nameText
  return (scope, fullName)

/-- The scoped identity of a closed constraint type. -/
private def constraintTypeName (image : PreparedImage) (token : Nat) :
    Except AuditError String := do
  let (scope, name) ← constraintTypeParts image token
  return scope ++ "::" ++ name

/-- Physical constraint identity. A VAR in an implemented interface refers to the corresponding
    closed argument of its declaring type. -/
private def constraintIdentity (image : PreparedImage) (token : Nat)
    (arguments : Option (List String) := none) :
    Except AuditError String := do
  if tableOf token != Table.typeSpec then return ← constraintTypeName image token
  let blob ← image.layout.blobAt image.view (← image.layout.cell image.view token 0)
  let .ok spec := decodeTypeSpec blob | throw .uncoveredConstraint
  match spec with
  | .genericInst false head args =>
    unless tableOf head == Table.typeDef do throw .uncoveredConstraint
    let (kind, arity) ← physicalTypeShape image (head % 2^24)
    unless kind == .interface && arity == args.toList.length do throw .uncoveredConstraint
    let core ← primitiveScope image
    let names ← args.toList.mapM fun argument => do
      match argument with
      | .primitive code =>
        let some name := (primitiveName code).bind spelled? | throw .uncoveredConstraint
        return core ++ "::" ++ name
      | .var index =>
        let some closed := arguments | throw .uncoveredConstraint
        let some name := closed[index]? | throw (.constraintMismatch token)
        return name
      | _ => throw .uncoveredConstraint
    return (← constraintTypeName image head) ++ "<" ++ String.intercalate "," names ++ ">"
  | .modified true modifier (.named false base) =>
    let name := (← constraintTypeName image modifier) ++ "!" ++ (← constraintTypeName image base)
    unless name == unmanagedTypeConstraint do throw .uncoveredConstraint
    return name
  | _ => throw .uncoveredConstraint

/-- The definition of the signature's interface head. A TypeRef follows its AssemblyRef
    and any supplied forwarders before the defining TypeDef fixes kind and arity. -/
private def interfaceHead (images : List PreparedImage) (image : PreparedImage)
    (head arity : Nat) : Except AuditError TypeExpr := do
  unless tableOf head == Table.typeDef || tableOf head == Table.typeRef do throw .uncoveredConstraint
  let (scope, name) ← constraintTypeParts image head
  let (defining, row) ← if tableOf head == Table.typeDef then pure (image, head % 2^24)
    else do
      let cell := image.layout.cell image.view head
      let space ← image.layout.stringAt image.view (← cell typeNamespaceColumn)
      let simple ← image.layout.stringAt image.view (← cell typeNameColumn)
      let some found ← findPinnedDefinition images [space, simple] (bytesOf scope)
        (images.length + 1) | throw .uncoveredConstraint
      pure found
  let (kind, count) ← physicalTypeShape defining row
  unless kind == .interface && count == arity do throw .uncoveredConstraint
  return .objectConstructor defining.identity name

/-- An open generic interface constraint with direct method parameters and primitive arguments. -/
private def openMethodConstraint? (images : List PreparedImage) (image : PreparedImage)
    (owner arity token : Nat) : Except AuditError (Option TypeExpr) := do
  if tableOf token != Table.typeSpec then return none
  let blob ← image.layout.blobAt image.view (← image.layout.cell image.view token 0)
  let .ok (.genericInst false head arguments) := decodeTypeSpec blob | return none
  let args := arguments.toList
  unless args.any (fun arg => arg matches .mvar _) do return none
  unless tableOf owner == Table.methodDef do throw (.constraintMismatch owner)
  let mut applied ← interfaceHead images image head args.length
  for arg in args do
    let element ← match arg with
      | .mvar index => do
        unless index < arity do throw (.constraintMismatch owner)
        pure (.parameter index)
      | .primitive code => do
        let some name := (primitiveName code).bind spelled? | throw .uncoveredConstraint
        if code == 1 then throw .uncoveredConstraint
        pure (.atom (← primitiveScope image) name)
      | _ => throw .uncoveredConstraint
    applied := .apply applied element
  return some applied

/-- Flags and every constraint of one physical GenericParam, in metadata order within each
    of the closed and open lists carried by the extraction. -/
private def parameterConstraint (image : PreparedImage) (owner arity row : Nat)
    (expectedFlags : Option Nat := none) (images : List PreparedImage := []) :
    Except AuditError GenericConstraint := do
  let flags ← image.layout.cellOfRow image.view Table.genericParam row 1
  if expectedFlags.any (· != flags) then throw (.constraintMismatch owner)
  let cell := image.layout.cellOfRow image.view constraintTable
  let mut types := #[]
  let mut interfaces := #[]
  for index in [:image.layout.rowCount constraintTable] do
    let constraint := index + 1
    if (← cell constraint 0) != row then continue
    let target ← constraintTarget image (← cell constraint 1)
    if let some applied ← openMethodConstraint? images image owner arity target then
      interfaces := interfaces.push applied
    else
      types := types.push (← constraintIdentity image target)
  return { flags, types := types.toList, interfaces := interfaces.toList }

/-- Physical GenericParam rows of one owner, in ordinal order and at its declared arity. -/
private def parameterRows (image : PreparedImage) (owner arity : Nat) :
    Except AuditError (List Nat) := do
  let tag := if tableOf owner == Table.methodDef then 1 else 0
  let ownerKey := 2 * (owner % 2^24) + tag
  let cell := image.layout.cellOfRow image.view Table.genericParam
  let mut rows := #[]
  for index in [:image.layout.rowCount Table.genericParam] do
    let row := index + 1
    if (← cell row 2) != ownerKey then continue
    unless (← cell row 0) == rows.size do throw (.constraintMismatch owner)
    rows := rows.push row
  unless rows.size == arity do throw (.constraintMismatch owner)
  return rows.toList

/-- All flags and constraints declared on the type or method, in parameter order. -/
def readParameterDeclarations (image : PreparedImage) (owner arity : Nat)
    (images : List PreparedImage := []) : Except AuditError (List GenericConstraint) := do
  let rows ← parameterRows image owner arity
  rows.mapM fun row => parameterConstraint image owner arity row (images := images)

/-- Compare the complete parameter list for a physical TypeOrMethodDef owner. -/
def parameterDeclarations (image : PreparedImage) (owner : Nat)
    (expected : List GenericConstraint) (images : List PreparedImage := []) : Except AuditError Unit := do
  let rows ← parameterRows image owner expected.length
  for (row, claim) in rows.zip expected do
    let actual ← parameterConstraint image owner expected.length row (some claim.flags) images
    unless actual == claim do throw (.constraintMismatch owner)

/-- Locate the physical TypeDef whose MethodList range contains this MethodDef. -/
def methodDeclaringType (image : PreparedImage) (method : Nat) : Except AuditError Nat := do
  unless tableOf method == Table.methodDef do throw (.notMethodDef method)
  let _ ← image.layout.rowAt method
  if image.layout.rowCount 0x05 != 0 then throw .uncoveredConstraint
  let target := method % 2^24
  let limit := image.layout.rowCount Table.methodDef + 1
  let cell := image.layout.cellOfRow image.view Table.typeDef
  let mut owner := none
  let mut previous := 1
  for index in [:image.layout.rowCount Table.typeDef] do
    let row := index + 1
    let first ← cell row 5
    unless previous ≤ first && first ≤ limit && (row != 1 || first == 1) do
      throw (.constraintMismatch method)
    if first ≤ target then owner := some row
    previous := first
  let some row := owner | throw (.constraintMismatch method)
  return StrictBinding.tokenOf Table.typeDef row

/-- The unique top-level value type of this scoped name, with its physical generic arity. -/
def valueLayoutOwner (image : PreparedImage) (identity : String) (fullName : List Char) :
    Except AuditError (Nat × Nat) := do
  let (reversedName, rest) := fullName.reverse.span (· != '.')
  let name := bytesOf (String.ofList reversedName.reverse)
  let space := bytesOf (String.ofList (rest.drop 1).reverse)
  let some row ← enumDefinition? image 0 [space, name] | throw .uncoveredConstraint
  unless (← constraintTypeName image (StrictBinding.tokenOf Table.typeDef row)) == identity do
    throw (.constraintMismatch (StrictBinding.tokenOf Table.typeDef row))
  let (kind, arity) ← physicalTypeShape image row
  unless kind == .valueType do throw .uncoveredConstraint
  return (row, arity)

/-- A closed value type's argument order and parameter declarations are those of its TypeDef.
    Only primitive arguments with the physical core scope can close an interface VAR here. -/
private def layoutTypeArguments (image : PreparedImage) (token : Nat) (layout : RawLayout) :
    Except AuditError (Option (List String)) := do
  let some generic := layout.generic | return none
  unless generic.owner matches .constructor .. do throw (.constraintMismatch token)
  unless genericOwnerIdentity generic.owner generic.arguments == some layout.identity &&
      generic.arity > 0 && generic.arguments.length == generic.arity do
    throw (.constraintMismatch token)
  parameterDeclarations image token (generic.constraints.map fun (flags, types) => { flags, types })
  let core ← primitiveScope image
  let names ← generic.arguments.mapM fun argument => do
    let .atom scope name := argument | throw .uncoveredConstraint
    unless scope == core && primitiveCodes.any (fun code =>
        code != 0x01 && (primitiveName code).bind spelled? == some name) do
      throw .uncoveredConstraint
    return scope ++ "::" ++ name
  return some names

/-- Direct interfaces of a concrete argument are the InterfaceImpl rows the physical type owns. -/
def layoutInterfaces (images : List PreparedImage) (layout : RawLayout) :
    Except AuditError Unit := do
  let ownerType := (layout.generic.map (·.owner)).getD (.aggregate layout.identity 0)
  let some (scope, name) := namedType ownerType | throw .uncoveredConstraint
  let some image := images.find? (·.identity == String.ofList scope) | throw .uncoveredConstraint
  let ownerName := String.ofList scope ++ "::" ++ String.ofList name
  let (owner, arity) ← valueLayoutOwner image ownerName name
  let token := StrictBinding.tokenOf Table.typeDef owner
  unless arity == (layout.generic.map (·.arity)).getD 0 do throw (.constraintMismatch token)
  let arguments ← layoutTypeArguments image token layout
  let cell := image.layout.cellOfRow image.view interfaceImplTable
  let mut interfaces := #[]
  for index in [:image.layout.rowCount interfaceImplTable] do
    let row := index + 1
    if (← cell row 0) == owner then
      let target ← constraintTarget image (← cell row 1)
      let identity ← constraintIdentity image target arguments
      if interfaces.contains identity then
        throw (.constraintMismatch (StrictBinding.tokenOf Table.typeDef owner))
      interfaces := interfaces.push identity
  unless interfaces.toList == layout.interfaces do
    throw (.constraintMismatch (StrictBinding.tokenOf Table.typeDef owner))

/-- An unhandled signature or unavailable scope leaves its claim uncovered. -/
private def constraintCovered (check : Except AuditError Unit) : Except AuditError Bool :=
  match check with
  | .ok () => .ok true
  | .error .uncoveredConstraint => .ok false
  | .error err => .error err

/-- Compare the method and owner declarations against the MethodDef and its owning TypeDef. -/
private def checkMethodConstraints (images : List PreparedImage) (item : MethodEvidence) :
    Except AuditError Bool := do
  let image ← located images item.assembly.identity
  let token := item.original.token
  let method ← constraintCovered (parameterDeclarations image token item.original.genericParameters images)
  let owner ← constraintCovered (do
    let declaring ← methodDeclaringType image token
    parameterDeclarations image declaring item.original.ownerParameters images)
  return method && owner

/-- Check every method, its owner and the interfaces of concrete arguments in the extraction.
    Imports, unsupported layout arguments and unhandled signatures leave the result partial. -/
def checkGenericConstraints (images : List PinnedImage) (methods : List MethodEvidence)
    (layouts : List RawLayout) (imports : List CIL.ImportSlot) : Except AuditError Bool := do
  let selected := methods.any fun method =>
    !method.original.genericParameters.isEmpty || !method.original.ownerParameters.isEmpty
  unless selected || layouts.any (·.generic.isSome) do return false
  let prepared ← prepare images
  let declarations ← methods.mapM (checkMethodConstraints prepared)
  let interfaces ← layouts.mapM (fun layout => constraintCovered (layoutInterfaces prepared layout))
  return imports.isEmpty && declarations.all id && interfaces.all id

/-- The completeness argument is computed from the same image and extraction as the proof. -/
def GenericConstraintsChecked (images : List PinnedImage) (methods : List MethodEvidence)
    (layouts : List RawLayout) (imports : List CIL.ImportSlot) (complete : Bool) : Prop :=
  (checkGenericConstraints images methods layouts imports).toOption = some complete

instance (images : List PinnedImage) (methods : List MethodEvidence) (layouts : List RawLayout)
    (imports : List CIL.ImportSlot) (complete : Bool) :
    Decidable (GenericConstraintsChecked images methods layouts imports complete) :=
  inferInstanceAs (Decidable (_ = _))

private theorem constraintCovered_ok {check : Except AuditError Unit}
    (complete : constraintCovered check = .ok true) : check = .ok () := by
  cases check with
  | ok value => rfl
  | error err => cases err <;> simp [constraintCovered] at complete
#print axioms constraintCovered_ok

/-- Full coverage identifies the pinned image and physical owner for every selected method
    and binds each concrete layout's interfaces in the same set of images. -/
theorem GenericConstraintsChecked.physical {images : List PinnedImage}
    {methods : List MethodEvidence}
    {layouts : List RawLayout} {imports : List CIL.ImportSlot}
    (checked : GenericConstraintsChecked images methods layouts imports true) :
    ∃ prepared, prepare images = .ok prepared ∧
      (∀ item ∈ methods, ∃ image declaring,
        located prepared item.assembly.identity = .ok image ∧
        methodDeclaringType image item.original.token = .ok declaring ∧
        parameterDeclarations image item.original.token item.original.genericParameters prepared = .ok () ∧
        parameterDeclarations image declaring item.original.ownerParameters prepared = .ok ()) ∧
      (∀ layout ∈ layouts, layoutInterfaces prepared layout = .ok ()) := by
  have done : checkGenericConstraints images methods layouts imports = .ok true := by
    cases result : checkGenericConstraints images methods layouts imports with
    | error err => simp [GenericConstraintsChecked, result, Except.toOption] at checked
    | ok value =>
      have yes : value = true := by
        simpa [GenericConstraintsChecked, result, Except.toOption] using checked
      rw [yes]
  unfold checkGenericConstraints at done
  dsimp only at done
  split at done
  · obtain ⟨prepared, built, done⟩ := CIL.Safety.except_bind_ok done
    obtain ⟨declarations, declarationsRead, done⟩ := CIL.Safety.except_bind_ok done
    obtain ⟨interfaces, interfacesRead, done⟩ := CIL.Safety.except_bind_ok done
    have complete := Except.ok.inj done
    simp only [Bool.and_eq_true] at complete
    refine ⟨prepared, built, ?_, ?_⟩
    · intro item member
      obtain ⟨value, found, read⟩ := read_member member declarationsRead
      have yes : value = true := List.all_eq_true.mp complete.1.2 value found
      unfold checkMethodConstraints at read
      obtain ⟨image, located, read⟩ := CIL.Safety.except_bind_ok read
      obtain ⟨method, methodRead, read⟩ := CIL.Safety.except_bind_ok read
      obtain ⟨owner, ownerRead, joined⟩ := CIL.Safety.except_bind_ok read
      have both := Bool.and_eq_true_iff.mp ((Except.ok.inj joined).trans yes)
      have ownerOK := constraintCovered_ok (both.2 ▸ ownerRead)
      obtain ⟨declaring, declared, parameters⟩ := CIL.Safety.except_bind_ok ownerOK
      exact ⟨image, declaring, located, declared, constraintCovered_ok (both.1 ▸ methodRead),
        parameters⟩
    · intro layout member
      obtain ⟨value, found, read⟩ := read_member member interfacesRead
      have yes : value = true := List.all_eq_true.mp complete.2 value found
      exact constraintCovered_ok (yes ▸ read)
  · cases done
#print axioms GenericConstraintsChecked.physical

end StrictBinding
