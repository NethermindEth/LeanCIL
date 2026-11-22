import StrictBinding.GenericConstraints
import StrictBinding.StaticData

/-! Reconstruct explicit and sequential scalar value layouts from the pinned PE metadata. -/

namespace StrictBinding

open CIL.Extraction

/-- ECMA-335 FieldLayout stores the offset and the owning Field. -/
private def fieldLayoutTable := 0x10

/-- Several attributes or interface implementations may legitimately name the same owner. -/
private def hasLayoutOwner (image : PreparedImage) (table owner : Nat) :
    Except AuditError Bool := do
  for index in [:image.layout.rowCount table] do
    if (← image.layout.cellOfRow image.view table (index + 1) 0) == owner then return true
  return false

/-- Reconstruct a supported value layout using only its scoped name and physical metadata.
    Custom attributes, interfaces, generics, automatic layouts and nonscalar fields are partial. -/
def physicalLayout (images : List PreparedImage) (identity : String) :
    Except AuditError (Option RawLayout) := do
  let some (scope, name) := namedType (.aggregate identity 0) | return none
  let some image := images.find? (·.identity == String.ofList scope) | return none
  let (owner, arity) ← match valueLayoutOwner image identity name with
    | .error .uncoveredConstraint => return none
    | other => other
  unless arity == 0 do return none
  let flags ← image.layout.cellOfRow image.view Table.typeDef owner typeDefFlagsColumn
  let layoutKind := flags &&& 0x18
  let explicit := layoutKind == 0x10
  unless explicit || layoutKind == 0x08 do return none
  -- HasCustomAttribute uses tag 3 for TypeDef. InterfaceImpl uses the TypeDef row directly.
  if ← hasLayoutOwner image 0x0c (owner * 32 + 3) then return none
  if ← hasLayoutOwner image 0x09 owner then return none
  let classes ← dataTableIndex image classLayoutTable 2 Table.typeDef
  let (packing, declaredSize) ← match classes[StrictBinding.tokenOf Table.typeDef owner]? with
    | none => pure ((-1 : Int), (-1 : Int))
    | some row => do
      let cell := image.layout.cellOfRow image.view classLayoutTable row
      pure (Int.ofNat (← cell 0), Int.ofNat (← cell 1))
  let offsets ← dataTableIndex image fieldLayoutTable 1 Table.field
  let (first, finish) ← platformFieldRange image owner
  let mut fields := #[]
  for field in [first:finish] do
    let cell := image.layout.cellOfRow image.view Table.field field
    let fieldFlags ← cell 0
    if fieldFlags &&& 0x10 != 0 then continue
    if fieldFlags &&& 0x1000 != 0 then return none
    let signature ← image.layout.blobAt image.view (← cell 2)
    let .ok (.primitive code) := decodeFieldSig signature | return none
    let some storage := ((primitiveName code).bind spelled?).bind primitiveField | return none
    let row := offsets[StrictBinding.tokenOf Table.field field]?
    let offset ← row.mapM fun index => image.layout.cellOfRow image.view fieldLayoutTable index 0
    unless offset.isSome == explicit do throw (.layoutMismatch identity)
    fields := fields.push { type := storage, offset }
  return some { identity, explicit, packing, declaredSize, fields := fields.toList }

/-- A supported physical layout must agree in every field, including its flags and interfaces. -/
private def checkOneLayout (images : List PreparedImage) (layout : RawLayout) :
    Except AuditError Bool := do
  let some actual ← physicalLayout images layout.identity | return false
  if actual = layout then return true
  throw (.layoutMismatch layout.identity)

/-- Check every raw layout, even when a different layout or an import leaves coverage partial. -/
def checkLayoutContent (images : List PinnedImage) (layouts : List RawLayout)
    (imports : List CIL.ImportSlot) : Except AuditError Bool := do
  if layouts.isEmpty then return false
  let prepared ← prepare images
  let coverage ← layouts.mapM (checkOneLayout prepared)
  return imports.isEmpty && coverage.all id

/-- The consumer's coverage bit is the result of checking the entire extraction's layout list. -/
def LayoutContentChecked (images : List PinnedImage) (layouts : List RawLayout)
    (imports : List CIL.ImportSlot) (complete : Bool) : Prop :=
  (checkLayoutContent images layouts imports).toOption = some complete

instance (images : List PinnedImage) (layouts : List RawLayout) (imports : List CIL.ImportSlot)
    (complete : Bool) : Decidable (LayoutContentChecked images layouts imports complete) :=
  inferInstanceAs (Decidable (_ = _))

/-- Each raw input to the certified size and offset computation comes from its physical image. -/
theorem LayoutContentChecked.physical {images : List PinnedImage} {layouts : List RawLayout}
    {imports : List CIL.ImportSlot} (checked : LayoutContentChecked images layouts imports true) :
    ∃ prepared, prepare images = .ok prepared ∧
      ∀ layout ∈ layouts, physicalLayout prepared layout.identity = .ok (some layout) := by
  have done : checkLayoutContent images layouts imports = .ok true := by
    cases result : checkLayoutContent images layouts imports with
    | error err => simp [LayoutContentChecked, result, Except.toOption] at checked
    | ok value => simpa [LayoutContentChecked, result, Except.toOption] using checked
  unfold checkLayoutContent at done
  split at done
  · cases done
  · obtain ⟨prepared, built, done⟩ := CIL.Safety.except_bind_ok done
    obtain ⟨coverage, read, done⟩ := CIL.Safety.except_bind_ok done
    refine ⟨prepared, built, ?_⟩
    intro layout member
    obtain ⟨value, found, result⟩ := read_member member read
    have yes : value = true :=
      List.all_eq_true.mp (Bool.and_eq_true_iff.mp (Except.ok.inj done)).2 value found
    subst value
    unfold checkOneLayout at result
    obtain ⟨actual, physical, compared⟩ := CIL.Safety.except_bind_ok result
    cases actual with
    | none => cases compared
    | some actual =>
      by_cases same : actual = layout
      · exact same ▸ physical
      · simp [same, throw] at compared
#print axioms LayoutContentChecked.physical

end StrictBinding
