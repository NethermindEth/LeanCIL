import CIL.Imports

/-!
# Imported layouts

An import slot for a method with a typed signature carries the struct layouts that
signature mentions: as published by the library and as read from the selected
implementation. `ImportedLayoutsValid` requires the two to agree, the layouts to recompute
correctly, and the slot's signature to match its arity and return shape.
-/

namespace CIL.Extraction

/-- One slot's layouts are valid, and either it has no typed signature and no layouts, or
    its supported signature agrees with the slot's arity and return shape. -/
def ImportSlotLayoutsValid (slot : ImportSlot) (architecture : Architecture) : Prop :=
  slot.layouts.Valid architecture ∧
    match slot.signature with
    | none => slot.layouts = {}
    | some signature => signature.supported slot.layouts.actual = true ∧
      signature.parameters.length = slot.parameterCount ∧
      (signature.returnType != .void) = slot.returnsValue

instance (slot : ImportSlot) (architecture : Architecture) :
    Decidable (ImportSlotLayoutsValid slot architecture) := by
  unfold ImportSlotLayoutsValid
  cases slot.signature <;> dsimp <;> infer_instance

/-- Every typed slot carries the selected and published signature-scoped layout values. -/
def ImportedLayoutsValid (imports : List ImportSlot) (architecture : Architecture) : Prop :=
  ∀ slot ∈ imports, ImportSlotLayoutsValid slot architecture

instance (imports : List ImportSlot) (architecture : Architecture) :
    Decidable (ImportedLayoutsValid imports architecture) :=
  inferInstanceAs (Decidable (∀ slot ∈ imports, _))

theorem imported_layouts_checked {imports : List ImportSlot} {architecture : Architecture}
    (valid : ImportedLayoutsValid imports architecture) (slot : ImportSlot)
    (member : slot ∈ imports) :
    slot.layouts.published = slot.layouts.actual ∧
      LayoutsValid slot.layouts.actual slot.layouts.computed architecture :=
  ⟨(valid slot member).1.metadata, (valid slot member).1.layouts⟩

#print axioms imported_layouts_checked

/-- The artifact index of the first layout with `identity`. -/
def artifactLayoutIndex (layouts : List RawLayout) (identity : String) : Option Nat :=
  layouts.findIdx? (·.identity == identity)

/-- A slot layout with each nested-struct index renumbered to the artifact entry of the same
    identity; a nested layout missing from the artifact gives `none`. -/
def rebindImportedLayout (layouts slotLayouts : List RawLayout) (layout : RawLayout) :
    Option RawLayout := do
  let fields ← layout.fields.mapM fun field => match field.type with
    | .aggregate index => do
      let nested ← slotLayouts[index]?
      return { field with type := .aggregate (← artifactLayoutIndex layouts nested.identity) }
    | _ => some field
  return { layout with fields }

/-- An artifact layout repeats, exactly and with nested indices bound by identity, the selected
    layout of every slot that publishes its identity, and has that slot's computed layout. -/
def importedLayoutBound (layouts : List RawLayout) (computed : Array ComputedLayout)
    (slot : ImportSlot) (entry : RawLayout × Nat) : Bool :=
  match slot.layouts.actual.findIdx? (·.identity == entry.1.identity) with
  | none => true
  | some position =>
    (slot.layouts.actual[position]?.bind (rebindImportedLayout layouts slot.layouts.actual)) ==
        some entry.1 &&
      slot.layouts.computed[position]? == computed[entry.2]?

/-- Every artifact layout of another assembly that an import slot publishes, such as the
    storage of an imported aggregate local, is that slot's selected layout. -/
def ImportedLocalLayoutsBound (layouts : List RawLayout) (computed : Array ComputedLayout)
    (imports : List ImportSlot) : Prop :=
  (layouts.zipIdx.all fun entry => imports.all fun slot =>
    importedLayoutBound layouts computed slot entry) = true

instance (layouts : List RawLayout) (computed : Array ComputedLayout) (imports : List ImportSlot) :
    Decidable (ImportedLocalLayoutsBound layouts computed imports) :=
  inferInstanceAs (Decidable (_ = true))

/-- A bound artifact layout has the selected metadata and computed layout of each slot that
    publishes its identity. -/
theorem imported_local_layout_bound {layouts : List RawLayout} {computed : Array ComputedLayout}
    {imports : List ImportSlot} (bound : ImportedLocalLayoutsBound layouts computed imports)
    {index : Nat} {layout : RawLayout} (found : layouts[index]? = some layout)
    {slot : ImportSlot} (member : slot ∈ imports) {position : Nat}
    (published : slot.layouts.actual.findIdx? (·.identity == layout.identity) = some position) :
    (slot.layouts.actual[position]?.bind (rebindImportedLayout layouts slot.layouts.actual)) =
        some layout ∧ slot.layouts.computed[position]? = computed[index]? := by
  have entry : (layout, index) ∈ layouts.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simpa using found
  have checked := List.all_eq_true.mp (List.all_eq_true.mp bound _ entry) slot member
  simp only [importedLayoutBound, published, Bool.and_eq_true, beq_iff_eq] at checked
  exact checked

#print axioms imported_local_layout_bound
end CIL.Extraction
