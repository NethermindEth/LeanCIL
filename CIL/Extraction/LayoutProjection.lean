import CIL.Extraction.Layout

namespace CIL.Extraction

private def expandPublicField (indices : List Nat) (field : RawField) : Option RawField := do
  match field.type with
  | .aggregate index => return { field with type := .aggregate (← indices[index]?) }
  | _ => return field

def expandPublicLayout (indices : List Nat) (layout : RawLayout) : Option RawLayout := do
  return { layout with fields := ← layout.fields.mapM (expandPublicField indices) }

/-- A public signature closure can reorder and omit private layouts, but cannot change
    metadata, nested identity bindings or the selected artifact's computed layouts. -/
def LayoutProjectionValid (artifact : List RawLayout) (computed : Array ComputedLayout)
    (published : List RawLayout) (publicComputed : Array ComputedLayout)
    (indices : List Nat) (architecture : Architecture) : Prop :=
  LayoutsValid artifact computed architecture ∧ LayoutsValid published publicComputed architecture ∧
  (artifact.map RawLayout.identity).Nodup ∧ (published.map RawLayout.identity).Nodup ∧
  indices.length = published.length ∧ indices.Nodup ∧
  published.mapM (expandPublicLayout indices) = indices.mapM (fun index => artifact[index]?) ∧
  indices.mapM (fun index => computed[index]?) = some publicComputed.toList

instance (artifact : List RawLayout) (computed : Array ComputedLayout)
    (published : List RawLayout) (publicComputed : Array ComputedLayout)
    (indices : List Nat) (architecture : Architecture) :
    Decidable (LayoutProjectionValid artifact computed published publicComputed indices architecture) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem projected_layouts_checked {artifact : List RawLayout} {computed : Array ComputedLayout}
    {published : List RawLayout} {publicComputed : Array ComputedLayout}
    {indices : List Nat} {architecture : Architecture}
    (valid : LayoutProjectionValid artifact computed published publicComputed indices architecture) :
    LayoutsValid published publicComputed architecture := valid.2.1

#print axioms projected_layouts_checked
end CIL.Extraction
