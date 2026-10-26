import CIL.Extraction.Layout
import CIL.Extraction.FlowIndex
import Std.Data.TreeSet.Lemmas

/-!
# Public layout projection

A library's published contract interface carries only the struct layouts its public
signatures need, renumbered. `LayoutProjectionValid` checks that this public catalog is a
faithful projection of the artifact layouts. Balanced indexes avoid repeatedly traversing
metadata lists, and ordered sets check identity and index uniqueness.
-/

namespace CIL.Extraction

/-- Reject repeated values and values already in the ordered set. -/
private def distinctFrom [Ord α] : Std.TreeSet α → List α → Bool
  | _, [] => true
  | seen, value :: rest => !seen.contains value && distinctFrom (seen.insert value) rest

/-- Ordered membership preserves the exact list uniqueness condition. -/
private theorem distinctFrom_correct [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    (seen : Std.TreeSet α) (values : List α) :
    distinctFrom seen values = true ↔ values.Nodup ∧ ∀ value ∈ values, value ∉ seen := by
  induction values generalizing seen with
  | nil => simp [distinctFrom]
  | cons value rest ih =>
    simp only [distinctFrom, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
      ih, List.nodup_cons, List.forall_mem_cons,
      Std.TreeSet.mem_insert, Std.compare_eq_iff_eq, not_or]
    constructor
    · rintro ⟨fresh, distinct, remaining⟩
      refine ⟨⟨?_, distinct⟩, fresh, ?_⟩
      · intro member
        exact (remaining value member).1 rfl
      · intro other member
        exact (remaining other member).2
    · rintro ⟨⟨fresh, distinct⟩, unseen, remaining⟩
      refine ⟨unseen, distinct, ?_⟩
      intro other member
      exact ⟨fun same => fresh (same ▸ member), remaining other member⟩

#print axioms distinctFrom_correct

/-- Check uniqueness using logarithmic ordered membership instead of repeated list scans. -/
def projectionDistinct [Ord α] (values : List α) : Bool := distinctFrom ∅ values

/-- The ordered uniqueness check accepts exactly the duplicate-free lists. -/
theorem projectionDistinct_iff [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    (values : List α) : projectionDistinct values = true ↔ values.Nodup := by
  simp [projectionDistinct, distinctFrom_correct]

#print axioms projectionDistinct_iff

/-- Maps a nested-struct field's public index to its artifact index. -/
private def expandPublicField (lookup : Nat → Option Nat) (field : RawField) :
    Option RawField := do
  match field.type with
  | .aggregate index => return { field with type := .aggregate (← lookup index) }
  | _ => return field

/-- A published layout with every nested-struct index mapped to its artifact index. -/
def expandPublicLayout (indices : List Nat) (layout : RawLayout) : Option RawLayout := do
  return { layout with fields := ← layout.fields.mapM (expandPublicField (indices[·]?)) }

/-- Match published metadata against its selected artifact entries with shared indexes. -/
def projectionMetadataMatches (artifact published : List RawLayout) (indices : List Nat) :
    Prop :=
  let publicIndex := FlowIndex.ofList indices
  let artifactIndex := FlowIndex.ofList artifact
  published.mapM (fun layout => do
    return { layout with fields := ← layout.fields.mapM (expandPublicField publicIndex.get?) }) =
      indices.mapM artifactIndex.get?

instance (artifact published : List RawLayout) (indices : List Nat) :
    Decidable (projectionMetadataMatches artifact published indices) :=
  inferInstanceAs (Decidable (_ = _))

/-- Indexed metadata matching preserves missing indices and nested field expansion exactly. -/
theorem projectionMetadataMatches_iff (artifact published : List RawLayout)
    (indices : List Nat) :
    projectionMetadataMatches artifact published indices ↔
      published.mapM (expandPublicLayout indices) =
        indices.mapM (fun index => artifact[index]?) := by
  have lookup {α : Type} (values : List α) : (FlowIndex.ofList values).get? = (values[·]?) := by
    funext index
    exact FlowIndex.get?_ofList values index
  simp only [projectionMetadataMatches, lookup]
  rfl

#print axioms projectionMetadataMatches_iff

/-- A public signature closure can reorder and omit private layouts, but cannot change
    metadata, nested identity bindings or the selected artifact's computed layouts. -/
def LayoutProjectionValid (artifact : List RawLayout) (computed : Array ComputedLayout)
    (published : List RawLayout) (publicComputed : Array ComputedLayout)
    (indices : List Nat) (architecture : Architecture) : Prop :=
  LayoutsValid artifact computed architecture ∧
    LayoutsValid published publicComputed architecture ∧
  projectionDistinct (artifact.map RawLayout.identity) = true ∧
  projectionDistinct (published.map RawLayout.identity) = true ∧
  indices.length = published.length ∧ projectionDistinct indices = true ∧
  projectionMetadataMatches artifact published indices ∧
  indices.mapM (fun index => computed[index]?) = some publicComputed.toList

instance (artifact : List RawLayout) (computed : Array ComputedLayout)
    (published : List RawLayout) (publicComputed : Array ComputedLayout)
    (indices : List Nat) (architecture : Architecture) :
    Decidable
      (LayoutProjectionValid artifact computed published publicComputed indices architecture) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The indexed validator accepts exactly the original list-based projection conditions. -/
theorem LayoutProjectionValid_iff_list (artifact : List RawLayout)
    (computed : Array ComputedLayout) (published : List RawLayout)
    (publicComputed : Array ComputedLayout) (indices : List Nat) (architecture : Architecture) :
    LayoutProjectionValid artifact computed published publicComputed indices architecture ↔
      LayoutsValid artifact computed architecture ∧
        LayoutsValid published publicComputed architecture ∧
      (artifact.map RawLayout.identity).Nodup ∧ (published.map RawLayout.identity).Nodup ∧
      indices.length = published.length ∧ indices.Nodup ∧
      published.mapM (expandPublicLayout indices) =
        indices.mapM (fun index => artifact[index]?) ∧
      indices.mapM (fun index => computed[index]?) = some publicComputed.toList := by
  simp only [LayoutProjectionValid, projectionDistinct_iff, projectionMetadataMatches_iff]

#print axioms LayoutProjectionValid_iff_list

/-- A valid projection retains the independent layout check of the published catalog. -/
theorem projected_layouts_checked {artifact : List RawLayout} {computed : Array ComputedLayout}
    {published : List RawLayout} {publicComputed : Array ComputedLayout}
    {indices : List Nat} {architecture : Architecture}
    (valid :
      LayoutProjectionValid artifact computed published publicComputed indices architecture) :
    LayoutsValid published publicComputed architecture := valid.2.1

#print axioms projected_layouts_checked
end CIL.Extraction
