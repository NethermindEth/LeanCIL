import CIL.Extraction.Layout

/-! Field accumulation preserves declaration order and all metadata rejection boundaries. Named
tables with a wrong offset, size, length, child position or generic owner are rejected by both
`layoutsValidIndexed` and `LayoutsValid`, and the owner index finds the first matching owner. -/
namespace Tests.LayoutAccumulation
open CIL CIL.Extraction

/-- Mixed widths expose any reversal of declaration order or alignment state. -/
def mixed : RawLayout := {
    explicit := false, packing := 0, declaredSize := 0,
    fields := [⟨.unsigned8, none⟩, ⟨.unsigned64, none⟩, ⟨.unsigned16, none⟩] }

/-- A lookup with no nested layouts. -/
def noLayouts : Nat → Option ComputedLayout := fun _ => none

/-- Field order and padding agree with sequential layout. -/
theorem ordered : computeLayout noLayouts mixed =
    some ⟨⟨24, [⟨0, 1, false⟩, ⟨8, 8, false⟩, ⟨16, 2, false⟩]⟩, 8⟩ := by decide +kernel
#print axioms ordered

/-- Explicit offsets can overlap and need not increase in declaration order. -/
theorem overlapping : computeLayout noLayouts { mixed with
      explicit := true, declaredSize := 16,
      fields := [⟨.unsigned64, some 2⟩, ⟨.unsigned32, some 0⟩] } =
    some ⟨⟨16, [⟨2, 8, false⟩, ⟨0, 4, false⟩]⟩, 8⟩ := by decide +kernel
#print axioms overlapping

/-- Empty layouts retain their one-byte size and missing nested layouts reject. -/
theorem emptyAndMissing :
    computeLayout noLayouts { mixed with fields := [] } = some ⟨⟨1, []⟩, 1⟩ ∧
    computeLayout noLayouts { mixed with fields := [⟨.aggregate 0, none⟩] } = none := by
  decide +kernel
#print axioms emptyAndMissing

/-- Invalid packing, mixed auto layout and absent or overflowing offsets still reject. -/
theorem invalid : computeLayout noLayouts { mixed with packing := 3 } = none ∧
    computeLayout noLayouts { mixed with auto := true } = none ∧
    computeLayout noLayouts { mixed with explicit := true, declaredSize := 32 } = none ∧
    computeLayout noLayouts { mixed with
        explicit := true, declaredSize := 65536,
        fields := [⟨.unsigned32, some 65535⟩] } = none := by decide +kernel
#print axioms invalid

/-- Architecture-dependent vector alignment and the scalar restriction are unchanged. -/
theorem vectorProfiles :
    computeLayout noLayouts { mixed with fields := [⟨.vector256, none⟩] } .scalar = none ∧
    computeLayout noLayouts { mixed with fields := [⟨.vector256, none⟩] } .arm64 =
      some ⟨⟨32, [⟨0, 32, false⟩]⟩, 16⟩ := by decide +kernel
#print axioms vectorProfiles

/-- One `ulong`. -/
def leaf : RawLayout := {
  identity := "Leaf", explicit := false, packing := 0, declaredSize := 0,
  fields := [⟨.unsigned64, none⟩] }

/-- The leaf at position 0 followed by a byte. -/
def parent : RawLayout := {
  identity := "Parent", explicit := false, packing := 0, declaredSize := 0,
  fields := [⟨.aggregate 0, none⟩, ⟨.unsigned8, none⟩] }

/-- The computed layout of `leaf`. -/
def leafLayout : ComputedLayout := ⟨⟨8, [⟨0, 8, false⟩]⟩, 8⟩

/-- The computed layout of `parent`. -/
def parentLayout : ComputedLayout := ⟨⟨16, [⟨0, 8, true⟩, ⟨8, 1, false⟩]⟩, 8⟩

/-- The correct table passes both checks. -/
theorem nestedAccepted : layoutsValidIndexed [leaf, parent] #[leafLayout, parentLayout] .scalar =
    true ∧ LayoutsValid [leaf, parent] #[leafLayout, parentLayout] .scalar := by decide +kernel
#print axioms nestedAccepted

/-- The proof form of the extraction header: the kernel runs the `Decidable` instance, which
    decides the indexed check. -/
theorem headerForm : LayoutsValid [leaf, parent] #[leafLayout, parentLayout] .scalar := by
  decide +kernel

/-- info: 'Tests.LayoutAccumulation.headerForm' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms headerForm

/-- `parent` with its byte one past where sequential layout places it. -/
def offByOne : ComputedLayout := ⟨⟨16, [⟨0, 8, true⟩, ⟨9, 1, false⟩]⟩, 8⟩

/-- `parent` with a size that still contains every field. -/
def oversized : ComputedLayout := ⟨⟨24, [⟨0, 8, true⟩, ⟨8, 1, false⟩]⟩, 8⟩

/-- A claimed offset one byte off is rejected. -/
theorem wrongOffset :
    layoutsValidIndexed [leaf, parent] #[leafLayout, offByOne] .scalar = false ∧
    ¬ LayoutsValid [leaf, parent] #[leafLayout, offByOne] .scalar := by decide +kernel
#print axioms wrongOffset

/-- A claimed size that still contains every field is rejected. -/
theorem wrongSize :
    layoutsValidIndexed [leaf, parent] #[leafLayout, oversized] .scalar = false ∧
    ¬ LayoutsValid [leaf, parent] #[leafLayout, oversized] .scalar := by decide +kernel
#print axioms wrongSize

/-- A struct cannot contain itself, even when the claimed table is self-consistent. -/
theorem childAtParent :
    layoutsValidIndexed [{ parent with fields := [⟨.aggregate 0, none⟩] }]
      #[⟨⟨8, [⟨0, 8, true⟩]⟩, 8⟩] .scalar = false ∧
    ¬ LayoutsValid [{ parent with fields := [⟨.aggregate 0, none⟩] }]
      #[⟨⟨8, [⟨0, 8, true⟩]⟩, 8⟩] .scalar := by decide +kernel
#print axioms childAtParent

/-- `parent` holding the layout at `child` and then a byte. -/
def parentOf (child : Nat) : RawLayout :=
  { parent with fields := [⟨.aggregate child, none⟩, ⟨.unsigned8, none⟩] }

/-- A child listed after its parent is rejected, even when the claimed table agrees with it. -/
theorem childAfterParent :
    layoutsValidIndexed [parentOf 1, leaf] #[parentLayout, leafLayout] .scalar = false ∧
    ¬ LayoutsValid [parentOf 1, leaf] #[parentLayout, leafLayout] .scalar := by decide +kernel
#print axioms childAfterParent

/-- A child index past the end of the table is rejected. -/
theorem childPastEnd :
    layoutsValidIndexed [leaf, parentOf 5] #[leafLayout, parentLayout] .scalar = false ∧
    ¬ LayoutsValid [leaf, parentOf 5] #[leafLayout, parentLayout] .scalar := by decide +kernel
#print axioms childPastEnd

/-- A claimed table longer or shorter than the raw table is rejected. -/
theorem wrongLength :
    layoutsValidIndexed [leaf, parent] #[leafLayout] .scalar = false ∧
    ¬ LayoutsValid [leaf, parent] #[leafLayout] .scalar ∧
    layoutsValidIndexed [leaf] #[leafLayout, leafLayout] .scalar = false ∧
    ¬ LayoutsValid [leaf] #[leafLayout, leafLayout] .scalar := by decide +kernel
#print axioms wrongLength

/-- The closed generic owner `S::Wrap{number}`1` applied to `Leaf`. -/
def wrapType (number : Nat) : TypeExpr :=
  .apply (.constructor "S" s!"Wrap{number}`1") (.aggregate "Leaf" 0)

/-- `Wrap{number}<Leaf>` with the given original field type, stored as the layout at `child`. -/
def wrap (number : Nat) (field : TypeExpr) (child : Nat) : RawLayout := {
  identity := s!"S::Wrap{number}`1<Leaf>", explicit := false, packing := 0, declaredSize := 0,
  generic := some {
    owner := .constructor "S" s!"Wrap{number}`1", arity := 1, arguments := [.aggregate "Leaf" 0],
    fields := [field], constraints := [(0, [])] },
  fields := [⟨.aggregate child, none⟩] }

/-- The original field type of `Wrap2`: `Wrap1` applied to the type parameter. -/
def wrapsFirst : TypeExpr := .apply (.constructor "S" "Wrap1`1") (.parameter 0)

/-- `Wrap2<Leaf>` holds `Wrap1<Leaf>`, found through its closed generic owner. -/
def genericTable : List RawLayout := [leaf, wrap 1 (.parameter 0) 0, wrap 2 wrapsFirst 1]

/-- The computed layouts of `genericTable`. -/
def genericLayouts : Array ComputedLayout :=
  #[leafLayout, ⟨⟨8, [⟨0, 8, true⟩]⟩, 8⟩, ⟨⟨8, [⟨0, 8, true⟩]⟩, 8⟩]

/-- The generic table passes both checks. -/
theorem genericAccepted : layoutsValidIndexed genericTable genericLayouts .scalar = true ∧
    LayoutsValid genericTable genericLayouts .scalar := by decide +kernel
#print axioms genericAccepted

/-- A generic layout whose owner differs from the one its identity spells is rejected by the
    identity check, before any owner lookup. -/
theorem wrongOwner :
    layoutsValidIndexed (genericTable.set 2
      { wrap 2 wrapsFirst 1 with generic := (wrap 3 wrapsFirst 1).generic })
      genericLayouts .scalar = false ∧
    ¬ LayoutsValid (genericTable.set 2
      { wrap 2 wrapsFirst 1 with generic := (wrap 3 wrapsFirst 1).generic })
      genericLayouts .scalar := by decide +kernel
#print axioms wrongOwner

/-- A field naming a generic owner that no layout has is rejected: the owner lookup finds
    nothing. -/
theorem missingOwner :
    layoutsValidIndexed (genericTable.set 2
      (wrap 2 (.apply (.constructor "S" "Missing`1") (.parameter 0)) 1))
      genericLayouts .scalar = false ∧
    ¬ LayoutsValid (genericTable.set 2
      (wrap 2 (.apply (.constructor "S" "Missing`1") (.parameter 0)) 1))
      genericLayouts .scalar := by decide +kernel
#print axioms missingOwner

/-- A field whose owner lookup finds position 1 while the stored field names position 0 is
    rejected. -/
theorem otherOwner :
    layoutsValidIndexed (genericTable.set 2 (wrap 2 wrapsFirst 0)) genericLayouts .scalar =
      false ∧
    ¬ LayoutsValid (genericTable.set 2 (wrap 2 wrapsFirst 0)) genericLayouts .scalar := by
  decide +kernel
#print axioms otherOwner

/-- `Wrap1` and `Wrap2` have the same layout, and `Wrap3` holds `Wrap2`, stored at `child`. -/
def sameShapes (child : Nat) : List RawLayout :=
  [leaf, wrap 1 (.parameter 0) 0, wrap 2 (.parameter 0) 0,
    wrap 3 (.apply (.constructor "S" "Wrap2`1") (.parameter 0)) child]

/-- The computed layouts of `sameShapes`, the same for every `child` of equal shape. -/
def sameShapeLayouts : Array ComputedLayout :=
  #[leafLayout, ⟨⟨8, [⟨0, 8, true⟩]⟩, 8⟩, ⟨⟨8, [⟨0, 8, true⟩]⟩, 8⟩, ⟨⟨8, [⟨0, 8, true⟩]⟩, 8⟩]

/-- Only the owner lookup tells `Wrap1` from `Wrap2`: storing the other owner of the same shape
    is rejected while the claimed table stays the same. -/
theorem swappedOwner :
    layoutsValidIndexed (sameShapes 2) sameShapeLayouts .scalar = true ∧
    layoutsValidIndexed (sameShapes 1) sameShapeLayouts .scalar = false ∧
    ¬ LayoutsValid (sameShapes 1) sameShapeLayouts .scalar := by decide +kernel
#print axioms swappedOwner

/-- Of two layouts with one closed type, the owner index finds the first, as the list scan does. -/
theorem firstOwner :
    (GenericOwnerIndex.ofList [leaf, wrap 1 (.parameter 0) 0, wrap 1 (.parameter 0) 0]).find
      (wrapType 1) = some 1 ∧
    genericLayoutIndex [leaf, wrap 1 (.parameter 0) 0, wrap 1 (.parameter 0) 0] (wrapType 1) =
      some 1 := by decide +kernel
#print axioms firstOwner
end Tests.LayoutAccumulation
