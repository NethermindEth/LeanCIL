import Tests.Support.EnumIdentity
import CIL.Extraction.Layout
import CIL.Extraction.TypeStorage
import CIL.Extraction.ValueDecoding

/-! Field accumulation preserves declaration order and all metadata rejection boundaries. Named
tables with a wrong offset, size, length, child position or generic owner are rejected by both
`layoutsValidIndexed` and `LayoutsValid`, a class owner included, the owner index finds the first
matching owner, class applications stay classes, and enum arguments require integer atoms. -/
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
    computeLayout noLayouts { mixed with fields := [⟨.vector256 .unsigned64, none⟩] } .scalar =
      none ∧
    computeLayout noLayouts { mixed with fields := [⟨.vector256 .unsigned64, none⟩] } .arm64 =
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

/-- A repeated identity is rejected even when both rows have correct computed layouts. -/
theorem repeatedIdentity :
    ¬ LayoutsValid [leaf, { parent with identity := leaf.identity }]
      #[leafLayout, parentLayout] .scalar := by decide +kernel
#print axioms repeatedIdentity

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
  declaration := (ClassName.ofText s!"Wrap{number}`1").levels,
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

/-- The same closed identity and field layout require the namespace and name of the pinned row. -/
theorem genericOwnerColumns :
    let base := wrap 1 (.parameter 0) 0
    let layout := { base with
      identity := "S::Rows.Wrap1`1<Leaf>"
      declaration := [⟨name!"Rows", name!"Wrap1`1"⟩] }
    let check := fun (name : ClassName) =>
      let raw := { layout with generic := layout.generic.map fun generic =>
        { generic with owner := .constructor "S" name } }
      genericLayoutValid (.ofList [leaf, raw]) raw
    check "Rows.Wrap1`1" = true ∧ check ⟨[⟨name!"", name!"Rows.Wrap1`1"⟩]⟩ = false := by
  decide +kernel
#print axioms genericOwnerColumns

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
/-- `Wrap1<Leaf>` stored with a class as its generic owner; its identity is spelled as the
    struct's is. -/
def classWrap : RawLayout := {
  wrap 1 (.parameter 0) 0 with
  generic := some {
    owner := .objectConstructor "S" "Wrap1`1", arity := 1, arguments := [.aggregate "Leaf" 0],
    fields := [.parameter 0], constraints := [(0, [])] } }

/-- `Wrap1<Leaf>` applied as a class. -/
def classWrapType : TypeExpr := .apply (.objectConstructor "S" "Wrap1`1") (.aggregate "Leaf" 0)

/-- A generic layout whose owner is a class is rejected, while the same layout with a struct
    owner is accepted: a class instance is a reference and never a struct's storage. -/
theorem classOwnerRejected :
    layoutsValidIndexed [leaf, wrap 1 (.parameter 0) 0] (genericLayouts.extract 0 2) .scalar =
      true ∧
    layoutsValidIndexed [leaf, classWrap] (genericLayouts.extract 0 2) .scalar = false ∧
    ¬ LayoutsValid [leaf, classWrap] (genericLayouts.extract 0 2) .scalar := by decide +kernel
#print axioms classOwnerRejected

/-- Closing a class application never looks it up, so it stays a class even against a table
    that claims it; the struct application still closes to its entry. -/
theorem classApplicationStaysClass :
    closeLayoutType [leaf, classWrap] classWrapType = classWrapType ∧
    closeLayoutType [leaf, wrap 1 (.parameter 0) 0] (wrapType 1) =
      .aggregate "S::Wrap1`1<Leaf>" 1 := by decide +kernel
#print axioms classApplicationStaysClass

/-- A generic class field keeps its owner through substitution and refuses struct decoding. -/
theorem classFieldRefusesStructLayout :
    let head := TypeExpr.objectConstructor "S" "Wrap1`1"
    let argument := TypeExpr.aggregate "Leaf" 0
    let source := RawOperand.field (.apply head (.parameter 0)) 0 (.parameter 0) name!"first" false
    let closed := RawOperand.field classWrapType 0 argument name!"first" false
    substituteOperand [argument] [leaf, classWrap] 0 source = some closed ∧
      Instruction.ofRaw? none ⟨0, 123, closed⟩ = none := by decide +kernel
#print axioms classFieldRefusesStructLayout

/-- A class keeps its second argument even when a layout claims that exact closed owner. -/
theorem twoArgumentClassStaysClass :
    let owner := TypeExpr.objectConstructor "S" "C`2"
    let first := TypeExpr.primitive .byte
    let second := TypeExpr.primitive .int32
    let applied := TypeExpr.apply (.apply owner first) second
    let entry := { classWrap with generic := some {
      owner, arity := 2, arguments := [first, second], fields := [], constraints := [] } }
    closeLayoutType [entry] applied = applied := by decide +kernel
#print axioms twoArgumentClassStaysClass

/-- `System.Runtime.Intrinsics.Vector128<ulong>`. -/
def vectorOfWords : TypeExpr :=
  .apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1")
    (.primitive .uint64)

/-- `S::Wrap1<E>` for an enum `E` with `storage`, stored with the one field `kind`. -/
def enumWrap (storage : EnumStorage) (kind : FieldType) : RawLayout := {
  identity := "S::Wrap1`1<Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null::E>", explicit := false, packing := 0, declaredSize := 0,
  declaration := [⟨name!"", name!"Wrap1`1"⟩],
  generic := some {
    owner := .constructor "S" "Wrap1`1", arity := 1, arguments := [.enum (Tests.enumIdentity "E") storage],
    fields := [.parameter 0], constraints := [(0, [])] },
  fields := [⟨kind, none⟩] }

/-- An enum argument's field kind is its storage's. The indexed and propositional checks refuse
    the same claim of another kind. -/
theorem enumArgumentFieldFollowsStorage :
    let integer := enumWrap .signed32 .signed32
    let widened := enumWrap .signed32 .signed64
    let computed : Array ComputedLayout := #[.mk (.mk 4 [.mk 0 4 false]) 4]
    [genericLayoutValid (.ofList [integer]) integer,
      genericLayoutValid (.ofList [widened]) widened,
      layoutsValidIndexed [integer] computed .scalar,
      layoutsValidIndexed [widened] computed .scalar,
      decide (LayoutsValid [widened] computed .scalar)] =
      [true, false, true, false, false] := by decide +kernel
#print axioms enumArgumentFieldFollowsStorage
end Tests.LayoutAccumulation
