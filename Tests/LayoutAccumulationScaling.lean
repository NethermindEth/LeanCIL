import CIL.Extraction.Layout

/-! Standalone before/after kernel workload for layout field accumulation. -/
namespace Tests.LayoutAccumulationScaling
open CIL CIL.Extraction
/-- Width, natural alignment and whether the field is a nested struct. A nested struct
    must already be in `previous`, which rules out forward references. -/
private def fieldStorage (previous : Array ComputedLayout) (architecture : Architecture) :
    FieldType → Option (Nat × Nat × Bool)
  | .signed8 | .unsigned8 | .boolean => some (1, 1, false)
  | .signed16 | .unsigned16 | .character => some (2, 2, false)
  | .signed32 | .unsigned32 => some (4, 4, false)
  | .signed64 | .unsigned64 | .nativeInt | .nativeUInt => some (8, 8, false)
  | .vector128 => some (16, 16, false)
  | .vector256 => some (32, if architecture == .arm64 then 16 else 32, false)
  | .aggregate index => do
    let child ← previous[index]?
    return (child.layout.size, child.alignment, true)

/-- The least multiple of `alignment` that is at least `size`. -/
private def alignUp (size alignment : Nat) : Nat :=
  (size + alignment - 1) / alignment * alignment

/-- Auto layout is admitted only where it coincides with sequential placement. -/
private def autoSequential (previous : Array ComputedLayout) (raw : RawLayout) : Bool :=
  !raw.explicit && raw.packing ≤ 0 && raw.declaredSize ≤ 0 &&
  match raw.fields.mapM (fun field => do
      if field.offset.isSome || field.type == FieldType.vector128 ||
          field.type == FieldType.vector256 then none else
        let (width, _, aggregate) ← fieldStorage previous .scalar field.type
        if aggregate then none else some width) with
  | some (width :: widths) => widths.all (· == width)
  | _ => false

/-- Recompute CoreCLR reference-free 64-bit layout from ordered metadata fields. -/
def baselineLayout (previous : Array ComputedLayout) (raw : RawLayout)
    (architecture : Architecture := .scalar) : Option ComputedLayout := do
  if raw.packing ∉ [-1, 0, 1, 2, 4, 8, 16, 32, 64, 128] then none
  else if raw.declaredSize < -1 || raw.declaredSize > 65536 then none
  else if raw.explicit && raw.declaredSize ≤ 0 then none
  else if raw.auto && !autoSequential previous raw then none
  else
    let pack := if raw.packing ≤ 0 then 64 else raw.packing.toNat
    let (size, alignment, fields) ← raw.fields.foldlM (init := (0, 1, ([] : List FieldLayout)))
        fun (size, alignment, fields) field => do
      if field.type == .vector256 && pack > 16 && architecture == .scalar then none else do
        let (width, natural, aggregate) ← fieldStorage previous architecture field.type
        let aligned := min pack natural
        if aligned = 0 then none else do
          let offset ← if raw.explicit then field.offset else
            if field.offset.isSome then none else some (alignUp size aligned)
          if offset + width > 65536 ||
              (raw.explicit && offset + width > raw.declaredSize.toNat) then none else
            return (max size (offset + width), max alignment aligned,
              fields ++ [⟨offset, width, aggregate⟩])
    let finalSize := max 1
      (if raw.declaredSize > 0 then max size raw.declaredSize.toNat else alignUp size alignment)
    if finalSize > 65536 then none else
      return ⟨⟨finalSize, fields⟩, alignment⟩


set_option maxRecDepth 65536
set_option maxHeartbeats 0
/-- A homogeneous layout with one byte per field. -/
def raw (count : Nat) : RawLayout := {
    explicit := false, packing := 0, declaredSize := 0,
    fields := List.replicate count ⟨.unsigned8, none⟩ }
/-- The expected ordered offsets expose a reversed accumulator. -/
def expected (count : Nat) : ComputedLayout :=
  ⟨⟨count, (List.range count).map fun index => ⟨index, 1, false⟩⟩, 1⟩
/-- Original append-based kernel workload at 128 fields. -/
theorem baseline128 : baselineLayout #[] (raw 128) = some (expected 128) := by decide +kernel
#print axioms baseline128
/-- Linear kernel workload at 128 fields. -/
theorem candidate128 : computeLayout #[] (raw 128) = some (expected 128) := by decide +kernel
#print axioms candidate128

/-- Original append-based kernel workload at 512 fields. -/
theorem baseline512 : baselineLayout #[] (raw 512) = some (expected 512) := by decide +kernel
#print axioms baseline512
/-- Linear kernel workload at 512 fields. -/
theorem candidate512 : computeLayout #[] (raw 512) = some (expected 512) := by decide +kernel
#print axioms candidate512

end Tests.LayoutAccumulationScaling



