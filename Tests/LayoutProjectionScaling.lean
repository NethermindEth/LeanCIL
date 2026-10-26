import CIL.Extraction.LayoutProjection

/-! Standalone paired projection validation workloads; not part of the normal library build. -/
namespace Tests.LayoutProjectionScaling
open CIL CIL.Extraction

/-- The former list-based projection conditions, including both layout checks. -/
def baseline (artifact : List RawLayout) (computed : Array ComputedLayout)
    (published : List RawLayout) (publicComputed : Array ComputedLayout)
    (indices : List Nat) : Prop :=
  LayoutsValid artifact computed .scalar ∧ LayoutsValid published publicComputed .scalar ∧
  (artifact.map RawLayout.identity).Nodup ∧ (published.map RawLayout.identity).Nodup ∧
  indices.length = published.length ∧ indices.Nodup ∧
  published.mapM (expandPublicLayout indices) = indices.mapM (fun index => artifact[index]?) ∧
  indices.mapM (fun index => computed[index]?) = some publicComputed.toList

instance (artifact : List RawLayout) (computed : Array ComputedLayout)
    (published : List RawLayout) (publicComputed : Array ComputedLayout) (indices : List Nat) :
    Decidable (baseline artifact computed published publicComputed indices) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Distinct empty layout identities expose catalog costs without large field computations. -/
def catalog (count : Nat) : List RawLayout := (List.range count).map fun index => {
  identity := toString index, explicit := false, packing := 0, declaredSize := 0, fields := [] }

/-- Empty sequential layouts retain their one-byte extent. -/
def computed (count : Nat) : Array ComputedLayout :=
  (List.replicate count ⟨⟨1, []⟩, 1⟩).toArray

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Baseline complete validation for 32 selected layouts. -/
theorem baseline32 : baseline (catalog 32) (computed 32) (catalog 32)
    (computed 32) (List.range 32) := by decide +kernel
#print axioms baseline32

/-- Indexed complete validation for 32 selected layouts. -/
theorem candidate32 : LayoutProjectionValid (catalog 32) (computed 32) (catalog 32)
    (computed 32) (List.range 32) .scalar := by decide +kernel
#print axioms candidate32

/-- Baseline complete validation for 128 selected layouts. -/
theorem baseline128 : baseline (catalog 128) (computed 128) (catalog 128)
    (computed 128) (List.range 128) := by decide +kernel
#print axioms baseline128

/-- Indexed complete validation for 128 selected layouts. -/
theorem candidate128 : LayoutProjectionValid (catalog 128) (computed 128) (catalog 128)
    (computed 128) (List.range 128) .scalar := by decide +kernel
#print axioms candidate128
end Tests.LayoutProjectionScaling

