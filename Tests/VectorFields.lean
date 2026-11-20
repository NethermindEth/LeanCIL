import CIL.Safety.InstructionMemory
import CIL.Extraction.LayoutCoverage
import CIL.Resolution
import Tests.Support

namespace Tests.VectorFields
open CIL CIL.Safety CIL.Extraction

def cells : List (BitVec 8 × Bool) :=
  (List.range 32).map fun index => (BitVec.ofNat 8 (17 * index + 3), index % 3 != 0)

def memory : CIL.Safety.Memory := {
  Memory.empty with
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨35, 1, []⟩, true, [35]⟩ else none
  nextIdentity := 1
  views := [⟨0, 0, 35, true, true⟩] }

example : (do
    let (stored, _) ← instruction (.setFieldAt 3 32)
      [.scalar (.snapshot .vector256 cells), Tests.reference] memory
    instruction (.fieldAt 3 32) [Tests.reference] stored).map Prod.snd =
    .ok [.scalar (.snapshot .vector256 cells)] := by rfl

example : instruction (.fieldAt 3 32)
    [.scalar (.snapshot (.aggregate 35) ([(0, true), (0, true), (0, true)] ++ cells))] memory =
    .ok (memory, [.scalar (.snapshot .vector256 cells)]) := by rfl

example : instruction (.fieldAt 0 32)
    [.scalar (.snapshot (.aggregate 35) cells)] memory = .error .invalidState := by rfl

example : instruction (.fieldAt 4 32)
    [.scalar (.aggregate (List.replicate 35 0))] memory = .error .invalidState := by rfl

example : instruction (.setFieldAt 3 32) [.scalar (.v128 0), Tests.reference] memory =
    .error .invalidState := by rfl

example : instruction (.setFieldAt 4 32) [.scalar (.v256 0), Tests.reference] memory =
    .error (.memory .outsideAllocation (.address ⟨0, 4⟩) 32) := by rfl

example : instruction (.setFieldAt 3 32) [.scalar (.v256 0), .reference .null] memory =
    .error (.memory .nullDereference .null 0) := by rfl

example : computeLayouts [{
    explicit := true, packing := 1, declaredSize := 35,
    fields := [⟨.vector256 .unsigned64, some 3⟩] }] =
    some #[⟨⟨35, [⟨3, 32, false⟩]⟩, 1⟩] := by decide

example : computeLayouts [{
    explicit := true, packing := 1, declaredSize := 34,
    fields := [⟨.vector256 .unsigned64, some 3⟩] }] = none := by decide

example : computeLayouts [{
    explicit := false, auto := true, packing := 0, declaredSize := -1,
    fields := [⟨.vector256 .unsigned64, none⟩] }] = none := by decide

example : computeLayouts [{
    explicit := false, packing := 32, declaredSize := -1,
    fields := [⟨.vector256 .unsigned64, none⟩] }] = none := by decide

example : computeLayouts [{
    explicit := false, packing := 0, declaredSize := -1,
    fields := [⟨.vector256 .unsigned64, none⟩] }] = none := by decide

example : computeLayouts [{
    explicit := false, packing := 0, declaredSize := -1,
    fields := [⟨.unsigned8, none⟩, ⟨.vector128 .unsigned64, none⟩] }] =
    some #[⟨⟨32, [⟨0, 1, false⟩, ⟨16, 16, false⟩]⟩, 16⟩] := by decide

def defaultVector256 : List RawLayout := [{
  identity := "VectorHolder", explicit := false, packing := 0, declaredSize := -1,
  fields := [⟨.unsigned8, none⟩, ⟨.vector256 .unsigned64, none⟩] }]

def x64Layout : Array ComputedLayout := #[⟨⟨64, [⟨0, 1, false⟩, ⟨32, 32, false⟩]⟩, 32⟩]
def arm64Layout : Array ComputedLayout := #[⟨⟨48, [⟨0, 1, false⟩, ⟨16, 32, false⟩]⟩, 16⟩]

example : LayoutsValid defaultVector256 x64Layout .x64 := by decide
example : LayoutsValid defaultVector256 arm64Layout .arm64 := by decide
example : ¬ LayoutsValid defaultVector256 x64Layout .arm64 := by decide
example : ¬ LayoutsValid defaultVector256 arm64Layout .x64 := by decide

/-- A typed vector field has the same instruction operand under both runtime profiles. -/
private def lanes : FieldRef := {
  owner := .aggregate "VectorHolder" 0, index := 1, name := name!"lanes",
  type := .apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector256`1")
    (.atom runtimeScope "System.UInt64") }

private def vectorLoad (architecture : Architecture) (layouts : Array ComputedLayout) : Method :=
  { profile := { architecture }, environment := { rawLayouts := defaultVector256, layouts },
    locals := [], returnsValue := true, code := [.ldfld lanes] }

/-- The same load resolves byte 32 on x64 and byte 16 on ARM64. Swapping the checked table
    invalidates the method layout for each profile. -/
theorem vector_load_profiles :
    let x64 := vectorLoad .x64 x64Layout
    let arm := vectorLoad .arm64 arm64Layout
    MethodLayoutsValid defaultVector256 x64Layout x64 [] ∧
      MethodLayoutsValid defaultVector256 arm64Layout arm [] ∧
      x64.fieldShape lanes = .value 32 32 false ∧ arm.fieldShape lanes = .value 16 32 false ∧
      ¬ MethodLayoutsValid defaultVector256 x64Layout (vectorLoad .arm64 x64Layout) [] ∧
      ¬ MethodLayoutsValid defaultVector256 arm64Layout (vectorLoad .x64 arm64Layout) [] := by
  decide +kernel
#print axioms vector_load_profiles

def nestedVector256 : List RawLayout := defaultVector256 ++
  [{ explicit := false, packing := 0, declaredSize := -1, fields := [⟨.unsigned8, none⟩, ⟨.aggregate 0, none⟩] }]

example : computeLayouts nestedVector256 .x64 =
    some (x64Layout.push ⟨⟨96, [⟨0, 1, false⟩, ⟨32, 64, true⟩]⟩, 32⟩) := by decide

example : computeLayouts nestedVector256 .arm64 =
    some (arm64Layout.push ⟨⟨64, [⟨0, 1, false⟩, ⟨16, 48, true⟩]⟩, 16⟩) := by decide

def raw : List RawLayout := [{
  identity := "VectorHolder", explicit := true, packing := 1,
  declaredSize := 35, fields := [⟨.vector256 .unsigned64, some 3⟩] }]

def vector (scope : String) : TypeExpr := .apply
  (.constructor scope "System.Runtime.Intrinsics.Vector256`1")
  (.atom "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
    "System.UInt64")

example : instructionLayoutUses raw 0 ⟨0, 0x7b, .field (.aggregate "VectorHolder" 0) 0
    (vector "System.Runtime.Intrinsics, Version=11.0.0.0, Culture=neutral, \
      PublicKeyToken=cc7b13ffcd2ddd51")
    name!"value" false⟩ =
    some [] := by decide

example : instructionLayoutUses raw 0 ⟨0, 0x7b, .field (.aggregate "VectorHolder" 0) 0
    (vector "Spoofed.Intrinsics") name!"value" false⟩ = none := by decide

example : instructionLayoutUses raw 0 ⟨0, 0x7b, .field (.aggregate "VectorHolder" 0) 0
    (.atom "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
      "System.UInt64")
    name!"value" false⟩ = none := by decide

end Tests.VectorFields
