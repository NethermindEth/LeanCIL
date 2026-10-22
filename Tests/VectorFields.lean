import CIL.Safety.InstructionMemory
import CIL.Extraction.LayoutCoverage
import Examples.Support

namespace Tests.VectorFields
open CIL CIL.Safety CIL.Extraction

def cells : List (BitVec 8 × Bool) :=
  (List.range 32).map fun index => (BitVec.ofNat 8 (17 * index + 3), index % 3 != 0)

def memory : CIL.Safety.Memory := {
  Examples.empty with
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨35, 1, []⟩, true, [35]⟩ else none
  nextIdentity := 1
  views := [⟨0, 0, 35, true, true⟩] }

example : (do
    let (stored, _) ← instruction (.setFieldAt 3 32)
      [.scalar (.snapshot .vector256 cells), Examples.reference] memory
    instruction (.fieldAt 3 32) [Examples.reference] stored).map Prod.snd =
    .ok [.scalar (.snapshot .vector256 cells)] := by rfl

example : instruction (.fieldAt 3 32)
    [.scalar (.snapshot (.aggregate 35) ([(0, true), (0, true), (0, true)] ++ cells))] memory =
    .ok (memory, [.scalar (.snapshot .vector256 cells)]) := by rfl

example : instruction (.fieldAt 4 32)
    [.scalar (.aggregate (List.replicate 35 0))] memory = .error .invalidState := by rfl

example : instruction (.setFieldAt 3 32) [.scalar (.v128 0), Examples.reference] memory =
    .error .invalidState := by rfl

example : instruction (.setFieldAt 4 32) [.scalar (.v256 0), Examples.reference] memory =
    .error (.memory .outsideAllocation (.address ⟨0, 4⟩) 32) := by rfl

example : instruction (.setFieldAt 3 32) [.scalar (.v256 0), .reference .null] memory =
    .error (.memory .nullDereference .null 0) := by rfl

example : computeLayouts [{ explicit := true, packing := 1, declaredSize := 35,
    fields := [⟨.vector256, some 3⟩] }] =
    some #[⟨⟨35, [⟨3, 32, false⟩]⟩, 1⟩] := by decide

example : computeLayouts [{ explicit := true, packing := 1, declaredSize := 34,
    fields := [⟨.vector256, some 3⟩] }] = none := by decide

example : computeLayouts [{ explicit := false, auto := true, packing := 0, declaredSize := -1,
    fields := [⟨.vector256, none⟩] }] = none := by decide

example : computeLayouts [{ explicit := false, packing := 32, declaredSize := -1,
    fields := [⟨.vector256, none⟩] }] = none := by decide

def raw : List RawLayout := [{ identity := "VectorHolder", explicit := true, packing := 1,
  declaredSize := 35, fields := [⟨.vector256, some 3⟩] }]

def vector (scope : String) : TypeExpr := .apply
  (.constructor scope "System.Runtime.Intrinsics.Vector256`1")
  (.atom "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" "System.UInt64")

example : instructionLayoutUses raw 0 ⟨0, 0x7b, .field (.aggregate "VectorHolder" 0) 0
    (vector "System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51") false⟩ =
    some [.field 0 0 0 .load] := by decide

example : instructionLayoutUses raw 0 ⟨0, 0x7b, .field (.aggregate "VectorHolder" 0) 0
    (vector "Spoofed.Intrinsics") false⟩ = none := by decide

example : instructionLayoutUses raw 0 ⟨0, 0x7b, .field (.aggregate "VectorHolder" 0) 0
    (.atom "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" "System.UInt64")
    false⟩ = none := by decide

end Tests.VectorFields
