import CIL.Safety.RegionRun

/-!
Kernel-work comparison for sequential region closure. This standalone benchmark retains the
former checker only as a measurement reference; production uses the proved indexed checker.
-/

namespace Tests.RegionScaling
open CIL CIL.Safety
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Reference implementation with repeated instruction and region list scans. -/
def baselineRegionClosedCheck (program : CIL.Program) (starts : List (Nat × Nat)) : Bool :=
  starts.all fun start => match program[start.1]? with
    | none => true
    | some body => (List.range body.code.length).all fun pc =>
      !(start.2 ≤ pc) || match body.code[pc]? with
      | none => true
      | some op => (!op.continues || inStarts starts start.1 (pc + 1)) &&
          op.targets.all (inStarts starts start.1) && op.callees.all (inStarts starts · 0)


/-- A long method with a single full-method region. -/
def program (count : Nat) : CIL.Program :=
  [{ code := List.replicate count .nop ++ [.ret], locals := [], returnsValue := false }]
/-- Reference kernel reduction at 128 instructions plus return. -/
theorem baseline128 : baselineRegionClosedCheck (program 128) [(0, 0)] = true := by decide +kernel
#print axioms baseline128
/-- Indexed kernel reduction at 128 instructions plus return. -/
theorem candidate128 : regionClosedCheck (program 128) [(0, 0)] = true := by decide +kernel
#print axioms candidate128

/-- Reference kernel reduction at 512 instructions plus return. -/
theorem baseline512 : baselineRegionClosedCheck (program 512) [(0, 0)] = true := by decide +kernel
#print axioms baseline512
/-- Indexed kernel reduction at 512 instructions plus return. -/
theorem candidate512 : regionClosedCheck (program 512) [(0, 0)] = true := by decide +kernel
#print axioms candidate512

/-- Reference kernel reduction at 2048 instructions plus return. -/
theorem baseline2048 : baselineRegionClosedCheck (program 2048) [(0, 0)] = true := by decide +kernel
#print axioms baseline2048
/-- Indexed kernel reduction at 2048 instructions plus return. -/
theorem candidate2048 : regionClosedCheck (program 2048) [(0, 0)] = true := by decide +kernel
#print axioms candidate2048

end Tests.RegionScaling
