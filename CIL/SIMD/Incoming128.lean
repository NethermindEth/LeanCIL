import CIL.SIMD.EvaluationLemmas

/-!
# Carrying a 64-bit lane between 128-bit halves

Shifting a 256-bit value held as two 128-bit vectors up by one 64-bit lane: each half takes
its new low lane from the lane below it. The theorems show that ARM `EXT` and the SSE byte
shift and align intrinsics all compute this, so one proof covers either ISA.
-/

namespace CIL.Vector

/-- The low half after the shift: zero below `low`'s lane 0. -/
def incoming128Low (low : BitVec 128) : BitVec 128 :=
  CIL.Vector.pack128 0 (CIL.Vector.lane64 low 0)

/-- The high half after the shift: `low`'s lane 1 below `high`'s lane 0. -/
def incoming128High (low high : BitVec 128) : BitVec 128 :=
  CIL.Vector.pack128 (CIL.Vector.lane64 low 1) (CIL.Vector.lane64 high 0)

theorem incoming128_arm_low (low : BitVec 128) :
    CIL.Vector.advExtract64 (BitVec.ofNat 128 0) low 1 = incoming128Low low := by
  simpa only [CIL.Vector.pack128_lanes, incoming128Low] using
    CIL.Vector.adv_incoming_zero (CIL.Vector.lane64 low 0) (CIL.Vector.lane64 low 1)

theorem incoming128_arm_high (low high : BitVec 128) :
    CIL.Vector.advExtract64 low high 1 = incoming128High low high := by
  simpa only [CIL.Vector.pack128_lanes, incoming128High] using CIL.Vector.adv_incoming
    (CIL.Vector.lane64 low 0) (CIL.Vector.lane64 low 1)
    (CIL.Vector.lane64 high 0) (CIL.Vector.lane64 high 1)

theorem incoming128_sse_low (low : BitVec 128) :
    CIL.Vector.sseShiftLeftBytes low 8 = incoming128Low low := by
  simpa only [CIL.Vector.pack128_lanes, incoming128Low] using
    CIL.Vector.sse_incoming_low (CIL.Vector.lane64 low 0) (CIL.Vector.lane64 low 1)

theorem incoming128_sse_high (low high : BitVec 128) :
    CIL.Vector.ssseAlignBytes high low 8 = incoming128High low high := by
  change CIL.Vector.advExtract64 low high 1 = _
  exact incoming128_arm_high low high

end CIL.Vector
