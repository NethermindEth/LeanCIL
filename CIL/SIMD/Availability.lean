import CIL.Features
import CIL.SIMD.Intrinsics

/-!
# Intrinsic availability

Which intrinsics a feature profile may call. `step` refuses an unavailable intrinsic, so a
proof under a profile covers only the code paths that profile can take.
-/

namespace CIL

/-- The capabilities an intrinsic needs. Portable `Vector128`/`Vector256` operations have
    executable software semantics and need none; ISA-specific operations need their
    runtime-visible capability. -/
def Intrinsic.requiredFeatures : Intrinsic → List Feature
  | .scalar _ => []
  | .vector _ => []
  | .advSimd _ => [.advSimd]
  | .sse .shiftLeftBytes => [.sse2]
  | .sse .alignBytes => [.ssse3]
  | .avx _ => [.avx]
  | .avx2 _ => [.avx2]
  | .avx512 .ltu512 | .avx512 .gtu512 => [.avx512F]
  | .avx512 _ => [.avx512F, .avx512FVL]
  | .bmi1 _ => [.bmi1]
  | .bmi2 _ => [.bmi2]
  | .armBase64 _ => [.armBase64]
  | .x86Base _ => [.x86Base64]
  | .avx512DQ .moveMask64 | .avx512DQ .moveMask512 => [.avx512DQ]
  | .avx512DQ .mul64 => [.avx512DQ, .avx512DQVL, .avx512F, .avx512FVL]

/-- Whether the profile may call an intrinsic: it has every required capability. -/
def Intrinsic.available (profile : FeatureProfile) (operation : Intrinsic) : Bool :=
  operation.requiredFeatures.all profile.evaluate

end CIL
