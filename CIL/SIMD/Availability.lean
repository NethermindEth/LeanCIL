import CIL.Features
import CIL.SIMD.Intrinsics

namespace CIL

-- Portable Vector128/Vector256 operations have executable software semantics.
-- ISA-specific operations additionally require their runtime-visible capability.
def Intrinsic.available (profile : FeatureProfile) : Intrinsic → Bool
  | .scalar _ => true
  | .vector _ => true
  | .advSimd _ => profile.advSimd
  | .sse .shiftLeftBytes => profile.sse2
  | .sse .alignBytes => profile.ssse3
  | .avx _ => profile.avx
  | .avx2 _ => profile.avx2
  | .avx512 _ => profile.avx512F && profile.avx512FVL
  | .bmi1 _ => profile.bmi1
  | .bmi2 _ => profile.bmi2
  | .armBase64 _ => profile.armBase64
  | .avx512DQ .moveMask64 => profile.avx512DQ
  | .avx512DQ .mul64 => profile.avx512DQ && profile.avx512DQVL && profile.avx512F && profile.avx512FVL

end CIL
