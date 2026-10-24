import Std

/-!
# Feature profiles

The hardware capabilities a method can observe through `IsSupported` and
`IsHardwareAccelerated`. A `FeatureProfile` fixes them for a whole execution; `step` reads
it for feature tests and intrinsic availability.

Supported deployment policy: .NET 10 CoreCLR on 64-bit little-endian hosts.
IsSupported includes OS support and runtime disabling, not just CPU capability.
The runtime enables SSE4.2, AVX2/BMI and AVX-512 capabilities in whole groups;
ARM64 enables ArmBase and AdvSimd together. Vector128 acceleration follows the
baseline SIMD group; Vector256 acceleration requires AVX2 but may be disabled
independently by the preferred vector width.
Pinned runtime sources, measured x64/ARM64 versions, and migration guidance:
docs/RUNTIME-PROFILES.md
https://github.com/dotnet/runtime/blob/v10.0.13/src/coreclr/vm/codeman.cpp
https://github.com/dotnet/runtime/blob/v10.0.13/src/coreclr/tools/Common/JitInterface/ThunkGenerator/InstructionSetDesc.txt
`FeatureProfile.valid_iff_prerequisites` spells out every operation prerequisite `Valid` implies.
-/

namespace CIL

/-- A capability flag a method can test; each names one `FeatureProfile` field. -/
inductive Feature where
  | advSimd | sse2 | ssse3 | sse42 | avx | avx2 | avx512F | avx512FVL | bmi1
  | sse41 | avx512DQ | avx512DQVL | bmi2 | armBase64 | vector256Accelerated
  | x86Base64 | vector128Accelerated
  deriving DecidableEq, Repr

/-- The target instruction set; `scalar` is a profile with no ISA-specific capability. -/
inductive Architecture where
  | scalar | arm64 | x64
  deriving DecidableEq, Repr

/-- Runtime-visible flags are fixed throughout an execution. `Valid` constrains
runtime disabling to the supported .NET 10 CoreCLR capability groups. -/
structure FeatureProfile where
  architecture : Architecture := .scalar
  nativeWidth : Nat := 64
  littleEndian : Bool := true
  advSimd : Bool := false
  sse2 : Bool := false
  ssse3 : Bool := false
  sse42 : Bool := false
  avx : Bool := false
  avx2 : Bool := false
  avx512F : Bool := false
  avx512FVL : Bool := false
  bmi1 : Bool := false
  sse41 : Bool := false
  avx512DQ : Bool := false
  avx512DQVL : Bool := false
  bmi2 : Bool := false
  armBase64 : Bool := false
  vector256Accelerated : Bool := false
  x86Base64 : Bool := false
  vector128Accelerated : Bool := false
  deriving DecidableEq, Repr

/-- The profile with every capability off, so only portable code paths run. -/
def FeatureProfile.scalar : FeatureProfile := {}

/-- The result of testing a feature under this profile. -/
def FeatureProfile.evaluate (p : FeatureProfile) : Feature → Bool
  | .advSimd => p.advSimd
  | .sse2 => p.sse2
  | .ssse3 => p.ssse3
  | .sse42 => p.sse42
  | .avx => p.avx
  | .avx2 => p.avx2
  | .avx512F => p.avx512F
  | .avx512FVL => p.avx512FVL
  | .bmi1 => p.bmi1
  | .sse41 => p.sse41
  | .avx512DQ => p.avx512DQ
  | .avx512DQVL => p.avx512DQVL
  | .bmi2 => p.bmi2
  | .armBase64 => p.armBase64
  | .vector256Accelerated => p.vector256Accelerated
  | .x86Base64 => p.x86Base64
  | .vector128Accelerated => p.vector128Accelerated

/-- Declared capability domain: 64-bit little-endian execution, architecture
separation, and prerequisites used by the reachable SSE/AVX operations. This is
an explicit domain, rather than a claim to enumerate every possible CLR host.
`valid_iff_prerequisites` restates it with every prerequisite it implies spelled out. -/
def FeatureProfile.Valid (p : FeatureProfile) : Prop :=
  p.nativeWidth = 64 ∧ p.littleEndian = true ∧
  (p.x86Base64 = true → p.architecture = .x64) ∧
  (p.armBase64 = true → p.architecture = .arm64) ∧
  -- The x86 prerequisite chain; each runtime group below inherits it.
  (p.avx512F = true → p.avx2 = true) ∧ (p.avx2 = true → p.avx = true) ∧
  (p.avx = true → p.sse42 = true) ∧ (p.sse42 = true → p.sse2 = true) ∧
  -- .NET 10 CoreCLR runtime groups; see docs/RUNTIME-PROFILES.md.
  p.sse2 = p.x86Base64 ∧ p.ssse3 = p.sse41 ∧ p.sse41 = p.sse42 ∧
  p.avx2 = p.bmi1 ∧ p.avx2 = p.bmi2 ∧
  p.avx512F = p.avx512FVL ∧ p.avx512F = p.avx512DQ ∧ p.avx512F = p.avx512DQVL ∧
  p.advSimd = p.armBase64 ∧ p.vector128Accelerated = (p.sse2 || p.advSimd) ∧
  (p.vector256Accelerated = true → p.avx2 = true)

instance (p : FeatureProfile) : Decidable p.Valid := inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem FeatureProfile.scalar_evaluate (f : Feature) : scalar.evaluate f = false := by
  cases f <;> rfl

theorem FeatureProfile.scalar_valid : scalar.Valid := by decide

/-- `Valid` is equivalent to its expanded form, which also lists every prerequisite that the
    runtime groups and the x86 chain already imply; dropping those weakened nothing. -/
theorem FeatureProfile.valid_iff_prerequisites (p : FeatureProfile) : p.Valid ↔
    p.nativeWidth = 64 ∧ p.littleEndian = true ∧
    (p.advSimd = true → p.architecture = .arm64) ∧
    ((p.sse2 || p.ssse3 || p.sse42 || p.avx || p.avx2 || p.avx512F || p.avx512FVL || p.bmi1 ||
        p.sse41 || p.avx512DQ || p.avx512DQVL || p.bmi2) = true →
      p.x86Base64 = true) ∧
    (p.x86Base64 = true → p.architecture = .x64) ∧
    (p.ssse3 = true → p.sse2 = true) ∧
    (p.sse42 = true → p.sse2 = true ∧ p.ssse3 = true) ∧
    (p.avx2 = true → p.avx = true) ∧
    (p.avx512FVL = true → p.avx512F = true) ∧
    (p.avx = true → p.sse42 = true) ∧
    (p.avx512F = true → p.avx2 = true) ∧
    (p.sse41 = true → p.ssse3 = true) ∧
    (p.sse42 = true → p.sse41 = true) ∧
    (p.avx512DQ = true → p.avx512F = true) ∧
    (p.avx512DQVL = true → p.avx512DQ = true ∧ p.avx512FVL = true) ∧
    (p.armBase64 = true → p.architecture = .arm64) ∧
    (p.advSimd = true → p.armBase64 = true) ∧
    -- .NET 10 CoreCLR runtime groups; see docs/RUNTIME-PROFILES.md.
    p.sse2 = p.x86Base64 ∧ p.ssse3 = p.sse41 ∧ p.sse41 = p.sse42 ∧
    p.avx2 = p.bmi1 ∧ p.avx2 = p.bmi2 ∧
    p.avx512F = p.avx512FVL ∧ p.avx512F = p.avx512DQ ∧ p.avx512F = p.avx512DQVL ∧
    p.advSimd = p.armBase64 ∧ p.vector128Accelerated = (p.sse2 || p.advSimd) ∧
    (p.vector256Accelerated = true → p.avx2 = true) := by
  unfold FeatureProfile.Valid
  cases p
  simp only
  constructor <;> intro h <;> grind

#print axioms FeatureProfile.valid_iff_prerequisites

end CIL
