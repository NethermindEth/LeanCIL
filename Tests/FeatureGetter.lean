import CIL.Extraction.Features

/-!
# Exact feature getter identities

The byte-table lookup must retain assembly, namespace, class and member identity,
including malformed signatures which share the admitted prefix.
-/

namespace Tests.FeatureGetter

open CIL CIL.Extraction

/-- A static feature getter with independently constructed raw metadata. -/
def getter (owner member : String) : CallSite := {
  declaringType := .atom intrinsicsScope ("System.Runtime.Intrinsics." ++ owner)
  name := member
  target := .external (intrinsicsScope ++ "::System.Boolean System.Runtime.Intrinsics." ++
    owner ++ "::" ++ member ++ "()")
  parameterCount := 0, hasThis := false, returnsValue := true, typeArguments := []
  returnType := .atom runtimeScope "System.Boolean", parameterTypes := [] }

/-- Hardware acceleration, nested class and ordinary supported getters retain their flags. -/
theorem supported :
    featureGetter (getter "Vector256" "get_IsHardwareAccelerated") = some .vector256Accelerated ∧
    featureGetter (getter "X86.Sse41" "get_IsSupported") = some .sse41 ∧
    featureGetter (getter "Arm.ArmBase/Arm64" "get_IsSupported") = some .armBase64 ∧
    featureGetter (getter "Arm.AdvSimd/Arm64" "get_IsSupported") = some .advSimd ∧
    featureGetter (getter "X86.Avx512Vbmi" "get_IsSupported") = some .avx512Vbmi ∧
    featureGetter (getter "X86.Avx512Vbmi/VL" "get_IsSupported") = some .avx512Vbmi := by
  decide +kernel
#print axioms supported

/-- A syntactically similar identity cannot change the exact admitted feature class or member. -/
theorem wrong_names :
    featureGetter (getter "Vector256" "get_IsSupported") = none ∧
    featureGetter (getter "X86.Sse41X" "get_IsSupported") = none ∧
    featureGetter (getter "X86.Sse41" "get_IsSupportedX") = none ∧
    featureGetter (getter "X86.Ssé41" "get_IsSupported") = none := by decide +kernel
#print axioms wrong_names

/-- Nested 64-bit classes outside the measured runtime groups remain unclassified. -/
theorem unclassified_nested :
    featureGetter (getter "Arm.Crc32/Arm64" "get_IsSupported") = none ∧
    featureGetter (getter "Arm.Rdm/Arm64" "get_IsSupported") = none ∧
    featureGetter (getter "Arm.AdvSimd/Arm64" "get_IsHardwareAccelerated") = none ∧
    featureGetter (getter "X86.Avx512Vbmi2/VL" "get_IsSupported") = none ∧
    featureGetter (getter "X86.Avx512Vbmi/VL" "get_IsHardwareAccelerated") = none := by
  decide +kernel
#print axioms unclassified_nested

/-- The x86-64-v3 capabilities, with AVX-512 and VBMI left to each case. -/
def v3Profile : FeatureProfile := {
  architecture := .x64, x86Base64 := true, sse2 := true, ssse3 := true, sse41 := true,
  sse42 := true, avx := true, avx2 := true, bmi1 := true, bmi2 := true,
  vector128Accelerated := true, vector256Accelerated := true }

/-- `x64-v4` with VBMI declared is valid; VBMI without AVX-512 is not. -/
theorem vbmi_profiles :
    { v3Profile with
      avx512F := true, avx512FVL := true, avx512DQ := true, avx512DQVL := true
      avx512Vbmi := true }.Valid ∧
    ¬ { v3Profile with avx512Vbmi := true }.Valid := by
  decide +kernel
#print axioms vbmi_profiles

/-- Truncation, an incorrect assembly and trailing signature bytes all fail exact matching. -/
theorem wrong_prefix_or_tail :
    (List.all ["", intrinsicsScope, intrinsicsScope ++ "::System.Boolean System.Runtime.Intrinsics.",
      "Other::System.Boolean System.Runtime.Intrinsics.X86.Sse41::get_IsSupported()",
      intrinsicsScope ++ "::System.Boolean System.Runtime.Intrinsics.X86.Sse41::get_IsSupported()X"]
      (fun identity =>
        (featureGetter { getter "X86.Sse41" "get_IsSupported" with
          target := .external identity }).isNone)) = true := by decide +kernel
#print axioms wrong_prefix_or_tail

/-- Signature acceleration leaves the existing call-shape checks intact. -/
theorem wrong_call_shape :
    featureGetter { getter "X86.Sse41" "get_IsSupported" with parameterCount := 1 } = none ∧
    featureGetter { getter "X86.Sse41" "get_IsSupported" with hasThis := true } = none ∧
    featureGetter { getter "X86.Sse41" "get_IsSupported" with returnsValue := false } = none ∧
    featureGetter { getter "X86.Sse41" "get_IsSupported" with
      typeArguments := [.atom runtimeScope "System.Int32"] } = none := by decide +kernel
#print axioms wrong_call_shape

/-- Raw process-width calls retain their exact owner, result and external identity. -/
def platform (owner member result : String) : CallSite := {
  declaringType := .atom runtimeScope owner, name := member
  target := .external (runtimeScope ++ "::" ++ result ++ " " ++ owner ++ "::" ++ member ++ "()")
  parameterCount := 0, hasThis := false, returnsValue := true, typeArguments := []
  returnType := .atom runtimeScope result, parameterTypes := [] }

/-- Both native-size getters and the process query use the admitted 64-bit platform. -/
theorem platform_values :
    platformConstant (platform "System.IntPtr" "get_Size" "System.Int32") = some 8 ∧
    platformConstant (platform "System.UIntPtr" "get_Size" "System.Int32") = some 8 ∧
    platformConstant (platform "System.Environment" "get_Is64BitProcess" "System.Boolean") =
      some 1 := by decide +kernel
#print axioms platform_values

/-- A platform constant is checked even when its forged instruction has the same stack effect. -/
theorem platform_encoding (raw : RawMethod) :
    let site := platform "System.IntPtr" "get_Size" "System.Int32"
    featureOpMatches #[] raw ⟨0, 40, .call site⟩ (.const32 8) = true ∧
    featureOpMatches #[] raw ⟨0, 40, .call site⟩ (.const32 4) = false ∧
    featureOpMatches #[] raw ⟨0, 40, .call { site with
      declaringType := .atom "forged" "System.IntPtr" }⟩ (.const32 8) = false ∧
    featureOpMatches #[] raw ⟨0, 40, .call { site with
      target := .external "forged" }⟩ (.const32 8) = false ∧
    featureOpMatches #[] raw ⟨0, 40, .call { site with
      returnType := .atom runtimeScope "System.UInt32" }⟩ (.const32 8) = false ∧
    featureOpMatches #[] raw ⟨0, 111, .call site⟩ (.const32 8) = false ∧
    featureOpMatches #[] raw ⟨0, 40, .call { site with hasThis := true }⟩ (.const32 8) = false ∧
    featureOpMatches #[] raw ⟨0, 40, .call { site with parameterCount := 1 }⟩ (.const32 8) = false ∧
    featureOpMatches #[] raw ⟨0, 40, .call { site with
      typeArguments := [.atom runtimeScope "System.Int32"] }⟩ (.const32 8) = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms platform_encoding

/-- A raw static Boolean load from `owner` in `scope`. -/
def staticBoolean (scope owner : String) : RawInstruction :=
  ⟨0, 126, .field (.atom scope owner) 0 (.atom runtimeScope "System.Boolean") true⟩

/-- A static `BitConverter` field of another type, which is not the endianness constant. -/
def integerField : RawOperand :=
  .field (.atom runtimeScope "System.BitConverter") 0 (.atom runtimeScope "System.Int32") true

/-- Only the runtime's `BitConverter` Boolean is the little-endian constant, bound exactly. -/
theorem platform_field (raw : RawMethod) :
    let endian := staticBoolean runtimeScope "System.BitConverter"
    platformField endian = some 1 ∧
    platformField (staticBoolean "forged" "System.BitConverter") = none ∧
    platformField (staticBoolean runtimeScope "System.BitConverterX") = none ∧
    platformField { endian with opcode := 127 } = none ∧
    platformField { endian with operand := integerField } = none ∧
    featureOpMatches #[] raw endian (.const32 1) = true ∧
    featureOpMatches #[] raw endian (.const32 0) = false ∧
    featureOpMatches #[] raw (staticBoolean "forged" "System.BitConverter") (.const32 1) =
      false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms platform_field

/-- A reference-content query retains its independently serialized generic argument. -/
def referenceQuery (type : TypeExpr) : CallSite := {
  declaringType := .atom runtimeScope "System.Runtime.CompilerServices.RuntimeHelpers"
  name := "IsReferenceOrContainsReferences"
  target := .external (runtimeScope ++
    "::System.Boolean System.Runtime.CompilerServices.RuntimeHelpers::" ++
    "IsReferenceOrContainsReferences()")
  parameterCount := 0, hasThis := false, returnsValue := true, typeArguments := [type]
  returnType := .atom runtimeScope "System.Boolean", parameterTypes := [] }

/-- Representable references and views are not reference-free generic value storage. -/
theorem reference_content_boundary :
    let integer := TypeExpr.atom runtimeScope "System.Int32"
    let query := fun type => referenceContentConstant #[] (referenceQuery type)
    query integer = some 0 ∧
    query (.atom runtimeScope "System.Boolean") = some 0 ∧
    query (.atom runtimeScope "System.Char") = some 0 ∧
    query (.atom runtimeScope "System.UIntPtr") = some 0 ∧
    query (.enum "enum" integer) = some 0 ∧
    query (.apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector256`1")
      integer) = some 0 ∧
    query (.apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector512`1")
      integer) = some 0 ∧
    query (.byref integer) = none ∧ query (.pointer integer) = none ∧
    query (.array integer) = none ∧ query (.parameter 0) = none ∧
    query (.atom runtimeScope "System.Object") = none ∧
    query (.atom runtimeScope "System.Single") = none ∧
    query (.apply (.constructor runtimeScope "System.Span`1") integer) = none ∧
    query (.apply (.constructor runtimeScope "System.ReadOnlySpan`1") integer) = none ∧
    query (.aggregate "missing" 0) = none := by decide +kernel
#print axioms reference_content_boundary

end Tests.FeatureGetter
