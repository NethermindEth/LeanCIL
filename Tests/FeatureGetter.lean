import Tests.Support.EnumIdentity
import CIL.Extraction.Features
import Tests.Support.ModelOperands

/-!
# Exact feature getter identities

The model operand binds assembly, namespace, class and member identity,
including malformed signatures which share the admitted prefix.
-/

namespace Tests.FeatureGetter

open CIL CIL.Extraction

/-- A static feature getter with independently constructed raw metadata. -/
def getter (owner member : String) : CallSite := {
  declared := { convention := 0, returnType := .primitive .boolean },
  method := {
    owner := .atom intrinsicsScope ("System.Runtime.Intrinsics." ++ owner) .classType,
    name := (MetadataName.ofBytes? (member.toUTF8.toList.map UInt8.toNat)).getD ⟨0⟩,
    hasThis := false, genericArity := 0,
    returnType := .primitive .boolean, parameters := [] }
  name := member
  target := .external (intrinsicsScope ++ "::System.Boolean System.Runtime.Intrinsics." ++
    owner ++ "::" ++ member ++ "()")
  parameterCount := 0, returnsValue := true, typeArguments := [] }

/-- The external identity must name the selected owner even for two admitted getters. -/
theorem targetOwner :
    let site := getter "X86.Avx2" "get_IsSupported"
    platformGetterModel site = some (.feature .avx2) ∧
      platformGetterModel { site with target := (getter "X86.Aes" "get_IsSupported").target } =
        none := by decide +kernel

#print axioms targetOwner

/-- Hardware acceleration, nested class and ordinary supported getters retain their flags. -/
theorem supported :
    platformGetterModel (getter "Vector256" "get_IsHardwareAccelerated") =
      some (.feature .vector256Accelerated) ∧
    platformGetterModel (getter "X86.Sse41" "get_IsSupported") = some (.feature .sse41) ∧
    platformGetterModel (getter "Arm.ArmBase/Arm64" "get_IsSupported") =
      some (.feature .armBase64) ∧
    platformGetterModel (getter "Arm.AdvSimd/Arm64" "get_IsSupported") = some (.feature .advSimd) ∧
    platformGetterModel (getter "X86.Avx512Vbmi" "get_IsSupported") = some (.feature .avx512Vbmi) ∧
    platformGetterModel (getter "X86.Avx512Vbmi/VL" "get_IsSupported") =
      some (.feature .avx512Vbmi) ∧
    platformGetterModel (getter "X86.Aes" "get_IsSupported") = some (.feature .aes) ∧
    platformGetterModel (getter "X86.Aes/X64" "get_IsSupported") = some (.feature .aes) ∧
    platformGetterModel (getter "Arm.Aes" "get_IsSupported") = some (.feature .armAes) ∧
    platformGetterModel (getter "Arm.Aes/Arm64" "get_IsSupported") = some (.feature .armAes) := by
  decide +kernel
#print axioms supported

/-- A syntactically similar identity cannot change the exact admitted feature class or member. -/
theorem wrong_names :
    platformGetterModel (getter "Vector256" "get_IsSupported") = none ∧
    platformGetterModel (getter "X86.Sse41X" "get_IsSupported") = none ∧
    platformGetterModel (getter "X86.Sse41" "get_IsSupportedX") = none ∧
    platformGetterModel (getter "X86.Ssé41" "get_IsSupported") = none := by decide +kernel
#print axioms wrong_names

/-- Nested 64-bit classes outside the measured runtime groups remain unclassified. -/
theorem unclassified_nested :
    platformGetterModel (getter "Arm.Crc32/Arm64" "get_IsSupported") = none ∧
    platformGetterModel (getter "Arm.Rdm/Arm64" "get_IsSupported") = none ∧
    platformGetterModel (getter "Arm.AdvSimd/Arm64" "get_IsHardwareAccelerated") = none ∧
    platformGetterModel (getter "X86.Avx512Vbmi2/VL" "get_IsSupported") = none ∧
    platformGetterModel (getter "X86.Avx512Vbmi/VL" "get_IsHardwareAccelerated") = none ∧
    platformGetterModel (getter "X86.Pclmulqdq" "get_IsSupported") = none ∧
    platformGetterModel (getter "X86.Aes/X86" "get_IsSupported") = none := by
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

/-- The `arm64-advsimd` capabilities, with AES left to each case. -/
def armProfile : FeatureProfile := {
  architecture := .arm64, armBase64 := true, advSimd := true, vector128Accelerated := true }

/-- AES needs only its architecture's base: any x64 or ARM64 profile may declare its own AES,
    but not the other architecture's, and a scalar profile declares neither. -/
theorem aes_profiles :
    { v3Profile with aes := true }.Valid ∧ { armProfile with armAes := true }.Valid ∧
    ¬ { v3Profile with armAes := true }.Valid ∧ ¬ { armProfile with aes := true }.Valid ∧
    ¬ { FeatureProfile.scalar with aes := true }.Valid ∧
    ¬ { FeatureProfile.scalar with armAes := true }.Valid := by
  decide +kernel
#print axioms aes_profiles

/-- Truncation, an incorrect assembly and trailing signature bytes all fail exact matching. -/
theorem wrong_prefix_or_tail :
    (List.all ["", intrinsicsScope, intrinsicsScope ++ "::System.Boolean System.Runtime.Intrinsics.",
      "Other::System.Boolean System.Runtime.Intrinsics.X86.Sse41::get_IsSupported()",
      intrinsicsScope ++ "::System.Boolean System.Runtime.Intrinsics.X86.Sse41::get_IsSupported()X"]
      (fun identity =>
        (platformGetterModel { getter "X86.Sse41" "get_IsSupported" with
          target := .external identity }).isNone)) = true := by decide +kernel
#print axioms wrong_prefix_or_tail

/-- Signature acceleration leaves the existing call-shape checks intact. -/
theorem wrong_call_shape :
    platformGetterModel { getter "X86.Sse41" "get_IsSupported" with parameterCount := 1 } = none ∧
    platformGetterModel { getter "X86.Sse41" "get_IsSupported" with method.hasThis := true } =
      none ∧
    platformGetterModel { getter "X86.Sse41" "get_IsSupported" with returnsValue := false } = none ∧
    platformGetterModel { getter "X86.Sse41" "get_IsSupported" with
      typeArguments := [.primitive .int32] } = none := by decide +kernel
#print axioms wrong_call_shape

/-- Raw process-width calls retain their exact owner, result and external identity. -/
def platform (owner : TypeExpr) (ownerName member : String) (result : PrimitiveType) :
    CallSite := {
  declared := { convention := 0, returnType := .primitive result },
  method := {
    owner,
    name := (MetadataName.ofBytes? (member.toUTF8.toList.map UInt8.toNat)).getD ⟨0⟩,
    hasThis := false, genericArity := 0, returnType := .primitive result,
    parameters := [] }
  name := member
  target := .external
    (runtimeScope ++ "::" ++ result.display ++ " " ++ ownerName ++ "::" ++ member ++ "()")
  parameterCount := 0, returnsValue := true, typeArguments := [] }

/-- The `get_Size` getter of the native integer `owner`. -/
def sizeGetter (owner : PrimitiveType) : CallSite :=
  platform (.primitive owner) owner.display "get_Size" .int32

/-- `Environment.get_Is64BitProcess`. -/
def processWidth : CallSite :=
  platform (.atom runtimeScope "System.Environment"
      .classType) "System.Environment" "get_Is64BitProcess"
    .boolean

/-- Each supported hardware owner and each process getter keeps its call only at its exact row. -/
theorem getter_decoding :
    (["Arm.AdvSimd", "Arm.AdvSimd/Arm64", "Arm.ArmBase/Arm64", "X86.Sse2", "X86.Ssse3",
      "X86.Sse41", "X86.Sse42", "X86.Avx", "X86.Avx2", "X86.Avx512F", "X86.Avx512F/VL",
      "X86.Avx512DQ", "X86.Avx512DQ/VL", "X86.Avx512Vbmi", "X86.Avx512Vbmi/VL", "X86.Aes",
      "X86.Aes/X64", "Arm.Aes", "Arm.Aes/Arm64", "X86.Bmi1", "X86.Bmi2/X64", "X86.X86Base/X64"].all
      (fun owner => Tests.ModelOperands.checks (getter owner "get_IsSupported"))) = true ∧
    (["Vector128", "Vector256"].all (fun owner =>
      Tests.ModelOperands.checks (getter owner "get_IsHardwareAccelerated"))) = true ∧
    ([sizeGetter .intPtr, sizeGetter .uintPtr, processWidth].all
        Tests.ModelOperands.checks) = true := by
  decide +kernel

#print axioms getter_decoding

/-- Both native-size getters and the process query use the admitted 64-bit platform. -/
theorem platform_values :
    platformGetterModel (sizeGetter .intPtr) = some (.constant 8) ∧
    platformGetterModel (sizeGetter .uintPtr) = some (.constant 8) ∧
    platformGetterModel processWidth = some (.constant 1) := by decide +kernel
#print axioms platform_values

/-- A platform constant is checked even when its forged instruction has the same stack effect. -/
theorem platform_encoding (raw : RawMethod) :
    let site := sizeGetter .intPtr
    featureOpMatches #[] raw ⟨0, 40, .call site⟩ (.call site.method {}) = true ∧
    featureOpMatches #[] raw ⟨0, 40, .call site⟩ (.ldc_i4 4) = false ∧
    featureOpMatches #[] raw ⟨0, 40, .call { site with
      method.owner := .atom "forged" "System.IntPtr" .valueType }⟩ (.ldc_i4 8) = false ∧
    featureOpMatches #[] raw ⟨0, 40, .call { site with
      method.owner := .atom runtimeScope "System.IntPtr" .valueType }⟩ (.ldc_i4 8) = false ∧
    featureOpMatches #[] raw ⟨0, 40, .call { site with
      target := .external "forged" }⟩ (.ldc_i4 8) = false ∧
    featureOpMatches #[] raw ⟨0, 40, .call { site with
      method.returnType := .primitive .uint32 }⟩ (.ldc_i4 8) = false ∧
    featureOpMatches #[] raw ⟨0, 111, .call site⟩ (.ldc_i4 8) = false ∧
    featureOpMatches #[] raw ⟨0, 40, .call { site with method.hasThis := true }⟩ (.ldc_i4 8) =
      false ∧
    featureOpMatches #[] raw ⟨0, 40, .call { site with parameterCount := 1 }⟩ (.ldc_i4 8) = false ∧
    featureOpMatches #[] raw ⟨0, 40, .call { site with
      typeArguments := [.primitive .int32] }⟩ (.ldc_i4 8) = false := by
  unfold featureOpMatches
  decide +kernel
#print axioms platform_encoding

/-- A raw static Boolean load from `owner` in `scope`. -/
def staticBoolean (scope owner : String) : RawInstruction :=
  ⟨0, 126, .field (.atom scope owner .classType) 0 (.primitive .boolean)
    name!"IsLittleEndian" true⟩

/-- A static `BitConverter` field of another type, which is not the endianness constant. -/
def integerField : RawOperand :=
  .field (.atom runtimeScope "System.BitConverter" .classType) 0 (.primitive .int32)
    name!"IsLittleEndian" true

/-- A static `BitConverter` Boolean with another name, which is not the endianness constant. -/
def otherBoolean : RawOperand :=
  .field (.atom runtimeScope "System.BitConverter" .classType) 0 (.primitive .boolean)
    name!"IsBigEndian" true

/-- Only the runtime's `BitConverter` Boolean is the little-endian constant, bound exactly. -/
theorem platform_field (raw : RawMethod) :
    let endian := staticBoolean runtimeScope "System.BitConverter"
    platformField endian = some 1 ∧
    platformField (staticBoolean "forged" "System.BitConverter") = none ∧
    platformField (staticBoolean runtimeScope "System.BitConverterX") = none ∧
    platformField { endian with opcode := 127 } = none ∧
    platformField { endian with operand := integerField } = none ∧
    platformField { endian with operand := otherBoolean } = none ∧
    featureOpMatches #[] raw endian (.ldc_i4 1) = true ∧
    featureOpMatches #[] raw endian (.ldc_i4 0) = false ∧
    featureOpMatches #[] raw (staticBoolean "forged" "System.BitConverter") (.ldc_i4 1) =
      false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms platform_field

/-- A reference-content query retains its independently serialized generic argument. -/
def referenceQuery (type : TypeExpr) : CallSite := {
  declared := { convention := 0x10, returnType := .primitive .boolean },
  method := {
    owner := .atom runtimeScope "System.Runtime.CompilerServices.RuntimeHelpers" .classType,
    name := name!"IsReferenceOrContainsReferences", hasThis := false, genericArity := 1,
    returnType := .primitive .boolean, parameters := [],
    methodArguments := [type] },
  name := "IsReferenceOrContainsReferences",
  target := .external (runtimeScope ++
    "::System.Boolean System.Runtime.CompilerServices.RuntimeHelpers::" ++
    "IsReferenceOrContainsReferences()"), parameterCount := 0, returnsValue := true,
  typeArguments := [type] }

/-- Representable references and views are not reference-free generic value storage. -/
theorem reference_content_boundary :
    let integer := TypeExpr.primitive .int32
    let query := fun type => referenceContentFact #[] (referenceQuery type)
    query integer = some 0 ∧
    query (.primitive .boolean) = some 0 ∧
    query (.primitive .char) = some 0 ∧
    query (.primitive .uintPtr) = some 0 ∧
    query (.enum (Tests.enumIdentity "enum") .signed32) = some 0 ∧
    query (.apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector256`1")
      integer) = some 0 ∧
    query (.apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector512`1")
      integer) = some 0 ∧
    query (.byref integer) = none ∧ query (.pointer integer) = none ∧
    query (.array integer) = none ∧ query (.parameter 0) = none ∧
    query (.atom runtimeScope "System.Object" .classType) = none ∧
    query (.primitive .single) = none ∧
    query (.apply (.constructor runtimeScope "System.Span`1") integer) = none ∧
    query (.apply (.constructor runtimeScope "System.ReadOnlySpan`1") integer) = none ∧
    query (.aggregate "missing" 0) = none := by decide +kernel
#print axioms reference_content_boundary

/-- A malformed query or an argument with managed references cannot acquire a model. -/
theorem reference_decoding :
    let query := referenceQuery (.primitive .int32)
    Tests.ModelOperands.checks query = true ∧
      Tests.ModelOperands.decoded (referenceQuery (.array (.primitive .int32))) =
        liveHoleAt 0 40 := by decide +kernel

#print axioms reference_decoding

end Tests.FeatureGetter
