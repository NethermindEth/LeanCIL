import CIL.Extraction.DecodedDefinition
import CIL.Extraction.DecodedMethod

/-! Decoder refusal tests for incomplete method-token operands. -/

namespace Tests.LoweredCallRefusal
open CIL CIL.Extraction

/-- A call without a supported overload, embedded in an otherwise empty static method. -/
private def body (opcode : Nat) (owner : TypeExpr) (member : MetadataName) (name : String) :
    RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false, callingConvention := 0,
  attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
  initLocals := false, maxStack := 0, genericParameters := [],
  code := [⟨0, opcode, .call {
    method := {
      owner, name := member, hasThis := false, genericArity := 0,
      returnType := .void, parameters := [] },
    declared := { convention := 0 }, name, target := .external "Fixture", typeArguments := [],
    parameterCount := 0, returnsValue := false }⟩] }

/-- Check who owns the raw site and decode its instruction at pc zero. -/
private def decoded (claim : SiteClaim LoweredFamily) (opcode : Nat) (owner : TypeExpr)
    (member : MetadataName) (name : String) : Option Instruction := do
  let source := body opcode owner member name
  let raw ← source.code.head?
  _root_.guard (siteClaim loweredCallFamily {} none raw == claim)
  (← Method.ofRaw? .scalar {} [] source []).code.head?

/-- An incomplete Missing operand produces an opcode 40 hole. -/
theorem unclaimed :
    decoded .refused 40
      (.atom "Fixture" "Fixture")
      name!"Missing" "Missing" = some (.unadmitted 40) := by rfl
#print axioms unclaimed

/-- An incomplete Missing operand produces an opcode 111 hole. -/
theorem virtualCall :
    decoded .refused 111
      (.atom "Fixture" "Fixture")
      name!"Missing" "Missing" = some (.unadmitted 111) := by rfl
#print axioms virtualCall

/-- An incomplete Missing operand produces an opcode 115 hole. -/
theorem construction :
    decoded .refused 115
      (.atom "Fixture" "Fixture")
      name!"Missing" "Missing" = some (.unadmitted 115) := by rfl
#print axioms construction

/-- An incomplete SkipInit operand produces an opcode 40 hole. -/
theorem skipInitialization :
    decoded (.lowered (.unsafeHelper .skipInit)) 40
      (.atom runtimeScope "System.Runtime.CompilerServices.Unsafe")
      name!"SkipInit" "SkipInit" = some (.unadmitted 40) := by rfl
#print axioms skipInitialization

/-- An incomplete NullRef operand produces an opcode 40 hole. -/
theorem nullReference :
    decoded (.lowered (.unsafeHelper .nullRef)) 40
      (.atom runtimeScope "System.Runtime.CompilerServices.Unsafe")
      name!"NullRef" "NullRef" = some (.unadmitted 40) := by rfl
#print axioms nullReference

/-- An incomplete IsNullRef operand produces an opcode 40 hole. -/
theorem isNullReference :
    decoded (.lowered (.unsafeHelper .isNullRef)) 40
      (.atom runtimeScope "System.Runtime.CompilerServices.Unsafe")
      name!"IsNullRef" "IsNullRef" = some (.unadmitted 40) := by rfl
#print axioms isNullReference

/-- An incomplete Read operand produces an opcode 40 hole. -/
theorem unsafeTransfer :
    decoded (.lowered .unsafeTransfer) 40
      (.atom runtimeScope "System.Runtime.CompilerServices.Unsafe")
      name!"Read" "Read" = some (.unadmitted 40) := by rfl
#print axioms unsafeTransfer

/-- An incomplete Add operand produces an opcode 40 hole. -/
theorem unsafeOffset :
    decoded (.lowered .unsafeOffset) 40
      (.atom runtimeScope "System.Runtime.CompilerServices.Unsafe")
      name!"Add" "Add" = some (.unadmitted 40) := by rfl
#print axioms unsafeOffset

/-- An incomplete As operand produces an opcode 40 hole. -/
theorem unsafeReference :
    decoded (.lowered .unsafeReference) 40
      (.atom runtimeScope "System.Runtime.CompilerServices.Unsafe")
      name!"As" "As" = some (.unadmitted 40) := by rfl
#print axioms unsafeReference

/-- An incomplete CopyBlock operand produces an opcode 40 hole. -/
theorem unsafeBlock :
    decoded (.lowered .unsafeBlock) 40
      (.atom runtimeScope "System.Runtime.CompilerServices.Unsafe")
      name!"CopyBlock" "CopyBlock" = some (.unadmitted 40) := by rfl
#print axioms unsafeBlock

/-- An incomplete BitCast operand produces an opcode 40 hole. -/
theorem bitCast :
    decoded (.lowered .bitCast) 40
      (.atom runtimeScope "System.Runtime.CompilerServices.Unsafe")
      name!"BitCast" "BitCast" = some (.unadmitted 40) := by rfl
#print axioms bitCast

/-- An incomplete SizeOf operand produces an opcode 40 hole. -/
theorem sizeOf :
    decoded (.lowered .sizeOf) 40
      (.atom runtimeScope "System.Runtime.CompilerServices.Unsafe")
      name!"SizeOf" "SizeOf" = some (.unadmitted 40) := by rfl
#print axioms sizeOf

/-- An incomplete ReadInt32BigEndian operand produces an opcode 40 hole. -/
theorem binaryTransfer :
    decoded (.lowered .binary) 40
      (.atom spanMemoryScope "System.Buffers.Binary.BinaryPrimitives")
      name!"ReadInt32BigEndian" "ReadInt32BigEndian" = some (.unadmitted 40) := by decide +kernel
#print axioms binaryTransfer

/-- An incomplete ThrowIfNull operand produces an opcode 40 hole. -/
theorem argumentGuard :
    decoded (.lowered .guard) 40
      (.atom runtimeScope "System.ArgumentNullException")
      name!"ThrowIfNull" "ThrowIfNull" = some (.unadmitted 40) := by rfl
#print axioms argumentGuard

/-- An incomplete Read operand produces an opcode 40 hole. -/
theorem marshalTransfer :
    decoded (.lowered .marshal) 40
      (.atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal")
      name!"Read" "Read" = some (.unadmitted 40) := by rfl
#print axioms marshalTransfer

/-- An incomplete GetArrayDataReference operand produces an opcode 40 hole. -/
theorem view :
    decoded (.lowered .view) 40
      (.atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal")
      name!"GetArrayDataReference" "GetArrayDataReference" = some (.unadmitted 40) := by rfl
#print axioms view

/-- An incomplete CreateReadOnlySpan operand produces an opcode 40 hole. -/
theorem span :
    decoded (.lowered .span) 40
      (.atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal")
      name!"CreateReadOnlySpan" "CreateReadOnlySpan" = some (.unadmitted 40) := by rfl
#print axioms span

/-- An incomplete GetReference operand produces an opcode 40 hole. -/
theorem spanReference :
    decoded (.lowered .spanReference) 40
      (.atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal")
      name!"GetReference" "GetReference" = some (.unadmitted 40) := by rfl
#print axioms spanReference

/-- An incomplete CreateSpan operand produces an opcode 40 hole. -/
theorem staticSpan :
    decoded (.lowered .staticSpan) 40
      (.atom runtimeScope "System.Runtime.CompilerServices.RuntimeHelpers")
      name!"CreateSpan" "CreateSpan" = some (.unadmitted 40) := by rfl
#print axioms staticSpan

/-- An incomplete DivRem operand produces an opcode 40 hole. -/
theorem integerMath :
    decoded (.lowered .integerMath) 40
      (.atom runtimeScope "System.Math")
      name!"DivRem" "DivRem" = some (.unadmitted 40) := by rfl
#print axioms integerMath

/-- An incomplete And operand produces an opcode 40 hole. -/
theorem hardware :
    decoded (.lowered .hardware) 40
      (.atom intrinsicsScope "System.Runtime.Intrinsics.X86.Avx2")
      name!"And" "And" = some (.unadmitted 40) := by rfl
#print axioms hardware

/-- An incomplete Create operand produces an opcode 40 hole. -/
theorem vectorCreate :
    decoded (.lowered .vectorCreate) 40
      (.atom intrinsicsScope "System.Runtime.Intrinsics.Vector128")
      name!"Create" "Create" = some (.unadmitted 40) := by rfl
#print axioms vectorCreate

/-- An incomplete LoadUnsafe operand produces an opcode 40 hole. -/
theorem vectorTransfer :
    decoded (.lowered .vectorTransfer) 40
      (.atom intrinsicsScope "System.Runtime.Intrinsics.Vector128")
      name!"LoadUnsafe" "LoadUnsafe" = some (.unadmitted 40) := by rfl
#print axioms vectorTransfer

/-- An incomplete get_IsSupported operand produces an opcode 40 hole. -/
theorem feature :
    decoded (.lowered .feature) 40
      (.atom intrinsicsScope "System.Runtime.Intrinsics.X86.Avx")
      name!"get_IsSupported" "get_IsSupported" = some (.unadmitted 40) := by rfl
#print axioms feature

/-- An incomplete op_Equality operand produces an opcode 40 hole. -/
theorem typeTest :
    decoded (.lowered .typeTest) 40
      (.atom runtimeScope "System.Type")
      name!"op_Equality" "op_Equality" = some (.unadmitted 40) := by rfl
#print axioms typeTest

/-- An incomplete ctor operand produces an opcode 115 hole. -/
theorem throwConstructor :
    decoded (.lowered .throwConstructor) 115
      (.atom runtimeScope "System.Exception")
      name!".ctor" ".ctor" = some (.unadmitted 115) := by rfl
#print axioms throwConstructor

/-- An incomplete get_Size operand produces an opcode 40 hole. -/
theorem platform :
    decoded (.lowered .platform) 40
      (.atom runtimeScope "System.IntPtr")
      name!"get_Size" "get_Size" = some (.unadmitted 40) := by rfl
#print axioms platform

/-- An incomplete IsReferenceOrContainsReferences operand produces an opcode 40 hole. -/
theorem referenceContent :
    decoded (.lowered .referenceContent) 40
      (.atom runtimeScope "System.Runtime.CompilerServices.RuntimeHelpers")
      name!"IsReferenceOrContainsReferences" "IsReferenceOrContainsReferences" =
        some (.unadmitted 40) := by rfl
#print axioms referenceContent

/-- An incomplete ctor operand produces an opcode 40 hole. -/
theorem objectModel :
    decoded .refused 40
      (.atom runtimeScope "System.Object")
      name!".ctor" ".ctor" = some (.unadmitted 40) := by rfl
#print axioms objectModel

/-- An incomplete PopCount operand produces an opcode 40 hole. -/
theorem bitModel :
    decoded .refused 40
      (.atom runtimeScope "System.Numerics.BitOperations")
      name!"PopCount" "PopCount" = some (.unadmitted 40) := by rfl
#print axioms bitModel

/-- An incomplete ReverseEndianness operand produces an opcode 40 hole. -/
theorem byteOrderModel :
    decoded .refused 40
      (.atom spanMemoryScope "System.Buffers.Binary.BinaryPrimitives")
      name!"ReverseEndianness" "ReverseEndianness" = some (.unadmitted 40) := by decide +kernel
#print axioms byteOrderModel

/-- An incomplete GetElement operand produces an opcode 40 hole. -/
theorem vectorModel :
    decoded .refused 40
      (.atom intrinsicsScope "System.Runtime.Intrinsics.Vector128")
      name!"GetElement" "GetElement" = some (.unadmitted 40) := by rfl
#print axioms vectorModel

/-- An incomplete Max operand produces an opcode 40 hole. -/
theorem mathModel :
    decoded .refused 40
      (.atom runtimeScope "System.Math")
      name!"Max" "Max" = some (.unadmitted 40) := by rfl
#print axioms mathModel

/-- The empty layout environment of the method with an unknown call. -/
private def emptyEnvironment : LayoutEnvironment := {}

cil_decoded_method unknownMethod := Method.ofRaw? .scalar emptyEnvironment []
  (body 40 (.atom "Fixture" "Fixture") name!"Missing" "Missing") []

/-- The generated code contains exactly the hole for the unresolved member. -/
theorem unknownMethodCode : unknownMethod.code = [.unadmitted 40] := rfl

#print axioms unknownMethodCode

/-- The linked instance slot takes the receiver type from the preceding constrained prefix. -/
private def constrainedSlot : CallSite := {
  method := {
    owner := .object "Fixture" "Fixture.Interface", name := name!"Read",
    hasThis := true, genericArity := 0, returnType := .void, parameters := [] },
  declared := { convention := 0x20 }, name := "Read", target := .managed 1, typeArguments := [],
  parameterCount := 0, returnsValue := false }

/-- Closed decoding preserves a constrained receiver at a linked call and refuses an unowned pc. -/
theorem constrainedLinkCode :
    let receiver := TypeExpr.atom runtimeScope "System.Int32"
    let source := { body 111 constrainedSlot.declaringType name!"Read" "Read" with
      code := [⟨0, 0xFE16, .type receiver⟩, ⟨6, 111, .call constrainedSlot⟩] }
    let decode := fun links => (Method.ofRaw? .scalar {} links source []).map Method.code
    decode [(1, .direct 1)] = some [.nop, .call constrainedSlot.method
      { constrained := some receiver }] ∧ decode [] = some [.nop, .unadmitted 111] := by
  exact ⟨rfl, rfl⟩

#print axioms constrainedLinkCode

/-- Every resolved family rejects every instruction other than its exact result. -/
theorem otherInstructionRefused (family : LoweredFamily) (environment : LayoutEnvironment)
    (profile : FeatureProfile) (raw : RawInstruction) (role : Option FoldRole)
    (expected emitted : Instruction) (called : methodTokenCall raw.opcode = true)
    (claimed : siteClaim loweredCallFamily environment none raw = .lowered family)
    (resolved : family.resolve environment.callLayouts profile role raw = some expected)
    (other : emitted ≠ expected) :
    runtimeCatalog.siteAgrees environment profile raw emitted none role true = false := by
  change siteClaim loweredCallFamily environment none raw runtimeCatalog.table.find =
    .lowered family at claimed
  simp [ModelCatalog.siteAgrees, ModelCatalog.agreesAt, called,
    ModelCatalog.callRequirement, claimed, resolved,
    CallRequirement.accepts, other]

#print axioms otherInstructionRefused

/-- A missing overload requires its own opcode's hole and is refused at a live site. -/
theorem missingOverloadRefused (family : LoweredFamily) (environment : LayoutEnvironment)
    (profile : FeatureProfile) (raw : RawInstruction) (role : Option FoldRole)
    (emitted : Instruction) (called : methodTokenCall raw.opcode = true)
    (claimed : siteClaim loweredCallFamily environment none raw = .lowered family)
    (missing : family.resolve environment.callLayouts profile role raw = none) :
    runtimeCatalog.siteAgrees environment profile raw emitted none role true = false ∧
    (runtimeCatalog.siteAgrees environment profile raw emitted none role false = true ↔
      emitted = .unadmitted raw.opcode) := by
  change siteClaim loweredCallFamily environment none raw runtimeCatalog.table.find =
    .lowered family at claimed
  simp [ModelCatalog.siteAgrees, ModelCatalog.agreesAt, called,
    ModelCatalog.callRequirement, claimed, missing,
    CallRequirement.accepts]

#print axioms missingOverloadRefused

end Tests.LoweredCallRefusal
