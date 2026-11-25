import CIL.Safety.Execution
import CIL.Safety.StepComposition
import CIL.Extraction.CallAgreement
import CIL.Extraction.KernelEquation
import CIL.ProfileEquivalence
import Tests.Support

/-!
# Bit and byte-order helper model tests

The runtime table models `BitOperations`, the bit helpers each integer type declares and
`BinaryPrimitives.ReverseEndianness` by their scalar intrinsics. The model states each helper's
result: `System.Int32` for a count of `BitOperations`, and the integer type, a 64-bit word only at
64 bits, for a count the type declares. A helper site keeps its call, which steps as the
intrinsic it was lowered to, and the lowered intrinsic or another helper's is refused there.
-/

namespace Tests.BitModels
open CIL CIL.Extraction CIL.Safety

private def runtimeType (name : String) : TypeExpr := .atom runtimeScope name
private def byte : TypeExpr := .primitive .byte
private def sbyte : TypeExpr := .primitive .sbyte
private def short : TypeExpr := .primitive .int16
private def int : TypeExpr := .primitive .int32
private def uint : TypeExpr := .primitive .uint32
private def long : TypeExpr := .primitive .int64
private def ulong : TypeExpr := .primitive .uint64
private def bool : TypeExpr := .primitive .boolean
private def bitOperations : TypeExpr := runtimeType "System.Numerics.BitOperations"
private def binaryPrimitives : TypeExpr :=
  .atom spanMemoryScope "System.Buffers.Binary.BinaryPrimitives"

/-- `owner::name` taking `type`, then `System.Int32` when `rotation`, and returning `result`. -/
private def helper (owner : TypeExpr) (name : MetadataName) (type result : TypeExpr)
    (rotation := false) : MethodRef :=
  { owner, name, hasThis := false, genericArity := 0, returnType := result,
    parameters := if rotation then [type, int] else [type] }

private def popCount : MethodRef := helper bitOperations name!"PopCount" ulong int
private def leadingZeroCount : MethodRef := helper bitOperations name!"LeadingZeroCount" uint int
private def trailingZeroCount : MethodRef :=
  helper bitOperations name!"TrailingZeroCount" ulong int
private def log2 : MethodRef := helper bitOperations name!"Log2" ulong int
private def roundUp : MethodRef := helper bitOperations name!"RoundUpToPowerOf2" uint uint
private def rotateLeft : MethodRef :=
  helper bitOperations name!"RotateLeft" ulong ulong (rotation := true)
private def isPow2 : MethodRef := helper bitOperations name!"IsPow2" long bool
/-- `UInt64.PopCount`, which returns its type. -/
private def ulongPopCount : MethodRef := helper ulong name!"PopCount" ulong ulong
private def uintPopCount : MethodRef := helper uint name!"PopCount" uint uint
private def bytePopCount : MethodRef := helper byte name!"PopCount" byte byte
private def byteRotateLeft : MethodRef :=
  helper byte name!"RotateLeft" byte byte (rotation := true)
private def reverseUlong : MethodRef :=
  helper binaryPrimitives name!"ReverseEndianness" ulong ulong
private def reverseShort : MethodRef :=
  helper binaryPrimitives name!"ReverseEndianness" short short
private def reverseSbyte : MethodRef :=
  helper binaryPrimitives name!"ReverseEndianness" sbyte sbyte

-- Each helper resolves to its scalar intrinsic at the width and signedness of its type.
example : runtimeModel {} .call leadingZeroCount =
    some (.intrinsic (.scalar (.leadingZeroCount 32 .word32)) 1) := by decide +kernel
example : runtimeModel {} .call trailingZeroCount =
    some (.intrinsic (.scalar (.trailingZeroCount 64 .word32)) 1) := by decide +kernel
example : runtimeModel {} .call log2 = some (.intrinsic (.scalar (.log2 64 .word32)) 1) := by
  decide +kernel
example : runtimeModel {} .call roundUp =
    some (.intrinsic (.scalar (.roundUpToPowerOf2 32)) 1) := by decide +kernel
example : runtimeModel {} .call rotateLeft = some (.intrinsic (.scalar (.rotateLeft 64)) 2) := by
  decide +kernel
example : runtimeModel {} .call isPow2 = some (.intrinsic (.scalar (.isPow2 64 true)) 1) := by
  decide +kernel
example : runtimeModel {} .call byteRotateLeft =
    some (.intrinsic (.scalar (.rotateLeft 8)) 2) := by decide +kernel
example : runtimeModel {} .call (helper short name!"IsPow2" short bool) =
    some (.intrinsic (.scalar (.isPow2 16 true)) 1) := by decide +kernel
example : runtimeModel {} .call reverseUlong =
    some (.intrinsic (.scalar (.reverseEndianness 64 false)) 1) := by decide +kernel
example : runtimeModel {} .call reverseSbyte =
    some (.intrinsic (.scalar (.reverseEndianness 8 true)) 1) := by decide +kernel

-- A count of `BitOperations` returns `System.Int32`, as a 32-bit word at every width.
example : runtimeModel {} .call popCount =
    some (.intrinsic (.scalar (.popCount 64 .word32)) 1) := by decide +kernel
example : runtimeModel {} .call { popCount with returnType := ulong } = none := by decide +kernel
-- A count an integer type declares returns the type: a 64-bit word at 64 bits, a 32-bit word at
-- 32 bits, and a 32-bit word holding the narrow value at 8 and 16 bits.
example : runtimeModel {} .call ulongPopCount =
    some (.intrinsic (.scalar (.popCount 64 .word64)) 1) := by decide +kernel
example : runtimeModel {} .call uintPopCount =
    some (.intrinsic (.scalar (.popCount 32 .word32)) 1) := by decide +kernel
example : runtimeModel {} .call bytePopCount =
    some (.intrinsic (.scalar (.popCount 8 .word32)) 1) := by decide +kernel
example : runtimeModel {} .call (helper short name!"LeadingZeroCount" short short) =
    some (.intrinsic (.scalar (.leadingZeroCount 16 .word32)) 1) := by decide +kernel
example : runtimeModel {} .call { ulongPopCount with returnType := int } = none := by
  decide +kernel
example : runtimeModel {} .call { bytePopCount with returnType := int } = none := by
  decide +kernel

-- A receiver, a generic arity or method argument, a wrong or mixed parameter, a wrong result, a
-- signed `Log2`, a signed narrow rotation, a helper the owner does not declare, or another owner,
-- assembly or opcode has no model.
example : runtimeModel {} .call { popCount with hasThis := true } = none := by decide +kernel
example : runtimeModel {} .call { popCount with genericArity := 1 } = none := by decide +kernel
example : runtimeModel {} .call { popCount with methodArguments := [ulong] } = none := by
  decide +kernel
example : runtimeModel {} .call { rotateLeft with parameters := [ulong, long] } = none := by
  decide +kernel
example : runtimeModel {} .call { rotateLeft with parameters := [ulong] } = none := by
  decide +kernel
example : runtimeModel {} .call { popCount with parameters := [ulong, ulong] } = none := by
  decide +kernel
example : runtimeModel {} .call (helper ulong name!"PopCount" uint uint) = none := by
  decide +kernel
example : runtimeModel {} .call (helper bitOperations name!"PopCount" bool int) = none := by
  decide +kernel
example : runtimeModel {} .call
    (helper bitOperations name!"PopCount" (.atom "Fixture" "System.UInt64") int) = none := by
  decide +kernel
example : runtimeModel {} .call { roundUp with returnType := int } = none := by decide +kernel
example : runtimeModel {} .call (helper int name!"Log2" int int) = none := by decide +kernel
example : runtimeModel {} .call (helper bitOperations name!"Log2" long int) = none := by
  decide +kernel
example : runtimeModel {} .call (helper sbyte name!"RotateLeft" sbyte sbyte (rotation := true)) =
    none := by decide +kernel
example : runtimeModel {} .call (helper bitOperations name!"PopCount" byte int) = none := by
  decide +kernel
example : runtimeModel {} .call (helper uint name!"RoundUpToPowerOf2" uint uint) = none := by
  decide +kernel
example : runtimeModel {} .call (helper bitOperations name!"ReverseEndianness" ulong ulong) =
    none := by decide +kernel
/-- `BinaryPrimitives` as `System.Runtime` would declare it. -/
private def runtimePrimitives : TypeExpr := runtimeType "System.Buffers.Binary.BinaryPrimitives"
example : runtimeModel {} .call { reverseUlong with owner := runtimePrimitives } = none := by
  decide +kernel
/-- `BitOperations` as `System.Memory` and as `System.Private.CoreLib` would declare it. -/
private def memoryBits : TypeExpr := .atom spanMemoryScope "System.Numerics.BitOperations"
private def coreBits : TypeExpr := .atom "System.Private.CoreLib" "System.Numerics.BitOperations"
example : runtimeModel {} .call { popCount with owner := memoryBits } = none := by decide +kernel
example : runtimeModel {} .call { popCount with owner := coreBits } = none := by decide +kernel
example : runtimeModel {} .newobj popCount = none := by decide +kernel

/-- A method whose only instruction is `instruction`. -/
private def method (instruction : RawInstruction) : RawMethod :=
  { token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
    attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
    initLocals := true, maxStack := 3, genericParameters := [], code := [instruction] }

/-- A call of `method`. -/
private def site (method : MethodRef) : RawInstruction :=
  ⟨0, 40, .call {
    method, declared := method.signature 0, target := .external "", typeArguments := [],
    parameterCount := method.parameters.length, returnsValue := true }⟩

/-- The bit and byte-order members require the default static calling convention. -/
example : [popCount, reverseUlong].all (fun method =>
    [0x40, 0x60, 0x01].all fun header =>
      let operand : CallSite := {
        method, declared := method.signature header,
        target := .external "", typeArguments := [], parameterCount := 1, returnsValue := true }
      !runtimeCatalog.siteAgrees {} {} ⟨0, 40, .call operand⟩ (.call method {})) := by
  decide +kernel

/-- A link does not excuse a mismatched model declaration at an occupied pc. -/
theorem linkedDeclarationRequired :
    let operand : CallSite := {
      method := popCount, declared := popCount.signature 0x40,
      target := .external "", typeArguments := [], parameterCount := 1, returnsValue := true }
    runtimeCatalog.siteAgrees {} {} ⟨0, 40, .call operand⟩ (.call popCount {})
      (some (.direct 0)) true = false := by decide +kernel

#print axioms linkedDeclarationRequired

/-- A method with no code, on the scalar profile. -/
private def body : CIL.Method := { code := [], locals := [], returnsValue := false }

/-- A body whose only instruction is `emitted`, with no link. -/
private def emitting (emitted : CIL.Instruction) : CIL.Method := { body with code := [emitted] }

/-- Each helper family has model ownership at its raw site. -/
theorem bitClaims :
    siteClaim {} none (site popCount) = .model ∧
    siteClaim {} none (site ulongPopCount) = .model ∧
    siteClaim {} none (site reverseUlong) = .model := by decide +kernel

#print axioms bitClaims

private def leading64 : CIL.Instruction :=
  .call (helper bitOperations name!"LeadingZeroCount" ulong int)
example : RuntimeModelsAgree (method (site popCount)) [true] (emitting (.call popCount {})) := by
  decide +kernel
example : ¬ RuntimeModelsAgree (method (site popCount)) [true] (emitting leading64) := by
  decide +kernel
example : ManagedCallsValid [] [] (callModelled body) (method (site popCount)) [true]
    (emitting (.call popCount {})) := by decide +kernel
example : ¬ ManagedCallsValid [] [] (callModelled body) (method (site popCount)) [true]
    (emitting (.call log2 {})) := by decide +kernel
private def narrowCount : CIL.Instruction := .call popCount
example : ¬ RuntimeModelsAgree (method (site ulongPopCount)) [true] (emitting narrowCount) := by
  decide +kernel
private def reverse32 : CIL.Instruction := .call (helper binaryPrimitives name!"ReverseEndianness" uint uint)
example : ¬ RuntimeModelsAgree (method (site reverseUlong)) [true] (emitting reverse32) := by
  decide +kernel

-- The helpers read no profile flag: a helper site agrees under the scalar and the AVX2 profile,
-- and every two profiles agree on a program that calls one.
example : runtimeCatalog.siteAgrees {} {} (site popCount) (.call popCount {}) = true := by
  decide +kernel
example : runtimeCatalog.siteAgrees {} { avx2 := true } (site popCount) (.call popCount {}) =
    true := by decide +kernel
/-- A method that returns the population of its argument. -/
private def popCountProgram : CIL.Program :=
  [{ body with code := [.ldarg 0, .call popCount {}, .ret], returnsValue := true }]
example : CIL.Program.profileReads popCountProgram = [] := by decide +kernel
example : CIL.Program.ProfileAgreement popCountProgram {} { avx2 := true } :=
  CIL.Program.ProfileAgreement.of_flags _ _ _ (by decide +kernel)

/-! ## Steps -/

private def frame : Frame := { activation := 0, locals := [], owned := [] }

/-- A body whose only instruction is a call of `method`, with no link. -/
private def calling (method : MethodRef) : CIL.Method := { body with code := [.call method {}] }
private def i32 (bits : Nat) : CIL.Safety.Value := .scalar (.i32 (BitVec.ofNat 32 bits))
private def i64 (bits : Nat) : CIL.Safety.Value := .scalar (.i64 (BitVec.ofNat 64 bits))

-- Each checked call runs its declared intrinsic, and the result word is the one the
-- model states: an int from `BitOperations.PopCount`, a long from `UInt64.PopCount`.
example : step (calling popCount) (.call popCount {}) 0 [] frame [i64 7] Memory.empty =
    intrinsicCall body.profile (.scalar (.popCount 64 .word32)) 1 0 frame [i64 7]
      Memory.empty := by rfl
example : step (calling popCount) (.call popCount {}) 0 [] frame [i64 7] Memory.empty =
    .ok (.next 1 [i32 3] frame Memory.empty) := by rfl
example : step (calling ulongPopCount) (.call ulongPopCount {}) 0 [] frame [i64 7] Memory.empty =
    .ok (.next 1 [i64 3] frame Memory.empty) := by rfl
example : step (calling bytePopCount) (.call bytePopCount {}) 0 [] frame [i32 0x1FF]
    Memory.empty = .ok (.next 1 [i32 8] frame Memory.empty) := by rfl
example : step (calling rotateLeft) (.call rotateLeft {}) 0 [] frame [i64 1, i32 65]
      Memory.empty =
    intrinsicCall body.profile (.scalar (.rotateLeft 64)) 2 0 frame [i64 1, i32 65]
      Memory.empty := by rfl
example : step (calling isPow2) (.call isPow2 {}) 0 [] frame [i64 (2 ^ 63)] Memory.empty =
    .ok (.next 1 [i32 0] frame Memory.empty) := by rfl

-- The counts and `Log2` of zero, `RoundUpToPowerOf2` past the largest power, and the byte
-- reversal of a sign-extended narrow value step as their intrinsics.
example : step (calling log2) (.call log2 {}) 0 [] frame [i64 0] Memory.empty =
    intrinsicCall body.profile (.scalar (.log2 64 .word32)) 1 0 frame [i64 0] Memory.empty := by
  rfl
example : step (calling log2) (.call log2 {}) 0 [] frame [i64 0] Memory.empty =
    .ok (.next 1 [i32 0] frame Memory.empty) := by rfl
example : step (calling leadingZeroCount) (.call leadingZeroCount {}) 0 [] frame [i32 0]
      Memory.empty =
    intrinsicCall body.profile (.scalar (.leadingZeroCount 32 .word32)) 1 0 frame [i32 0]
      Memory.empty := by rfl
example : step (calling leadingZeroCount) (.call leadingZeroCount {}) 0 [] frame [i32 0]
    Memory.empty = .ok (.next 1 [i32 32] frame Memory.empty) := by rfl
example : step (calling trailingZeroCount) (.call trailingZeroCount {}) 0 [] frame [i64 0]
    Memory.empty = .ok (.next 1 [i32 64] frame Memory.empty) := by rfl
example : step (calling popCount) (.call popCount {}) 0 [] frame [i64 0] Memory.empty =
    .ok (.next 1 [i32 0] frame Memory.empty) := by rfl
example : step (calling roundUp) (.call roundUp {}) 0 [] frame [i32 0x80000001] Memory.empty =
    intrinsicCall body.profile (.scalar (.roundUpToPowerOf2 32)) 1 0 frame [i32 0x80000001]
      Memory.empty := by rfl
example : step (calling roundUp) (.call roundUp {}) 0 [] frame [i32 0x80000001] Memory.empty =
    .ok (.next 1 [i32 0] frame Memory.empty) := by rfl
example : step (calling reverseShort) (.call reverseShort {}) 0 [] frame [i32 0xFFFFFF80]
      Memory.empty =
    intrinsicCall body.profile (.scalar (.reverseEndianness 16 true)) 1 0 frame [i32 0xFFFFFF80]
      Memory.empty := by rfl
example : step (calling reverseShort) (.call reverseShort {}) 0 [] frame [i32 0xFFFFFF80]
    Memory.empty = .ok (.next 1 [i32 0xFFFF80FF] frame Memory.empty) := by rfl
example : step (calling reverseSbyte) (.call reverseSbyte {}) 0 [] frame [i32 0xFFFFFF80]
    Memory.empty = .ok (.next 1 [i32 0xFFFFFF80] frame Memory.empty) := by rfl
-- A call faults where its intrinsic does: a 64-bit helper given a 32-bit word.
example : step (calling popCount) (.call popCount {}) 0 [] frame [i32 7] Memory.empty =
    intrinsicCall body.profile (.scalar (.popCount 64 .word32)) 1 0 frame [i32 7]
      Memory.empty := by rfl
example : (step (calling popCount) (.call popCount {}) 0 [] frame [i32 7] Memory.empty).toBool =
    false := by rfl

end Tests.BitModels
