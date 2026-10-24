import Lean
import CIL.Extraction.Translation
import CIL.SIMD.DivisionLemmas

open CIL CIL.Extraction

namespace Tests.DivisionIntrinsics

private def scope := "System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"
private def runtimeScope := "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
private def vectorType (width : String) : TypeExpr :=
  .apply (.constructor scope ("System.Runtime.Intrinsics.Vector" ++ width ++ "`1"))
    (.atom runtimeScope "System.UInt64")
private def profile : FeatureProfile := { architecture := .x64, x86Base64 := true, sse2 := true, ssse3 := true, sse41 := true, sse42 := true, avx := true, avx2 := true, bmi1 := true, bmi2 := true, avx512F := true, avx512FVL := true, avx512DQ := true, avx512DQVL := true, vector128Accelerated := true, vector256Accelerated := true }
private def body (operations : List Op) : Method := { code := operations, locals := [], returnsValue := true, profile }
private def raw (site : CallSite) : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := false,
  maxStack := 2, genericParameters := [], code := [⟨0, 40, .call site⟩] }
private def call0 : CallSite := {
  declaringType := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := "And",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::And(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)"), typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := true, returnType := vectorType "256", parameterTypes := [vectorType "256", vectorType "256"] }
example : DivisionIntrinsicsValid (raw call0) [true] (body [.intrinsic (.avx2 .band) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call0 with returnType := .atom runtimeScope "System.UInt64" }) [true]
    (body [.intrinsic (.avx2 .band) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call0 with parameterTypes := [vectorType "128", vectorType "256"] }) [true]
    (body [.intrinsic (.avx2 .band) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call0) [true] (body [.intrinsic (.avx2 .band) 3]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call0 with hasThis := true }) [true] (body [.intrinsic (.avx2 .band) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call0 with target := .external "forged" }) [true] (body [.intrinsic (.avx2 .band) 2]) := by decide +kernel
private def call1 : CallSite := {
  declaringType := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := "Or",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::Or(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)"), typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := true, returnType := vectorType "256", parameterTypes := [vectorType "256", vectorType "256"] }
example : DivisionIntrinsicsValid (raw call1) [true] (body [.intrinsic (.avx2 .bor) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call1) [true] (body [.intrinsic (.avx2 .bor) 3]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call1 with hasThis := true }) [true] (body [.intrinsic (.avx2 .bor) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call1 with target := .external "forged" }) [true] (body [.intrinsic (.avx2 .bor) 2]) := by decide +kernel
private def call2 : CallSite := {
  declaringType := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := "Xor",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::Xor(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)"), typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := true, returnType := vectorType "256", parameterTypes := [vectorType "256", vectorType "256"] }
example : DivisionIntrinsicsValid (raw call2) [true] (body [.intrinsic (.avx2 .bxor) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call2) [true] (body [.intrinsic (.avx2 .bxor) 3]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call2 with hasThis := true }) [true] (body [.intrinsic (.avx2 .bxor) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call2 with target := .external "forged" }) [true] (body [.intrinsic (.avx2 .bxor) 2]) := by decide +kernel
private def call3 : CallSite := {
  declaringType := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := "AndNot",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::AndNot(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)"), typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := true, returnType := vectorType "256", parameterTypes := [vectorType "256", vectorType "256"] }
example : DivisionIntrinsicsValid (raw call3) [true] (body [.intrinsic (.avx2 .andNot) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call3) [true] (body [.intrinsic (.avx2 .andNot) 3]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call3 with hasThis := true }) [true] (body [.intrinsic (.avx2 .andNot) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call3 with target := .external "forged" }) [true] (body [.intrinsic (.avx2 .andNot) 2]) := by decide +kernel
private def call4 : CallSite := {
  declaringType := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := "ShiftLeftLogical"
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::ShiftLeftLogical(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector128`1<System.UInt64>)"), typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := true, returnType := vectorType "256", parameterTypes := [vectorType "256", vectorType "128"] }
example : DivisionIntrinsicsValid (raw call4) [true] (body [.intrinsic (.avx2 .shl64Count) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call4) [true] (body [.intrinsic (.avx2 .shl64Count) 3]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call4 with hasThis := true }) [true] (body [.intrinsic (.avx2 .shl64Count) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call4 with target := .external "forged" }) [true] (body [.intrinsic (.avx2 .shl64Count) 2]) := by decide +kernel
private def call5 : CallSite := {
  declaringType := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := "ShiftRightLogical"
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::ShiftRightLogical(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector128`1<System.UInt64>)"), typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := true, returnType := vectorType "256", parameterTypes := [vectorType "256", vectorType "128"] }
example : DivisionIntrinsicsValid (raw call5) [true] (body [.intrinsic (.avx2 .shr64Count) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call5) [true] (body [.intrinsic (.avx2 .shr64Count) 3]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call5 with hasThis := true }) [true] (body [.intrinsic (.avx2 .shr64Count) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call5 with target := .external "forged" }) [true] (body [.intrinsic (.avx2 .shr64Count) 2]) := by decide +kernel
private def call6 : CallSite := {
  declaringType := .atom scope "System.Runtime.Intrinsics.X86.Avx512F", name := "CompareLessThan",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector512`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx512F::CompareLessThan(System.Runtime.Intrinsics.Vector512`1<System.UInt64>,System.Runtime.Intrinsics.Vector512`1<System.UInt64>)"), typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := true, returnType := vectorType "512", parameterTypes := [vectorType "512", vectorType "512"] }
example : DivisionIntrinsicsValid (raw call6) [true] (body [.intrinsic (.avx512 .ltu512) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call6) [true] (body [.intrinsic (.avx512 .ltu512) 3]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call6 with hasThis := true }) [true] (body [.intrinsic (.avx512 .ltu512) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call6 with target := .external "forged" }) [true] (body [.intrinsic (.avx512 .ltu512) 2]) := by decide +kernel
private def call7 : CallSite := {
  declaringType := .atom scope "System.Runtime.Intrinsics.X86.Avx512F", name := "CompareGreaterThan",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector512`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx512F::CompareGreaterThan(System.Runtime.Intrinsics.Vector512`1<System.UInt64>,System.Runtime.Intrinsics.Vector512`1<System.UInt64>)"), typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := true, returnType := vectorType "512", parameterTypes := [vectorType "512", vectorType "512"] }
example : DivisionIntrinsicsValid (raw call7) [true] (body [.intrinsic (.avx512 .gtu512) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call7) [true] (body [.intrinsic (.avx512 .gtu512) 3]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call7 with hasThis := true }) [true] (body [.intrinsic (.avx512 .gtu512) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call7 with target := .external "forged" }) [true] (body [.intrinsic (.avx512 .gtu512) 2]) := by decide +kernel
private def call8 : CallSite := {
  declaringType := .atom scope "System.Runtime.Intrinsics.X86.Avx512DQ", name := "MoveMask"
  target := .external (scope ++ "::System.Int32 System.Runtime.Intrinsics.X86.Avx512DQ::MoveMask(System.Runtime.Intrinsics.Vector512`1<System.UInt64>)"), typeArguments := [], parameterCount := 1, hasThis := false, returnsValue := true, returnType := .atom runtimeScope "System.Int32", parameterTypes := [vectorType "512"] }
example : DivisionIntrinsicsValid (raw call8) [true] (body [.intrinsic (.avx512DQ .moveMask512) 1]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call8) [true] (body [.intrinsic (.avx512DQ .moveMask512) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call8 with hasThis := true }) [true] (body [.intrinsic (.avx512DQ .moveMask512) 1]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call8 with target := .external "forged" }) [true] (body [.intrinsic (.avx512DQ .moveMask512) 1]) := by decide +kernel
private def call9 : CallSite := {
  declaringType := .atom scope "System.Runtime.Intrinsics.Vector512", name := "Create",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector512`1<System.UInt64> System.Runtime.Intrinsics.Vector512::Create(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)"), typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := true, returnType := vectorType "512", parameterTypes := [vectorType "256", vectorType "256"] }
example : DivisionIntrinsicsValid (raw call9) [true] (body [.intrinsic (.vector .combine256) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call9) [true] (body [.intrinsic (.vector .combine256) 3]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call9 with hasThis := true }) [true] (body [.intrinsic (.vector .combine256) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call9 with target := .external "forged" }) [true] (body [.intrinsic (.vector .combine256) 2]) := by decide +kernel
private def call10 : CallSite := {
  declaringType := .atom scope "System.Runtime.Intrinsics.Vector128", name := "CreateScalarUnsafe",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector128`1<System.UInt64> System.Runtime.Intrinsics.Vector128::CreateScalarUnsafe(System.UInt64)"), typeArguments := [], parameterCount := 1, hasThis := false, returnsValue := true, returnType := vectorType "128", parameterTypes := [.atom runtimeScope "System.UInt64"] }
example : DivisionIntrinsicsValid (raw call10) [true] (body [.intrinsic (.vector .createScalarUnsafe64) 1]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call10) [true] (body [.intrinsic (.vector .createScalarUnsafe64) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call10 with hasThis := true }) [true] (body [.intrinsic (.vector .createScalarUnsafe64) 1]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call10 with target := .external "forged" }) [true] (body [.intrinsic (.vector .createScalarUnsafe64) 1]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call10 with target := .external "forged" }) [true]
    (body [.intrinsic (.vector (.createScalar64 128)) 1]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw { call0 with parameterCount := 1 }) [true]
    (body [.intrinsic (.vector (.band 256)) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call0) [true] (body [.intrinsic (.avx2 .bor) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call4) [true] (body [.intrinsic (.avx2 .shl64) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call6) [true] (body [.intrinsic (.avx512 .gtu512) 2]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call10) [true] (body [.intrinsic (.vector (.createScalar64 128)) 1]) := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call0) [true]
    { body [.intrinsic (.avx2 .band) 2] with profile := .scalar } := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call6) [true]
    { body [.intrinsic (.avx512 .ltu512) 2] with profile := { profile with avx512F := false } } := by decide +kernel
example : ¬ DivisionIntrinsicsValid (raw call8) [true]
    { body [.intrinsic (.avx512DQ .moveMask512) 1] with profile := { profile with avx512DQ := false } } := by decide +kernel
example : Intrinsic.available profile (.avx512 .ltu512) = true := by decide +kernel
example : Intrinsic.available profile (.avx512DQ .moveMask512) = true := by decide +kernel

example : ¬ DivisionIntrinsicsValid (raw call0) [true]
    { body [.intrinsic (.avx2 .band) 2] with profile := { profile with architecture := .arm64 } } := by decide +kernel

private def vector128 : TypeExpr := .apply (.constructor scope "System.Runtime.Intrinsics.Vector128`1") (.atom runtimeScope "System.UInt64")
private def withLocal : RawMethod := { raw call10 with locals := [vector128], code := [] }
private def localBody : Method := { body [.intrinsic (.vector .createScalarUnsafe64) 1] with locals := [.unmodeled], localKinds := [.vector128], opaqueVectorLocals := [0] }
example : OpaqueLocalsValid withLocal localBody := by decide +kernel
example : OpaqueLocalsValid withLocal { localBody with code := [], opaqueVectorLocals := [] } := by decide +kernel
example : ¬ OpaqueLocalsValid withLocal { localBody with code := [] } := by decide +kernel
example : ¬ OpaqueLocalsValid withLocal { localBody with opaqueVectorLocals := [] } := by decide +kernel
example : ¬ OpaqueLocalsValid { withLocal with code := [⟨0, 18, .local 0⟩] } localBody := by decide +kernel
example : ¬ OpaqueLocalsValid { withLocal with code := [⟨0, 65037, .local 0⟩] } localBody := by decide +kernel
example : ¬ OpaqueLocalsValid withLocal
    { localBody with code := [.intrinsic (.vector .createScalarUnsafe64) 1, .localAddr 0] } := by decide +kernel
example : ¬ OpaqueLocalsValid withLocal { localBody with localKinds := [.word64] } := by decide +kernel
example : ¬ OpaqueLocalsValid { withLocal with locals := [.atom runtimeScope "System.UInt64"] } localBody := by decide +kernel

example : evalIntrinsic (.avx2 .andNot) [.v256 1, .v256 3] = some (.v256 2) := by decide +kernel
example : evalIntrinsic (.vector .combine256) [.v256 1, .v256 2] = some (.v512 ((2 : BitVec 256) ++ (1 : BitVec 256))) := rfl
example : evalIntrinsic (.vector .createScalarUnsafe64) [.i64 7] = some (.v128Low64 7) := rfl
example : evalIntrinsic (.vector (.extract64 128)) [.v128Low64 7, .i32 0] = some (.i64 7) := rfl
example : Safety.checkedIntrinsic (.vector (.extract64 128)) [.v128Low64 7, .i32 1] =
    .error (.unsupported "Intrinsic observes unspecified vector bits") := rfl
example : Safety.checkedIntrinsic (.vector (.equalsAll 128)) [.v128Low64 7, .v128 7] =
    .error (.unsupported "Intrinsic observes unspecified vector bits") := rfl
example : Safety.bitcastValue .vector128 .vector128 (.v128Low64 7) =
    .error (.unsupported "Bitcast observes unspecified vector bits") := rfl
example (memory : Safety.Memory) : Safety.storeLocal memory (.opaque128 none) (.scalar (.v128Low64 7)) =
    .ok (.opaque128 (some (.low64 7)), memory) := rfl
example (memory : Safety.Memory) : Safety.makeArgumentHomes 0 [0] [.scalar (.v128Low64 7)] memory =
    .error (.unsupported "Argument home observes unspecified vector bits") := rfl
example (memory : Safety.Memory) : Safety.instruction .eq [.scalar (.v128Low64 7), .scalar (.v128Low64 7)] memory =
    .error (.unsupported "Instruction observes unspecified vector bits") := rfl

theorem unspecified_return (body : Method) (memory : Safety.Memory) (frame : Safety.Frame) :
    Safety.step body .ret 0 [] frame [.scalar (.v128Low64 7)] memory =
      .error (.unsupported "Instruction observes unspecified vector bits") := rfl
#print axioms unspecified_return

theorem unspecified_call (body : Method) (memory : Safety.Memory) (frame : Safety.Frame) :
    Safety.step body (.call 1 2) 0 [] frame [.scalar (.i64 0), .scalar (.v128Low64 7)] memory =
      .error (.unsupported "Instruction observes unspecified vector bits") := rfl
#print axioms unspecified_call

theorem unspecified_call_rest (body : Method) (memory : Safety.Memory) (frame : Safety.Frame) :
    Safety.step body (.call 1 1) 0 [] frame [.scalar (.i64 3), .scalar (.v128Low64 7)] memory =
      .ok (.call 1 [.scalar (.i64 3)] [.scalar (.v128Low64 7)] memory) := rfl
#print axioms unspecified_call_rest

theorem defined_vector_return (memory : Safety.Memory) (frame : Safety.Frame) (bits : BitVec 128) :
    Safety.step { code := [], locals := [], returnsValue := true } .ret 0 [] frame [.scalar (.v128 bits)] memory =
      .ok (.returned [.scalar (.v128 bits)] memory) := rfl
#print axioms defined_vector_return

theorem unspecified_constructor (body : Method) (memory : Safety.Memory) (frame : Safety.Frame) :
    Safety.step body (.newAggregate 1 1 16) 0 [] frame [.scalar (.v128Low64 7)] memory =
      .error (.unsupported "Instruction observes unspecified vector bits") := rfl
#print axioms unspecified_constructor

theorem unspecified_store (memory : Safety.Memory) (destination : Safety.ManagedReference) :
    Safety.storeValue memory destination (.v128Low64 7) =
      .error (.unsupported "Store observes unspecified vector bytes") := rfl
#print axioms unspecified_store
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 0) 3 = 1 := by decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 0) 3 = 1 := by decide +kernel
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 1) 3 = 2 := by decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 1) 3 = 0 := by decide +kernel
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 63) 3 = 9223372036854775808 := by decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 63) 3 = 0 := by decide +kernel
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 64) 3 = 0 := by decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 64) 3 = 0 := by decide +kernel
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 255) 3 = 0 := by decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 255) 3 = 0 := by decide +kernel
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 256) 3 = 0 := by decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 256) 3 = 0 := by decide +kernel
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 18446744073709551615) 3 = 0 := by decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 18446744073709551615) 3 = 0 := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 9223372036854775808 0 0 0 0 0 0 0) = 1 := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 9223372036854775808 0 0 0 0 0 0) = 2 := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 0 9223372036854775808 0 0 0 0 0) = 4 := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 0 0 9223372036854775808 0 0 0 0) = 8 := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 0 0 0 9223372036854775808 0 0 0) = 16 := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 0 0 0 0 9223372036854775808 0 0) = 32 := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 0 0 0 0 0 9223372036854775808 0) = 64 := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 0 0 0 0 0 0 9223372036854775808) = 128 := by decide +kernel
example : evalIntrinsic (.avx512 .ltu512)
    [.v512 (Vector.pack512 9223372036854775808 1 0 0 0 0 0 0),
     .v512 (Vector.pack512 1 1 0 0 0 0 0 0)] = some (.v512 0) := by decide +kernel

example : DivisionIntrinsicsValid (raw {
    declaringType := .atom scope "System.Runtime.Intrinsics.X86.Avx2"
    name := "ShiftLeftLogical"
    target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::ShiftLeftLogical(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Byte)"),
    typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := true, returnType := vectorType "256", parameterTypes := [vectorType "256", .atom runtimeScope "System.Byte"] }) [true]
    (body [.intrinsic (.avx2 .shl64) 2]) := by decide +kernel

example : DivisionIntrinsicsValid (raw {
    declaringType := .atom scope "System.Runtime.Intrinsics.X86.Avx2"
    name := "ShiftRightLogical"
    target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::ShiftRightLogical(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Byte)"),
    typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := true, returnType := vectorType "256", parameterTypes := [vectorType "256", .atom runtimeScope "System.Byte"] }) [true]
    (body [.intrinsic (.avx2 .shr64) 2]) := by decide +kernel

example : DivisionIntrinsicsValid (raw {
    declaringType := .atom scope "System.Runtime.Intrinsics.X86.Avx512DQ"
    name := "MoveMask"
    target := .external (scope ++ "::System.Int32 System.Runtime.Intrinsics.X86.Avx512DQ::MoveMask(System.Runtime.Intrinsics.Vector256`1<System.UInt64>)"),
    typeArguments := [], parameterCount := 1, hasThis := false, returnsValue := true, returnType := .atom runtimeScope "System.Int32", parameterTypes := [vectorType "256"] }) [true]
    (body [.intrinsic (.avx512DQ .moveMask64) 1]) := by decide +kernel


private def initBody (type : TypeExpr) : RawMethod :=
  { raw call0 with code := [⟨0, 65045, .type type⟩] }

example : VectorInitializationsValid (initBody (vectorType "128")) [true]
    (body [.initAggregate 16]) := by decide +kernel
example : VectorInitializationsValid (initBody (vectorType "256")) [true]
    (body [.initAggregate 32]) := by decide +kernel
example : VectorInitializationsValid (initBody (vectorType "512")) [true]
    (body [.initAggregate 64]) := by decide +kernel
example : VectorInitializationsValid (initBody (vectorType "512")) [true]
    { body [.initAggregate 64] with profile := .scalar } := by decide +kernel
example : VectorInitializationsValid (initBody (vectorType "256")) [true]
    { body [.initAggregate 32] with profile := { architecture := .arm64 } } := by decide +kernel
example : ¬ VectorInitializationsValid (initBody (vectorType "128")) [true]
    (body [.initAggregate 32]) := by decide +kernel
example : ¬ VectorInitializationsValid (initBody (vectorType "256")) [true]
    (body [.initAggregate 16]) := by decide +kernel
example : ¬ VectorInitializationsValid (initBody (vectorType "512")) [true]
    (body [.initAggregate 32]) := by decide +kernel
example : ¬ VectorInitializationsValid (initBody (vectorType "128")) [true]
    (body [.nop]) := by decide +kernel
example : ¬ VectorInitializationsValid
    { initBody (vectorType "128") with code := [⟨0, 113, .type (vectorType "128")⟩] } [true]
    (body [.initAggregate 16]) := by decide +kernel
example : ¬ VectorInitializationsValid (initBody (.atom runtimeScope "System.UInt64")) [true]
    (body [.initAggregate 16]) := by decide +kernel
example : ¬ VectorInitializationsValid
    (initBody (.apply (.constructor "forged" "System.Runtime.Intrinsics.Vector128`1") (.atom runtimeScope "System.UInt64")))
    [true] (body [.initAggregate 16]) := by decide +kernel
example : ¬ VectorInitializationsValid
    (initBody (.apply (.constructor scope "System.Runtime.Intrinsics.Vector128`1") (.atom "forged" "System.UInt64")))
    [true] (body [.initAggregate 16]) := by decide +kernel
example : ¬ VectorInitializationsValid
    (initBody (.apply (.constructor scope "System.Runtime.Intrinsics.Vector128`1") (.atom runtimeScope "System.Int64")))
    [true] (body [.initAggregate 16]) := by decide +kernel
example : ¬ VectorInitializationsValid
    (initBody (.apply (.constructor scope "System.Runtime.Intrinsics.Vector64`1") (.atom runtimeScope "System.UInt64")))
    [true] (body [.initAggregate 16]) := by decide +kernel
example : ¬ VectorInitializationsValid (initBody (vectorType "128")) [true]
    { body [.initAggregate 16] with profile := { nativeWidth := 32 } } := by decide +kernel
example : ¬ VectorInitializationsValid (initBody (vectorType "128")) []
    (body [.initAggregate 16]) := by decide +kernel
example : ¬ VectorInitializationsValid (initBody (vectorType "128")) [true]
    (body []) := by decide +kernel

-- A default case yields a guarded equation, so a new op reading vector bits would pass as a
-- forwarder. Every equation must be unconditional: one per constructor pattern.
open Lean Meta in
run_meta do
  for name in [``CIL.Safety.observerCount, ``CIL.MemoryOp.argumentCount] do
    let some equations ← getEqnsFor? name | throwError "No equations for {name}"
    for equation in equations do
      let type ← inferType (← mkConstWithLevelParams equation)
      forallTelescope type fun binders _ => do
        for binder in binders do
          if ← isProp (← inferType binder) then
            throwError "{name} has a default case: {equation} assumes {← inferType binder}"

-- Unspecified lanes reach only the four lane-0 consumers, whatever else evalIntrinsic admits.
example : Safety.checkedIntrinsic (.vector (.reinterpret 128)) [.v128Low64 7] = .ok (.v128Low64 7) := rfl
example : Safety.checkedIntrinsic (.avx2 .shl64Count) [.v256 1, .v128Low64 1] = .ok (.v256 (Vector.shiftLeftCount64 1 1)) := rfl
example : Safety.checkedIntrinsic (.vector (.reinterpret 256)) [.v128Low64 7] =
    .error (.unsupported "Intrinsic observes unspecified vector bits") := rfl
example : Safety.checkedIntrinsic (.avx2 .shl64Count) [.v128Low64 1, .v128Low64 1] =
    .error (.unsupported "Intrinsic observes unspecified vector bits") := rfl
example : Safety.checkedIntrinsic (.scalar (.leadingZeroCount 64)) [.v128Low64 1] =
    .error (.unsupported "Intrinsic observes unspecified vector bits") := rfl

end Tests.DivisionIntrinsics
