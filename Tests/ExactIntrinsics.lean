import Tests.Support.EnumIdentity
import Lean
import CIL.Extraction.DecodedMethod
import CIL.SIMD.UnspecifiedLanes
import CIL.Safety.IntrinsicExecution
import Tests.Support
import Tests.Support.RawDecoding
import Tests.ExactIntrinsics.WordContracts

open CIL CIL.Extraction

namespace Tests.ExactIntrinsics

private def scope :=
  "System.Runtime.Intrinsics, Version=11.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"
private def runtimeScope :=
  "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
private def vectorType (width : String) : TypeExpr :=
  .apply (.constructor scope ("System.Runtime.Intrinsics.Vector" ++ width ++ "`1"))
    (.primitive .uint64)
private def profile : FeatureProfile := { architecture := .x64, x86Base64 := true, sse2 := true, ssse3 := true, sse41 := true, sse42 := true, avx := true, avx2 := true, bmi1 := true, bmi2 := true, avx512F := true, avx512FVL := true, avx512DQ := true, avx512DQVL := true, vector128Accelerated := true, vector256Accelerated := true }
private def body (operations : List Instruction) : Method :=
  { code := operations, locals := [], returnsValue := true, profile }
private def raw (site : CallSite) : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := false,
  maxStack := 2, genericParameters := [], code := [⟨0, 40, .call site⟩] }
/-- A resolving call keeps its reference and executes the expected operation. -/
private def keeps (site : CallSite) (expected : RuntimeModel) (features := profile) : Bool :=
  runtimeModel {} .call site.method == some expected &&
    decide ((decodeRaw features {} [] [true] (raw site) []).map Method.code =
      .ok [.call site.method {}])

/-- A live unresolved operand produces its own opcode's hole and prevents method construction. -/
private def refuses (site : CallSite) (features := profile) : Bool :=
  methodCode features {} [] [true] (raw site) == [.unadmitted 40] &&
    decide ((decodeRaw features {} [] [true] (raw site) []).map Method.code = liveHoleAt 0 40)

private def call0 : CallSite := {
  declared := {
    convention := 0, returnType := vectorType "256",
    parameters := [vectorType "256", vectorType "256"] },
  method := {
    owner := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := name!"And",
    hasThis := false, genericArity := 0, returnType := vectorType "256",
    parameters := [vectorType "256", vectorType "256"] },
  name := "And",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
    System.Runtime.Intrinsics.X86.Avx2::And(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
    System.Runtime.Intrinsics.Vector256`1<System.UInt64>)"),
  typeArguments := [], parameterCount := 2, returnsValue := true }
example : keeps call0 (.intrinsic (.avx2 .band) 2) := by decide +kernel
example : refuses { call0 with method.returnType := .primitive .uint64 } := by
  decide +kernel
example : refuses { call0 with method.parameters := [vectorType "128", vectorType "256"] } := by
  decide +kernel
example : runtimeModel {} .call call0.method ≠ some (.intrinsic (.avx2 .band) 3) := by
  decide +kernel
example : refuses { call0 with method.hasThis := true } := by decide +kernel
example : refuses { call0 with target := .external "forged" } := by decide +kernel
private def call1 : CallSite := {
  declared := {
    convention := 0, returnType := vectorType "256",
    parameters := [vectorType "256", vectorType "256"] },
  method := {
    owner := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := name!"Or", hasThis := false,
    genericArity := 0, returnType := vectorType "256",
    parameters := [vectorType "256", vectorType "256"] },
  name := "Or",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
    System.Runtime.Intrinsics.X86.Avx2::Or(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
    System.Runtime.Intrinsics.Vector256`1<System.UInt64>)"),
  typeArguments := [], parameterCount := 2, returnsValue := true }
example : keeps call1 (.intrinsic (.avx2 .bor) 2) := by decide +kernel
example : runtimeModel {} .call call1.method ≠ some (.intrinsic (.avx2 .bor) 3) := by decide +kernel
example : refuses { call1 with method.hasThis := true } := by decide +kernel
example : refuses { call1 with target := .external "forged" } := by decide +kernel
private def call2 : CallSite := {
  declared := {
    convention := 0, returnType := vectorType "256",
    parameters := [vectorType "256", vectorType "256"] },
  method := {
    owner := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := name!"Xor",
    hasThis := false, genericArity := 0, returnType := vectorType "256",
    parameters := [vectorType "256", vectorType "256"] },
  name := "Xor",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
    System.Runtime.Intrinsics.X86.Avx2::Xor(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
    System.Runtime.Intrinsics.Vector256`1<System.UInt64>)"),
  typeArguments := [], parameterCount := 2, returnsValue := true }
example : keeps call2 (.intrinsic (.avx2 .bxor) 2) := by decide +kernel
example : runtimeModel {} .call call2.method ≠ some (.intrinsic (.avx2 .bxor) 3) := by
  decide +kernel
example : refuses { call2 with method.hasThis := true } := by decide +kernel
example : refuses { call2 with target := .external "forged" } := by decide +kernel
private def call3 : CallSite := {
  declared := {
    convention := 0, returnType := vectorType "256",
    parameters := [vectorType "256", vectorType "256"] },
  method := {
    owner := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := name!"AndNot",
    hasThis := false, genericArity := 0, returnType := vectorType "256",
    parameters := [vectorType "256", vectorType "256"] },
  name := "AndNot",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
    System.Runtime.Intrinsics.X86.Avx2::AndNot(\
    System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
    System.Runtime.Intrinsics.Vector256`1<System.UInt64>)"),
  typeArguments := [], parameterCount := 2, returnsValue := true }
example : keeps call3 (.intrinsic (.avx2 .andNot) 2) := by decide +kernel
example : runtimeModel {} .call call3.method ≠ some (.intrinsic (.avx2 .andNot) 3) := by
  decide +kernel
example : refuses { call3 with method.hasThis := true } := by decide +kernel
example : refuses { call3 with target := .external "forged" } := by decide +kernel
private def call4 : CallSite := {
  declared := {
    convention := 0, returnType := vectorType "256",
    parameters := [vectorType "256", vectorType "128"] },
  method := {
    owner := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := name!"ShiftLeftLogical",
    hasThis := false, genericArity := 0, returnType := vectorType "256",
    parameters := [vectorType "256", vectorType "128"] },
  name := "ShiftLeftLogical",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
    System.Runtime.Intrinsics.X86.Avx2::ShiftLeftLogical(\
    System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
    System.Runtime.Intrinsics.Vector128`1<System.UInt64>)"),
  typeArguments := [], parameterCount := 2, returnsValue := true }
example : keeps call4 (.intrinsic (.avx2 .shl64Count) 2) := by decide +kernel
example : runtimeModel {} .call call4.method ≠ some (.intrinsic (.avx2 .shl64Count) 3) := by
  decide +kernel
example : refuses { call4 with method.hasThis := true } := by decide +kernel
example : refuses { call4 with target := .external "forged" } := by decide +kernel
private def call5 : CallSite := {
  declared := {
    convention := 0, returnType := vectorType "256",
    parameters := [vectorType "256", vectorType "128"] },
  method := {
    owner := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := name!"ShiftRightLogical",
    hasThis := false, genericArity := 0, returnType := vectorType "256",
    parameters := [vectorType "256", vectorType "128"] },
  name := "ShiftRightLogical",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
    System.Runtime.Intrinsics.X86.Avx2::ShiftRightLogical(\
    System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
    System.Runtime.Intrinsics.Vector128`1<System.UInt64>)"),
  typeArguments := [], parameterCount := 2, returnsValue := true }
example : keeps call5 (.intrinsic (.avx2 .shr64Count) 2) := by decide +kernel
example : runtimeModel {} .call call5.method ≠ some (.intrinsic (.avx2 .shr64Count) 3) := by
  decide +kernel
example : refuses { call5 with method.hasThis := true } := by decide +kernel
example : refuses { call5 with target := .external "forged" } := by decide +kernel
private def call6 : CallSite := {
  declared := {
    convention := 0, returnType := vectorType "512",
    parameters := [vectorType "512", vectorType "512"] },
  method := {
    owner := .atom scope "System.Runtime.Intrinsics.X86.Avx512F", name := name!"CompareLessThan",
    hasThis := false, genericArity := 0, returnType := vectorType "512",
    parameters := [vectorType "512", vectorType "512"] },
  name := "CompareLessThan",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector512`1<System.UInt64> \
    System.Runtime.Intrinsics.X86.Avx512F::CompareLessThan(\
    System.Runtime.Intrinsics.Vector512`1<System.UInt64>,\
    System.Runtime.Intrinsics.Vector512`1<System.UInt64>)"),
  typeArguments := [], parameterCount := 2, returnsValue := true }
example : keeps call6 (.intrinsic (.avx512 .ltu512) 2) := by decide +kernel
example : runtimeModel {} .call call6.method ≠ some (.intrinsic (.avx512 .ltu512) 3) := by
  decide +kernel
example : refuses { call6 with method.hasThis := true } := by decide +kernel
example : refuses { call6 with target := .external "forged" } := by decide +kernel
private def call7 : CallSite := {
  declared := {
    convention := 0, returnType := vectorType "512",
    parameters := [vectorType "512", vectorType "512"] },
  method := {
    owner := .atom scope "System.Runtime.Intrinsics.X86.Avx512F",
    name := name!"CompareGreaterThan", hasThis := false, genericArity := 0,
    returnType := vectorType "512", parameters := [vectorType "512", vectorType "512"] },
  name := "CompareGreaterThan",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector512`1<System.UInt64> \
    System.Runtime.Intrinsics.X86.Avx512F::CompareGreaterThan(\
    System.Runtime.Intrinsics.Vector512`1<System.UInt64>,\
    System.Runtime.Intrinsics.Vector512`1<System.UInt64>)"),
  typeArguments := [], parameterCount := 2, returnsValue := true }
example : keeps call7 (.intrinsic (.avx512 .gtu512) 2) := by decide +kernel
example : runtimeModel {} .call call7.method ≠ some (.intrinsic (.avx512 .gtu512) 3) := by
  decide +kernel
example : refuses { call7 with method.hasThis := true } := by decide +kernel
example : refuses { call7 with target := .external "forged" } := by decide +kernel
private def call8 : CallSite := {
  declared := {
    convention := 0, returnType := .primitive .int32,
    parameters := [vectorType "512"] },
  method := {
    owner := .atom scope "System.Runtime.Intrinsics.X86.Avx512DQ", name := name!"MoveMask",
    hasThis := false, genericArity := 0, returnType := .primitive .int32,
    parameters := [vectorType "512"] },
  name := "MoveMask",
  target := .external (scope ++ "::System.Int32 System.Runtime.Intrinsics.X86.Avx512DQ::MoveMask(\
    System.Runtime.Intrinsics.Vector512`1<System.UInt64>)"),
  typeArguments := [], parameterCount := 1, returnsValue := true }
example : keeps call8 (.intrinsic (.avx512DQ .moveMask512) 1) := by decide +kernel
example : runtimeModel {} .call call8.method ≠ some (.intrinsic (.avx512DQ .moveMask512) 2) := by
  decide +kernel
example : refuses { call8 with method.hasThis := true } := by decide +kernel
example : refuses { call8 with target := .external "forged" } := by decide +kernel
private def call9 : CallSite := {
  declared := {
    convention := 0, returnType := vectorType "512",
    parameters := [vectorType "256", vectorType "256"] },
  method := {
    owner := .atom scope "System.Runtime.Intrinsics.Vector512", name := name!"Create",
    hasThis := false, genericArity := 0, returnType := vectorType "512",
    parameters := [vectorType "256", vectorType "256"] },
  name := "Create",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector512`1<System.UInt64> \
    System.Runtime.Intrinsics.Vector512::Create(\
    System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
    System.Runtime.Intrinsics.Vector256`1<System.UInt64>)"),
  typeArguments := [], parameterCount := 2, returnsValue := true }
example : runtimeModel {} .call call9.method = some (.intrinsic (.vector .combine256) 2) := by
  decide +kernel
example : runtimeCatalog.siteAgrees {} profile ⟨0, 40, .call call9⟩ (.call call9.method {}) := by
  decide +kernel
example : ¬ RuntimeModelsAgree (raw call9) [true]
    (body [.call call0.method]) := by decide +kernel
example : ¬ RuntimeModelsAgree (raw call9) [true]
    (body [.call { call9.method with parameters := call9.method.parameters ++ [call9.method.returnType] }]) := by decide +kernel
example : ¬ RuntimeModelsAgree (raw { call9 with method.hasThis := true }) [true]
    (body [.call call9.method]) := by decide +kernel
example : ¬ RuntimeModelsAgree (raw { call9 with target := .external "forged" }) [true]
    (body [.call call9.method]) := by decide +kernel
/-- The same vector equality declaration instantiated at the supplied owner element. -/
private def equalitySite (width : Nat) (element : PrimitiveType) : CallSite :=
  let head := s!"System.Runtime.Intrinsics.Vector{width}`1"
  let vector := TypeExpr.apply (.constructor scope head) (.primitive element)
  let openVector := TypeExpr.apply (.constructor scope head) (.ownerParameter 0)
  let boolean := TypeExpr.primitive .boolean
  let parameters := s!"{head}<!0>,{head}<!0>"
  let target := s!"{scope}::System.Boolean {head}<{element.display}>::op_Equality({parameters})"
  let method : MethodRef :=
    { owner := vector, name := name!"op_Equality", hasThis := false, genericArity := 0,
      returnType := boolean, parameters := [vector, vector] }
  let declared : OpenSignature :=
    { convention := 0, returnType := boolean, parameters := [openVector, openVector] }
  { method, declared,
    name := "op_Equality", target := .external target, returnsValue := true,
    parameterCount := 2, typeArguments := [] }

/-- Integer equality keeps its call and a floating element at the same declaration is refused. -/
theorem equalityElements :
    [128, 256, 512].all (fun width =>
      [PrimitiveType.byte, .int32, .uint32, .int64, .uint64, .single, .double].all fun element =>
        let site := equalitySite width element
        let expected := if element ∈ [.single, .double] then liveHoleAt 0 40
          else .ok [Instruction.call site.method {}]
        decide ((decodeRaw .scalar {} [] [true] (raw site) []).map Method.code =
          expected)) = true := by decide +kernel

#print axioms equalityElements

private def call10 : CallSite := {
  declared := {
    convention := 0, returnType := vectorType "128",
    parameters := [.primitive .uint64] },
  method := {
    owner := .atom scope "System.Runtime.Intrinsics.Vector128", name := name!"CreateScalarUnsafe",
    hasThis := false, genericArity := 0, returnType := vectorType "128",
    parameters := [.primitive .uint64] },
  name := "CreateScalarUnsafe",
  target := .external (scope ++ "::System.Runtime.Intrinsics.Vector128`1<System.UInt64> \
    System.Runtime.Intrinsics.Vector128::CreateScalarUnsafe(System.UInt64)"),
  typeArguments := [], parameterCount := 1, returnsValue := true }
-- The emitted call must name the member and instantiation of the original operand.
example : RuntimeModelsAgree (raw call10) [true] (body [.call call10.method {}]) := by
  decide +kernel
example : ¬ RuntimeModelsAgree (raw call10) [true]
    (body [.call call0.method]) := by decide +kernel
example : ¬ RuntimeModelsAgree (raw call0) [true]
    (body [.call createScalarUnsafeMethod]) := by decide +kernel
example : ¬ RuntimeModelsAgree (raw call10) [true]
    (body [.call getElement128Method]) := by decide +kernel
-- CreateScalar initializes the upper lane. Its checked call cannot replace CreateScalarUnsafe.
private def createScalar : MethodRef := { createScalarUnsafeMethod with name := name!"CreateScalar" }
example : call10.method = createScalarUnsafeMethod := by decide +kernel
example : runtimeModel {} .call createScalar = some (.intrinsic (.vector (.createScalar64 128)) 1) := rfl
example : ¬ ModelsAgree runtimeCatalog {} profile (raw call10) [true]
    [.call createScalar] := by decide +kernel
example : ¬ ModelsAgree runtimeCatalog {} profile
    (raw { call10 with target := .external "forged" }) [true]
    [.call createScalar] := by decide +kernel
example : refuses { call0 with parameterCount := 1 } := by decide +kernel
example : runtimeModel {} .call call0.method ≠ some (.intrinsic (.avx2 .bor) 2) := by decide +kernel
example : runtimeModel {} .call call4.method ≠ some (.intrinsic (.avx2 .shl64) 2) := by
  decide +kernel
example : runtimeModel {} .call call6.method ≠ some (.intrinsic (.avx512 .gtu512) 2) := by
  decide +kernel
example : refuses call0 (.scalar) := by decide +kernel
example : refuses call6 ({ profile with avx512F := false }) := by decide +kernel
example : refuses call8 ({ profile with avx512DQ := false }) := by decide +kernel
example : Intrinsic.available profile (.avx512 .ltu512) = true := by decide +kernel
example : Intrinsic.available profile (.avx512DQ .moveMask512) = true := by decide +kernel
-- A kept hardware call is refused at the evidence level under a profile lacking its feature.
example : RuntimeModelsAgree (raw call0) [true] (body [.call call0.method {}]) := by
  decide +kernel
example : ¬ RuntimeModelsAgree (raw call0) [true]
    { body [.call call0.method {}] with profile := .scalar } := by decide +kernel
example : ¬ RuntimeModelsAgree (raw call6) [true]
    { body [.call call6.method {}] with profile := { profile with avx512F := false } } := by
  decide +kernel
example : ¬ RuntimeModelsAgree (raw call8) [true]
    { body [.call call8.method {}] with profile := { profile with avx512DQ := false } } := by
  decide +kernel
-- A link at a hardware site keeps the feature requirement of the model the site resolves to.
example : RuntimeModelsAgree (raw call0) [true]
    { body [.call call0.method {}] with links := [(0, .direct 0)] } := by decide +kernel
example : ¬ RuntimeModelsAgree (raw call0) [true]
    { body [.call call0.method {}] with links := [(0, .direct 0)], profile := .scalar } := by
  decide +kernel

example : ¬ ({ profile with architecture := .arm64 } : FeatureProfile).Valid := by decide +kernel

private def vector128 : TypeExpr := .apply (.constructor scope "System.Runtime.Intrinsics.Vector128`1") (.primitive .uint64)
private def withLocal : RawMethod := { raw call10 with locals := [vector128], code := [] }
private def createsBody : Method := body [.call createScalarUnsafeMethod {}]

/-- Masking the creator removes the opaque local from the decoded frame. -/
theorem decoded_opaque_mask :
    let source := { raw call10 with locals := [vector128] }
    let slots := fun live => (Method.ofRaw? profile {} [] [live] source []).map
      Method.opaqueVectorLocals
    slots true = some [0] ∧ slots false = some [] := by
  exact ⟨rfl, rfl⟩
#print axioms decoded_opaque_mask
private def localBody : Method :=
  { createsBody with
      locals := [.unmodeled], localKinds := [.vector128], opaqueVectorLocals := [0] }
example : OpaqueLocalsValid withLocal localBody := by decide +kernel
example : OpaqueLocalsValid withLocal { localBody with code := [], opaqueVectorLocals := [] }
    := by decide +kernel
example : ¬ OpaqueLocalsValid withLocal { localBody with code := [] } := by decide +kernel
example : ¬ OpaqueLocalsValid withLocal { localBody with opaqueVectorLocals := [] }
    := by decide +kernel
example : ¬ OpaqueLocalsValid { withLocal with code := [⟨0, 18, .local 0⟩] } localBody
    := by decide +kernel
example : ¬ OpaqueLocalsValid { withLocal with code := [⟨0, 65037, .local 0⟩] } localBody
    := by decide +kernel
example : ¬ OpaqueLocalsValid withLocal
    { localBody with code := [.call createScalarUnsafeMethod {}, .ldloca 0] } := by
  decide +kernel
-- A different closed member cannot claim the opaque local of CreateScalarUnsafe.
example : ¬ OpaqueLocalsValid withLocal
    { localBody with code := [.call getElement128Method] } := by decide +kernel
example : ¬ OpaqueLocalsValid withLocal { localBody with localKinds := [.word64] }
    := by decide +kernel
example : ¬ OpaqueLocalsValid { withLocal with locals := [.primitive .uint64] } localBody := by
  decide +kernel

example : evalIntrinsic (.avx2 .andNot) [.v256 1, .v256 3] = some (.v256 2) := by decide +kernel
example : evalIntrinsic (.vector .combine256) [.v256 1, .v256 2] = some (.v512 ((2 : BitVec 256) ++ (1 : BitVec 256))) := rfl
example : evalIntrinsic (.vector .createScalarUnsafe64) [.i64 7] = some (.v128Low64 7) := rfl
example : evalIntrinsic (.vector (.extract64 128)) [.v128Low64 7, .i32 0] = some (.i64 7) := rfl
example : Safety.checkedIntrinsic (.vector (.extract64 128)) [.v128Low64 7, .i32 1] =
    .error (.unsupported "Intrinsic observes unspecified vector bits") := rfl
example : Safety.checkedIntrinsic (.vector (.equalsAll 128)) [.v128Low64 7, .v128 7] =
    .error (.unsupported "Intrinsic observes unspecified vector bits") := rfl
/-- Whole-vector bitwise operations cannot turn unspecified lanes into concrete results. -/
theorem unspecified_bitwise :
    Safety.checkedIntrinsic (.vector (.band 128)) [.v128Low64 7, .v128 0] =
      .error (.unsupported "Intrinsic observes unspecified vector bits") ∧
    Safety.checkedIntrinsic (.vector (.bor 128)) [.v128 0, .v128Low64 7] =
      .error (.unsupported "Intrinsic observes unspecified vector bits") ∧
    Safety.checkedIntrinsic (.vector (.bxor 128)) [.v128Low64 7, .v128Low64 7] =
      .error (.unsupported "Intrinsic observes unspecified vector bits") ∧
    Safety.checkedIntrinsic (.vector (.bnot 128)) [.v128Low64 7] =
      .error (.unsupported "Intrinsic observes unspecified vector bits") := ⟨rfl, rfl, rfl, rfl⟩
#print axioms unspecified_bitwise
example : Safety.bitcastValue .vector128 .vector128 (.v128Low64 7) =
    .error (.unsupported "Bitcast observes unspecified vector bits") := rfl
example (memory : Safety.Memory) : Safety.storeLocal memory (.opaque128 none) (.scalar (.v128Low64 7)) =
    .ok (.opaque128 (some (.low64 7)), memory) := rfl
example (memory : Safety.Memory) :
    Safety.instruction .ceq [.scalar (.v128Low64 7), .scalar (.v128Low64 7)] memory =
    .error (.unsupported "Instruction observes unspecified vector bits") := rfl

theorem unspecified_return (body : Method) (memory : Safety.Memory) (frame : Safety.Frame) :
    Safety.step body .ret 0 [] frame [.scalar (.v128Low64 7)] memory =
      .error (.unsupported "Instruction observes unspecified vector bits") := rfl
#print axioms unspecified_return

theorem unspecified_call (body : Method) (link : Link) (linked : body.linkAt 0 = some link)
    (memory : Safety.Memory) (frame : Safety.Frame) :
    Safety.step body (.call (Tests.callee 2)) 0 [] frame [.scalar (.i64 0), .scalar (.v128Low64 7)]
      memory =
      .error (.unsupported "Instruction observes unspecified vector bits") := by
  simp only [Safety.step, Safety.observerCount, linked]
  rfl
#print axioms unspecified_call

theorem unspecified_call_rest (memory : Safety.Memory) (frame : Safety.Frame) :
    Safety.step { body [.call (Tests.callee 1)] with links := [(0, .direct 1)] }
      (.call (Tests.callee 1)) 0 [] frame
      [.scalar (.i64 3), .scalar (.v128Low64 7)] memory =
      .ok (.call 1 [.scalar (.i64 3)] [.scalar (.v128Low64 7)] memory) := rfl
#print axioms unspecified_call_rest

theorem defined_vector_return (memory : Safety.Memory) (frame : Safety.Frame) (bits : BitVec 128) :
    Safety.step { code := [], locals := [], returnsValue := true } .ret 0 [] frame [.scalar (.v128 bits)] memory =
      .ok (.returned [.scalar (.v128 bits)] memory) := rfl
#print axioms defined_vector_return

theorem unspecified_constructor (body : Method) (memory : Safety.Memory) (frame : Safety.Frame) :
    Safety.step body (.newobj (.arity 1)) 0 [] frame [.scalar (.v128Low64 7)] memory =
      .error (.unsupported "Instruction observes unspecified vector bits") := rfl
#print axioms unspecified_constructor

theorem unspecified_store (memory : Safety.Memory) (destination : Safety.ManagedReference) :
    Safety.storeValue memory destination (.v128Low64 7) =
      .error (.unsupported "Store observes unspecified vector bytes") := rfl
#print axioms unspecified_store
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 0) 3 = 1
    := by decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 0) 3 = 1
    := by decide +kernel
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 1) 3 = 2
    := by decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 1) 3 = 0
    := by decide +kernel
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 63) 3 = 9223372036854775808 := by
  decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 63) 3 = 0
    := by decide +kernel
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 64) 3 = 0
    := by decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 64) 3 = 0
    := by decide +kernel
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 255) 3 = 0
    := by decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 255) 3 = 0
    := by decide +kernel
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 256) 3 = 0
    := by decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 256) 3 = 0
    := by decide +kernel
example : Vector.lane64 (Vector.shiftLeftCount64 (Vector.pack256 1 1 1 1) 18446744073709551615) 3 = 0 := by
  decide +kernel
example : Vector.lane64 (Vector.shiftRightCount64 (Vector.pack256 1 1 1 1) 18446744073709551615) 3 = 0 := by
  decide +kernel
example : Vector.moveMask512 (Vector.pack512 9223372036854775808 0 0 0 0 0 0 0) = 1
    := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 9223372036854775808 0 0 0 0 0 0) = 2
    := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 0 9223372036854775808 0 0 0 0 0) = 4
    := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 0 0 9223372036854775808 0 0 0 0) = 8
    := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 0 0 0 9223372036854775808 0 0 0) = 16
    := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 0 0 0 0 9223372036854775808 0 0) = 32
    := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 0 0 0 0 0 9223372036854775808 0) = 64
    := by decide +kernel
example : Vector.moveMask512 (Vector.pack512 0 0 0 0 0 0 0 9223372036854775808) = 128
    := by decide +kernel
example : evalIntrinsic (.avx512 .ltu512)
    [.v512 (Vector.pack512 9223372036854775808 1 0 0 0 0 0 0),
     .v512 (Vector.pack512 1 1 0 0 0 0 0 0)] = some (.v512 0) := by decide +kernel

example : keeps {
    declared := {
      convention := 0, returnType := vectorType "256",
      parameters := [vectorType "256", .primitive .byte] },
    method := {
      owner := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := name!"ShiftLeftLogical",
      hasThis := false, genericArity := 0, returnType := vectorType "256",
      parameters := [vectorType "256", .primitive .byte] },
    name := "ShiftLeftLogical",
    target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
      System.Runtime.Intrinsics.X86.Avx2::ShiftLeftLogical(\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Byte)"),
    typeArguments := [], parameterCount := 2, returnsValue := true }
    (.intrinsic (.avx2 .shl64) 2) := by decide +kernel

example : keeps {
    declared := {
      convention := 0, returnType := vectorType "256",
      parameters := [vectorType "256", .primitive .byte] },
    method := {
      owner := .atom scope "System.Runtime.Intrinsics.X86.Avx2", name := name!"ShiftRightLogical",
      hasThis := false, genericArity := 0, returnType := vectorType "256",
      parameters := [vectorType "256", .primitive .byte] },
    name := "ShiftRightLogical",
    target := .external (scope ++ "::System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
      System.Runtime.Intrinsics.X86.Avx2::ShiftRightLogical(\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Byte)"),
    typeArguments := [], parameterCount := 2, returnsValue := true }
    (.intrinsic (.avx2 .shr64) 2) := by decide +kernel

example : keeps {
    declared := {
      convention := 0, returnType := .primitive .int32,
      parameters := [vectorType "256"] },
    method := {
      owner := .atom scope "System.Runtime.Intrinsics.X86.Avx512DQ", name := name!"MoveMask",
      hasThis := false, genericArity := 0, returnType := .primitive .int32,
      parameters := [vectorType "256"] },
    name := "MoveMask",
    target := .external (scope ++ "::System.Int32 System.Runtime.Intrinsics.X86.Avx512DQ::\
      MoveMask(System.Runtime.Intrinsics.Vector256`1<System.UInt64>)"),
    typeArguments := [], parameterCount := 1, returnsValue := true }
    (.intrinsic (.avx512DQ .moveMask64) 1) := by decide +kernel


/-- A method using the specified type at its only instruction. -/
private def objectBody (opcode : Nat) (type : TypeExpr) : RawMethod :=
  { raw call0 with code := [⟨0, opcode, .type type⟩] }

/-- Object admission checks vector storage on each profile and refuses malformed evidence. -/
theorem init_vector_admission :
    let unsigned := vectorType "128"
    let emitted := body [.initobj unsigned]
    let valid := fun operand => decide (ObjectOperandsValid (objectBody 0xfe15 operand)
      [true] emitted)
    let malformed := fun head element => TypeExpr.apply head element
    ["128", "256", "512"].all (fun width => valid (vectorType width)) &&
      decide (ObjectOperandsValid (objectBody 0xfe15 unsigned) [true]
        { emitted with profile := .scalar }) &&
      decide (ObjectOperandsValid (objectBody 0xfe15 unsigned) [true]
        { emitted with profile := { architecture := .arm64 } }) &&
      !(valid (malformed (.constructor "forged" "System.Runtime.Intrinsics.Vector128`1")
        (.primitive .uint64))) &&
      !(valid (malformed (.constructor scope "System.Runtime.Intrinsics.Vector128`1")
        (.atom "forged" "System.UInt64"))) &&
      !(valid (malformed (.constructor scope "System.Runtime.Intrinsics.Vector128`1")
        (.primitive .int16))) &&
      !(valid (vectorType "64")) &&
      !decide (ObjectOperandsValid (objectBody 0xfe15 unsigned) [true]
        { emitted with profile := { nativeWidth := 32 } }) &&
      !decide (ObjectOperandsValid (objectBody 0xfe15 unsigned) [] emitted) &&
      !decide (ObjectOperandsValid (objectBody 0xfe15 unsigned) [true] (body [])) := by
  decide +kernel
#print axioms init_vector_admission

/-- An enum-span copy reads its own direct home and clears the reference flag on the value. -/
theorem enum_span_copy :
    let element := TypeExpr.enum (Tests.enumIdentity "Signed8") (.primitive .sbyte)
    let span := TypeExpr.apply (.constructor runtimeScope "System.Span`1") element
    let load := RawInstruction.mk 0 2 .none
    let copy := RawInstruction.mk 1 0x71 (.type span)
    let input := { raw call0 with parameters := [.byref span], code := [load, copy] }
    let emitted := body [.ldarg 0, .ldobj span]
    let kind := ScalarKind.enumSpan (.enumeration (Tests.enumIdentity "Signed8") .signed8) true
    ObjectOperandsValid input [true, true] emitted ∧
      scalarTransfer input copy [kind true] = some [kind false] ∧
      scalarTransfer input copy [kind false] = none ∧
      ¬ ObjectOperandsValid { input with parameters := [.byref (.apply
        (.constructor runtimeScope "System.Span`1") (.primitive .int32))] }
        [true, true] emitted ∧
      ¬ ObjectOperandsValid { input with code := [load, ⟨1, 0, .none⟩, copy] }
        [true, true, true] (body [.ldarg 0, .nop, .ldobj span]) ∧
      ¬ ObjectOperandsValid { input with code := [load, copy, ⟨2, 43, .target 1⟩] }
        [true, true, false] (body [.ldarg 0, .ldobj span, .unadmitted 43]) := by decide +kernel
#print axioms enum_span_copy

/-- A valid load of a span does not admit a later sizeof of the same span type. -/
theorem span_load_then_size_refused :
    let span := TypeExpr.apply (.constructor runtimeScope "System.Span`1")
      (.primitive .int32)
    let source := { raw call0 with
      parameters := [.byref span]
      code := [⟨0, 2, .none⟩, ⟨1, 0x71, .type span⟩] }
    let input := { source with
      returnType := .primitive .int32
      code := source.code ++ [⟨6, 38, .none⟩, ⟨7, 0xfe1c, .type span⟩, ⟨13, 42, .none⟩] }
    let emitted := body [.ldarg 0, .ldobj span, .pop, .sizeof span, .ret]
    ObjectOperandsValid source [true, true] (body [.ldarg 0, .ldobj span]) ∧
      ¬ ObjectOperandsValid input [true, true, true, true, true] emitted := by decide +kernel
#print axioms span_load_then_size_refused

/-- A literal site binds both opcode and token, including between two supported vectors. -/
theorem init_vector_binding :
    let target := vectorType "128"
    let raw := RawInstruction.mk 0 0xfe15 (.type target)
    [Instruction.nop, .initobj (vectorType "256"), .initobj (vectorType "512"),
      .initobj (.primitive .uint64), .ldobj target].all fun emitted =>
        !scalarEmissionMatches none none raw [] emitted := by decide +kernel
#print axioms init_vector_binding

/-- Floating-point loads, class sizes and span stores fail admission. -/
theorem object_shape_refusals :
    let span := TypeExpr.apply (.constructor runtimeScope "System.Span`1")
      (.primitive .int32)
    let double := TypeExpr.primitive .double
    let input := fun opcode type => objectBody opcode type
    ¬ ObjectOperandsValid (input 0x71 double) [true] (body [.ldobj double]) ∧
      ¬ ObjectOperandsValid (input 0xfe1c (.object runtimeScope "System.Object")) [true]
        (body [.sizeof (.object runtimeScope "System.Object")]) ∧
      ¬ ObjectOperandsValid (input 0x81 span) [true] (body [.stobj span]) := by decide +kernel
#print axioms object_shape_refusals

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
example : Safety.checkedIntrinsic (.scalar (.leadingZeroCount 64 .word32)) [.v128Low64 1] =
    .error (.unsupported "Intrinsic observes unspecified vector bits") := rfl

/-- Family membership and model selection use the typed reference for both target spellings. -/
theorem typed_family :
    let crossed := { call10 with target := call0.target }
    exactCallFamily call0.method = true ∧ exactCallFamily crossed.method = false ∧
      exactIntrinsic crossed.method = none ∧
      exactIntrinsic call0.method = some (.intrinsic (.avx2 .band) 2) := by decide +kernel

#print axioms typed_family

/-- The model row compares the complete external identity and the raw metadata name. -/
theorem exact_identity_boundaries :
    refuses { call0 with name := "Andλ" } ∧ refuses { call0 with target := .external scope } ∧
      refuses { call0 with target := .external (scope ++ "::λ") } := by decide +kernel

#print axioms exact_identity_boundaries

/-- A dead call is its opcode's hole even if the closed signature or opcode is unmodelled. -/
theorem unreachable_call :
    let source := { raw call0 with code := [⟨0, 111, .call { call0 with name := "Other" }⟩] }
    (decodeRaw profile {} [] [false] source []).map Method.code = .ok [.unadmitted 111] ∧
      (decodeRaw profile {} [] [true] source []).map Method.code = liveHoleAt 0 111 := by
  decide +kernel

#print axioms unreachable_call

/-- Decoding a nop cannot introduce a call to an intrinsic. -/
theorem nop_excludes_intrinsic_call :
    let source := { raw call0 with code := [⟨0, 0, .none⟩] }
    methodCode profile {} [] [true] source ≠ [.call call0.method] := by decide +kernel

#print axioms nop_excludes_intrinsic_call

/-- Model agreement requires the same number of raw instructions, live flags and emissions. -/
theorem exact_call_lengths :
    (¬ RuntimeModelsAgree (raw call0) [] (body [.call call0.method {}])) ∧
      (¬ RuntimeModelsAgree (raw call0) [false] (body [])) := by decide +kernel

#print axioms exact_call_lengths

/-! Generated runtime comparisons apply the broadcast execution facts to extracted bodies, which
    carry their declared signature and the extraction's layouts. Each example states a body in
    the emitted form and proves its claim with the term the fixture generator writes. -/

/-- The declared signature of a `(ulong, ulong) -> ulong` method. -/
private def wordSignature : DeclaredSignature :=
  { parameters := [.primitive .uint64,
      .primitive .uint64],
    returnType := .primitive .uint64 }

/-- A layout environment with one entry, as an extraction that reads a struct records. -/
private def emittedEnvironment : LayoutEnvironment := { layouts := #[⟨⟨4, []⟩, 4⟩] }

/-- `Avx2.And` of two broadcasts, then a call for lane 0, in the form an extraction emits. -/
private def emittedAnd : Method :=
  { profile := profile, returnsValue := true, locals := [], localKinds := [],
    opaqueVectorLocals := [], parameterHomes := [], staticSites := [],
    declared := wordSignature, environment := emittedEnvironment, links := [],
    code := [.ldarg 0, .call broadcast256Method {}, .ldarg 1,
      .call broadcast256Method {}, .call call0.method {}, .ldc_i4 0,
      .call getElement256Method {}, .ret] }

example : (Safety.invoke [emittedAnd] 256 0 [.scalar (.i64 13), .scalar (.i64 6)]
    Safety.Memory.empty).map Prod.snd = .ok [.scalar (.i64 4)] := by
  exact congrArg (Except.map Prod.snd) (Safety.invoke_broadcastBinary_word profile .band
    (reference := call0.method) 0 13 6 4
    Safety.Memory.empty rfl rfl rfl rfl rfl (by decide) (Safety.checked_broadcast_and 13 6))

/-- `Avx2.ShiftLeftLogical` of a broadcast by a full-width count, in the emitted form. -/
private def emittedShift : Method :=
  { profile := profile, returnsValue := true, locals := [.v128 0], localKinds := [.vector128],
    opaqueVectorLocals := [0], parameterHomes := [], staticSites := [],
    declared := wordSignature, environment := emittedEnvironment, links := [],
    code := [.ldarg 1, .call createScalarUnsafeMethod {}, .stloc 0, .ldarg 0,
      .call broadcast256Method {}, .ldloc 0, .call call4.method {},
      .ldc_i4 0, .call getElement256Method {}, .ret] }

example : (Safety.invoke [emittedShift] 256 0 [.scalar (.i64 1), .scalar (.i64 63)]
    Safety.Memory.empty).map Prod.snd = .ok [.scalar (.i64 9223372036854775808)] := by
  exact congrArg (Except.map Prod.snd) (Safety.invoke_broadcastShift profile .shl64Count
    (reference := call4.method) 0 1 63
    9223372036854775808 Safety.Memory.empty rfl rfl rfl rfl rfl (by decide)
    (Safety.checked_broadcast_shiftLeft 1 63))

end Tests.ExactIntrinsics
