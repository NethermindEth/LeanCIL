import CIL.Extraction.WideArithmetic

/-! Hardware overloads bind the closed member and its open declaration to one checked intrinsic. -/

namespace CIL.Extraction

/-- A declaration can use a runtime primitive, a vector, its generic element, or a pair result. -/
private inductive HWType where
  | word (name : String)
  | vector (width : Nat) (element : HWType)
  | element
  | pair
  deriving DecidableEq

/-- The structured type and Cecil spelling of a signature component. -/
private abbrev Operand := TypeExpr × String

/-- The checked scope and metadata name of a vector constructor. -/
private def vectorHead (width : Nat) := s!"System.Runtime.Intrinsics.Vector{width}`1"

/-- A declaration component retains its type variable in the external identity. -/
private def HWType.operand (argument : Operand) (result : TypeExpr) : HWType → Operand
  | .element => argument
  | .pair => (result, "System.ValueTuple`2<System.UInt64,System.UInt64>")
  | .word name => (.atom runtimeScope ("System." ++ name), "System." ++ name)
  | .vector width scalar =>
    let (type, name) := scalar.operand argument result
    let head := vectorHead width
    (.apply (.constructor intrinsicsScope head) type, s!"{head}<{name}>")

/-- The allowed instantiations of an open declaration determine its operation. -/
private structure HardwareRow where
  result : HWType
  parameters : List HWType
  operation : String → Intrinsic
  elements : List String := []

/-- A signature with one operation at every admitted element. -/
private def signature (result : HWType) (parameters : List HWType) (operation : Intrinsic)
    (elements : List String := []) : HardwareRow :=
  ⟨result, parameters, fun _ => operation, elements⟩

/-- One opcode, owner and metadata name reserves every overload in its slot. -/
private structure HardwareSlot where
  owner : String
  key : MetadataName
  name : String
  rows : List HardwareRow
  genericOwner : Bool := false

/-- The full owner spelling includes its namespace and any generic arity. -/
private def HardwareSlot.fullOwner (slot : HardwareSlot) :=
  "System.Runtime.Intrinsics." ++ slot.owner

/-- The exact declaring type or open vector constructor used for table lookup. -/
private def HardwareSlot.head (slot : HardwareSlot) : TypeExpr :=
  if slot.genericOwner then .constructor intrinsicsScope slot.fullOwner
  else .atom intrinsicsScope slot.fullOwner

/-- A static member of a vector constructor carries its element in the declaring type. -/
private def HardwareSlot.matches (slot : HardwareSlot) (method : MethodRef) : Bool :=
  method.name == slot.key && if slot.genericOwner then
    match method.owner with
    | .apply head _ => head == slot.head
    | _ => false
  else method.owner == slot.head

/-- The closed signature selects a primitive argument from exactly the declared binder. -/
private def HardwareRow.argument (row : HardwareRow) (slot : HardwareSlot) (method : MethodRef) :
    Option Operand := do
  guard (slot.matches method && !method.hasThis)
  let generic := !slot.genericOwner && !row.elements.isEmpty
  guard (method.genericArity == (if generic then 1 else 0))
  let type ← if generic then
      match method.methodArguments with
      | [argument] => some argument
      | _ => none
    else do
      guard method.methodArguments.isEmpty
      if !slot.genericOwner then pure TypeExpr.void
      else match method.owner with
        | .apply _ element => pure element
        | _ => none
  if row.elements.isEmpty then return (.void, "")
  let .atom scope name := type | none
  guard (scope == runtimeScope && row.elements.contains name)
  return (type, name)

/-- An overload checks the full closed signature before assigning an intrinsic and arity. -/
private def HardwareRow.accepts (row : HardwareRow) (slot : HardwareSlot) (method : MethodRef) :
    Bool :=
  (row.argument slot method).any fun argument =>
    let operand := HWType.operand argument method.returnType
    method.parameters == row.parameters.map (fun type => (operand type).1) &&
      method.returnType == (operand row.result).1 &&
      (row.result != .pair || (match method.returnType with
        | .aggregate identity _ => identity == integerPairIdentity "System.UInt64"
        | _ => false))

/-- The open signature and external identity distinguish owner and method binders. -/
private def HardwareRow.binding (row : HardwareRow) (slot : HardwareSlot) : ModelOperand :=
  let generic := !slot.genericOwner && !row.elements.isEmpty
  let binder : Operand := if slot.genericOwner then (.ownerParameter 0, "!0")
    else (.parameter 0, "!!0")
  let declared (method : MethodRef) : OpenSignature :=
    let operand := HWType.operand binder method.returnType
    { convention := if generic then 16 else 0, returnType := (operand row.result).1,
      parameters := row.parameters.map (fun type => (operand type).1) }
  .external declared slot.name fun method => do
    let argument ← row.argument slot method
    let owner := if slot.genericOwner then s!"{slot.fullOwner}<{argument.2}>" else slot.fullOwner
    let operand := HWType.operand binder method.returnType
    let names := ",".intercalate (row.parameters.map (fun type => (operand type).2))
    return s!"{intrinsicsScope}::{(operand row.result).2} {owner}::{slot.name}({names})"

/-- Only a checked pair layout can receive the tuple produced by hardware division. -/
private def HardwareRow.model (row : HardwareRow) (slot : HardwareSlot) (reader : CallLayouts)
    (method : MethodRef) : Option RuntimeModel := do
  let argument ← row.argument slot method
  guard (row.result != .pair || integerPairResult reader method.returnType "System.UInt64" 8)
  return .intrinsic (row.operation argument.2) row.parameters.length

/-- The row selected by the closed types also supplies the external operand check. -/
private def HardwareSlot.entry (slot : HardwareSlot) : ModelEntry :=
  { opcode := .call, owner := slot.head, name := slot.key, ownsName := true,
    overloads := slot.rows.map fun row =>
      { operand := row.binding slot, accepts := row.accepts slot, resolve := row.model slot } }

/-- The UInt64 hardware signature component. -/
private def u64 := HWType.word "UInt64"

/-- The Int64 hardware signature component. -/
private def i64 := HWType.word "Int64"

/-- The UInt32 hardware signature component. -/
private def u32 := HWType.word "UInt32"

/-- The Int32 hardware signature component. -/
private def i32 := HWType.word "Int32"

/-- The Byte hardware signature component. -/
private def u8 := HWType.word "Byte"

/-- The Boolean hardware signature component. -/
private def boolean := HWType.word "Boolean"

/-- The Single hardware signature component. -/
private def f32 := HWType.word "Single"

/-- The Double hardware signature component. -/
private def f64 := HWType.word "Double"

/-- The element type determines the 128-bit vector signature. -/
private def v128 := HWType.vector 128

/-- The element type determines the 256-bit vector signature. -/
private def v256 := HWType.vector 256

/-- The element type determines the 512-bit vector signature. -/
private def v512 := HWType.vector 512

/-- The fixed declarations of `X86.Avx2.And`. -/
private def x86Avx2And : HardwareSlot :=
  ⟨"X86.Avx2", name!"And", "And",
    [signature (v256 u64) [v256 u64, v256 u64] (.avx2 .band)], false⟩

/-- The fixed declarations of `X86.Avx2.Or`. -/
private def x86Avx2Or : HardwareSlot :=
  ⟨"X86.Avx2", name!"Or", "Or",
    [signature (v256 u64) [v256 u64, v256 u64] (.avx2 .bor)], false⟩

/-- The fixed declarations of `X86.Avx2.Xor`. -/
private def x86Avx2Xor : HardwareSlot :=
  ⟨"X86.Avx2", name!"Xor", "Xor",
    [signature (v256 u64) [v256 u64, v256 u64] (.avx2 .bxor)], false⟩

/-- The fixed declarations of `X86.Avx2.AndNot`. -/
private def x86Avx2AndNot : HardwareSlot :=
  ⟨"X86.Avx2", name!"AndNot", "AndNot",
    [signature (v256 u64) [v256 u64, v256 u64] (.avx2 .andNot)], false⟩

/-- The fixed declarations of `X86.Avx2.ShiftLeftLogical`. -/
private def x86Avx2ShiftLeftLogical : HardwareSlot :=
  ⟨"X86.Avx2", name!"ShiftLeftLogical", "ShiftLeftLogical",
    [signature (v256 u64) [v256 u64, v128 u64] (.avx2 .shl64Count),
     signature (v256 u64) [v256 u64, u8] (.avx2 .shl64)], false⟩

/-- The fixed declarations of `X86.Avx2.ShiftRightLogical`. -/
private def x86Avx2ShiftRightLogical : HardwareSlot :=
  ⟨"X86.Avx2", name!"ShiftRightLogical", "ShiftRightLogical",
    [signature (v256 u64) [v256 u64, v128 u64] (.avx2 .shr64Count),
     signature (v256 u64) [v256 u64, u8] (.avx2 .shr64)], false⟩

/-- The fixed declarations of `X86.Avx512F.CompareLessThan`. -/
private def x86Avx512FCompareLessThan : HardwareSlot :=
  ⟨"X86.Avx512F", name!"CompareLessThan", "CompareLessThan",
    [signature (v512 u64) [v512 u64, v512 u64] (.avx512 .ltu512)], false⟩

/-- The fixed declarations of `X86.Avx512F.CompareGreaterThan`. -/
private def x86Avx512FCompareGreaterThan : HardwareSlot :=
  ⟨"X86.Avx512F", name!"CompareGreaterThan", "CompareGreaterThan",
    [signature (v512 u64) [v512 u64, v512 u64] (.avx512 .gtu512)], false⟩

/-- The fixed declarations of `X86.Avx512DQ.MoveMask`. -/
private def x86Avx512DQMoveMask : HardwareSlot :=
  ⟨"X86.Avx512DQ", name!"MoveMask", "MoveMask",
    [signature i32 [v512 u64] (.avx512DQ .moveMask512),
     signature i32 [v256 u64] (.avx512DQ .moveMask64)], false⟩

/-- The fixed declarations of `Arm.AdvSimd.ReverseElement8`. -/
private def armAdvSimdReverseElement8 : HardwareSlot :=
  ⟨"Arm.AdvSimd", name!"ReverseElement8", "ReverseElement8",
    [signature (v128 u64) [v128 u64] (.advSimd .reverseElement8)], false⟩

/-- The fixed declarations of `X86.Sse2.Multiply`. -/
private def x86Sse2Multiply : HardwareSlot :=
  ⟨"X86.Sse2", name!"Multiply", "Multiply",
    [signature (v128 u64) [v128 u32, v128 u32] (.sse .multiplyEven32)], false⟩

/-- The fixed declarations of `X86.Ssse3.Shuffle`. -/
private def x86Ssse3Shuffle : HardwareSlot :=
  ⟨"X86.Ssse3", name!"Shuffle", "Shuffle",
    [signature (v128 u8) [v128 u8, v128 u8] (.sse .shuffleBytes)], false⟩

/-- The fixed declarations of `X86.Avx2.Shuffle`. -/
private def x86Avx2Shuffle : HardwareSlot :=
  ⟨"X86.Avx2", name!"Shuffle", "Shuffle",
    [signature (v256 u8) [v256 u8, v256 u8] (.avx2 .shuffleBytes)], false⟩

/-- The fixed declarations of `X86.Aes.Encrypt`. -/
private def x86AesEncrypt : HardwareSlot :=
  ⟨"X86.Aes", name!"Encrypt", "Encrypt",
    [signature (v128 u8) [v128 u8, v128 u8] (.aes .encrypt)], false⟩

/-- The fixed declarations of `Arm.Aes.Encrypt`. -/
private def armAesEncrypt : HardwareSlot :=
  ⟨"Arm.Aes", name!"Encrypt", "Encrypt",
    [signature (v128 u8) [v128 u8, v128 u8] (.armAes .encrypt)], false⟩

/-- The fixed declarations of `Arm.Aes.MixColumns`. -/
private def armAesMixColumns : HardwareSlot :=
  ⟨"Arm.Aes", name!"MixColumns", "MixColumns",
    [signature (v128 u8) [v128 u8] (.armAes .mixColumns)], false⟩

/-- The fixed declarations of `X86.Avx512F/VL.PermuteVar4x64x2`. -/
private def x86Avx512FVLPermuteVar4x64x2 : HardwareSlot :=
  ⟨"X86.Avx512F/VL", name!"PermuteVar4x64x2", "PermuteVar4x64x2",
    [signature (v256 u64) [v256 u64, v256 u64, v256 u64] (.avx512 .permuteVar4x64x2)], false⟩

/-- The exact machine hardware slots. -/
private def exactMachineSlots : List HardwareSlot := [
  x86Avx2And,
  x86Avx2Or,
  x86Avx2Xor,
  x86Avx2AndNot,
  x86Avx2ShiftLeftLogical,
  x86Avx2ShiftRightLogical,
  x86Avx512FCompareLessThan,
  x86Avx512FCompareGreaterThan,
  x86Avx512DQMoveMask,
  armAdvSimdReverseElement8,
  x86Sse2Multiply,
  x86Ssse3Shuffle,
  x86Avx2Shuffle,
  x86AesEncrypt,
  armAesEncrypt,
  armAesMixColumns,
  x86Avx512FVLPermuteVar4x64x2]


/-- The fixed declarations of `Arm.AdvSimd.ExtractVector128`. -/
private def armAdvSimdExtractVector128 : HardwareSlot :=
  ⟨"Arm.AdvSimd", name!"ExtractVector128", "ExtractVector128",
    [signature (v128 u64) [v128 u64, v128 u64, u8] (.advSimd .extract64)], false⟩

/-- The fixed declarations of `X86.Sse2.ShiftLeftLogical128BitLane`. -/
private def x86Sse2ShiftLeftLogical128BitLane : HardwareSlot :=
  ⟨"X86.Sse2", name!"ShiftLeftLogical128BitLane", "ShiftLeftLogical128BitLane",
    [signature (v128 u64) [v128 u64, u8] (.sse .shiftLeftBytes)], false⟩

/-- The fixed declarations of `X86.Ssse3.AlignRight`. -/
private def x86Ssse3AlignRight : HardwareSlot :=
  ⟨"X86.Ssse3", name!"AlignRight", "AlignRight",
    [signature (v128 u8) [v128 u8, v128 u8, u8] (.sse .alignBytes)], false⟩

/-- The fixed declarations of `X86.Avx2.Permute4x64`. -/
private def x86Avx2Permute4x64 : HardwareSlot :=
  ⟨"X86.Avx2", name!"Permute4x64", "Permute4x64",
    [signature (v256 u64) [v256 u64, u8] (.avx2 .permute4x64)], false⟩

/-- The fixed declarations of `X86.Avx2.Blend`. -/
private def x86Avx2Blend : HardwareSlot :=
  ⟨"X86.Avx2", name!"Blend", "Blend",
    [signature (v256 u32) [v256 u32, v256 u32, u8] (.avx2 .blend32),
     signature (v256 i32) [v256 i32, v256 i32, u8] (.avx2 .blend32)], false⟩

/-- The fixed declarations of `X86.Avx2.Add`. -/
private def x86Avx2Add : HardwareSlot :=
  ⟨"X86.Avx2", name!"Add", "Add",
    [signature (v256 u64) [v256 u64, v256 u64] (.avx2 .add64)], false⟩

/-- The fixed declarations of `X86.Avx2.CompareEqual`. -/
private def x86Avx2CompareEqual : HardwareSlot :=
  ⟨"X86.Avx2", name!"CompareEqual", "CompareEqual",
    [signature (v256 u64) [v256 u64, v256 u64] (.avx2 .eq64)], false⟩

/-- The fixed declarations of `X86.Avx2.CompareGreaterThan`. -/
private def x86Avx2CompareGreaterThan : HardwareSlot :=
  ⟨"X86.Avx2", name!"CompareGreaterThan", "CompareGreaterThan",
    [signature (v256 i64) [v256 i64, v256 i64] (.avx2 .signedgt64)], false⟩

/-- The fixed declarations of `X86.Avx2.Multiply`. -/
private def x86Avx2Multiply : HardwareSlot :=
  ⟨"X86.Avx2", name!"Multiply", "Multiply",
    [signature (v256 u64) [v256 u32, v256 u32] (.avx2 .multiplyEven32)], false⟩

/-- The fixed declarations of `X86.Avx512F/VL.AlignRight64`. -/
private def x86Avx512FVLAlignRight64 : HardwareSlot :=
  ⟨"X86.Avx512F/VL", name!"AlignRight64", "AlignRight64",
    [signature (v256 u64) [v256 u64, v256 u64, u8] (.avx512 .alignRight64)], false⟩

/-- The fixed declarations of `X86.Avx512F/VL.TernaryLogic`. -/
private def x86Avx512FVLTernaryLogic : HardwareSlot :=
  ⟨"X86.Avx512F/VL", name!"TernaryLogic", "TernaryLogic",
    [signature (v256 u64) [v256 u64, v256 u64, v256 u64, u8] (.avx512 .ternaryLogic)], false⟩

/-- The fixed declarations of `X86.Avx512F/VL.CompareLessThan`. -/
private def x86Avx512FVLCompareLessThan : HardwareSlot :=
  ⟨"X86.Avx512F/VL", name!"CompareLessThan", "CompareLessThan",
    [signature (v256 u64) [v256 u64, v256 u64] (.avx512 .ltu64)], false⟩

/-- The fixed declarations of `X86.Avx512F/VL.CompareGreaterThan`. -/
private def x86Avx512FVLCompareGreaterThan : HardwareSlot :=
  ⟨"X86.Avx512F/VL", name!"CompareGreaterThan", "CompareGreaterThan",
    [signature (v256 u64) [v256 u64, v256 u64] (.avx512 .gtu64)], false⟩

/-- The fixed declarations of `X86.Avx512F/VL.CompareGreaterThanOrEqual`. -/
private def x86Avx512FVLCompareGreaterThanOrEqual : HardwareSlot :=
  ⟨"X86.Avx512F/VL", name!"CompareGreaterThanOrEqual", "CompareGreaterThanOrEqual",
    [signature (v256 u64) [v256 u64, v256 u64] (.avx512 .geu64)], false⟩

/-- The fixed declarations of `X86.Avx512DQ/VL.MultiplyLow`. -/
private def x86Avx512DQVLMultiplyLow : HardwareSlot :=
  ⟨"X86.Avx512DQ/VL", name!"MultiplyLow", "MultiplyLow",
    [signature (v256 u64) [v256 u64, v256 u64] (.avx512DQ .mul64)], false⟩

/-- The fixed declarations of `X86.Avx.MoveMask`. -/
private def x86AvxMoveMask : HardwareSlot :=
  ⟨"X86.Avx", name!"MoveMask", "MoveMask",
    [signature i32 [v256 f64] (.avx .moveMask64),
     signature i32 [v256 f32] (.avx .moveMask32)], false⟩

/-- The fixed declarations of `X86.Avx.Blend`. -/
private def x86AvxBlend : HardwareSlot :=
  ⟨"X86.Avx", name!"Blend", "Blend",
    [signature (v256 f32) [v256 f32, v256 f32, u8] (.avx .blend32)], false⟩

/-- The fixed declarations of `X86.Avx.TestZ`. -/
private def x86AvxTestZ : HardwareSlot :=
  ⟨"X86.Avx", name!"TestZ", "TestZ",
    [signature boolean [v256 u64, v256 u64] (.avx .testZ64)], false⟩

/-- The fixed declarations of `X86.Bmi1.BitFieldExtract`. -/
private def x86Bmi1BitFieldExtract : HardwareSlot :=
  ⟨"X86.Bmi1", name!"BitFieldExtract", "BitFieldExtract",
    [signature u32 [u32, u8, u8] (.bmi1 .bextr32)], false⟩

/-- The fixed declarations of `X86.Bmi2/X64.MultiplyNoFlags`. -/
private def x86Bmi2X64MultiplyNoFlags : HardwareSlot :=
  ⟨"X86.Bmi2/X64", name!"MultiplyNoFlags", "MultiplyNoFlags",
    [signature u64 [u64, u64] (.bmi2 .multiplyHigh64)], false⟩

/-- The fixed declarations of `Arm.ArmBase/Arm64.MultiplyHigh`. -/
private def armArmBaseArm64MultiplyHigh : HardwareSlot :=
  ⟨"Arm.ArmBase/Arm64", name!"MultiplyHigh", "MultiplyHigh",
    [signature u64 [u64, u64] (.armBase64 .multiplyHigh64)], false⟩

/-- The fixed declarations of `X86.X86Base/X64.DivRem`. -/
private def x86X86BaseX64DivRem : HardwareSlot :=
  ⟨"X86.X86Base/X64", name!"DivRem", "DivRem",
    [signature .pair [u64, u64, u64] (.x86Base .divRem64)], false⟩

/-- The other machine hardware slots. -/
private def otherMachineSlots : List HardwareSlot := [
  armAdvSimdExtractVector128,
  x86Sse2ShiftLeftLogical128BitLane,
  x86Ssse3AlignRight,
  x86Avx2Permute4x64,
  x86Avx2Blend,
  x86Avx2Add,
  x86Avx2CompareEqual,
  x86Avx2CompareGreaterThan,
  x86Avx2Multiply,
  x86Avx512FVLAlignRight64,
  x86Avx512FVLTernaryLogic,
  x86Avx512FVLCompareLessThan,
  x86Avx512FVLCompareGreaterThan,
  x86Avx512FVLCompareGreaterThanOrEqual,
  x86Avx512DQVLMultiplyLow,
  x86AvxMoveMask,
  x86AvxBlend,
  x86AvxTestZ,
  x86Bmi1BitFieldExtract,
  x86Bmi2X64MultiplyNoFlags,
  armArmBaseArm64MultiplyHigh,
  x86X86BaseX64DivRem]

/-- Portable integer bitwise operations admit the same five primitive elements at each width. -/
private def integerElements :=
  ["System.Byte", "System.Int32", "System.UInt32", "System.Int64", "System.UInt64"]

/-- A portable helper uses the named static class or the vector constructor of its width. -/
private def portableSlot (width : Nat) (key : MetadataName) (name : String)
    (rows : List HardwareRow) (genericOwner := false) : HardwareSlot :=
  ⟨s!"Vector{width}" ++ (if genericOwner then "`1" else ""), key, name, rows, genericOwner⟩

/-- Every integer bitwise declaration keeps its element, arity and vector width. -/
private def exactVectorSlots (width : Nat) : List HardwareSlot :=
  let vector := HWType.vector width .element
  let member := fun key name count op =>
    portableSlot width key name
    [signature vector (List.replicate count vector) (.vector op) integerElements] true
  [member name!"op_BitwiseAnd" "op_BitwiseAnd" 2 (.band width),
   member name!"op_BitwiseOr" "op_BitwiseOr" 2 (.bor width),
   member name!"op_ExclusiveOr" "op_ExclusiveOr" 2 (.bxor width),
   member name!"op_OnesComplement" "op_OnesComplement" 1 (.bnot width),
   member name!"get_Zero" "get_Zero" 0 (.zero width),
   member name!"get_AllBitsSet" "get_AllBitsSet" 0 (.ones width),
   portableSlot width name!"EqualsAll" "EqualsAll"
     [signature (.word "Boolean") [vector, vector] (.vector (.equalsAll width)) integerElements]]

/-- Arithmetic and reinterpretation helpers admit the specified closed elements. -/
private def otherVectorSlots (width : Nat) : List HardwareSlot :=
  let vec := HWType.vector width
  let openVector := vec .element
  let words := ["System.UInt64"]
  let cast := fun key name element => portableSlot width key name
    [signature (vec (.word element)) [openVector] (.vector (.reinterpret width))
      (integerElements ++ ["System.Single"])]
  [portableSlot width name!"op_Addition" "op_Addition"
     [signature openVector [openVector, openVector] (.vector (.add64 width)) words] true,
   portableSlot width name!"op_Subtraction" "op_Subtraction"
     [signature openVector [openVector, openVector] (.vector (.sub64 width)) words] true,
   portableSlot width name!"Equals" "Equals"
     [signature openVector [openVector, openVector] (.vector (.eq64 width)) words],
   portableSlot width name!"LessThan" "LessThan"
     [⟨openVector, [openVector, openVector], fun element =>
       .vector (if element == "System.Int64" then .lt64 width else .ltu64 width),
       ["System.Int64", "System.UInt64"]⟩],
   portableSlot width name!"Sum" "Sum"
     [signature .element [openVector] (.vector (.sum64 width)) words],
   portableSlot width name!"ExtractMostSignificantBits" "ExtractMostSignificantBits"
     [signature u32 [openVector] (.vector (.extractMSB64 width)) words],
   portableSlot width name!"ShiftRightArithmetic" "ShiftRightArithmetic"
     [signature (vec i64) [vec i64, .word "Int32"] (.vector (.ashr64 width))],
   portableSlot width name!"CreateScalar" "CreateScalar"
     [signature (vec u32) [u32] (.vector (.createScalar32 width)),
      signature (vec u64) [u64] (.vector (.createScalar64 width))],
   cast name!"AsByte" "AsByte" "Byte",
   cast name!"AsDouble" "AsDouble" "Double",
   cast name!"AsInt32" "AsInt32" "Int32",
   cast name!"AsInt64" "AsInt64" "Int64",
   cast name!"AsSingle" "AsSingle" "Single",
   cast name!"AsUInt32" "AsUInt32" "UInt32",
   cast name!"AsUInt64" "AsUInt64" "UInt64"]

/-- The exact family contains fixed signatures and portable integer bitwise declarations. -/
private def exactSlots := exactMachineSlots ++ [128, 256, 512].flatMap exactVectorSlots

/-- Each hardware name reserves its exact owner, including names with several declarations. -/
private def hardwareSlots :=
  exactSlots ++ otherMachineSlots ++ [128, 256].flatMap otherVectorSlots

/-- Hardware calls retain their closed method reference for execution. -/
def hardwareEntries : List ModelEntry := hardwareSlots.map HardwareSlot.entry

/-- Every registered hardware overload executes a checked intrinsic with the declared arity. -/
theorem hardwareEntries_yields {property : RuntimeModel → Prop}
    (intrinsic : ∀ operation count, property (.intrinsic operation count)) :
    ∀ entry ∈ hardwareEntries, entry.Yields property := by
  intro entry listed reader method model found
  obtain ⟨slot, _, rfl⟩ := List.mem_map.mp listed
  obtain ⟨overload, selected, resolved⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp (ModelEntry.select?_mem selected)
  change row.model slot reader method = some model at resolved
  unfold HardwareRow.model at resolved
  cases argument : row.argument slot method <;>
    simp [argument, bind, Option.bind, guard] at resolved
  split at resolved <;> simp_all
  subst model
  exact intrinsic _ _

#print axioms hardwareEntries_yields

/-- The exact hardware slot selected by the closed reference's owner and name. -/
private def exactSlot (method : MethodRef) := exactSlots.find? (·.matches method)

/-- A closed reference belongs to the exact family even if its overload is inadmissible. -/
def exactCallFamily (method : MethodRef) : Bool := (exactSlot method).isSome

/-- Exact signatures have no layout-dependent result and select only their declared operation. -/
def exactIntrinsic (method : MethodRef) : Option RuntimeModel := do
  let slot ← exactSlot method
  slot.entry.resolve (LayoutEnvironment.callLayouts {}) method

/-- Table lookup examines only these fields of a closed reference. -/
private def slotReference (owner : TypeExpr) (name : MetadataName) : MethodRef :=
  { owner, name, genericArity := 0, hasThis := false, returnType := .void, parameters := [] }

/-- Each owner shape of this slot selects its own entry in the registered table. -/
private def HardwareSlot.Registered (slot : HardwareSlot) (table : ModelTable) : Prop :=
  if slot.genericOwner then ∀ element,
    table.entry? .call (slotReference (.apply slot.head element) slot.key) = some slot.entry
  else table.entry? .call (slotReference slot.head slot.key) = some slot.entry

/-- Every hardware slot selects its own registered entry for every instantiation of its owner,
    so no other entry of the table shadows a hardware name. -/
def HardwareRegistered (table : ModelTable) : Prop :=
  ∀ slot ∈ hardwareSlots, slot.Registered table

/-- Literal lookups at the static hardware slots certify the runtime table's registration. -/
macro "hardware_registrations" : tactic => `(tactic|
  (simp only [HardwareRegistered, hardwareSlots, exactSlots, exactMachineSlots, exactVectorSlots,
     otherMachineSlots, otherVectorSlots,
     List.flatMap_cons, List.flatMap_nil, List.forall_mem_append, List.forall_mem_cons,
     List.not_mem_nil, false_implies, implies_true, and_true, true_and]
   repeat' first | apply And.intro | exact True.intro
   all_goals first | rfl | exact fun _ => rfl))

/-- The closed reference selects the registered entry of its exact slot. -/
private theorem HardwareSlot.lookup {table : ModelTable} {slot : HardwareSlot} {method : MethodRef}
    (registered : slot.Registered table) (matched : slot.matches method = true) :
    table.entry? .call method = some slot.entry := by
  unfold HardwareSlot.matches at matched
  obtain ⟨name, owner⟩ := Bool.and_eq_true_iff.mp matched
  have named := beq_iff_eq.mp name
  cases generic : slot.genericOwner with
  | false =>
    simp [generic] at owner
    simpa only [ModelTable.entry?, named, owner, slotReference] using
      (show table.entry? .call (slotReference slot.head slot.key) = _ from
        by simpa [HardwareSlot.Registered, generic] using registered)
  | true =>
    cases shape : method.owner <;> simp [generic, shape] at owner
    rename_i head element
    subst head
    have registration : ∀ arg, table.entry? .call
        (slotReference (.apply slot.head arg) slot.key) = some slot.entry := by
      simpa [HardwareSlot.Registered, generic] using registered
    simpa only [ModelTable.entry?, named, shape, slotReference] using registration element

#print axioms HardwareSlot.lookup

/-- Every exact row returns a scalar or vector and needs no tuple layout. -/
private theorem exactSlots_noPair : exactSlots.all (fun slot =>
    slot.rows.all (fun row => row.result != .pair)) = true := by decide +kernel

#print axioms exactSlots_noPair

/-- The hardware slot selected by the closed reference's owner and name. -/
private def hardwareSlot (method : MethodRef) := hardwareSlots.find? (·.matches method)

/-- A closed reference names a hardware member even if no row of its slot admits it. -/
def hardwareCallFamily (method : MethodRef) : Bool := (hardwareSlot method).isSome

/-- The model the rows of a hardware reference's own slot select. -/
def hardwareModel (environment : LayoutEnvironment) (method : MethodRef) :
    Option RuntimeModel := do
  let slot ← hardwareSlot method
  slot.entry.resolve environment.callLayouts method

/-- The table resolves a hardware reference only through the rows of its own slot. -/
theorem HardwareRegistered.resolve {table : ModelTable} (registered : HardwareRegistered table)
    (environment : LayoutEnvironment) (method : MethodRef)
    (member : hardwareCallFamily method = true) :
    table.find environment .call method = hardwareModel environment method := by
  obtain ⟨slot, selected⟩ := Option.isSome_iff_exists.mp member
  have found : hardwareSlots.find? (·.matches method) = some slot := selected
  have listed := List.mem_of_find?_eq_some found
  have matched := List.find?_some found
  rw [ModelTable.find, HardwareSlot.lookup (registered slot listed) matched]
  simp only [hardwareModel, selected]
  rfl

#print axioms HardwareRegistered.resolve

/-- The runtime table resolves an exact-family method only through its exact closed signature. -/
theorem HardwareRegistered.resolveExact {table : ModelTable}
    (registered : HardwareRegistered table)
    (environment : LayoutEnvironment) (method : MethodRef)
    (member : exactCallFamily method = true) :
    table.find environment .call method = exactIntrinsic method := by
  obtain ⟨slot, selected⟩ := Option.isSome_iff_exists.mp member
  have found : exactSlots.find? (·.matches method) = some slot := selected
  have listed := List.mem_of_find?_eq_some found
  have matched := List.find?_some found
  have exact : slot ∈ hardwareSlots := List.mem_append_left _ (List.mem_append_left _ listed)
  rw [ModelTable.find, HardwareSlot.lookup (registered slot exact) matched]
  simp only [exactIntrinsic, selected]
  change slot.entry.resolve environment.callLayouts method = slot.entry.resolve _ method
  unfold ModelEntry.resolve
  cases chosen : slot.entry.select? method with
  | none => rfl
  | some overload =>
    obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp (ModelEntry.select?_mem chosen)
    have rows := List.all_eq_true.mp exactSlots_noPair slot listed
    have valid := List.all_eq_true.mp rows row rowMem
    change row.model slot environment.callLayouts method = row.model slot _ method
    simp [HardwareRow.model, valid]

#print axioms HardwareRegistered.resolveExact

end CIL.Extraction
