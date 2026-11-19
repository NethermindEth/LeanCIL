import CIL.Extraction.RuntimeSignatures
import CIL.Extraction.ExactIntrinsics

/-!
# Arithmetic and hardware overloads

The fixed signatures below supplement the exact vector matcher. A portable generic overload
also binds the closed element types and the open spelling of its external target.
-/

namespace CIL.Extraction

/-- The closed type and its spelling in a non-generic intrinsic signature. -/
private abbrev Operand := TypeExpr × String

/-- A primitive from the runtime assembly. -/
private def word (name : String) : Operand :=
  let full := "System." ++ name
  (.atom runtimeScope full, full)

/-- A closed vector of the intrinsics assembly. -/
private def vector (width : Nat) (element : Operand) : Operand :=
  let owner := s!"System.Runtime.Intrinsics.Vector{width}`1"
  (.apply (.constructor intrinsicsScope owner) element.1, s!"{owner}<{element.2}>")

/-- A fixed hardware signature returns exactly the indicated intrinsic and arity. -/
private def machineInstruction (environment : CallLayouts) (site : CallSite)
    (owner : String) : Option (Intrinsic × Nat) := do
  let u64 := word "UInt64"
  let i64 := word "Int64"
  let u32 := word "UInt32"
  let i32 := word "Int32"
  let byte := word "Byte"
  let v128 := vector 128
  let v256 := vector 256
  let signature (result : Operand) (parameters : List Operand) (op : Intrinsic) := do
    guard (concreteRuntimeCall site intrinsicsScope owner result.1 result.2 parameters)
    return (op, parameters.length)
  match owner, site.name with
  | "System.Runtime.Intrinsics.Arm.AdvSimd", "ExtractVector128" =>
    signature (v128 u64) [v128 u64, v128 u64, byte] (.advSimd .extract64)
  | "System.Runtime.Intrinsics.X86.Sse2", "ShiftLeftLogical128BitLane" =>
    signature (v128 u64) [v128 u64, byte] (.sse .shiftLeftBytes)
  | "System.Runtime.Intrinsics.X86.Ssse3", "AlignRight" =>
    signature (v128 byte) [v128 byte, v128 byte, byte] (.sse .alignBytes)
  | "System.Runtime.Intrinsics.X86.Avx2", "Permute4x64" =>
    signature (v256 u64) [v256 u64, byte] (.avx2 .permute4x64)
  | "System.Runtime.Intrinsics.X86.Avx2", "Blend" =>
    signature (v256 u32) [v256 u32, v256 u32, byte] (.avx2 .blend32) <|>
    signature (v256 i32) [v256 i32, v256 i32, byte] (.avx2 .blend32)
  | "System.Runtime.Intrinsics.X86.Avx2", "Add" =>
    signature (v256 u64) [v256 u64, v256 u64] (.avx2 .add64)
  | "System.Runtime.Intrinsics.X86.Avx2", "CompareEqual" =>
    signature (v256 u64) [v256 u64, v256 u64] (.avx2 .eq64)
  | "System.Runtime.Intrinsics.X86.Avx2", "CompareGreaterThan" =>
    signature (v256 i64) [v256 i64, v256 i64] (.avx2 .signedgt64)
  | "System.Runtime.Intrinsics.X86.Avx2", "Multiply" =>
    signature (v256 u64) [v256 u32, v256 u32] (.avx2 .multiplyEven32)
  | "System.Runtime.Intrinsics.X86.Avx512F/VL", "AlignRight64" =>
    signature (v256 u64) [v256 u64, v256 u64, byte] (.avx512 .alignRight64)
  | "System.Runtime.Intrinsics.X86.Avx512F/VL", "TernaryLogic" =>
    signature (v256 u64) [v256 u64, v256 u64, v256 u64, byte] (.avx512 .ternaryLogic)
  | "System.Runtime.Intrinsics.X86.Avx512F/VL", "CompareLessThan" =>
    signature (v256 u64) [v256 u64, v256 u64] (.avx512 .ltu64)
  | "System.Runtime.Intrinsics.X86.Avx512F/VL", "CompareGreaterThan" =>
    signature (v256 u64) [v256 u64, v256 u64] (.avx512 .gtu64)
  | "System.Runtime.Intrinsics.X86.Avx512F/VL", "CompareGreaterThanOrEqual" =>
    signature (v256 u64) [v256 u64, v256 u64] (.avx512 .geu64)
  | "System.Runtime.Intrinsics.X86.Avx512DQ/VL", "MultiplyLow" =>
    signature (v256 u64) [v256 u64, v256 u64] (.avx512DQ .mul64)
  | "System.Runtime.Intrinsics.X86.Avx", "MoveMask" =>
    signature i32 [v256 (word "Double")] (.avx .moveMask64) <|>
    signature i32 [v256 (word "Single")] (.avx .moveMask32)
  | "System.Runtime.Intrinsics.X86.Avx", "Blend" =>
    let floats := v256 (word "Single")
    signature floats [floats, floats, byte] (.avx .blend32)
  | "System.Runtime.Intrinsics.X86.Avx", "TestZ" =>
    signature (word "Boolean") [v256 u64, v256 u64] (.avx .testZ64)
  | "System.Runtime.Intrinsics.X86.Bmi1", "BitFieldExtract" =>
    signature u32 [u32, byte, byte] (.bmi1 .bextr32)
  | "System.Runtime.Intrinsics.X86.Bmi2/X64", "MultiplyNoFlags" =>
    signature u64 [u64, u64] (.bmi2 .multiplyHigh64)
  | "System.Runtime.Intrinsics.Arm.ArmBase/Arm64", "MultiplyHigh" =>
    signature u64 [u64, u64] (.armBase64 .multiplyHigh64)
  | "System.Runtime.Intrinsics.X86.X86Base/X64", "DivRem" =>
    guard (integerPairResult environment site.returnType u64.2 8)
    let pair := "System.ValueTuple`2<System.UInt64,System.UInt64>"
    signature (site.returnType, pair) [u64, u64, u64] (.x86Base .divRem64)
  | _, _ => none

/-- Arithmetic, lane creation and casts on 128- and 256-bit vectors. -/
private def vectorInstruction (site : CallSite) : Option (Intrinsic × Nat) := do
  let (width, owner) ← match site.declaringType with
    | .atom scope owner | .apply (.constructor scope owner) _ => do
      guard (scope == intrinsicsScope)
      match owner with
      | "System.Runtime.Intrinsics.Vector128" | "System.Runtime.Intrinsics.Vector128`1" =>
        some (128, "System.Runtime.Intrinsics.Vector128")
      | "System.Runtime.Intrinsics.Vector256" | "System.Runtime.Intrinsics.Vector256`1" =>
        some (256, "System.Runtime.Intrinsics.Vector256")
      | _ => none
    | _ => none
  let u64 := word "UInt64"
  let i64 := word "Int64"
  let u32 := word "UInt32"
  let vec := vector width
  let parameter : Operand := (.parameter 0, "!!0")
  let openVec := vec parameter
  let declared (ownerName : String) (result : Operand) (parameters : List Operand)
      (closedResult : Operand) (closedParams : List Operand) (arguments : List TypeExpr) :=
    let names := ",".intercalate (parameters.map Prod.snd)
    let signature := s!"{result.2} {ownerName}::{site.name}({names})"
    site.declared.returnType == result.1 && site.declared.parameters == parameters.map Prod.fst &&
      staticRuntimeCall site intrinsicsScope signature closedResult.1
        (closedParams.map Prod.fst) arguments
  let choose (res : Operand) (pars : List Operand) (op : VectorIntrinsic) := do
    guard (concreteRuntimeCall site intrinsicsScope owner res.1 res.2 pars)
    return (Intrinsic.vector op, pars.length)
  let generic (element res : Operand) (pars : List Operand) (openResult : Operand)
      (openParams : List Operand)
      (op : VectorIntrinsic) := do
    guard (declared owner openResult openParams res pars [element.1])
    return (Intrinsic.vector op, pars.length)
  if site.declaringType == (vec u64).1 then
    let op ← match site.name with
      | "op_Addition" => some (VectorIntrinsic.add64 width)
      | "op_Subtraction" => some (.sub64 width)
      | _ => none
    let v := (vec u64)
    let template := vec (.ownerParameter 0, "!0")
    guard (declared v.2 template [template, template] v [v, v] [])
    return (.vector op, 2)
  guard (site.declaringType == .atom intrinsicsScope owner)
  match site.name with
  | "LessThan" | "Equals" =>
    let element := if site.typeArguments == [i64.1] then i64 else u64
    let op ← match site.name, element.1 == i64.1 with
      | "LessThan", true => some (VectorIntrinsic.lt64 width)
      | "LessThan", false => some (.ltu64 width)
      | "Equals", false => some (.eq64 width)
      | _, _ => none
    generic element (vec element) [vec element, vec element] openVec [openVec, openVec] op
  | "Sum" => generic u64 u64 [vec u64] parameter [openVec] (.sum64 width)
  | "ExtractMostSignificantBits" =>
    generic u64 u32 [vec u64] u32 [openVec] (.extractMSB64 width)
  | "ShiftRightArithmetic" =>
    choose (vec i64) [vec i64, word "Int32"] (.ashr64 width)
  | "CreateScalar" =>
    choose (vec u64) [u64] (.createScalar64 width) <|>
      choose (vec u32) [u32] (.createScalar32 width)
  | "Create" =>
    choose (vec u64) [u64] (.create64 width) <|>
      choose (vec u64) (List.replicate (width / 64) u64) (.create64 width) <|>
      choose (vec u32) (List.replicate (width / 32) u32) (.create32 width)
  | member =>
    let target ← [("AsByte", "Byte"), ("AsUInt32", "UInt32"), ("AsInt64", "Int64"),
      ("AsDouble", "Double"), ("AsUInt64", "UInt64"), ("AsInt32", "Int32"),
      ("AsSingle", "Single")].lookup member
    let [.atom scope source] := site.typeArguments | none
    guard (scope == runtimeScope)
    let name ← ["UInt64", "Byte", "UInt32", "Int64", "Int32", "Single"].find?
      (fun short => source == "System." ++ short)
    let element := word name
    let result := vec (word target)
    generic element result [vec element] result [openVec] (.reinterpret width)

/-- Exact metadata and target availability determine the emitted hardware instruction. -/
def hardwareInstruction (environment : CallLayouts) (profile : FeatureProfile)
    (raw : RawInstruction) (site : CallSite) : Option Instruction := do
  let (intrinsic, count) ← exactIntrinsic raw <|> vectorInstruction site <|> do
    let .atom scope owner := site.declaringType | none
    guard (scope == intrinsicsScope)
    machineInstruction environment site owner
  guard (intrinsic.available profile)
  return .intrinsic intrinsic count

end CIL.Extraction
