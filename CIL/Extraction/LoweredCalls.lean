import CIL.Extraction.ExactIntrinsics
import CIL.Extraction.UnsafeCalls
import CIL.Extraction.Scalars

/-!
# Ownership of lowered call sites

Runtime ownership uses the opcode and qualified member name.
Each owner resolves the closed signature separately.
-/

namespace CIL.Extraction

/-- A checked runtime family of calls or constructions. -/
inductive LoweredFamily where
  | hardware | span
  deriving DecidableEq, Repr

/-- The portable arithmetic and hardware members lowered to intrinsic instructions. -/
private def hardwareMember (owner member : String) : Bool :=
  match owner with
  | "System.Runtime.Intrinsics.Vector128"
  | "System.Runtime.Intrinsics.Vector256" => member ∈
      ["AsByte", "AsDouble", "AsInt32", "AsInt64", "AsSingle", "AsUInt32", "AsUInt64",
       "CreateScalar", "Equals", "EqualsAll", "ExtractMostSignificantBits", "LessThan",
       "ShiftRightArithmetic", "Sum"]
  | "System.Runtime.Intrinsics.Vector128`1"
  | "System.Runtime.Intrinsics.Vector256`1" => member ∈
      ["get_AllBitsSet", "get_Zero", "op_Addition", "op_BitwiseAnd", "op_BitwiseOr",
       "op_ExclusiveOr", "op_OnesComplement", "op_Subtraction"]
  | "System.Runtime.Intrinsics.Vector512" => member ∈
      ["EqualsAll"]
  | "System.Runtime.Intrinsics.Vector512`1" => member ∈
      ["get_AllBitsSet", "get_Zero", "op_BitwiseAnd", "op_BitwiseOr",
       "op_ExclusiveOr", "op_OnesComplement"]
  | "System.Runtime.Intrinsics.X86.Avx" => member ∈
      ["Blend", "MoveMask", "TestZ"]
  | "System.Runtime.Intrinsics.X86.Avx512DQ" => member ∈
      ["MoveMask"]
  | "System.Runtime.Intrinsics.Arm.Aes" => member ∈
      ["Encrypt", "MixColumns"]
  | "System.Runtime.Intrinsics.X86.Aes" => member ∈
      ["Encrypt"]
  | "System.Runtime.Intrinsics.X86.Ssse3" => member ∈
      ["AlignRight", "Shuffle"]
  | "System.Runtime.Intrinsics.Arm.AdvSimd" => member ∈
      ["ExtractVector128", "ReverseElement8"]
  | "System.Runtime.Intrinsics.X86.Sse2" => member ∈
      ["Multiply", "ShiftLeftLogical128BitLane"]
  | "System.Runtime.Intrinsics.X86.Avx2" => member ∈
      ["Add", "And", "AndNot", "Blend", "CompareEqual", "CompareGreaterThan", "Multiply",
       "Or", "Permute4x64", "ShiftLeftLogical", "ShiftRightLogical", "Shuffle", "Xor"]
  | "System.Runtime.Intrinsics.X86.Avx512DQ/VL" => member ∈
      ["MultiplyLow"]
  | "System.Runtime.Intrinsics.X86.Avx512F/VL" => member ∈
      ["AlignRight64", "CompareGreaterThan", "CompareGreaterThanOrEqual", "CompareLessThan",
       "PermuteVar4x64x2", "TernaryLogic"]
  | "System.Runtime.Intrinsics.X86.Avx512F" => member ∈
      ["CompareGreaterThan", "CompareLessThan"]
  | "System.Runtime.Intrinsics.X86.Bmi1" => member ∈
      ["BitFieldExtract"]
  | "System.Runtime.Intrinsics.Arm.ArmBase/Arm64" => member ∈
      ["MultiplyHigh"]
  | "System.Runtime.Intrinsics.X86.Bmi2/X64" => member ∈
      ["MultiplyNoFlags"]
  | "System.Runtime.Intrinsics.X86.X86Base/X64" => member ∈
      ["DivRem"]
  | _ => false

/-- The family of a method-token call before inspecting its overload, layouts or fold role. -/
def loweredCallFamily (raw : RawInstruction) : Option LoweredFamily := do
  let .call site := raw.operand | none
  let owner := site.declaringType
  let name := site.name
  if raw.opcode != 40 then none else
  match owner with
  | .apply (.constructor scope type) _ =>
    if scope == intrinsicsScope && hardwareMember type name then some .hardware
    else if scope != runtimeScope || type ∉ ["System.Span`1", "System.ReadOnlySpan`1"] then none
    else if name == ".ctor" then some .span else none
  | .atom scope type =>
    if scope == intrinsicsScope && hardwareMember type name then some .hardware else none
  | _ => none

end CIL.Extraction
