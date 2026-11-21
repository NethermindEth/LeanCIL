import CIL.Safety.ResolutionFacts
import CIL.SymbolicExecution
import CIL.Extraction.RuntimeModels

/-! Closed runtime member signatures used by the checked SIMD execution fixtures. -/

namespace Tests.IntrinsicMethods
open CIL CIL.Extraction

private def i32 := TypeExpr.atom runtimeScope "System.Int32"
private def byte := TypeExpr.atom runtimeScope "System.Byte"
private def vectorOf (width : Nat) (element : String) := TypeExpr.apply
  (.constructor intrinsicsScope s!"System.Runtime.Intrinsics.Vector{width}`1") (.atom runtimeScope element)
private def v32 := vectorOf 256 "System.UInt32"
/-- The closed vector operand shared by the arithmetic calls and typed memory accesses. -/
def vector256UInt64 := vectorOf 256 "System.UInt64"

private def layouts : LayoutEnvironment := {}

cil_value_shape layouts vector256UInt64

private def member (owner : String) (name : MetadataName) (result : TypeExpr)
    (parameters : List TypeExpr) : MethodRef :=
  { owner := .atom intrinsicsScope ("System.Runtime.Intrinsics." ++ owner),
    name, hasThis := false, genericArity := 0, returnType := result, parameters }

def add64 := member "X86.Avx2" name!"Add" vector256UInt64 [vector256UInt64, vector256UInt64]

@[cil_code] theorem add64_model (env : LayoutEnvironment) :
    runtimeModel env .call add64 = some (.intrinsic (.avx2 .add64) 2) := rfl

def multiplyEven32 := member "X86.Avx2" name!"Multiply" vector256UInt64 [v32, v32]

@[cil_code] theorem multiplyEven32_model (env : LayoutEnvironment) :
    runtimeModel env .call multiplyEven32 = some (.intrinsic (.avx2 .multiplyEven32) 2) := rfl

def shiftRight := member "X86.Avx2" name!"ShiftRightLogical" vector256UInt64 [vector256UInt64, byte]

@[cil_code] theorem shiftRight_model (env : LayoutEnvironment) :
    runtimeModel env .call shiftRight = some (.intrinsic (.avx2 .shr64) 2) := rfl

def shiftLeft := member "X86.Avx2" name!"ShiftLeftLogical" vector256UInt64 [vector256UInt64, byte]

@[cil_code] theorem shiftLeft_model (env : LayoutEnvironment) :
    runtimeModel env .call shiftLeft = some (.intrinsic (.avx2 .shl64) 2) := rfl

def permute := member "X86.Avx2" name!"Permute4x64" vector256UInt64 [vector256UInt64, byte]

@[cil_code] theorem permute_model (env : LayoutEnvironment) :
    runtimeModel env .call permute = some (.intrinsic (.avx2 .permute4x64) 2) := rfl

def compareEqual := member "X86.Avx2" name!"CompareEqual" vector256UInt64 [vector256UInt64, vector256UInt64]

@[cil_code] theorem compareEqual_model (env : LayoutEnvironment) :
    runtimeModel env .call compareEqual = some (.intrinsic (.avx2 .eq64) 2) := rfl

def compareLessThan := member "X86.Avx512F/VL" name!"CompareLessThan" vector256UInt64 [vector256UInt64, vector256UInt64]

@[cil_code] theorem compareLessThan_model (env : LayoutEnvironment) :
    runtimeModel env .call compareLessThan = some (.intrinsic (.avx512 .ltu64) 2) := rfl

def moveMask := member "X86.Avx512DQ" name!"MoveMask" i32 [vector256UInt64]

@[cil_code] theorem moveMask_model (env : LayoutEnvironment) :
    runtimeModel env .call moveMask = some (.intrinsic (.avx512DQ .moveMask64) 1) := rfl

def multiplyLow := member "X86.Avx512DQ/VL" name!"MultiplyLow" vector256UInt64 [vector256UInt64, vector256UInt64]

@[cil_code] theorem multiplyLow_model (env : LayoutEnvironment) :
    runtimeModel env .call multiplyLow = some (.intrinsic (.avx512DQ .mul64) 2) := rfl

private def word := TypeExpr.atom runtimeScope "System.UInt64"

def createFour := member "Vector256" name!"Create" vector256UInt64 [word, word, word, word]

@[cil_code] theorem createFour_model (env : LayoutEnvironment) :
    runtimeModel env .call createFour = some (.intrinsic (.vector (.create64 256)) 4) := rfl

def portableAdd := { member "Vector256" name!"op_Addition" vector256UInt64 [vector256UInt64, vector256UInt64] with owner := vector256UInt64 }

@[cil_code] theorem portableAdd_model (env : LayoutEnvironment) :
    runtimeModel env .call portableAdd = some (.intrinsic (.vector (.add64 256)) 2) := rfl

def subtract := { member "Vector256" name!"op_Subtraction" vector256UInt64 [vector256UInt64, vector256UInt64] with owner := vector256UInt64 }

@[cil_code] theorem subtract_model (env : LayoutEnvironment) :
    runtimeModel env .call subtract = some (.intrinsic (.vector (.sub64 256)) 2) := rfl

def sum := { member "Vector256" name!"Sum" word [vector256UInt64] with
  genericArity := 1, methodArguments := [word] }

@[cil_code] theorem sum_model (env : LayoutEnvironment) :
    runtimeModel env .call sum = some (.intrinsic (.vector (.sum64 256)) 1) := rfl

def asUInt32 := { member "Vector256" name!"AsUInt32" v32 [vector256UInt64] with
  genericArity := 1, methodArguments := [word] }

@[cil_code] theorem asUInt32_model (env : LayoutEnvironment) :
    runtimeModel env .call asUInt32 = some (.intrinsic (.vector (.reinterpret 256)) 1) := rfl

/-- The closed vector operand used by the byte intrinsics and typed loads. -/
def vector128Byte := vectorOf 128 "System.Byte"

cil_value_shape layouts vector128Byte

def shiftLeftBytes := member "X86.Sse2" name!"ShiftLeftLogical128BitLane"
  (vectorOf 128 "System.UInt64") [vectorOf 128 "System.UInt64", byte]

theorem shiftLeftBytes_model (env : LayoutEnvironment) :
    runtimeModel env .call shiftLeftBytes = some (.intrinsic (.sse .shiftLeftBytes) 2) := rfl

def armEncrypt := member "Arm.Aes" name!"Encrypt" vector128Byte [vector128Byte, vector128Byte]

theorem armEncrypt_model (env : LayoutEnvironment) :
    runtimeModel env .call armEncrypt = some (.intrinsic (.armAes .encrypt) 2) := rfl

def ternaryLogic := member "X86.Avx512F/VL" name!"TernaryLogic" vector256UInt64 [vector256UInt64, vector256UInt64, vector256UInt64, byte]

theorem ternaryLogic_model (env : LayoutEnvironment) :
    runtimeModel env .call ternaryLogic = some (.intrinsic (.avx512 .ternaryLogic) 4) := rfl

def shuffle256 := member "X86.Avx2" name!"Shuffle" (vectorOf 256 "System.Byte")
  [vectorOf 256 "System.Byte", vectorOf 256 "System.Byte"]

theorem shuffle256_model (env : LayoutEnvironment) :
    runtimeModel env .call shuffle256 = some (.intrinsic (.avx2 .shuffleBytes) 2) := rfl

def shuffle128 := member "X86.Ssse3" name!"Shuffle" vector128Byte [vector128Byte, vector128Byte]

theorem shuffle128_model (env : LayoutEnvironment) :
    runtimeModel env .call shuffle128 = some (.intrinsic (.sse .shuffleBytes) 2) := rfl

end Tests.IntrinsicMethods
