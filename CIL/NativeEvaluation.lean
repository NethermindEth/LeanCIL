import CIL.Semantics

/-!
# Mixed-width native operands

Binary instructions whose operands are an `i32` and a native-width `i64`, as CoreCLR
accepts them. The `i32` operand is widened the way the runtime widens it, then the
instruction runs through the ordinary `step`, `divideValues` or `checkedValues`, so the
mixed path adds no arithmetic of its own. The checked interpreter dispatches here.
-/

namespace CIL

/-- Only mixed integer arithmetic, comparisons and branches may use this path.
    Memory operations, calls and feature queries do not widen operands. -/
def nativePureBinary : Instruction → Bool
  | .add | .sub | .mul | .and | .or | .xor | .clt | .clt_un | .cgt | .cgt_un | .ceq
    | .bgt _ | .ble _ | .bge _ | .blt _ | .beq _ => true
  | _ => false

/-- Pure mixed operands with int32 sign-extended; other instructions and shapes are unchanged. -/
def widenMixed (operation : Instruction) (values : List Value) : List Value :=
  if nativePureBinary operation then
    match values with
    | [.i64 right, .i32 left] => [.i64 right, .i64 (left.signExtend 64)]
    | [.i32 right, .i64 left] => [.i64 (right.signExtend 64), .i64 left]
    | values => values
  else values

end CIL
