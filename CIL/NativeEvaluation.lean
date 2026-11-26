import CIL.Instructions

/-!
# Mixed-width native operands

Binary instructions whose operands are an `i32` and a native-width `i64`, as ECMA-335 III.1.5
admits them. `CIL.step` widens the `i32` operand the way the runtime widens it before it
selects an arm, so a mixed pair runs the same-width arithmetic and adds none of its own.
Division, remainder and overflow-checked arithmetic widen inside `divideValues` and
`checkedValues` instead.
-/

namespace CIL

/-- The instructions whose mixed operands `step` widens: wrapping arithmetic, bitwise
    operations, comparisons and signed compare-and-branch. Memory operations, calls, feature
    queries and unsigned branches keep their operands. -/
def nativePureBinary : Instruction → Bool
  | .add | .sub | .mul | .and | .or | .xor | .clt | .clt_un | .cgt | .cgt_un | .ceq
    | .bgt _ | .ble _ | .bge _ | .blt _ | .beq _ => true
  | _ => false

/-- The stack with the int32 operand of a mixed int32 and native pair on top sign-extended to
    64 bits, for an instruction `nativePureBinary` admits; any other stack is unchanged. -/
def widenMixed (operation : Instruction) (stack : List Value) : List Value :=
  match nativePureBinary operation, stack with
  | true, .i64 right :: .i32 left :: rest => .i64 right :: .i64 (left.signExtend 64) :: rest
  | true, .i32 right :: .i64 left :: rest => .i64 (right.signExtend 64) :: .i64 left :: rest
  | _, stack => stack

end CIL
