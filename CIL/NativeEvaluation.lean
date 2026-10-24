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
    It cannot dispatch memory, calls, features or another native wrapper. -/
def nativePureBinary : Op → Bool
  | .add | .sub | .mul | .band | .bor | .bxor | .lt | .ltu | .gt | .gtu | .eq
    | .bgt _ | .ble _ | .bge _ | .blt _ | .beq _ => true
  | _ => false

/-- The admitted .NET runtime zero-extends for unsigned checked arithmetic.
    Other admitted mixed operations sign-extend, including scalar clt.un/cgt.un.
    Mixed unsigned branches are rejected: CoreCLR's widening depends on whether
    its importer sees a constant, which can change through inlining. -/
def widenNativeOperand (op : Op) (bits : W32) : W64 :=
  match op with
  | .checkedArithmetic _ false => bits.zeroExtend 64
  | _ => bits.signExtend 64

/-- Runs a mixed `i32`/`i64` binary instruction at `pc`: the next pc and the values it
    pushes, or the arithmetic fault. Any other operand pair is `invalidOperands`. -/
def nativeBinaryValues (op : Op) (pc : Nat) (x y : Value) :
    Except ArithmeticFault (Nat × List Value) := do
  let (x, y) ← match x, y with
    | .i32 a, .i64 b => .ok (Value.i64 (widenNativeOperand op a), Value.i64 b)
    | .i64 a, .i32 b => .ok (Value.i64 a, Value.i64 (widenNativeOperand op b))
    | _, _ => .error .invalidOperands
  match op with
  | .divide signed remainder =>
    return (pc + 1, [← divideValues signed remainder x y])
  | .checkedArithmetic kind signed =>
    return (pc + 1, [← checkedValues kind signed x y])
  | _ =>
    if nativePureBinary op then
      match step op false pc [] 0 [y, x] (fun _ => none) with
      | some (.next target values _) => .ok (target, values)
      | _ => .error .invalidOperands
    else .error .invalidOperands

end CIL
