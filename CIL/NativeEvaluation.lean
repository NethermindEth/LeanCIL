import CIL.Semantics

namespace CIL

/-- Only mixed integer arithmetic, comparisons and branches may use this path.
    It cannot dispatch memory, calls, features or another native wrapper. -/
def nativePureBinary : Op → Bool
  | .add | .sub | .mul | .band | .bor | .bxor | .lt | .ltu | .gt | .gtu | .eq
    | .bgt _ | .ble _ | .bleu _ | .bltu _ | .bgeu _ | .bgtu _ | .bge _ | .blt _
    | .beq _ | .bne _ => true
  | _ => false

/-- The admitted .NET runtime zero-extends for unsigned checked arithmetic and
    unsigned conditional branches. Other admitted mixed operations sign-extend,
    including the scalar comparison instructions clt.un and cgt.un. -/
def widenNativeOperand (op : Op) (bits : W32) : W64 :=
  match op with
  | .checkedArithmetic _ false | .bltu _ | .bgeu _ | .bgtu _ | .bleu _ | .bne _ => bits.zeroExtend 64
  | _ => bits.signExtend 64

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
