import CIL.Memory
import CIL.Instructions
import CIL.IntegerArithmetic

/-!
# Instruction evaluation

Shared arithmetic, feature and intrinsic evaluation used by checked execution. Whole-method
execution, frame entry and call composition are defined only in `CIL.Safety.Execution`.
The optional single-step result is an internal evaluator, not a memory-safety judgment.
-/

namespace CIL

/-- Writes `values` into the locals of `frame`, local `i` getting the `i`th value. -/
def initLocals (memory : Memory) (frame : Nat) (values : List Value) : Memory :=
  values.zipIdx.foldl (fun memory (value, i) => write memory (.local frame i) value) memory

/-- The truth value a conditional branch tests: a nonzero integer is true. -/
def truth : Value → Option Bool
  | .i32 w => some (w != 0)
  | .i64 w => some (w != 0)
  | _ => none

/-- Two-operand arithmetic, bitwise and comparison instructions. `a` is the deeper stack
    operand. Comparisons push `1` or `0` as an `i32`; shift counts are taken modulo the width. -/
def binary (op : Instruction) (a b : Value) : Option Value :=
  match op, a, b with
  -- Division, remainder and overflow-checked arithmetic; a fault gives no value.
  | .div, x, y => (divideValues true false x y).toOption
  | .div_un, x, y => (divideValues false false x y).toOption
  | .rem, x, y => (divideValues true true x y).toOption
  | .rem_un, x, y => (divideValues false true x y).toOption
  | .add_ovf, x, y => (checkedValues .add true x y).toOption
  | .add_ovf_un, x, y => (checkedValues .add false x y).toOption
  | .sub_ovf, x, y => (checkedValues .sub true x y).toOption
  | .sub_ovf_un, x, y => (checkedValues .sub false x y).toOption
  | .mul_ovf, x, y => (checkedValues .mul true x y).toOption
  | .mul_ovf_un, x, y => (checkedValues .mul false x y).toOption
  -- Wrapping arithmetic and bitwise operations.
  | .add, .i64 x, .i64 y => some (.i64 (x + y))
  | .add, .i32 x, .i32 y => some (.i32 (x + y))
  | .sub, .i64 x, .i64 y => some (.i64 (x - y))
  | .sub, .i32 x, .i32 y => some (.i32 (x - y))
  | .mul, .i64 x, .i64 y => some (.i64 (x * y))
  | .mul, .i32 x, .i32 y => some (.i32 (x * y))
  | .and, .i64 x, .i64 y => some (.i64 (x &&& y))
  | .and, .i32 x, .i32 y => some (.i32 (x &&& y))
  | .or, .i64 x, .i64 y => some (.i64 (x ||| y))
  | .or, .i32 x, .i32 y => some (.i32 (x ||| y))
  | .xor, .i64 x, .i64 y => some (.i64 (x ^^^ y))
  | .xor, .i32 x, .i32 y => some (.i32 (x ^^^ y))
  -- Shifts.
  | .shl, .i64 x, .i32 count => some (.i64 (x <<< (count.toNat % 64)))
  | .shl, .i32 x, .i32 count => some (.i32 (x <<< (count.toNat % 32)))
  | .shr_un, .i64 x, .i32 count => some (.i64 (x >>> (count.toNat % 64)))
  | .shr_un, .i32 x, .i32 count => some (.i32 (x >>> (count.toNat % 32)))
  | .shr, .i64 x, .i32 count => some (.i64 (x.sshiftRight (count.toNat % 64)))
  | .shr, .i32 x, .i32 count => some (.i32 (x.sshiftRight (count.toNat % 32)))
  -- Native counts use their low bits; extraction distinguishes native values from int64.
  | .shl, .i64 x, .i64 count => some (.i64 (x <<< ((count.setWidth 32).toNat % 64)))
  | .shl, .i32 x, .i64 count => some (.i32 (x <<< ((count.setWidth 32).toNat % 32)))
  | .shr_un, .i64 x, .i64 count => some (.i64 (x >>> ((count.setWidth 32).toNat % 64)))
  | .shr_un, .i32 x, .i64 count => some (.i32 (x >>> ((count.setWidth 32).toNat % 32)))
  | .shr, .i64 x, .i64 count => some (.i64 (x.sshiftRight ((count.setWidth 32).toNat % 64)))
  | .shr, .i32 x, .i64 count => some (.i32 (x.sshiftRight ((count.setWidth 32).toNat % 32)))
  -- Comparisons.
  | .ceq, .i64 x, .i64 y => some (.i32 (if x = y then 1 else 0))
  | .ceq, .i32 x, .i32 y => some (.i32 (if x = y then 1 else 0))
  | .clt, .i64 x, .i64 y => some (.i32 (if x.toInt < y.toInt then 1 else 0))
  | .clt, .i32 x, .i32 y => some (.i32 (if x.toInt < y.toInt then 1 else 0))
  | .cgt, .i64 x, .i64 y => some (.i32 (if y.toInt < x.toInt then 1 else 0))
  | .cgt, .i32 x, .i32 y => some (.i32 (if y.toInt < x.toInt then 1 else 0))
  | .clt_un, .i64 x, .i64 y => some (.i32 (if x < y then 1 else 0))
  | .clt_un, .i32 x, .i32 y => some (.i32 (if x < y then 1 else 0))
  | .cgt_un, .i64 x, .i64 y => some (.i32 (if y < x then 1 else 0))
  | .cgt_un, .i32 x, .i32 y => some (.i32 (if y < x then 1 else 0))
  | _ , _, _ => none

/-- Native shift counts normalize to their low 32 bits under the admitted 64-bit runtime. -/
theorem binary_native_shift_count (operation : Instruction) (value : Value) (count : W64)
    (shift : operation = .shl ∨ operation = .shr ∨ operation = .shr_un) :
    binary operation value (.i64 count) = binary operation value (.i32 (count.setWidth 32)) := by
  rcases shift with rfl | rfl | rfl <;> cases value <;> rfl

#print axioms binary_native_shift_count

/-- One-operand instructions: negation, complement and integer conversions. A narrowing
    conversion truncates, then sign- or zero-extends back to `i32`. -/
def unary (op : Instruction) (value : Value) : Option Value :=
  match op, value with
  | .conv_ovf target, value => (convertInteger target.width target.signed false value).toOption
  | .conv_ovf_un target, value =>
    (convertInteger target.width target.signed true value).toOption
  | .neg, .i32 w => some (.i32 (-w))
  | .neg, .i64 w => some (.i64 (-w))
  | .not, .i64 w => some (.i64 (~~~w))
  | .not, .i32 w => some (.i32 (~~~w))
  -- To 8, 16 and 32 bits.
  | .conv_i1, .i32 w => some (.i32 (NarrowKind.signed8.extend w))
  | .conv_i1, .i64 w => some (.i32 (NarrowKind.signed8.extend (w.setWidth 32)))
  | .conv_u1, .i32 w => some (.i32 ((w.setWidth 8).zeroExtend 32))
  | .conv_u1, .i64 w => some (.i32 ((w.setWidth 8).zeroExtend 32))
  | .conv_i2, .i32 w => some (.i32 (NarrowKind.signed16.extend w))
  | .conv_i2, .i64 w => some (.i32 (NarrowKind.signed16.extend (w.setWidth 32)))
  | .conv_u2, .i32 w => some (.i32 (NarrowKind.unsigned16.extend w))
  | .conv_u2, .i64 w => some (.i32 (NarrowKind.unsigned16.extend (w.setWidth 32)))
  | .conv_i4, .i64 w => some (.i32 (w.setWidth 32))
  | .conv_i4, .i32 w => some (.i32 w)
  | .conv_u4, .i64 w => some (.i32 (w.setWidth 32))
  | .conv_u4, .i32 w => some (.i32 w)
  -- To 64 bits.
  | .conv_i8, .i32 w => some (.i64 (w.signExtend 64))
  | .conv_i8, .i64 w => some (.i64 w)
  | .conv_i, .i32 w => some (.i64 (w.signExtend 64))
  | .conv_i, .i64 w => some (.i64 w)
  | .conv_u8, .i32 w => some (.i64 (w.zeroExtend 64))
  | .conv_u8, .i64 w => some (.i64 w)
  | .conv_u, .i32 w => some (.i64 (w.zeroExtend 64))
  | .conv_u, .i64 w => some (.i64 w)
  | _, _ => none

/-- What a step asks the driver to do next. -/
inductive Action where
  /-- Continue at `pc` with the new stack and memory. -/
  | next (pc : Nat) (stack : List Value) (memory : Memory)
  /-- Call `callee` with `args`; its results are pushed onto `rest`. -/
  | call (callee : Nat) (args rest : List Value) (memory : Memory)
  /-- The method returned `result`. -/
  | returned (result : List Value) (memory : Memory)

/-- A `ret`: a value-returning method must leave exactly one initialized value (narrowed
    to the declared return width); a `void` method must leave an empty stack. -/
def returnFromStack (narrow : Option NarrowKind) (returns : Bool)
    (stack : List Value) (memory : Memory) : Option Action := do
  if returns then
    match stack with
    | [v] =>
      let v ← narrowValue narrow v
      if v.initialized then return .returned [v] memory else none
    | _ => none
  else if narrow.isNone && stack.isEmpty then return .returned [] memory else none

/-- Executes instruction `op` at `pc`. Binary operands are popped as `b :: a :: rest`, so
    `a` was pushed first. `returns` says whether the method returns a value; `profile`
    decides feature tests and intrinsic availability. -/
def step (op : Instruction) (returns : Bool) (pc : Nat) (args : List Value) (frame : Nat)
    (stack : List Value) (memory : Memory)
    (profile : FeatureProfile := FeatureProfile.scalar) : Option Action := do
  match op, stack with
  -- Constants and stack shuffling.
  | .nop, _ => return .next (pc + 1) stack memory
  | .ldc_i4 w, _ => return .next (pc + 1) (.i32 w :: stack) memory
  | .ldc_i8 w, _ => return .next (pc + 1) (.i64 w :: stack) memory
  | .dup, v :: rest => return .next (pc + 1) (v :: v :: rest) memory
  | .pop, _ :: rest => return .next (pc + 1) rest memory
  -- Arguments and locals; a read must be initialized.
  | .arg i narrow, _ =>
    let value ← args[i]?
    let value ← narrowValue narrow value
    if !value.initialized then none else return .next (pc + 1) (value :: stack) memory
  | .local i narrow, _ =>
    let value ← memory (.local frame i)
    let value ← narrowValue narrow value
    if !value.initialized then none else return .next (pc + 1) (value :: stack) memory
  | .localAddr i, _ => return .next (pc + 1) (.ref (.local frame i) :: stack) memory
  | .setLocal i narrow, v :: rest =>
    return .next (pc + 1) rest (write memory (.local frame i) (← narrowValue narrow v))
  -- Arithmetic, through `unary` and `binary`.
  | .neg, v :: rest | .not, v :: rest
  | .conv_ovf _, v :: rest | .conv_ovf_un _, v :: rest
  | .conv_i1, v :: rest | .conv_i2, v :: rest | .conv_u2, v :: rest
  | .conv_i4, v :: rest | .conv_i8, v :: rest | .conv_u1, v :: rest
  | .conv_u4, v :: rest | .conv_u8, v :: rest | .conv_u, v :: rest | .conv_i, v :: rest =>
    return .next (pc + 1) ((← unary op v) :: rest) memory
  | .add, b :: a :: rest | .sub, b :: a :: rest
  | .div, b :: a :: rest | .div_un, b :: a :: rest
  | .rem, b :: a :: rest | .rem_un, b :: a :: rest
  | .add_ovf, b :: a :: rest | .add_ovf_un, b :: a :: rest
  | .sub_ovf, b :: a :: rest | .sub_ovf_un, b :: a :: rest
  | .mul_ovf, b :: a :: rest | .mul_ovf_un, b :: a :: rest
  | .and, b :: a :: rest | .or, b :: a :: rest
  | .mul, b :: a :: rest | .xor, b :: a :: rest
  | .shl, b :: a :: rest | .shr, b :: a :: rest | .shr_un, b :: a :: rest
  | .clt, b :: a :: rest | .clt_un, b :: a :: rest | .cgt, b :: a :: rest
  | .cgt_un, b :: a :: rest
  | .ceq, b :: a :: rest =>
    return .next (pc + 1) ((← binary op a b) :: rest) memory
  -- 64-bit loads and stores through a reference.
  | .load64, .ref a :: rest =>
    match ← read64 memory a with
    | .i64 w => return .next (pc + 1) (.i64 w :: rest) memory
    | _ => none
  | .store64, .i64 w :: .ref a :: rest => return .next (pc + 1) rest (← write64 memory a w)
  -- Unconditional and truth-tested branches.
  | .br target, _ => return .next target stack memory
  | .switch targets, .i32 index :: rest =>
    return .next (targets[index.toNat]?.getD (pc + 1)) rest memory
  | .brfalse target, v :: rest => return .next (if ← truth v then pc + 1 else target) rest memory
  | .brtrue target, v :: rest => return .next (if ← truth v then target else pc + 1) rest memory
  -- Compare-and-branch: `a` was pushed first, and every condition is stated with `<` or `≤`.
  | .beq target, .i32 b :: .i32 a :: rest => return .next (if a = b then target else pc + 1) rest memory
  | .beq target, .i64 b :: .i64 a :: rest => return .next (if a = b then target else pc + 1) rest memory
  | .bne_un target, .i32 b :: .i32 a :: rest =>
    return .next (if a ≠ b then target else pc + 1) rest memory
  | .bne_un target, .i64 b :: .i64 a :: rest =>
    return .next (if a ≠ b then target else pc + 1) rest memory
  | .blt target, .i32 b :: .i32 a :: rest =>
    return .next (if a.toInt < b.toInt then target else pc + 1) rest memory
  | .blt target, .i64 b :: .i64 a :: rest =>
    return .next (if a.toInt < b.toInt then target else pc + 1) rest memory
  | .ble target, .i32 b :: .i32 a :: rest =>
    return .next (if a.toInt ≤ b.toInt then target else pc + 1) rest memory
  | .ble target, .i64 b :: .i64 a :: rest =>
    return .next (if a.toInt ≤ b.toInt then target else pc + 1) rest memory
  | .bgt target, .i32 b :: .i32 a :: rest =>
    return .next (if b.toInt < a.toInt then target else pc + 1) rest memory
  | .bgt target, .i64 b :: .i64 a :: rest =>
    return .next (if b.toInt < a.toInt then target else pc + 1) rest memory
  | .bge target, .i32 b :: .i32 a :: rest =>
    return .next (if b.toInt ≤ a.toInt then target else pc + 1) rest memory
  | .bge target, .i64 b :: .i64 a :: rest =>
    return .next (if b.toInt ≤ a.toInt then target else pc + 1) rest memory
  | .blt_un target, .i32 b :: .i32 a :: rest =>
    return .next (if a < b then target else pc + 1) rest memory
  | .blt_un target, .i64 b :: .i64 a :: rest =>
    return .next (if a < b then target else pc + 1) rest memory
  | .ble_un target, .i32 b :: .i32 a :: rest =>
    return .next (if a ≤ b then target else pc + 1) rest memory
  | .ble_un target, .i64 b :: .i64 a :: rest =>
    return .next (if a ≤ b then target else pc + 1) rest memory
  | .bgt_un target, .i32 b :: .i32 a :: rest =>
    return .next (if b < a then target else pc + 1) rest memory
  | .bgt_un target, .i64 b :: .i64 a :: rest =>
    return .next (if b < a then target else pc + 1) rest memory
  | .bge_un target, .i32 b :: .i32 a :: rest =>
    return .next (if b ≤ a then target else pc + 1) rest memory
  | .bge_un target, .i64 b :: .i64 a :: rest =>
    return .next (if b ≤ a then target else pc + 1) rest memory
  -- Calls; every argument must be initialized.
  | .call callee argc, _ =>
    if stack.length < argc || (stack.take argc).any (! ·.initialized) then none else
      return .call callee (stack.take argc).reverse (stack.drop argc) memory
  -- Hardware features, intrinsics and memory operations.
  | .feature id, _ =>
    return .next (pc + 1) (.i32 (if profile.evaluate id then 1 else 0) :: stack) memory
  | .intrinsic operation argc, _ =>
    if stack.length < argc || !operation.available profile then none else
      return .next (pc + 1)
        ((← evalIntrinsic operation (stack.take argc).reverse) :: stack.drop argc) memory
  | .memory operation, _ =>
    let (updated, values) ← evalMemory operation stack memory
    return .next (pc + 1) values updated
  | .skipInit, .object _ :: rest => return .next (pc + 1) rest memory
  | .skipInit, .ref _ :: rest => return .next (pc + 1) rest memory
  -- Return.
  | .ret narrow, _ => returnFromStack narrow returns stack memory
  | _, _ => none

end CIL
