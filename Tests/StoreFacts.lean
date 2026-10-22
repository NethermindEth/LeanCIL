import CIL.Safety.MethodContract

/-! Store facts stated in their source form, as a carry or borrow helper's proof
    states them, rather than in the form the checked steps compute. -/
namespace Tests.StoreFacts

open CIL.Safety

/-- `*sum = a + b + c; *carry = (a + b + c < a) ? 1 : 0`. -/
@[cil_code] def carryMethod : CIL.Method := {
  code := [.arg 3, .arg 0, .arg 1, .add, .arg 2, .add, .store64,
    .arg 4, .arg 0, .arg 1, .add, .arg 2, .add, .arg 0, .ltu, .convU8, .store64, .ret]
  locals := [], returnsValue := false }
@[cil_code] def carryProgram : CIL.Program := [carryMethod]

/-- `*difference = a - b - c; *borrow = (a < b) | (c & (a == b))`, with sign-extended flags. -/
@[cil_code] def borrowMethod : CIL.Method := {
  code := [.arg 3, .arg 0, .arg 1, .sub, .arg 2, .sub, .store64,
    .arg 4, .arg 0, .arg 1, .ltu, .convI8, .arg 2, .arg 0, .arg 1, .eq, .convI8, .band, .bor, .store64, .ret]
  locals := [], returnsValue := false }
@[cil_code] def borrowProgram : CIL.Program := [borrowMethod]

def carryOut (a b c : CIL.W64) : CIL.W64 := (if a + b + c < a then (1 : CIL.W32) else 0).zeroExtend 64

def borrowOut (a b c : CIL.W64) : CIL.W64 :=
  (if a < b then (1 : CIL.W32) else 0).signExtend 64 ||| (c &&& (if a = b then (1 : CIL.W32) else 0).signExtend 64)

def carryArgs (a b c : CIL.W64) (sum carry : Reference) : List Value :=
  [.scalar (.i64 a), .scalar (.i64 b), .scalar (.i64 c), .reference (.address sum), .reference (.address carry)]

-- Each write equation names its value as the contract does; the simp set only adds `carryOut`.
theorem carry_stores (a b c : CIL.W64) (sum carry : Reference) (m m1 m2 : Memory)
    (formedSum : form m sum = .ok sum) (formedCarry : form m carry = .ok carry)
    (formedCarry1 : form m1 carry = .ok carry)
    (sumWrite : write m sum (numberBytes (a + b + c).toNat 8) 1 = .ok m1)
    (carryWrite : write m1 carry (numberBytes (carryOut a b c).toNat 8) 1 = .ok m2) :
    invoke carryProgram (CIL.executionBound carryProgram 0) 0 (carryArgs a b c sum carry) m = .ok (m2, []) := by
  cil_checked_steps [carryArgs, carryOut, checkedValue, formValue, checkedAt, instruction, storeValue, referenceAt,
    formedSum, formedCarry, formedCarry1, sumWrite, carryWrite,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms carry_stores

theorem borrow_stores (a b c : CIL.W64) (difference borrow : Reference) (m m1 m2 : Memory)
    (formedDifference : form m difference = .ok difference) (formedBorrow : form m borrow = .ok borrow)
    (formedBorrow1 : form m1 borrow = .ok borrow)
    (differenceWrite : write m difference (numberBytes (a - b - c).toNat 8) 1 = .ok m1)
    (borrowWrite : write m1 borrow (numberBytes (borrowOut a b c).toNat 8) 1 = .ok m2) :
    invoke borrowProgram (CIL.executionBound borrowProgram 0) 0 (carryArgs a b c difference borrow) m =
      .ok (m2, []) := by
  cil_checked_steps [carryArgs, borrowOut, checkedValue, formValue, checkedAt, instruction, storeValue, referenceAt,
    formedDifference, formedBorrow, formedBorrow1, differenceWrite, borrowWrite,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms borrow_stores

-- The same facts drive `cil_contract_steps` on an existential run.
theorem carry_contract_steps (a b c : CIL.W64) (sum carry : Reference) (m m1 m2 : Memory)
    (formedSum : form m sum = .ok sum) (formedCarry : form m carry = .ok carry)
    (formedCarry1 : form m1 carry = .ok carry)
    (sumWrite : write m sum (numberBytes (a + b + c).toNat 8) 1 = .ok m1)
    (carryWrite : write m1 carry (numberBytes (carryOut a b c).toNat 8) 1 = .ok m2) :
    ∃ fuel final values, invoke carryProgram fuel 0 (carryArgs a b c sum carry) m = .ok (final, values) ∧
      final = m2 ∧ values = [] := by
  cil_contract_steps [carryArgs, carryOut, checkedValue, formValue, checkedAt, instruction, storeValue, referenceAt,
    formedSum, formedCarry, formedCarry1, sumWrite, carryWrite,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨rfl, rfl⟩

#print axioms carry_contract_steps

-- Hand-written stepping gets the same normalisation, under its own simp configuration.
example (a b c : CIL.W64) (r : Reference) (m m1 : Memory)
    (written : write m r (numberBytes (a + b + c).toNat 8) 1 = .ok m1) :
    storeValue m (.address r) (.i64 (a + b + c)) = .ok m1 := by
  -- Plain simp rewrites the stored sum but leaves `written` as stated, so it never fires.
  set_option linter.unusedSimpArgs false in
    fail_if_success (simp [storeValue, referenceAt, checkedAt, Except.mapError, Bind.bind, Except.bind, written]; done)
  cil_fact_simp (config := { implicitDefEqProofs := false })
    [storeValue, referenceAt, checkedAt, Except.mapError, Bind.bind, Except.bind] [written]

-- A fact that differs after normalisation stops the steps at its store, with the fact as stated.
-- The carry write names the sum: the second store is wrong.
/--
error: unsolved goals
case executed
a b c : CIL.W64
sum carry : Reference
m m1 m2 : Memory
formedSum : form m sum = Except.ok sum
formedCarry : form m carry = Except.ok carry
formedCarry1 : form m1 carry = Except.ok carry
sumWrite : write m sum (numberBytes (BitVec.toNat (a + b + c)) 8) 1 = Except.ok m1
carryWrite : write m1 carry (numberBytes (BitVec.toNat (a + b + c)) 8) 1 = Except.ok m2
⊢ run carryProgram 3 0 16 (carryArgs a b c sum carry) { activation := m.nextIdentity, locals := [], owned := [] }
      ([Value.scalar (CIL.Value.i64 (BitVec.zeroExtend 64 (if a + b + c < a then 1#32 else 0#32)))].reverse ++
        [Value.reference (ManagedReference.address carry)])
      m1 =
    Except.ok (m2, [])
-/
#guard_msgs in
example (a b c : CIL.W64) (sum carry : Reference) (m m1 m2 : Memory)
    (formedSum : form m sum = .ok sum) (formedCarry : form m carry = .ok carry)
    (formedCarry1 : form m1 carry = .ok carry)
    (sumWrite : write m sum (numberBytes (a + b + c).toNat 8) 1 = .ok m1)
    (carryWrite : write m1 carry (numberBytes (a + b + c).toNat 8) 1 = .ok m2) :
    invoke carryProgram (CIL.executionBound carryProgram 0) 0 (carryArgs a b c sum carry) m = .ok (m2, []) := by
  cil_checked_steps [carryArgs, carryOut, checkedValue, formValue, checkedAt, instruction, storeValue, referenceAt,
    formedSum, formedCarry, formedCarry1, sumWrite, carryWrite,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

-- The sum written to the carry's address.
/--
error: unsolved goals
case executed
a b c : CIL.W64
sum carry : Reference
m m1 : Memory
formedSum : form m sum = Except.ok sum
formedCarry : form m carry = Except.ok carry
sumWrite : write m carry (numberBytes (BitVec.toNat (a + b + c)) 8) 1 = Except.ok m1
⊢ run carryProgram 13 0 6 (carryArgs a b c sum carry) { activation := m.nextIdentity, locals := [], owned := [] }
      ([Value.scalar (CIL.Value.i64 (a + b + c))].reverse ++ [Value.reference (ManagedReference.address sum)]) m =
    Except.ok (m1, [])
-/
#guard_msgs in
example (a b c : CIL.W64) (sum carry : Reference) (m m1 : Memory)
    (formedSum : form m sum = .ok sum) (formedCarry : form m carry = .ok carry)
    (sumWrite : write m carry (numberBytes (a + b + c).toNat 8) 1 = .ok m1) :
    invoke carryProgram (CIL.executionBound carryProgram 0) 0 (carryArgs a b c sum carry) m = .ok (m1, []) := by
  cil_checked_steps [carryArgs, checkedValue, formValue, checkedAt, instruction, storeValue, referenceAt,
    formedSum, formedCarry, sumWrite, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

-- The sum written from a memory the method never reaches.
/--
error: unsolved goals
case executed
a b c : CIL.W64
sum carry : Reference
m m1 m2 : Memory
formedSum : form m sum = Except.ok sum
formedCarry : form m carry = Except.ok carry
sumWrite : write m1 sum (numberBytes (BitVec.toNat (a + b + c)) 8) 1 = Except.ok m2
⊢ run carryProgram 13 0 6 (carryArgs a b c sum carry) { activation := m.nextIdentity, locals := [], owned := [] }
      ([Value.scalar (CIL.Value.i64 (a + b + c))].reverse ++ [Value.reference (ManagedReference.address sum)]) m =
    Except.ok (m2, [])
-/
#guard_msgs in
example (a b c : CIL.W64) (sum carry : Reference) (m m1 m2 : Memory)
    (formedSum : form m sum = .ok sum) (formedCarry : form m carry = .ok carry)
    (sumWrite : write m1 sum (numberBytes (a + b + c).toNat 8) 1 = .ok m2) :
    invoke carryProgram (CIL.executionBound carryProgram 0) 0 (carryArgs a b c sum carry) m = .ok (m2, []) := by
  cil_checked_steps [carryArgs, checkedValue, formValue, checkedAt, instruction, storeValue, referenceAt,
    formedSum, formedCarry, sumWrite, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

end Tests.StoreFacts
