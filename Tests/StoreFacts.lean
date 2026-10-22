import CIL.Safety.MethodContract
import CIL.Safety.OutcomeContract

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
      [Value.scalar (CIL.Value.i64 (BitVec.setWidth 64 (if a + b + c < a then 1#32 else 0#32))),
        Value.reference (ManagedReference.address carry)]
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
      [Value.scalar (CIL.Value.i64 (a + b + c)), Value.reference (ManagedReference.address sum)] m =
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
      [Value.scalar (CIL.Value.i64 (a + b + c)), Value.reference (ManagedReference.address sum)] m =
    Except.ok (m2, [])
-/
#guard_msgs in
example (a b c : CIL.W64) (sum carry : Reference) (m m1 m2 : Memory)
    (formedSum : form m sum = .ok sum) (formedCarry : form m carry = .ok carry)
    (sumWrite : write m1 sum (numberBytes (a + b + c).toNat 8) 1 = .ok m2) :
    invoke carryProgram (CIL.executionBound carryProgram 0) 0 (carryArgs a b c sum carry) m = .ok (m2, []) := by
  cil_checked_steps [carryArgs, checkedValue, formValue, checkedAt, instruction, storeValue, referenceAt,
    formedSum, formedCarry, sumWrite, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

open Lean Elab Tactic in
elab "fact_normalizations " expected:num " in " body:tacticSeq : tactic => do
  let before ← getTraceState
  withOptions (fun options => options.setBool `trace.CIL.factNormalize true) do
    evalTactic body
  let after ← getTraceState
  setTraceState before
  let count := after.traces.size - before.traces.size
  unless count = expected.getNat do
    throwError "Expected {expected.getNat} fact normalizations, got {count}"

@[cil_code] def twentySeven : CIL.Method :=
  { code := List.replicate 26 .nop ++ [.ret], locals := [], returnsValue := false }

@[cil_code] def twentySevenProgram : CIL.Program := [twentySeven]

theorem normalize_once (words : Nat → Nat) (memory : Memory)
    (h0 : words 0 = 0) (h1 : words 1 = 0) (h2 : words 2 = 0) (h3 : words 3 = 0)
    (h4 : words 4 = 0) (h5 : words 5 = 0) (h6 : words 6 = 0) (h7 : words 7 = 0)
    (h8 : words 8 = 0) (h9 : words 9 = 0) (h10 : words 10 = 0) (h11 : words 11 = 0) :
    invoke twentySevenProgram 27 0 [] memory = .ok (memory, []) := by
  fact_normalizations 12 in
    cil_checked_steps [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

theorem contract_normalize_once (words : Nat → Nat) (memory : Memory) (zero : words 0 = 0) :
    ∃ fuel final values, invoke twentySevenProgram fuel 0 [] memory = .ok (final, values) ∧
      final = memory ∧ values = [] := by
  fact_normalizations 1 in
    cil_contract_steps [zero]
  exact ⟨rfl, rfl⟩

@[cil_code] def twentySevenRaises : CIL.Method :=
  { code := List.replicate 26 .nop ++ [.throw "Test.Exception"], locals := [], returnsValue := false }

@[cil_code] def twentySevenRaisesProgram : CIL.Program := [twentySevenRaises]

theorem raise_normalize_once (words : Nat → Nat) (memory : Memory) (zero : words 0 = 0) :
    Raises twentySevenRaisesProgram 0 [] memory "Test.Exception" := by
  fact_normalizations 1 in
    cil_raise_steps [zero]

@[cil_code] def fourLimb : CIL.Method :=
  { code := [.arg 0, .fieldAt 0 8, .arg 0, .fieldAt 8 8, .arg 0, .fieldAt 16 8,
      .arg 0, .fieldAt 24 8, .pop, .pop, .pop, .ret], locals := [], returnsValue := true }

@[cil_code] def fourLimbProgram : CIL.Program := [fourLimb]

theorem indexed_fields (memory : Memory) (left : Reference) (words : Fin 4 → CIL.W64)
    (formed : form memory left = .ok left)
    (limbs : ∀ (index : Fin 4) rest,
      instruction (.fieldAt (8 * index.val) 8) (.reference (.address left) :: rest) memory =
        .ok (memory, .scalar (.i64 (words index)) :: rest)) :
    invoke fourLimbProgram 12 0 [.reference (.address left)] memory =
      .ok (memory, [.scalar (.i64 (words 0))]) := by
  cil_checked_steps [checkedValue, formValue, checkedAt, formed, limbs]

@[cil_code] def literalBranch : CIL.Method :=
  { code := [.arg 0, .fieldAt 8 8, .brzero 5, .const32 9, .ret, .const32 0, .ret],
    locals := [], returnsValue := true }

@[cil_code] def literalBranchProgram : CIL.Program := [literalBranch]

theorem constructor_index_branch (memory : Memory) (left : Reference) (words : Fin 4 → CIL.W64)
    (bound : 1 < 4) (formed : form memory left = .ok left)
    (field : ∀ rest, instruction (.fieldAt 8 8) (.reference (.address left) :: rest) memory =
      .ok (memory, .scalar (.i64 (words ⟨1, bound⟩)) :: rest))
    (zero : words 1 = 0) :
    invoke literalBranchProgram 7 0 [.reference (.address left)] memory =
      .ok (memory, [.scalar (.i32 0)]) := by
  cil_checked_steps [checkedValue, formValue, checkedAt, formed, field, zero]

#print axioms normalize_once
#print axioms contract_normalize_once
#print axioms raise_normalize_once
#print axioms indexed_fields
#print axioms constructor_index_branch

end Tests.StoreFacts
