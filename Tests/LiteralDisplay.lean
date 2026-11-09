import CIL

/-!
# Literal display tests

Pins how goals print bit-vector literals: values of `2 ^ 16` or more in hexadecimal, smaller
ones in decimal, and either form elaborating back to the same term. Canonical literals also
keep hypotheses usable by default `simp`, including through a list predicate.
-/

namespace Tests.LiteralDisplay

open CIL (W32 W64)

-- A spec's mask prints as written, in both the numeral and the `#w` form.
/-- info: fun count => count ||| 0x80000000 : W32 → W32 -/
#guard_msgs in
#check fun count : W32 => count ||| 0x80000000

/-- info: 0x80000000#32 : BitVec 32 -/
#guard_msgs in
#check BitVec.ofNat 32 2147483648

/-- info: 0x9E3779B97F4A7C15#64 : BitVec 64 -/
#guard_msgs in
#check (0x9E3779B97F4A7C15#64 : W64)

-- Counts and indexes below the threshold stay decimal, as does every `Nat`.
/-- info: (5#32, 65535) : BitVec 32 × W32 -/
#guard_msgs in
#check ((5#32, 65535) : BitVec 32 × W32)

/-- info: 0x10000 : W32 -/
#guard_msgs in
#check (65536 : W32)

/-- info: 2147483648 : Nat -/
#guard_msgs in
#check (2147483648 : Nat)

-- The printed form is the same term, so a goal copied from the display elaborates back to it.
example : (0x80000000#32 : W32) = BitVec.ofNat 32 2147483648 := rfl
example : (0x80000000 : W32) = @OfNat.ofNat W32 2147483648 _ := rfl

/-- A nonzero hypothesis in simp-normal form closes the matching bit-vector goal. -/
theorem nonzero_simp (value : W32) (nonzero : value ≠ 0#32) : value ≠ 0#32 := by
  simp [nonzero]
#print axioms nonzero_simp

/-- A hypothesis using an ordinary numeral can be restated for default simplification. -/
theorem nonzero_simp_restate (value : W32) (nonzero : value ≠ 0) : value ≠ 0#32 := by
  simp [show value ≠ 0#32 from nonzero]
#print axioms nonzero_simp_restate

/-- The words before the first zero, with the predicate in simp-normal form. -/
def nonzeroPrefix (values : List W32) : List W32 := values.takeWhile (· ≠ 0#32)

/-- Default simplification uses a nonzero hypothesis under an unfolded list predicate. -/
theorem nonzeroPrefix_cons (value : W32) (rest : List W32) (nonzero : value ≠ 0#32) :
    nonzeroPrefix (value :: rest) = value :: nonzeroPrefix rest := by
  simp [nonzeroPrefix, nonzero]
#print axioms nonzeroPrefix_cons

/-! Checked stepping evaluates the closed literal operands a step leaves in its state, so a
    state reads the same from `cil_checked_steps` and `cil_contract_steps` and a lemma stated
    over the evaluated numeral applies without a separate rewrite. Symbolic operands keep their
    form. -/

open CIL.Safety in
/-- Sign-extends a 32-bit literal, shifts by a literal count and truncates a literal to a
    byte; `high` and `count` are the literals a case checks. -/
def literalBody (high count narrow : Nat) : CIL.Method :=
  { returnsValue := true, locals := [], code :=
      [.const32 (BitVec.ofNat 32 high), .convI8, .arg 0, .const32 (BitVec.ofNat 32 count), .shl,
        .const32 (BitVec.ofNat 32 narrow), .convU1, .ret] }

section LiteralOperands
open CIL.Safety

variable (frame : Frame) (memory : Memory) (x : W64)
  (result : Except LocatedFault (Memory × List Value))

/-- The state after the seven instructions before `ret`, with the three evaluated operands. -/
abbrev literalState (frame : Frame) (memory : Memory) (x : W64)
    (result : Except LocatedFault (Memory × List Value)) (high count narrow : Nat)
    (extended : W64) (shift : Nat) (byte : W32) : Prop :=
  run [literalBody high count narrow] 2 0 7 [.scalar (.i64 x)] frame
    [.scalar (.i32 byte), .scalar (.i64 (x <<< shift)), .scalar (.i64 extended)] memory = result

/-- `cil_checked_steps` leaves the sign extension, masked count and truncation evaluated: the
    consumer cases `signExtend 64 0xFFFFFFFF#32`, `(63#32).toNat % 64` and
    `((3#32).setWidth 8)`. -/
example (rest : literalState frame memory x result 0xFFFFFFFF 63 3 0xFFFFFFFFFFFFFFFF#64 63 3#32) :
    run [literalBody 0xFFFFFFFF 63 3] 9 0 0 [.scalar (.i64 x)] frame [] memory = result := by
  cil_checked_steps 7 [literalBody]
  with_reducible exact rest

/-- Boundary values keep signedness, truncation and shift masking: `0x7FFFFFFF` stays
    positive and `0x80000000` extends its sign, a count of 127 masks to 63 and 65 to 1, and
    `0x1FF` truncates to `0xFF`. -/
example (rest : literalState frame memory x result 0x7FFFFFFF 127 0x1FF 0x7FFFFFFF#64 63
      0xFF#32) :
    run [literalBody 0x7FFFFFFF 127 0x1FF] 9 0 0 [.scalar (.i64 x)] frame [] memory = result := by
  cil_checked_steps 7 [literalBody]
  with_reducible exact rest

example (rest : literalState frame memory x result 0x80000000 65 0x100
      0xFFFFFFFF80000000#64 1 0#32) :
    run [literalBody 0x80000000 65 0x100] 9 0 0 [.scalar (.i64 x)] frame [] memory = result := by
  cil_checked_steps 7 [literalBody]
  with_reducible exact rest

/-- A zero extension, an unmasked count and an untruncated byte are each rejected, compared as
    the state is written: evaluating the run would drop the operands under the returned one. -/
example
    (zeroExtended : literalState frame memory x result 0x80000000 127 0x1FF 0x80000000#64 63
      0xFF#32)
    (unmasked : literalState frame memory x result 0x80000000 127 0x1FF 0xFFFFFFFF80000000#64
      127 0xFF#32)
    (untruncated : literalState frame memory x result 0x80000000 127 0x1FF
      0xFFFFFFFF80000000#64 63 0x1FF#32)
    (rest : literalState frame memory x result 0x80000000 127 0x1FF 0xFFFFFFFF80000000#64 63
      0xFF#32) :
    run [literalBody 0x80000000 127 0x1FF] 9 0 0 [.scalar (.i64 x)] frame [] memory = result := by
  cil_checked_steps 7 [literalBody]
  fail_if_success with_reducible exact zeroExtended
  fail_if_success with_reducible exact unmasked
  fail_if_success with_reducible exact untruncated
  with_reducible exact rest

/-- `cil_contract_steps` leaves the same evaluated state. -/
example (program : CIL.Program) (found : program[0]? = some (literalBody 0xFFFFFFFF 63 3))
    (post : Memory → List Value → Prop)
    (rest : ∃ fuel final returned, run program fuel 0 7 [.scalar (.i64 x)] frame
      [.scalar (.i32 3#32), .scalar (.i64 (x <<< 63)), .scalar (.i64 0xFFFFFFFFFFFFFFFF#64)]
      memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run program fuel 0 0 [.scalar (.i64 x)] frame [] memory =
      .ok (final, returned) ∧ post final returned := by
  cil_contract_steps 7 [found, literalBody]
  with_reducible exact rest

/-- A symbolic count keeps its masked form, which a consumer's lemma about it still matches. -/
def symbolicShiftBody : CIL.Method :=
  { returnsValue := true, locals := [], code := [.arg 0, .arg 1, .shl, .ret] }

example (count : W32)
    (rest : run [symbolicShiftBody] 2 0 3 [.scalar (.i64 x), .scalar (.i32 count)] frame
      [.scalar (.i64 (x <<< (count.toNat % 64)))] memory = result) :
    run [symbolicShiftBody] 5 0 0 [.scalar (.i64 x), .scalar (.i32 count)] frame [] memory =
      result := by
  cil_checked_steps 3 [symbolicShiftBody]
  with_reducible exact rest

end LiteralOperands
end Tests.LiteralDisplay
