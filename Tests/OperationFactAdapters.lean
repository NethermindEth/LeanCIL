import CIL.Safety.SymbolicExecution

/-!
# Byte-operation fact adapters

Checked stepping reuses encoded reads and writes inside quantified conjunctions. Signed
narrow loads retain the byte width and sign extension; unrelated memory facts cannot advance
the instruction.
-/

namespace Tests.OperationFactAdapters
open CIL.Safety

/-- Taking a byte local's address needs formation at the current memory, not initialized bytes. -/
theorem local_address {memory other : Memory} {reference : Reference} {kind : CIL.LocalKind}
    {index : Nat} (body : CIL.Method) (pc : Nat) (args : List Value)
    (frame : Frame) (rest : List Value)
    (slot : frame.locals[index]? = some (.bytes kind reference))
    (wrongMemory : form other reference = .ok reference)
    (formed : form memory reference = .ok reference) :
    step body (.localAddr index) pc args frame rest memory =
      .ok (.next (pc + 1) (.reference (.address reference) :: rest) frame memory) := by
  fail_if_success solve | cil_checked_step [slot, wrongMemory]
  cil_checked_step [slot, formed]
#print axioms local_address

/-- A signed byte load extends the initialized eight-bit value to the CIL stack width. -/
theorem signed_byte {memory : Memory} {source : Reference} {bits : BitVec 8}
    (loaded : read memory source 1 1 = .ok (numberBytes bits.toNat 1))
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.loadScalar 1 true) pc args frame (.reference (.address source) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i32 (bits.signExtend 32)) :: rest) frame memory) := by
  cil_checked_step [loaded]
#print axioms signed_byte

/-- A signed two-byte load extends both initialized bytes to the CIL stack width. -/
theorem signed_short {memory : Memory} {source : Reference} {bits : BitVec 16}
    (loaded : read memory source 2 1 = .ok (numberBytes bits.toNat 2))
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.loadScalar 2 true) pc args frame (.reference (.address source) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i32 (bits.signExtend 32)) :: rest) frame memory) := by
  cil_checked_step [loaded]
#print axioms signed_short

/-- The read adapter selects equations inside nested conjunctions. -/
theorem conjoined_read {memory : Memory} {source : Reference} {bits : CIL.W64}
    (facts : True ∧ (read memory source 8 1 = .ok (numberBytes bits.toNat 8) ∧ True))
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body .load64 pc args frame (.reference (.address source) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i64 bits) :: rest) frame memory) := by
  cil_checked_step [facts]
#print axioms conjoined_read

/-- The write adapter preserves its exact resulting memory inside nested conjunctions. -/
theorem conjoined_write {memory after : Memory} {target : Reference} {bits : CIL.W64}
    (facts : True ∧ (write memory target (numberBytes bits.toNat 8) 1 = .ok after ∧ True))
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body .store64 pc args frame
        (.scalar (.i64 bits) :: .reference (.address target) :: rest) memory =
      .ok (.next (pc + 1) rest frame after) := by
  cil_checked_step [facts]
#print axioms conjoined_write

/-- A universally quantified conjunction supplies the signed read at its selected reference. -/
theorem quantified_signed_read {memory : Memory} (source : Nat → Reference)
    (bits : Nat → BitVec 16)
    (facts : ∀ index, True ∧ read memory (source index) 2 1 =
      .ok (numberBytes (bits index).toNat 2))
    (index : Nat) (body : CIL.Method) (pc : Nat) (args : List Value)
    (frame : Frame) (rest : List Value) :
    step body (.loadScalar 2 true) pc args frame
        (.reference (.address (source index)) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i32 ((bits index).signExtend 32)) :: rest)
        frame memory) := by
  cil_checked_step [facts]
#print axioms quantified_signed_read

/-- A universally quantified conjunction supplies the exact vector write. -/
theorem quantified_vector_write {memory : Memory} (after : Nat → Memory)
    (target : Nat → Reference) (bits : Nat → BitVec 256)
    (facts : ∀ index, write memory (target index) (numberBytes (bits index).toNat 32) 1 =
      .ok (after index) ∧ True)
    (index : Nat) (body : CIL.Method) (pc : Nat) (args : List Value)
    (frame : Frame) (rest : List Value) :
    step body (.memory .store256) pc args frame
        (.scalar (.v256 (bits index)) :: .reference (.address (target index)) :: rest) memory =
      .ok (.next (pc + 1) rest frame (after index)) := by
  cil_checked_step [facts]
#print axioms quantified_vector_write

/-- Aggregate reads accept symbolic widths and byte lists inside a conjunction. -/
theorem conjoined_aggregate_read {memory : Memory} {source : Reference} {width : Nat}
    {bytes : List (BitVec 8)} (facts : True ∧ read memory source width 1 = .ok bytes)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.loadAggregate width) pc args frame (.reference (.address source) :: rest)
        memory = .ok (.next (pc + 1) (.scalar (.aggregate bytes) :: rest) frame memory) := by
  cil_checked_step [facts]
#print axioms conjoined_aggregate_read

/-- A readonly aggregate preserves the initialization mask of a quantified snapshot fact. -/
theorem quantified_readonly_snapshot {memory : Memory} (source : Nat → Reference)
    (width : Nat) (bytes : Nat → List (BitVec 8 × Bool))
    (facts : ∀ index, True ∧ readSnapshot memory (source index) width 1 = .ok (bytes index))
    (index : Nat) (body : CIL.Method) (pc : Nat) (args : List Value)
    (frame : Frame) (rest : List Value) :
    step body (.loadAggregate width) pc args frame
        (.readOnlyReference (.address (source index)) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (snapshotValue (.aggregate width) (bytes index)) :: rest)
        frame memory) := by
  cil_checked_step [facts]
#print axioms quantified_readonly_snapshot

/-- Other memory, reference, width or write authority cannot replace an initialized read. -/
theorem read_requires_matching_evidence {memory other after : Memory}
    {source elsewhere : Reference} {bits : BitVec 16} {byte : BitVec 8} {stored : CIL.W32}
    {bytes : List (BitVec 8 × Bool)}
    (_wrongMemory : True ∧ read other source 2 1 = .ok (numberBytes bits.toNat 2))
    (_wrongSource : True ∧ read memory elsewhere 2 1 = .ok (numberBytes bits.toNat 2))
    (_wrongWidth : True ∧ read memory source 1 1 = .ok (numberBytes byte.toNat 1))
    (_onlyWritten : True ∧ write memory source (numberBytes stored.toNat 2) 1 = .ok after)
    (_onlySnapshot : True ∧ readSnapshot memory source 2 1 = .ok bytes)
    (loaded : read memory source 2 1 = .ok (numberBytes bits.toNat 2))
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.loadScalar 2 true) pc args frame (.reference (.address source) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i32 (bits.signExtend 32)) :: rest) frame memory) := by
  fail_if_success cil_checked_step [_wrongMemory]
  fail_if_success cil_checked_step [_wrongSource]
  fail_if_success cil_checked_step [_wrongWidth]
  fail_if_success cil_checked_step [_onlyWritten]
  fail_if_success cil_checked_step [_onlySnapshot]
  cil_checked_step [loaded]
#print axioms read_requires_matching_evidence

/-- Literal sign extension in a field-write fact preserves the surrounding symbolic sum. -/
theorem field_store_literal_conversion (left right : CIL.W64)
    (memory other final : Memory) (reference elsewhere : Reference)
    (added : add memory reference 1 0#64 = .ok reference)
    (_wrongMemory : write other reference
      (numberBytes (left + right + (1#32).signExtend 64).toNat 8) 1 = .ok final)
    (_wrongReference : write memory elsewhere
      (numberBytes (left + right + (1#32).signExtend 64).toNat 8) 1 = .ok final)
    (written : write memory reference
      (numberBytes (left + right + (1#32).signExtend 64).toNat 8) 1 = .ok final)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) :
    step body (.setFieldAt 0 8) pc args frame
      [.scalar (.i64 (left + right + 1#64)), .reference (.address reference)] memory =
      .ok (.next (pc + 1) [] frame final) := by
  fail_if_success cil_checked_step [added, _wrongMemory]
  fail_if_success cil_checked_step [added, _wrongReference]
  cil_checked_step [added, written]
#print axioms field_store_literal_conversion

/-- A truth-tested branch selects one of two distinct scalar results. -/
@[cil_code] def truthBranchBody (branch : CIL.Instruction) : CIL.Method := {
  locals := [], returnsValue := true,
  code := [.arg 0, branch, .const64 1, .ret, .const64 2, .ret] }

/-- A negative 64-bit case fact decides the next pc before it becomes a conditional term. -/
theorem branch_nonzero_literal (word unrelated : CIL.W64) (memory : Memory)
    (_unrelated : unrelated ≠ 0#64) (nonzero : word ≠ 0#64) :
    invoke [truthBranchBody (.brnonzero 4)] 5 0 [.scalar (.i64 word)] memory =
      .ok (memory, [.scalar (.i64 2)]) := by
  fail_if_success (cil_checked_steps [_unrelated]; done)
  cil_checked_steps [nonzero]
#print axioms branch_nonzero_literal

/-- A positive 32-bit case fact uses the same literal spelling for a zero branch. -/
theorem branch_zero_literal (word : CIL.W32) (memory : Memory) (zero : word = 0#32) :
    invoke [truthBranchBody (.brzero 4)] 5 0 [.scalar (.i32 word)] memory =
      .ok (memory, [.scalar (.i64 2)]) := by
  cil_checked_steps [zero]
#print axioms branch_zero_literal

/-- A supplied truth equation retains priority over unfolding the same condition. -/
theorem branch_truth_fact (word unrelated : CIL.W32) (memory : Memory)
    (_unrelated : CIL.truth (.i32 unrelated) = some false)
    (truth : CIL.truth (.i32 word) = some false) :
    invoke [truthBranchBody (.brzero 4)] 5 0 [.scalar (.i32 word)] memory =
      .ok (memory, [.scalar (.i64 2)]) := by
  fail_if_success (cil_checked_steps [_unrelated]; done)
  cil_checked_steps [truth]
#print axioms branch_truth_fact

/-- An unrelated truth equation does not prevent a matching zero comparison from deciding. -/
theorem branch_truth_fact_fallback (word unrelated : CIL.W64) (memory : Memory)
    (_unrelated : CIL.truth (.i64 unrelated) = some false) (nonzero : word ≠ 0#64) :
    invoke [truthBranchBody (.brnonzero 4)] 5 0 [.scalar (.i64 word)] memory =
      .ok (memory, [.scalar (.i64 2)]) := by
  cil_checked_steps [_unrelated, nonzero]
#print axioms branch_truth_fact_fallback

/-- A closed zero operand decides the negative branch condition without a supplied guard. -/
theorem branch_closed_zero (memory : Memory) :
    invoke [truthBranchBody (.brnonzero 4)] 5 0 [.scalar (.i32 0)] memory =
      .ok (memory, [.scalar (.i64 1)]) := by
  cil_checked_steps []
#print axioms branch_closed_zero

/-- A signed comparison follows a narrowing conversion of a symbolic natural literal. -/
@[cil_code] def narrowedBranchBody : CIL.Method := {
  locals := [], returnsValue := true,
  code := [.arg 0, .arg 1, .convI4, .blt 6, .const64 1, .ret, .const64 2, .ret] }

/-- Narrowed branch operands match the supplied comparison without expanding symbolic arithmetic. -/
theorem branch_narrowed_literal (index : CIL.W32) (length : Nat) (memory : Memory)
    (inside : index.toInt < (BitVec.ofNat 32 length).toInt) :
    invoke [narrowedBranchBody] 7 0
      [.scalar (.i32 index), .scalar (.i64 (BitVec.ofNat 64 length))] memory =
      .ok (memory, [.scalar (.i64 2)]) := by
  cil_checked_steps [inside]
#print axioms branch_narrowed_literal

/-- A named word value preserves the comparison result before widening it. -/
def reportedWord (condition : Prop) [Decidable condition] : BitVec 64 :=
  (if condition then (1 : BitVec 32) else 0).signExtend 64

/-- Widening a Boolean word preserves its zero or one value. -/
@[local simp] theorem widen_report (condition : Prop) [Decidable condition] :
    (if condition then (1 : BitVec 32) else 0).signExtend 64 =
      if condition then (1 : BitVec 64) else 0 := by
  split <;> rfl
#print axioms widen_report

/-- Explicit definitions match operation facts without imposing global arithmetic normal forms. -/
theorem named_report_write (condition : Prop) [Decidable condition]
    {memory after : Memory} {target : Reference}
    (written : write memory target (numberBytes (reportedWord condition).toNat 8) 1 = .ok after)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body .store64 pc args frame
        (.scalar (.i64 ((if condition then (1 : BitVec 32) else 0).signExtend 64)) ::
          .reference (.address target) :: rest) memory =
      .ok (.next (pc + 1) rest frame after) := by
  cil_checked_step [written, reportedWord]
#print axioms named_report_write

/-- A result projection forwards the values produced by a helper contract. -/
def forwardedResults (values : List Value) : List Value := values

/-- Narrowed return equations accept a stack hidden behind a named result projection. -/
theorem projected_return (memory : Memory) (frame : Frame) :
    step { code := [], locals := [], returnsValue := true } (.ret (some .unsigned8))
      1 [] frame (forwardedResults [.scalar (.i32 1)] ++ []) memory =
      .ok (.returned [.scalar (.i32 1)] memory) := by
  cil_checked_step []
#print axioms projected_return

end Tests.OperationFactAdapters
