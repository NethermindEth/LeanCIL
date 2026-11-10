import CIL.Safety.SymbolicExecution

/-!
# Byte-operation fact adapters

Checked stepping reuses encoded reads and writes inside quantified conjunctions. Signed
narrow loads retain the byte width and sign extension; unrelated memory facts cannot advance
the instruction.
-/

namespace Tests.OperationFactAdapters
open CIL.Safety

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

end Tests.OperationFactAdapters
