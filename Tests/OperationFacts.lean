import CIL.Safety.SymbolicExecution

/-!
# Checked memory operations without evaluator definitions

The instruction proofs consume successful byte operations. A write requires authority but
does not require old contents; reads require the actual initialized encoding at this memory.
-/

namespace Tests.OperationFacts
open CIL.Safety

/-- A vector load consumes the read fact for the same memory, reference and width. -/
theorem vector_load {memory : Memory} {source : Reference} {bits : BitVec 256}
    (loaded : read memory source 32 1 = .ok (numberBytes bits.toNat 32))
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.memory .load256) pc args frame (.reference (.address source) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.v256 bits) :: rest) frame memory) := by
  cil_checked_step [loaded]
#print axioms vector_load

/-- A vector store consumes its successful write, without asking for any previous snapshot. -/
theorem vector_store {memory after : Memory} {destination : Reference} {bits : BitVec 256}
    (written : write memory destination (numberBytes bits.toNat 32) 1 = .ok after)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.memory .store256) pc args frame
        (.scalar (.v256 bits) :: .reference (.address destination) :: rest) memory =
      .ok (.next (pc + 1) rest frame after) := by
  cil_checked_step [written]
#print axioms vector_store

/-- A scalar load uses the same byte-read evidence as a vector load. -/
theorem word_load {memory : Memory} {source : Reference} {bits : CIL.W64}
    (loaded : read memory source 8 1 = .ok (numberBytes bits.toNat 8))
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.ldind .i8) pc args frame (.reference (.address source) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i64 bits) :: rest) frame memory) := by
  cil_checked_step [loaded]
#print axioms word_load

/-- A scalar store needs the write equation and no evaluator implementation names. -/
theorem word_store {memory after : Memory} {destination : Reference} {bits : CIL.W64}
    (written : write memory destination (numberBytes bits.toNat 8) 1 = .ok after)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.stind .i8) pc args frame
        (.scalar (.i64 bits) :: .reference (.address destination) :: rest) memory =
      .ok (.next (pc + 1) rest frame after) := by
  cil_checked_step [written]
#print axioms word_store

/-- An initialized byte load zero-extends the checked byte encoding. -/
theorem byte_load {memory : Memory} {source : Reference} {bits : BitVec 8}
    (loaded : read memory source 1 1 = .ok (numberBytes bits.toNat 1))
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.loadScalar 1 false) pc args frame (.reference (.address source) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i32 (bits.setWidth 32)) :: rest) frame memory) := by
  cil_checked_step [loaded]
#print axioms byte_load

/-- A byte store consumes write authority without requiring old initialized contents. -/
theorem byte_store {memory after : Memory} {destination : Reference} {bits : CIL.W32}
    (written : write memory destination (numberBytes bits.toNat 1) 1 = .ok after)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.storeScalar 1) pc args frame
        (.scalar (.i32 bits) :: .reference (.address destination) :: rest) memory =
      .ok (.next (pc + 1) rest frame after) := by
  cil_checked_step [written]
#print axioms byte_store

/-- A four-byte `stind` consumes the write fact for its width; its kind decides the width. -/
theorem int_store {memory after : Memory} {destination : Reference} {bits : CIL.W32}
    (written : write memory destination (numberBytes bits.toNat 4) 1 = .ok after)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.stind .i4) pc args frame
        (.scalar (.i32 bits) :: .reference (.address destination) :: rest) memory =
      .ok (.next (pc + 1) rest frame after) := by
  cil_checked_step [written]
#print axioms int_store

/-- Stores its second argument as two bytes through its first. -/
@[cil_code] def storeShortMethod : CIL.Method := {
  code := [.ldarg 0, .ldarg 1, .stind .i2, .ret]
  locals := [], returnsValue := false }

/-- A body run reaches a two-byte `stind` and steps it with the fact derived from its write. -/
theorem stored_short {memory after : Memory} {destination : Reference} {bits : CIL.W32}
    (formed : form memory destination = .ok destination)
    (written : write memory destination (numberBytes bits.toNat 2) 1 = .ok after) :
    invoke [storeShortMethod] 5 0 [.reference (.address destination), .scalar (.i32 bits)]
        memory = .ok (after, []) := by
  cil_checked_steps [formed, written]
#print axioms stored_short

/-- One-byte writes of a narrowed int and of a one-byte literal, as narrow struct fields and
    flags store them, give no int store step; the run beside them kernel-checks. -/
theorem stored_beside_byte_writes {memory after other : Memory} {destination : Reference}
    {bits value : CIL.W32}
    (formed : form memory destination = .ok destination)
    (written : write memory destination (numberBytes bits.toNat 2) 1 = .ok after)
    (narrowed : write memory destination (numberBytes (value.setWidth 8).toNat 1) 1 = .ok other)
    (flagged : write memory destination (numberBytes (1 : BitVec (8 * 1)).toNat 1) 1 = .ok other) :
    invoke [storeShortMethod] 5 0 [.reference (.address destination), .scalar (.i32 bits)]
        memory = .ok (after, []) := by
  cil_checked_steps [formed, written, narrowed, flagged]
#print axioms stored_beside_byte_writes

/-- A symbolic reference with an established formation result can be skipped without a write. -/
theorem skip_formed_reference {memory : Memory} {reference : ManagedReference}
    {value : Value} (formed : formValue memory reference = .ok value)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body .skipInit pc args frame (.reference reference :: rest) memory =
      .ok (.next (pc + 1) rest frame memory) := by
  cil_checked_step [formed]
#print axioms skip_formed_reference

end Tests.OperationFacts
