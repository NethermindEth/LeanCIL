import CIL.Semantics

/-!
# Scalar memory lemmas

Frame facts for the reference interpreter's memory: caller bytes and scalar locals
are separate address spaces, so a write to one leaves reads of the others unchanged.
Stepping proofs use these to carry facts about caller memory across local updates.
-/

open CIL
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace CIL

/-- A caller-byte read depends only on caller bytes. -/
theorem readBytes_congr (m n : Memory)
    (h : ∀ address, m (.byte address) = n (.byte address)) (base count : Nat) :
    readBytes m base count = readBytes n base count := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih => simp [readBytes, h, ih]

@[simp] theorem readBytes_write_local (m : Memory) (frame index base count : Nat) (v : Value) :
    readBytes (write m (.local frame index) v) base count = readBytes m base count := by
  apply readBytes_congr
  intro address
  simp [write]

theorem initLocals_bytes (m : Memory) (frame : Nat) (values : List Value) (address : Nat) :
    initLocals m frame values (.byte address) = m (.byte address) := by
  unfold initLocals
  generalize values.zipIdx = entries
  induction entries generalizing m with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [write]

@[simp] theorem readBytes_initLocals (m : Memory) (frame base count : Nat) (values : List Value) :
    readBytes (initLocals m frame values) base count = readBytes m base count := by
  apply readBytes_congr
  exact initLocals_bytes m frame values

@[simp] theorem writeBytes_local (m : Memory) (base word count frame index : Nat) :
    writeBytes m base word count (.local frame index) = m (.local frame index) := by
  induction count generalizing m base word with
  | zero => rfl
  | succ count ih =>
    rw [writeBytes, ih]
    simp [write]

@[simp] theorem read64_write_local_byte (m : Memory) (frame index base : Nat) (v : Value) :
    read64 (write m (.local frame index) v) (.byte base) = read64 m (.byte base) := by
  simp [read64]

@[simp] theorem read64_initLocals_byte (m : Memory) (frame base : Nat) (values : List Value) :
    read64 (initLocals m frame values) (.byte base) = read64 m (.byte base) := by
  simp [read64]

@[simp] theorem write_local_read_byte (m : Memory) (frame index address : Nat) (v : Value) :
    write m (.local frame index) v (.byte address) = m (.byte address) := by
  simp [write]

theorem write_byte_local_commute (m : Memory) (base frame index : Nat) (byte v : Value) :
    write (write m (.local frame index) v) (.byte base) byte =
      write (write m (.byte base) byte) (.local frame index) v := by
  funext address
  simp only [write]
  by_cases hb : address = .byte base <;> by_cases hl : address = .local frame index
  all_goals simp_all

@[simp] theorem writeBytes_write_local (m : Memory) (base word count frame index : Nat)
    (v : Value) :
    writeBytes (write m (.local frame index) v) base word count =
      write (writeBytes m base word count) (.local frame index) v := by
  induction count generalizing m base word with
  | zero => rfl
  | succ count ih =>
    rw [writeBytes, write_byte_local_commute, ih]
    rfl

end CIL
