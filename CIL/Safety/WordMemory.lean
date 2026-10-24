import CIL.Safety.ByteEncoding
import CIL.Safety.WriteEffects
import CIL.Safety.Frames

/-!
# Word loads and stores

How encoded numbers read back through the checked interpreter: an initialized read of
`numberBytes x width` loads as `x` at every scalar and vector width, and a numeric local
can be stored with write access alone. The word lemmas are the base case the stepping
lemmas for locals and fields build on.
-/

namespace CIL.Safety

/-- Decoding the eight-byte little-endian encoding of a word gives the word back. -/
theorem decode_word64 (word : BitVec 64) :
    BitVec.ofNat 64 (byteNumber (numberBytes word.toNat 8)) = word := by
  rw [byteNumber_numberBytes]
  have bound : word.toNat < 256^8 := word.isLt
  rw [Nat.mod_eq_of_lt bound]
  simp

theorem load_word64_of_read {memory : Memory} {reference : Reference} {word : BitVec 64}
    (loaded : read memory reference 8 1 = .ok (numberBytes word.toNat 8)) :
    loadValue memory (.address reference) 8 = .ok (.i64 word) := by
  simp [loadValue, dereference, loaded, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure, decode_word64]

/-- What an unsigned `loadValue` of `width` bytes returns for the decoded `number`; meaningful
    only at a `ScalarWidth`. -/
def numericOfWidth (width number : Nat) : CIL.Value :=
  match width with
  | 1 | 2 | 4 => .i32 (BitVec.ofNat 32 number)
  | 8 => .i64 (BitVec.ofNat 64 number)
  | 16 => .v128 (BitVec.ofNat 128 number)
  | 32 => .v256 (BitVec.ofNat 256 number)
  | _ => .v512 (BitVec.ofNat 512 number)

/-- The widths `loadValue` decodes as one scalar or vector. -/
abbrev ScalarWidth (width : Nat) : Prop :=
  width = 1 ∨ width = 2 ∨ width = 4 ∨ width = 8 ∨ width = 16 ∨ width = 32 ∨ width = 64

/-- An initialized read at any scalar width decodes its bytes; the vector widths never fall
    back to snapshots. -/
theorem loadValue_of_read {memory : Memory} {reference : Reference} {width : Nat}
    {bytes : List (BitVec 8)}
    (scalar : ScalarWidth width) (loaded : read memory reference width 1 = .ok bytes) :
    loadValue memory (.address reference) width =
      .ok (numericOfWidth width (byteNumber bytes)) := by
  rcases scalar with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [loadValue, dereference, loaded, checkedAt, Except.mapError, numericOfWidth,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A width-generic `load_word64_of_read`: an encoded `width`-byte value loads as itself. -/
theorem load_scalar_of_read {memory : Memory} {reference : Reference} {width : Nat}
    {x : BitVec (8 * width)} (scalar : ScalarWidth width)
    (loaded : read memory reference width 1 = .ok (numberBytes x.toNat width)) :
    loadValue memory (.address reference) width = .ok (numericOfWidth width x.toNat) := by
  have bound : x.toNat < 256 ^ width := by have := x.isLt; rwa [Nat.pow_mul] at this
  rw [loadValue_of_read scalar loaded, byteNumber_numberBytes, Nat.mod_eq_of_lt bound]

theorem load_local_word64_of_read {memory : Memory} {reference : Reference} {word : BitVec 64}
    (loaded : read memory reference 8 1 = .ok (numberBytes word.toNat 8)) :
    loadLocal memory (.bytes .word64 reference) = .ok (.scalar (.i64 word)) := by
  change (do
    let bytes ← checkedAt (.address reference) 8 (read memory reference 8 1)
    pure (Value.scalar (.i64 (BitVec.ofNat 64 (byteNumber bytes)))) : ExecutionResult Value) = _
  simp only [loaded, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure, decode_word64]

/-- Numeric local storage requires write access but no prior initialization. -/
theorem store_local_word64 {memory : Memory} {reference : Reference} (word : BitVec 64)
    (ready : access memory reference 8 1 true = .ok ()) :
    ∃ result,
      write memory reference (numberBytes word.toNat 8) 1 = .ok result ∧
      storeLocal memory (.bytes .word64 reference) (.scalar (.i64 word)) =
        .ok (.bytes .word64 reference, result) ∧
      read result reference 8 1 = .ok (numberBytes word.toNat 8) ∧
      loadLocal result (.bytes .word64 reference) = .ok (.scalar (.i64 word)) := by
  have length : (numberBytes word.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨result, written⟩ := write_succeeds (bytes := numberBytes word.toNat 8)
    (by simpa only [length] using ready)
  have readback := write_readback _ _ _ _ _ written
  rw [length] at readback
  refine ⟨result, written, ?_, readback, load_local_word64_of_read readback⟩
  simp only [storeLocal, Value.hasUnspecified, CIL.Value.hasUnspecified, Bool.false_and,
    Bool.false_eq_true, ite_false, localNumber, localWidth, written, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms decode_word64
#print axioms load_word64_of_read
#print axioms loadValue_of_read
#print axioms load_scalar_of_read
#print axioms load_local_word64_of_read
#print axioms store_local_word64

end CIL.Safety
