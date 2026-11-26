import CIL.VectorMemory
import CIL.MemoryLemmas

/-!
# Vector memory lemmas

Frame lemmas for byte-level vector storage: vector reads of caller bytes ignore local writes,
and vector stores into caller bytes leave locals and static data unchanged. Also the
`Unsafe.Add` offset equations.
-/

open CIL

namespace CIL

@[simp] theorem byte_cast_bound (value : Nat) : value % 256 % 4294967296 < 256 := by
  have h := Nat.mod_lt value (by decide : 0 < 256)
  have hle := Nat.mod_le (value % 256) 4294967296
  omega

@[simp] theorem unsafeAdd_static_nonnegative (size offset : Nat) (bytes : List (BitVec 8)) :
    CIL.unsafeAdd size (offset : Int) (.static bytes 0) =
      some (.static bytes (size * offset)) := by
  simp [CIL.unsafeAdd, ← Int.natCast_mul]

@[simp] theorem writeBytes_static (m : Memory) (base word count offset : Nat)
    (bytes : List (BitVec 8)) :
    writeBytes m base word count (.static bytes offset) = m (.static bytes offset) := by
  induction count generalizing m base word with
  | zero => rfl
  | succ count ih => rw [writeBytes, ih]; simp [write]

@[simp] theorem read128_write_local (m : Memory) (frame index base : Nat) (v : Value) :
    read128 (write m (.local frame index) v) (.byte base) = read128 m (.byte base) := by
  simp [read128]

@[simp] theorem read256_write_local (m : Memory) (frame index base : Nat) (v : Value) :
    read256 (write m (.local frame index) v) (.byte base) = read256 m (.byte base) := by
  simp [read256]

@[simp] theorem write128_preserves_local (m : Memory) (base frame index : Nat)
    (bits : BitVec 128) :
    writeBytes m base bits.toNat 16 (.local frame index) = m (.local frame index) := by
  simp

@[simp] theorem write256_preserves_local (m : Memory) (base frame index : Nat)
    (bits : BitVec 256) :
    writeBytes m base bits.toNat 32 (.local frame index) = m (.local frame index) := by
  simp

theorem unsafeAdd_byte_nonnegative (size base offset : Nat) :
    unsafeAdd size (offset : Int) (.byte base) = some (.byte (base + size * offset)) := by
  exact unsafeAdd_byte_natural size base offset

@[simp] theorem unsafeAdd_byte_one (size base : Nat) :
    unsafeAdd size 1 (.byte base) = some (.byte (base + size)) := by
  simpa only [Int.natCast_one, Nat.mul_one] using unsafeAdd_byte_nonnegative size base 1

end CIL
