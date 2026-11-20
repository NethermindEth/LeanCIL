import CIL.Safety.MethodContract

/-! The compiled AVX2 byte-shuffle contract and the input that distinguishes two incorrect
implementations. Both spans may start at arbitrary addresses and may overlap. -/

namespace Tests.ShuffleContract
open CIL.Safety

/-- A byte span and the 32 initialized bytes available at its start. -/
structure InputSpan where
  address : Reference
  length : Nat
  bits : BitVec 256

/-- A readonly span of bytes in caller memory. -/
def byteSpan (reference : Reference) (length : Nat) : SpanView :=
  ⟨.address reference, length, 1, false⟩

/-- The span is valid, long enough, and its first 32 bytes are readable in caller memory. -/
def readable (span : InputSpan) (memory : Memory) : Prop :=
  (byteSpan span.address span.length).validate memory = .ok () ∧ 32 ≤ span.length ∧
    loadSnapshot memory (.address span.address) .vector256 = .ok (.v256 span.bits)

/-- Shuffle each 128-bit half independently, zeroing bytes whose control has bit 7 set. -/
def shuffle : MethodContract (InputSpan × InputSpan) (BitVec 256) where
  args input := [.bufferSpan (byteSpan input.1.address input.1.length),
    .bufferSpan (byteSpan input.2.address input.2.length)]
  results value := [.scalar (.v256 value)]
  pre input memory := readable input.1 memory ∧ readable input.2 memory
  footprint _ := []
  post input before after value := after = before ∧
    value = CIL.Vector.shuffleBytes256 input.1.bits input.2.bits

/-- Vector construction from a readable span leaves memory and the rest of the stack intact. -/
theorem read_span (memory : Memory) (s : Reference) (n : Nat) (bits : BitVec 256)
    (valid : (byteSpan s n).validate memory = .ok ()) (enough : 32 ≤ n)
    (loaded : loadSnapshot memory (.address s) .vector256 = .ok (.v256 bits))
    (rest : List Value) :
    memoryInstruction (.marshalRead (.snapshot .vector256) false)
        (.bufferSpan (byteSpan s n) :: rest)
      memory = .ok (memory, .scalar (.v256 bits) :: rest) := by
  simp [memoryInstruction, otherMemoryInstruction, loadTransfer, valid, checkedAt,
    byteSpan, CIL.MemoryOp.argumentCount, unspecifiedOperands, Value.hasUnspecified,
    CIL.TransferKind.width, CIL.SnapshotShape.width, Nat.not_lt.mpr enough, loaded] at *
  rfl
#print axioms read_span

/-- A vector with the same byte at every position of each 128-bit half. -/
def halves (low high : BitVec 8) : BitVec 256 :=
  let repeated (byte : BitVec 8) : BitVec 128 :=
    byte.zeroExtend 128 * 0x01010101010101010101010101010101
  repeated high ++ repeated low

/-- Source bytes are one in the low half and two in the high half. The low control half masks
    every byte and the high control half selects its first source byte. -/
def witness : InputSpan × InputSpan :=
  (⟨⟨0, 0⟩, 32, halves 1 2⟩, ⟨⟨1, 0⟩, 32, halves 0x80 0⟩)

/-- The source and control occupy separate live readonly regions of 32 initialized bytes. -/
def witnessMemory : Memory := { Memory.empty with
  allocations := fun id => if id < 2 then some ⟨.callerStack, ⟨32, 1, []⟩, true, [32]⟩ else none
  cells := fun id offset => ⟨if id == 0 then (if offset < 16 then 1 else 2)
    else (if offset < 16 then 0x80 else 0), true⟩
  views := [⟨0, 0, 32, true, false⟩, ⟨1, 0, 32, true, false⟩]
  nextIdentity := 2 }

/-- Both spans satisfy the contract's bounds and initialized-read requirements. -/
theorem witness_ready : shuffle.pre witness witnessMemory :=
  ⟨⟨rfl, by decide, rfl⟩, ⟨rfl, by decide, rfl⟩⟩
#print axioms witness_ready

/-- The wrong vector from a terminating compiled call refutes the contract at this input. -/
theorem refuted_of_shuffle {program : CIL.Program} {fuel : Nat} {actual : BitVec 256}
    (different : actual ≠ halves 0 2)
    (ran : invoke program fuel 0 (shuffle.args witness) witnessMemory =
      .ok (witnessMemory, [.scalar (.v256 actual)])) : shuffle.Refuted program 0 := by
  apply MethodContract.Refuted.of_return (c := shuffle) (input := witness) witness_ready ran
  rintro ⟨_, value, encoded, _, rfl⟩
  have expected : CIL.Vector.shuffleBytes256 witness.1.bits witness.2.bits = halves 0 2 := by
    decide +kernel
  change [Value.scalar (.v256 actual)] =
    [Value.scalar (.v256 (CIL.Vector.shuffleBytes256 witness.1.bits witness.2.bits))] at encoded
  rw [expected] at encoded
  exact different (by simpa using encoded)
#print axioms refuted_of_shuffle

end Tests.ShuffleContract
