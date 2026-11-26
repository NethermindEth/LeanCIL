import CIL.Safety.MethodContract

/-! Contracts for the compiled SSSE3 and AVX2 byte shuffles. The source and control spans
may start at arbitrary addresses and may overlap. -/

namespace Tests.ShuffleContract
open CIL.Safety

/-- A byte span and the vector of initialized bytes at its start. -/
structure InputSpan (bitsize : Nat) where
  address : Reference
  length : Nat
  bits : BitVec bitsize

/-- A readonly span of bytes in caller memory. -/
def byteSpan (reference : Reference) (length : Nat) : SpanView :=
  ⟨.address reference, length, 1, false⟩

/-- The span contains a readable, initialized vector of the required shape. -/
def readable {n : Nat} (shape : CIL.SnapshotShape) (pack : BitVec n → CIL.Value)
    (span : InputSpan n) (memory : Memory) : Prop :=
  (byteSpan span.address span.length).validate memory = .ok () ∧ shape.width ≤ span.length ∧
    loadSnapshot memory (.address span.address) shape = .ok (pack span.bits)

private def shuffleContract {n : Nat} (shape : CIL.SnapshotShape) (pack : BitVec n → CIL.Value)
    (permute : BitVec n → BitVec n → BitVec n) :
    MethodContract (InputSpan n × InputSpan n) (BitVec n) where
  args input := [.bufferSpan (byteSpan input.1.address input.1.length),
    .bufferSpan (byteSpan input.2.address input.2.length)]
  results value := [.scalar (pack value)]
  pre input memory := readable shape pack input.1 memory ∧ readable shape pack input.2 memory
  footprint _ := []
  post input before after value := after = before ∧
    value = permute input.1.bits input.2.bits

/-- AVX2 shuffles the two 128-bit halves independently. -/
def shuffle := shuffleContract .vector256 .v256 CIL.Vector.shuffleBytes256

/-- SSSE3 selects a source byte by the low nibble of each control byte and zeros masked bytes. -/
def shuffle128 := shuffleContract .vector128 .v128 CIL.Vector.shuffleBytes128

/-- Vector construction from a readable span leaves memory and the rest of the stack intact. -/
theorem read_span (memory : Memory) (s : Reference) (n : Nat) (value : CIL.Value) {shape : CIL.SnapshotShape}
    (valid : (byteSpan s n).validate memory = .ok ()) (enough : shape.width ≤ n)
    (loaded : loadSnapshot memory (.address s) shape = .ok value)
    (rest : List Value) :
    memoryInstruction (.marshalRead (.snapshot shape) false)
        (.bufferSpan (byteSpan s n) :: rest)
      memory = .ok (memory, .scalar value :: rest) := by
  unfold byteSpan at valid
  simp [memoryInstruction, otherMemoryInstruction, loadTransfer, valid, checkedAt,
    byteSpan, CIL.MemoryOp.argumentCount, unspecifiedOperands, Value.hasUnspecified,
    CIL.TransferKind.width, Nat.not_lt.mpr enough, loaded]
  rfl
#print axioms read_span

/-- A vector with the same byte at every position of each 128-bit half. -/
def halves (low high : BitVec 8) : BitVec 256 :=
  let repeated (byte : BitVec 8) : BitVec 128 :=
    byte.zeroExtend 128 * 0x01010101010101010101010101010101
  repeated high ++ repeated low

/-- Source bytes are one in the low half and two in the high half. The low control half masks
    every byte and the high control half selects its first source byte. -/
def witness : InputSpan 256 × InputSpan 256 :=
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

/-- The 16-byte source contains ones and the control masks every byte. -/
def witness128 : InputSpan 128 × InputSpan 128 :=
  (⟨⟨0, 0⟩, 16, 0x01010101010101010101010101010101⟩,
   ⟨⟨1, 0⟩, 16, 0x80808080808080808080808080808080⟩)

/-- Reversing the operands selects masked control bytes as data and returns them unchanged. -/
theorem refuted_of_reversed128 {program : CIL.Program} {fuel : Nat}
    (ran : invoke program fuel 0 (shuffle128.args witness128) witnessMemory =
      .ok (witnessMemory, [.scalar (.v128 witness128.2.bits)])) :
    shuffle128.Refuted program 0 := by
  have ready : shuffle128.pre witness128 witnessMemory :=
    ⟨⟨rfl, by decide, rfl⟩, ⟨rfl, by decide, rfl⟩⟩
  apply MethodContract.Refuted.of_return (c := shuffle128) (input := witness128) ready ran
  rintro ⟨_, value, encoded, _, rfl⟩
  change [Value.scalar (.v128 witness128.2.bits)] =
    [Value.scalar (.v128 (CIL.Vector.shuffleBytes128 witness128.1.bits witness128.2.bits))] at encoded
  exact (by decide +kernel : witness128.2.bits ≠
    CIL.Vector.shuffleBytes128 witness128.1.bits witness128.2.bits) (by simpa using encoded)
#print axioms refuted_of_reversed128

end Tests.ShuffleContract
