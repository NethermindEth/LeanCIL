import Extracted
import CIL.Safety.ByteRoundTrip

open CIL.Safety
namespace ExampleProof

/-- Caller memory with one readable and writable 8-byte allocation, identity 0. -/
def callerMemory : CIL.Safety.Memory where
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 8, true, true⟩]
  nextIdentity := 1

/-- A reference to the start of `callerMemory`'s allocation. -/
def callerReference : CIL.Safety.Value := .reference (.address ⟨0, 0⟩)

/-- Mutating a struct through its managed `this` reference preserves every input bit. -/
theorem correctness (x : CIL.W64) :
    (invoke Extracted.program 8 0 [callerReference, .scalar (.i64 x)] callerMemory).map Prod.snd =
      .ok [.scalar (.i64 x)] := by
  change (Except.ok [Value.scalar (.i64 (BitVec.ofNat 64 (byteNumber (numberBytes x.toNat 8))))] :
    Except LocatedFault (List Value)) = _
  rw [byteNumber_numberBytes]
  simp
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt x.isLt]

#print axioms correctness
end ExampleProof
