import Extracted
import Examples.Support
import CIL.Safety.ByteRoundTrip

open CIL.Safety
namespace ExampleProof

def sourceMemory (x : CIL.W64) : Memory := {
  allocations := fun id => if id < 2 then some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
  cells := fun id offset => if id = 0 then ⟨(numberBytes x.toNat 8)[offset]?.getD 0, true⟩ else ⟨0, false⟩
  views := [⟨0, 0, 8, true, true⟩, ⟨1, 0, 8, true, true⟩]
  nextIdentity := 2
}

/-- Copying a typed 64-bit value into uninitialized destination storage returns
    that value for every input, independently of its bit pattern. -/
theorem correctness (x : CIL.W64) :
    (invoke Extracted.program 8 0 [.reference (.address ⟨1, 0⟩), .reference (.address ⟨0, 0⟩)]
      (sourceMemory x)).map Prod.snd = .ok [.scalar (.i64 x)] := by
  change (Except.ok [Value.scalar (.i64 (BitVec.ofNat 64 (byteNumber (numberBytes x.toNat 8))))] :
    Except LocatedFault (List Value)) = _
  rw [byteNumber_numberBytes]
  simp
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt x.isLt]

#print axioms correctness
end ExampleProof
