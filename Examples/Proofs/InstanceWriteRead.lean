import Extracted
import Examples.Support
import CIL.Safety.ByteRoundTrip

open CIL.Safety
namespace ExampleProof

/-- Mutating a struct through its managed `this` reference preserves every input bit. -/
theorem correctness (x : CIL.W64) :
    (invoke Extracted.program 8 0 [Examples.reference, .scalar (.i64 x)] Examples.caller).map Prod.snd =
      .ok [.scalar (.i64 x)] := by
  change (Except.ok [Value.scalar (.i64 (BitVec.ofNat 64 (byteNumber (numberBytes x.toNat 8))))] :
    Except LocatedFault (List Value)) = _
  rw [byteNumber_numberBytes]
  simp
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt x.isLt]

#print axioms correctness
end ExampleProof
