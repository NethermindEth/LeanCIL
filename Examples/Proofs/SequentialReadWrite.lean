import Extracted
import Examples.Support
import CIL.Safety.ByteRoundTrip

open CIL.Safety
namespace ExampleProof

/-- A field in an ordinary sequential struct preserves every 32-bit input. -/
theorem correctness (x : CIL.W32) :
    (invoke Extracted.program 8 0 [Examples.reference, .scalar (.i32 x)] Examples.caller).map Prod.snd =
      .ok [.scalar (.i32 x)] := by
  change (Except.ok [Value.scalar (.i32 (BitVec.ofNat 32 (byteNumber (numberBytes x.toNat 4))))] :
    Except LocatedFault (List Value)) = _
  rw [byteNumber_numberBytes]
  simp
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt x.isLt]

#print axioms correctness
end ExampleProof
