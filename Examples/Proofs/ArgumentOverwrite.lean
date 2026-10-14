import Extracted
import Examples.Support
import CIL.Safety.ByteRoundTrip

open CIL.Safety
namespace ExampleProof

/-- Reassigning a by-value argument returns the replacement for every input. -/
theorem correctness (original replacement : CIL.W32) :
    (invoke Extracted.program 8 0 [.scalar (.i32 original), .scalar (.i32 replacement)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i32 replacement)] := by
  change (Except.ok [Value.scalar (.i32 (BitVec.ofNat 32 (byteNumber (numberBytes replacement.toNat 4))))] :
    Except LocatedFault (List Value)) = _
  rw [byteNumber_numberBytes]
  simp
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt replacement.isLt]

#print axioms correctness
end ExampleProof
