import Extracted
import Examples.Support

namespace ExampleProof

theorem correctness (x : CIL.W64) :
    (CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i64 x)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i64 x)] := by
  change (Except.ok [CIL.Safety.Value.scalar (.i64 ((x.rotateLeft 13).rotateRight 13))] :
    Except CIL.Safety.LocatedFault (List CIL.Safety.Value)) = _
  have identity : (x.rotateLeft 13).rotateRight 13 = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft, Nat.reduceMod, Nat.reduceSub]
    by_cases h : i < 51
    · simp [h, show ¬ (13 + i < 13) by omega, show 13 + i < 64 by omega]
    · simp [h, show i - 51 < 13 by omega, show 51 + (i - 51) = i by omega, hi]
  rw [identity]

#print axioms correctness
end ExampleProof
