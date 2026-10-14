import Extracted
import Examples.Support

namespace ExampleProof

-- The independently stated specification is reduction modulo 65536.
theorem correctness (x : CIL.W32) :
    ∃ result : CIL.W32,
      (CIL.Safety.invoke Extracted.program 3 0
        [.scalar (.i32 x)] Examples.empty).map Prod.snd = .ok [.scalar (.i32 result)] ∧
      result.toNat = x.toNat % 65536 := by
  refine ⟨(x.setWidth 16).zeroExtend 32, rfl, ?_⟩
  simp
  omega

#print axioms correctness
end ExampleProof
