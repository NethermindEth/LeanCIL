import Extracted
import Examples.Support

open CIL CIL.Safety
namespace ExampleProof

/-- Every nonzero divisor yields the natural-number quotient, for all inputs. -/
theorem correctness (x y : W32) (nonzero : y ≠ 0) :
    (CIL.Safety.invoke Extracted.program 4 0
      [.scalar (.i32 x), .scalar (.i32 y)] Examples.empty).map Prod.snd =
        .ok [.scalar (.i32 (BitVec.ofNat 32 (x.toNat / y.toNat)))] := by
  have calculation : divideValues false false (.i32 x) (.i32 y) =
      .ok (.i32 (BitVec.ofNat 32 (x.toNat / y.toNat))) := by
    simp only [divideValues, divideBits, nonzero, ite_false]
    rfl
  simp [Extracted.program, Extracted.method0, CIL.Safety.invoke, CIL.Safety.run,
    CIL.Safety.step, checkedValue, numericValue, enterFrame, makeLocals,
    makeArgumentHomes, makeParameterHomes, leaveFrame, calculation, List.mapM, List.mapM.loop,
    Bind.bind, Except.bind, Except.mapError, Except.map, Pure.pure, Except.pure]

#print axioms correctness
end ExampleProof
