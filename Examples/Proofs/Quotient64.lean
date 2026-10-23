import Extracted
import Examples.Support

open CIL CIL.Safety
namespace ExampleProof

/-- Every nonzero divisor yields the natural-number quotient, for all inputs. -/
theorem correctness (x y : W64) (nonzero : y ≠ 0) :
    (CIL.Safety.invoke Extracted.program 4 0
      [.scalar (.i64 x), .scalar (.i64 y)] Examples.empty).map Prod.snd =
        .ok [.scalar (.i64 (BitVec.ofNat 64 (x.toNat / y.toNat)))] := by
  have calculation : divideValues false false (.i64 x) (.i64 y) =
      .ok (.i64 (BitVec.ofNat 64 (x.toNat / y.toNat))) := by
    simp only [divideValues, divideBits, nonzero, ite_false]
    rfl
  simp [Extracted.program, Extracted.method0, CIL.Safety.invoke, CIL.Safety.run,
    CIL.Safety.step, checkedValue, numericValue, enterFrame, makeSelectedLocals, makeLocals,
    observerCount, unspecifiedOperands, CIL.Safety.Value.hasUnspecified, CIL.Value.hasUnspecified,
    makeArgumentHomes, makeParameterHomes, leaveFrame, calculation, List.mapM, List.mapM.loop,
    Bind.bind, Except.bind, Except.mapError, Except.map, Pure.pure, Except.pure]

#print axioms correctness
end ExampleProof
