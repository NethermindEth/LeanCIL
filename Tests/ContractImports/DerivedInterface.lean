import CIL.Safety.OutcomeContract

/-! The public contracts of the derived-export fixture library, published as its interface.
    Each is weaker than the internal contract its producer proves against the actual
    extraction; nothing here names that internal contract or its proof. -/

namespace DerivedInterface
open CIL.Safety

/-- The exception `Percent` throws for an input: none up to 100, otherwise
    `ArgumentOutOfRangeException`. -/
def percentRaises (value : CIL.W64) : Option String :=
  if value ≤ 100 then none else some "System.ArgumentOutOfRangeException"

/-- Public `Percent`: inputs above 100 throw `ArgumentOutOfRangeException`; a returned result
    is only promised to be at most 100, not equal to the input. -/
def percentBounded : OutcomeContract CIL.W64 CIL.W64 where
  args value := [.scalar (.i64 value)]
  results output := [.scalar (.i64 output)]
  pre _ memory := memory.WellFormed
  footprint _ := []
  post _ _ _ output := output ≤ 100
  raises value _ := percentRaises value

/-- The inputs of `AddTo(in left, in right, out sum)`: three word references, the 32-byte
    `region` the caller declares around `sum`, and the words `left` and `right` hold. -/
structure AddInput where
  left : Reference
  right : Reference
  sum : Reference
  region : Reference
  leftValue : CIL.W64
  rightValue : CIL.W64

/-- `AddTo`'s arguments: the three references, in parameter order. -/
def addArguments (input : AddInput) : List Value :=
  [.reference (.address input.left), .reference (.address input.right),
    .reference (.address input.sum)]

/-- Public `AddTo`: it may write anywhere in `region`, stores the sum, and keeps `left`, which
    lies apart from `sum`. -/
def addPublic : MethodContract AddInput where
  args := addArguments
  pre input memory := memory.WellFormed ∧
    read memory input.left 8 1 = .ok (numberBytes input.leftValue.toNat 8) ∧
    read memory input.right 8 1 = .ok (numberBytes input.rightValue.toNat 8) ∧
    access memory input.sum 8 1 true = .ok () ∧
    Apart input.left 8 (input.sum, 8) ∧ Within (input.sum, 8) (input.region, 32)
  footprint input := [(input.region, 32)]
  post input _ final values := values = [] ∧
    read final input.sum 8 1 = .ok (numberBytes (input.leftValue + input.rightValue).toNat 8) ∧
    read final input.left 8 1 = .ok (numberBytes input.leftValue.toNat 8)

end DerivedInterface
