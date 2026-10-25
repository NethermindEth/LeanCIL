import CIL.Safety.MethodContract

namespace TypedImportInterface
open CIL.Safety

def identity : MethodContract CIL.W64 CIL.W64 where
  args value := [.scalar (.i64 value)]
  results value := [.scalar (.i64 value)]
  pre _ memory := memory.WellFormed
  footprint _ := []
  post input _ _ output := output = input

/-- The nested public Pair contains one UInt64; source and destination may alias. -/
def copy : MethodContract (Reference × Reference × CIL.W64) Unit where
  args input := [.reference (.address input.1), .reference (.address input.2.1)]
  results _ := []
  pre input memory := memory.WellFormed ∧
    read memory input.1 8 1 = .ok (numberBytes input.2.2.toNat 8) ∧
    access memory input.2.1 8 1 true = .ok ()
  footprint input := [(input.2.1, 8)]
  post input _ final _ := read final input.2.1 8 1 = .ok (numberBytes input.2.2.toNat 8)

end TypedImportInterface
