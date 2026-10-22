import CIL.Safety.MethodContract

namespace ImportFixture
open CIL.Safety

def addOne : MethodContract CIL.W64 CIL.W64 where
  args value := [.scalar (.i64 value)]
  results value := [.scalar (.i64 value)]
  pre _ memory := memory.WellFormed
  footprint _ := []
  post input _ _ output := output = input + 1

end ImportFixture
