import CIL.Safety.MethodContract

namespace CIL
def importedPost (input output : W64) : Prop := output = input + 1
end CIL

namespace ImportFixture
open CIL.Safety

def addOne : MethodContract CIL.W64 CIL.W64 where
  args value := [.scalar (.i64 value)]
  results value := [.scalar (.i64 value)]
  pre _ memory := memory.WellFormed
  footprint _ := []
  post input _ _ output := CIL.importedPost input output

end ImportFixture
