import CIL.Extraction.Scalars
import CIL.Extraction.CallLayouts

/-!
# Signatures of lowered runtime overloads

The helpers here compare closed operand types with a specific overload and its raw external
identity. The spelling in an external identity retains the definition's generic placeholders.
-/

namespace CIL.Extraction

/-- A closed static signature and the open runtime signature naming it must both match. -/
def staticRuntimeCall (site : CallSite) (scope signature : String) (result : TypeExpr)
    (parameters arguments : List TypeExpr) : Bool :=
  !site.hasThis && site.ownerArgumentCount == 0 && site.typeArguments == arguments &&
    site.method.genericArity == arguments.length && site.method.methodArguments == arguments &&
    site.parameterTypes == parameters && site.parameterCount == parameters.length &&
    site.returnType == result && site.returnsValue == (result != .void) &&
    site.target == .external (scope ++ "::" ++ signature)

/-- A non-generic static runtime overload whose result and parameters all have closed names. -/
def concreteRuntimeCall (site : CallSite) (scope owner : String) (result : TypeExpr)
    (resultName : String) (parameters : List (TypeExpr × String)) : Bool :=
  staticRuntimeCall site scope (resultName ++ " " ++ owner ++ "::" ++ site.name ++ "(" ++
    ",".intercalate (parameters.map Prod.snd) ++ ")") result (parameters.map Prod.fst) []

end CIL.Extraction
