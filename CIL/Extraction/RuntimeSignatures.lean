import CIL.Extraction.Scalars
import CIL.Extraction.IntegerMath

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

/-- The closed tuple resulting from DivRem, with its fields at offsets zero and one word. -/
def integerPairResult (environment : CallLayouts) (type : TypeExpr)
    (name : String) (width : Nat) : Bool :=
  match type with
  | .aggregate identity index =>
    let expected := runtimeScope ++ "::System.ValueTuple`2<" ++ name ++ "," ++ name ++ ">"
    let validRaw := (environment.indexedRaw[index]?).any fun raw =>
      match raw.fields with
      | [first, second] => raw.identity == identity && raw.packing <= 0 &&
        (primitiveField name).any fun kind => first.type == kind && second.type == kind
      | _ => false
    identity == expected && validRaw &&
      (environment.layouts[index]?).any fun entry =>
        entry.alignment == width && entry.layout.size == 2 * width && match entry.layout.fields with
        | [first, second] => first.offset == 0 && first.width == width &&
          second.offset == width && second.width == width && !first.aggregate && !second.aggregate
        | _ => false
  | _ => false

/-- Exact BigMul and DivRem overloads, including tuple results and out-parameter writes. -/
def integerMathInstruction (environment : CallLayouts) (site : CallSite) :
    Option Instruction := do
  let some (type@(.atom scope name)) := site.parameterTypes.head? | none
  guard (scope == runtimeScope)
  let (width, signed) ← mathIntegers.lookup name
  let operand := (type, name)
  let pair := [operand, operand]
  let out := pair ++ [(.byref type, name ++ "&")]
  let signature := concreteRuntimeCall site runtimeScope "System.Math"
  if site.name == "BigMul" then
    if width == 32 then
      let result := if signed then "System.Int64" else "System.UInt64"
      guard (signature (.atom runtimeScope result) result pair)
      return .intrinsic (.scalar (.bigMul32 signed)) 2
    else
      guard (name ∈ ["System.Int64", "System.UInt64"] && signature type name out)
      return .memory (.bigMul64 signed)
  else
    guard (site.name == "DivRem")
    if site.parameterCount == 3 then
      guard (name ∈ ["System.Int32", "System.Int64"] && signature type name out)
      return .memory (.divRemOut width)
    else
      guard (integerPairResult environment site.returnType name (width / 8))
      guard (signature site.returnType ("System.ValueTuple`2<" ++ name ++ "," ++ name ++ ">") pair)
      return .intrinsic (.scalar (.divRem width signed)) 2

end CIL.Extraction
