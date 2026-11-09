import CIL.Extraction.Generics

/-!
# Argument guard calls

`ArgumentNullException.ThrowIfNull(object, string)` and the integer instances of the
`ArgumentOutOfRangeException` guards emit exactly their guard operation, decoded from the raw
owner, name, type argument, parameter shape and external identity. No other instruction emits a
guard, and a guard call emits nothing else.
-/

namespace CIL.Extraction

/-- The integer type arguments of the guards, with the width and signedness each denotes; the
    native integers take the 64-bit target. -/
private def guardIntegers : List (String × Nat × Bool) :=
  [("System.SByte", 8, true), ("System.Byte", 8, false), ("System.Int16", 16, true),
    ("System.UInt16", 16, false), ("System.Int32", 32, true), ("System.UInt32", 32, false),
    ("System.Int64", 64, true), ("System.UInt64", 64, false), ("System.IntPtr", 64, true),
    ("System.UIntPtr", 64, false)]

/-- The `ArgumentOutOfRangeException` methods that test one value against zero. -/
private def zeroGuards : List (String × ZeroGuard) :=
  [("ThrowIfZero", .zero), ("ThrowIfNegative", .negative),
    ("ThrowIfNegativeOrZero", .negativeOrZero)]

/-- The `ArgumentOutOfRangeException` methods that compare a value with a bound. -/
private def comparisonGuards : List (String × ComparisonGuard) :=
  [("ThrowIfEqual", .equal), ("ThrowIfNotEqual", .notEqual), ("ThrowIfGreaterThan", .greaterThan),
    ("ThrowIfGreaterThanOrEqual", .greaterThanOrEqual), ("ThrowIfLessThan", .lessThan),
    ("ThrowIfLessThanOrEqual", .lessThanOrEqual)]

/-- A guard operation, compared between the raw call and the emitted instruction. -/
private inductive Guard where
  | null
  | zero (guard : ZeroGuard) (width : Nat) (signed : Bool)
  | comparison (guard : ComparisonGuard) (width : Nat) (signed : Bool)
  deriving DecidableEq

/-- The `System.String` parameter name every guard takes last. -/
private def parameterName : TypeExpr := .object runtimeScope "System.String"

/-- The external identity of a guard on `owner` with the given signature tail. -/
private def guardTarget (owner signature : String) : MethodId :=
  .external (runtimeScope ++ "::System.Void " ++ owner ++ "::" ++ signature)

/-- The guard operation a raw call implements, from its metadata alone. -/
private def guardCall (raw : RawInstruction) : Option Guard := do
  if raw.opcode != 40 then none else pure ()
  let .call site := raw.operand | none
  if site.hasThis || site.returnsValue || site.returnType != .void then none else pure ()
  if site.declaringType == .atom runtimeScope "System.ArgumentNullException" then
    let parameters := [.atom runtimeScope "System.Object", parameterName]
    if site.name == "ThrowIfNull" && site.typeArguments.isEmpty &&
        site.parameterCount == 2 && site.parameterTypes == parameters &&
        site.target == guardTarget "System.ArgumentNullException"
          "ThrowIfNull(System.Object,System.String)"
      then some .null else none
  else if site.declaringType == .atom runtimeScope "System.ArgumentOutOfRangeException" then
    let [argument] := site.typeArguments | none
    let .atom scope type := argument | none
    if scope != runtimeScope then none else pure ()
    let (_, width, signed) ← guardIntegers.find? (·.1 == type)
    let owner := "System.ArgumentOutOfRangeException"
    match zeroGuards.find? (·.1 == site.name) with
    | some (name, guard) =>
      if site.parameterCount == 2 && site.parameterTypes == [argument, parameterName] &&
          site.target == guardTarget owner (name ++ "(!!0,System.String)")
        then some (.zero guard width signed) else none
    | none =>
      let (name, guard) ← comparisonGuards.find? (·.1 == site.name)
      if site.parameterCount == 3 &&
          site.parameterTypes == [argument, argument, parameterName] &&
          site.target == guardTarget owner (name ++ "(!!0,!!0,System.String)")
        then some (.comparison guard width signed) else none
  else none

/-- A call to `ArgumentNullException.ThrowIfNull(object, string)`, whose `object` parameter takes
    any object reference. -/
def nullGuardCall (raw : RawInstruction) : Bool :=
  guardCall raw == some .null

/-- The guard an emitted operation performs, if any. -/
private def emittedGuard : Op → Option Guard
  | .memory .throwIfNull => some .null
  | .memory (.zeroGuard guard width signed) => some (.zero guard width signed)
  | .memory (.comparisonGuard guard width signed) => some (.comparison guard width signed)
  | _ => none

/-- A guard operation comes only from its exact call, and a guard call emits only its guard. -/
def guardCallMatches (raw : RawInstruction) (emitted : Op) : Bool :=
  guardCall raw == emittedGuard emitted

end CIL.Extraction
