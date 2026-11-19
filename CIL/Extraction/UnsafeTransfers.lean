import CIL.Extraction.Generics

/-!
# Checked Unsafe block and vector operations

Block helpers bind their exact signatures and address alignment.
`Vector128.LoadUnsafe<byte>` and `StoreUnsafe<byte>`, with or without a `nuint` offset, are
bound to the one operation that displaces and transfers like `Unsafe.Add` and `load128` or
`store128`.
-/

namespace CIL.Extraction

/-- Whether `Vector128.LoadUnsafe` or `StoreUnsafe` is named, whatever the remaining metadata. -/
def vector128UnsafeFamily (site : CallSite) : Bool :=
  (site.name == "LoadUnsafe" || site.name == "StoreUnsafe") &&
    match site.declaringType with
    | .atom _ owner => owner == "System.Runtime.Intrinsics.Vector128"
    | _ => false

/-- `(store, offset)` of an exact `Vector128.LoadUnsafe<byte>` or `StoreUnsafe<byte>` call,
    checked against its closed types and its open generic identity. -/
def vector128UnsafeCall (raw : RawInstruction) : Option (Bool × Bool) := do
  if raw.opcode != 40 then none else pure ()
  let .call site := raw.operand | none
  if !vector128UnsafeFamily site || site.hasThis then none else pure ()
  let byte := TypeExpr.atom runtimeScope "System.Byte"
  let vectorName := "System.Runtime.Intrinsics.Vector128`1"
  let vector := TypeExpr.apply (.constructor intrinsicsScope vectorName) byte
  let store := site.name == "StoreUnsafe"
  let offset := site.parameterCount == (if store then 3 else 2)
  let offsetType := if offset then [TypeExpr.atom runtimeScope "System.UIntPtr"] else []
  let offsetName := if offset then ",System.UIntPtr" else ""
  let parameters := (if store then [vector] else []) ++ [.byref byte] ++ offsetType
  let parameterNames := (if store then vectorName ++ "<!!0>," else "") ++ "!!0&" ++ offsetName
  let resultName := if store then "System.Void" else vectorName ++ "<!!0>"
  if site.typeArguments == [byte] && site.parameterTypes == parameters &&
      site.parameterCount == parameters.length && site.returnsValue == !store &&
      site.returnType == (if store then .void else vector) &&
      site.target == .external (intrinsicsScope ++ "::" ++ resultName ++
        " System.Runtime.Intrinsics.Vector128::" ++ site.name ++ "(" ++ parameterNames ++ ")")
    then some (store, offset) else none

/-- An exact `Vector128` byte load or store emits its operation; no other instruction may emit
    it, and no other call named like one is admitted. -/
def vector128UnsafeMatches (raw : RawInstruction) : Instruction → Bool
  | .memory (.vector128Unsafe store offset) => vector128UnsafeCall raw == some (store, offset)
  | _ => match raw.operand with
    | .call site => !vector128UnsafeFamily site
    | _ => true

end CIL.Extraction
