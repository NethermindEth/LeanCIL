import CIL.Extraction.UnsafeTransfers

/-!
# Exact byte-span value transfers

`Vector128.Create<byte>` and `Vector256.Create<byte>` over a byte span are the same checked
read of the vector, including the `ArgumentOutOfRangeException` for a short span.
-/

namespace CIL.Extraction

/-- The vector type a byte-span vector construction produces, by transfer shape. -/
private def spanVectorOwner : TransferKind → Option String
  | .snapshot .vector128 => some "System.Runtime.Intrinsics.Vector128"
  | .snapshot .vector256 => some "System.Runtime.Intrinsics.Vector256"
  | _ => none

/-- A call to `Vector128.Create<byte>` or `Vector256.Create<byte>` taking one read-only span,
    by owner, name, type argument and parameter shape alone. -/
def byteSpanCreateFamily (site : CallSite) : Bool :=
  site.name == "Create" && site.typeArguments == [.atom runtimeScope "System.Byte"] &&
  (site.declaringType == .atom intrinsicsScope "System.Runtime.Intrinsics.Vector128" ||
    site.declaringType == .atom intrinsicsScope "System.Runtime.Intrinsics.Vector256") &&
  match site.parameterTypes with
  | [.apply (.constructor _ "System.ReadOnlySpan`1") _] => true
  | _ => false

/-- An exact byte-span vector construction agrees with the checked read of its vector. -/
def byteSpanCreateMatches (raw : RawInstruction) (kind : TransferKind) : Bool :=
  Id.run do
  if raw.opcode != 40 then return false
  let .call site := raw.operand | return false
  let some owner := spanVectorOwner kind | return false
  let byte := TypeExpr.atom runtimeScope "System.Byte"
  let span := TypeExpr.apply (.constructor runtimeScope "System.ReadOnlySpan`1") byte
  let vector := TypeExpr.apply (.constructor intrinsicsScope (owner ++ "`1")) byte
  return site.declaringType == .atom intrinsicsScope owner && site.name == "Create" &&
    !site.hasThis && site.typeArguments == [byte] && site.parameterCount == 1 &&
    site.parameterTypes == [span] && site.returnType == vector && site.returnsValue &&
    site.target == .external (intrinsicsScope ++ "::" ++ owner ++ "`1<!!0> " ++ owner ++
      "::Create(System.ReadOnlySpan`1<!!0>)")

end CIL.Extraction
