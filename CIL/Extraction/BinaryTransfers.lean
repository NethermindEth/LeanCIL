import CIL.Extraction.Generics

/-!
# Exact endian-aware integer transfers

BinaryPrimitives span operations retain their integer width, result signedness, byte order
and failure behavior. The 16-, 32-, 64-bit and native integer overloads use the validated 64-bit target.
-/

namespace CIL.Extraction

/-- The semantic choice made by a fixed-width endian-aware transfer. -/
private inductive BinaryTransfer where
  | read (width : Nat) (signed bigEndian trying : Bool)
  | write (width : Nat) (bigEndian trying : Bool)
  deriving DecidableEq

/-- Exact assembly identity for the endian-aware span API. -/
private def binaryScope : String :=
  "System.Memory, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"

/-- Decode a bounded overload family, retaining its complete raw signature. -/
private def binaryCall (raw : RawInstruction) : Option BinaryTransfer := do
  if raw.opcode != 40 then none else pure ()
  let .call site := raw.operand | none
  if site.hasThis || !site.typeArguments.isEmpty || site.declaringType !=
      .atom binaryScope "System.Buffers.Binary.BinaryPrimitives" then none else pure ()
  let (read, trying, suffix) ←
    if site.name.startsWith "TryRead" then some (true, true, site.name.drop 7 |>.toString)
    else if site.name.startsWith "TryWrite" then some (false, true, site.name.drop 8 |>.toString)
    else if site.name.startsWith "Read" then some (true, false, site.name.drop 4 |>.toString)
    else if site.name.startsWith "Write" then some (false, false, site.name.drop 5 |>.toString)
    else none
  let bigEndian := suffix.endsWith "BigEndian"
  let endian := if bigEndian then "BigEndian" else "LittleEndian"
  let (name, width, signed) ←
    [("Int16", 2, true), ("UInt16", 2, false), ("Int32", 4, true),
      ("UInt32", 4, false), ("Int64", 8, true), ("UInt64", 8, false),
      ("IntPtr", 8, true), ("UIntPtr", 8, false)].find?
      (fun (name, _, _) => suffix == name ++ endian)
  let integer := TypeExpr.atom runtimeScope ("System." ++ name)
  let spanName := if read then "System.ReadOnlySpan`1" else "System.Span`1"
  let span := TypeExpr.apply (.constructor runtimeScope spanName) (.atom runtimeScope "System.Byte")
  let parameters := if read && !trying then [span]
    else [span, if read then .byref integer else integer]
  let result := if trying then TypeExpr.atom runtimeScope "System.Boolean"
    else if read then integer else .void
  let resultName := if trying then "System.Boolean" else if read then "System." ++ name
    else "System.Void"
  let parameterNames := spanName ++ "<System.Byte>" ++
    (if read && !trying then "" else ",System." ++ name ++ (if read then "&" else ""))
  if site.parameterTypes != parameters || site.parameterCount != parameters.length ||
      site.returnType != result || site.returnsValue != (read || trying) ||
      site.target != .external (binaryScope ++ "::" ++ resultName ++
        " System.Buffers.Binary.BinaryPrimitives::" ++ site.name ++ "(" ++ parameterNames ++ ")")
    then none
  else if read then some (.read width signed bigEndian trying)
    else some (.write width bigEndian trying)

/-- Covered transfers cannot be forged from another call with the same stack effect. -/
def binaryTransferMatches (raw : RawInstruction) (emitted : Op) : Bool :=
  let expected := binaryCall raw
  let actual := match emitted with
    | .memory (.binaryRead width signed bigEndian trying) =>
      some (.read width signed bigEndian trying)
    | .memory (.binaryWrite width bigEndian trying) => some (.write width bigEndian trying)
    | _ => none
  expected == actual

end CIL.Extraction
