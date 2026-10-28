import CIL.Extraction.Generics

/-!
# Exact Unsafe reference helpers

Runtime reference observations and byte offsets reuse checked allocation-relative operations.
The call identity, closed signature and offset signedness are bound independently of emission.
-/

namespace CIL.Extraction

/-- Reference helpers whose runtime signatures have checked allocation-relative meanings. -/
inductive UnsafeReferenceHelper where
  | areSame | less | greater | byteOffset | addBytes (signed : Bool) | subtractBytes
  deriving DecidableEq, Repr

/-- Exact runtime identity and closed types for a two-argument generic Unsafe helper. -/
private def referenceSignature (site : CallSite) (result : TypeExpr)
    (parameters : List TypeExpr) (signature : String) : Bool :=
  site.declaringType == .atom runtimeScope "System.Runtime.CompilerServices.Unsafe" &&
    !site.hasThis && site.parameterCount == 2 && site.returnsValue &&
    site.returnType == result && site.parameterTypes == parameters &&
    site.target == .external (runtimeScope ++ "::" ++ signature)

/-- Recognize exact helper metadata before checking its admitted storage type argument. -/
def unsafeReferenceHelper (instruction : RawInstruction) : Option UnsafeReferenceHelper := do
  if instruction.opcode != 0x28 then none else
    let .call site := instruction.operand | none
    let [type] := site.typeArguments | none
    let reference := TypeExpr.byref type
    let native := TypeExpr.atom runtimeScope "System.IntPtr"
    let unsigned := TypeExpr.atom runtimeScope "System.UIntPtr"
    let boolean := TypeExpr.atom runtimeScope "System.Boolean"
    let pair := [reference, reference]
    if site.name == "AreSame" && referenceSignature site boolean pair
        "System.Boolean System.Runtime.CompilerServices.Unsafe::AreSame(!!0&,!!0&)" then
      some .areSame
    else if site.name == "IsAddressLessThan" && referenceSignature site boolean pair
        "System.Boolean System.Runtime.CompilerServices.Unsafe::IsAddressLessThan(!!0&,!!0&)" then
      some .less
    else if site.name == "IsAddressGreaterThan" && referenceSignature site boolean pair
        "System.Boolean System.Runtime.CompilerServices.Unsafe::IsAddressGreaterThan(!!0&,!!0&)" then
      some .greater
    else if site.name == "ByteOffset" && referenceSignature site native pair
        "System.IntPtr System.Runtime.CompilerServices.Unsafe::ByteOffset(!!0&,!!0&)" then
      some .byteOffset
    else if site.name == "AddByteOffset" && referenceSignature site reference [reference, native]
        "!!0& System.Runtime.CompilerServices.Unsafe::AddByteOffset(!!0&,System.IntPtr)" then
      some (.addBytes true)
    else if site.name == "AddByteOffset" && referenceSignature site reference [reference, unsigned]
        "!!0& System.Runtime.CompilerServices.Unsafe::AddByteOffset(!!0&,System.UIntPtr)" then
      some (.addBytes false)
    else if site.name == "SubtractByteOffset" && referenceSignature site reference [reference, native]
        "!!0& System.Runtime.CompilerServices.Unsafe::SubtractByteOffset(!!0&,System.IntPtr)" then
      some .subtractBytes
    else none

/-- The exact existing operation implementing each reference helper. -/
def UnsafeReferenceHelper.matches : UnsafeReferenceHelper → Op → Bool
  | .areSame, .eq | .less, .ltu | .greater, .gtu | .byteOffset, .memory .byteOffset
  | .subtractBytes, .sub => true
  | .addBytes expected, .memory (.add width signed) => width == 1 && signed == expected
  | _, _ => false

/-- Existing element additions remain separately governed by their layout evidence. -/
def unsafeElementAdd (instruction : RawInstruction) : Bool := Id.run do
  if instruction.opcode != 0x28 then return false
  let .call site := instruction.operand | return false
  let [type] := site.typeArguments | return false
  if site.name != "Add" then return false
  return ["System.Int32", "System.IntPtr", "System.UIntPtr"].any fun offset =>
    referenceSignature site (.byref type) [.byref type, .atom runtimeScope offset]
      ("!!0& System.Runtime.CompilerServices.Unsafe::Add(!!0&," ++ offset ++ ")")

/-- New helper names and byte-add calls cannot escape exact matching through stack effects. -/
def unsafeReferenceRequired (instruction : RawInstruction) (emitted : Op) : Bool :=
  match emitted with
  | .memory .byteOffset => true
  | .call .. => (unsafeReferenceHelper instruction).isSome
  | _ => match instruction.opcode, instruction.operand with
    | 0x28, .call site =>
      (match site.declaringType with
        | .atom _ "System.Runtime.CompilerServices.Unsafe" => true
        | _ => false) && site.name ∈ ["AreSame", "IsAddressLessThan", "IsAddressGreaterThan", "ByteOffset",
        "AddByteOffset", "SubtractByteOffset"] ||
        match emitted with | .memory (.add ..) => !unsafeElementAdd instruction | _ => false
    | _, _ => false

end CIL.Extraction
