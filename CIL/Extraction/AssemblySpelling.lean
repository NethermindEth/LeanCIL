import CIL.Identity

/-!
# Assembly identity spelling

Assembly references and scoped type names use the same UTF-8 display name for a typed assembly
identity. The spelling includes its version, culture and public key token.
-/

namespace CIL.Extraction

/-- The bytes of a string literal, for comparison with heap entries. -/
def bytesOf (text : String) : List Nat := text.toByteArray.data.toList.map UInt8.toNat

/-- The decimal ASCII digits of a number below `10 ^ fuel`. -/
def decimalDigits : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, value =>
    if value < 10 then [48 + value] else decimalDigits fuel (value / 10) ++ [48 + value % 10]

/-- The 16 lowercase hexadecimal digits of the eight bytes of a public key token. -/
def hexDigits : List Nat → List Nat
  | [] => []
  | byte :: rest =>
    let digit (value : Nat) : Nat := if value < 10 then 48 + value else 87 + value
    digit (byte / 16) :: digit (byte % 16) :: hexDigits rest

/-- The fixed words of an assembly identity as bytes: `, Version=`, `, Culture=`, `neutral`,
    `, PublicKeyToken=` and `null`. They are byte lists, not strings, so the kernel never
    evaluates a string literal to read an identity. -/
def versionMarker : List Nat := [44, 32, 86, 101, 114, 115, 105, 111, 110, 61]
def cultureMarker : List Nat := [44, 32, 67, 117, 108, 116, 117, 114, 101, 61]
def neutralCulture : List Nat := [110, 101, 117, 116, 114, 97, 108]
def tokenMarker : List Nat :=
  [44, 32, 80, 117, 98, 108, 105, 99, 75, 101, 121, 84, 111, 107, 101, 110, 61]
def nullToken : List Nat := [110, 117, 108, 108]

/-- The text of an assembly name as Cecil writes it:
    `Name, Version=a.b.c.d, Culture=culture, PublicKeyToken=token`. -/
def assemblySpelling (name : List Nat) (major minor build revision : Nat)
    (culture token : List Nat) :
    List Nat :=
  name ++ versionMarker ++ decimalDigits 5 major ++ [46] ++ decimalDigits 5 minor ++ [46] ++
    decimalDigits 5 build ++ [46] ++ decimalDigits 5 revision ++ cultureMarker ++
    (if culture.isEmpty then neutralCulture else culture) ++ tokenMarker ++ token

/-- The eight bytes of a public key token, in the order an `AssemblyRef` row stores them. -/
def tokenBytes (token : Nat) : List Nat :=
  (List.range 8).reverse.map fun index => (token >>> (8 * index)) % 256

/-- The display bytes of an assembly as Cecil writes them:
    `Name, Version=a.b.c.d, Culture=culture, PublicKeyToken=token`. Spelled type heads carry
    them as their scope; slices and pins are compared as `AssemblyName` values instead. -/
def _root_.CIL.AssemblyName.spelling (assembly : AssemblyName) : List Nat :=
  let version := assembly.version
  assemblySpelling (assembly.name.bytes?.getD []) version.major version.minor version.build
    version.revision (assembly.culture.bytes?.getD [])
    (match assembly.publicKeyToken with
     | some token => hexDigits (tokenBytes token)
     | none => nullToken)

/-- The spelling has no colon, so `spelling ++ "::"` begins the type names of one spelling only. -/
def _root_.CIL.AssemblyName.colonFree (assembly : AssemblyName) : Bool :=
  !assembly.spelling.contains 58

/-- `scope` is `assembly`'s colon-free spelling, as a scoped type identity's text names its
    assembly. -/
def _root_.CIL.AssemblyName.spelledAs (assembly : AssemblyName) (scope : String) : Bool :=
  assembly.colonFree && assembly.spelling == bytesOf scope

end CIL.Extraction
