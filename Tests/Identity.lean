import CIL.Identity
import Std.Data.TreeMap

/-!
# Typed identity tests

Pins how identities print, compare and hash: the display text of each kind and its fallbacks,
`name!` and `str!` round trips and escapes, goals and `#print` output in `name!` and `type!`
form, raw structures for codes that spell no text or hide a component, the codec theorems and
their axioms, and equality decided on codes, including types whose dotted text coincides and
nested types that differ in one level's namespace.
-/

namespace Tests.Identity

open CIL

/-- The core library assembly of .NET 11. -/
def runtime : AssemblyName :=
  { name := name!"System.Runtime", version := ⟨11, 0, 0, 0⟩, culture := name!"",
    publicKeyToken := some 0xb03f5f7f11d50a3a }

/-- An application assembly with a neutral culture and a null public key token. -/
def examples : AssemblyName :=
  { name := name!"Examples", version := ⟨1, 0, 0, 0⟩, culture := name!"",
    publicKeyToken := none }

/-- A type in a namespace. -/
def pointType : TypeIdentity :=
  { assembly := examples, typeNamespace := name!"Examples", name := name!"Point" }

/-- A generic type nested in a generic type; as C# emits it, only the outer one has a namespace. -/
def enumeratorType : TypeIdentity :=
  { assembly := runtime, typeNamespace := name!"",
    enclosing := [⟨name!"System.Collections.Generic", name!"List`1"⟩], name := name!"Enumerator" }

-- Each kind displays as a reader writes it.
/-- info: "System.Collections" -/
#guard_msgs in
#eval (name!"System.Collections").display

/-- info: "a \"quoted\" line" -/
#guard_msgs in
#eval (str!"a \"quoted\" line").display

/-- info: "11.0.0.0" -/
#guard_msgs in
#eval runtime.version.display

/-- info: "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" -/
#guard_msgs in
#eval runtime.display

/-- info: "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" -/
#guard_msgs in
#eval examples.display

/-- info: "Examples, Version=1.0.0.0, Culture=en-US, PublicKeyToken=000000000000beef" -/
#guard_msgs in
#eval ({ examples with culture := name!"en-US", publicKeyToken := some 0xbeef }).display

-- A type shows its whole assembly scope: name and version, and culture and token when either
-- is not neutral or null.
/-- info: "[Examples,1.0.0.0]Examples.Point" -/
#guard_msgs in
#eval pointType.display

#guard enumeratorType.display == "[System.Runtime,11.0.0.0,neutral,b03f5f7f11d50a3a]" ++
  "System.Collections.Generic.List`1/Enumerator"

/-- info: "[Examples,1.0.0.0,en-US,null]Global" -/
#guard_msgs in
#eval ({ assembly := { examples with culture := name!"en-US" }, typeNamespace := name!"",
          name := name!"Global" } : TypeIdentity).display

/-- info: "System.Int32" -/
#guard_msgs in
#eval PrimitiveType.int32.display

/-- info: 8 -/
#guard_msgs in
#eval PrimitiveType.int32.elementType

/-- info: CIL.TypeKind.enumType (CIL.PrimitiveType.uint16) -/
#guard_msgs in
#eval TypeKind.enumType .uint16

-- An unapplied constructor prints unchanged; only applied literals take the notation.
/-- info: MetadataName.mk : Nat → MetadataName -/
#guard_msgs in
#check (MetadataName.mk)

/-- info: UserString.mk : Nat → UserString -/
#guard_msgs in
#check (UserString.mk)

-- Under `open CIL` the type of type identities is unambiguous and prints unqualified.
/-- info: fun type => type.name : TypeIdentity → MetadataName -/
#guard_msgs in
#check fun type : TypeIdentity => type.name

-- Terms print in the notation that wrote them.
/-- info: name!"Int32" : MetadataName -/
#guard_msgs in
#check name!"Int32"

/-- info: str!"hello" : UserString -/
#guard_msgs in
#check str!"hello"

/-- info: type!"[Examples,1.0.0.0]Examples.Point" : TypeIdentity -/
#guard_msgs in
#check ({ assembly := examples, typeNamespace := name!"Examples", name := name!"Point" } :
  TypeIdentity)

/-- A signed assembly with a short name, so its types print within one line. -/
def signed : AssemblyName :=
  { name := name!"Lib", version := ⟨4, 2, 0, 1⟩, culture := name!"",
    publicKeyToken := some 0xb03f5f7f11d50a3a }

/-- info: type!"[Lib,4.2.0.1,neutral,b03f5f7f11d50a3a]N.Outer/Inner" : TypeIdentity -/
#guard_msgs in
#check ({ assembly := signed, typeNamespace := name!"", enclosing := [⟨name!"N", name!"Outer"⟩],
          name := name!"Inner" } : TypeIdentity)

/-- info: def Tests.Identity.pointType : TypeIdentity :=
type!"[Examples,1.0.0.0]Examples.Point" -/
#guard_msgs in
#print pointType

-- Another pinned version of the assembly prints as another type.
/-- info: type!"[Examples,2.0.0.0]Examples.Point" : TypeIdentity -/
#guard_msgs in
#check ({ assembly := { name := name!"Examples", version := ⟨2, 0, 0, 0⟩, culture := name!"",
                        publicKeyToken := none },
          typeNamespace := name!"Examples", name := name!"Point" } : TypeIdentity)

-- A goal shows a closed type in `type!` form and a named one by its name.
/--
trace: type : TypeIdentity
found : type = type!"[Examples,1.0.0.0]Examples.Point"
⊢ type = pointType
---
trace: ⊢ type!"[Examples,1.0.0.0]Examples.Point" = pointType
-/
#guard_msgs in
example (type : TypeIdentity)
    (found : type =
      { assembly := examples, typeNamespace := name!"Examples", name := name!"Point" }) :
    type = pointType := by
  trace_state
  subst found
  trace_state
  rfl

-- A type whose assembly has a free version, culture or token keeps its structure, so the free
-- component stays visible.
/--
trace: version : Version
culture : MetadataName
token : Option Nat
type : TypeIdentity
freeVersion : type = { assembly := { name := name!"E", version := version, culture := name!"",
  publicKeyToken := none }, typeNamespace := name!"", name := name!"P" }
freeCulture : type = { assembly := { name := name!"E", version := { major := 1, minor := 0,
  build := 0, revision := 0 }, culture := culture, publicKeyToken := none },
  typeNamespace := name!"", name := name!"P" }
freeToken : type = { assembly := { name := name!"E", version := { major := 1, minor := 0,
  build := 0, revision := 0 }, culture := name!"", publicKeyToken := token },
  typeNamespace := name!"", name := name!"P" }
⊢ True
-/
#guard_msgs (whitespace := lax) in
set_option linter.unusedVariables false in
example (version : Version) (culture : MetadataName) (token : Option Nat) (type : TypeIdentity)
    (freeVersion : type =
      { assembly := { name := name!"E", version, culture := name!"", publicKeyToken := none },
        typeNamespace := name!"", name := name!"P" })
    (freeCulture : type =
      { assembly := { name := name!"E", version := ⟨1, 0, 0, 0⟩, culture,
                      publicKeyToken := none },
        typeNamespace := name!"", name := name!"P" })
    (freeToken : type =
      { assembly := { name := name!"E", version := ⟨1, 0, 0, 0⟩, culture := name!"",
                      publicKeyToken := token },
        typeNamespace := name!"", name := name!"P" }) :
    True := by
  trace_state
  trivial

-- Text that would be ambiguous falls back to the structure: an assembly name or culture with
-- `,` or `]`, a culture spelled `neutral`, a name with `.` or `/`, a namespace with `/`, and a
-- component that is not UTF-8.
/-- An unsigned neutral assembly of version 1.0.0.0 with the given name. -/
def renamed (name : MetadataName) : AssemblyName :=
  { name, version := ⟨1, 0, 0, 0⟩, culture := name!"", publicKeyToken := none }

/-- An unsigned assembly `E` of version 1.0.0.0 with the given culture. -/
def localized (culture : MetadataName) : AssemblyName :=
  { name := name!"E", version := ⟨1, 0, 0, 0⟩, culture, publicKeyToken := none }

/-- An assembly whose name holds `]`, written as a literal so the delaborator reads it. -/
def bracketed : AssemblyName :=
  { name := name!"E]", version := ⟨1, 0, 0, 0⟩, culture := name!"", publicKeyToken := none }

/-- An assembly whose culture is spelled `neutral`, written as a literal. -/
def spelledNeutral : AssemblyName :=
  { name := name!"E", version := ⟨1, 0, 0, 0⟩, culture := name!"neutral", publicKeyToken := none }

#guard (renamed name!"E").scopeText? == some "[E,1.0.0.0]"
#guard (renamed name!"E]").scopeText?.isNone
#guard (renamed name!"E,F").scopeText?.isNone
#guard (renamed ⟨511⟩).scopeText?.isNone
#guard (localized name!"en-US").scopeText? == some "[E,1.0.0.0,en-US,null]"
#guard (localized name!"en]").scopeText?.isNone
#guard (localized name!"en,US").scopeText?.isNone
#guard (localized name!"neutral").scopeText?.isNone
#guard (localized name!"neutral").display != (localized name!"").display
#guard (localized name!"neutral").display.startsWith "{ name := name!\"E\""
#guard (renamed name!"E,F").display.startsWith "{ name := name!\"E,F\""

/-- info: { assembly := examples, typeNamespace := name!"N", name := name!"A/B" } : TypeIdentity -/
#guard_msgs in
#check ({ assembly := examples, typeNamespace := name!"N", name := name!"A/B" } : TypeIdentity)

/-- info: { assembly := examples, typeNamespace := name!"N/M", name := name!"A" } : TypeIdentity -/
#guard_msgs in
#check ({ assembly := examples, typeNamespace := name!"N/M", name := name!"A" } : TypeIdentity)

/-- info: { assembly := bracketed, typeNamespace := name!"N", name := name!"A" } : TypeIdentity -/
#guard_msgs in
#check ({ assembly := bracketed, typeNamespace := name!"N", name := name!"A" } : TypeIdentity)

/--
info: { assembly := spelledNeutral, typeNamespace := name!"N", name := name!"A" } : TypeIdentity
-/
#guard_msgs in
#check ({ assembly := spelledNeutral, typeNamespace := name!"N", name := name!"A" } :
  TypeIdentity)

/-- info: { assembly := examples, typeNamespace := { code := 0x1ff }, name := name!"A" } :
  TypeIdentity -/
#guard_msgs (whitespace := lax) in
#check ({ assembly := examples, typeNamespace := ⟨511⟩, name := name!"A" } : TypeIdentity)

-- A type with a free or malformed component keeps its structure.
/--
trace: space : MetadataName
type : TypeIdentity
free : type = { assembly := examples, typeNamespace := space, name := name!"P" }
malformed : type = { assembly := examples, typeNamespace := name!"N", name := { code := 0x2ff } }
⊢ True
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (space : MetadataName) (type : TypeIdentity)
    (free : type = { assembly := examples, typeNamespace := space, name := name!"P" })
    (malformed : type = { assembly := examples, typeNamespace := name!"N", name := ⟨767⟩ }) :
    True := by
  trace_state
  trivial

-- A code that spells no text prints as its raw structure, never as a name.
/-- info: { code := 0x2ff } : MetadataName -/
#guard_msgs in
#check MetadataName.mk 767

/-- info: { code := 0x0 } : MetadataName -/
#guard_msgs in
#check MetadataName.mk 0

/-- info: "{ code := 0x2ff }" -/
#guard_msgs in
#eval (MetadataName.mk 767).display

-- 511 is the byte 0xFF after the leading 1: a well-formed code whose byte is not UTF-8.
/-- info: { code := 0x1ff } : MetadataName -/
#guard_msgs in
#check MetadataName.mk 511

-- 120832 is the code unit 0xD800 after the leading 1: an unpaired high surrogate.
/-- info: { code := 0x1d800 } : UserString -/
#guard_msgs in
#check UserString.mk 120832

/-- info: "{ code := 0x1d800 }" -/
#guard_msgs in
#eval (UserString.mk 120832).display

-- The compiled UTF-8 decision refuses an overlong form (C0 80) and an encoded surrogate
-- (ED A0 80), and a lone low surrogate (DC00) is no UTF-16 text.
/-- info: { code := 0x1c080 } : MetadataName -/
#guard_msgs in
#check MetadataName.mk 114816

/-- info: { code := 0x1eda080 } : MetadataName -/
#guard_msgs in
#check MetadataName.mk 32350336

/-- info: { code := 0x1dc00 } : UserString -/
#guard_msgs in
#check UserString.mk 121856

example : MetadataName.ofBytes? [0xC0, 0x80] = some ⟨114816⟩ := by decide +kernel
example : MetadataName.ofBytes? [0xED, 0xA0, 0x80] = some ⟨32350336⟩ := by decide +kernel
example : UserString.ofUnits? [0xDC00] = some ⟨121856⟩ := by decide +kernel

-- Codes that are zero or whose leading digit is not 1 read back as nothing.
example : (MetadataName.mk 0).bytes? = none := by decide +kernel
example : (MetadataName.mk 2).bytes? = none := by decide +kernel
example : (MetadataName.mk 767).bytes? = none := by decide +kernel
example : UserString.ofUnits? [65536] = none := by decide +kernel

-- Byte lists with the same digits and different lengths give different names.
example : MetadataName.ofBytes? [0] ≠ MetadataName.ofBytes? [0, 0] := by decide +kernel
example : MetadataName.ofBytes? [65] ≠ MetadataName.ofBytes? [0, 65] := by decide +kernel

-- An escaped quote and backslash reach the name as the bytes they stand for.
example : (name!"a\"b\\c").bytes? = some [97, 34, 98, 92, 99] := by decide +kernel

-- Under `pp.all` a name is its constructor applied to its code, with no text.
/--
info: CIL.MetadataName.mk (@OfNat.ofNat.{0} Nat (nat_lit 321) (instOfNatNat (nat_lit 321)))
  : CIL.MetadataName
-/
#guard_msgs (whitespace := lax) in
set_option pp.all true in
#check name!"A"

-- The element type codes of ECMA-335 II.23.1.16.
example : [PrimitiveType.boolean, .char, .sbyte, .byte, .int16, .uint16, .int32, .uint32, .int64,
    .uint64, .single, .double, .intPtr, .uintPtr].map PrimitiveType.elementType =
    [0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x18, 0x19] := by
  decide

-- No metadata name holds a NUL: `name!` refuses one, and the code of the byte 0 prints raw.
/-- error: name!: a metadata name cannot hold a NUL character -/
#guard_msgs in
#check name!"a\x00"

/-- info: { code := 0x100 } : MetadataName -/
#guard_msgs in
#check MetadataName.mk 256

-- A malformed code and a name whose text spells its raw structure display differently.
#guard (MetadataName.mk 767).display == "{ code := 0x2ff }"
#guard (name!"{ code := 0x2ff }").display == "\\{ code := 0x2ff }"
#guard (UserString.mk 120832).display != (str!"{ code := 0x1d800 }").display

-- Escapes in printed text: a backslash, and control, format, separator and non-ASCII space
-- characters, each of which would otherwise print as nothing or as a space.
#guard (name!"a\\b").display == "a\\\\b"
#guard (name!"a\u200Bb").display == "a\\u200Bb"
#guard (str!"line\nnext").display == "line\\u000Anext"

/-- info: name!"a\"b\\c" : MetadataName -/
#guard_msgs in
#check name!"a\"b\\c"

-- A `#guard_msgs` docstring reads `\uHHHH` of a visible-width character as the character, so
-- these escapes are pinned on the literal text that `Repr` and the delaborators print.
#guard reprStr name!"Cc\u0085 Cf\u202E Zl\u2028 Zp\u2029 Zs\u00A0" ==
  "name!\"Cc\\u0085 Cf\\u202E Zl\\u2028 Zp\\u2029 Zs\\u00A0\""
#guard (str!"zero\x00width\u200B").literal? == some "\"zero\\u0000width\\u200B\""
#guard ({ assembly := examples, typeNamespace := name!"N", name := name!"A\u200B" } :
  TypeIdentity).text? == some "[Examples,1.0.0.0]N.A\\u200B"

/-- info: str!"tab\u0009zero\u0000next\u0085" : UserString -/
#guard_msgs in
#check str!"tab\tzero\x00next\u0085"

-- U+E0041, a tag character, is invisible and above U+FFFF, where a Lean literal has no escape,
-- so a name holding it prints raw although its bytes are valid UTF-8.
#guard MetadataName.ofBytes? [0xF3, 0xA0, 0x81, 0x81] == some ⟨8382349697⟩
#guard (MetadataName.mk 8382349697).text?.isSome

/-- info: { code := 0x1f3a08181 } : MetadataName -/
#guard_msgs in
#check MetadataName.mk 8382349697

#guard (MetadataName.mk 8382349697).display == "{ code := 0x1f3a08181 }"

-- `type!` is display only.
/-- error: type!"..." is display only; write the TypeIdentity structure -/
#guard_msgs in
#check type!"[Examples]Examples.Point"

-- `name!` and `str!` round trip through the bytes and code units they encode.
example : (name!"Int32").bytes? = some [73, 110, 116, 51, 50] := by decide +kernel
example : MetadataName.ofBytes? [73, 110, 116, 51, 50] = some name!"Int32" := by decide +kernel
example : (name!"é").bytes? = some [0xC3, 0xA9] := by decide +kernel
example : (name!"").bytes? = some [] := by decide +kernel
example : name!"" = ⟨1⟩ := by decide +kernel
example : MetadataName.ofBytes? [256] = none := by decide +kernel
example : (str!"A😀").units? = some [0x41, 0xD83D, 0xDE00] := by decide +kernel

-- A printed name or literal determines its value: reading back and building are inverse.
example (name : MetadataName) (bytes : List Nat) (decoded : name.bytes? = some bytes) :
    MetadataName.ofBytes? bytes = some name := MetadataName.ofBytes?_bytes? decoded
example (literal : UserString) (units : List Nat) (decoded : literal.units? = some units) :
    UserString.ofUnits? units = some literal := UserString.ofUnits?_units? decoded

-- Every codec theorem rests on the standard axioms alone.
/--
info: 'CIL.MetadataName.ofBytes?_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MetadataName.ofBytes?_injective

/--
info: 'CIL.MetadataName.bytes?_ofBytes?' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MetadataName.bytes?_ofBytes?

/--
info: 'CIL.MetadataName.ofBytes?_bytes?' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms MetadataName.ofBytes?_bytes?

/--
info: 'CIL.UserString.ofUnits?_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UserString.ofUnits?_injective

/--
info: 'CIL.UserString.units?_ofUnits?' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms UserString.units?_ofUnits?

/--
info: 'CIL.UserString.ofUnits?_units?' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms UserString.ofUnits?_units?

/-- info: name!"é" : MetadataName -/
#guard_msgs in
#check name!"é"

/-- info: name!"" : MetadataName -/
#guard_msgs in
#check name!""

/-- info: str!"A😀" : UserString -/
#guard_msgs in
#check str!"A😀"

-- Equality is decided on codes and components.
example : name!"Int32" ≠ name!"Int64" := by decide +kernel
example : name!"" ≠ ⟨256⟩ := by decide +kernel
example : pointType =
    { assembly := examples, typeNamespace := name!"Examples", name := name!"Point" } := by
  decide +kernel
-- The same names defined in another pinned version of the assembly are another type.
example : pointType ≠ { pointType with assembly := { examples with version := ⟨2, 0, 0, 0⟩ } } :=
  by decide +kernel
example : examples ≠ { examples with culture := name!"en-US" } := by decide +kernel
example : examples ≠ { examples with publicKeyToken := some 0 } := by decide +kernel
example : compare name!"A" name!"B" = .lt := by decide +kernel

-- A hash depends on every byte or code unit, not only on the last 64 bits of the code.
#guard hash name!"ArgumentException" != hash name!"FormatException"
#guard hash str!"xABCD" != hash str!"yABCD"
#guard hash pointType != hash { pointType with name := name!"Points" }

-- Namespace `A.B` with name `C` and namespace `A` with name `B.C` are different types.
/-- The type `C` in namespace `A.B`. -/
def dottedNamespace : TypeIdentity :=
  { assembly := examples, typeNamespace := name!"A.B", name := name!"C" }

/-- The type `B.C` in namespace `A`. -/
def dottedName : TypeIdentity :=
  { assembly := examples, typeNamespace := name!"A", name := name!"B.C" }

example : dottedNamespace ≠ dottedName := by decide +kernel

-- Both would read `[Examples,1.0.0.0]A.B.C`, so only the first prints and displays as text.
#guard dottedNamespace.display == "[Examples,1.0.0.0]A.B.C"
#guard dottedName.display.startsWith "{ assembly := { name := name!\"Examples\""

/-- info: type!"[Examples,1.0.0.0]A.B.C" : TypeIdentity -/
#guard_msgs in
#check ({ assembly := examples, typeNamespace := name!"A.B", name := name!"C" } : TypeIdentity)

/--
info: { assembly := examples, typeNamespace := name!"A", name := name!"B.C" } : TypeIdentity
-/
#guard_msgs in
#check ({ assembly := examples, typeNamespace := name!"A", name := name!"B.C" } : TypeIdentity)

-- A nested type differs from a type whose name holds the enclosing path, and from a deeper one.
example : enumeratorType ≠
    { enumeratorType with enclosing := [], name := name!"List`1/Enumerator" } := by
  decide +kernel
example : enumeratorType ≠ { enumeratorType with
    enclosing := enumeratorType.enclosing ++ [⟨name!"", name!"Enumerator"⟩] } := by
  decide +kernel

-- Each level of a nesting chain keeps its namespace column: nested types that differ only in an
-- enclosing level's namespace, or only in their own, are different types and print differently.
/-- `Outer/Inner` with the outer type in namespace `N`. -/
def innerType : TypeIdentity :=
  { assembly := examples, typeNamespace := name!"", enclosing := [⟨name!"N", name!"Outer"⟩],
    name := name!"Inner" }

example : innerType ≠ { innerType with enclosing := [⟨name!"M", name!"Outer"⟩] } := by
  decide +kernel
example : innerType ≠ { innerType with typeNamespace := name!"N" } := by decide +kernel

/-- info: "[Examples,1.0.0.0]N.Outer/Inner" -/
#guard_msgs in
#eval innerType.display

/-- info: "[Examples,1.0.0.0]M.Outer/Inner" -/
#guard_msgs in
#eval ({ innerType with enclosing := [⟨name!"M", name!"Outer"⟩] }).display

/-- info: "[Examples,1.0.0.0]N.Outer/N.Inner" -/
#guard_msgs in
#eval ({ innerType with typeNamespace := name!"N" }).display

/-- info: type!"[Examples,1.0.0.0]N.Outer/N.Inner" : TypeIdentity -/
#guard_msgs in
#check ({ assembly := examples, typeNamespace := name!"N", enclosing := [⟨name!"N", name!"Outer"⟩],
          name := name!"Inner" } : TypeIdentity)

/-- Boundary codes and payload digits agree with the mathematical radix specification. -/
def checkIdentityCodec : IO Unit := do
  for bits in [8, 16] do
    let base := 2^bits
    for code in List.range 1024 ++
        [base - 1, base, base + 1, 2 * base - 1, 2 * base, base^2 - 1,
          base^2, base^2 + 1, 2 * base^2 - 1, 2 * base^2] do
      unless bitDigits? bits code == radixDigits? base code code [] do
        throw (IO.userError s!"decoder admission differs: width {bits}, code {code}")
    for digits in [[], [0], [0, 0], [base - 1], [0, base - 1, 0],
        [base - 1, 0, base - 1], [base], [0, base], [base + 1, 0]] do
      unless bitCode? bits digits == radixCode? base digits 1 do
        throw (IO.userError s!"encoder differs: width {bits}, digits {digits}")
      if let some code := bitCode? bits digits then
        unless bitDigits? bits code == some digits do
          throw (IO.userError s!"payload digits differ: width {bits}, digits {digits}")
  for seed in [0, 1, 0x0123456789abcdef] do
    for code in [0, 1, 2^64 - 1, 2^64, 2^64 + 1, 2^128 - 1,
        2^128, 2^128 + 1, 2^192 + 2^64 + 7] do
      unless mixCodeLimbs seed code == mixCodeLimbsSpec seed code do
        throw (IO.userError s!"hash limbs differ: seed {seed}, code {code}")

#eval checkIdentityCodec

/-- Separate runtime measurements cover encoding, decoding and hashing of growing payloads. -/
def checkIdentityCodecCost : IO Unit := do
  for bits in [8, 16] do
    let mut previous : Array Nat := #[0, 0, 0]
    for size in [8192, 65536, 524288] do
      let mut best : Array Nat := #[1000000000000, 1000000000000, 1000000000000]
      let mut checksum : UInt64 := 0
      for sample in [:3] do
        let digits := (List.range (size * 8 / bits)).map
          (fun index => (index + sample) % (2^bits))
        let started ← IO.monoNanosNow
        let some code := bitCode? bits digits | throw (IO.userError "bounded encoder rejected")
        let encoded ← IO.monoNanosNow
        let decoded := bitDigits? bits code
        let finished ← IO.monoNanosNow
        let hashed := mixCodeLimbs (UInt64.ofNat sample) code
        let ended ← IO.monoNanosNow
        unless decoded == some digits do
          throw (IO.userError "growing payload did not round trip")
        checksum := checksum ^^^ hashed
        let times := #[encoded - started, finished - encoded, ended - finished]
        for index in [:3] do best := best.set! index (min best[index]! times[index]!)
      for index in [:3] do
        if previous[index]! > 0 && best[index]! > previous[index]! * 16 + 2000000 then
          throw (IO.userError (s!"codec cost grew too quickly: width {bits}, size {size}, " ++
            s!"operation {index}, {previous[index]!} -> {best[index]!} ns"))
      IO.println (s!"PASS codec width {bits}, bytes {size}: " ++
        s!"encode/decode/hash ns {best}, {checksum}")
      previous := best

#eval checkIdentityCodecCost

/-- Every component takes precedence over all following components. -/
def checkAssemblyComponentOrder : IO Unit := do
  let lower : AssemblyName := ⟨⟨1⟩, ⟨1, 1, 1, 1⟩, ⟨1⟩, none⟩
  let upper : AssemblyName := ⟨⟨2⟩, ⟨2, 2, 2, 2⟩, ⟨2⟩, some 0⟩
  let pairs : Array (AssemblyName × AssemblyName) := #[
    ({ upper with name := lower.name }, { lower with name := upper.name }),
    ({ upper with name := lower.name, version := ⟨1, 2, 2, 2⟩ },
      { lower with version := ⟨2, 1, 1, 1⟩ }),
    (⟨⟨1⟩, ⟨1, 1, 2, 2⟩, ⟨2⟩, some 0⟩, { lower with version := ⟨1, 2, 1, 1⟩ }),
    (⟨⟨1⟩, ⟨1, 1, 1, 2⟩, ⟨2⟩, some 0⟩, { lower with version := ⟨1, 1, 2, 1⟩ }),
    ({ lower with culture := upper.culture, publicKeyToken := upper.publicKeyToken },
      { lower with version := ⟨1, 1, 1, 2⟩ }),
    ({ lower with publicKeyToken := upper.publicKeyToken },
      { lower with culture := upper.culture }),
    (lower, { lower with publicKeyToken := some 0 }),
    ({ lower with publicKeyToken := some 0 }, { lower with publicKeyToken := some 1 })]
  for (left, right) in pairs do
    unless compare left right == .lt && compare right left == .gt do
      throw (IO.userError "assembly component precedence changed")

#eval checkAssemblyComponentOrder

/-- Text delimiters, invalid UTF-8, culture and null-token distinctions survive ordered lookup. -/
def assemblyMapKeys : Array AssemblyName := #[examples,
  { examples with publicKeyToken := some 0 },
  { examples with culture := name!"neutral" },
  { examples with name := name!"A, Version=1.0.0.0" },
  { examples with name := name!"A", culture := name!"Version=1.0.0.0" },
  { examples with name := ⟨0x1ff⟩ }, { examples with name := ⟨0x1fe⟩ }]

/-- All distinct assembly components remain separate map entries with their original values. -/
def checkAssemblyMap : IO Unit := do
  let mut entries : Std.TreeMap AssemblyName Nat := ∅
  for bound : index in [:assemblyMapKeys.size] do
    entries := entries.insert assemblyMapKeys[index] index
  unless entries.size == assemblyMapKeys.size do
    throw (IO.userError "distinct assembly keys collapsed")
  for bound : index in [:assemblyMapKeys.size] do
    unless entries[assemblyMapKeys[index]]? == some index do
      throw (IO.userError "assembly lookup returned another identity")
  unless entries[{ examples with version := ⟨9, 0, 0, 0⟩ }]? == none do
    throw (IO.userError "absent assembly key was found")
  entries := entries.insert examples 99
  unless entries.size == assemblyMapKeys.size && entries[examples]? == some 99 do
    throw (IO.userError "equal assembly key did not replace its value")

#eval checkAssemblyMap

/-- Equal comparison implies exact identity, including optional tokens and undecodable names. -/
theorem assemblyMapComparison (left right : AssemblyName) :
    compare left right = .eq ↔ left = right :=
  AssemblyName.compare_eq_iff left right

/-- info: 'Tests.Identity.assemblyMapComparison' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assemblyMapComparison

/-- Ordered lookup uses transitive raw component comparisons. -/
theorem assemblyComparisonTransitive (first second third : AssemblyName)
    (firstBefore : compare first second = .lt) (secondBefore : compare second third = .lt) :
    compare first third = .lt :=
  Std.TransCmp.lt_trans firstBefore secondBefore

/-- info: 'Tests.Identity.assemblyComparisonTransitive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assemblyComparisonTransitive

/-- Prebuilt names share a byte prefix and differ only in their two final nonzero bytes. -/
def assemblyCostKeys (count prefixBytes : Nat) : Array AssemblyName := Id.run do
  let prefixCode := (bitCode? 8 (List.replicate prefixBytes 97)).getD 1
  return (Array.range count).map fun index =>
    { examples with name := ⟨(prefixCode <<< 16) + (index / 255 + 1) * 256 + index % 255 + 1⟩ }

/-- Times map construction and successful lookup without timing identity construction. -/
def measureAssemblyMap (keys : Array AssemblyName) : IO Nat := do
  let mut best := 1000000000000
  for _ in [:3] do
    let started ← IO.monoNanosNow
    for _ in [:16] do
      let mut entries : Std.TreeMap AssemblyName Nat := ∅
      for bound : index in [:keys.size] do entries := entries.insert keys[index] index
      unless entries.size == keys.size do throw (IO.userError "growing map lost keys")
      for bound : index in [:keys.size] do
        unless entries[keys[index]]? == some index do
          throw (IO.userError "growing map lookup failed")
    best := min best ((← IO.monoNanosNow) - started)
  return best

/-- Map cost grows with key count and comparison bit length, with no text decoding. -/
def checkAssemblyMapCost : IO Unit := do
  for prefixBytes in [4, 4096] do
    let mut previous := 0
    for count in [64, 512, 4096] do
      let elapsed ← measureAssemblyMap (assemblyCostKeys count prefixBytes)
      if previous > 0 && elapsed > previous * 20 + 2000000 then
        throw (IO.userError s!"assembly count cost grew too quickly: {previous} -> {elapsed}")
      IO.println s!"PASS assembly count {count}, prefix bytes {prefixBytes}: {elapsed} ns"
      previous := elapsed
  let mut previous := 0
  for prefixBytes in [4096, 32768, 262144] do
    let elapsed ← measureAssemblyMap (assemblyCostKeys 64 prefixBytes)
    if previous > 0 && elapsed > previous * 20 + 2000000 then
      throw (IO.userError s!"assembly bit cost grew too quickly: {previous} -> {elapsed}")
    IO.println s!"PASS assembly count 64, prefix bytes {prefixBytes}: {elapsed} ns"
    previous := elapsed

#eval checkAssemblyMapCost

end Tests.Identity
