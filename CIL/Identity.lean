import CIL.LiteralDisplay

/-!
# Typed identities

Values that name metadata entities: a metadata name (`MetadataName`), a user string literal
(`UserString`), an assembly (`AssemblyName` with its `Version`), a named type (`TypeIdentity`), a
primitive type (`PrimitiveType`) and what metadata says a named type is (`TypeKind`). Each is a
function of the entity it names and holds no row number, heap offset or per-extraction counter.

A name or literal is one natural number: its UTF-8 bytes or UTF-16 code units read as a
big-endian number after a leading 1, so the number fixes the length and every digit. Equality
of every identity is the derived `DecidableEq`, which the kernel decides with `Nat.beq` on codes
and constructor matches. Code comparison reads numeric limbs rather than reducing a digit list;
runtime comparison still depends on the number of limbs.

Text appears only in the `name!` and `str!` elaborators, which turn a literal into a code when
the term is elaborated, and in the display functions and delaborators, which turn a value back
into text for a reader. Printed text determines the value: where text would be ambiguous, the
value prints as its structure. `type!"..."` is printed for types whose components are all
literals and refused as input, so no text is parsed back into an identity.
-/

namespace CIL

/-! ## Codes of digit lists -/

/-- The number of values one UTF-8 byte can take. -/
def byteBase : Nat := 256

/-- The number of values one UTF-16 code unit can take. -/
def codeUnitBase : Nat := 65536

/-- The number that `digits` continue in `base`, most significant first, after the digits
    already read into `code`; `none` when a digit is not below `base`. Each step scales a growing code. -/
def radixCode? (base : Nat) : List Nat → Nat → Option Nat
  | [], code => some code
  | digit :: rest, code =>
    if digit < base then radixCode? base rest (code * base + digit) else none

/-- The digits of `code` in `base` below its leading digit 1, followed by `found`; `none` when
    the leading digit is not 1 or `fuel` runs out. A code of `n` digits after the leading 1
    takes `n + 1` steps, and the code itself always suffices as fuel. -/
def radixDigits? (base : Nat) : Nat → Nat → List Nat → Option (List Nat)
  | 0, _, _ => none
  | fuel + 1, code, found =>
    if code == 1 then some found
    else if code < base then none
    else radixDigits? base fuel (code / base) (code % base :: found)

/-- A code read from a leading 1 is at least that start plus the number of digits read. -/
theorem radixCode?_bound {base : Nat} (wide : 2 ≤ base) (digits : List Nat) :
    ∀ (start code : Nat), 1 ≤ start → radixCode? base digits start = some code →
      start + digits.length ≤ code := by
  induction digits with
  | nil =>
    intro start code _ read
    simp only [radixCode?, Option.some.injEq] at read
    subst read
    simp
  | cons digit rest ih =>
    intro start code positive read
    simp only [radixCode?] at read
    split at read
    · have scaled : start * 2 ≤ start * base := Nat.mul_le_mul_left start wide
      have restBound := ih (start * base + digit) code (by omega) read
      simp only [List.length_cons]
      omega
    · simp at read

#print axioms radixCode?_bound

/-- Reading back one digit of a code whose leading part is at least 1 removes that digit. -/
theorem radixDigits?_peel {base : Nat} (wide : 2 ≤ base) {start digit : Nat}
    (positive : 1 ≤ start) (small : digit < base) (fuel : Nat) (found : List Nat) :
    radixDigits? base (fuel + 1) (start * base + digit) found =
      radixDigits? base fuel start (digit :: found) := by
  have scaled : 1 * base ≤ start * base := Nat.mul_le_mul_right base positive
  have notOne : start * base + digit ≠ 1 := by omega
  have notSmall : ¬ start * base + digit < base := by omega
  have quotient : (start * base + digit) / base = start := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt small,
      Nat.zero_add]
  have remainder : (start * base + digit) % base = digit := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt small]
  simp [radixDigits?, notOne, notSmall, quotient, remainder]

#print axioms radixDigits?_peel

/-- Reading the digits of a code back, one step per digit, ends at the start of the code. -/
theorem radixDigits?_radixCode? {base : Nat} (wide : 2 ≤ base) (digits : List Nat) :
    ∀ (start code fuel : Nat) (found : List Nat), 1 ≤ start →
      radixCode? base digits start = some code →
      radixDigits? base (fuel + digits.length) code found =
        radixDigits? base fuel start (digits ++ found) := by
  induction digits with
  | nil => intro start code fuel found _ read; simp [radixCode?] at read; simp [read]
  | cons digit rest ih =>
    intro start code fuel found positive read
    simp only [radixCode?] at read
    split at read
    next small =>
      have scaled : start * 2 ≤ start * base := Nat.mul_le_mul_left start wide
      have step := ih (start * base + digit) code (fuel + 1) found (by omega) read
      rw [List.length_cons, show fuel + (rest.length + 1) = fuel + 1 + rest.length by omega,
        step, radixDigits?_peel wide positive small]
      rfl
    next => simp at read

#print axioms radixDigits?_radixCode?

/-- The digits of a code read from a leading 1 come back from the code alone. -/
theorem radixDigits?_of_radixCode? {base : Nat} (wide : 2 ≤ base) {digits : List Nat}
    {code : Nat} (read : radixCode? base digits 1 = some code) :
    radixDigits? base code code [] = some digits := by
  have bound := radixCode?_bound wide digits 1 code (Nat.le_refl 1) read
  have back := radixDigits?_radixCode? wide digits 1 code (code - digits.length) []
    (Nat.le_refl 1) read
  rw [Nat.sub_add_cancel (by omega), List.append_nil] at back
  rw [back, show code - digits.length = code - digits.length - 1 + 1 by omega]
  simp [radixDigits?]

#print axioms radixDigits?_of_radixCode?

/-- Two digit lists read from a leading 1 into the same code are equal. -/
theorem radixCode?_injective {base : Nat} (wide : 2 ≤ base) {left right : List Nat}
    {code : Nat} (fromLeft : radixCode? base left 1 = some code)
    (fromRight : radixCode? base right 1 = some code) : left = right :=
  Option.some.inj ((radixDigits?_of_radixCode? wide fromLeft).symm.trans
    (radixDigits?_of_radixCode? wide fromRight))

#print axioms radixCode?_injective

/-- Reading digits after a list of digits continues from the code the list reached. -/
theorem radixCode?_append (base : Nat) (front back : List Nat) :
    ∀ start, radixCode? base (front ++ back) start =
      (radixCode? base front start).bind (radixCode? base back) := by
  induction front with
  | nil => intro start; rfl
  | cons digit rest ih =>
    intro start
    simp only [List.cons_append, radixCode?]
    split
    · exact ih _
    · rfl

#print axioms radixCode?_append

/-- Digits read back from a code, followed by `found`, are digits that build the code from a
    leading 1, followed by `found`. -/
theorem radixCode?_of_radixDigits? {base : Nat} (wide : 2 ≤ base) :
    ∀ (fuel code : Nat) (found digits : List Nat),
      radixDigits? base fuel code found = some digits →
      ∃ front, digits = front ++ found ∧ radixCode? base front 1 = some code := by
  intro fuel
  induction fuel with
  | zero => intro code found digits read; simp [radixDigits?] at read
  | succ fuel ih =>
    intro code found digits read
    simp only [radixDigits?] at read
    split at read
    next isOne =>
      simp only [Option.some.injEq] at read
      exact ⟨[], by simp [read], by simp [radixCode?, (beq_iff_eq.mp isOne)]⟩
    next =>
      split at read
      next => simp at read
      next =>
        obtain ⟨front, split, upper⟩ := ih (code / base) (code % base :: found) digits read
        refine ⟨front ++ [code % base], by simp [split], ?_⟩
        have lowDigit : code % base < base := Nat.mod_lt _ (by omega)
        rw [radixCode?_append, upper]
        simp [radixCode?, lowDigit, Nat.div_add_mod']

#print axioms radixCode?_of_radixDigits?

/-- The digits read back from a code build that code from a leading 1. -/
theorem radixCode?_of_radixDigits?_self {base : Nat} (wide : 2 ≤ base) {code : Nat}
    {digits : List Nat} (read : radixDigits? base code code [] = some digits) :
    radixCode? base digits 1 = some code := by
  obtain ⟨front, split, built⟩ := radixCode?_of_radixDigits? wide code code [] digits read
  simpa [split] using built

#print axioms radixCode?_of_radixDigits?_self

/-- Exactly `count` base-2^bits digits when the code fits, most significant first, then `tail`.
    Balanced splits keep bit operations within O(payload bits * log count). -/
def fixedDigits (bits count code : Nat) (tail : List Nat) : List Nat :=
  match count with
  | 0 => tail
  | 1 => code :: tail
  | count + 2 =>
    let lowCount := (count + 2) / 2
    let highCount := count + 2 - lowCount
    let lowBits := bits * lowCount
    fixedDigits bits highCount (code >>> lowBits)
      (fixedDigits bits lowCount (code &&& ((1 <<< lowBits) - 1)) tail)
termination_by count
decreasing_by all_goals omega

/-- The digit count is independent of the code and includes every leading zero. -/
theorem fixedDigits_length (bits count code : Nat) (tail : List Nat) :
    (fixedDigits bits count code tail).length = count + tail.length := by
  induction count using Nat.strongRecOn generalizing code tail with
  | ind count ih =>
    match count with
    | 0 => simp [fixedDigits]
    | 1 => simp [fixedDigits, Nat.add_comm]
    | count + 2 =>
      rw [fixedDigits, ih _ (by omega), ih _ (by omega)]
      omega

#print axioms fixedDigits_length

/-- Reading bounded fixed-width digits continues any initial code with their exact value. -/
theorem fixedDigits_spec (bits count code : Nat) (bounded : code < (2^bits)^count)
    (tail : List Nat) (start : Nat) :
    radixCode? (2^bits) (fixedDigits bits count code tail) start =
      radixCode? (2^bits) tail (start * (2^bits)^count + code) := by
  induction count using Nat.strongRecOn generalizing code tail start with
  | ind count ih =>
    match count with
    | 0 => simp_all [fixedDigits]
    | 1 => simp_all [fixedDigits, radixCode?]
    | count + 2 =>
      let low := (count + 2) / 2
      let high := count + 2 - low
      have splitCount : high + low = count + 2 := by dsimp [high, low]; omega
      have lowSmall : low < count + 2 := by dsimp [low]; omega
      have highSmall : high < count + 2 := by dsimp [high, low]; omega
      have power : 2^(bits*low) = (2^bits)^low := by rw [Nat.pow_mul]
      have positive : 0 < (2^bits)^low := Nat.pow_pos (Nat.pow_pos (by decide))
      have upper : code / (2^bits)^low < (2^bits)^high := by
        apply (Nat.div_lt_iff_lt_mul positive).mpr
        rw [← Nat.pow_add, splitCount]
        exact bounded
      have lower : code % (2^bits)^low < (2^bits)^low := Nat.mod_lt _ positive
      rw [fixedDigits]
      change radixCode? (2^bits)
        (fixedDigits bits high (code >>> (bits*low))
          (fixedDigits bits low (code &&& ((1 <<< (bits*low)) - 1)) tail)) start = _
      simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul]
      rw [Nat.and_two_pow_sub_one_eq_mod, power]
      rw [ih high highSmall _ upper, ih low lowSmall _ lower]
      congr 1
      rw [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, splitCount]
      have joined := Nat.div_add_mod code ((2^bits)^low)
      rw [Nat.mul_comm] at joined
      omega


#print axioms fixedDigits_spec

/-- Every digit accepted by the radix reader is below its base. -/
theorem radixCode?_digits {base : Nat} {digits : List Nat} {start code : Nat}
    (read : radixCode? base digits start = some code) :
    ∀ digit ∈ digits, digit < base := by
  induction digits generalizing start with
  | nil => simp
  | cons head rest ih =>
    simp only [radixCode?] at read
    split at read
    next small =>
      intro digit member
      rcases List.mem_cons.mp member with same | member
      · simpa [same] using small
      · exact ih read digit member
    next => simp at read

#print axioms radixCode?_digits

/-- Every digit of a bounded code fits the requested digit width, including zero-width digits. -/
theorem fixedDigits_bound (bits count code : Nat) (bounded : code < (2^bits)^count) :
    ∀ digit ∈ fixedDigits bits count code [], digit < 2^bits := by
  apply radixCode?_digits (start := 0) (code := code)
  simpa [radixCode?] using fixedDigits_spec bits count code bounded [] 0

#print axioms fixedDigits_bound

/-! ## Names and literals -/

/-- One metadata name, such as `Int32` or `System.Collections`: its UTF-8 bytes read as a
    big-endian base-256 number after a leading 1, so the value fixes the length and every
    byte. A code that is zero or whose leading digit is not 1 names nothing. -/
structure MetadataName where
  /-- The bytes of the name after a leading 1, as one number. -/
  code : Nat
  deriving DecidableEq, Ord

/-- The number of values one 64-bit limb of a code takes. -/
def hashLimbBase : Nat := 2 ^ 64

/-- `seed` mixed with every 64-bit limb of `code`, least significant first, so a hash depends
    on every byte of a name; the derived `Hashable Nat` keeps only the last eight. -/
def mixCodeLimbs (seed : UInt64) (code : Nat) : UInt64 :=
  if code = 0 then seed
  else mixCodeLimbs (mixHash seed (UInt64.ofNat code)) (code / hashLimbBase)
termination_by code
decreasing_by exact Nat.div_lt_self (by omega) (by unfold hashLimbBase; decide)

instance : Hashable MetadataName := ⟨fun name => mixCodeLimbs 0 name.code⟩

/-- The name whose UTF-8 bytes are `bytes`, or `none` when an entry is not a byte. -/
def MetadataName.ofBytes? (bytes : List Nat) : Option MetadataName :=
  (radixCode? byteBase bytes 1).map MetadataName.mk

/-- The UTF-8 bytes a name holds, or `none` when its code is zero or its leading base-256 digit
    is not 1. -/
def MetadataName.bytes? (name : MetadataName) : Option (List Nat) :=
  radixDigits? byteBase name.code name.code []

/-- The bytes a name was built from come back from the name. -/
theorem MetadataName.bytes?_ofBytes? {bytes : List Nat} {name : MetadataName}
    (encoded : MetadataName.ofBytes? bytes = some name) : name.bytes? = some bytes := by
  obtain ⟨code, read, rfl⟩ := Option.map_eq_some_iff.mp encoded
  exact radixDigits?_of_radixCode? (by decide) read

#print axioms MetadataName.bytes?_ofBytes?

/-- A name whose bytes read back is the name of those bytes, so a name is malformed exactly
    when no byte list gives it. -/
theorem MetadataName.ofBytes?_bytes? {bytes : List Nat} {name : MetadataName}
    (decoded : name.bytes? = some bytes) : MetadataName.ofBytes? bytes = some name := by
  simp [ofBytes?, radixCode?_of_radixDigits?_self (by decide) decoded]

#print axioms MetadataName.ofBytes?_bytes?

/-- Two byte lists that give the same name are equal. -/
theorem MetadataName.ofBytes?_injective {left right : List Nat} {name : MetadataName}
    (fromLeft : MetadataName.ofBytes? left = some name)
    (fromRight : MetadataName.ofBytes? right = some name) : left = right := by
  obtain ⟨_, readLeft, rfl⟩ := Option.map_eq_some_iff.mp fromLeft
  obtain ⟨_, readRight, sameCode⟩ := Option.map_eq_some_iff.mp fromRight
  cases sameCode
  exact radixCode?_injective (by decide) readLeft readRight

#print axioms MetadataName.ofBytes?_injective

/-- A `#US` literal: its UTF-16 code units read as a big-endian base-65536 number after a
    leading 1. -/
structure UserString where
  /-- The code units of the literal after a leading 1, as one number. -/
  code : Nat
  deriving DecidableEq, Ord

instance : Hashable UserString := ⟨fun literal => mixCodeLimbs 0 literal.code⟩

/-- The literal whose UTF-16 code units are `units`, or `none` when an entry is not a code
    unit. -/
def UserString.ofUnits? (units : List Nat) : Option UserString :=
  (radixCode? codeUnitBase units 1).map UserString.mk

/-- The UTF-16 code units a literal holds, or `none` when its code is zero or its leading
    base-65536 digit is not 1. -/
def UserString.units? (literal : UserString) : Option (List Nat) :=
  radixDigits? codeUnitBase literal.code literal.code []

/-- The code units a literal was built from come back from the literal. -/
theorem UserString.units?_ofUnits? {units : List Nat} {literal : UserString}
    (encoded : UserString.ofUnits? units = some literal) : literal.units? = some units := by
  obtain ⟨code, read, rfl⟩ := Option.map_eq_some_iff.mp encoded
  exact radixDigits?_of_radixCode? (by decide) read

#print axioms UserString.units?_ofUnits?

/-- A literal whose code units read back is the literal of those units, so a literal is
    malformed exactly when no unit list gives it. -/
theorem UserString.ofUnits?_units? {units : List Nat} {literal : UserString}
    (decoded : literal.units? = some units) : UserString.ofUnits? units = some literal := by
  simp [ofUnits?, radixCode?_of_radixDigits?_self (by decide) decoded]

#print axioms UserString.ofUnits?_units?

/-- Two code unit lists that give the same literal are equal. -/
theorem UserString.ofUnits?_injective {left right : List Nat} {literal : UserString}
    (fromLeft : UserString.ofUnits? left = some literal)
    (fromRight : UserString.ofUnits? right = some literal) : left = right := by
  obtain ⟨_, readLeft, rfl⟩ := Option.map_eq_some_iff.mp fromLeft
  obtain ⟨_, readRight, sameCode⟩ := Option.map_eq_some_iff.mp fromRight
  cases sameCode
  exact radixCode?_injective (by decide) readLeft readRight

#print axioms UserString.ofUnits?_injective

/-! ## Assemblies, types and kinds -/

/-- The four version numbers of an `Assembly` or `AssemblyRef` row. -/
structure Version where
  major : Nat
  minor : Nat
  build : Nat
  revision : Nat
  deriving DecidableEq, Hashable, Ord, Repr

/-- An assembly by its name, version, culture and public key token. Name, version and culture
    are columns of its `Assembly` or `AssemblyRef` row; the culture is the empty name when
    neutral. An `Assembly` row holds the public key, whose token is the last eight bytes of its
    SHA-1 digest in reverse order; an `AssemblyRef` row holds the key or the token, as its
    `PublicKey` flag (0x0001) says. `publicKeyToken` is the number whose big-endian base-256
    digits are the eight token bytes in the order an `AssemblyRef` row stores them and display
    text writes them, and `none` for an assembly without a key. -/
structure AssemblyName where
  name : MetadataName
  version : Version
  culture : MetadataName
  /-- The strong-name token as a big-endian number, or `none` for a null token. -/
  publicKeyToken : Option Nat
  deriving DecidableEq, Hashable

/-- One row of a type's nesting chain: its namespace column and its name column. -/
structure TypeLevel where
  typeNamespace : MetadataName
  name : MetadataName
  deriving DecidableEq, Hashable

/-- A type by the assembly that defines it, its namespace and name columns, and the namespace
    and name columns of each enclosing type from the outermost. The assembly is the pinned
    assembly that holds the `TypeDef` row, reached by following `ExportedType` forwarders, so
    every reference to one type gives one value; producing it from a reference is the binding's
    job. Every column is a separate component, so no two distinct types share a value. -/
structure TypeIdentity where
  assembly : AssemblyName
  typeNamespace : MetadataName
  enclosing : List TypeLevel := []
  name : MetadataName
  deriving DecidableEq, Hashable

/-- The value types ECMA-335 encodes by element type (II.23.1.16), without an assembly. -/
inductive PrimitiveType where
  | boolean | char | sbyte | byte | int16 | uint16 | int32 | uint32 | int64 | uint64
  | single | double | intPtr | uintPtr
  deriving DecidableEq, Hashable, Repr

/-- The element type code of a primitive (0x02 to 0x0D, 0x18, 0x19). -/
def PrimitiveType.elementType : PrimitiveType → Nat
  | .boolean => 0x02 | .char => 0x03 | .sbyte => 0x04 | .byte => 0x05 | .int16 => 0x06
  | .uint16 => 0x07 | .int32 => 0x08 | .uint32 => 0x09 | .int64 => 0x0A | .uint64 => 0x0B
  | .single => 0x0C | .double => 0x0D | .intPtr => 0x18 | .uintPtr => 0x19

/-- What metadata says a named type is. -/
inductive TypeKind where
  | valueType
  | enumType (underlying : PrimitiveType)
  | classType
  | interfaceType
  deriving DecidableEq, Hashable, Repr

/-! ## Display -/

/-- The first UTF-16 code unit of a surrogate pair. -/
def highSurrogateStart : Nat := 0xD800

/-- The second UTF-16 code unit of a surrogate pair. -/
def lowSurrogateStart : Nat := 0xDC00

/-- The first UTF-16 code unit after the surrogates. -/
def surrogateEnd : Nat := 0xE000

/-- The first code point that UTF-16 writes as a surrogate pair. -/
def supplementaryStart : Nat := 0x10000

/-- The number of values each half of a surrogate pair carries. -/
def surrogateSpan : Nat := 0x400

/-- The UTF-16 code units of `text`. -/
def utf16Units (text : String) : List Nat :=
  text.toList.flatMap fun char =>
    if char.toNat < supplementaryStart then [char.toNat]
    else
      let offset := char.toNat - supplementaryStart
      [highSurrogateStart + offset / surrogateSpan, lowSurrogateStart + offset % surrogateSpan]

/-- The characters that UTF-16 `units` encode, or `none` at an unpaired surrogate. -/
def utf16Chars? : List Nat → Option (List Char)
  | [] => some []
  | [unit] => if unit < highSurrogateStart || surrogateEnd ≤ unit then some [Char.ofNat unit]
    else none
  | unit :: next :: rest =>
    if unit < highSurrogateStart || surrogateEnd ≤ unit then
      (Char.ofNat unit :: ·) <$> utf16Chars? (next :: rest)
    else if unit < lowSurrogateStart && lowSurrogateStart ≤ next && next < surrogateEnd then
      let point := supplementaryStart + (unit - highSurrogateStart) * surrogateSpan +
        (next - lowSurrogateStart)
      (Char.ofNat point :: ·) <$> utf16Chars? rest
    else none

/-- Inclusive code point ranges of the characters in Unicode categories Cc, Cf, Zl and Zp and
    of the non-ASCII characters in Zs, as the .NET 10 runtime classifies them. -/
def invisibleRanges : List (Nat × Nat) :=
  [(0x0000, 0x001F), (0x007F, 0x00A0), (0x00AD, 0x00AD), (0x0600, 0x0605), (0x061C, 0x061C),
    (0x06DD, 0x06DD), (0x070F, 0x070F), (0x0890, 0x0891), (0x08E2, 0x08E2), (0x1680, 0x1680),
    (0x180E, 0x180E), (0x2000, 0x200F), (0x2028, 0x202F), (0x205F, 0x2064), (0x2066, 0x206F),
    (0x3000, 0x3000), (0xFEFF, 0xFEFF), (0xFFF9, 0xFFFB), (0x110BD, 0x110BD),
    (0x110CD, 0x110CD), (0x13430, 0x1343F), (0x1BCA0, 0x1BCA3), (0x1D173, 0x1D17A),
    (0xE0001, 0xE0001), (0xE0020, 0xE007F)]

/-- Whether a character is a control, format, separator or non-ASCII space character, which
    shows as nothing or as a space, or reorders the text around it. -/
def isInvisible (char : Char) : Bool :=
  invisibleRanges.any fun (low, high) => low ≤ char.toNat && char.toNat ≤ high

/-- The number of hexadecimal digits of a `\uHHHH` escape. -/
def unicodeEscapeDigits : Nat := 4

/-- The escape `\uHHHH` of a character below U+10000. -/
def unicodeEscape (char : Char) : String :=
  let digits := upperHexDigits char.toNat
  "\\u" ++ String.ofList (List.replicate (unicodeEscapeDigits - digits.length) '0') ++ digits

/-- `text` with `\` written `\\`, `"` written `\"` when `quoted`, and each invisible character
    written `\uHHHH`; `none` when an invisible character lies above U+FFFF, which a Lean string
    literal cannot escape. Every `\` of the result starts an escape, so it determines `text`. -/
def escapedText? (quoted : Bool) (text : String) : Option String :=
  if text.any fun char => supplementaryStart ≤ char.toNat && isInvisible char then none
  else some (String.join (text.toList.map fun char =>
    if char == '\\' then "\\\\"
    else if quoted && char == '"' then "\\\""
    else if isInvisible char then unicodeEscape char
    else char.toString))

/-- `text` as `escapedText?` writes it without quotes, with a leading `{` written `\{` so that
    no text reads as the raw structure of a code. -/
def readableText? (text : String) : Option String := do
  let escaped ← escapedText? false text
  return if text.startsWith "{" then "\\" ++ escaped else escaped

/-- A Lean string literal that elaborates to `text`, with invisible characters escaped. -/
def quotedText? (text : String) : Option String :=
  (fun escaped => "\"" ++ escaped ++ "\"") <$> escapedText? true text

/-- The hexadecimal digit count obtained from the highest set bit contains the complete code. -/
theorem hexCode_bound (code : Nat) : code < (2 ^ 4) ^ (code.log2 / 4 + 1) := by
  rw [← Nat.pow_mul]
  apply Nat.lt_of_lt_of_le Nat.lt_log2_self
  apply Nat.pow_le_pow_right (by decide)
  omega

#print axioms hexCode_bound

/-- The digits used by raw hexadecimal display retain the exact natural code. -/
theorem fixedDigits_hex_exact (code : Nat) :
    radixCode? 16 (fixedDigits 4 (code.log2 / 4 + 1) code []) 0 = some code := by
  simpa [radixCode?] using
    fixedDigits_spec 4 (code.log2 / 4 + 1) code (hexCode_bound code) [] 0

#print axioms fixedDigits_hex_exact

/-- Minimal lowercase hexadecimal digits of a natural code, including one digit for zero. -/
def rawCodeHex (code : Nat) : String :=
  let count := code.log2 / 4 + 1
  let digits := fixedDigits 4 count code []
  String.ofList (digits.map Nat.digitChar)

/-- The raw structure of a code, for a value that no text shows faithfully. Its leading `{`
    sets it apart from every `readableText?`. -/
def rawCodeDisplay (code : Nat) : String :=
  "{ code := 0x" ++ rawCodeHex code ++ " }"

/-- The text of a name, or `none` when its code is malformed or its bytes are not UTF-8. -/
def MetadataName.text? (name : MetadataName) : Option String := do
  let bytes ← name.bytes?
  String.fromUTF8? ⟨(bytes.map Nat.toUInt8).toArray⟩

/-- The text of a name as `readableText?` writes it, or `none` when there is none. -/
def MetadataName.readable? (name : MetadataName) : Option String :=
  name.text? >>= readableText?

/-- The text of a name as `readableText?` writes it, or the raw structure of its code; distinct
    names never display alike. -/
def MetadataName.display (name : MetadataName) : String :=
  name.readable?.getD (rawCodeDisplay name.code)

/-- The `name!` literal of a name, or `none` when it has no text, holds a NUL, which no
    `#Strings` entry can, or holds an invisible character above U+FFFF. -/
def MetadataName.literal? (name : MetadataName) : Option String := do
  let text ← name.text?
  guard (!text.contains '\x00')
  quotedText? text

/-- The text of a literal, or `none` when its code is malformed or holds an unpaired
    surrogate. -/
def UserString.text? (literal : UserString) : Option String := do
  let units ← literal.units?
  String.ofList <$> utf16Chars? units

/-- The text of a literal as `readableText?` writes it, or the raw structure of its code;
    distinct literals never display alike. -/
def UserString.display (literal : UserString) : String :=
  (literal.text? >>= readableText?).getD (rawCodeDisplay literal.code)

/-- The `str!` literal of a literal, or `none` when it has no text or holds an invisible
    character above U+FFFF. -/
def UserString.literal? (literal : UserString) : Option String :=
  literal.text? >>= quotedText?

instance : Repr MetadataName where
  reprPrec name _ := match name.literal? with
    | some quoted => "name!" ++ quoted
    | none => rawCodeDisplay name.code

instance : Repr UserString where
  reprPrec literal _ := match literal.literal? with
    | some quoted => "str!" ++ quoted
    | none => rawCodeDisplay literal.code

deriving instance Repr for AssemblyName
deriving instance Repr for TypeLevel
deriving instance Repr for TypeIdentity

/-- Dotted version numbers, such as `11.0.0.0`. -/
def Version.display (version : Version) : String :=
  s!"{version.major}.{version.minor}.{version.build}.{version.revision}"

/-- The number of hexadecimal digits of a public key token. -/
def publicKeyTokenDigits : Nat := 16

/-- A public key token as sixteen lowercase hexadecimal digits, or `null`. -/
def publicKeyTokenText : Option Nat → String
  | none => "null"
  | some token =>
    let digits := Nat.toDigits 16 token
    String.ofList (List.replicate (publicKeyTokenDigits - digits.length) '0' ++ digits)

/-- The readable name of an assembly and its readable culture, `neutral` for the empty culture,
    when both have text free of `,` and `]` and the culture is not spelled `neutral`. Text built
    from these parts then splits back at its separators into exactly this assembly. -/
def AssemblyName.parts? (assembly : AssemblyName) : Option (String × String) := do
  let name ← assembly.name.readable?
  let culture ← assembly.culture.readable?
  guard ([name, culture].all fun text => !text.contains ',' && !text.contains ']')
  guard (culture != "neutral")
  return (name, if culture.isEmpty then "neutral" else culture)

/-- The display name of an assembly, such as
    `System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a`, when
    `AssemblyName.parts?` reads it. -/
def AssemblyName.text? (assembly : AssemblyName) : Option String := do
  let (name, culture) ← assembly.parts?
  return s!"{name}, Version={assembly.version.display}, Culture={culture}, " ++
    s!"PublicKeyToken={publicKeyTokenText assembly.publicKeyToken}"

/-- The display name of an assembly, or its `Repr` structure when no display name determines
    it; distinct assemblies never display alike. -/
def AssemblyName.display (assembly : AssemblyName) : String :=
  assembly.text?.getD (reprStr assembly)

/-- An assembly as the scope of a type: `[Name,Version]` when its culture is neutral and its
    token null, otherwise `[Name,Version,Culture,Token]`; see `AssemblyName.parts?`. -/
def AssemblyName.scopeText? (assembly : AssemblyName) : Option String := do
  let (name, culture) ← assembly.parts?
  let version := assembly.version.display
  if assembly.culture.code == 1 && assembly.publicKeyToken.isNone then
    return s!"[{name},{version}]"
  return s!"[{name},{version},{culture},{publicKeyTokenText assembly.publicKeyToken}]"

/-- One level of a nesting chain as `Namespace.Name` of readable texts, or `Name` in the empty
    namespace, when both parts have text, the namespace holds no `/` and the name no `.` or `/`.
    The level then splits back at its last `.`. -/
def TypeLevel.text? (level : TypeLevel) : Option String := do
  let typeNamespace ← level.typeNamespace.readable?
  let name ← level.name.readable?
  guard (!typeNamespace.contains '/' && !name.contains '.' && !name.contains '/')
  return if typeNamespace.isEmpty then name else typeNamespace ++ "." ++ name

/-- The levels of a type from the outermost, its own level last. -/
def TypeIdentity.levels (type : TypeIdentity) : List TypeLevel :=
  type.enclosing ++ [⟨type.typeNamespace, type.name⟩]

/-- A type in ILAsm form with its full assembly scope, `[Name,Version]Namespace.Outer/Name`,
    when its scope and every level read as text; such text determines the type. -/
def TypeIdentity.text? (type : TypeIdentity) : Option String := do
  let scope ← type.assembly.scopeText?
  let levels ← type.levels.mapM TypeLevel.text?
  return scope ++ "/".intercalate levels

/-- A type as `TypeIdentity.text?` writes it, such as `[Examples,1.0.0.0]Examples.Point`, or
    its `Repr` structure; distinct types never display alike. -/
def TypeIdentity.display (type : TypeIdentity) : String :=
  type.text?.getD (reprStr type)

/-- The full name Cecil and method signatures give a primitive, such as `System.Int32`. -/
def PrimitiveType.display : PrimitiveType → String
  | .boolean => "System.Boolean" | .char => "System.Char" | .sbyte => "System.SByte"
  | .byte => "System.Byte" | .int16 => "System.Int16" | .uint16 => "System.UInt16"
  | .int32 => "System.Int32" | .uint32 => "System.UInt32" | .int64 => "System.Int64"
  | .uint64 => "System.UInt64" | .single => "System.Single" | .double => "System.Double"
  | .intPtr => "System.IntPtr" | .uintPtr => "System.UIntPtr"

/-! ## Notation -/

section Notation

open Lean Elab Term Meta PrettyPrinter Delaborator SubExpr

/-- `name!"Int32"` is the `MetadataName` of the UTF-8 bytes of the literal, computed when the
    term is elaborated. -/
syntax:max (name := metadataNameLiteral) "name!" str : term

/-- `str!"text"` is the `UserString` of the UTF-16 code units of the literal, computed when the
    term is elaborated. -/
syntax:max (name := userStringLiteral) "str!" str : term

/-- Display-only notation for a closed `TypeIdentity`; refused as input, so that no text is
    parsed into a type. -/
syntax:max (name := typeIdentityDisplay) "type!" str : term

/-- Elaborates `name!"..."` to `MetadataName.mk` of the literal's code; refuses a NUL, since a
    `#Strings` entry ends at its first NUL and no metadata name holds one. -/
@[term_elab metadataNameLiteral] def elabMetadataName : TermElab := fun syntaxTree _ => do
  let some text := syntaxTree[1].isStrLit? | throwUnsupportedSyntax
  if text.contains '\x00' then throwError "name!: a metadata name cannot hold a NUL character"
  let some name := MetadataName.ofBytes? (text.toUTF8.toList.map UInt8.toNat)
    | throwError "name!: a UTF-8 byte is out of range"
  return mkApp (mkConst ``MetadataName.mk) (mkNatLit name.code)

/-- Elaborates `str!"..."` to `UserString.mk` of the literal's code. -/
@[term_elab userStringLiteral] def elabUserString : TermElab := fun syntaxTree _ => do
  let some text := syntaxTree[1].isStrLit? | throwUnsupportedSyntax
  let some literal := UserString.ofUnits? (utf16Units text)
    | throwError "str!: a UTF-16 code unit is out of range"
  return mkApp (mkConst ``UserString.mk) (mkNatLit literal.code)

/-- Refuses `type!"..."` as input. -/
@[term_elab typeIdentityDisplay] def elabTypeIdentityDisplay : TermElab := fun _ _ =>
  throwError "type!\"...\" is display only; write the TypeIdentity structure"

/-- How many constants the type delaborator unfolds to reach one component's literal. -/
def identityUnfoldLimit : Nat := 8

/-- `term` with at most `identityUnfoldLimit` constants at its head unfolded. -/
def unfoldIdentityConstants (term : Expr) : MetaM Expr := do
  let mut current := term.consumeMData
  for _ in [0:identityUnfoldLimit] do
    unless current.isConst do break
    let some unfolded ← unfoldDefinition? current | break
    current := unfolded.consumeMData
  return current

/-- The name a term spells as `MetadataName.mk` of a literal, through named constants. -/
def metadataNameLiteral? (term : Expr) : MetaM (Option MetadataName) := do
  let term ← unfoldIdentityConstants term
  unless term.isAppOfArity ``MetadataName.mk 1 do return none
  return MetadataName.mk <$> natLiteral? term.appArg!

/-- The level a term spells as `TypeLevel.mk` of two name literals, through named constants. -/
def typeLevelLiteral? (term : Expr) : MetaM (Option TypeLevel) := do
  let term ← unfoldIdentityConstants term
  let #[typeNamespace, name] := term.getAppArgs | return none
  unless term.isAppOf ``TypeLevel.mk do return none
  let some typeNamespace ← metadataNameLiteral? typeNamespace | return none
  let some name ← metadataNameLiteral? name | return none
  return some ⟨typeNamespace, name⟩

/-- The levels a list literal of `TypeLevel.mk` literals spells. -/
partial def typeLevelList? (term : Expr) : MetaM (Option (List TypeLevel)) := do
  let term ← unfoldIdentityConstants term
  if term.isAppOfArity ``List.nil 1 then return some []
  unless term.isAppOfArity ``List.cons 3 do return none
  let some head ← typeLevelLiteral? (term.getArg! 1) | return none
  let some tail ← typeLevelList? (term.getArg! 2) | return none
  return some (head :: tail)

/-- The version a term spells as `Version.mk` of four literals, through named constants. -/
def versionLiteral? (term : Expr) : MetaM (Option Version) := do
  let term ← unfoldIdentityConstants term
  let #[major, minor, build, revision] := term.getAppArgs | return none
  unless term.isAppOf ``Version.mk do return none
  return return ⟨← natLiteral? major, ← natLiteral? minor, ← natLiteral? build,
    ← natLiteral? revision⟩

/-- The token a term spells as `none` or `some` of a literal, through named constants. -/
def publicKeyTokenLiteral? (term : Expr) : MetaM (Option (Option Nat)) := do
  let term ← unfoldIdentityConstants term
  if term.isAppOfArity ``Option.none 1 then return some none
  unless term.isAppOfArity ``Option.some 2 do return none
  return some <$> natLiteral? term.appArg!

/-- The assembly a term spells as `AssemblyName.mk` of literals, through named constants. -/
def assemblyNameLiteral? (term : Expr) : MetaM (Option AssemblyName) := do
  let term ← unfoldIdentityConstants term
  let #[name, version, culture, token] := term.getAppArgs | return none
  unless term.isAppOf ``AssemblyName.mk do return none
  let some name ← metadataNameLiteral? name | return none
  let some version ← versionLiteral? version | return none
  let some culture ← metadataNameLiteral? culture | return none
  let some token ← publicKeyTokenLiteral? token | return none
  return some ⟨name, version, culture, token⟩

/-- The type a `TypeIdentity.mk` term spells when every component is a literal, reading
    literals and unfolding named constants but evaluating nothing. Linear in the term's size. -/
def typeIdentityLiteral? (term : Expr) : MetaM (Option TypeIdentity) := do
  let #[assembly, typeNamespace, enclosing, name] := term.getAppArgs | return none
  let some assembly ← assemblyNameLiteral? assembly | return none
  let some typeNamespace ← metadataNameLiteral? typeNamespace | return none
  let some enclosing ← typeLevelList? enclosing | return none
  let some name ← metadataNameLiteral? name | return none
  return some ⟨assembly, typeNamespace, enclosing, name⟩

/-- Prints a name as its `MetadataName.literal?`, which elaborates back to it; any other name
    keeps its raw structure. -/
@[delab app.CIL.MetadataName.mk] def delabMetadataName : Delab := do
  if ← getPPOption getPPAll then failure
  let #[codeTerm] := (← getExpr).getAppArgs | failure
  let some code := natLiteral? codeTerm | failure
  if let some quoted := (MetadataName.mk code).literal? then
    `(name! $(⟨Syntax.mkLit strLitKind quoted⟩))
  else
    let field ← `(Parser.Term.structInstLVal| $(mkIdent `code):ident)
    `({ $field := $(Syntax.mkNumLit ("0x" ++ rawCodeHex code)) })

/-- Prints a literal as its `UserString.literal?`, which elaborates back to it; any other
    literal keeps its raw structure. -/
@[delab app.CIL.UserString.mk] def delabUserString : Delab := do
  if ← getPPOption getPPAll then failure
  let #[codeTerm] := (← getExpr).getAppArgs | failure
  let some code := natLiteral? codeTerm | failure
  if let some quoted := (UserString.mk code).literal? then
    `(str! $(⟨Syntax.mkLit strLitKind quoted⟩))
  else
    let field ← `(Parser.Term.structInstLVal| $(mkIdent `code):ident)
    `({ $field := $(Syntax.mkNumLit ("0x" ++ rawCodeHex code)) })

/-- Prints a type whose components are all literals as `type!"..."` when `TypeIdentity.text?`
    reads it, so the printed text determines the type; any other type keeps its structure. -/
@[delab app.CIL.TypeIdentity.mk] def delabTypeIdentity : Delab := do
  if ← getPPOption getPPAll then failure
  let some type ← typeIdentityLiteral? (← getExpr) | failure
  let some text := type.text? | failure
  `(type! $(Syntax.mkStrLit text))

end Notation

end CIL
