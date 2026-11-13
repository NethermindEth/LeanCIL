import StrictBinding.Tables
import StrictBinding.Sha1

/-!
# Heaps and assembly identity

Reads entries of the `#Strings` and `#Blob` heaps and spells the identity of the assembly an
image defines from its Assembly row, in the form the extractor records:
`Name, Version=a.b.c.d, Culture=neutral, PublicKeyToken=0123456789abcdef`. The token is the
strong-name token of the public key (`StrictBinding.Sha1.keyToken`), or `null` for an unsigned
assembly. A pinned image must spell the identity it is pinned under.
-/

namespace StrictBinding

/-- The bytes of the NUL-terminated string at `key` in the `#Strings` heap. -/
def MetadataLayout.stringAt (layout : MetadataLayout) (view : ImageView) (key : Nat) :
    Except AuditError (List Nat) := do
  let heap := layout.pe.strings
  if key >= heap.size then throw (.tables (.outsideHeap key))
  readName view (heap.start + key) (.tables (.outsideHeap key)) (heap.size - key)

/-- The length prefix of a blob (II.24.2.4): one byte below `0x80`, two bytes below `0xC0` and
    four bytes below `0xE0`. The result is the bytes of the prefix and the length it states. -/
def blobPrefix (view : ImageView) (offset : Nat) : Except AuditError (Nat × Nat) := do
  let first ← view.u offset 1
  if first < 0x80 then pure (1, first)
  else if first < 0xC0 then pure (2, (first - 0x80) * 2 ^ 8 + (← view.slice (offset + 1) 1))
  else if first < 0xE0 then pure (4, (first - 0xC0) * 2 ^ 24 + (← view.slice (offset + 1) 3))
  else throw (.tables (.outsideHeap offset))

/-- The bytes of the blob at `key` in the `#Blob` heap, which must lie inside the heap. -/
def MetadataLayout.blobAt (layout : MetadataLayout) (view : ImageView) (key : Nat) :
    Except AuditError (List Nat) := do
  let heap := layout.pe.blobs
  if key >= heap.size then throw (.tables (.outsideHeap key))
  let (prefixBytes, length) ← blobPrefix view (heap.start + key)
  if key + prefixBytes + length > heap.size then throw (.tables (.outsideHeap key))
  view.bytes (heap.start + key + prefixBytes) length

/-- The code points of well-formed UTF-8 bytes: shortest forms only, no surrogates. -/
def utf8CodePoints : Nat → List Nat → Option (List Nat)
  | 0, bytes => if bytes.isEmpty then some [] else none
  | _ + 1, [] => some []
  | fuel + 1, first :: rest =>
    let continuation (byte : Nat) : Bool := byte / 64 == 2
    let more (point : Nat) (remaining : List Nat) : Option (List Nat) :=
      (utf8CodePoints fuel remaining).map (point :: ·)
    if first < 0x80 then more first rest
    else if first / 32 == 6 then
      match rest with
      | second :: remaining =>
        let point := first % 32 * 64 + second % 64
        if continuation second && 0x80 <= point then more point remaining else none
      | [] => none
    else if first / 16 == 14 then
      match rest with
      | second :: third :: remaining =>
        let point := (first % 16 * 64 + second % 64) * 64 + third % 64
        if continuation second && continuation third && 0x800 <= point &&
            (point < 0xD800 || 0xDFFF < point) then more point remaining
        else none
      | _ => none
    else if first / 8 == 30 then
      match rest with
      | second :: third :: fourth :: remaining =>
        let point := ((first % 8 * 64 + second % 64) * 64 + third % 64) * 64 + fourth % 64
        if continuation second && continuation third && continuation fourth &&
            0x10000 <= point && point < 0x110000 then more point remaining
        else none
      | _ => none
    else none

/-- The code points of a string heap entry. -/
def MetadataLayout.stringText (layout : MetadataLayout) (view : ImageView) (key : Nat) :
    Except AuditError (List Nat) := do
  let bytes ← layout.stringAt view key
  let some points := utf8CodePoints bytes.length bytes | throw (.tables .invalidUtf8)
  pure points

/-- The code points of a text, which are ASCII for the identities audited here. -/
def asciiOf (text : String) : List Nat := text.toList.map Char.toNat

/-- The ASCII decimal digits of a version component, which is a 16-bit number. -/
def decimal (value : Nat) : List Nat :=
  let places := (List.range 5).map fun place => 48 + value / 10 ^ (4 - place) % 10
  match places.dropWhile (· == 48) with
  | [] => [48]
  | digits => digits

/-- `count` lowercase hexadecimal digits of a number, as ASCII. -/
def hexDigits (count value : Nat) : List Nat :=
  (List.range count).map fun place =>
    let digit := value / 16 ^ (count - 1 - place) % 16
    if digit < 10 then 48 + digit else 87 + digit

/-- The code points of the identity the Assembly row spells. -/
def assemblyIdentity (view : ImageView) (layout : MetadataLayout) :
    Except AuditError (List Nat) := do
  let row := tokenOf 0x20 1
  let major ← layout.cell view row 1
  let minor ← layout.cell view row 2
  let build ← layout.cell view row 3
  let revision ← layout.cell view row 4
  let key ← layout.blobAt view (← layout.cell view row 6)
  let name ← layout.stringText view (← layout.cell view row 7)
  let culture ← layout.stringText view (← layout.cell view row 8)
  let version := decimal major ++ [46] ++ decimal minor ++ [46] ++ decimal build ++ [46] ++
    decimal revision
  let token := if key.isEmpty then asciiOf "null" else hexDigits 16 (Sha1.keyToken key)
  pure (name ++ asciiOf ", Version=" ++ version ++ asciiOf ", Culture=" ++
    (if culture.isEmpty then asciiOf "neutral" else culture) ++ asciiOf ", PublicKeyToken=" ++
    token)

end StrictBinding
