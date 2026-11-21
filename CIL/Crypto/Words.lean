import Init

/-!
# Hash words and byte blocks

Numeric operations shared by SHA-1, SHA-256 and image reads. Byte lists are joined in balanced
groups, and hash messages are padded to 64-byte blocks.
-/

namespace CIL.Crypto

/-- Addition modulo `2 ^ 32`. -/
def add (left right : Nat) : Nat := Nat.mod (Nat.add left right) 4294967296

/-- Exclusive or of three words. -/
def xor3 (a b c : Nat) : Nat := Nat.xor (Nat.xor a b) c

/-- Selects `f` where `e` has a bit set and `g` elsewhere. -/
def choose (e f g : Nat) : Nat :=
  Nat.xor (Nat.land e f) (Nat.land (Nat.sub 4294967295 e) g)

/-- The bitwise majority of three words. -/
def majority (a b c : Nat) : Nat :=
  xor3 (Nat.land a b) (Nat.land a c) (Nat.land b c)

/-- The sixteen big-endian words of one 64-byte block. -/
def blockWords (block : Nat) : List Nat :=
  [480, 448, 416, 384, 352, 320, 288, 256, 224, 192, 160, 128, 96, 64, 32, 0].map
    fun shift => Nat.mod (Nat.shiftRight block shift) 4294967296

/-- The chunks of a message of `length` bytes with the FIPS padding: the `0x80` byte follows the
    last data byte and the bit length ends the last block. -/
def padded (chunks : List Nat) (length : Nat) : List Nat :=
  let tail := length % 64
  let opened :=
    if tail == 0 then 0x80 * 2 ^ 504 else chunks.getLastD 0 + 0x80 * 2 ^ (8 * (63 - tail))
  let full := if tail == 0 then chunks else chunks.dropLast
  if tail < 56 then full ++ [opened + 8 * length] else full ++ [opened, 8 * length]

/-- The big-endian number of a list of 32-bit words. -/
def wordsValue (words : List Nat) : Nat :=
  words.foldl (fun acc word => acc * 4294967296 + word) 0

/-- Values with their bit widths, adjacent pairs joined into one value of the summed width. -/
def joinPairs : List (Nat × Nat) → List (Nat × Nat)
  | (high, highWidth) :: (low, lowWidth) :: rest =>
    (high * 2 ^ lowWidth + low, highWidth + lowWidth) :: joinPairs rest
  | items => items

/-- The big-endian concatenation of values and the sum of their widths, joined level by level;
    the fuel is the item count, which halves at every level. -/
def joinValues : Nat → List (Nat × Nat) → Nat × Nat
  | 0, items => items.headD (0, 0)
  | fuel + 1, items =>
    match items with
    | [] => (0, 0)
    | [single] => single
    | _ => joinValues fuel (joinPairs items)

/-- The big-endian value of a byte list. -/
def bytesValue (bytes : List Nat) : Nat :=
  (joinValues bytes.length (bytes.map fun byte => (byte, 8))).1

/-- Reverses the order of the `count` bytes of a big-endian value. -/
def littleEndian : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, value => (value % 256) * 256 ^ count + littleEndian count (value / 256)

/-- Big-endian chunks of a byte list, zero-padded to whole chunks. -/
def chunkValues : Nat → List Nat → List Nat
  | 0, _ => []
  | fuel + 1, bytes =>
    if bytes.isEmpty then []
    else
      let block := bytes.take 64
      let chunk := bytesValue (block ++ List.replicate (64 - block.length) 0)
      chunk :: chunkValues fuel (bytes.drop 64)

end CIL.Crypto
