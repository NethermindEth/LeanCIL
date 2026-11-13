import StrictBinding.Image

/-!
# SHA-256 over image chunks

FIPS 180-4 SHA-256 written for kernel evaluation: state as lists, and direct `Nat` functions
(`Nat.xor`, `Nat.land`, `Nat.shiftRight`), which the kernel reduces natively. A message is its
64-byte chunks (`StrictBinding.ImageBytes`) and its length; `padded` appends the `0x80` byte and
the bit length in the last block. `DigestIs` is the statement audited theorems make about an image
constant: the image is well formed and its SHA-256 is the stated number.
-/

namespace StrictBinding.Sha256

/-- Addition modulo `2 ^ 32`. -/
def add (left right : Nat) : Nat := Nat.mod (Nat.add left right) 4294967296

/-- Rotation of a 32-bit word to the right. -/
def rotr (word amount : Nat) : Nat :=
  Nat.lor (Nat.shiftRight word amount) (Nat.mod (Nat.shiftLeft word (32 - amount)) 4294967296)

/-- Exclusive or of three words. -/
def xor3 (a b c : Nat) : Nat := Nat.xor (Nat.xor a b) c

/-- The compression function's upper-case sigma of `a`. -/
def bigSigma0 (word : Nat) : Nat := xor3 (rotr word 2) (rotr word 13) (rotr word 22)

/-- The compression function's upper-case sigma of `e`. -/
def bigSigma1 (word : Nat) : Nat := xor3 (rotr word 6) (rotr word 11) (rotr word 25)

/-- The message schedule's lower-case sigma of the second word back. -/
def smallSigma0 (word : Nat) : Nat := xor3 (rotr word 7) (rotr word 18) (Nat.shiftRight word 3)

/-- The message schedule's lower-case sigma of the fifteenth word back. -/
def smallSigma1 (word : Nat) : Nat := xor3 (rotr word 17) (rotr word 19) (Nat.shiftRight word 10)

/-- Selects `f` where `e` has a bit set and `g` elsewhere. -/
def choose (e f g : Nat) : Nat :=
  Nat.xor (Nat.land e f) (Nat.land (Nat.sub 4294967295 e) g)

/-- The bitwise majority of three words. -/
def majority (a b c : Nat) : Nat :=
  xor3 (Nat.land a b) (Nat.land a c) (Nat.land b c)

/-- The 64 round constants. -/
def roundConstants : List Nat :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The state before the first block. -/
def initialState : List Nat :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The `count` message schedule words that follow the sixteen words of a block. -/
def expand : Nat → List Nat → List Nat
  | 0, _ => []
  | count + 1, w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 ::
      w13 :: w14 :: w15 :: _ =>
    let next := add (add (smallSigma1 w14) w9) (add (smallSigma0 w1) w0)
    next :: expand count [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, next]
  | _ + 1, _ => []

/-- The 64 rounds over the constants and schedule words, returning the working variables. -/
def rounds : List Nat → List Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat
  | k :: ks, w :: ws, a, b, c, d, e, f, g, h =>
    let t1 := add (add (add h (bigSigma1 e)) (add (choose e f g) k)) w
    let t2 := add (bigSigma0 a) (majority a b c)
    rounds ks ws (add t1 t2) a b c (add d t1) e f g
  | _, _, a, b, c, d, e, f, g, h => [a, b, c, d, e, f, g, h]

/-- The sixteen big-endian words of one 64-byte block. -/
def blockWords (block : Nat) : List Nat :=
  [480, 448, 416, 384, 352, 320, 288, 256, 224, 192, 160, 128, 96, 64, 32, 0].map
    fun shift => Nat.mod (Nat.shiftRight block shift) 4294967296

/-- One block applied to the state. -/
def compress (state : List Nat) (block : Nat) : List Nat :=
  match state with
  | [a, b, c, d, e, f, g, h] =>
    let words := blockWords block
    match rounds roundConstants (words ++ expand 48 words) a b c d e f g h with
    | [a', b', c', d', e', f', g', h'] =>
      [add a a', add b b', add c c', add d d', add e e', add f f', add g g', add h h']
    | _ => []
  | _ => []

/-- All blocks applied in order. Both branches are equal; testing the state sum makes the kernel
    evaluate each block's state once instead of once per use. -/
def hashBlocks : List Nat → List Nat → List Nat
  | state, [] => state
  | state, block :: blocks =>
    let next := compress state block
    bif Nat.beq (next.foldl Nat.add 0) 0 then hashBlocks next blocks else hashBlocks next blocks

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

/-- All pages hashed in order, each from the state the previous one left. -/
def hashPages : List Nat → List (List Nat) → List Nat
  | state, [] => state
  | state, page :: pages => hashPages (hashBlocks state page) pages

/-- The pages to hash for a message of `length` bytes: every page but the last as it is, and the
    last page with the padding blocks. -/
def hashPlan (pages : List (List Nat)) (length : Nat) : List (List Nat) :=
  pages.dropLast ++ [padded (pages.getLastD []) length]

/-- The SHA-256 digest, as a number, of a message given as pages of zero-padded chunks and its
    length. -/
def ofPages (pages : List (List Nat)) (length : Nat) : Nat :=
  wordsValue (hashPages initialState (hashPlan pages length))

/-- Hashing `pages` from `state` gives `final`, with each page's result stated separately. One
    kernel evaluation of a whole image holds every intermediate term of every block; stating
    pages as separate lemmas bounds the memory of each evaluation to one page. -/
inductive PagesHash : List Nat → List (List Nat) → List Nat → Prop where
  | nil (state : List Nat) : PagesHash state [] state
  | cons {state next final page : List Nat} {pages : List (List Nat)} :
      hashBlocks state page = next → PagesHash next pages final →
      PagesHash state (page :: pages) final

/-- A chain of page results is the hash of the pages. -/
theorem PagesHash.hashPages_eq {state : List Nat} {pages : List (List Nat)} {final : List Nat}
    (chain : PagesHash state pages final) : hashPages state pages = final := by
  induction chain with
  | nil => rfl
  | cons step _ ih => rw [hashPages, step]; exact ih

#print axioms PagesHash.hashPages_eq

end StrictBinding.Sha256

namespace StrictBinding

/-- The image is well formed and its SHA-256 digest is `digest`. -/
def DigestIs (image : ImageBytes) (digest : Nat) : Prop :=
  image.wellFormed = true ∧ Sha256.ofPages image.pages image.length = digest

instance (image : ImageBytes) (digest : Nat) : Decidable (DigestIs image digest) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The digest of an image from per-page hash results: `blocks` are the pages to hash, `chain`
    hashes them to `final`, and `final` is the number `digest`. Each page result can be checked
    in its own kernel evaluation. -/
theorem digestIs_of_hashes {image : ImageBytes} {digest : Nat} {final : List Nat}
    {blocks : List (List Nat)} (plan : Sha256.hashPlan image.pages image.length = blocks)
    (chain : Sha256.PagesHash Sha256.initialState blocks final)
    (wellFormed : image.wellFormed = true) (value : Sha256.wordsValue final = digest) :
    DigestIs image digest := by
  refine ⟨wellFormed, ?_⟩
  unfold Sha256.ofPages
  rw [plan, chain.hashPages_eq]
  exact value

#print axioms digestIs_of_hashes

end StrictBinding
