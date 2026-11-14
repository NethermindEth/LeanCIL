import StrictBinding.Error
import CIL.Crypto.Words

/-!
# Image bytes and reads

An assembly file reaches the audit as an `ImageBytes` constant: the file zero-padded to a
multiple of 64 bytes, as big-endian 64-byte chunks in pages of at most 64 chunks. The chunks are
what SHA-256 hashes (`StrictBinding.Sha256`), and the same chunks, arranged once into a balanced
tree, are what every container and table read decodes. Both uses read one constant, so a digest
of the constant is a digest of the bytes that are decoded.

`ImageBytes.wellFormed` is required by every check: a chunk at or above `2 ^ 512` would hash one
way and read another. A read touches only the chunks that hold its bytes, found in time
logarithmic in the image size, so the cost of a check grows with the number of reads and the
bytes they cover, not with the image size per read. Values are joined pairwise, so joining `n`
bytes costs `n log n` rather than `n ^ 2`.
-/

namespace StrictBinding

open CIL.Crypto (joinValues bytesValue littleEndian chunkValues)

/-- The bits in one 64-byte chunk. -/
def chunkBits : Nat := 512

/-- The most chunks a page holds, so literals and nesting stay small. -/
def pageChunks : Nat := 64

/-- A file zero-padded to a multiple of 64 bytes, as big-endian chunks in pages. -/
structure ImageBytes where
  /-- The length of the file in bytes, before padding. -/
  length : Nat
  pages : List (List Nat)

/-- The chunks of all pages, in file order. -/
def ImageBytes.chunks (image : ImageBytes) : List Nat :=
  image.pages.foldr (fun page rest => page ++ rest) []

/-- The chunk count matches the length, every page is nonempty and at most `pageChunks` long,
    every chunk is below `2 ^ 512` and the padding after the last byte is zero. -/
def ImageBytes.wellFormed (image : ImageBytes) : Bool :=
  let chunks := image.chunks
  chunks.length == (image.length + 63) / 64 &&
    image.pages.all (fun page => !page.isEmpty && page.length <= pageChunks) &&
    chunks.all (· < 2 ^ chunkBits) &&
    chunks.getLastD 0 % 2 ^ (8 * (64 * chunks.length - image.length)) == 0

/-- The chunks of an image in a balanced tree, each node knowing how many chunks it holds. -/
inductive ChunkTree where
  | leaf (chunk : Nat)
  | node (count : Nat) (left right : ChunkTree)

/-- The number of chunks in a tree. -/
def ChunkTree.count : ChunkTree → Nat
  | .leaf _ => 1
  | .node count _ _ => count

/-- The chunk at an index, found by descending one subtree per level. -/
def ChunkTree.at : ChunkTree → Nat → Nat
  | .leaf chunk, _ => chunk
  | .node _ left right, index =>
    if index < left.count then left.at index else right.at (index - left.count)

/-- Adjacent trees joined under one node each. -/
def pairTrees : List ChunkTree → List ChunkTree
  | left :: right :: rest => .node (left.count + right.count) left right :: pairTrees rest
  | trees => trees

/-- One tree over all the given trees, built level by level. -/
def buildTree : Nat → List ChunkTree → Option ChunkTree
  | 0, trees => trees.head?
  | fuel + 1, trees =>
    match trees with
    | [] => none
    | [single] => some single
    | _ => buildTree fuel (pairTrees trees)

/-- A checked image, ready to be read. -/
structure ImageView where
  length : Nat
  chunks : Option ChunkTree

/-- The view of a well-formed image. -/
def ImageView.ofImage (image : ImageBytes) : Except AuditError ImageView :=
  if image.wellFormed then
    let chunks := image.chunks
    .ok { length := image.length, chunks := buildTree chunks.length (chunks.map .leaf) }
  else .error .malformedImage

/-- The big-endian value of `count` bytes at `offset`: the chunks that hold them, joined, with
    the bytes after them shifted out. -/
def ImageView.slice (view : ImageView) (offset count : Nat) : Except AuditError Nat :=
  match view.chunks with
  | some tree =>
    if offset + count <= view.length then
      if count == 0 then .ok 0
      else
        let first := offset / 64
        let last := (offset + count - 1) / 64
        let held := (List.range (last - first + 1)).map fun index =>
          (tree.at (first + index), chunkBits)
        let trailing := 8 * (64 * (last + 1) - (offset + count))
        .ok (Nat.mod (Nat.shiftRight (joinValues held.length held).1 trailing) (2 ^ (8 * count)))
    else .error (.outsideImage offset count)
  | none =>
    if count == 0 && offset <= view.length then .ok 0 else .error (.outsideImage offset count)

/-- The little-endian unsigned integer of `count` bytes at `offset`, as PE and metadata store
    integers. -/
def ImageView.u (view : ImageView) (offset count : Nat) : Except AuditError Nat :=
  (view.slice offset count).map (littleEndian count)

/-- The bytes at `offset` are exactly `bytes`, each a byte value. -/
def ImageView.hasBytesAt (view : ImageView) (offset : Nat) (bytes : List Nat) :
    Except AuditError Bool := do
  pure (bytes.all (· < 256) && (← view.slice offset bytes.length) == bytesValue bytes)

/-- The `count` bytes at `offset` as a byte list. -/
def ImageView.bytes (view : ImageView) (offset count : Nat) : Except AuditError (List Nat) :=
  (List.range count).mapM fun index => view.slice (offset + index) 1

/-- Splits a list into pages of at most `pageChunks` items. -/
def paginate : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | fuel + 1, chunks =>
    if chunks.isEmpty then [] else chunks.take pageChunks :: paginate fuel (chunks.drop pageChunks)

/-- The image of a file given as bytes, for tests and small inputs. -/
def ImageBytes.ofBytes (bytes : List Nat) : ImageBytes :=
  { length := bytes.length, pages := paginate bytes.length (chunkValues bytes.length bytes) }

/-- An image together with the assembly identity it must spell. -/
structure PinnedImage where
  identity : String
  image : ImageBytes

end StrictBinding
