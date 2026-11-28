import StrictBinding.Image
import CIL.Safety.Execution

/-!
# Reads of image bytes

A check reads the bytes it compares with one `ImageView.slice`, which joins the chunks that hold
them into one value, and a proposition about an image states those bytes with `ImageView.bytes`,
one byte at a time. In a view whose chunks are each below `2 ^ chunkBits`, as every view
`ImageView.ofImage` builds is, the two agree: `bytes_of_hasBytesAt` turns a successful
comparison into the bytes the image holds there.
-/

namespace StrictBinding

open CIL.Crypto

/-- One step of a big-endian concatenation: the value so far, shifted past the next item. -/
def joinStep (value : Nat) (item : Nat × Nat) : Nat := value * 2 ^ item.2 + item.1

/-- Joining adjacent pairs first does not change a big-endian concatenation. -/
theorem foldl_joinPairs (items : List (Nat × Nat)) (value : Nat) :
    (joinPairs items).foldl joinStep value = items.foldl joinStep value := by
  induction items using joinPairs.induct generalizing value with
  | case1 high highWidth low lowWidth rest onRest =>
    simp only [joinPairs, List.foldl_cons, onRest]
    congr 1
    simp only [joinStep, Nat.pow_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  | case2 items notPair =>
    match items, notPair with
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _, notPair => exact absurd rfl (notPair _ _ _ _ _)

#print axioms foldl_joinPairs

/-- Joining adjacent pairs halves a list, rounding up. -/
theorem length_joinPairs (items : List (Nat × Nat)) :
    (joinPairs items).length = (items.length + 1) / 2 := by
  induction items using joinPairs.induct with
  | case1 high highWidth low lowWidth rest onRest =>
    simp only [joinPairs, List.length_cons, onRest]; omega
  | case2 items notPair =>
    match items, notPair with
    | [], _ => rfl
    | [_], _ => simp [joinPairs]
    | _ :: _ :: _, notPair => exact absurd rfl (notPair _ _ _ _ _)

#print axioms length_joinPairs

/-- With enough fuel, `joinValues` computes the big-endian concatenation of the items. -/
theorem joinValues_fst (fuel : Nat) (items : List (Nat × Nat)) (fits : items.length ≤ fuel + 1) :
    (joinValues fuel items).1 = items.foldl joinStep 0 := by
  induction fuel generalizing items with
  | zero =>
    match items, fits with
    | [], _ => rfl
    | [item], _ => simp [joinValues, joinStep]
  | succ fuel onRest =>
    match items with
    | [] => rfl
    | [item] => simp [joinValues, joinStep]
    | first :: second :: rest =>
      simp only [joinValues]
      rw [onRest _ (by simp only [length_joinPairs, List.length_cons] at fits ⊢; omega),
        foldl_joinPairs]

#print axioms joinValues_fst

/-- The bits of a concatenation of `count` values of `width` bits each. -/
theorem testBit_foldl_joinStep (value : Nat → Nat) {width : Nat} (positive : 0 < width)
    (fits : ∀ index, value index < 2 ^ width) (count bit : Nat) :
    Nat.testBit (((List.range count).map fun index => (value index, width)).foldl joinStep 0) bit =
      (decide (bit < width * count) &&
        (value (count - 1 - bit / width)).testBit (bit % width)) := by
  induction count generalizing bit with
  | zero => simp
  | succ count onRest =>
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, joinStep]
    rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (fits count)]
    by_cases low : bit < width
    · simp only [low, ite_true, Nat.div_eq_of_lt low, Nat.mod_eq_of_lt low]
      have : bit < width * (count + 1) := by rw [Nat.mul_succ]; omega
      simp [this]
    · simp only [low, ite_false]
      obtain ⟨rest, rfl⟩ : ∃ rest, bit = rest + width := ⟨bit - width, by omega⟩
      rw [Nat.add_sub_cancel, onRest, Nat.add_div_right _ positive, Nat.add_mod_right]
      have same : decide (rest < width * count) = decide (rest + width < width * (count + 1)) := by
        rw [Nat.mul_succ]; simp
      rw [same]
      congr 3
      omega

#print axioms testBit_foldl_joinStep

/-- Every chunk a view holds is below `2 ^ chunkBits`, as `ImageView.ofImage` requires. -/
def ImageView.Bounded (view : ImageView) : Prop :=
  match view.chunks with
  | some tree => ∀ index, tree.at index < 2 ^ chunkBits
  | none => True

/-- The bits of a read: bit `bit` of the value of `count` bytes at `offset` is a bit of the byte
    at `offset + count - 1 - bit / 8`, in the chunk that holds it. -/
theorem testBit_slice {view : ImageView} (bounded : view.Bounded) {offset count value : Nat}
    (read : view.slice offset count = .ok value) (positive : 0 < count) (bit : Nat) :
    ∃ tree, view.chunks = some tree ∧
      value.testBit bit = (decide (bit < 8 * count) &&
        (tree.at ((offset + count - 1 - bit / 8) / 64)).testBit
          (8 * (63 - (offset + count - 1 - bit / 8) % 64) + bit % 8)) := by
  unfold ImageView.slice at read
  cases chunksEq : view.chunks with
  | none =>
    simp only [chunksEq] at read
    split at read
    · rename_i empty; simp at empty; omega
    · cases read
  | some tree =>
    refine ⟨tree, rfl, ?_⟩
    have fits : ∀ index, tree.at index < 2 ^ chunkBits := by
      simpa [ImageView.Bounded, chunksEq] using bounded
    simp only [chunksEq] at read
    split at read
    · rename_i inside
      have nonzero : (count == 0) = false := by simp; omega
      simp only [nonzero, Bool.false_eq_true, ite_false] at read
      injection read with read
      subst read
      rw [show ∀ value modulus : Nat, Nat.mod value modulus = value % modulus from fun _ _ => rfl,
        show ∀ value shift : Nat, Nat.shiftRight value shift = value >>> shift from fun _ _ => rfl,
        Nat.testBit_mod_two_pow, Nat.shiftRight_eq_div_pow, Nat.testBit_div_two_pow,
        joinValues_fst _ _ (by simp),
        testBit_foldl_joinStep (fun index => tree.at (offset / 64 + index)) (by decide)
          (fun index => fits _)]
      by_cases low : bit < 8 * count
      · simp only [low, decide_true, Bool.true_and, chunkBits]
        have within : bit + 8 * (64 * ((offset + count - 1) / 64 + 1) - (offset + count)) <
            512 * ((offset + count - 1) / 64 - offset / 64 + 1) := by omega
        simp only [within, decide_true, Bool.true_and]
        congr 2 <;> omega
      · simp [low]
    · cases read

#print axioms testBit_slice

/-- A read that succeeds is inside the image. -/
theorem slice_inside {view : ImageView} {offset count value : Nat}
    (read : view.slice offset count = .ok value) (positive : 0 < count) :
    offset + count ≤ view.length ∧ view.chunks.isSome := by
  unfold ImageView.slice at read
  cases chunksEq : view.chunks with
  | none =>
    simp only [chunksEq] at read
    split at read
    · rename_i empty; simp at empty; omega
    · cases read
  | some tree =>
    simp only [chunksEq] at read
    split at read
    · rename_i inside; exact ⟨inside, rfl⟩
    · cases read

#print axioms slice_inside

/-- A read inside an image with chunks succeeds. -/
theorem slice_of_inside {view : ImageView} {offset count : Nat}
    (inside : offset + count ≤ view.length) (held : view.chunks.isSome) :
    ∃ value, view.slice offset count = .ok value := by
  unfold ImageView.slice
  cases chunksEq : view.chunks with
  | none => simp [chunksEq] at held
  | some tree =>
    simp only [inside, ite_true]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

#print axioms slice_of_inside

/-- The big-endian bytes of the low `count` bytes of a value. -/
def valueBytes (count value : Nat) : List Nat :=
  (List.range count).map fun index => value / 256 ^ (count - 1 - index) % 256

/-- Bit `bit` of byte `shift` bytes from the right of a value. -/
theorem testBit_byte (value shift bit : Nat) :
    (value / 256 ^ shift % 256).testBit bit =
      (decide (bit < 8) && value.testBit (bit + 8 * shift)) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.mul_comm 8 shift]

#print axioms testBit_byte

/-- Mapping a list through a check that succeeds on every item succeeds with the results. -/
theorem mapM_ok {ε α β : Type} {check : α → Except ε β} {result : α → β} :
    ∀ {items : List α}, (∀ item ∈ items, check item = .ok (result item)) →
      items.mapM check = .ok (items.map result)
  | [], _ => rfl
  | item :: rest, each => by
    simp only [List.mapM_cons, each item (List.mem_cons_self ..),
      mapM_ok (fun other inside => each other (List.mem_cons_of_mem _ inside))]
    rfl

#print axioms mapM_ok

/-- The value of `count` bytes read at once is the bytes read one at a time. -/
theorem bytes_of_slice {view : ImageView} (bounded : view.Bounded) {offset count value : Nat}
    (read : view.slice offset count = .ok value) :
    view.bytes offset count = .ok (valueBytes count value) := by
  unfold ImageView.bytes valueBytes
  apply mapM_ok
  intro index member
  have below : index < count := List.mem_range.mp member
  have ⟨inside, held⟩ := slice_inside read (by omega)
  have ⟨byte, readByte⟩ := slice_of_inside (offset := offset + index) (count := 1) (by omega) held
  rw [readByte]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro bit
  have ⟨tree, chunksEq, byteBit⟩ := testBit_slice bounded readByte (by decide) bit
  have ⟨sameTree, sameChunks, valueBit⟩ :=
    testBit_slice bounded read (by omega) (bit + 8 * (count - 1 - index))
  rw [chunksEq] at sameChunks
  cases sameChunks
  rw [byteBit, testBit_byte, valueBit]
  by_cases low : bit < 8
  · have position : offset + count - 1 - (bit + 8 * (count - 1 - index)) / 8 =
        offset + index + 1 - 1 - bit / 8 := by omega
    have within : (bit + 8 * (count - 1 - index)) % 8 = bit % 8 := by omega
    have inByte : bit + 8 * (count - 1 - index) < 8 * count := by omega
    simp [position, within, inByte, low]
  · simp [low]

#print axioms bytes_of_slice

/-- Bytes are the big-endian bytes of their value. -/
theorem valueBytes_bytesValue {bytes : List Nat} (small : bytes.all (· < 256) = true) :
    valueBytes bytes.length (bytesValue bytes) = bytes := by
  have items : bytes.map (fun byte => (byte, 8)) =
      (List.range bytes.length).map fun index => (bytes.getD index 0, 8) := by
    apply List.ext_getElem
    · simp
    · intro index inMap _
      simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by simpa using inMap)]
      rfl
  have fits : ∀ index, bytes.getD index 0 < 2 ^ 8 := by
    intro index
    simp only [List.all_eq_true, decide_eq_true_eq] at small
    rw [List.getD_eq_getElem?_getD]
    cases found : bytes[index]? with
    | none => simp
    | some byte => exact small byte (List.mem_of_getElem? found)
  apply List.ext_getElem
  · simp [valueBytes]
  · intro index inValue inBytes
    simp only [valueBytes, List.getElem_map, List.getElem_range]
    apply Nat.eq_of_testBit_eq
    intro bit
    rw [testBit_byte, bytesValue, joinValues_fst _ _ (by simp), items,
      testBit_foldl_joinStep _ (by decide) fits]
    by_cases low : bit < 8
    · have position : bytes.length - 1 - (bit + 8 * (bytes.length - 1 - index)) / 8 = index := by
        omega
      have within : (bit + 8 * (bytes.length - 1 - index)) % 8 = bit := by omega
      have inside : bit + 8 * (bytes.length - 1 - index) < 8 * bytes.length := by omega
      simp [position, within, inside, low, List.getD_eq_getElem?_getD, inBytes]
    · have byteFits : bytes[index] < 2 ^ 8 := by
        simpa [List.getD_eq_getElem?_getD, inBytes] using fits index
      have large : bytes[index] < 2 ^ bit :=
        Nat.lt_of_lt_of_le byteFits (Nat.pow_le_pow_right (by decide) (by omega))
      simp [low, Nat.testBit_lt_two_pow large]

#print axioms valueBytes_bytesValue

/-- Bytes found at an offset are the bytes read there one at a time. -/
theorem bytes_of_hasBytesAt {view : ImageView} (bounded : view.Bounded) {offset : Nat}
    {bytes : List Nat} (found : view.hasBytesAt offset bytes = .ok true) :
    view.bytes offset bytes.length = .ok bytes := by
  unfold ImageView.hasBytesAt at found
  cases read : view.slice offset bytes.length with
  | error _ => simp [read, bind, Except.bind] at found
  | ok value =>
    simp only [read, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Bool.and_eq_true,
      beq_iff_eq] at found
    rw [bytes_of_slice bounded read, found.2, valueBytes_bytesValue found.1]

#print axioms bytes_of_hasBytesAt

/-! ## Views of well-formed images -/

/-- Every leaf of a tree is below `2 ^ chunkBits`. -/
def ChunkTree.Bounded : ChunkTree → Prop
  | .leaf chunk => chunk < 2 ^ chunkBits
  | .node _ left right => left.Bounded ∧ right.Bounded

/-- Every chunk a bounded tree holds is below `2 ^ chunkBits`. -/
theorem ChunkTree.at_lt {tree : ChunkTree} (bounded : tree.Bounded) (index : Nat) :
    tree.at index < 2 ^ chunkBits := by
  induction tree generalizing index with
  | leaf chunk => exact bounded
  | node count left right inLeft inRight =>
    simp only [ChunkTree.at]
    split
    · exact inLeft bounded.1 _
    · exact inRight bounded.2 _

#print axioms ChunkTree.at_lt

/-- Pairing bounded trees gives bounded trees. -/
theorem pairTrees_bounded {trees : List ChunkTree} (bounded : ∀ tree ∈ trees, tree.Bounded) :
    ∀ tree ∈ pairTrees trees, tree.Bounded := by
  induction trees using pairTrees.induct with
  | case1 left right rest inRest =>
    simp only [pairTrees, List.mem_cons, forall_eq_or_imp] at bounded ⊢
    exact ⟨⟨bounded.1, bounded.2.1⟩, inRest bounded.2.2⟩
  | case2 trees notPair =>
    match trees, notPair with
    | [], _ => simp [pairTrees]
    | [_], _ => simpa [pairTrees] using bounded
    | _ :: _ :: _, notPair => exact absurd rfl (notPair _ _ _)

#print axioms pairTrees_bounded

/-- The tree built from bounded trees is bounded. -/
theorem buildTree_bounded :
    ∀ (fuel : Nat) {trees : List ChunkTree}, (∀ tree ∈ trees, tree.Bounded) →
      ∀ {tree : ChunkTree}, buildTree fuel trees = some tree → tree.Bounded
  | 0, trees, bounded, tree, built => by
    cases trees with
    | nil => cases built
    | cons first _ =>
      simp only [buildTree, List.head?_cons, Option.some.injEq] at built
      exact built ▸ bounded first (List.mem_cons_self ..)
  | fuel + 1, trees, bounded, tree, built => by
    match trees with
    | [] => cases built
    | [single] =>
      simp only [buildTree, Option.some.injEq] at built
      exact built ▸ bounded single (List.mem_cons_self ..)
    | first :: second :: rest =>
      exact buildTree_bounded fuel (pairTrees_bounded bounded) built

#print axioms buildTree_bounded

/-- A view `ImageView.ofImage` builds holds only chunks below `2 ^ chunkBits`. -/
theorem ofImage_bounded {image : ImageBytes} {view : ImageView}
    (built : ImageView.ofImage image = .ok view) : view.Bounded := by
  unfold ImageView.ofImage at built
  split at built
  · rename_i wellFormed
    cases built
    simp only [ImageView.Bounded]
    split
    · rename_i tree treeEq
      have small : ∀ chunk ∈ image.chunks, chunk < 2 ^ chunkBits := by
        simp only [ImageBytes.wellFormed, Bool.and_eq_true, List.all_eq_true,
          decide_eq_true_eq] at wellFormed
        exact wellFormed.1.2
      have leaves : ∀ leaf ∈ image.chunks.map ChunkTree.leaf, leaf.Bounded := by
        simp only [List.mem_map]
        rintro _ ⟨chunk, member, rfl⟩
        exact small chunk member
      exact ChunkTree.at_lt (buildTree_bounded _ leaves treeEq)
    · trivial
  · cases built

#print axioms ofImage_bounded

end StrictBinding
