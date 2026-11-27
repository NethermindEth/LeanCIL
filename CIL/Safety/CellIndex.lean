/-!
# Indexed memory cells

Checked writes retain the bytes of a native address range. Kernel reduction shares its byte
ranges across lookups, and compiled execution indexes the stored array directly.
-/

namespace CIL.Safety

/-- One past the largest native (64-bit) offset or size. -/
def nativeLimit : Nat := 2^64

/-- The cells following a short snapshot prefix, indexed from its first byte. -/
private def suffixCell {cell : Type} : List cell -> Nat -> Option cell
  | [] => fun _ => none
  | value :: bytes =>
    let tail := suffixCell bytes
    fun index => match index with
      | 0 => some value
      | next + 1 => tail next

/-- Reading a suffix at any index agrees with list lookup, including past the end. -/
private theorem suffixCell_eq {cell : Type} (bytes : List cell) (index : Nat) :
    suffixCell bytes index = bytes[index]? := by
  induction bytes generalizing index with
  | nil => cases index <;> rfl
  | cons head tail ih => cases index with
    | zero => rfl
    | succ next => exact ih next
#print axioms suffixCell_eq

/-- A decision tree indexes byte ranges. Each right branch shares the remaining list. -/
private def rangeCell {cell : Type} : Nat -> Nat -> List cell -> Nat -> Option cell
  | 0, _, bytes => fun index => bytes[index]?
  | height + 1, stride, bytes =>
    let left := rangeCell height (stride / 2) bytes
    let right := rangeCell height (stride / 2) (bytes.drop stride)
    fun index => if index < stride then left index else right (index - stride)

/-- Splitting a range preserves the cell at every index for every split size. -/
private theorem rangeCell_eq {cell : Type} (height stride : Nat) (bytes : List cell)
    (index : Nat) : rangeCell height stride bytes index = bytes[index]? := by
  induction height generalizing stride bytes index with
  | zero => rfl
  | succ height ih =>
    simp only [rangeCell]
    split
    next => apply ih
    next outside =>
      rw [ih, List.getElem?_drop]
      congr 1
      omega
#print axioms rangeCell_eq

/-- Four low offset bits select one of sixteen cells at a leaf. -/
private def leafBits := 4

/-- Consecutive ranges double in width. The tail preserves lookup beyond the last range. -/
private def indexedRanges {cell : Type} : Nat -> Nat -> Nat -> List cell -> Nat -> Option cell
  | 0, _, _, bytes => fun index => bytes[index]?
  | remaining + 1, height, width, bytes =>
    if bytes.isEmpty then fun _ => none else
    let here := rangeCell height (width / 2) bytes
    let later := indexedRanges remaining (height + 1) (width * 2) (bytes.drop width)
    fun index => if index < width then here index else later (index - width)

/-- Reading successive ranges agrees with list lookup for any choice of range widths. -/
private theorem indexedRanges_eq {cell : Type} (remaining height width : Nat) (bytes : List cell)
    (index : Nat) : indexedRanges remaining height width bytes index = bytes[index]? := by
  induction remaining generalizing height width bytes index with
  | zero => rfl
  | succ remaining ih =>
    cases bytes with
    | nil => rfl
    | cons first tail =>
      simp only [indexedRanges, List.isEmpty_cons, Bool.false_eq_true, ite_false]
      split
      next => apply rangeCell_eq
      next outside =>
        rw [ih, List.getElem?_drop]
        congr 1
        omega
#print axioms indexedRanges_eq

/-- The ranges cover every native offset, with at most sixteen byte probes in its leaf. -/
def snapshotCellAt {cell : Type} (indexed : Array cell) : Nat -> Option cell :=
  let width := 2 ^ leafBits
  let first := suffixCell indexed.toList
  let later := indexedRanges (nativeLimit.log2 - leafBits) 1 (2 * width)
    (indexed.toList.drop width)
  fun index => if index < width then first index else later (index - width)

/-- The snapshot index agrees with list lookup, including for offsets past the end. -/
theorem snapshotCellAt_eq {cell : Type} (bytes : List cell) (index : Nat) :
    snapshotCellAt bytes.toArray index = bytes[index]? := by
  unfold snapshotCellAt
  split
  next => apply suffixCell_eq
  next outside =>
    rw [indexedRanges_eq, List.getElem?_drop]
    congr 1
    omega
#print axioms snapshotCellAt_eq

/-- Compiled reads index an array captured at write time. -/
@[inline] private def arrayCellAt {cell : Type} (indexed : Array cell) (index : Nat) :
    Option cell :=
  indexed[index]?

/-- The compiler can use direct array reads for every snapshot and offset. -/
@[csimp] private theorem snapshotCellAt_eq_array : @snapshotCellAt = @arrayCellAt := by
  funext cell indexed index
  cases indexed with
  | mk bytes => simp only [snapshotCellAt_eq, arrayCellAt, List.getElem?_toArray]
#print axioms snapshotCellAt_eq_array

end CIL.Safety
