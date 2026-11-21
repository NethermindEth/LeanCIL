import CIL.Safety.MemoryLemmas
import CIL.Types
import CIL.Safety.MemoryBelow
import CIL.Safety.MemoryEquivalence

/-!
# Snapshot reads and writes

Value copies move bytes together with their initialization flags, so copying uninitialized
memory never makes it initialized. This file defines `readSnapshot` and `writeSnapshot` and
proves they keep memory well formed, only extend allocations, leave older memory alone, and
respect memory equivalence.
-/

namespace CIL.Safety

/-- A value copy checks authority and lifetime but does not inspect initialization. -/
def readSnapshot (m : Memory) (r : Reference) (width alignment : Nat) :
    Checked (List (BitVec 8 × Bool)) := do
  access m r width alignment false
  return (List.range width).map fun i =>
    let cell := m.cells r.allocation (r.offset + i)
    (cell.bits, cell.initialized)

theorem readSnapshot_length {m : Memory} {r : Reference} {width alignment : Nat}
    {bytes : List (BitVec 8 × Bool)} (h : readSnapshot m r width alignment = .ok bytes) :
    bytes.length = width := by
  unfold readSnapshot at h
  cases ha : access m r width alignment false <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    simp

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
private def arrayCellAt {cell : Type} (indexed : Array cell) (index : Nat) : Option cell :=
  indexed[index]?

/-- The compiler can use direct array reads for every snapshot and offset. -/
@[csimp] private theorem snapshotCellAt_eq_array : @snapshotCellAt = @arrayCellAt := by
  funext cell indexed index
  cases indexed with
  | mk bytes => simp only [snapshotCellAt_eq, arrayCellAt, List.getElem?_toArray]
#print axioms snapshotCellAt_eq_array

/-- Copy bits and initialization flags together. Uninitialized input never becomes
    initialized just because it was assigned to another value or local. -/
def writeSnapshot (m : Memory) (r : Reference) (bytes : List (BitVec 8 × Bool))
    (alignment : Nat) : Checked Memory := do
  let written ← write m r (bytes.map Prod.fst) alignment
  let indexed := bytes.toArray
  return { written with cells := (fun id offset =>
    if id = r.allocation ∧ r.offset ≤ offset then
      match snapshotCellAt indexed (offset - r.offset) with
      | some cell => ⟨cell.1, cell.2⟩
      | none => m.cells id offset
    else m.cells id offset) }

/-- A successful store overlays exactly the supplied cells and preserves every other cell. -/
theorem writeSnapshot_cells_eq {m result : Memory} {r : Reference}
    {bytes : List (Prod (BitVec 8) Bool)} {alignment : Nat}
    (stored : writeSnapshot m r bytes alignment = .ok result) :
    result.cells = fun id offset =>
      if (And (id = r.allocation) (r.offset <= offset)) then
        match bytes[offset - r.offset]? with
        | some cell => .mk cell.1 cell.2
        | none => m.cells id offset
      else m.cells id offset := by
  unfold writeSnapshot at stored
  cases written : write m r (bytes.map Prod.fst) alignment <;>
    simp only [written, Bind.bind, Except.bind, Pure.pure, Except.pure] at stored
  next => cases stored
  next =>
    cases stored
    simp only [snapshotCellAt_eq]
#print axioms writeSnapshot_cells_eq

theorem writeSnapshot_preserves_wellFormed (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8 × Bool)) (alignment : Nat) (hm : m.WellFormed)
    (h : writeSnapshot m r bytes alignment = .ok result) : result.WellFormed := by
  unfold writeSnapshot at h
  cases hw : write m r (bytes.map Prod.fst) alignment <;>
    simp only [hw, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    have preserved := write_preserves_wellFormed _ _ _ _ _ hm hw
    exact {
      allocations := preserved.allocations
      views := preserved.views
      slots := preserved.slots }

theorem writeSnapshot_extends_allocations (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8 × Bool)) (alignment : Nat)
    (h : writeSnapshot m r bytes alignment = .ok result) : AllocationExtension m result := by
  unfold writeSnapshot at h
  cases hw : write m r (bytes.map Prod.fst) alignment <;>
    simp only [hw, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    have preserved := write_extends_allocations _ _ _ _ _ hw
    exact ⟨preserved.next, preserved.lookup⟩

/-- A snapshot write into an allocation at or above `watermark` leaves memory below it
    unchanged. -/
theorem writeSnapshot_preserves_memory_below (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8 × Bool)) (alignment watermark : Nat)
    (fresh : watermark ≤ r.allocation)
    (h : writeSnapshot m r bytes alignment = .ok result) : MemoryBelow watermark m result := by
  unfold writeSnapshot at h
  cases hw : write m r (bytes.map Prod.fst) alignment <;>
    simp only [hw, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    have preserved := write_preserves_memory_below _ _ _ _ _ _ fresh hw
    refine ⟨preserved.allocations, ?_, preserved.permissions, preserved.slots⟩
    intro id old offset
    have different : id ≠ r.allocation := by omega
    simp [different]

theorem Memory.Equivalent.readSnapshot {m n : Memory} (same : m.Equivalent n)
    (r : Reference) (width alignment : Nat) :
    readSnapshot m r width alignment = readSnapshot n r width alignment := by
  simp only [CIL.Safety.readSnapshot, same.access, same.cells]

theorem Memory.Equivalent.writeSnapshot {m n : Memory} (same : m.Equivalent n)
    (r : Reference) (bytes : List (BitVec 8 × Bool)) (alignment : Nat) :
    ResultEquivalent Memory.Equivalent (writeSnapshot m r bytes alignment)
      (writeSnapshot n r bytes alignment) := by
  unfold CIL.Safety.writeSnapshot
  apply ResultEquivalent.bind (same.write r _ alignment)
  intro left right related
  apply ResultEquivalent.ok
  exact ⟨related.allocations, by simp only [same.cells], related.permissions,
    related.nextIdentity, related.staticBindings, related.stackLimit, related.heapBudget,
    related.slots, related.literals⟩

end CIL.Safety
