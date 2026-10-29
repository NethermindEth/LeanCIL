import Std

/-!
# Allocation-aware memory

The storage model of the checked interpreter (`CIL/Safety/Execution.lean`). Memory is a set
of allocations, each with a kind, a layout and a liveness flag, plus byte cells and the
views that grant read or write authority. A reference is an allocation identity and an
offset; it must first *form* (live allocation, in-bounds or sentinel offset) and then pass
an *access* check (bounds, alignment, authority, no GC slots) before bytes move. Every
failure is a `Fault`, never undefined behaviour.

This layer is independent of application types and of the extracted program. Its checked
operations are not yet a production certificate.
-/
namespace CIL.Safety

/-- The identity of an allocation; identities are never reused. -/
abbrev AllocationId := Nat

/-- Where an allocation lives; only an immutable static may never be written. -/
inductive StorageKind where
  | managedHeap | callerStack | frame (activation : Nat) | immutableStatic
  deriving DecidableEq, Repr

/-- The byte size, alignment and GC reference slots of an allocation. -/
structure Layout where
  size : Nat
  alignment : Nat
  /-- GC-sensitive fields can occur elsewhere in a larger containing object.
      Only accesses intersecting these byte intervals are unsupported. -/
  referenceSlots : List (Nat × Nat) := []
  deriving DecidableEq, Repr

/-- One allocation: its storage kind, layout, whether it is still live, and the end
    positions that may be formed as sentinels. -/
structure Allocation where
  kind : StorageKind
  layout : Layout
  live : Bool := true
  /-- Only specified field/array end positions may be used as sentinels. -/
  sentinels : List Nat := []
  deriving DecidableEq, Repr

/-- A byte position inside an allocation. -/
structure Reference where
  allocation : AllocationId
  offset : Nat
  deriving DecidableEq, Repr

/-- A managed reference: `null` or the address of a byte in an allocation. -/
inductive ManagedReference where
  | null | address (reference : Reference)
  deriving DecidableEq, Repr

/-- One byte of memory and whether it has been initialized. -/
structure Cell where
  bits : BitVec 8
  initialized : Bool
  deriving DecidableEq, Repr

/-- Read and/or write authority over `length` bytes of an allocation from `start`. -/
structure View where
  allocation : AllocationId
  start : Nat
  length : Nat
  readable : Bool
  writable : Bool
  deriving DecidableEq, Repr

/-- The whole checked heap: allocation table, byte cells, granted views, the next fresh
    identity, and the references bound to loaded static fields. -/
structure Memory where
  allocations : AllocationId → Option Allocation
  cells : AllocationId → Nat → Cell
  views : List View
  /-- Never decreases; allocation identities are not recycled when frames return. -/
  nextIdentity : Nat
  /-- Loaded assembly fields retain identity independently of their contents. -/
  staticBindings : List (Nat × Reference) := []
  /-- Admitted dynamic-stack bytes per activation; deployment must justify this quota.
      Zero is the default, so existing memory grants no dynamic stack storage. -/
  stackLimit : Nat := 0

/-- Why a memory operation was rejected. -/
inductive Fault where
  | nullDereference | missingAllocation | expiredLifetime | invalidReference
  | outsideAllocation | unreadable | unwritable | uninitialized
  | unsupportedLayout | alignment | identityReuse
  | malformedAllocation
  deriving DecidableEq, Repr

/-- A memory operation that either succeeds or reports a `Fault`. -/
abbrev Checked := Except Fault

/-- One past the largest native (64-bit) offset or size. -/
def nativeLimit : Nat := 2^64

/-- An allocation fits the native address space, has a positive alignment, and its
    sentinels and reference slots lie within its size. -/
def Allocation.WellFormed (a : Allocation) : Prop :=
  a.layout.size < nativeLimit ∧ 0 < a.layout.alignment ∧
    (∀ offset ∈ a.sentinels, offset ≤ a.layout.size) ∧
    ∀ slot ∈ a.layout.referenceSlots, slot.1 + slot.2 ≤ a.layout.size

/-- Decidable form of `Allocation.WellFormed`, checked by `allocate`. -/
def Allocation.valid (a : Allocation) : Bool :=
  decide (a.layout.size < nativeLimit) && decide (0 < a.layout.alignment) &&
    a.sentinels.all (fun offset => decide (offset ≤ a.layout.size)) &&
    a.layout.referenceSlots.all (fun slot => decide (slot.1 + slot.2 ≤ a.layout.size))

/-- Every allocation has an identity below `nextIdentity` and is well formed, and every
    view lies inside an existing allocation. -/
def Memory.WellFormed (m : Memory) : Prop :=
  (∀ id a, m.allocations id = some a → id < m.nextIdentity ∧ a.WellFormed) ∧
  ∀ view ∈ m.views, ∃ a, m.allocations view.allocation = some a ∧
    view.start + view.length ≤ a.layout.size

/-- The allocation `id`, failing if it is missing or has expired. -/
def liveAllocation (m : Memory) (id : AllocationId) : Checked Allocation := do
  let some a := m.allocations id | .error .missingAllocation
  if a.live then return a else .error .expiredLifetime

/-- An offset may be formed if it is strictly inside the allocation, or is a declared
    sentinel at most its size. -/
def validPosition (a : Allocation) (offset : Nat) : Bool :=
  decide (offset < nativeLimit) &&
    (decide (offset < a.layout.size) ||
      (decide (offset ≤ a.layout.size) && a.sentinels.contains offset))

/-- Formation checks do not require access permission or initialized bytes. -/
def form (m : Memory) (r : Reference) : Checked Reference := do
  let a ← liveAllocation m r.allocation
  if validPosition a r.offset then return r else .error .invalidReference

/-- `null` or an address that forms. -/
def validManagedReference (m : Memory) : ManagedReference → Bool
  | .null => true
  | .address r => match form m r with | .ok _ => true | .error _ => false

/-- Offset multiplication and addition wrap at native width. A wrapped result
    retains its allocation identity and must pass formation validity anew. -/
def add (m : Memory) (r : Reference) (elementSize : Nat) (offset : BitVec 64) :
    Checked Reference := do
  let _ ← form m r
  form m { r with offset :=
    (BitVec.ofNat 64 r.offset + BitVec.ofNat 64 elementSize * offset).toNat }

/-- The byte at `r` lies inside `view`. -/
def viewContains (view : View) (r : Reference) : Bool :=
  decide (view.allocation = r.allocation ∧ view.start ≤ r.offset ∧
    r.offset < view.start + view.length)

/-- Some view covering the byte at `r` grants the requested read or write authority. -/
def permitted (m : Memory) (write : Bool) (r : Reference) : Bool :=
  m.views.any fun view => viewContains view r && (if write then view.writable else view.readable)

/-- Access bounds and API authority are distinct from formation validity. The
    required alignment is supplied by the particular instruction, not its width. -/
def access (m : Memory) (r : Reference) (width alignment : Nat) (write : Bool) :
    Checked Unit := do
  let _ ← form m r
  let a ← liveAllocation m r.allocation
  if a.layout.referenceSlots.any (fun slot =>
      decide (r.offset < slot.1 + slot.2 ∧ slot.1 < r.offset + width))
    then .error .unsupportedLayout else pure ()
  if r.offset + width ≤ a.layout.size then pure () else .error .outsideAllocation
  if alignment > 0 && a.layout.alignment % alignment == 0 && r.offset % alignment == 0
    then pure () else .error .alignment
  if write && a.kind == .immutableStatic then .error .unwritable else pure ()
  if (List.range width).all (fun i => permitted m write { r with offset := r.offset + i })
    then pure () else .error (if write then .unwritable else .unreadable)

/-- Reads `width` bytes at `r`; every byte must be readable and initialized. -/
def read (m : Memory) (r : Reference) (width alignment : Nat) : Checked (List (BitVec 8)) := do
  access m r width alignment false
  let cells := (List.range width).map fun i => m.cells r.allocation (r.offset + i)
  if cells.all (·.initialized) then return cells.map (·.bits) else .error .uninitialized

/-- Reads through a managed reference; `null` faults with `nullDereference`. -/
def dereference (m : Memory) (reference : ManagedReference) (width alignment : Nat) :
    Checked (List (BitVec 8)) :=
  match reference with
  | .null => .error .nullDereference
  | .address r => read m r width alignment

/-- A covering readable view is the common fast path; fragmented authority may
    also cover every byte. Empty writes need no additional authority. -/
def readableRange (m : Memory) (r : Reference) (width : Nat) : Bool :=
  width == 0 ||
    m.views.any (fun view => view.readable && decide
      (view.allocation = r.allocation ∧ view.start ≤ r.offset ∧
        r.offset + width ≤ view.start + view.length)) ||
    (List.range width).all (fun i => permitted m false { r with offset := r.offset + i })

/-- The views after writing `width` bytes at `r`: a read-only view of the written bytes
    is added unless they are already readable. -/
def writeViews (m : Memory) (r : Reference) (width : Nat) : List View :=
  if readableRange m r width then m.views
  else ⟨r.allocation, r.offset, width, true, false⟩ :: m.views

/-- Reference implementation retained to state and prove optimization equivalence. -/
def writeAlwaysPrepend (m : Memory) (r : Reference) (bytes : List (BitVec 8)) (alignment : Nat) :
    Checked Memory := do
  access m r bytes.length alignment true
  -- A method may read its own initialized output. This grants no write authority
  -- and exposes exactly the interval whose original write authority was checked.
  return { m with
    views := ⟨r.allocation, r.offset, bytes.length, true, false⟩ :: m.views
    cells := (fun id offset =>
    if id = r.allocation ∧ r.offset ≤ offset then
      (match bytes[offset - r.offset]? with
      | some bits => { bits, initialized := true }
      | none => m.cells id offset)
    else m.cells id offset) }

/-- Writes `bytes` at `r` after a write access check, marking them initialized and
    making them readable. -/
def write (m : Memory) (r : Reference) (bytes : List (BitVec 8)) (alignment : Nat) :
    Checked Memory := do
  access m r bytes.length alignment true
  -- A method may read its own initialized output. This grants no write authority
  -- and exposes exactly the interval whose original write authority was checked.
  return { m with
    views := writeViews m r bytes.length
    cells := (fun id offset =>
    if id = r.allocation ∧ r.offset ≤ offset then
      (match bytes[offset - r.offset]? with
      | some bits => { bits, initialized := true }
      | none => m.cells id offset)
    else m.cells id offset) }

/-- A checked byte write with constant-time lookup in its retained snapshot. -/
def writeIndexed (memory : Memory) (reference : Reference) (bytes : List (BitVec 8))
    (alignment : Nat) : Checked Memory := do
  access memory reference bytes.length alignment true
  let snapshot := bytes.toArray
  return { memory with
    views := writeViews memory reference bytes.length
    cells := fun id offset =>
      if id = reference.allocation ∧ reference.offset ≤ offset then
        match snapshot[offset - reference.offset]? with
        | some bits => { bits, initialized := true }
        | none => memory.cells id offset
      else memory.cells id offset }

/-- Indexed snapshots retain exactly the checked write semantics. -/
theorem writeIndexed_eq (memory : Memory) (reference : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat) :
    writeIndexed memory reference bytes alignment = write memory reference bytes alignment := by
  simp only [writeIndexed, write, List.getElem?_toArray]
#print axioms writeIndexed_eq

/-- A snapshot is obtained before any destination change, preserving overlap. -/
def copy (m : Memory) (source target : Reference) (width : Nat) : Checked Memory := do
  let bytes ← read m source width 1
  write m target bytes 1

/-- SkipInit does not initialize or erase anything. -/
def skipInit (m : Memory) (r : Reference) : Checked Memory := do
  let _ ← form m r
  return m

/-- Marks allocation `id` as no longer live; its identity stays taken. -/
def expire (m : Memory) (id : AllocationId) : Memory :=
  { m with allocations := fun other =>
      if other = id then (m.allocations other).map fun a => { a with live := false }
      else m.allocations other }

/-- Fresh activation storage has unknown bytes, even if a physical stack slot
    held initialized data in an earlier activation. -/
def allocate (m : Memory) (a : Allocation) : Checked (AllocationId × Memory) :=
  if !a.valid then .error .malformedAllocation else
  if (m.allocations m.nextIdentity).isSome then .error .identityReuse else
    .ok (m.nextIdentity, { m with
      allocations := fun id => if id = m.nextIdentity then some a else m.allocations id
      cells := fun id offset => if id = m.nextIdentity then { bits := 0, initialized := false }
        else m.cells id offset
      nextIdentity := m.nextIdentity + 1 })

end CIL.Safety
