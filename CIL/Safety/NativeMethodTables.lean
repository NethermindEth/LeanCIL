import CIL.Safety.Memory
import CIL.MethodPointers

/-!
# Authenticated native handler-table storage

A supplied immutable native table binds opaque managed identities to checked backing storage.
Offsets retain the allocation and the table origin; loads check bounds, initialization and
authority before returning an identity. Byte values never become callable identities.
-/

namespace CIL.Safety

/-- A supplied immutable table and a cursor into its backing allocation. Its identities are
    authenticated input, independently of the numeric bytes used by the runtime for addresses. -/
structure NativeMethodTable where
  signature : CIL.ManagedSignature
  targets : Array CIL.ManagedIdentity
  origin : Reference
  cursor : Reference
  deriving DecidableEq, Repr

/-- Every admitted runtime profile uses eight-byte native method addresses. -/
def nativeMethodWidth : Nat := 8

/-- The origin names immutable storage large enough for all entries. The cursor may be one
    past the table, but cannot change allocation identity or move before its origin. -/
def NativeMethodTable.check (table : NativeMethodTable) (memory : Memory) : Checked Unit := do
  let allocation ← liveAllocation memory table.origin.allocation
  if allocation.kind != .immutableStatic then .error .unsupportedLayout else pure ()
  if table.targets.size >= 2^31 ||
      table.origin.offset + nativeMethodWidth * table.targets.size > allocation.layout.size then
    .error .outsideAllocation else pure ()
  if allocation.layout.alignment % nativeMethodWidth != 0 ||
      table.origin.offset % nativeMethodWidth != 0 then .error .alignment else pure ()
  if table.cursor.allocation != table.origin.allocation ||
      table.cursor.offset < table.origin.offset ||
      table.cursor.offset > table.origin.offset + nativeMethodWidth * table.targets.size then
    .error .invalidReference else pure ()

/-- Native byte addition preserves the supplied table and checks the resulting cursor;
    one-past cursors may be formed but cannot be loaded. -/
def NativeMethodTable.addBytes (table : NativeMethodTable) (memory : Memory)
    (offset : BitVec 64) : Checked NativeMethodTable := do
  table.check memory
  let cursor := { table.cursor with offset :=
    (BitVec.ofNat 64 table.cursor.offset + offset).toNat }
  let result := { table with cursor }
  result.check memory
  return result

/-- A native load checks the backing bytes but returns the supplied opaque identity;
    no bit pattern, including a program index, can manufacture a callable target. -/
def NativeMethodTable.load (table : NativeMethodTable) (memory : Memory) :
    Checked CIL.MethodPointer := do
  table.check memory
  let relative := table.cursor.offset - table.origin.offset
  if relative % nativeMethodWidth != 0 then .error .alignment else pure ()
  let index := relative / nativeMethodWidth
  let some identity := table.targets[index]? | .error .outsideAllocation
  let _ ← read memory table.cursor nativeMethodWidth nativeMethodWidth
  return ⟨table.signature, some identity⟩

/-- Moving the cursor never changes the admitted target identities or their signature. -/
theorem NativeMethodTable.addBytes_provenance (table result : NativeMethodTable)
    (memory : Memory) (offset : BitVec 64)
    (added : table.addBytes memory offset = .ok result) :
    result.targets = table.targets ∧ result.signature = table.signature ∧
      result.origin = table.origin := by
  unfold NativeMethodTable.addBytes at added
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at added
  split at added <;> simp_all
  split at added <;> simp_all
  subst result
  exact ⟨rfl, rfl, rfl⟩

#print axioms NativeMethodTable.addBytes_provenance

/-- Every loaded pointer retains the table's exact signature and an authenticated entry. -/
theorem NativeMethodTable.load_provenance (table : NativeMethodTable) (memory : Memory)
    (pointer : CIL.MethodPointer) (loaded : table.load memory = .ok pointer) :
    pointer.signature = table.signature ∧
      ∃ identity, pointer.target = some identity ∧ identity ∈ table.targets := by
  unfold NativeMethodTable.load at loaded
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at loaded
  split at loaded <;> (try simp_all)
  split at loaded <;> (try simp_all)
  split at loaded <;> (try simp_all)
  split at loaded <;> (try simp_all)
  subst pointer
  refine ⟨rfl, ⟨_, rfl, ?_⟩⟩
  exact Array.mem_of_getElem? (by assumption)

#print axioms NativeMethodTable.load_provenance

/-- Resolve an authenticated table's stable storage binding to the current allocation.
    Bindings are transported by the existing memory renaming relation. -/
def nativeTableView (table : CIL.MethodTable) (memory : Memory) :
    Checked NativeMethodTable := do
  let some targets := table.targets | .error .nullDereference
  let some backing := table.backing | .error .invalidReference
  let some (_, origin) := memory.staticBindings.find? (·.1 == backing.identity) |
    .error .missingAllocation
  let view : NativeMethodTable := ⟨table.signature, targets, origin,
    { origin with offset := origin.offset + backing.byteOffset }⟩
  view.check memory
  return view

/-- Move an opaque native table cursor without changing its identities or storage binding. -/
def addNativeTable (table : CIL.MethodTable) (memory : Memory) (offset : BitVec 64) :
    Checked CIL.MethodTable := do
  let view ← nativeTableView table memory
  let moved ← view.addBytes memory offset
  let some backing := table.backing | .error .invalidReference
  return { table with backing := some { backing with
    byteOffset := moved.cursor.offset - moved.origin.offset } }

/-- Load an authenticated native entry through the current storage binding. -/
def loadNativeTable (table : CIL.MethodTable) (memory : Memory) : Checked CIL.MethodPointer := do
  let view ← nativeTableView table memory
  view.load memory

end CIL.Safety
