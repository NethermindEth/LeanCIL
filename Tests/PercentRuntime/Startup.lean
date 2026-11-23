import CIL.Safety.Execution
import CIL.Safety.HeapObjects

/-! Loading interned strings before entering a method on the modeled 64-bit profile. -/
namespace Tests.PercentRuntime.Startup
open CIL.Extraction CIL.Safety

private def stringType : RuntimeType := ⟨.object coreLibraryScope "System.String", []⟩

/-- Model slots store the UTF-16 length and payload of a loader-owned string. -/
def bytesOfString (text : String) : List (BitVec 8) :=
  let units := CIL.utf16Units text
  numberBytes units.length 4 ++ [0,0,0,0] ++
    units.flatMap (fun unit => numberBytes unit 2) ++ [0,0]

/-- A loader-owned string allocation aligned for object access. -/
def storage (bytes : List (BitVec 8)) : Allocation :=
  ⟨.object stringType, ⟨bytes.length, objectAlignment, []⟩, true, []⟩

/-- The modeled length field, padding and null terminator take ten bytes in addition to
    the two bytes for each UTF-16 code unit. -/
theorem storageSize (text : String) :
    (bytesOfString text).length = 10 + 2 * (CIL.utf16Units text).length := by
  have payload (units : List Nat) :
      (units.flatMap fun unit => numberBytes unit 2).length = 2 * units.length := by
    induction units with
    | nil => rfl
    | cons _ rest ih => simp [List.flatMap_cons, numberBytes] at ih ⊢; omega
  unfold bytesOfString
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [payload]
  simp only [numberBytes, List.length_map, List.length_range]
  omega
#print axioms storageSize

/-- Fill the new loader allocation and grant a read-only view of its bytes. -/
def loaded (memory : Memory) (identity : Nat) (text : String)
    (bytes : List (BitVec 8)) : Memory :=
  { memory with
    cells := fun id offset => if id == identity then
      match bytes[offset]? with
      | some byte => ⟨byte, true⟩
      | none => ⟨0, false⟩
      else memory.cells id offset
    views := ⟨identity, 0, bytes.length, true, false⟩ :: memory.views
    literals := (text, ⟨identity, 0⟩) :: memory.literals }

/-- Intern one loader entry. A repeated text reuses the original allocation. -/
def intern (memory : Memory) (text : String) : Checked (Reference × Memory) := do
  if let some reference := memory.literals.lookup text then return (reference, memory)
  let units := CIL.utf16Units text
  if units.length > 0x7fffffff then throw .malformedAllocation
  let bytes := bytesOfString text
  let (identity, allocated) ← allocate memory (storage bytes)
  return (⟨identity, 0⟩, loaded allocated identity text bytes)

/-- Interning the same entry retains its reference and all memory. -/
theorem existing (memory : Memory) (text : String) (reference : Reference)
    (bound : memory.literals.lookup text = some reference) :
    intern memory text = .ok (reference, memory) := by simp [intern, bound, pure, Except.pure]
#print axioms existing

/-- A representable byte extent satisfies the allocator’s bounds. -/
theorem validStorage (text : String) (fits : (bytesOfString text).length < nativeLimit) :
    (storage (bytesOfString text)).valid = true := by
  simp [storage, Allocation.valid, fits, objectAlignment]

#print axioms validStorage

/-- The loader accepts every representable string from empty caller memory, and the original
    ldstr loads a non-null reference without changing the initialized state. -/
theorem fromEmpty (text : String) (stack : List Value)
    (lengthFits : (CIL.utf16Units text).length ≤ 0x7fffffff) :
    ∃ memory, intern Memory.empty text = .ok (⟨0,0⟩, memory) ∧
      intern memory text = .ok (⟨0,0⟩, memory) ∧ memory.nextIdentity = 1 ∧
      memory.heapBudget = 0 ∧
      stringLiteralInstruction text stack memory =
        .ok (memory, .object (.address ⟨0,0⟩) :: stack) := by
  have fits : (bytesOfString text).length < nativeLimit := by
    rw [storageSize]; unfold nativeLimit; omega
  have valid := validStorage text fits
  simp only [intern, Memory.empty, List.lookup_nil, Nat.not_lt.mpr lengthFits, ↓reduceIte,
    allocate, valid, Bool.not_true, Bool.false_eq_true, Option.isSome_none, bind, Except.bind,
    pure, Except.pure]
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · simp [loaded]
  · simp [stringLiteralInstruction, literalObject, loaded, formObject, liveAllocation, storage,
      checkedAt, Except.mapError, bind, Except.bind, pure, Except.pure]
#print axioms fromEmpty

/-- Loading both constructor literals from empty caller memory aliases equal texts and gives
    distinct texts separate live references. Neither operation consumes the method's heap quota. -/
theorem constructorLiterals (name message : String)
    (nameFits : (CIL.utf16Units name).length ≤ 0x7fffffff)
    (messageFits : (CIL.utf16Units message).length ≤ 0x7fffffff) :
    ∃ first final, intern Memory.empty name = .ok (⟨0, 0⟩, first) ∧
      intern first message = .ok (⟨if name = message then 0 else 1, 0⟩, final) ∧
      final.heapBudget = 0 ∧
      stringLiteralInstruction name [] final = .ok (final, [.object (.address ⟨0,0⟩)]) ∧
      stringLiteralInstruction message [] final =
        .ok (final, [.object (.address ⟨if name = message then 0 else 1, 0⟩)]) := by
  by_cases same : name = message
  · subst message
    obtain ⟨first, installed, reused, _, budget, loaded⟩ := fromEmpty name [] nameFits
    exact ⟨first, first, installed, by simpa using reused, budget, loaded, by simpa using loaded⟩
  · have valid (text : String) (lengthFits : (CIL.utf16Units text).length ≤ 0x7fffffff) :
        (storage (bytesOfString text)).valid = true := by
      apply validStorage
      rw [storageSize]; unfold nativeLimit; omega
    have unequal := Ne.symm same
    have different : (message == name) = false := by simpa using unequal
    have reverse : (name == message) = false := by simpa using same
    obtain ⟨first, installed, _, _, _, _⟩ := fromEmpty name [] nameFits
    refine ⟨first, ?_⟩
    simp only [installed, true_and]
    simp only [intern, Memory.empty, List.lookup_nil, Nat.not_lt.mpr nameFits, ↓reduceIte,
      allocate, valid name nameFits, Bool.not_true, Bool.false_eq_true, Option.isSome_none,
      bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, true_and] at installed
    subst first
    simp [-List.length_flatMap, intern, loaded, List.lookup, different, same,
      Nat.not_lt.mpr messageFits, allocate,
      valid message messageFits, bind, Except.bind, pure, Except.pure]
    simp [stringLiteralInstruction, literalObject, List.lookup, formObject, liveAllocation,
      storage, checkedAt, Except.mapError, reverse, bind, Except.bind, pure, Except.pure]
#print axioms constructorLiterals
end Tests.PercentRuntime.Startup
