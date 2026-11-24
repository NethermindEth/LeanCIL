import CIL.Extraction.Generics
import CIL.Safety.InstructionMemory
import CIL.Safety.HeapObjects

/-! Entry memory for decoded programs on the modeled 64-bit profile. Literal objects belong to
    the loaded image. A deployment can bound allocations made during execution. -/
namespace CIL.Safety.LiteralImage
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


/-- Original string loads of byte-checked methods, in method and instruction order.
Read the original instructions so a checked semantic summary cannot hide a literal operand. -/
def operands (methods : List RawMethod) : List String :=
  methods.flatMap fun method => method.code.filterMap fun site =>
    match site.opcode, site.operand with
    | 0x72, .text text => some text
    | _, _ => none

/-- Load the program's literals before entry. A repeated operand keeps its object identity.
Ordinary execution assumes global heap availability. An explicit budget applies after loading. -/
def initialMemory (methods : List RawMethod) (heapBytes : Option Nat := none) : Checked Memory := do
  let memory ← (operands methods).foldlM
    (fun memory text => Prod.snd <$> intern memory text) Memory.empty
  return { memory with heapBudget := heapBytes }

/-- Code without literal operands enters with no loader allocations. -/
theorem withoutLiterals (methods : List RawMethod) (heapBytes : Option Nat) (none : operands methods = []) :
    initialMemory methods heapBytes = .ok { Memory.empty with heapBudget := heapBytes } := by
  rw [initialMemory, none]
  rfl
#print axioms withoutLiterals

end CIL.Safety.LiteralImage
