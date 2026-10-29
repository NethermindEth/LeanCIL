import CIL.Safety.FrameEquivalence

/-!
# Equivalent memories run instructions alike

The checked interpreter's memory and value instructions give related results from
`Memory.Equivalent` memories: the same fault, or equivalent memories with equal values.
A proof may therefore swap memory for an equivalent one before stepping an instruction.
-/

namespace CIL.Safety

theorem Memory.Equivalent.loadValue {m n : Memory} (same : m.Equivalent n)
    (reference : ManagedReference) (width : Nat) (signed : Bool) :
    loadValue m reference width signed = loadValue n reference width signed := by
  simp only [CIL.Safety.loadValue, same.dereference, same.loadSnapshot]

theorem Memory.Equivalent.storeValue {m n : Memory} (same : m.Equivalent n)
    (reference : ManagedReference) (value : CIL.Value) :
    ResultEquivalent Memory.Equivalent (storeValue m reference value)
      (storeValue n reference value) := by
  cases value <;> simp only [CIL.Safety.storeValue, Bind.bind, Except.bind]
  all_goals repeat first
    | exact .error _
    | (apply ResultEquivalent.bind_same
       intro address
       first
       | exact (same.write address _ ordinaryAccessAlignment).mapError _
       | exact (same.writeSnapshot address _ ordinaryAccessAlignment).mapError _)
    | split

/-- Pointer subtraction and observations depend only on allocation metadata. -/
theorem Memory.Equivalent.referencePositions {m n : Memory} (same : m.Equivalent n)
    (left right : ManagedReference) :
    referencePositions m left right = referencePositions n left right := by
  simp only [CIL.Safety.referencePositions, checkedAt, same.form]
#print axioms Memory.Equivalent.referencePositions

/-- Equivalent memories give the same native pointer difference. -/
theorem Memory.Equivalent.referenceDifference {m n : Memory} (same : m.Equivalent n)
    (left right : ManagedReference) :
    referenceDifference m left right = referenceDifference n left right := by
  simp only [CIL.Safety.referenceDifference, same.referencePositions]
#print axioms Memory.Equivalent.referenceDifference

/-- Typed transfer reads observe the same bytes in equivalent memories. -/
theorem Memory.Equivalent.loadTransfer {m n : Memory} (same : m.Equivalent n)
    (reference : ManagedReference) (kind : CIL.TransferKind) :
    loadTransfer m reference kind = loadTransfer n reference kind := by
  cases kind <;> simp only [CIL.Safety.loadTransfer, same.loadValue, same.loadSnapshot]
#print axioms Memory.Equivalent.loadTransfer

/-- Typed transfer writes preserve memory equivalence. -/
theorem Memory.Equivalent.storeTransfer {m n : Memory} (same : m.Equivalent n)
    (reference : ManagedReference) (kind : CIL.TransferKind) (value : CIL.Value) :
    ResultEquivalent Memory.Equivalent (storeTransfer m reference kind value)
      (storeTransfer n reference kind value) := by
  unfold CIL.Safety.storeTransfer
  repeat first
    | exact .error _
    | (apply ResultEquivalent.bind_same; intro)
    | exact (same.write _ _ _).mapError _
    | exact (same.writeSnapshot _ _ _).mapError _
    | split
#print axioms Memory.Equivalent.storeTransfer

theorem Memory.Equivalent.memoryInstruction {m n : Memory} (same : m.Equivalent n)
    (operation : CIL.MemoryOp) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (memoryInstruction operation stack m)
      (memoryInstruction operation stack n) := by
  unfold CIL.Safety.memoryInstruction
  split <;> try simp only [same.read, same.access, same.loadValue, same.formValue, same.add,
    same.referenceDifference, same.spanValidate, same.spanSlice, same.spanElement,
    same.arrayValidate, same.arrayElement, same.loadTransfer]
  all_goals repeat first
    | exact .error _
    | exact .ok ⟨same, rfl⟩
    | (apply ResultEquivalent.bind ((same.spanFill _ _).mapError _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | (apply ResultEquivalent.bind_same; intro)
    | (apply ResultEquivalent.bind ((same.write _ _ _).mapError _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | (apply ResultEquivalent.bind (same.storeValue _ _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | (apply ResultEquivalent.bind (same.storeTransfer _ _ _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | (apply ResultEquivalent.bind ((same.writeSnapshot _ _ _).mapError _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | split

theorem Memory.Equivalent.instruction {m n : Memory} (same : m.Equivalent n)
    (operation : CIL.Op) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (instruction operation stack m)
      (instruction operation stack n) := by
  unfold CIL.Safety.instruction
  split <;> try simp only [same.read, same.dereference, same.loadValue, same.loadSnapshot,
    same.formValue, same.add]
  all_goals repeat first
    | exact same.memoryInstruction _ _
    | exact .error _
    | exact .ok ⟨same, rfl⟩
    | (apply ResultEquivalent.bind_same; intro)
    | (apply ResultEquivalent.bind ((same.write _ _ _).mapError _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | (apply ResultEquivalent.bind (same.storeValue _ _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | (apply ResultEquivalent.bind ((same.writeSnapshot _ _ _).mapError _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | split

#print axioms Memory.Equivalent.instruction
#print axioms Memory.Equivalent.memoryInstruction
#print axioms Memory.Equivalent.loadValue
#print axioms Memory.Equivalent.storeValue

end CIL.Safety
