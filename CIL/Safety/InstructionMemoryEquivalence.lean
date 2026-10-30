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

/-- Overlapping span copies preserve equivalent memories and the exact success flag. -/
theorem Memory.Equivalent.spanCopyInstruction {m n : Memory} (same : m.Equivalent n)
    (width : Nat) (tryCopy : Bool) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (spanCopyInstruction width tryCopy stack m)
      (spanCopyInstruction width tryCopy stack n) := by
  unfold CIL.Safety.spanCopyInstruction
  simp only [writeIndexed_eq, same.spanValidate, same.read]
  repeat first
    | exact .error _
    | exact .ok ⟨same, rfl⟩
    | (apply ResultEquivalent.bind ((same.write _ _ _).mapError _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | (apply ResultEquivalent.bind_same; intro)
    | split
#print axioms Memory.Equivalent.spanCopyInstruction

/-- Repeated snapshot writes preserve byte values and masks on equivalent memories. -/
theorem Memory.Equivalent.spanFillSnapshot {m n : Memory} (same : m.Equivalent n)
    (view : SpanView) (element : List (BitVec 8 × Bool)) :
    ResultEquivalent Memory.Equivalent (view.fillSnapshot m element)
      (view.fillSnapshot n element) := by
  unfold SpanView.fillSnapshot SpanView.fillWith
  rw [same.spanValidate]
  repeat first
    | exact .error _
    | exact .ok same
    | exact same.writeSnapshot _ _ _
    | (apply ResultEquivalent.bind_same; intro)
    | split
#print axioms Memory.Equivalent.spanFillSnapshot

/-- Fill and clear preserve equivalent backing memories and identical retained values. -/
theorem Memory.Equivalent.spanFillInstruction {m n : Memory} (same : m.Equivalent n)
    (width : Nat) (clear : Bool) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (spanFillInstruction width clear stack m)
      (spanFillInstruction width clear stack n) := by
  unfold CIL.Safety.spanFillInstruction
  repeat first
    | (apply ResultEquivalent.bind ((same.spanFillSnapshot _ _).mapError _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | exact .error _
    | (apply ResultEquivalent.bind ((same.spanFill _ _).mapError _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | (apply ResultEquivalent.bind_same; intro)
    | split
#print axioms Memory.Equivalent.spanFillInstruction

/-- Typed array fill uses the same checked span write in equivalent memories. -/
theorem Memory.Equivalent.arrayFillInstruction {m n : Memory} (same : m.Equivalent n)
    (element : CIL.ArrayElement) (counted : Bool) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (arrayFillInstruction element counted stack m)
      (arrayFillInstruction element counted stack n) := by
  unfold CIL.Safety.arrayFillInstruction
  simp only [same.spanSlice, same.arrayValidate]
  repeat first
    | exact same.spanFillInstruction _ _ _
    | exact .error _
    | (apply ResultEquivalent.bind_same; intro)
    | split
#print axioms Memory.Equivalent.arrayFillInstruction

/-- Checked reference addition observes equivalent allocation states and returns the same address. -/
theorem Memory.Equivalent.referenceAddInstruction {m n : Memory} (same : m.Equivalent n)
    (size : Nat) (signed : Bool) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (referenceAddInstruction size signed stack m)
      (referenceAddInstruction size signed stack n) := by
  unfold CIL.Safety.referenceAddInstruction
  split <;> try simp only [same.add]
  all_goals repeat first
    | exact .error _
    | exact .ok ⟨same, rfl⟩
    | (apply ResultEquivalent.bind_same; intro)
    | split
#print axioms Memory.Equivalent.referenceAddInstruction

/-- Non-fill memory operations preserve equivalent memories and identical values. -/
private theorem Memory.Equivalent.otherMemoryInstruction {m n : Memory} (same : m.Equivalent n)
    (operation : CIL.MemoryOp) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (otherMemoryInstruction operation stack m)
      (otherMemoryInstruction operation stack n) := by
  unfold CIL.Safety.otherMemoryInstruction
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

#print axioms Memory.Equivalent.otherMemoryInstruction

/-- Observations depend only on allocation metadata and preserve equivalent memories. -/
theorem Memory.Equivalent.viewObservationInstruction {m n : Memory} (same : m.Equivalent n)
    (observation : CIL.ViewObservation) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (viewObservationInstruction observation stack m)
      (viewObservationInstruction observation stack n) := by
  unfold CIL.Safety.viewObservationInstruction
  split <;> try simp only [same.spanValidate, same.arrayValidate, same.formValue]
  all_goals repeat first
    | exact .error _
    | exact .ok ⟨same, rfl⟩
    | (apply ResultEquivalent.bind_same; intro)
    | split
#print axioms Memory.Equivalent.viewObservationInstruction

/-- Endian transfers retain their exact results over equivalent backing memories. -/
theorem Memory.Equivalent.binaryTransferInstruction {m n : Memory} (same : m.Equivalent n)
    (width : Nat) (signed bigEndian read trying : Bool) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent
      (binaryTransferInstruction width signed bigEndian read trying stack m)
      (binaryTransferInstruction width signed bigEndian read trying stack n) := by
  unfold CIL.Safety.binaryTransferInstruction
  split <;> try simp only [same.spanValidate, same.loadTransfer]
  all_goals repeat first
    | exact .error _
    | exact .ok ⟨same, rfl⟩
    | (apply ResultEquivalent.bind_same; intro)
    | (apply ResultEquivalent.bind (same.storeTransfer _ _ _)
       intro left right related
       first
       | exact .ok ⟨related, rfl⟩
       | split <;> exact .ok ⟨related, rfl⟩)
    | split
#print axioms Memory.Equivalent.binaryTransferInstruction

/-- A single-reference view depends only on equivalent allocation metadata. -/
theorem Memory.Equivalent.singleSpanInstruction {m n : Memory} (same : m.Equivalent n)
    (width : Nat) (writable : Bool) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (singleSpanInstruction width writable stack m)
      (singleSpanInstruction width writable stack n) := by
  unfold CIL.Safety.singleSpanInstruction
  split <;> try simp only [same.spanValidate]
  all_goals repeat first
    | exact .error _
    | exact .ok ⟨same, rfl⟩
    | (apply ResultEquivalent.bind_same; intro)
    | split
#print axioms Memory.Equivalent.singleSpanInstruction

/-- Typed array transfers observe identical bytes and preserve equivalent checked writes. -/
theorem Memory.Equivalent.arrayTransferInstruction {m n : Memory} (same : m.Equivalent n)
    (element : CIL.ArrayElement) (store : Bool) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (arrayTransferInstruction element store stack m)
      (arrayTransferInstruction element store stack n) := by
  unfold CIL.Safety.arrayTransferInstruction
  simp only [same.arrayElement, same.loadTransfer]
  repeat first
    | exact .error _
    | exact .ok ⟨same, rfl⟩
    | (apply ResultEquivalent.bind_same; intro)
    | (apply ResultEquivalent.bind (same.storeTransfer _ _ _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | split
#print axioms Memory.Equivalent.arrayTransferInstruction

/-- Aligned transfers retain exact access failures and the existing typed transfer equivalence. -/
theorem Memory.Equivalent.pointerTransferInstruction {m n : Memory} (same : m.Equivalent n)
    (kind : CIL.TransferKind) (alignment : Nat) (store : Bool) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (pointerTransferInstruction kind alignment store stack m)
      (pointerTransferInstruction kind alignment store stack n) := by
  unfold CIL.Safety.pointerTransferInstruction
  split <;> try simp only [same.access, same.loadTransfer]
  all_goals repeat first
    | exact .error _
    | exact .ok ⟨same, rfl⟩
    | (apply ResultEquivalent.bind_same; intro)
    | (apply ResultEquivalent.bind (same.storeTransfer _ _ _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | split
#print axioms Memory.Equivalent.pointerTransferInstruction

/-- Opcode dispatch preserves the memory equivalence of each checked family. -/
theorem Memory.Equivalent.memoryInstruction {m n : Memory} (same : m.Equivalent n)
    (operation : CIL.MemoryOp) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (memoryInstruction operation stack m)
      (memoryInstruction operation stack n) := by
  unfold CIL.Safety.memoryInstruction
  split
  · exact .error _
  · split
    · exact same.referenceAddInstruction _ _ _
    · exact same.pointerTransferInstruction _ _ _ _
    · exact same.arrayTransferInstruction _ _ _
    · exact same.binaryTransferInstruction _ _ _ _ _ _
    · exact same.binaryTransferInstruction _ _ _ _ _ _
    · exact same.singleSpanInstruction _ _ _
    · exact same.viewObservationInstruction _ _
    · exact same.spanCopyInstruction _ _ _
    · exact same.spanFillInstruction _ _ _
    · exact same.arrayFillInstruction _ _ _
    · exact same.otherMemoryInstruction _ _

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
