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
  unfold CIL.Safety.referenceAddInstruction CIL.Safety.displaceReference
  split <;> try simp only [same.add]
  all_goals repeat first
    | exact .error _
    | exact .ok ⟨same, rfl⟩
    | (apply ResultEquivalent.bind_same; intro)
    | split
#print axioms Memory.Equivalent.referenceAddInstruction

/-- Locating an object field reads only allocation metadata, which equivalent memories share. -/
theorem Memory.Equivalent.objectFieldAddress {m n : Memory} (same : m.Equivalent n)
    (reference : ManagedReference) (owner : CIL.Extraction.TypeExpr) (offset : Nat) :
    CIL.Safety.objectFieldAddress m reference owner offset =
      CIL.Safety.objectFieldAddress n reference owner offset := by
  cases reference <;>
    simp only [CIL.Safety.objectFieldAddress, liveAllocation, same.allocations, same.add]
#print axioms Memory.Equivalent.objectFieldAddress

/-- Locating an array of class references reads only allocation metadata. -/
theorem Memory.Equivalent.referenceArrayOf {m n : Memory} (same : m.Equivalent n)
    (array : ManagedReference) :
    CIL.Safety.referenceArrayOf m array = CIL.Safety.referenceArrayOf n array := by
  cases array <;> simp only [CIL.Safety.referenceArrayOf, liveAllocation, same.allocations]
#print axioms Memory.Equivalent.referenceArrayOf

/-- Locating an element slot of an array of class references reads only allocation metadata. -/
theorem Memory.Equivalent.referenceArraySlot {m n : Memory} (same : m.Equivalent n)
    (array : ManagedReference) (index : Nat) :
    CIL.Safety.referenceArraySlot m array index = CIL.Safety.referenceArraySlot n array index :=
  by simp only [CIL.Safety.referenceArraySlot, same.referenceArrayOf]
#print axioms Memory.Equivalent.referenceArraySlot

/-- The covariance check reads only the stored object's runtime type. -/
theorem Memory.Equivalent.storableIn {m n : Memory} (same : m.Equivalent n)
    (element : CIL.Extraction.TypeExpr) (value : ManagedReference) :
    CIL.Safety.storableIn m element value = CIL.Safety.storableIn n element value := by
  cases value <;> simp only [CIL.Safety.storableIn, liveAllocation, same.allocations]
#print axioms Memory.Equivalent.storableIn

/-- Equivalent memories hold the same field references and stay equivalent after one changes. -/
theorem Memory.Equivalent.setSlot {m n : Memory} (same : m.Equivalent n) (field : Reference)
    (value : ManagedReference) :
    (CIL.Safety.setSlot m field value).Equivalent (CIL.Safety.setSlot n field value) :=
  ⟨same.allocations, same.cells, same.permissions, same.nextIdentity, same.staticBindings,
    same.stackLimit, same.heapBudget, by simp only [CIL.Safety.setSlot, same.slots], same.literals⟩
#print axioms Memory.Equivalent.setSlot

/-- A field reference load reads the slot, authority and metadata equivalent memories share. -/
theorem Memory.Equivalent.loadSlot {m n : Memory} (same : m.Equivalent n) (field : Reference) :
    CIL.Safety.loadSlot m field = CIL.Safety.loadSlot n field := by
  simp only [CIL.Safety.loadSlot, same.access, same.formObject, same.slots]
#print axioms Memory.Equivalent.loadSlot

/-- A field reference store makes the same checks and slot change in equivalent memories. -/
theorem Memory.Equivalent.storeSlot {m n : Memory} (same : m.Equivalent n) (field : Reference)
    (value : ManagedReference) :
    ResultEquivalent Memory.Equivalent (CIL.Safety.storeSlot m field value)
      (CIL.Safety.storeSlot n field value) := by
  simp only [CIL.Safety.storeSlot, same.access, same.formObject]
  apply ResultEquivalent.bind_same
  intro
  apply ResultEquivalent.bind_same
  intro
  exact .ok (same.setSlot field value)
#print axioms Memory.Equivalent.storeSlot

/-- The array a value-array field holds reads only allocation metadata and the view's bounds. -/
theorem Memory.Equivalent.arrayOfSlot {m n : Memory} (same : m.Equivalent n)
    (held : ManagedReference) (element : CIL.ArrayElement) :
    CIL.Safety.arrayOfSlot m held element = CIL.Safety.arrayOfSlot n held element := by
  cases held <;> simp only [CIL.Safety.arrayOfSlot, liveAllocation, same.allocations,
    same.arrayValidate]
#print axioms Memory.Equivalent.arrayOfSlot

/-- A value-array field load reads the slot, authority and metadata equivalent memories share. -/
theorem Memory.Equivalent.loadArraySlot {m n : Memory} (same : m.Equivalent n)
    (field : Reference) (element : CIL.ArrayElement) :
    CIL.Safety.loadArraySlot m field element = CIL.Safety.loadArraySlot n field element := by
  simp only [CIL.Safety.loadArraySlot, same.access, same.arrayOfSlot, same.slots]
#print axioms Memory.Equivalent.loadArraySlot

/-- A value-array field store makes the same checks and slot change in equivalent memories. -/
theorem Memory.Equivalent.storeArraySlot {m n : Memory} (same : m.Equivalent n)
    (field : Reference) (view : ArrayView) (element : CIL.ArrayElement) :
    ResultEquivalent Memory.Equivalent (CIL.Safety.storeArraySlot m field view element)
      (CIL.Safety.storeArraySlot n field view element) := by
  have held : CIL.Safety.arraySlotValue m view element =
      CIL.Safety.arraySlotValue n view element := by
    unfold CIL.Safety.arraySlotValue
    split <;> simp only [liveAllocation, same.allocations]
  simp only [CIL.Safety.storeArraySlot, same.access, held]
  apply ResultEquivalent.bind_same
  intro
  apply ResultEquivalent.bind_same
  intro held
  exact .ok (same.setSlot field held)
#print axioms Memory.Equivalent.storeArraySlot

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

/-- Wide multiplication and out-reference division perform equivalent checked stores. -/
private theorem Memory.Equivalent.wideArithmeticInstruction {m n : Memory} (same : m.Equivalent n)
    (operation : CIL.MemoryOp) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (wideArithmeticInstruction operation stack m)
      (wideArithmeticInstruction operation stack n) := by
  unfold CIL.Safety.wideArithmeticInstruction
  split
  all_goals repeat first
    | exact .error _
    | exact .ok ⟨same, rfl⟩
    | (apply ResultEquivalent.bind_same; intro)
    | (apply ResultEquivalent.bind ((same.write _ _ _).mapError _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | (apply ResultEquivalent.bind (same.storeValue _ _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | split
#print axioms Memory.Equivalent.wideArithmeticInstruction

/-- Object field accesses locate the same field and perform equivalent checked accesses. -/
private theorem Memory.Equivalent.objectFieldInstruction {m n : Memory} (same : m.Equivalent n)
    (operation : CIL.MemoryOp) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (objectFieldInstruction operation stack m)
      (objectFieldInstruction operation stack n) := by
  unfold CIL.Safety.objectFieldInstruction
  split <;> try simp only [same.objectFieldAddress, same.loadValue, same.loadSlot,
    same.referenceArrayOf, same.referenceArraySlot, same.storableIn, same.loadArraySlot]
  all_goals repeat first
    | exact .error _
    | exact .ok ⟨same, rfl⟩
    | (apply ResultEquivalent.bind_same; intro)
    | (apply ResultEquivalent.bind ((same.write _ _ _).mapError _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | (apply ResultEquivalent.bind (same.storeSlot _ _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | (apply ResultEquivalent.bind (same.storeArraySlot _ _ _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | split
#print axioms Memory.Equivalent.objectFieldInstruction

/-- A string literal loads the same bound object from equivalent memories. -/
private theorem Memory.Equivalent.stringLiteralInstruction {m n : Memory} (same : m.Equivalent n)
    (text : String) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (stringLiteralInstruction text stack m)
      (stringLiteralInstruction text stack n) := by
  unfold CIL.Safety.stringLiteralInstruction CIL.Safety.literalObject
  rw [same.literals]
  split
  all_goals first
    | exact .error _
    | (rw [same.formObject]
       apply ResultEquivalent.bind_same
       intro
       exact .ok ⟨same, rfl⟩)
#print axioms Memory.Equivalent.stringLiteralInstruction

/-- A null guard reads only the stack, so equivalent memories give the same outcome. -/
private theorem Memory.Equivalent.throwIfNullInstruction {m n : Memory} (same : m.Equivalent n)
    (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (throwIfNullInstruction stack m)
      (throwIfNullInstruction stack n) := by
  unfold CIL.Safety.throwIfNullInstruction
  split
  all_goals first | exact .error _ | exact .ok ⟨same, rfl⟩
#print axioms Memory.Equivalent.throwIfNullInstruction

/-- A zero guard reads only the stack, so equivalent memories give the same outcome. -/
private theorem Memory.Equivalent.zeroGuardInstruction {m n : Memory} (same : m.Equivalent n)
    (guard : ZeroGuard) (width : Nat) (signed : Bool) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (zeroGuardInstruction guard width signed stack m)
      (zeroGuardInstruction guard width signed stack n) := by
  unfold CIL.Safety.zeroGuardInstruction
  repeat first | exact .error _ | exact .ok ⟨same, rfl⟩ | split
#print axioms Memory.Equivalent.zeroGuardInstruction

/-- A comparison guard reads only the stack, so equivalent memories give the same outcome. -/
private theorem Memory.Equivalent.comparisonGuardInstruction {m n : Memory}
    (same : m.Equivalent n) (guard : ComparisonGuard) (width : Nat) (signed : Bool)
    (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (comparisonGuardInstruction guard width signed stack m)
      (comparisonGuardInstruction guard width signed stack n) := by
  unfold CIL.Safety.comparisonGuardInstruction
  repeat first | exact .error _ | exact .ok ⟨same, rfl⟩ | split
#print axioms Memory.Equivalent.comparisonGuardInstruction

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

/-- Vector128 byte loads and stores displace, read and write identically over equivalent
    memories. -/
theorem Memory.Equivalent.vector128UnsafeInstruction {m n : Memory} (same : m.Equivalent n)
    (store offset : Bool) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (vector128UnsafeInstruction store offset stack m)
      (vector128UnsafeInstruction store offset stack n) := by
  unfold CIL.Safety.vector128UnsafeInstruction CIL.Safety.displaceReference
  split <;> try simp only [same.add, same.loadValue]
  all_goals repeat first
    | exact .error _
    | exact .ok ⟨same, rfl⟩
    | (apply ResultEquivalent.bind_same; intro)
    | (apply ResultEquivalent.bind (same.storeValue _ _)
       intro left right related
       exact .ok ⟨related, rfl⟩)
    | split
#print axioms Memory.Equivalent.vector128UnsafeInstruction

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
    · exact same.vector128UnsafeInstruction _ _ _
    · exact same.arrayTransferInstruction _ _ _
    · exact same.binaryTransferInstruction _ _ _ _ _ _
    · exact same.binaryTransferInstruction _ _ _ _ _ _
    · exact same.singleSpanInstruction _ _ _
    · exact same.viewObservationInstruction _ _
    · exact same.spanCopyInstruction _ _ _
    · exact same.spanFillInstruction _ _ _
    · exact same.arrayFillInstruction _ _ _
    · exact same.wideArithmeticInstruction _ _
    · exact same.wideArithmeticInstruction _ _
    · exact same.objectFieldInstruction _ _
    · exact same.objectFieldInstruction _ _
    · exact same.objectFieldInstruction _ _
    · exact same.objectFieldInstruction _ _
    · exact same.objectFieldInstruction _ _
    · exact same.objectFieldInstruction _ _
    · exact same.objectFieldInstruction _ _
    · exact same.objectFieldInstruction _ _
    · exact same.objectFieldInstruction _ _
    · exact same.stringLiteralInstruction _ _
    · exact same.throwIfNullInstruction _
    · exact same.zeroGuardInstruction _ _ _ _
    · exact same.comparisonGuardInstruction _ _ _ _
    · exact same.otherMemoryInstruction _ _

theorem Memory.Equivalent.instruction {m n : Memory} (same : m.Equivalent n)
    (operation : CIL.Instruction) (stack : List Value) :
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
