import CIL.Safety.MemoryEquivalence
import CIL.Safety.Frames

/-!
# Frame operations respect memory equivalence

Every frame operation in `CIL/Safety/Frames.lean` (load, store, address, allocation, entry
and exit) gives equivalent results, or equal faults, on `Memory.Equivalent` memories, which
may differ only in how their view lists are represented. Values agree exactly; returned
memories are again `Memory.Equivalent`. The checked interpreter's equivalence
proof in `CIL/Safety/ExecutionEquivalence.lean` is assembled from these.
-/

namespace CIL.Safety

/-- Span validation observes only allocation descriptors. -/
theorem Memory.Equivalent.spanValidate {m n : Memory} (same : m.Equivalent n) (view : SpanView) :
    view.validate m = view.validate n := by
  simp only [SpanView.validate, liveAllocation, same.allocations]

/-- Slicing respects observational memory equivalence. -/
theorem Memory.Equivalent.spanSlice {m n : Memory} (same : m.Equivalent n)
    (view : SpanView) (start length : Nat) : view.slice m start length = view.slice n start length := by
  simp only [SpanView.slice, same.spanValidate]

/-- Indexed addresses respect observational memory equivalence. -/
theorem Memory.Equivalent.spanElement {m n : Memory} (same : m.Equivalent n)
    (view : SpanView) (index : Nat) : view.element m index = view.element n index := by
  simp only [SpanView.element, same.spanValidate, same.form]

#print axioms Memory.Equivalent.spanValidate
#print axioms Memory.Equivalent.spanSlice
#print axioms Memory.Equivalent.spanElement

/-- Filling a span preserves observational equivalence, including newly readable bytes. -/
theorem Memory.Equivalent.spanFill {m n : Memory} (same : m.Equivalent n)
    (view : SpanView) (element : List (BitVec 8)) :
    ResultEquivalent Memory.Equivalent (view.fill m element) (view.fill n element) := by
  unfold SpanView.fill
  rw [same.spanValidate]
  repeat first
    | exact .error _
    | exact .ok same
    | exact same.write _ _ _
    | (apply ResultEquivalent.bind_same; intro)
    | split
#print axioms Memory.Equivalent.spanFill

/-- Array formation respects observational memory equivalence. -/
theorem Memory.Equivalent.arrayValidate {m n : Memory} (same : m.Equivalent n)
    (view : ArrayView) : view.validate m = view.validate n := by
  simp only [ArrayView.validate, same.spanValidate]

/-- Array element addresses respect observational memory equivalence. -/
theorem Memory.Equivalent.arrayViewElement {m n : Memory} (same : m.Equivalent n)
    (view : ArrayView) (index : Nat) : view.element m index = view.element n index := by
  simp only [ArrayView.element, same.arrayValidate, same.spanElement]

/-- Array access checks produce the same address or fault in equivalent memories. -/
theorem Memory.Equivalent.arrayElement {m n : Memory} (same : m.Equivalent n)
    (view : ArrayView) (index width : Nat) :
    CIL.Safety.arrayElement m view index width = CIL.Safety.arrayElement n view index width := by
  simp only [CIL.Safety.arrayElement, same.arrayValidate, same.arrayViewElement]

#print axioms Memory.Equivalent.arrayValidate
#print axioms Memory.Equivalent.arrayViewElement
#print axioms Memory.Equivalent.arrayElement

theorem Memory.Equivalent.loadSnapshot {m n : Memory} (same : m.Equivalent n)
    (r : ManagedReference) (shape : CIL.SnapshotShape) :
    loadSnapshot m r shape = loadSnapshot n r shape := by
  simp only [CIL.Safety.loadSnapshot, same.readSnapshot]

theorem Memory.Equivalent.formValue {m n : Memory} (same : m.Equivalent n)
    (r : ManagedReference) :
    CIL.Safety.formValue m r = CIL.Safety.formValue n r := by
  cases r <;> simp only [CIL.Safety.formValue, same.form]

theorem Memory.Equivalent.loadLocal {m n : Memory} (same : m.Equivalent n)
    (slot : LocalSlot) :
    CIL.Safety.loadLocal m slot = CIL.Safety.loadLocal n slot := by
  cases slot with
  | root value => cases value <;> simp only [CIL.Safety.loadLocal, same.formValue]
  | readOnlyRoot value => simp only [CIL.Safety.loadLocal, same.formValue]
  | bytes kind reference => simp only [CIL.Safety.loadLocal, same.read, same.loadSnapshot]
  | opaque128 value => cases value <;> rfl
  | span width writable value =>
    cases value <;> simp only [CIL.Safety.loadLocal, same.spanValidate]
  | array element value =>
    cases value <;> simp only [CIL.Safety.loadLocal, same.arrayValidate]

theorem Memory.Equivalent.localAddress {m n : Memory} (same : m.Equivalent n)
    (slot : LocalSlot) :
    CIL.Safety.localAddress m slot = CIL.Safety.localAddress n slot := by
  cases slot <;> simp only [CIL.Safety.localAddress, same.formValue]

theorem Memory.Equivalent.allocateHome {m n : Memory} (same : m.Equivalent n)
    (activation width alignment : Nat) :
    ResultEquivalent MemoryLastEquivalent
      (CIL.Safety.allocateHome m activation width alignment)
      (CIL.Safety.allocateHome n activation width alignment) := by
  unfold CIL.Safety.allocateHome checkedAt
  apply ResultEquivalent.bind (same.allocate _ |>.mapError _)
  intro left right related
  obtain ⟨id, allocated⟩ := left
  obtain ⟨other, otherMemory⟩ := right
  obtain ⟨rfl, memory⟩ := related
  exact .ok ⟨rfl, memory.prependView _⟩

theorem Memory.Equivalent.storeLocal {m n : Memory} (same : m.Equivalent n)
    (slot : LocalSlot) (value : Value) :
    ResultEquivalent MemoryLastEquivalent (CIL.Safety.storeLocal m slot value)
      (CIL.Safety.storeLocal n slot value) := by
  cases slot with
  | opaque128 slot =>
    cases value with
    | scalar scalar =>
      cases scalar <;> first | exact .error _ | exact .ok ⟨rfl, same⟩
    | reference _ => exact .error _
    | span _ _ => exact .error _
    | bufferSpan _ | readOnlyReference _ | array _ => exact .error _
  | root root | readOnlyRoot root =>
    cases value with
    | reference reference | readOnlyReference reference =>
      simp only [CIL.Safety.storeLocal, Value.hasUnspecified, same.formValue, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
      apply ResultEquivalent.bind_same
      intro ignored
      exact .ok ⟨rfl, same⟩
    | scalar scalar => cases scalar <;> exact .error _
    | span reference length => exact .error _
    | bufferSpan _ | array _ => exact .error _
  | bytes kind reference =>
    cases value with
    | scalar value =>
      cases value <;> simp only [CIL.Safety.storeLocal, Value.hasUnspecified,
        CIL.Value.hasUnspecified, Bool.not_false, Bool.and_true,
        Bool.false_eq_true, ↓reduceIte]
      all_goals first
        | exact .error _
        | (split
           · exact .error _
           · apply ResultEquivalent.bind (same.writeSnapshot _ _ _ |>.mapError _)
             intro left right related
             exact .ok ⟨rfl, related⟩)
        | (apply ResultEquivalent.bind_same
           intro number
           apply ResultEquivalent.bind
             (same.write reference (numberBytes number (localWidth kind)) 1 |>.mapError _)
           intro left right related
           exact .ok ⟨rfl, related⟩)
    | reference reference => exact .error _
    | span reference length => exact .error _
    | bufferSpan _ | readOnlyReference _ | array _ => exact .error _
  | span width writable stored =>
    cases value
    case scalar scalar => cases scalar <;> exact .error _
    all_goals simp only [CIL.Safety.storeLocal, Value.hasUnspecified,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, same.spanValidate]
    all_goals repeat' first
      | contradiction
      | exact .error _
      | exact .ok ⟨rfl, same⟩
      | (apply ResultEquivalent.bind_same; intro)
      | split
  | array element stored =>
    cases value
    case scalar scalar => cases scalar <;> exact .error _
    all_goals simp only [CIL.Safety.storeLocal, Value.hasUnspecified,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, same.arrayValidate]
    all_goals repeat' first
      | contradiction
      | exact .error _
      | exact .ok ⟨rfl, same⟩
      | (apply ResultEquivalent.bind_same; intro)
      | split

/-- Two frame-builder results agree on the built value and owned ids, and their memories are
    equivalent. -/
def OwnedEquivalent (left right : α × List AllocationId × Memory) : Prop :=
  left.1 = right.1 ∧ left.2.1 = right.2.1 ∧ left.2.2.Equivalent right.2.2

theorem Memory.Equivalent.makeLocal {m n : Memory} (same : m.Equivalent n)
    (activation : Nat) (kind : CIL.LocalKind) (initial : CIL.Value) :
    ResultEquivalent OwnedEquivalent (CIL.Safety.makeLocal activation kind initial m)
      (CIL.Safety.makeLocal activation kind initial n) := by
  cases kind <;> simp only [CIL.Safety.makeLocal]
  all_goals first
  | (split
     · exact .error _
     · cases initial <;> first | exact .error _ | exact .ok ⟨rfl, rfl, same⟩)
  | (apply ResultEquivalent.bind (same.allocateHome _ _ _)
     intro left right related
     obtain ⟨reference, memory⟩ := left
     obtain ⟨other, otherMemory⟩ := right
     obtain ⟨rfl, equivalent⟩ := related
     split
     · exact .ok ⟨rfl, rfl, equivalent⟩
     · apply ResultEquivalent.bind (equivalent.storeLocal _ _)
       intro left right related
       obtain ⟨slot, stored⟩ := left
       obtain ⟨otherSlot, otherStored⟩ := right
       obtain ⟨rfl, storedEquivalent⟩ := related
       exact .ok ⟨rfl, rfl, storedEquivalent⟩)
  | (cases initial <;> first | exact .error _ | exact .ok ⟨rfl, rfl, same⟩)

theorem Memory.Equivalent.makeLocals {m n : Memory} (same : m.Equivalent n)
    (activation : Nat) (kinds : List CIL.LocalKind) (initializers : List CIL.Value) :
    ResultEquivalent OwnedEquivalent (CIL.Safety.makeLocals activation kinds initializers m)
      (CIL.Safety.makeLocals activation kinds initializers n) := by
  induction kinds generalizing m n initializers with
  | nil => cases initializers <;> first | exact .error _ | exact .ok ⟨rfl, rfl, same⟩
  | cons kind kinds ih =>
    cases initializers with
    | nil => exact .error _
    | cons initial initials =>
      simp only [CIL.Safety.makeLocals]
      apply ResultEquivalent.bind (same.makeLocal activation kind initial)
      intro left right related
      obtain ⟨slot, owned, memory⟩ := left
      obtain ⟨otherSlot, otherOwned, otherMemory⟩ := right
      obtain ⟨rfl, rfl, equivalent⟩ := related
      apply ResultEquivalent.bind (ih equivalent initials)
      intro left right related
      obtain ⟨slots, ids, stored⟩ := left
      obtain ⟨otherSlots, otherIds, otherStored⟩ := right
      obtain ⟨rfl, rfl, storedEquivalent⟩ := related
      exact .ok ⟨rfl, rfl, storedEquivalent⟩

theorem Memory.Equivalent.makeOpaque128 {m n : Memory} (same : m.Equivalent n)
    (initial : CIL.Value) :
    ResultEquivalent OwnedEquivalent (CIL.Safety.makeOpaque128 initial m)
      (CIL.Safety.makeOpaque128 initial n) := by
  cases initial <;> first | exact .error _ | exact .ok ⟨rfl, rfl, same⟩

theorem Memory.Equivalent.makeSelectedLocalsFrom {m n : Memory} (same : m.Equivalent n)
    (activation : Nat) (indices : List Nat) (index : Nat) (kinds : List CIL.LocalKind)
    (initializers : List CIL.Value) :
    ResultEquivalent OwnedEquivalent
      (CIL.Safety.makeSelectedLocalsFrom activation indices index kinds initializers m)
      (CIL.Safety.makeSelectedLocalsFrom activation indices index kinds initializers n) := by
  induction kinds generalizing m n index initializers with
  | nil => cases initializers <;> first | exact .error _ | exact .ok ⟨rfl, rfl, same⟩
  | cons kind kinds ih =>
    cases initializers with
    | nil => exact .error _
    | cons initial initials =>
      simp only [CIL.Safety.makeSelectedLocalsFrom]
      have finish (left right : ExecutionResult (LocalSlot × List AllocationId × Memory))
          (related : ResultEquivalent OwnedEquivalent left right) :
          ResultEquivalent OwnedEquivalent
            (do
              let (slot, owned, memory) ← left
              let (slots, ids, stored) ← CIL.Safety.makeSelectedLocalsFrom activation indices
                (index + 1) kinds initials memory
              pure (slot :: slots, owned ++ ids, stored))
            (do
              let (slot, owned, memory) ← right
              let (slots, ids, stored) ← CIL.Safety.makeSelectedLocalsFrom activation indices
                (index + 1) kinds initials memory
              pure (slot :: slots, owned ++ ids, stored)) := by
        apply ResultEquivalent.bind related
        intro left right related
        obtain ⟨slot, owned, memory⟩ := left
        obtain ⟨otherSlot, otherOwned, otherMemory⟩ := right
        obtain ⟨rfl, rfl, equivalent⟩ := related
        apply ResultEquivalent.bind (ih equivalent (index + 1) initials)
        intro left right related
        obtain ⟨slots, ids, stored⟩ := left
        obtain ⟨otherSlots, otherIds, otherStored⟩ := right
        obtain ⟨rfl, rfl, storedEquivalent⟩ := related
        exact .ok ⟨rfl, rfl, storedEquivalent⟩
      by_cases member : index ∈ indices
      · by_cases width : (kind == .vector128) = true
        · simp only [member, width, ite_true]
          exact finish _ _ (same.makeOpaque128 initial)
        · simp only [member, width, ite_true, Bind.bind, Except.bind]
          exact .error _
      · simp only [member, ite_false]
        exact finish _ _ (same.makeLocal _ _ _)

theorem Memory.Equivalent.makeSelectedLocals {m n : Memory} (same : m.Equivalent n)
    (activation : Nat) (indices : List Nat) (kinds : List CIL.LocalKind)
    (initializers : List CIL.Value) :
    ResultEquivalent OwnedEquivalent
      (CIL.Safety.makeSelectedLocals activation indices kinds initializers m)
      (CIL.Safety.makeSelectedLocals activation indices kinds initializers n) := by
  unfold CIL.Safety.makeSelectedLocals
  split
  · exact same.makeLocals _ _ _
  · exact same.makeSelectedLocalsFrom _ _ _ _ _

theorem Memory.Equivalent.makeArgumentHomes {m n : Memory} (same : m.Equivalent n)
    (activation : Nat) (indices : List Nat) (args : List Value) :
    ResultEquivalent OwnedEquivalent (CIL.Safety.makeArgumentHomes activation indices args m)
      (CIL.Safety.makeArgumentHomes activation indices args n) := by
  induction indices generalizing m n with
  | nil => exact .ok ⟨rfl, rfl, same⟩
  | cons index indices ih =>
    simp only [CIL.Safety.makeArgumentHomes]
    cases found : args[index]? with
    | none =>
      simp only [Option.map_none, Option.getD_none, Bool.false_eq_true, ite_false]
      exact .error _
    | some value =>
      simp only [Option.map_some, Option.getD_some]
      cases value with
      | reference reference => exact .error _
      | span reference length => exact .error _
      | bufferSpan _ | readOnlyReference _ | array _ => exact .error _
      | scalar value =>
        cases value <;> first | exact .error _ | skip
        apply ResultEquivalent.bind (same.allocateHome _ _ _)
        intro left right related
        obtain ⟨reference, memory⟩ := left
        obtain ⟨other, otherMemory⟩ := right
        obtain ⟨rfl, equivalent⟩ := related
        apply ResultEquivalent.bind (equivalent.storeLocal _ _)
        intro left right related
        obtain ⟨slot, stored⟩ := left
        obtain ⟨otherSlot, otherStored⟩ := right
        obtain ⟨rfl, storedEquivalent⟩ := related
        apply ResultEquivalent.bind (ih storedEquivalent)
        intro left right related
        obtain ⟨homes, owned, result⟩ := left
        obtain ⟨otherHomes, otherOwned, otherResult⟩ := right
        obtain ⟨rfl, rfl, resultEquivalent⟩ := related
        exact .ok ⟨rfl, rfl, resultEquivalent⟩

theorem Memory.Equivalent.makeParameterHomes {m n : Memory} (same : m.Equivalent n)
    (activation : Nat) (parameters : List (Nat × CIL.LocalKind)) (args : List Value) :
    ResultEquivalent OwnedEquivalent (CIL.Safety.makeParameterHomes activation parameters args m)
      (CIL.Safety.makeParameterHomes activation parameters args n) := by
  induction parameters generalizing m n with
  | nil => exact .ok ⟨rfl, rfl, same⟩
  | cons parameter parameters ih =>
    obtain ⟨index, kind⟩ := parameter
    simp only [CIL.Safety.makeParameterHomes]
    cases found : args[index]? with
    | none => exact .error _
    | some value =>
      apply ResultEquivalent.bind (same.makeLocal activation kind .unmodeled)
      intro left right related
      obtain ⟨slot, owned, memory⟩ := left
      obtain ⟨otherSlot, otherOwned, otherMemory⟩ := right
      obtain ⟨rfl, rfl, equivalent⟩ := related
      apply ResultEquivalent.bind (equivalent.storeLocal _ _)
      intro left right related
      obtain ⟨slot, stored⟩ := left
      obtain ⟨otherSlot, otherStored⟩ := right
      obtain ⟨rfl, storedEquivalent⟩ := related
      apply ResultEquivalent.bind (ih storedEquivalent)
      intro left right related
      obtain ⟨homes, ids, result⟩ := left
      obtain ⟨otherHomes, otherIds, otherResult⟩ := right
      obtain ⟨rfl, rfl, resultEquivalent⟩ := related
      exact .ok ⟨rfl, rfl, resultEquivalent⟩

theorem Memory.Equivalent.enterFrame {m n : Memory} (same : m.Equivalent n)
    (body : CIL.Method) (args : List Value) :
    ResultEquivalent MemoryLastEquivalent (CIL.Safety.enterFrame body args m)
      (CIL.Safety.enterFrame body args n) := by
  simp only [CIL.Safety.enterFrame, same.nextIdentity]
  apply ResultEquivalent.bind (same.makeSelectedLocals _ _ _ _)
  intro left right related
  obtain ⟨locals, owned, memory⟩ := left
  obtain ⟨otherLocals, otherOwned, otherMemory⟩ := right
  obtain ⟨rfl, rfl, equivalent⟩ := related
  apply ResultEquivalent.bind (equivalent.makeArgumentHomes _ _ _)
  intro left right related
  obtain ⟨arguments, argumentIds, stored⟩ := left
  obtain ⟨otherArguments, otherIds, otherStored⟩ := right
  obtain ⟨rfl, rfl, storedEquivalent⟩ := related
  apply ResultEquivalent.bind (storedEquivalent.makeParameterHomes _ _ _)
  intro left right related
  obtain ⟨parameters, parameterIds, result⟩ := left
  obtain ⟨otherParameters, otherParameterIds, otherResult⟩ := right
  obtain ⟨rfl, rfl, resultEquivalent⟩ := related
  exact .ok ⟨rfl, resultEquivalent⟩

theorem Memory.Equivalent.leaveFrame {m n : Memory} (same : m.Equivalent n)
    (frame : Frame) :
    Memory.Equivalent (CIL.Safety.leaveFrame frame m) (CIL.Safety.leaveFrame frame n) := by
  unfold CIL.Safety.leaveFrame
  generalize frame.owned = ids
  induction ids generalizing m n with
  | nil => exact same
  | cons id ids ih => exact ih (same.expire id)

#print axioms Memory.Equivalent.makeLocals
#print axioms Memory.Equivalent.makeArgumentHomes
#print axioms Memory.Equivalent.makeParameterHomes
#print axioms Memory.Equivalent.enterFrame
#print axioms Memory.Equivalent.leaveFrame
#print axioms Memory.Equivalent.allocateHome
#print axioms Memory.Equivalent.storeLocal

end CIL.Safety
