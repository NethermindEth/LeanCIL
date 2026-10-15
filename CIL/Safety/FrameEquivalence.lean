import CIL.Safety.MemoryEquivalence
import CIL.Safety.Frames

namespace CIL.Safety

theorem Memory.Equivalent.formValue {m n : Memory} (same : m.Equivalent n) (r : ManagedReference) :
    CIL.Safety.formValue m r = CIL.Safety.formValue n r := by
  cases r <;> simp only [CIL.Safety.formValue, same.form]

theorem Memory.Equivalent.loadLocal {m n : Memory} (same : m.Equivalent n) (slot : LocalSlot) :
    CIL.Safety.loadLocal m slot = CIL.Safety.loadLocal n slot := by
  cases slot with
  | root value => cases value <;> simp only [CIL.Safety.loadLocal, same.formValue]
  | bytes kind reference => simp only [CIL.Safety.loadLocal, same.read]

theorem Memory.Equivalent.localAddress {m n : Memory} (same : m.Equivalent n) (slot : LocalSlot) :
    CIL.Safety.localAddress m slot = CIL.Safety.localAddress n slot := by
  cases slot <;> simp only [CIL.Safety.localAddress, same.formValue]

theorem Memory.Equivalent.allocateHome {m n : Memory} (same : m.Equivalent n)
    (activation width alignment : Nat) :
    ResultEquivalent MemoryLastEquivalent
      (CIL.Safety.allocateHome m activation width alignment) (CIL.Safety.allocateHome n activation width alignment) := by
  unfold CIL.Safety.allocateHome checkedAt
  apply ResultEquivalent.bind (same.allocate _ |>.mapError _)
  intro left right related
  obtain ⟨id, allocated⟩ := left
  obtain ⟨other, otherMemory⟩ := right
  obtain ⟨rfl, memory⟩ := related
  exact .ok ⟨rfl, memory.prependView _⟩

theorem Memory.Equivalent.storeLocal {m n : Memory} (same : m.Equivalent n)
    (slot : LocalSlot) (value : Value) :
    ResultEquivalent MemoryLastEquivalent (CIL.Safety.storeLocal m slot value) (CIL.Safety.storeLocal n slot value) := by
  cases slot with
  | root root =>
    cases value with
    | reference reference =>
      simp only [CIL.Safety.storeLocal, same.formValue]
      apply ResultEquivalent.bind_same
      intro ignored
      exact .ok ⟨rfl, same⟩
    | scalar scalar => exact .error _
    | span reference length => exact .error _
  | bytes kind reference =>
    cases value with
    | scalar value =>
      simp only [CIL.Safety.storeLocal]
      apply ResultEquivalent.bind_same
      intro number
      apply ResultEquivalent.bind (same.write reference (numberBytes number (localWidth kind)) 1 |>.mapError _)
      intro left right related
      exact .ok ⟨rfl, related⟩
    | reference reference => exact .error _
    | span reference length => exact .error _

def OwnedEquivalent (left right : α × List AllocationId × Memory) : Prop :=
  left.1 = right.1 ∧ left.2.1 = right.2.1 ∧ left.2.2.Equivalent right.2.2

theorem Memory.Equivalent.makeLocal {m n : Memory} (same : m.Equivalent n)
    (activation : Nat) (kind : CIL.LocalKind) (initial : CIL.Value) :
    ResultEquivalent OwnedEquivalent (CIL.Safety.makeLocal activation kind initial m)
      (CIL.Safety.makeLocal activation kind initial n) := by
  cases kind <;> simp only [CIL.Safety.makeLocal]
  all_goals first
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

theorem Memory.Equivalent.makeArgumentHomes {m n : Memory} (same : m.Equivalent n)
    (activation : Nat) (indices : List Nat) (args : List Value) :
    ResultEquivalent OwnedEquivalent (CIL.Safety.makeArgumentHomes activation indices args m)
      (CIL.Safety.makeArgumentHomes activation indices args n) := by
  induction indices generalizing m n with
  | nil => exact .ok ⟨rfl, rfl, same⟩
  | cons index indices ih =>
    simp only [CIL.Safety.makeArgumentHomes]
    cases found : args[index]? with
    | none => exact .error _
    | some value =>
      cases value with
      | reference reference => exact .error _
      | span reference length => exact .error _
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
    ResultEquivalent MemoryLastEquivalent (CIL.Safety.enterFrame body args m) (CIL.Safety.enterFrame body args n) := by
  simp only [CIL.Safety.enterFrame, same.nextIdentity]
  apply ResultEquivalent.bind (same.makeLocals _ _ _)
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

theorem Memory.Equivalent.leaveFrame {m n : Memory} (same : m.Equivalent n) (frame : Frame) :
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
