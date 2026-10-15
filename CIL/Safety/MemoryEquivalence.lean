import CIL.Safety.ViewReuse

namespace CIL.Safety

/-- Interpreter-visible memory observations. The public view list representation
    may differ; authority at every address, allocation identities and static
    bindings must agree. Contracts inspecting the raw view list are excluded. -/
structure Memory.Equivalent (left right : Memory) : Prop where
  allocations : left.allocations = right.allocations
  cells : left.cells = right.cells
  permissions : ∀ writing reference, permitted left writing reference = permitted right writing reference
  nextIdentity : left.nextIdentity = right.nextIdentity
  staticBindings : left.staticBindings = right.staticBindings

theorem Memory.Equivalent.refl (m : Memory) : m.Equivalent m :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Memory.Equivalent.symm {m n : Memory} (same : m.Equivalent n) : n.Equivalent m :=
  ⟨same.allocations.symm, same.cells.symm, fun w r => (same.permissions w r).symm,
    same.nextIdentity.symm, same.staticBindings.symm⟩

theorem Memory.Equivalent.trans {m n p : Memory} (first : m.Equivalent n) (second : n.Equivalent p) :
    m.Equivalent p :=
  ⟨first.allocations.trans second.allocations, first.cells.trans second.cells,
    fun w r => (first.permissions w r).trans (second.permissions w r),
    first.nextIdentity.trans second.nextIdentity, first.staticBindings.trans second.staticBindings⟩

/-- Errors, including their exact payloads, must coincide. -/
inductive ResultEquivalent (relation : α → β → Prop) : Except ε α → Except ε β → Prop where
  | error (fault : ε) : ResultEquivalent relation (.error fault) (.error fault)
  | ok {left : α} {right : β} : relation left right → ResultEquivalent relation (.ok left) (.ok right)

theorem ResultEquivalent.bind {left : Except ε α} {right : Except ε β}
    {relation : α → β → Prop} {result : γ → δ → Prop}
    {f : α → Except ε γ} {g : β → Except ε δ}
    (same : ResultEquivalent relation left right)
    (next : ∀ a b, relation a b → ResultEquivalent result (f a) (g b)) :
    ResultEquivalent result (left.bind f) (right.bind g) := by
  cases same with
  | error fault => exact .error fault
  | ok related => exact next _ _ related

theorem ResultEquivalent.bind_same (value : Except ε α) {result : β → γ → Prop}
    {f : α → Except ε β} {g : α → Except ε γ}
    (next : ∀ a, ResultEquivalent result (f a) (g a)) :
    ResultEquivalent result (value.bind f) (value.bind g) := by
  cases value with
  | error fault => exact .error fault
  | ok a => exact next a

theorem ResultEquivalent.mapError {left : Except ε α} {right : Except ε β}
    {relation : α → β → Prop} (same : ResultEquivalent relation left right) (f : ε → δ) :
    ResultEquivalent relation (left.mapError f) (right.mapError f) := by
  cases same with
  | error fault => exact .error _
  | ok related => exact .ok related

theorem ResultEquivalent.map {left : Except ε α} {right : Except ε β}
    {relation : α → β → Prop} {result : γ → δ → Prop}
    (same : ResultEquivalent relation left right) (f : α → γ) (g : β → δ)
    (next : ∀ a b, relation a b → result (f a) (g b)) :
    ResultEquivalent result (left.map f) (right.map g) := by
  cases same with
  | error fault => exact .error _
  | ok related => exact .ok (next _ _ related)

theorem Memory.Equivalent.form {m n : Memory} (same : m.Equivalent n) (r : Reference) :
    CIL.Safety.form m r = CIL.Safety.form n r := by simp only [CIL.Safety.form, liveAllocation, same.allocations]

theorem Memory.Equivalent.access {m n : Memory} (same : m.Equivalent n)
    (r : Reference) (width alignment : Nat) (writing : Bool) :
    CIL.Safety.access m r width alignment writing = CIL.Safety.access n r width alignment writing := by
  simp only [CIL.Safety.access, same.form, liveAllocation, same.allocations, same.permissions]

theorem Memory.Equivalent.read {m n : Memory} (same : m.Equivalent n)
    (r : Reference) (width alignment : Nat) : CIL.Safety.read m r width alignment = CIL.Safety.read n r width alignment := by
  simp only [CIL.Safety.read, same.access, same.cells]

theorem Memory.Equivalent.add {m n : Memory} (same : m.Equivalent n)
    (r : Reference) (size : Nat) (offset : BitVec 64) :
    CIL.Safety.add m r size offset = CIL.Safety.add n r size offset := by
  simp only [CIL.Safety.add, same.form]

theorem Memory.Equivalent.dereference {m n : Memory} (same : m.Equivalent n)
    (r : ManagedReference) (width alignment : Nat) :
    CIL.Safety.dereference m r width alignment = CIL.Safety.dereference n r width alignment := by
  cases r <;> simp only [CIL.Safety.dereference, same.read]

theorem Memory.Equivalent.prependView {m n : Memory} (same : m.Equivalent n) (view : View) :
    Memory.Equivalent { m with views := view :: m.views } { n with views := view :: n.views } := by
  refine ⟨same.allocations, same.cells, ?_, same.nextIdentity, same.staticBindings⟩
  intro writing reference
  simp only [permitted, List.any_cons]
  exact congrArg (fun rest => (viewContains view reference &&
    (if writing then view.writable else view.readable)) || rest) (same.permissions writing reference)

theorem Memory.Equivalent.expire {m n : Memory} (same : m.Equivalent n) (id : AllocationId) :
    Memory.Equivalent (CIL.Safety.expire m id) (CIL.Safety.expire n id) := by
  refine ⟨?_, same.cells, same.permissions, same.nextIdentity, same.staticBindings⟩
  simp only [CIL.Safety.expire, same.allocations]

theorem Memory.Equivalent.write {m n : Memory} (same : m.Equivalent n)
    (r : Reference) (bytes : List (BitVec 8)) (alignment : Nat) :
    ResultEquivalent Memory.Equivalent (CIL.Safety.write m r bytes alignment) (CIL.Safety.write n r bytes alignment) := by
  unfold CIL.Safety.write
  rw [same.access]
  cases ha : CIL.Safety.access n r bytes.length alignment true with
  | error fault => exact .error fault
  | ok value =>
    cases value
    apply ResultEquivalent.ok
    refine ⟨same.allocations, ?_, ?_, same.nextIdentity, same.staticBindings⟩
    · simp only [same.cells]
    · intro writing reference
      change permitted { m with views := writeViews m r bytes.length } writing reference =
        permitted { n with views := writeViews n r bytes.length } writing reference
      rw [writeViews_permitted, writeViews_permitted]
      exact (same.prependView _).permissions writing reference

def MemoryFirstEquivalent (left right : Memory × α) : Prop :=
  left.1.Equivalent right.1 ∧ left.2 = right.2

def MemoryLastEquivalent (left right : α × Memory) : Prop :=
  left.1 = right.1 ∧ left.2.Equivalent right.2

theorem Memory.Equivalent.allocate {m n : Memory} (same : m.Equivalent n) (a : Allocation) :
    ResultEquivalent MemoryLastEquivalent (CIL.Safety.allocate m a) (CIL.Safety.allocate n a) := by
  unfold CIL.Safety.allocate
  rw [same.allocations, same.nextIdentity]
  split
  · exact .error _
  · split
    · exact .error _
    · apply ResultEquivalent.ok
      refine ⟨rfl, ?_, ?_, same.permissions, rfl, same.staticBindings⟩
      · rfl
      · simp only [same.cells]

theorem Memory.Equivalent.copy {m n : Memory} (same : m.Equivalent n)
    (source target : Reference) (width : Nat) :
    ResultEquivalent Memory.Equivalent (CIL.Safety.copy m source target width) (CIL.Safety.copy n source target width) := by
  unfold CIL.Safety.copy
  rw [same.read]
  cases h : CIL.Safety.read n source width 1 with
  | error fault => exact .error fault
  | ok bytes => exact same.write target bytes 1

theorem Memory.Equivalent.skipInit {m n : Memory} (same : m.Equivalent n) (r : Reference) :
    ResultEquivalent Memory.Equivalent (CIL.Safety.skipInit m r) (CIL.Safety.skipInit n r) := by
  unfold CIL.Safety.skipInit
  rw [same.form]
  cases h : CIL.Safety.form n r with
  | error fault => exact .error fault
  | ok reference => exact .ok same

/-- No access condition changes: both implementations check exactly the same
    operation before either writes bytes or grants read authority. -/
theorem write_equivalent_alwaysPrepend (m : Memory) (r : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat) :
    ResultEquivalent Memory.Equivalent (write m r bytes alignment) (writeAlwaysPrepend m r bytes alignment) := by
  unfold write writeAlwaysPrepend
  cases ha : access m r bytes.length alignment true with
  | error fault => exact .error fault
  | ok value =>
    cases value
    apply ResultEquivalent.ok
    refine ⟨rfl, rfl, ?_, rfl, rfl⟩
    intro writing reference
    exact writeViews_permitted m r bytes.length writing reference

#print axioms write_equivalent_alwaysPrepend
end CIL.Safety
