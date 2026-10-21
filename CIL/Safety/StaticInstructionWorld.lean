import CIL.Safety.StaticInitialization

namespace CIL.Safety

set_option maxHeartbeats 800000

theorem write_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (r : Reference) (bytes : List (BitVec 8)) (alignment : Nat)
    (world : StaticWorldValid descriptors m) (h : write m r bytes alignment = .ok result) :
    StaticWorldValid descriptors result := by
  apply (write_preserves_immutable _ _ _ _ _ h).world descriptors world
  simp only [write] at h
  cases ha : access m r bytes.length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    rfl

theorem writeSnapshot_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (r : Reference) (bytes : List (BitVec 8 × Bool)) (alignment : Nat)
    (world : StaticWorldValid descriptors m) (h : writeSnapshot m r bytes alignment = .ok result) :
    StaticWorldValid descriptors result := by
  apply (writeSnapshot_preserves_immutable _ _ _ _ _ h).world descriptors world
  simp only [writeSnapshot, write] at h
  cases ha : access m r (bytes.map Prod.fst).length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h; rfl

theorem checked_write_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (r : Reference) (bytes : List (BitVec 8)) (alignment : Nat)
    (reference : ManagedReference) (width : Nat) (world : StaticWorldValid descriptors m)
    (h : checkedAt reference width (write m r bytes alignment) = .ok result) :
    StaticWorldValid descriptors result := by
  exact write_preserves_static_world _ _ _ _ _ _ world (checkedAt_ok h)

theorem InstructionEffect.staticWorld {m result : Memory} (effect : InstructionEffect m result)
    (descriptors : List CIL.StaticDescriptor) (world : StaticWorldValid descriptors m) :
    StaticWorldValid descriptors result := by
  cases effect with
  | unchanged => exact world
  | write h => exact write_preserves_static_world _ _ _ _ _ _ world h
  | snapshot h => exact writeSnapshot_preserves_static_world _ _ _ _ _ _ world h

theorem storeValue_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (reference : ManagedReference) (value : CIL.Value)
    (world : StaticWorldValid descriptors m) (h : storeValue m reference value = .ok result) :
    StaticWorldValid descriptors result := by
  exact (storeValue_effect _ _ _ _ h).staticWorld descriptors world

theorem memoryInstruction_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (operation : CIL.MemoryOp) (stack values : List Value) (m result : Memory)
    (world : StaticWorldValid descriptors m)
    (h : memoryInstruction operation stack m = .ok (result, values)) :
    StaticWorldValid descriptors result := by
  exact (memoryInstruction_effect _ _ _ _ _ h).staticWorld descriptors world

theorem instruction_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (operation : CIL.Op) (stack values : List Value) (m result : Memory)
    (world : StaticWorldValid descriptors m)
    (h : instruction operation stack m = .ok (result, values)) :
    StaticWorldValid descriptors result := by
  exact (instruction_effect _ _ _ _ _ h).staticWorld descriptors world

/-- Every site descriptor belongs to the selected extracted program's static
    world. Selection is independent of executing or proving a lookup. -/
def StaticSitesValid (descriptors : List CIL.StaticDescriptor) (body : CIL.Method) : Prop :=
  ∀ site ∈ body.staticSites, site.2 ∈ descriptors

theorem selected_static_site (descriptors : List CIL.StaticDescriptor) (body : CIL.Method)
    (pc site : Nat) (descriptor : CIL.StaticDescriptor) (sites : StaticSitesValid descriptors body)
    (found : body.staticSites.find? (fun site => site.1 == pc) = some (site, descriptor)) :
    descriptor ∈ descriptors := sites _ (List.mem_of_find?_eq_some found)

theorem StaticInstructionEffect.staticWorld {body : CIL.Method} {m result : Memory}
    (effect : StaticInstructionEffect body m result) (descriptors : List CIL.StaticDescriptor)
    (hm : m.WellFormed) (sites : StaticSitesValid descriptors body)
    (world : StaticWorldValid descriptors m) : StaticWorldValid descriptors result := by
  cases effect with
  | ordinary effect => exact effect.staticWorld descriptors world
  | reference selected h =>
    exact staticReference_preserves_static_world _ _ _ _ _ hm world
      (selected_static_site _ _ _ _ _ sites selected) h

theorem staticInstruction_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (body : CIL.Method) (pc : Nat) (operation : CIL.MemoryOp)
    (stack values : List Value) (m result : Memory) (hm : m.WellFormed)
    (sites : StaticSitesValid descriptors body) (world : StaticWorldValid descriptors m)
    (h : staticInstruction body pc operation stack m = .ok (result, values)) :
    StaticWorldValid descriptors result := by
  exact (staticInstruction_effect _ _ _ _ _ _ _ h).staticWorld descriptors hm sites world

#print axioms write_preserves_static_world
#print axioms memoryInstruction_preserves_static_world
#print axioms instruction_preserves_static_world
#print axioms staticInstruction_preserves_static_world

end CIL.Safety
