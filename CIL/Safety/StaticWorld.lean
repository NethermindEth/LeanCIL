import CIL.Safety.StaticMemoryLemmas

/-!
# Static worlds

`StaticWorldValid descriptors m` says the readonly statics a program may load are
consistent with the memory's static registry: identities are unique, every registered
binding is a live immutable-static allocation, and a cached binding holds exactly the
descriptor's bytes. Under it `staticReference` never fails, which is what lets contracts
step over static loads without a fault case.
-/

namespace CIL.Safety

/-- Loaded readonly field storage, described independently of executing a lookup. -/
def StaticBindingValid (m : Memory) (descriptor : CIL.StaticDescriptor) (reference : Reference) :
    Prop :=
  reference.offset = 0 ∧ ∃ allocation,
    m.allocations reference.allocation = some allocation ∧ allocation.live = true ∧
    allocation.kind = .immutableStatic ∧ allocation.layout.size = descriptor.bytes.length ∧
    read m reference descriptor.bytes.length 1 = .ok descriptor.bytes

/-- The static registry binds each identity once, to distinct allocations that are all live
    immutable statics. -/
def StaticRegistryValid (m : Memory) : Prop :=
  m.staticBindings.Pairwise (fun left right =>
    left.1 ≠ right.1 ∧ left.2.allocation ≠ right.2.allocation) ∧
  ∀ binding ∈ m.staticBindings, ∃ allocation,
    m.allocations binding.2.allocation = some allocation ∧
      allocation.live = true ∧ allocation.kind = .immutableStatic

/-- The descriptors fit native sizes and have unique identities, the registry is valid, and
    every registered binding for a descriptor holds that descriptor's bytes. -/
def StaticWorldValid (descriptors : List CIL.StaticDescriptor) (m : Memory) : Prop :=
  (∀ descriptor ∈ descriptors, descriptor.bytes.length < nativeLimit) ∧
  (∀ left ∈ descriptors, ∀ right ∈ descriptors,
    left.identity = right.identity → left = right) ∧
  StaticRegistryValid m ∧
  ∀ descriptor ∈ descriptors, ∀ binding ∈ m.staticBindings,
    descriptor.identity = binding.1 → StaticBindingValid m descriptor binding.2

/-- A cached binding that is valid for the descriptor is returned without allocating. -/
theorem cached_static_reference_succeeds (m : Memory) (descriptor : CIL.StaticDescriptor)
    (key : Nat) (reference : Reference)
    (cache : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) =
      some (key, reference))
    (valid : StaticBindingValid m descriptor reference) :
    staticReference descriptor m = .ok (m, reference) := by
  obtain ⟨offset, allocation, present, live, kind, size, bytes⟩ := valid
  simp [staticReference, cache, checkedAt, liveAllocation, present, live, kind, offset, size,
    bytes, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem wellFormed_next_unused (m : Memory) (hm : m.WellFormed) :
    m.allocations m.nextIdentity = none := by
  cases h : m.allocations m.nextIdentity with
  | none => rfl
  | some allocation =>
    have bad := (hm.1 m.nextIdentity allocation h).1
    exact False.elim (Nat.lt_irrefl _ bad)

/-- In a valid static world, loading any of its descriptors succeeds: from the cache if bound,
    otherwise by allocating a fresh immutable static. -/
theorem staticReference_succeeds (m : Memory) (descriptor : CIL.StaticDescriptor)
    (descriptors : List CIL.StaticDescriptor) (hm : m.WellFormed)
    (world : StaticWorldValid descriptors m) (member : descriptor ∈ descriptors) :
    ∃ result reference, staticReference descriptor m = .ok (result, reference) := by
  cases hc : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    have bindingMember : binding ∈ m.staticBindings := List.mem_of_find?_eq_some hc
    have found : binding.1 = descriptor.identity := by
      have matched := List.find?_some hc
      simpa using matched
    have valid := world.2.2.2 descriptor member binding bindingMember found.symm
    exact ⟨m, binding.2, cached_static_reference_succeeds _ _ _ _ hc valid⟩
  | none =>
    have unused := wellFormed_next_unused m hm
    have size := world.1 descriptor member
    have valid : (Allocation.mk .immutableStatic ⟨descriptor.bytes.length, 1, []⟩
        true [descriptor.bytes.length]).valid = true := by
      simp [Allocation.valid, size]
    simp only [staticReference, hc, allocate, valid, Bool.not_true, Bool.false_eq_true,
      ite_false, unused, Option.isSome_none, checkedAt, Except.mapError, Bind.bind,
      Except.bind, Pure.pure, Except.pure]
    exact ⟨_, _, rfl⟩

#print axioms cached_static_reference_succeeds
#print axioms staticReference_succeeds

theorem empty_static_world_valid (descriptors : List CIL.StaticDescriptor) (m : Memory)
    (sizes : ∀ descriptor ∈ descriptors, descriptor.bytes.length < nativeLimit)
    (identities : ∀ left ∈ descriptors, ∀ right ∈ descriptors,
      left.identity = right.identity → left = right)
    (empty : m.staticBindings = []) : StaticWorldValid descriptors m := by
  refine ⟨sizes, identities, ?_, ?_⟩
  · constructor <;> simp [empty]
  · simp [empty]

theorem static_registry_fields_live (descriptors : List CIL.StaticDescriptor) (m : Memory)
    (world : StaticWorldValid descriptors m) (binding : Nat × Reference)
    (member : binding ∈ m.staticBindings) :
    ∃ allocation, m.allocations binding.2.allocation = some allocation ∧
      allocation.live = true ∧ allocation.kind = .immutableStatic := by
  exact world.2.2.1.2 binding member

/-- None of `identities` is bound in the static registry yet. -/
def StaticIdentitiesAbsent (identities : List Nat) (m : Memory) : Prop :=
  ∀ binding ∈ m.staticBindings, binding.1 ∉ identities

/-- A valid registry with none of the descriptors bound yet gives a valid static world. -/
theorem StaticWorldValid.of_absent (descriptors : List CIL.StaticDescriptor) (m : Memory)
    (sizes : ∀ descriptor ∈ descriptors, descriptor.bytes.length < nativeLimit)
    (identities : ∀ left ∈ descriptors, ∀ right ∈ descriptors,
      left.identity = right.identity → left = right)
    (registry : StaticRegistryValid m)
    (absent : StaticIdentitiesAbsent (descriptors.map CIL.StaticDescriptor.identity) m) :
    StaticWorldValid descriptors m := by
  refine ⟨sizes, identities, registry, ?_⟩
  intro descriptor selected binding member same
  exact False.elim (absent binding member (same ▸ List.mem_map.mpr ⟨descriptor, selected, rfl⟩))

theorem StaticWorldValid.mono {descriptors selected : List CIL.StaticDescriptor} {m : Memory}
    (world : StaticWorldValid descriptors m) (subset : selected ⊆ descriptors) :
    StaticWorldValid selected m :=
  ⟨fun descriptor member => world.1 descriptor (subset member),
    fun left hl right hr => world.2.1 left (subset hl) right (subset hr),
    world.2.2.1, fun descriptor member => world.2.2.2 descriptor (subset member)⟩

theorem StaticWorldValid.append {left right : List CIL.StaticDescriptor} {m : Memory}
    (first : StaticWorldValid left m) (second : StaticWorldValid right m)
    (compatible : ∀ a ∈ left, ∀ b ∈ right, a.identity = b.identity → a = b) :
    StaticWorldValid (left ++ right) m := by
  refine ⟨?_, ?_, first.2.2.1, ?_⟩
  · intro descriptor member
    rcases List.mem_append.mp member with member | member
    · exact first.1 descriptor member
    · exact second.1 descriptor member
  · intro a ha b hb same
    rcases List.mem_append.mp ha with ha | ha <;>
      rcases List.mem_append.mp hb with hb | hb
    · exact first.2.1 a ha b hb same
    · exact compatible a ha b hb same
    · exact (compatible b hb a ha same.symm).symm
    · exact second.2.1 a ha b hb same
  · intro descriptor member
    rcases List.mem_append.mp member with member | member
    · exact first.2.2.2 descriptor member
    · exact second.2.2.2 descriptor member

theorem StaticWorldValid.left {left right : List CIL.StaticDescriptor} {m : Memory}
    (world : StaticWorldValid (left ++ right) m) : StaticWorldValid left m :=
  world.mono (fun _ member => List.mem_append_left _ member)

theorem StaticWorldValid.right {left right : List CIL.StaticDescriptor} {m : Memory}
    (world : StaticWorldValid (left ++ right) m) : StaticWorldValid right m :=
  world.mono (fun _ member => List.mem_append_right _ member)

#print axioms empty_static_world_valid
#print axioms static_registry_fields_live
#print axioms StaticWorldValid.of_absent
#print axioms StaticWorldValid.mono
#print axioms StaticWorldValid.append
#print axioms StaticWorldValid.left
#print axioms StaticWorldValid.right
end CIL.Safety
