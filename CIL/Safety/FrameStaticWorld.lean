import CIL.Safety.StaticInstructionWorld
import CIL.Safety.FrameSetupLemmas

namespace CIL.Safety

/-- Setup preserves every existing static binding because it only touches fresh
    homes and retains the registry. No traversal-specific static proof is needed. -/
theorem FrameSetup.staticWorld {activation : Nat} {before after : Memory}
    {slots : List LocalSlot} {owned : List AllocationId}
    (setup : FrameSetup activation before after slots owned) (descriptors : List CIL.StaticDescriptor)
    (hm : before.WellFormed) (world : StaticWorldValid descriptors before) :
    StaticWorldValid descriptors after := by
  apply PreservesImmutable.world (m := before) (result := after) ?_ descriptors world setup.registry
  intro id a present _
  have old := (hm.1 id a present).1
  exact ⟨(setup.below.allocations id old).trans present, setup.below.cells id old,
    fun offset => setup.below.permissions id old offset false⟩


theorem allocateHome_preserves_static_world {alignment : Nat} (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (activation width : Nat) (r : Reference) (hm : m.WellFormed)
    (world : StaticWorldValid descriptors m)
    (h : allocateHome m activation width alignment = .ok (r, result)) : StaticWorldValid descriptors result := by
  exact (allocateHome_setup _ _ _ _ _ .byte h).staticWorld descriptors hm world

theorem storeLocal_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (slot final : LocalSlot) (value : Value)
    (world : StaticWorldValid descriptors m)
    (h : storeLocal m slot value = .ok (final, result)) : StaticWorldValid descriptors result := by
  unfold storeLocal at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact world
      | solve | exact writeSnapshot_preserves_static_world _ _ _ _ _ _ world (checkedAt_ok (by assumption))
      | solve | apply checked_write_preserves_static_world _ _ _ _ _ _ _ _ world; assumption
      | cases h
      | split at h

theorem makeLocal_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (activation : Nat) (kind : CIL.LocalKind) (initial : CIL.Value)
    (slot : LocalSlot) (owned : List AllocationId) (hm : m.WellFormed)
    (world : StaticWorldValid descriptors m)
    (h : makeLocal activation kind initial m = .ok (slot, owned, result)) :
    StaticWorldValid descriptors result := by
  exact (makeLocal_setup _ _ _ _ _ _ _ h).staticWorld descriptors hm world

theorem makeLocals_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (activation : Nat) (kinds : List CIL.LocalKind)
    (initializers : List CIL.Value) (slots : List LocalSlot) (owned : List AllocationId)
    (hm : m.WellFormed) (world : StaticWorldValid descriptors m)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    StaticWorldValid descriptors result := by
  exact (makeLocals_setup _ _ _ _ _ _ _ h).staticWorld descriptors hm world

theorem makeArgumentHomes_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (activation : Nat) (indices : List Nat) (args : List Value)
    (homes : List (Nat × LocalSlot)) (owned : List AllocationId) (hm : m.WellFormed)
    (world : StaticWorldValid descriptors m)
    (h : makeArgumentHomes activation indices args m = .ok (homes, owned, result)) :
    StaticWorldValid descriptors result := by
  exact (makeArgumentHomes_setup _ _ _ _ _ _ _ h).staticWorld descriptors hm world

theorem makeParameterHomes_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m result : Memory) (activation : Nat) (parameters : List (Nat × CIL.LocalKind))
    (args : List Value) (homes : List (Nat × LocalSlot)) (owned : List AllocationId)
    (hm : m.WellFormed) (world : StaticWorldValid descriptors m)
    (h : makeParameterHomes activation parameters args m = .ok (homes, owned, result)) :
    StaticWorldValid descriptors result := by
  exact (makeParameterHomes_setup _ _ _ _ _ _ _ h).staticWorld descriptors hm world

theorem enterFrame_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (body : CIL.Method) (args : List Value) (m result : Memory) (frame : Frame)
    (hm : m.WellFormed) (world : StaticWorldValid descriptors m)
    (h : enterFrame body args m = .ok (frame, result)) : StaticWorldValid descriptors result := by
  exact (enterFrame_setup _ _ _ _ _ h).staticWorld descriptors hm world

#print axioms allocateHome_preserves_static_world
#print axioms storeLocal_preserves_static_world
#print axioms enterFrame_preserves_static_world

end CIL.Safety
