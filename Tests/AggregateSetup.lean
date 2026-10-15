import CIL.Safety.ConstructSetup
import CIL.Safety.ConstructComposition
import CIL.Safety.AggregateLocals
import Examples.Support

namespace Tests.AggregateSetup
open CIL CIL.Safety

def constructor (size : Fin (2^64)) : CIL.Program := [
  { code := [.newAggregate 1 0 size, .ret], locals := [], returnsValue := true },
  { code := [.ret], locals := [], returnsValue := false }]

/-- The existing generic constructor composition API consumes aggregate setup
    and load lemmas directly, with no vector-specific result representation. -/
theorem composed_constructor (size : Fin (2^64)) (positive : 0 < size.val)
    (memory : CIL.Safety.Memory) (wf : memory.WellFormed) (frame : Frame)
    (child : ∀ temporary updated,
      step ((constructor size)[0]'(by simp [constructor])) (.newAggregate 1 0 size) 0 [] frame [] memory =
        .ok (.construct 1 [.reference (.address temporary)] []
          { frame with owned := temporary.allocation :: frame.owned } temporary (.aggregate size) updated) →
      invoke (constructor size) 4 1 [.reference (.address temporary)] updated = .ok (updated, []))
    (continuation : ∀ temporary updated,
      read updated temporary size 1 = .ok (List.replicate size 0) →
      run (constructor size) 4 0 1 []
        { frame with owned := temporary.allocation :: frame.owned }
        [.scalar (.aggregate (List.replicate size 0))] updated =
        .ok (leaveFrame { frame with owned := temporary.allocation :: frame.owned } updated,
          [.scalar (.aggregate (List.replicate size 0))])) :
    ∃ (temporary : Reference) (updated : CIL.Safety.Memory),
      run (constructor size) 5 0 0 [] frame [] memory =
        .ok (leaveFrame { frame with owned := temporary.allocation :: frame.owned } updated,
          [.scalar (.aggregate (List.replicate size 0))]) ∧
      MemoryBelow memory.nextIdentity memory updated := by
  obtain ⟨temporary, updated, stepped, loaded, _, preserved, _⟩ :=
    step_newAggregate (body := ((constructor size)[0]'(by simp [constructor]))) (pc := 0) (callee := 1)
      size positive [] [] [] frame memory wf rfl
  refine ⟨temporary, updated, ?_, preserved⟩
  exact run_construct_of_invoke (body := ((constructor size)[0]'(by simp [constructor]))) rfl rfl stepped
    (child temporary updated stepped) (load_local_aggregate_of_read loaded)
    (continuation temporary updated loaded)

def initial : CIL.Safety.Memory := Examples.empty

-- Packed/non-word width and the 32-byte consumer width both execute complete
-- constructor invocation, including fresh-frame expiration and value readback.
theorem packed_constructor :
    (invoke (constructor 5) 8 0 [] initial).map Prod.snd =
      .ok [.scalar (.aggregate [0, 0, 0, 0, 0])] := rfl

theorem wide_constructor :
    (invoke (constructor 32) 8 0 [] initial).map Prod.snd =
      .ok [.scalar (.aggregate (List.replicate 32 0))] := rfl

theorem zero_constructor_rejected :
    invoke (constructor 0) 8 0 [] initial = .error ⟨0, 0, .invalidState⟩ := rfl

theorem wrong_size_rejected (memory : CIL.Safety.Memory) (reference : Reference) :
    storeLocal memory (.bytes (.aggregate 5) reference) (.scalar (.aggregate [1, 2])) =
      .error .invalidState := rfl

/-- All byte patterns at all representable widths are copied into a fresh
    by-value parameter home and can be loaded back without changing old memory. -/
theorem copied_parameter (size : Fin (2^64)) (bytes : List (BitVec 8))
    (length : bytes.length = size) (memory : CIL.Safety.Memory) (wf : memory.WellFormed) :
    ∃ reference result,
      makeParameterHomes 7 [(0, .aggregate size)] [.scalar (.aggregate bytes)] memory =
        .ok ([(0, .bytes (.aggregate size) reference)], [reference.allocation], result) ∧
      loadLocal result (.bytes (.aggregate size) reference) = .ok (.scalar (.aggregate bytes)) ∧
      MemoryBelow memory.nextIdentity memory result := by
  obtain ⟨reference, result, setup, loaded, _, preserved, _⟩ :=
    make_parameter_home_aggregate memory 7 0 [.scalar (.aggregate bytes)] size bytes length wf rfl
  exact ⟨reference, result, setup, load_local_aggregate_of_read loaded, preserved⟩

/-- Store and subsequent load compose at any slot and width while preserving
    the caller's memory, not only the initialized constructor example. -/
theorem private_store_load {body : CIL.Method} {frame : Frame}
    {memory : CIL.Safety.Memory} {reference : Reference} (size : Fin (2^64))
    (bytes : List (BitVec 8)) (length : bytes.length = size) (index watermark : Nat)
    (slot : frame.locals[index]? = some (.bytes (.aggregate size) reference))
    (ready : access memory reference size 1 true = .ok ())
    (fresh : watermark ≤ reference.allocation) :
    ∃ result,
      step body (.setLocal index) 0 [] frame [.scalar (.aggregate bytes)] memory =
        .ok (.next 1 [] frame result) ∧
      step body (.local index) 1 [] frame [] result =
        .ok (.next 2 [.scalar (.aggregate bytes)] frame result) ∧
      MemoryBelow watermark memory result := by
  obtain ⟨result, stored, _, loaded, _, _, preserved⟩ :=
    step_store_aggregate (body := body) (pc := 0) (args := []) (rest := [])
      size bytes length slot ready fresh
  exact ⟨result, stored, step_load_aggregate slot loaded, preserved⟩

#print axioms composed_constructor
#print axioms packed_constructor
#print axioms wide_constructor
#print axioms zero_constructor_rejected
#print axioms wrong_size_rejected
#print axioms copied_parameter
#print axioms private_store_load
end Tests.AggregateSetup
