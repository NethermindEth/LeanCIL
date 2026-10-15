import CIL.Safety.AggregateHomeValues
import CIL.Safety.Execution

namespace CIL.Safety

/-- A private aggregate store changes only its bytes; older allocation metadata,
    bytes and authorities remain identical. The frame retains the same slots. -/
theorem step_store_aggregate {body : CIL.Method} {pc index watermark : Nat}
    {args rest : List Value} {frame : Frame} {memory : Memory} {reference : Reference}
    (size : Fin (2^64)) (bytes : List (BitVec 8)) (length : bytes.length = size)
    (slot : frame.locals[index]? = some (.bytes (.aggregate size) reference))
    (ready : access memory reference size 1 true = .ok ())
    (privateHome : watermark ≤ reference.allocation) :
    ∃ result,
      step body (.setLocal index) pc args frame (.scalar (.aggregate bytes) :: rest) memory =
        .ok (.next (pc + 1) rest frame result) ∧
      write memory reference bytes 1 = .ok result ∧
      read result reference size 1 = .ok bytes ∧
      loadLocal result (.bytes (.aggregate size) reference) = .ok (.scalar (.aggregate bytes)) ∧
      result.allocations = memory.allocations ∧
      MemoryBelow watermark memory result := by
  obtain ⟨result, written, stored, loaded, value, allocations⟩ := store_local_aggregate size bytes length ready
  have unchanged : frame.locals.set index (.bytes (.aggregate size) reference) = frame.locals := by
    apply List.ext_getElem?
    intro other
    by_cases same : index = other
    · subst other
      simp only [List.getElem?_set_self', slot]
      rfl
    · simp only [List.getElem?_set_ne same]
  refine ⟨result, ?_, written, loaded, value, allocations,
    write_preserves_memory_below _ _ _ _ _ _ privateHome written⟩
  simp only [step, slot, stored, unchanged, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem step_load_aggregate {body : CIL.Method} {pc index : Nat}
    {args stack : List Value} {frame : Frame} {memory : Memory} {reference : Reference}
    {size : Fin (2^64)} {bytes : List (BitVec 8)}
    (slot : frame.locals[index]? = some (.bytes (.aggregate size) reference))
    (loaded : read memory reference size 1 = .ok bytes) :
    step body (.local index) pc args frame stack memory =
      .ok (.next (pc + 1) (.scalar (.aggregate bytes) :: stack) frame memory) := by
  simp only [step, slot, load_local_aggregate_of_read loaded,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_store_aggregate
#print axioms step_load_aggregate
end CIL.Safety
