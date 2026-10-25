import CIL.Safety.ArgumentHomeValues
import CIL.Safety.ByteRoundTrip

/-!
# Aggregate homes

Loads, stores and allocation of by-value struct (`.aggregate`) storage. An aggregate home
holds the struct's bytes verbatim, with no SIMD encoding. These lemmas back the stepping
lemmas for aggregate locals and parameters in `AggregateLocals`.
-/

namespace CIL.Safety

/-- Aggregate homes store exactly the supplied bytes, without a SIMD encoding. -/
theorem load_local_aggregate_of_read {memory : Memory} {reference : Reference}
    {size : Fin (2^64)} {bytes : List (BitVec 8)}
    (loaded : read memory reference size 1 = .ok bytes) :
    loadLocal memory (.bytes (.aggregate size) reference) =
      .ok (.scalar (.aggregate bytes)) := by
  exact loadLocal_of_read (kind := .aggregate size) loaded

/-- Full-width checked aggregate stores need write access, not initialized bytes.
    The explicit write equation also exposes the exact footprint to callers. -/
theorem store_local_aggregate {memory : Memory} {reference : Reference}
    (size : Fin (2^64)) (bytes : List (BitVec 8)) (length : bytes.length = size)
    (ready : access memory reference size 1 true = .ok ()) :
    ∃ result,
      write memory reference bytes 1 = .ok result ∧
      storeLocal memory (.bytes (.aggregate size) reference) (.scalar (.aggregate bytes)) =
        .ok (.bytes (.aggregate size) reference, result) ∧
      read result reference size 1 = .ok bytes ∧
      loadLocal result (.bytes (.aggregate size) reference) = .ok (.scalar (.aggregate bytes)) ∧
      result.allocations = memory.allocations := by
  obtain ⟨result, written⟩ := write_succeeds (bytes := bytes) (by simpa only [length] using ready)
  have readback := write_readback _ _ _ _ _ written
  rw [length] at readback
  refine ⟨result, written, ?_, readback, load_local_aggregate_of_read readback,
    write_allocations _ _ _ _ _ written⟩
  have encoded : numberBytes (byteNumber bytes) size = bytes := by
    rw [← length, numberBytes_byteNumber]
  simp [storeLocal, Value.hasUnspecified, CIL.Value.hasUnspecified, localNumber, localWidth,
    length, encoded, written, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure,
    Except.pure]

/-- Fresh aggregate storage is initialized, readable and writable at its exact
    width, and preserves every older allocation, cell and permission. -/
theorem allocate_initialized_aggregate (memory : Memory) (activation : Nat)
    (size : Fin (2^64)) (bytes : List (BitVec 8)) (length : bytes.length = size)
    (wellFormed : memory.WellFormed) :
    ∃ reference allocated result,
      allocateHome memory activation size = .ok (reference, allocated) ∧
      storeLocal allocated (.bytes (.aggregate size) reference) (.scalar (.aggregate bytes)) =
        .ok (.bytes (.aggregate size) reference, result) ∧
      read result reference size 1 = .ok bytes ∧
      access result reference size 1 true = .ok () ∧
      MemoryBelow memory.nextIdentity memory result ∧
      reference.allocation = memory.nextIdentity := by
  obtain ⟨reference, allocated, home⟩ := allocateHome_succeeds (alignment := 1)
    memory activation size wellFormed size.isLt (by decide)
  have ready := allocateHome_write_access _ _ _ _ _ home
  obtain ⟨result, written, stored, loaded, _, _⟩ :=
    store_local_aggregate size bytes length ready.access
  have created : makeLocal activation (.aggregate size) (.aggregate bytes) memory =
      .ok (.bytes (.aggregate size) reference, [reference.allocation], result) := by
    simp [makeLocal, localWidth, localAlignment, home, stored,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨reference, allocated, result, home, stored, loaded,
    (ready.after_write written).access,
    makeLocal_preserves_caller_memory _ _ _ _ _ _ _ created,
    (allocateHome_fresh _ _ _ _ _ home).2.1⟩

/-- By-value aggregate parameters get private initialized copies of their actual
    bytes, using the emitted parameterHomes path rather than vector arguments. -/
theorem make_parameter_home_aggregate (memory : Memory) (activation index : Nat)
    (args : List Value) (size : Fin (2^64)) (bytes : List (BitVec 8))
    (length : bytes.length = size) (wellFormed : memory.WellFormed)
    (argument : args[index]? = some (.scalar (.aggregate bytes))) :
    ∃ reference result,
      makeParameterHomes activation [(index, .aggregate size)] args memory =
        .ok ([(index, .bytes (.aggregate size) reference)], [reference.allocation], result) ∧
      read result reference size 1 = .ok bytes ∧
      access result reference size 1 true = .ok () ∧
      MemoryBelow memory.nextIdentity memory result ∧
      reference.allocation = memory.nextIdentity := by
  obtain ⟨reference, allocated, result, home, stored, loaded, writable, preserved, fresh⟩ :=
    allocate_initialized_aggregate memory activation size bytes length wellFormed
  refine ⟨reference, result, ?_, loaded, writable, preserved, fresh⟩
  simp [makeParameterHomes, argument, makeLocal, localWidth, localAlignment, home, stored,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms store_local_aggregate
#print axioms allocate_initialized_aggregate
#print axioms make_parameter_home_aggregate
end CIL.Safety
