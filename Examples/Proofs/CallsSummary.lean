import Extracted
import CIL
import CIL.MethodIdentity
import CIL.Safety.LoopScaffold

/-!
# A call chain through decoded summaries

`Examples.Arithmetic::Calls` stores `Increment(x)` in a local, passes the local by reference to
`Mutate`, which adds two through it, and returns the local. `correctness_stepped` steps the
caller and both callees instruction by instruction. `correctness` proves the same statement from
a `DecodedSummary` of each callee, bound to the record whose pinned bytes decode to it, without
stepping either body.
-/

namespace ExampleProof
open CIL CIL.Safety CIL.Extraction

bind_entry entry (memory : Safety.Memory) (x : W64) (wellFormed : memory.WellFormed) :=
  Extracted.method0 with [.scalar (.i64 x)] from memory allocating wellFormed
bind_method increment incrementBody := "System.UInt64 Examples.Arithmetic::Increment(System.UInt64)"
bind_method mutate mutateBody := "System.Void Examples.Arithmetic::Mutate(System.UInt64&)"

/-- The caller returns `x + 3` and keeps all memory below its entry, stepping both callees. -/
theorem correctness_stepped (memory : Safety.Memory) (x : W64) (wellFormed : memory.WellFormed) :
    WP (Execution (fun fuel => invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory))
      (fun (final, values) => values = [.scalar (.i64 (x + 3))] ∧
        MemoryBelow memory.nextIdentity memory final) := by
  obtain ⟨reference, entered, enter⟩ := entry.checked memory x wellFormed
  have ready := enter.numeric0.writable
  obtain ⟨first, firstWrite, firstStore, firstRead, -⟩ := store_local_word64 (x + 1) ready
  have readyAfter := snapshot_access_after_write ready firstWrite
  obtain ⟨second, secondWrite, secondStore, secondRead⟩ := store_word64 (x + 3) readyAfter
  rw [← show x + 1 + 2#64 = x + 3 by bv_omega] at secondStore
  have below := MemoryBelow.frame_round_trip enter.setup
    ((write_preserves_memory_below _ _ _ _ _ _ enter.numeric0.fresh firstWrite).trans
      (write_preserves_memory_below _ _ _ _ _ _ enter.numeric0.fresh secondWrite))
  suffices ran : ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory =
      .ok (leaveFrame (entry.frame memory reference) second, [.scalar (.i64 (x + 3))]) by
    obtain ⟨fuel, ran⟩ := ran
    exact WP.adequate.mpr ⟨fuel, _, _, ran, rfl, below⟩
  cil_checked_steps [enter.setup, entry.frame, firstStore, firstRead, secondStore,
    load_local_word64_of_read secondRead, localAddress, access_reference_valid _ _ _ _ _ ready,
    access_reference_valid _ _ _ _ _ readyAfter,
    checkedValue_address _ _ (access_reference_valid _ _ _ _ _ readyAfter), numericOfWidth]
#print axioms correctness_stepped

/-- `Increment` returns its argument plus one and changes no memory. -/
def incrementContract : MethodContract W64 W64 where
  args x := [.scalar (.i64 x)]
  results value := [.scalar (.i64 value)]
  pre _ _ := True
  footprint _ := []
  post x initial final value := value = x + 1 ∧ final = initial

/-- `Mutate` adds two to the word its argument names and writes nothing else. -/
def mutateContract : MethodContract (Reference × W64) Unit where
  args := fun (place, _) => [.reference (.address place)]
  results _ := []
  pre := fun (place, old) memory => access memory place 8 1 true = .ok () ∧
    read memory place 8 1 = .ok (numberBytes old.toNat 8)
  footprint := fun (place, _) => [(place, 8)]
  post := fun (place, old) _ final _ =>
    read final place 8 1 = .ok (numberBytes (old + 2).toNat 8)

/-- `Increment` meets its contract. -/
theorem increment_holds : incrementContract.Holds Extracted.program increment := by
  rintro x memory -
  refine MethodContract.Holds.intro memory (x + 1) ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
  cil_checked_steps
#print axioms increment_holds

/-- `Mutate` meets its contract. -/
theorem mutate_holds : mutateContract.Holds Extracted.program mutate := by
  rintro ⟨place, old⟩ memory ⟨ready, loaded⟩
  obtain ⟨final, written, stored, readback⟩ := store_word64 (old + 2) ready
  refine MethodContract.Holds.intro final () ?_
    (Confined.write written (by simp [mutateContract])) readback
  cil_checked_steps [loaded, stored, access_reference_valid _ _ _ _ _ ready,
    checkedValue_address _ _ (access_reference_valid _ _ _ _ _ ready)]
#print axioms mutate_holds

/-- Every record's pinned bytes decode to the method at its index of the extraction. -/
theorem bodies_decode :
    decodedProgram? Extracted.profile Extracted.environment Extracted.methodEvidence =
      some Extracted.program :=
  decodedProgram?_eq_some
    (.cons ((Method.ofBody?_of_decodes Extracted.method0_body_validated).trans
        Extracted.method0_decoded)
      (.cons ((Method.ofBody?_of_decodes Extracted.method1_body_validated).trans
          Extracted.method1_decoded)
        (.cons ((Method.ofBody?_of_decodes Extracted.method2_body_validated).trans
            Extracted.method2_decoded) .nil)))
#print axioms bodies_decode

/-- The contract of `Increment`, bound to its record and the bytes it decodes from. -/
theorem increment_summary : ∃ record, Extracted.methodEvidence[increment]? = some record ∧
    DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment increment record.assembly record.original.token record.arguments
      incrementContract :=
  ⟨_, rfl, .of_decoded bodies_decode rfl Extracted.method2_specialization_validated.1
    increment_holds⟩
#print axioms increment_summary

/-- The contract of `Mutate`, bound to its record and the bytes it decodes from. -/
theorem mutate_summary : ∃ record, Extracted.methodEvidence[mutate]? = some record ∧
    DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment mutate record.assembly record.original.token record.arguments
      mutateContract :=
  ⟨_, rfl, .of_decoded bodies_decode rfl Extracted.method1_specialization_validated.1
    mutate_holds⟩
#print axioms mutate_summary

/-- The caller returns `x + 3` and keeps all memory below its entry, applying each callee's
    summary at its call. -/
theorem correctness (memory : Safety.Memory) (x : W64) (wellFormed : memory.WellFormed) :
    WP (Execution (fun fuel => invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory))
      (fun (final, values) => values = [.scalar (.i64 (x + 3))] ∧
        MemoryBelow memory.nextIdentity memory final) := by
  obtain ⟨incrementRecord, -, incrementSummary⟩ := increment_summary
  obtain ⟨mutateRecord, -, mutateSummary⟩ := mutate_summary
  obtain ⟨reference, entered, enter⟩ := entry.checked memory x wellFormed
  apply WP.enter (by rfl) (by rfl) enter.setup
  cil_contract_steps [incrementSummary.holds, incrementContract, entry.frame]
    with middle value incremented
  obtain ⟨rfl, rfl⟩ := incremented.post
  obtain ⟨stored, store, frame, -⟩ := (enter.frame []).store 0 (.i64 (x + 1)) rfl
  have permitted : mutateContract.pre (reference, x + 1) stored := by
    obtain ⟨value, number, fits, result, loaded⟩ := frame.snapshots.read_at (index := 0) rfl rfl
    refine ⟨frame.homes.writable_at (kind := .word64) (home := reference) (index := 0) rfl, ?_⟩
    cases value <;> simp [localNumber, localResult, CIL.Value.hasUnspecified] at fits result
    subst fits result
    exact loaded
  cil_contract_steps [store, localAddress, frame.form_home 0]
  apply WP.exists_execution
  apply WP.local_call frame mutateSummary.holds (reference, x + 1) (by rfl) (by rfl)
    (by cil_checked_step [localAddress, frame.form_home 0]) permitted 0 .word64 reference rfl rfl
    (fun _ => .i64 (x + 3)) (fun _ => (x + 3).toNat) (fun _ => rfl)
    (fun _ _ post => by rw [← show x + 1 + 2 = x + 3 by bv_omega]; exact post)
  intro final values mutated updated
  have loaded := updated.snapshots.load (index := 0) (.i64 (x + 3)) rfl
    (body := Extracted.method0) (pc := 5) (args := [.scalar (.i64 x)]) (stack := [])
  cil_contract_steps [loaded]
  exact ⟨rfl, updated.leave_kept enter.setup _ rfl⟩
#print axioms correctness

end ExampleProof
