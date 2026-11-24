import Extracted
import CIL.Safety.StepComposition
import CIL.Safety.RuntimeExceptions

/-! The audited package entry on the .NET 11 Windows x64 runtime. -/
namespace ExampleProof
open CIL CIL.Safety CIL.Extraction

set_option maxRecDepth 65536
set_option maxHeartbeats 30000000

private def entry := (Extracted.translation_valid.entry .net11WinX64).getD (.translated [] [])
private def initial := entry.initialMemory.toOption.getD Safety.Memory.empty
private def caller := entry.methods[0]?.getD { code := [], locals := [], returnsValue := true }
private def frame : Safety.Frame := ⟨initial.nextIdentity, [], [], 0⟩

private theorem found : entry.methods[0]? = some caller := by cil_kernel_rfl

private theorem setupFrame :
    (fun (value : W32) (m : Safety.Memory) => enterFrame caller [.scalar (.i32 value)] m) =
    (fun _ m => .ok (⟨m.nextIdentity, [], [], 0⟩, m)) := by cil_kernel_rfl

private theorem loadArgumentZero :
    (fun (value : W32) (m : Safety.Memory) => Safety.step caller (.ldarg 0) 0 [.scalar (.i32 value)]
      ⟨m.nextIdentity, [], [], 0⟩ [] m) =
    (fun value m => .ok (.next 1 [.scalar (.i32 value)] ⟨m.nextIdentity, [], [], 0⟩ m)) := by
  cil_kernel_rfl

private theorem atComparison (program : Program) (lookup : program[0]? = some caller)
    (value : W32) (m : Safety.Memory) :
    invoke program 66 0 [.scalar (.i32 value)] m =
    run program 64 0 2 [.scalar (.i32 value)] ⟨m.nextIdentity, [], [], 0⟩
      [.scalar (.i32 100), .scalar (.i32 value)] m := by
  let args : List Safety.Value := [.scalar (.i32 value)]
  let activation : Safety.Frame := ⟨m.nextIdentity, [], [], 0⟩
  have checked : args.mapM (checkedValue m) = .ok args := rfl
  have setup : enterFrame caller args m = .ok (activation, m) := congrFun (congrFun setupFrame value) m
  change invoke program 66 0 args m = run program 64 0 2 args activation _ m
  simp only [invoke_eq, lookup, checked, setup, Except.mapError, Bind.bind, Except.bind]
  have load : Safety.step caller (.ldarg 0) 0 args activation [] m =
      .ok (.next 1 args activation m) := congrFun (congrFun loadArgumentZero value) m
  rw [run_next (fuel := 65) lookup (by cil_kernel_rfl) load]
  have constant : Safety.step caller (.ldc_i4 100) 1 args activation args m =
      .ok (.next 2 [.scalar (.i32 100), .scalar (.i32 value)] activation m) := by rfl
  exact run_next lookup (by cil_kernel_rfl) constant

private theorem comparison :
    (fun value : W32 => Safety.step caller (.ble_un 7) 2 [.scalar (.i32 value)] frame
      [.scalar (.i32 100), .scalar (.i32 value)] initial) =
    (fun value => .ok (.next (if value ≤ 100 then 7 else 3) [] frame initial)) := by cil_kernel_rfl

private theorem returning :
    (fun value : W32 => run entry.methods 63 0 7 [.scalar (.i32 value)] frame [] initial) =
    (fun value => .ok (initial, [.scalar (.i32 value)])) := by cil_kernel_rfl

private theorem raising :
    (fun value : W32 => run entry.methods 63 0 3 [.scalar (.i32 value)] frame [] initial) =
    (fun _ => .error ⟨0, 6, .thrown .argumentOutOfRange⟩) := by cil_kernel_rfl

/-- From empty caller storage, startup loads the original literals. Every in-range input
returns without changing that memory, and every larger input raises the range exception. -/
theorem managedContract :
    ∃ image memory, Extracted.translation_valid.entry .net11WinX64 = some image ∧
      image.initialMemory = .ok memory ∧
      ∀ value : W32, Extracted.translation_valid.invoke .net11WinX64 66 [.scalar (.i32 value)] =
        some (.ok (if value ≤ 100 then .ok (memory, [.scalar (.i32 value)])
          else .error ⟨0, 6, .thrown .argumentOutOfRange⟩)) := by
  have bound : Extracted.translation_valid.entry .net11WinX64 = some entry := by cil_kernel_rfl
  have loaded : entry.initialMemory = .ok initial := by cil_kernel_rfl
  refine ⟨entry, initial, bound, loaded, ?_⟩
  intro value
  simp only [TranslationValid.invoke, bound, Option.map_some, ProgramEntry.invoke, loaded, Except.map]
  apply congrArg (fun result => some (Except.ok result))
  rw [atComparison _ found value initial]
  change run entry.methods (63 + 1) 0 2 [.scalar (.i32 value)] frame
    [.scalar (.i32 100), .scalar (.i32 value)] initial = _
  rw [run_next (pc := 2) (fuel := 63) (body := caller) (op := .ble_un 7) found (by cil_kernel_rfl)
    (congrFun comparison value)]
  by_cases within : value ≤ 100
  · simpa only [ite_eq_left within] using congrFun returning value
  · simpa only [ite_eq_right within] using congrFun raising value
#print axioms managedContract

/-- The root CLR contract at the memory prepared by package startup. -/
def contract (loaded : Safety.Memory) : OutcomeContract W32 W32 where
  args value := [.scalar (.i32 value)]
  results result := [.scalar (.i32 result)]
  pre _ memory := memory = loaded
  footprint _ := []
  post value _ _ result := result = value
  raises value _ := if value ≤ 100 then none else some .argumentOutOfRange

/-- The public verifier's default theorem. The certificate supplies the methods and the loader
constructs the initial memory. The caller supplies neither runtime bodies nor message text. -/
theorem correctness :
    ∃ image memory, Extracted.translation_valid.entry .net11WinX64 = some image ∧
      image.initialMemory = .ok memory ∧ (contract memory).HoldsCLR image.methods 0 := by
  obtain ⟨image, memory, selected, loaded, runs⟩ := managedContract
  refine ⟨image, memory, selected, loaded, ?_⟩
  intro value initial permitted
  change initial = memory at permitted
  subst initial
  have actual := runs value
  simp only [TranslationValid.invoke, selected, Option.map_some, ProgramEntry.invoke, loaded,
    Except.map, Option.some.injEq, Except.ok.injEq] at actual
  by_cases within : value ≤ 100
  · simp only [contract, within, ite_true]
    rw [ite_eq_left within] at actual
    exact ⟨66, memory, _, actual, Confined.refl _ _, value, rfl, rfl⟩
  · simp only [contract, within, ite_false]
    rw [ite_eq_right within] at actual
    exact RaisesCLR.of_invoke actual rfl
#print axioms correctness

/-- The first out-of-range input through the public entry. -/
theorem managedException : Extracted.translation_valid.invoke .net11WinX64 66 [.scalar (.i32 101)] =
      some (.ok (.error ⟨0, 6, .thrown .argumentOutOfRange⟩)) := by
  obtain ⟨_, _, _, _, runs⟩ := managedContract
  simpa using runs 101
#print axioms managedException

/-- At an explicit zero quota, the allocation fails before the constructor can throw. -/
theorem zeroBudget :
    Extracted.translation_valid.invoke .net11WinX64 66 [.scalar (.i32 101)] (some 0) =
      some (.ok (.error ⟨0, 5, .allocationFailure 128 0⟩)) := by cil_kernel_rfl
#print axioms zeroBudget

end ExampleProof