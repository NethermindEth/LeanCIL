import Extracted
import CIL.Safety.StepComposition
import CIL.Runtime.EntryContract

/-! The audited package entry on the .NET 11 Windows x64 runtime. -/
namespace ExampleProof
open CIL CIL.Safety CIL.Extraction

set_option maxRecDepth 65536
set_option maxHeartbeats 30000000

private def package := Extracted.managedPackage.get (by cil_kernel_rfl)
private def entry := ProgramEntry.range package
private def initial := entry.initialMemory.toOption.getD Safety.Memory.empty
private def caller := entry.methods[0]?.getD { code := [], locals := [], returnsValue := true }

private theorem found :
    (fun extra : Program => (entry.methods ++ extra)[0]?) = fun _ => some caller := by cil_kernel_rfl
#print axioms found

private theorem setupFrame :
    (fun (value : W32) (m : Safety.Memory) => enterFrame caller [.scalar (.i32 value)] m) =
    (fun _ m => .ok (⟨m.nextIdentity, [], [], 0⟩, m)) := by cil_kernel_rfl
#print axioms setupFrame

private theorem loadArgumentZero :
    (fun (value : W32) (m : Safety.Memory) => Safety.step caller (.ldarg 0) 0 [.scalar (.i32 value)]
      ⟨m.nextIdentity, [], [], 0⟩ [] m) =
    (fun value m => .ok (.next 1 [.scalar (.i32 value)] ⟨m.nextIdentity, [], [], 0⟩ m)) := by
  cil_kernel_rfl
#print axioms loadArgumentZero

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
  have load : Safety.step caller (.ldarg 0) 0 args activation [] m =
      .ok (.next 1 args activation m) := congrFun (congrFun loadArgumentZero value) m
  have constant : Safety.step caller (.ldc_i4 100) 1 args activation args m =
      .ok (.next 2 [.scalar (.i32 100), .scalar (.i32 value)] activation m) := by rfl
  have steps := (run_next (fuel := 65) lookup (by cil_kernel_rfl) load).trans
    (run_next lookup (by cil_kernel_rfl) constant)
  cases outcome : run program 64 0 2 args activation [.scalar (.i32 100), .scalar (.i32 value)] m with
  | ok pair =>
    obtain ⟨final, values⟩ := pair
    exact invoke_of_run lookup checked setup (steps.trans outcome)
  | error fault => exact invoke_of_run_fault lookup checked setup (steps.trans outcome)
#print axioms atComparison

private def callerFrame (memory : Safety.Memory) : Safety.Frame := ⟨memory.nextIdentity, [], [], 0⟩

private theorem comparison :
    (fun (value : W32) (memory : Safety.Memory) =>
      Safety.step caller (.ble_un 7) 2 [.scalar (.i32 value)] (callerFrame memory)
        [.scalar (.i32 100), .scalar (.i32 value)] memory) =
    (fun value memory => .ok (.next (if value ≤ 100 then 7 else 3) [] (callerFrame memory) memory)) :=
  by cil_kernel_rfl
#print axioms comparison

private theorem returning :
    (fun (extra : Program) (v : W32) (memory : Safety.Memory) =>
      run (entry.methods ++ extra) 63 0 7 [.scalar (.i32 v)] (callerFrame memory) [] memory) =
    (fun _ v memory => .ok (memory, [.scalar (.i32 v)])) := by cil_kernel_rfl
#print axioms returning

/-- The public program returns an in-range value with exactly the caller's original memory. -/
theorem inRangeFromCallerMemory (value : W32) (within : value ≤ 100) (memory : Safety.Memory) :
    invoke Extracted.program 66 0 [.scalar (.i32 value)] memory =
      .ok (memory, [.scalar (.i32 value)]) := by
  have root : Extracted.program[0]? = some caller := by cil_kernel_rfl
  rw [atComparison _ root value memory]
  have branch := congrFun (congrFun comparison value) memory
  rw [ite_eq_left within] at branch
  change run Extracted.program (63 + 1) 0 2 _ (callerFrame memory) _ memory = _
  rw [run_next root (by cil_kernel_rfl) branch]
  have same : entry.methods = Extracted.program := by cil_kernel_rfl
  simpa only [List.append_nil, same] using congrFun (congrFun (congrFun returning []) value) memory
#print axioms inRangeFromCallerMemory

private theorem raising :
    (fun (extra : Program) (v : W32) =>
      run (entry.methods ++ extra) 63 0 3 [.scalar (.i32 v)] (callerFrame initial) [] initial) =
    (fun _ _ => .error ⟨0, 6, .thrown .argumentOutOfRange⟩) := by cil_kernel_rfl
#print axioms raising

/-- Both branches stay in the bound methods for every input. Any implementation of
the remaining resource getter gives the same return or located range exception. -/
theorem independentOfResource :
    ∃ body memory, Extracted.managedPackage = some body ∧
      body.checked Extracted.environment Extracted.assemblies
        Extracted.platformDefinitions = true ∧
      (ProgramEntry.range body).initialMemory = .ok memory ∧ ∀ (extra : Program) (value : W32),
        invoke (body.methods ++ extra) 66 0 [.scalar (.i32 value)] memory =
          if value ≤ 100 then .ok (memory, [.scalar (.i32 value)])
          else .error ⟨0, 6, .thrown .argumentOutOfRange⟩ := by
  refine ⟨package, initial, by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl, ?_⟩
  intro extra value
  change invoke (entry.methods ++ extra) 66 0 [.scalar (.i32 value)] initial = _
  have root := congrFun found extra
  rw [atComparison _ root value initial]
  change run (entry.methods ++ extra) (63 + 1) 0 2 [.scalar (.i32 value)] (callerFrame initial)
    [.scalar (.i32 100), .scalar (.i32 value)] initial = _
  rw [run_next root (by cil_kernel_rfl) (congrFun (congrFun comparison value) initial)]
  by_cases within : value ≤ 100
  · simpa only [within, ite_true] using congrFun (congrFun (congrFun returning extra) value) initial
  · simpa only [within, ite_false] using congrFun (congrFun raising extra) value
#print axioms independentOfResource

/-- The public package entry selects the same validated definitions as the physical source. -/
private theorem certifiedEntry {body : ManagedPackage}
    (source : Extracted.managedPackage = some body) :
    Extracted.translation_valid.entry .net11WinX64 = some (.range body) := by
  have selected : Extracted.managedPackage = some package := by cil_kernel_rfl
  cases Option.some.inj (selected.symm.trans source)
  cil_kernel_rfl
#print axioms certifiedEntry

/-- From empty caller storage, startup loads the original literals. Every in-range input
returns without changing that memory, and every larger input raises the range exception. -/
theorem managedContract :
    ∃ image memory, Extracted.translation_valid.entry .net11WinX64 = some image ∧
      image.initialMemory = .ok memory ∧
      ∀ value : W32, Extracted.translation_valid.invoke .net11WinX64 66 [.scalar (.i32 value)] =
        some (.ok (if value ≤ 100 then .ok (memory, [.scalar (.i32 value)])
          else .error ⟨0, 6, .thrown .argumentOutOfRange⟩)) := by
  obtain ⟨body, memory, source, _, loaded, runs⟩ := independentOfResource
  have bound := certifiedEntry source
  refine ⟨.range body, memory, bound, loaded, ?_⟩
  intro value
  simp only [TranslationValid.invoke, bound, Option.map_some, ProgramEntry.invoke, loaded, Except.map]
  apply congrArg (fun result => some (Except.ok result))
  simpa only [ProgramEntry.methods, List.append_nil] using runs [] value
#print axioms managedContract

/-- The root CLR contract at the memory prepared by package startup. -/
def contract : OutcomeContract W32 W32 where
  args value := [.scalar (.i32 value)]
  results result := [.scalar (.i32 result)]
  pre _ _ := True
  footprint _ := []
  post value _ _ result := result = value
  raises value _ := if value ≤ 100 then none else some .argumentOutOfRange

/-- The public verifier's default theorem. The certificate supplies the methods and the loader
constructs the initial memory. The caller supplies neither runtime bodies nor message text. -/
theorem correctness :
    contract.HoldsAtEntryCLR Extracted.program 0 Extracted.translation_valid .net11WinX64 := by
  obtain ⟨body, memory, source, _, loaded, runs⟩ := independentOfResource
  refine ⟨.range body, memory, certifiedEntry source, loaded, by decide, ?_⟩
  intro extra value initial permitted
  have same : initial = memory := permitted.1
  subst initial
  have actual := runs extra value
  by_cases within : value ≤ 100
  · simp only [OutcomeContract.atStartup, contract, within, ite_true]
    rw [ite_eq_left within] at actual
    exact ⟨66, memory, _, actual, Confined.refl _ _, value, rfl, rfl⟩
  · simp only [OutcomeContract.atStartup, contract, within, ite_false]
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
