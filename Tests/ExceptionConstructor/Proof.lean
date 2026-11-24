import Extracted
import CIL.Safety.Imports
import CIL.Safety.ValueSteps

/-! Execution and constructor-argument checks for the three-argument exception constructor fixtures. -/

namespace ExceptionConstructorProof
open CIL CIL.Extraction CIL.Safety

set_option maxRecDepth 65536
set_option maxHeartbeats 30000000

/-- The fixture's public method selects the specified exception and the original null-load pc. -/
private def expected? : Option (ExceptionType × Nat) :=
  match Extracted.method0Signature with
  | "System.UInt32 Examples.Throws::ActualValue(System.UInt32)" => some (.argumentOutOfRange, 3)
  | "System.UInt32 Examples.Throws::ArgumentInner(System.UInt32)" => some (.argument, 4)
  | _ => none

private def expected := expected?.get (by cil_kernel_rfl)
private def entry := ProgramEntry.range Extracted.boundPackage
private def initial := entry.initialMemory.toOption.getD .empty
private def frame : Safety.Frame := ⟨initial.nextIdentity, [], [], 0⟩
private def args (value : W32) : List Safety.Value := [.scalar (.i32 value)]

private theorem loaded :
    (fun value => invoke Extracted.program 64 0 (args value) initial) =
    fun value => run Extracted.program 63 0 1 (args value) frame (args value) initial := by
  cil_kernel_rfl

private theorem returned :
    (fun value => run Extracted.program 62 0 7 (args value) frame [] initial) =
    fun value => .ok (initial, args value) := by cil_kernel_rfl

private theorem thrown :
    (fun value => run Extracted.program 62 0 2 (args value) frame [] initial) =
    fun _ => .error ⟨0, 6, .thrown expected.1⟩ := by cil_kernel_rfl

private theorem branch (value : W32) :
    invoke Extracted.program 64 0 (args value) initial =
      run Extracted.program 62 0 (if value = 0 then 7 else 2) (args value) frame [] initial := by
  have found : Extracted.program[0]? = some Extracted.method0 := Extracted.program_method0
  have code : Extracted.method0.code[1]? = some (.brfalse 7) := by cil_kernel_rfl
  have load : invoke Extracted.program 64 0 (args value) initial =
      run Extracted.program 63 0 1 (args value) frame (args value) initial := congrFun loaded value
  have stepTaken : Safety.step Extracted.method0 (.brfalse 7) 1 (args value) frame (args value) initial =
      .ok (.next (if value = 0 then 7 else 2) [] frame initial) := by
    unfold args
    rw [step_brfalse_i32_eq]
    by_cases zero : value = 0#32 <;> simp [CIL.truth, zero] <;> rfl
  rw [load, run_next found code stepTaken]

/-- Every uint executes against the published program at the original 64-fuel bound. -/
theorem outcome (value : W32) (tail : Program) :
    invoke (Extracted.program ++ tail) 64 0 (args value) initial =
      if value = 0 then .ok (initial, args value) else .error ⟨0, 6, .thrown expected.1⟩ := by
  split
  · rename_i zero
    apply invoke_extend ⟨tail, rfl⟩ _ _ _ _ (.ok (initial, args value)) (fun _ impossible => nomatch impossible)
    rw [branch, ite_eq_left zero]
    exact congrFun returned value
  · rename_i nonzero
    apply invoke_extend ⟨tail, rfl⟩ _ _ _ _ _ (by intro fault wrong; cases wrong; decide)
    rw [branch, ite_eq_right nonzero]
    exact congrFun thrown value
#print axioms outcome

/-- The certificate rejects replacing the original null argument or the stack throw. -/
private def acceptsReplacement (pc : Nat) (replacement : Instruction) : Bool :=
  let package := Extracted.boundPackage
  let changed := { package.root.2 with code := package.root.2.code.set pc replacement }
  let forged := { package with root := (package.caller, changed) }
  forged.checked Extracted.environment Extracted.assemblies Extracted.platformDefinitions

/-- Starting from the loader's empty storage, the bound overload returns or throws as specified.
    Appending any implementation at a declared slot preserves both outcomes. -/
theorem correctness :
    Extracted.translation_valid.entry .net11WinX64 = some entry ∧
    Extracted.translation_valid.entry .portable = none ∧
    entry.initialMemory = .ok initial ∧
    acceptsReplacement expected.2 .nop = false ∧ acceptsReplacement expected.2 (Extracted.method0.code[2]?.getD .nop) = false ∧
    acceptsReplacement 6 (.throw (some expected.1)) = false ∧
    ∀ (value : W32) (tail : Program), invoke (Extracted.program ++ tail) 64 0 (args value) initial =
      if value = 0 then .ok (initial, args value) else .error ⟨0, 6, .thrown expected.1⟩ :=
  ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl,
    by cil_kernel_rfl, by cil_kernel_rfl, outcome⟩
#print axioms correctness
end ExceptionConstructorProof
