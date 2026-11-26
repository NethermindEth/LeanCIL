import Extracted
import CIL.Safety.Imports
import CIL.Safety.ValueSteps

/-! Execution and constructor-argument checks for the exception constructor fixtures that pass
literal string arguments, with or without a null argument. -/

namespace ExceptionConstructorProof
open CIL CIL.Extraction CIL.Safety

set_option maxRecDepth 65536
set_option maxHeartbeats 30000000

/-- The raised exception, its HResult, the original pcs of the last constructor argument load, the
throw and the return, and an instruction the certificate must refuse in place of that load. -/
private structure Shape where
  raised : ExceptionType
  hresult : W32
  argumentLoad : Nat
  throwAt : Nat
  returnAt : Nat
  substitute : Instruction

/-- The fixture's public method selects its exception and compiled instruction positions. -/
private def expected? : Option Shape :=
  match Extracted.method0Signature with
  | "System.UInt32 Examples.Throws::ActualValue(System.UInt32)" =>
    some ⟨.argumentOutOfRange, 0x80131502, 3, 6, 7, message⟩
  | "System.UInt32 Examples.Throws::ArgumentInner(System.UInt32)" =>
    some ⟨.argument, 0x80070057, 4, 6, 7, message⟩
  | "System.UInt32 Examples.Throws::Inner(System.UInt32)" =>
    some ⟨.invalidOperation, 0x80131509, 3, 5, 6, message⟩
  | "System.UInt32 Examples.Throws::Message(System.UInt32)" =>
    some ⟨.invalidOperation, 0x80131509, 2, 4, 5, .ldnull⟩
  | "System.UInt32 Examples.Throws::NamedArgument(System.UInt32)" =>
    some ⟨.argument, 0x80070057, 3, 5, 6, .ldnull⟩
  | _ => none
where
  /-- The message literal, which may not stand in for a null argument. -/
  message := Extracted.method0.code[2]?.getD .nop

private def expected := expected?.get (by cil_kernel_rfl)
private def entry := ProgramEntry.range Extracted.boundPackage
private def initial := entry.initialMemory.toOption.getD .empty
private def frame : Safety.Frame := ⟨initial.nextIdentity, [], [], 0, []⟩
private def args (value : W32) : List Safety.Value := [.scalar (.i32 value)]

private theorem loaded :
    (fun value => invoke Extracted.program 64 0 (args value) initial) =
    fun value => run Extracted.program 63 0 1 (args value) frame (args value) initial := by
  cil_kernel_rfl

private theorem returned :
    (fun value => run Extracted.program 62 0 expected.returnAt (args value) frame [] initial) =
    fun value => .ok (initial, args value) := by cil_kernel_rfl

private theorem thrown :
    (fun value => run Extracted.program 62 0 2 (args value) frame [] initial) =
    fun _ => .error ⟨0, expected.throwAt, .thrown expected.raised⟩ := by cil_kernel_rfl

private theorem branch (value : W32) :
    invoke Extracted.program 64 0 (args value) initial =
      run Extracted.program 62 0 (if value = 0 then expected.returnAt else 2) (args value) frame []
        initial := by
  have found : Extracted.program[0]? = some Extracted.method0 := Extracted.program_method0
  have code : Extracted.method0.code[1]? = some (.brfalse expected.returnAt) := by cil_kernel_rfl
  have load : invoke Extracted.program 64 0 (args value) initial =
      run Extracted.program 63 0 1 (args value) frame (args value) initial := congrFun loaded value
  have stepTaken : Safety.step Extracted.method0 (.brfalse expected.returnAt) 1 (args value) frame
      (args value) initial =
        .ok (.next (if value = 0 then expected.returnAt else 2) [] frame initial) := by
    unfold args
    rw [step_brfalse_i32_eq]
    by_cases zero : value = 0#32 <;> simp [CIL.truth, zero] <;> rfl
  rw [load, run_next found code stepTaken]

/-- Every uint executes against the published program at the original 64-fuel bound. -/
theorem outcome (value : W32) (tail : Program) :
    invoke (Extracted.program ++ tail) 64 0 (args value) initial =
      if value = 0 then .ok (initial, args value)
      else .error ⟨0, expected.throwAt, .thrown expected.raised⟩ := by
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

/-- The certificate rejects replacing the original argument load or the stack throw. -/
private def acceptsReplacement (pc : Nat) (replacement : Instruction) : Bool :=
  let package := Extracted.boundPackage
  let changed := { package.root.2 with code := package.root.2.code.set pc replacement }
  let forged := { package with root := (package.caller, changed) }
  forged.checked Extracted.environment Extracted.assemblies Extracted.platformDefinitions

/-- Read the HResult field selected by the physical CoreLib setter from the raised object. -/
private def raisedDetails : Option (LocatedFault × ExceptionType × W32) := do
  let .error state := invokeWithFaultState Extracted.program 64 0 (args 1) initial | none
  let reference ← state.exceptionObject
  let memory := state.unwoundMemory
  let type ← (runtimeTypeOf memory reference).toOption
  let raised ← runtimeException? type.identity
  let store ← Runtime.Net11WinX64.Core.SetHResult.definition.code[2]?
  let .field owner slot _ name false := store.operand | none
  guard (store.opcode == 0x7D && name == name!"_HResult")
  let address ← (objectFieldAddress memory (.address reference) owner (objectFieldOffset slot)).toOption
  let .i32 result ← (loadValue memory (.address address) 4).toOption | none
  return (state.location, raised, result)

private def expectedRaised : LocatedFault × ExceptionType × W32 :=
  (⟨0, expected.throwAt, .thrown expected.raised⟩, expected.raised, expected.hresult)

/-- The constructors complete their writes before the caller raises the actual object. -/
theorem raisedObject :
    raisedDetails = some expectedRaised := by cil_kernel_rfl
#print axioms raisedObject

/-- Starting from the loader's empty storage, the bound overload returns or throws as specified.
    Appending any implementation at a declared slot, such as the resource getter, preserves both
    outcomes. -/
theorem correctness :
    Extracted.translation_valid.entry .net11WinX64 = some entry ∧
    Extracted.translation_valid.entry .portable = none ∧
    entry.initialMemory = .ok initial ∧
    acceptsReplacement expected.argumentLoad .nop = false ∧
    acceptsReplacement expected.argumentLoad expected.substitute = false ∧
    acceptsReplacement expected.throwAt (.throw (some expected.raised)) = false ∧
    raisedDetails = some expectedRaised ∧
    ∀ (value : W32) (tail : Program), invoke (Extracted.program ++ tail) 64 0 (args value) initial =
      if value = 0 then .ok (initial, args value)
      else .error ⟨0, expected.throwAt, .thrown expected.raised⟩ :=
  ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl,
    by cil_kernel_rfl, by cil_kernel_rfl, raisedObject, outcome⟩
#print axioms correctness
end ExceptionConstructorProof