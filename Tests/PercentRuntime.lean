import Tests.PercentRuntime.Program
import Tests.PercentRuntime.Startup
import CIL.Safety.Imports
import CIL.Safety.StepComposition

/-! The original exception path after the loader interns both arguments. -/
namespace Tests.PercentRuntime
open CIL CIL.Extraction CIL.Safety Startup
set_option maxRecDepth 65536
set_option maxHeartbeats 30000000

open Lean Elab Tactic Meta in
local elab "percent_rfl" : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← instantiateMVars (← goal.getType')
  let some (_, lhs, _) := type.eq? | throwError "expected equation"
  goal.assign (← withOptions (Elab.async.set · false) do mkAuxTheorem type (← mkEqRefl lhs))
  replaceMainGoal []

/-- Installing or reusing a runtime literal leaves the method's allocation budget independent. -/
def funded (m : Safety.Memory) : Safety.Memory := { m with heapBudget := 128 }

private theorem loadWithBudget (text : String) (m : Safety.Memory) (ref : Reference)
    (loaded : stringLiteralInstruction text [] m = .ok (m, [.object (.address ref)])) :
    literalObject (funded m) text = .ok (.object (.address ref)) := by
  change literalObject m text = _
  cases read : literalObject m text with
  | error fault => simp [stringLiteralInstruction, read, bind, Except.bind] at loaded
  | ok value =>
    simpa [stringLiteralInstruction, read, bind, Except.bind, pure, Except.pure] using loaded

#print axioms loadWithBudget

private theorem startAtBranch (name message : String) (value : W32) (m : Safety.Memory) :
    invoke (program name message) 66 0 [.scalar (.i32 value)] m =
    run (program name message) 63 0 (if value ≤ 100 then 7 else 3) [.scalar (.i32 value)]
      ⟨m.nextIdentity, [], [], 0⟩ [] m := by
  have first : invoke (program name message) 66 0 [.scalar (.i32 value)] m =
      run (program name message) 64 0 2 [.scalar (.i32 value)] ⟨m.nextIdentity, [], [], 0⟩
        [.scalar (.i32 100), .scalar (.i32 value)] m := by percent_rfl
  rw [first]
  apply run_next (body := caller name message) (op := .ble_un 7) rfl (by percent_rfl)
  percent_rfl
#print axioms startAtBranch

private theorem returned (name message : String) (value : W32) (m : Safety.Memory) :
    run (program name message) 63 0 7 [.scalar (.i32 value)] ⟨m.nextIdentity, [], [], 0⟩
      [] m = .ok (m, [.scalar (.i32 value)]) := by percent_rfl
#print axioms returned

/-- All nine instruction sites come from Percent's decoded body. The two string operands
    vary freely. After loader initialization and a 128-byte runtime allocation grant, the actual
    constructor call returns and the original throw reports ArgumentOutOfRangeException. -/
theorem initializedPercent (name message : String)
    (nameFits : (CIL.utf16Units name).length ≤ 0x7fffffff)
    (messageFits : (CIL.utf16Units message).length ≤ 0x7fffffff) :
    ∃ first final, intern Safety.Memory.empty name = .ok (⟨0,0⟩, first) ∧
      intern first message = .ok (⟨if name = message then 0 else 1,0⟩, final) ∧
      ∀ value : W32, invoke (program name message) 66 0 [.scalar (.i32 value)] (funded final) =
        if value ≤ 100 then .ok (funded final, [.scalar (.i32 value)])
        else .error ⟨0,6,.thrown .argumentOutOfRange⟩ := by
  obtain ⟨first, final, installed, repeated, _, nameLoad, messageLoad⟩ :=
    constructorLiterals name message nameFits messageFits
  refine ⟨first, final, installed, repeated, ?_⟩
  intro value
  rw [startAtBranch]
  by_cases within : value ≤ 100
  · simp only [within, ite_true]
    exact returned _ _ _ _
  simp only [within, ite_false]
  let args : List Safety.Value := [.scalar (.i32 value)]
  let activation : Safety.Frame := ⟨final.nextIdentity, [], [], 0⟩
  change run (program name message) 63 0 3 args activation [] (funded final) = _
  have load (pc : Nat) (stack : List Safety.Value) (text : String) (ref : Reference)
      (ok : literalObject (funded final) text = .ok (.object (.address ref))) :
      step (caller name message) (.ldstr text) pc args activation stack (funded final) =
        .ok (.next (pc+1) (.object (.address ref) :: stack) activation (funded final)) := by
    rw [step_ldstr_eq, ok]
    rfl
  rw [run_next (body := caller name message) (op := .ldstr name) rfl (by percent_rfl)
    (load 3 [] name _ (loadWithBudget _ _ _ nameLoad))]
  rw [run_next (body := caller name message) (op := .ldstr message) rfl (by percent_rfl)
    (load 4 _ message _ (loadWithBudget _ _ _ messageLoad))]
  have valid (text : String) (fits : (CIL.utf16Units text).length ≤ 0x7fffffff) :
      (storage (bytesOfString text)).valid = true := by
    apply validStorage
    rw [storageSize]
    unfold nativeLimit
    omega
  simp only [intern, Safety.Memory.empty, List.lookup_nil, Nat.not_lt.mpr nameFits, ↓reduceIte,
    allocate, valid name nameFits, Bool.not_true, Bool.false_eq_true, Option.isSome_none,
    bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, true_and] at installed
  subst first
  by_cases same : name = message
  · subst message
    simp [intern, Startup.loaded, pure, Except.pure] at repeated
    subst final
    simp only [ite_true, args, activation]
    percent_rfl
  · have reverse : (message == name) = false := by simpa using Ne.symm same
    simp [-List.length_flatMap, intern, Startup.loaded, List.lookup, reverse,
      Nat.not_lt.mpr messageFits, allocate, valid message messageFits,
      same, bind, Except.bind, pure, Except.pure] at repeated
    subst final
    simp only [same, ite_false, args, activation]
    percent_rfl
#print axioms initializedPercent

/-- Reading the two original operands reconstructs the decoded instruction sequence exactly. -/
private theorem compiledProgram_eq :
    let texts := physicalLiterals.getD ("", "")
    compiledProgram = program texts.1 texts.2 := by cil_kernel_rfl
#print axioms compiledProgram_eq

/-- Every UInt32 input to the original method returns its value or reaches the source throw.
    Only the loader reads the actual literal texts. The contract observes the exception type. -/
theorem compiledPercent :
    ∃ name message first final, physicalLiterals = some (name, message) ∧
      intern Safety.Memory.empty name = .ok (⟨0,0⟩, first) ∧
      intern first message = .ok (⟨if name = message then 0 else 1,0⟩, final) ∧
      ∀ value : W32, invoke compiledProgram 66 0 [.scalar (.i32 value)] (funded final) =
        if value ≤ 100 then .ok (funded final, [.scalar (.i32 value)])
        else .error ⟨0,6,.thrown .argumentOutOfRange⟩ := by
  let texts := physicalLiterals.getD ("","")
  have bound : physicalLiterals = some texts := by dsimp only [texts]; cil_kernel_rfl
  have same : compiledProgram = program texts.1 texts.2 := compiledProgram_eq
  have fitsName : (CIL.utf16Units texts.1).length ≤ 0x7fffffff := by
    dsimp only [texts]; decide +kernel
  have fitsMessage : (CIL.utf16Units texts.2).length ≤ 0x7fffffff := by
    dsimp only [texts]; decide +kernel
  obtain ⟨first, final, loaded, interned, ran⟩ :=
    initializedPercent texts.1 texts.2 fitsName fitsMessage
  exact ⟨texts.1, texts.2, first, final, bound, loaded, interned, same ▸ ran⟩
#print axioms compiledPercent
/-- Execute the ordinary decoded program on arbitrary UInt32 input after runtime initialization.
    The PE string operands and the actual constructor are taken directly from the checked bodies. -/
theorem decodedPercent :
    ∃ entry constructors name message first final, checkedCaller = some entry ∧
      coreMethods = some constructors ∧ physicalLiterals = some (name, message) ∧
      intern Safety.Memory.empty name = .ok (⟨0,0⟩, first) ∧
      intern first message = .ok (⟨if name = message then 0 else 1,0⟩, final) ∧
      ∀ (additional : Program) (value : W32),
        invoke ((entry :: constructors) ++ additional) 66 0 [.scalar (.i32 value)] (funded final) =
        if value ≤ 100 then .ok (funded final, [.scalar (.i32 value)])
        else .error ⟨0,6,.thrown .argumentOutOfRange⟩ := by
  obtain ⟨entry, constructors, decoded, closure, same⟩ := decoderProgram
  obtain ⟨name, message, first, final, literals, loaded, interned, ran⟩ := compiledPercent
  refine ⟨entry, constructors, name, message, first, final, decoded, closure, literals,
    loaded, interned, ?_⟩
  intro additional value
  apply invoke_extend ⟨additional, rfl⟩
  · split
    · intro fault outcome
      cases outcome
    · intro fault outcome
      cases outcome
      decide
  · rw [← same]
    exact ran value
#print axioms decodedPercent


/-- Before any loader action, the admitted branch preserves every caller memory. At the first
string load, the unprepared exceptional branch is inconclusive for CLR contracts. -/
theorem unpreparedPercent :
    ∃ entry constructors, checkedCaller = some entry ∧ coreMethods = some constructors ∧
      (∀ (value : W32) (memory : Safety.Memory), value ≤ 100 →
        invoke (entry :: constructors) 66 0 [.scalar (.i32 value)] memory =
          .ok (memory, [.scalar (.i32 value)])) ∧
      (∀ (value : W32), 100 < value → ∃ reason,
        invoke (entry :: constructors) 66 0 [.scalar (.i32 value)] Safety.Memory.empty =
          .error ⟨0, 3, .unsupported reason⟩) := by
  obtain ⟨entry, constructors, decoded, closure, same⟩ := decoderProgram
  refine ⟨entry, constructors, decoded, closure, ?_, ?_⟩ <;> rw [← same]
  · intro value memory within
    rw [compiledProgram_eq, startAtBranch, ite_eq_left within]
    exact returned _ _ _ _
  · intro value outside
    rw [compiledProgram_eq, startAtBranch, ite_eq_right (BitVec.not_le.mpr outside)]
    exact ⟨"String literal is not bound by the caller", by percent_rfl⟩
#print axioms unpreparedPercent

end Tests.PercentRuntime
