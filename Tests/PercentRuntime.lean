import Tests.PercentRuntime.Program
import Tests.PercentRuntime.Startup
import CIL.Safety.Imports
import CIL.Safety.StepComposition

/-! The original exception path after the loader interns both arguments. -/
namespace Tests.PercentRuntime
open CIL CIL.Extraction CIL.Safety CIL.Safety.LiteralImage CIL.Runtime.Net11WinX64 Startup
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
def atBudget (budget : Option Nat) (m : Safety.Memory) : Safety.Memory := { m with heapBudget := budget }

/-- Changing the deployment quota preserves the object reached by a loaded string. -/
private theorem loadWithBudget (budget : Option Nat) (text : String) (m : Safety.Memory) (ref : Reference)
    (loaded : stringLiteralInstruction text [] m = .ok (m, [.object (.address ref)])) :
    literalObject (atBudget budget m) text = .ok (.object (.address ref)) := by
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


/-- A successful string load supplies a checked object argument to the constructor. -/
private theorem checkedLiteralArgument (memory : Safety.Memory) (frame : Safety.Frame)
    (text : String) (ref : Reference)
    (loaded : literalObject memory text = .ok (.object (.address ref))) :
    callArgument frame memory (.object (.address ref)) = .ok (.object (.address ref)) := by
  cases found : memory.literals.lookup text with
  | none => simp [literalObject, found] at loaded
  | some actual =>
    have formed : formObject memory (.address actual) = .ok (.object (.address ref)) := by
      simpa [literalObject, found] using loaded
    have same := formObject_returns_input formed
    cases same
    exact callArgument_of_checked (checkedValue_object memory _ formed)
#print axioms checkedLiteralArgument

/-- On the original exceptional branch, a short budget fails at the allocation. Every sufficient
quota admits the constructor and reaches the typed throw. Both literal operands vary freely. -/
theorem initializedPercentAtBudget (budget : Option Nat) (name message : String)
    (nameFits : (CIL.utf16Units name).length ≤ 0x7fffffff)
    (messageFits : (CIL.utf16Units message).length ≤ 0x7fffffff) :
    ∃ first final, intern Safety.Memory.empty name = .ok (⟨0,0⟩, first) ∧
      intern first message = .ok (⟨if name = message then 0 else 1,0⟩, final) ∧
      ∀ value : W32, invoke (program name message) 66 0 [.scalar (.i32 value)] (atBudget budget final) =
        if value ≤ 100 then .ok (atBudget budget final, [.scalar (.i32 value)])
        else if budget.getD 128 < 128 then .error ⟨0, 5, .allocationFailure 128 (budget.getD 128)⟩
        else .error ⟨0, 6, .thrown .argumentOutOfRange⟩ := by
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
  change run (program name message) 63 0 3 args activation [] (atBudget budget final) = _
  have load (pc : Nat) (stack : List Safety.Value) (text : String) (ref : Reference)
      (ok : literalObject (atBudget budget final) text = .ok (.object (.address ref))) :
      step (caller name message) (.ldstr text) pc args activation stack (atBudget budget final) =
        .ok (.next (pc+1) (.object (.address ref) :: stack) activation (atBudget budget final)) := by
    rw [step_ldstr_eq, ok]
    rfl
  rw [run_next (body := caller name message) (op := .ldstr name) rfl (by percent_rfl)
    (load 3 [] name _ (loadWithBudget budget _ _ _ nameLoad))]
  rw [run_next (body := caller name message) (op := .ldstr message) rfl (by percent_rfl)
    (load 4 _ message _ (loadWithBudget budget _ _ _ messageLoad))]
  by_cases short : budget.getD 128 < 128
  · rw [ite_eq_left short]
    have firstArg := checkedLiteralArgument _ activation name _ (loadWithBudget budget _ _ _ nameLoad)
    have secondArg := checkedLiteralArgument _ activation message _
      (loadWithBudget budget _ _ _ messageLoad)
    apply run_fault (body := caller name message) (op := .newobj Source.member.method)
      rfl (by percent_rfl)
    let stack : List Safety.Value := [.object (.address ⟨if name = message then 0 else 1, 0⟩),
      .object (.address ⟨0, 0⟩)]
    have original : step (caller name message) (.newobj Source.member.method) 5 args activation
        stack (atBudget budget final) = newobjStep
          (some (.object 1 Core.RangeCtor.definition.objectBases 128)) Source.member.method
          (caller name message) 5 activation stack (atBudget budget final) := by
      dsimp only [stack]
      percent_rfl
    rw [original]
    dsimp only [stack]
    have arity : Source.member.method.parameters.length = 2 := by cil_kernel_rfl
    have insufficient : (atBudget budget final).heapBudget.getD 128 < 128 := short
    simp [newobjStep, arity, constructObject, List.mapM_cons, List.mapM_nil, firstArg, secondArg,
      allocateObject, insufficient, bind, Except.bind, pure, Except.pure]
    rfl
  rw [ite_eq_right short]
  have enough : budget = none ∨ ∃ spare, budget = some (spare + 128) := by
    cases budget with
    | none => exact Or.inl rfl
    | some bytes =>
      change ¬bytes < 128 at short
      exact Or.inr ⟨bytes - 128, by congr 1; omega⟩
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
    simp [intern, LiteralImage.loaded, pure, Except.pure] at repeated
    subst final
    simp only [ite_true, args, activation]
    rcases enough with rfl | ⟨spare, rfl⟩ <;> percent_rfl
  · have reverse : (message == name) = false := by simpa using Ne.symm same
    simp [-List.length_flatMap, intern, LiteralImage.loaded, List.lookup, reverse,
      Nat.not_lt.mpr messageFits, allocate, valid message messageFits,
      same, bind, Except.bind, pure, Except.pure] at repeated
    subst final
    simp only [same, ite_false, args, activation]
    rcases enough with rfl | ⟨spare, rfl⟩ <;> percent_rfl
#print axioms initializedPercentAtBudget


/-- Startup state with exactly the checked exception instance size available. -/
def funded (m : Safety.Memory) := atBudget (some 128) m

/-- A quota of 128 bytes admits the real allocation for any representable pair of strings. -/
theorem initializedPercent (name message : String)
    (nameFits : (CIL.utf16Units name).length ≤ 0x7fffffff)
    (messageFits : (CIL.utf16Units message).length ≤ 0x7fffffff) :
    ∃ first final, intern Safety.Memory.empty name = .ok (⟨0,0⟩, first) ∧
      intern first message = .ok (⟨if name = message then 0 else 1,0⟩, final) ∧
      ∀ value : W32, invoke (program name message) 66 0 [.scalar (.i32 value)] (funded final) =
        if value ≤ 100 then .ok (funded final, [.scalar (.i32 value)])
        else .error ⟨0,6,.thrown .argumentOutOfRange⟩ :=
  initializedPercentAtBudget (some 128) name message nameFits messageFits
#print axioms initializedPercent

/-- Reading the two original operands reconstructs the decoded instruction sequence exactly. -/
private theorem compiledProgram_eq :
    let texts := physicalLiterals.getD ("", "")
    compiledProgram = program texts.1 texts.2 := by cil_kernel_rfl
#print axioms compiledProgram_eq

/-- Every UInt32 input to the original method returns its value or reaches the source throw.
    Only the loader reads the actual literal texts. The contract observes the exception type. -/
private theorem compiledAtBudget (budget : Option Nat) :
    ∃ name message first final, physicalLiterals = some (name, message) ∧
      intern Safety.Memory.empty name = .ok (⟨0,0⟩, first) ∧
      intern first message = .ok (⟨if name = message then 0 else 1,0⟩, final) ∧
      ∀ value : W32, invoke compiledProgram 66 0 [.scalar (.i32 value)] (atBudget budget final) =
        if value ≤ 100 then .ok (atBudget budget final, [.scalar (.i32 value)])
        else if budget.getD 128 < 128 then .error ⟨0, 5, .allocationFailure 128 (budget.getD 128)⟩
        else .error ⟨0, 6, .thrown .argumentOutOfRange⟩ := by
  let texts := physicalLiterals.getD ("","")
  have bound : physicalLiterals = some texts := by dsimp only [texts]; cil_kernel_rfl
  have same : compiledProgram = program texts.1 texts.2 := compiledProgram_eq
  have fitsName : (CIL.utf16Units texts.1).length ≤ 0x7fffffff := by
    dsimp only [texts]; decide +kernel
  have fitsMessage : (CIL.utf16Units texts.2).length ≤ 0x7fffffff := by
    dsimp only [texts]; decide +kernel
  obtain ⟨first, final, loaded, interned, ran⟩ :=
    initializedPercentAtBudget budget texts.1 texts.2 fitsName fitsMessage
  exact ⟨texts.1, texts.2, first, final, bound, loaded, interned, same ▸ ran⟩
#print axioms compiledAtBudget

/-- Every UInt32 input to the original method returns its value or reaches the source throw.
    Only the loader reads the actual literal texts. The contract observes the exception type. -/
theorem compiledPercent :
    ∃ name message first final, physicalLiterals = some (name, message) ∧
      intern Safety.Memory.empty name = .ok (⟨0,0⟩, first) ∧
      intern first message = .ok (⟨if name = message then 0 else 1,0⟩, final) ∧
      ∀ value : W32, invoke compiledProgram 66 0 [.scalar (.i32 value)] (funded final) =
        if value ≤ 100 then .ok (funded final, [.scalar (.i32 value)])
        else .error ⟨0,6,.thrown .argumentOutOfRange⟩ := compiledAtBudget (some 128)
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


/-- The verifier can derive the entire initial literal registry from the decoded program.
Only the deployment's explicit instance-allocation quota is needed at entry. -/
theorem imagePercent (heapBytes : Nat) :
    ∃ entry constructors initial, checkedCaller = some entry ∧ coreMethods = some constructors ∧
      initialMemory imageMethods heapBytes = .ok initial ∧
      ∀ value : W32, invoke (entry :: constructors) 66 0 [.scalar (.i32 value)] initial =
        if value ≤ 100 then .ok (initial, [.scalar (.i32 value)])
        else if heapBytes < 128 then .error ⟨0, 5, .allocationFailure 128 heapBytes⟩
        else .error ⟨0, 6, .thrown .argumentOutOfRange⟩ := by
  obtain ⟨entry, constructors, decoded, closure, same⟩ := decoderProgram
  obtain ⟨name, message, first, final, literals, installed, repeated, ran⟩ :=
    compiledAtBudget heapBytes
  refine ⟨entry, constructors, atBudget heapBytes final, decoded, closure, ?_, same ▸ ran⟩
  have source : physicalLiterals.map (fun pair => [pair.1, pair.2]) =
      some (operands imageMethods) := by cil_kernel_rfl
  rw [literals] at source
  have sites : operands imageMethods = [name, message] := (Option.some.inj source).symm
  simp [initialMemory, sites, List.foldlM_cons, installed, repeated, atBudget,
    Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
#print axioms imagePercent

end Tests.PercentRuntime
