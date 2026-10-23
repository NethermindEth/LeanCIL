import Tests.WrapperProofs

namespace Tests.UnsafeWrappers
open CIL.Safety

def addMethod (size : Nat) (signed : Bool) (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, code := [.arg 0, .arg 1, .memory (.add size signed), .ret],
    locals := [], returnsValue := true }

theorem add_ok (size : Nat) (signed : Bool) (profile : CIL.FeatureProfile)
    (memory : Memory) (reference returned : ManagedReference) (offset : CIL.Value)
    (valid : checkedValue memory (.reference reference) = .ok (.reference reference))
    (numeric : checkedValue memory (.scalar offset) = .ok (.scalar offset))
    (operation : memoryInstruction (.add size signed) [.scalar offset, .reference reference] memory =
      .ok (memory, [.reference returned]))
    (result : checkedValue memory (.reference returned) = .ok (.reference returned)) :
    (invoke [addMethod size signed profile] 8 0 [.reference reference, .scalar offset] memory).map Prod.snd =
      .ok [.reference returned] := by
  have specified : offset.hasUnspecified = false := by
    cases unknown : offset.hasUnspecified with
    | false => rfl
    | true =>
      have rejected := operation
      simp [memoryInstruction, CIL.MemoryOp.argumentCount, unspecifiedOperands,
        Value.hasUnspecified, unknown] at rejected
  simp only [invoke, addMethod, List.getElem?_cons_zero, List.mapM_cons, List.mapM_nil,
    valid, numeric, enterFrame, makeSelectedLocals, List.isEmpty, ↓reduceIte, makeLocals,
    makeArgumentHomes, makeParameterHomes,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    List.map_nil, List.nil_append]
  rw [run_next (body := addMethod size signed profile) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, valid] <;> rfl)]
  rw [run_next (body := addMethod size signed profile) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, numeric] <;> rfl)]
  rw [run_next (body := addMethod size signed profile) rfl rfl
    (by simp [step, observerCount, CIL.MemoryOp.argumentCount, unspecifiedOperands,
      Value.hasUnspecified, specified, staticInstruction, operation] <;> rfl)]
  rw [run_return (body := addMethod size signed profile) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, addMethod, result] <;> rfl)
    (by simp [leaveFrame, result] <;> rfl)]
  rfl

theorem add_error (size : Nat) (signed : Bool) (profile : CIL.FeatureProfile)
    (memory : Memory) (reference : ManagedReference) (offset : CIL.Value) (fault : ExecutionFault)
    (valid : checkedValue memory (.reference reference) = .ok (.reference reference))
    (numeric : checkedValue memory (.scalar offset) = .ok (.scalar offset))
    (specified : offset.hasUnspecified = false)
    (operation : memoryInstruction (.add size signed) [.scalar offset, .reference reference] memory =
      .error fault) :
    (invoke [addMethod size signed profile] 8 0 [.reference reference, .scalar offset] memory).map Prod.snd =
      .error ⟨0, 2, fault⟩ := by
  simp only [invoke, addMethod, List.getElem?_cons_zero, List.mapM_cons, List.mapM_nil,
    valid, numeric, enterFrame, makeSelectedLocals, List.isEmpty, ↓reduceIte, makeLocals,
    makeArgumentHomes, makeParameterHomes,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    List.map_nil, List.nil_append]
  rw [run_next (body := addMethod size signed profile) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, valid] <;> rfl)]
  rw [run_next (body := addMethod size signed profile) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, numeric] <;> rfl)]
  rw [Tests.WrapperProofs.run_fault (body := addMethod size signed profile) rfl rfl
    (by simp [step, observerCount, CIL.MemoryOp.argumentCount, unspecifiedOperands,
      Value.hasUnspecified, specified, staticInstruction, operation] <;> rfl)]
  rfl

/-- A partial vector is rejected before the integer-offset adapter runs. -/
example (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame)
    (memory : Memory) (reference : ManagedReference) (low : CIL.W64) :
    memoryInstruction (.add 1 false) [.scalar (.v128Low64 low), .reference reference] memory =
      .error (.unsupported "Memory operation observes unspecified vector bits") ∧
    step body (.memory (.add 1 false)) pc args frame
      [.scalar (.v128Low64 low), .reference reference] memory =
      .error (.unsupported "Instruction observes unspecified vector bits") := by
  constructor <;> rfl

/-- The complete checked constant-return wrapper, for every size and caller memory. -/
theorem size_ok (size : BitVec 32) (profile : CIL.FeatureProfile) (memory : Memory) :
    (invoke [{ profile := profile, code := [.const32 size, .ret], locals := [], returnsValue := true }]
      8 0 [] memory).map Prod.snd = .ok [.scalar (.i32 size)] := by
  rfl

#print axioms add_ok
#print axioms add_error
#print axioms size_ok
end Tests.UnsafeWrappers
