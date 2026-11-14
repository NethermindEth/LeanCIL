import Tests.WrapperProofs

/-! Execution facts that the generated Unsafe layout fixtures apply to extracted bodies. Each body
    takes the declared signature and layout environment an extraction records, which execution
    does not read, so a fact applies to an extracted body by unification alone. -/

namespace Tests.UnsafeWrappers
open CIL.Safety

/-- `Unsafe.Add` of an element of `size` bytes as an extraction emits it. -/
def addMethod (size : Nat) (signed : Bool) (profile : CIL.FeatureProfile)
    (declared : CIL.DeclaredSignature) (environment : CIL.LayoutEnvironment) : CIL.Method :=
  { profile := profile, code := [.arg 0, .arg 1, .memory (.add size signed), .ret],
    locals := [], returnsValue := true, declared := declared, environment := environment }

/-- An in-bounds `Unsafe.Add` returns the offset reference. -/
theorem add_ok {declared : CIL.DeclaredSignature} {environment : CIL.LayoutEnvironment}
    (size : Nat) (signed : Bool) (profile : CIL.FeatureProfile)
    (memory : Memory) (reference returned : ManagedReference) (offset : CIL.Value)
    (valid : checkedValue memory (.reference reference) = .ok (.reference reference))
    (numeric : checkedValue memory (.scalar offset) = .ok (.scalar offset))
    (operation : memoryInstruction (.add size signed) [.scalar offset, .reference reference] memory =
      .ok (memory, [.reference returned]))
    (result : checkedValue memory (.reference returned) = .ok (.reference returned)) :
    (invoke [addMethod size signed profile declared environment] 8 0
      [.reference reference, .scalar offset] memory).map Prod.snd = .ok [.reference returned] := by
  have specified : offset.hasUnspecified = false := by
    cases unknown : offset.hasUnspecified with
    | false => rfl
    | true =>
      have rejected := operation
      simp [memoryInstruction, CIL.MemoryOp.argumentCount, unspecifiedOperands,
        Value.hasUnspecified, unknown] at rejected
  simp only [invoke, addMethod, List.getElem?_cons_zero, List.mapM_cons, List.mapM_nil,
    valid, numeric, enterFrame, makeSelectedLocals, List.isEmpty, ↓reduceIte, makeLocals,
    makeParameterHomes,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    List.map_nil, List.nil_append]
  rw [run_next (body := addMethod size signed profile declared environment) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, valid] <;> rfl)]
  rw [run_next (body := addMethod size signed profile declared environment) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, numeric] <;> rfl)]
  rw [run_next (body := addMethod size signed profile declared environment) rfl rfl
    (by simp [step, observerCount, CIL.MemoryOp.argumentCount, unspecifiedOperands,
      Value.hasUnspecified, specified, staticInstruction, operation] <;> rfl)]
  rw [run_return (body := addMethod size signed profile declared environment) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, addMethod, result] <;> rfl)
    (by simp [leaveFrame, result] <;> rfl)]
  rfl

/-- A faulting `Unsafe.Add` stops at the add with its fault. -/
theorem add_error {declared : CIL.DeclaredSignature} {environment : CIL.LayoutEnvironment}
    (size : Nat) (signed : Bool) (profile : CIL.FeatureProfile)
    (memory : Memory) (reference : ManagedReference) (offset : CIL.Value) (fault : ExecutionFault)
    (valid : checkedValue memory (.reference reference) = .ok (.reference reference))
    (numeric : checkedValue memory (.scalar offset) = .ok (.scalar offset))
    (specified : offset.hasUnspecified = false)
    (operation : memoryInstruction (.add size signed) [.scalar offset, .reference reference] memory =
      .error fault) :
    (invoke [addMethod size signed profile declared environment] 8 0
      [.reference reference, .scalar offset] memory).map Prod.snd = .error ⟨0, 2, fault⟩ := by
  simp only [invoke, addMethod, List.getElem?_cons_zero, List.mapM_cons, List.mapM_nil,
    valid, numeric, enterFrame, makeSelectedLocals, List.isEmpty, ↓reduceIte, makeLocals,
    makeParameterHomes,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    List.map_nil, List.nil_append]
  rw [run_next (body := addMethod size signed profile declared environment) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, valid] <;> rfl)]
  rw [run_next (body := addMethod size signed profile declared environment) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, numeric] <;> rfl)]
  rw [Tests.WrapperProofs.run_fault
    (body := addMethod size signed profile declared environment) rfl rfl
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
theorem size_ok {declared : CIL.DeclaredSignature} {environment : CIL.LayoutEnvironment}
    (size : BitVec 32) (profile : CIL.FeatureProfile) (memory : Memory) :
    (invoke
      [{ profile := profile, code := [.ldc_i4 size, .ret], locals := [], returnsValue := true,
         declared := declared, environment := environment }]
      8 0 [] memory).map Prod.snd = .ok [.scalar (.i32 size)] := by
  rfl

#print axioms add_ok
#print axioms add_error
#print axioms size_ok

/-! The fixtures apply these facts to extracted bodies, which carry their declared signature and
    the extraction's layouts. Each example states a body in the emitted form, with a non-empty
    environment, and proves its claim with the term the fixture generator writes. -/

/-- A layout environment with one entry, as an extraction that reads a struct records. -/
private def emittedEnvironment : CIL.LayoutEnvironment := { layouts := #[⟨⟨4, []⟩, 4⟩] }

/-- `Unsafe.SizeOf` in the form an extraction emits. -/
private def emittedSize : CIL.Method :=
  { profile := .scalar, returnsValue := true, locals := [], localKinds := [],
    opaqueVectorLocals := [], parameterHomes := [], staticSites := [],
    declared :=
      { parameters := [], returnType := .atom CIL.Extraction.runtimeScope "System.Int32" },
    environment := emittedEnvironment, links := [], code := [.ldc_i4 4, .ret] }

example : (invoke [emittedSize] 8 0 [] Memory.empty).map Prod.snd = .ok [.scalar (.i32 4)] := by
  exact size_ok _ _ _

/-- `Unsafe.Add` of a byte element in the form an extraction emits. -/
private def emittedAdd : CIL.Method :=
  { profile := .scalar, returnsValue := true, locals := [], localKinds := [],
    opaqueVectorLocals := [], parameterHomes := [], staticSites := [],
    declared :=
      { parameters := [.byref (.atom CIL.Extraction.runtimeScope "System.Boolean"),
          .atom CIL.Extraction.runtimeScope "System.Int32"],
        returnType := .byref (.atom CIL.Extraction.runtimeScope "System.Boolean") },
    environment := emittedEnvironment, links := [],
    code := [.arg 0, .arg 1, .memory (.add 1 true), .ret] }

/-- Four caller-stack bytes at allocation 0. -/
private def emittedMemory : Memory := { Memory.empty with
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨4, 1, []⟩, true, [4]⟩ else none
  nextIdentity := 1 }

example :
    (invoke [emittedAdd] 8 0 [.reference (.address ⟨0, 2⟩), .scalar (.i32 4294967295)]
      emittedMemory).map Prod.snd = .ok [.reference (.address ⟨0, 1⟩)] ∧
    (invoke [emittedAdd] 8 0 [.reference .null, .scalar (.i32 0)] emittedMemory).map Prod.snd =
      .error ⟨0, 2, .memory .nullDereference .null 0⟩ := by
  exact ⟨add_ok _ _ _ _ _ _ _ rfl rfl rfl rfl, add_error _ _ _ _ _ _ _ rfl rfl rfl rfl⟩

end Tests.UnsafeWrappers
