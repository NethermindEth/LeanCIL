import Tests.WrapperProofs

/-! Execution facts that the generated Unsafe layout fixtures apply to extracted bodies. Each body
    takes the declared signature and layout environment an extraction records. Its return metadata
    must match the reference or integer result that the execution fact guarantees. -/

namespace Tests.UnsafeWrappers
open CIL.Safety

/-- `Unsafe.Add` of a closed element type as an extraction emits it. -/
def addMethod (method : CIL.Extraction.MethodRef) (profile : CIL.FeatureProfile)
    (declared : CIL.DeclaredSignature) (environment : CIL.LayoutEnvironment) : CIL.Method :=
  { profile := profile, code := [.ldarg 0, .ldarg 1, .call method {}, .ret],
    locals := [], returnsValue := true, declared := declared, environment := environment }

/-- An in-bounds `Unsafe.Add` over arguments read whole returns the offset reference. -/
theorem add_ok {declared : CIL.DeclaredSignature} {environment : CIL.LayoutEnvironment}
    {element : CIL.Extraction.TypeExpr}
    (returnedType : declared.returnType = .byref element)
    (referenceStorage : (declared.argumentType 0).bind
      (CIL.Extraction.declaredNarrow environment.rawLayouts) = none)
    (offsetStorage : (declared.argumentType 1).bind
      (CIL.Extraction.declaredNarrow environment.rawLayouts) = none)
    {method : CIL.Extraction.MethodRef} {size : Nat} {signed : Bool}
    (found : CIL.Extraction.runtimeModel environment .call method =
      some (.memory (.add size signed)))
    (profile : CIL.FeatureProfile)
    (memory : Memory) (reference returned : ManagedReference) (offset : CIL.Value)
    (valid : checkedValue memory (.reference reference) = .ok (.reference reference))
    (numeric : checkedValue memory (.scalar offset) = .ok (.scalar offset))
    (operation : memoryInstruction (.add size signed) [.scalar offset, .reference reference] memory =
      .ok (memory, [.reference returned]))
    (result : checkedValue memory (.reference returned) = .ok (.reference returned)) :
    (invoke [addMethod method profile declared environment] 8 0
      [.reference reference, .scalar offset] memory).map Prod.snd = .ok [.reference returned] := by
  have specified : offset.hasUnspecified = false := by
    cases unknown : offset.hasUnspecified with
    | false => rfl
    | true =>
      have rejected := operation
      simp [memoryInstruction, CIL.MemoryOp.argumentCount, unspecifiedOperands,
        Value.hasUnspecified, unknown] at rejected
  simp only [invoke_eq, addMethod, List.getElem?_cons_zero, List.mapM_cons, List.mapM_nil,
    valid, numeric, enterFrame, makeSelectedLocals, List.isEmpty, ↓reduceIte, makeLocals,
    makeParameterHomes,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    List.map_nil, List.nil_append]
  rw [run_next (body := addMethod method profile declared environment) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, loadArgument, CIL.Method.argumentAccess,
      addMethod, referenceStorage, valid] <;> rfl)]
  rw [run_next (body := addMethod method profile declared environment) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, loadArgument, CIL.Method.argumentAccess,
      addMethod, offsetStorage, numeric] <;> rfl)]
  rw [run_next (body := addMethod method profile declared environment) rfl rfl
    (by
      rw [step_call_memory (link := rfl) (found := found) (direct := rfl)]
      simp [step, observerCount, CIL.MemoryOp.argumentCount, unspecifiedOperands,
        Value.hasUnspecified, specified, staticInstruction, operation, viewOperandCount,
        viewOperands] <;> rfl)]
  rw [run_return (body := addMethod method profile declared environment) rfl rfl
    (by simp [step, returnFrom, observerCount, unspecifiedOperands, addMethod, result,
      CIL.Method.returnNarrow, returnedType, CIL.Extraction.declaredNarrow,
      CIL.Extraction.typeStorage] <;> rfl)
    (by simp [leaveFrame, result] <;> rfl)]
  rfl

/-- A faulting `Unsafe.Add` stops at the add with its fault. -/
theorem add_error {declared : CIL.DeclaredSignature} {environment : CIL.LayoutEnvironment}
    (referenceStorage : (declared.argumentType 0).bind
      (CIL.Extraction.declaredNarrow environment.rawLayouts) = none)
    (offsetStorage : (declared.argumentType 1).bind
      (CIL.Extraction.declaredNarrow environment.rawLayouts) = none)
    {method : CIL.Extraction.MethodRef} {size : Nat} {signed : Bool}
    (found : CIL.Extraction.runtimeModel environment .call method =
      some (.memory (.add size signed)))
    (profile : CIL.FeatureProfile)
    (memory : Memory) (reference : ManagedReference) (offset : CIL.Value) (fault : ExecutionFault)
    (valid : checkedValue memory (.reference reference) = .ok (.reference reference))
    (numeric : checkedValue memory (.scalar offset) = .ok (.scalar offset))
    (specified : offset.hasUnspecified = false)
    (operation : memoryInstruction (.add size signed) [.scalar offset, .reference reference] memory =
      .error fault) :
    (invoke [addMethod method profile declared environment] 8 0
      [.reference reference, .scalar offset] memory).map Prod.snd = .error ⟨0, 2, fault⟩ := by
  simp only [invoke_eq, addMethod, List.getElem?_cons_zero, List.mapM_cons, List.mapM_nil,
    valid, numeric, enterFrame, makeSelectedLocals, List.isEmpty, ↓reduceIte, makeLocals,
    makeParameterHomes,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    List.map_nil, List.nil_append]
  rw [run_next (body := addMethod method profile declared environment) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, loadArgument, CIL.Method.argumentAccess,
      addMethod, referenceStorage, valid] <;> rfl)]
  rw [run_next (body := addMethod method profile declared environment) rfl rfl
    (by simp [step, observerCount, unspecifiedOperands, loadArgument, CIL.Method.argumentAccess,
      addMethod, offsetStorage, numeric] <;> rfl)]
  rw [Tests.WrapperProofs.run_fault
    (body := addMethod method profile declared environment) rfl rfl
    (by
      rw [step_call_memory (link := rfl) (found := found) (direct := rfl)]
      simp [step, observerCount, CIL.MemoryOp.argumentCount, unspecifiedOperands,
        Value.hasUnspecified, specified, staticInstruction, operation, viewOperandCount,
        viewOperands] <;> rfl)]
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

/-- `Unsafe.SizeOf` as an extraction emits it: a call without a link, whose model the layouts
    give. -/
def sizeMethod (method : CIL.Extraction.MethodRef) (profile : CIL.FeatureProfile)
    (declared : CIL.DeclaredSignature) (environment : CIL.LayoutEnvironment) : CIL.Method :=
  { profile := profile, code := [.call method {}, .ret], locals := [], returnsValue := true,
    declared := declared, environment := environment }

/-- The complete checked wrapper of a call the layouts model as a constant, for every caller
    memory. -/
theorem size_ok {declared : CIL.DeclaredSignature} {environment : CIL.LayoutEnvironment}
    {method : CIL.Extraction.MethodRef} {size : BitVec 32}
    (returnedType : declared.returnType = .atom CIL.Extraction.runtimeScope "System.Int32")
    (found : CIL.Extraction.runtimeModel environment .call method = some (.constant size))
    (profile : CIL.FeatureProfile) (memory : Memory) :
    (invoke [sizeMethod method profile declared environment] 8 0 [] memory).map Prod.snd =
      .ok [.scalar (.i32 size)] := by
  let body := sizeMethod method profile declared environment
  let frame : Frame := ⟨memory.nextIdentity, [], [], 0⟩
  let values := [Value.scalar (.i32 size)]
  have pushes : step body (.call method {}) 0 [] frame [] memory =
      .ok (.next 1 values frame memory) :=
    step_call_model (body := body) (pc := 0) (method := method) (prefixes := {})
      (args := []) (frame := frame) (memory := memory) rfl found rfl []
  have narrow : body.returnNarrow = none := by
    simp only [body, sizeMethod, CIL.Method.returnNarrow, returnedType]
    rfl
  have returns : step body .ret 1 [] frame values memory = .ok (.returned values memory) := by
    change returnFrom body.returnNarrow true values memory = _
    rw [narrow]
    rfl
  have next := run_next (program := [body]) (fuel := 7) (method := 0) rfl rfl pushes
  have done := run_return (program := [body]) (fuel := 6) (method := 0) rfl rfl returns
    (by rfl)
  have entered : enterFrame body [] memory = .ok (frame, memory) := rfl
  change (invoke [body] 8 0 [] memory).map Prod.snd = _
  simp only [invoke_eq, List.getElem?_cons_zero, List.mapM_nil, entered, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure, next, done]
  rfl

#print axioms add_ok
#print axioms add_error
#print axioms size_ok

/-! The fixtures apply these facts to extracted bodies, which carry their declared signature and
    the extraction's layouts. Each example states a body in the emitted form, with a non-empty
    environment, and proves its claim with the term the fixture generator writes. -/

/-- A layout environment with one entry, as an extraction that reads a struct records. -/
private def emittedEnvironment : CIL.LayoutEnvironment := { layouts := #[⟨⟨4, []⟩, 4⟩] }

/-- `int Unsafe.SizeOf<int>()` as a call site instantiates it. -/
private def sizeOfInt : CIL.Extraction.MethodRef :=
  { owner := CIL.Extraction.unsafeOwner, name := name!"SizeOf", hasThis := false,
    genericArity := 1, returnType := .atom CIL.Extraction.runtimeScope "System.Int32",
    parameters := [], methodArguments := [.atom CIL.Extraction.runtimeScope "System.Int32"] }

/-- `Unsafe.SizeOf` in the form an extraction emits. -/
private def emittedSize : CIL.Method :=
  { profile := .scalar, returnsValue := true, locals := [], localKinds := [],
    opaqueVectorLocals := [], parameterHomes := [], staticSites := [],
    declared :=
      { parameters := [], returnType := .atom CIL.Extraction.runtimeScope "System.Int32" },
    environment := emittedEnvironment, links := [], code := [.call sizeOfInt {}, .ret] }

example : (invoke [emittedSize] 8 0 [] Memory.empty).map Prod.snd = .ok [.scalar (.i32 4)] := by
  exact size_ok (declared := emittedSize.declared) (method := sizeOfInt)
    (environment := emittedEnvironment) (size := 4) rfl (by decide +kernel) .scalar Memory.empty

/-- The signed Int32 offset overload at a Boolean element. -/
private def addBoolean : CIL.Extraction.MethodRef :=
  let element := CIL.Extraction.TypeExpr.atom CIL.Extraction.runtimeScope "System.Boolean"
  let offset := CIL.Extraction.TypeExpr.atom CIL.Extraction.runtimeScope "System.Int32"
  { owner := CIL.Extraction.unsafeOwner, name := name!"Add", hasThis := false,
    genericArity := 1, returnType := .byref element, parameters := [.byref element, offset],
    methodArguments := [element] }

/-- `Unsafe.Add` of a byte element in the form an extraction emits. -/
private def emittedAdd : CIL.Method :=
  { profile := .scalar, returnsValue := true, locals := [], localKinds := [],
    opaqueVectorLocals := [], parameterHomes := [], staticSites := [],
    declared :=
      { parameters := [.byref (.atom CIL.Extraction.runtimeScope "System.Boolean"),
          .atom CIL.Extraction.runtimeScope "System.Int32"],
        returnType := .byref (.atom CIL.Extraction.runtimeScope "System.Boolean") },
    environment := emittedEnvironment, links := [],
    code := [.ldarg 0, .ldarg 1, .call addBoolean {}, .ret] }

/-- Four caller-stack bytes at allocation 0. -/
private def emittedMemory : Memory := { Memory.empty with
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨4, 1, []⟩, true, [4]⟩ else none
  nextIdentity := 1 }

example :
    (invoke [emittedAdd] 8 0 [.reference (.address ⟨0, 2⟩), .scalar (.i32 4294967295)]
      emittedMemory).map Prod.snd = .ok [.reference (.address ⟨0, 1⟩)] ∧
    (invoke [emittedAdd] 8 0 [.reference .null, .scalar (.i32 0)] emittedMemory).map Prod.snd =
      .error ⟨0, 2, .memory .nullDereference .null 0⟩ := by
  exact ⟨add_ok rfl rfl rfl rfl _ _ _ _ _ rfl rfl rfl rfl,
    add_error rfl rfl rfl _ _ _ _ _ rfl rfl rfl rfl⟩

end Tests.UnsafeWrappers
