import CIL.Extraction.DecodedMethod
import CIL.Extraction.Features
import CIL.Safety.CallComposition
import CIL.Safety.ExecutionLifetime
import CIL.Safety.ObjectSteps

set_option maxRecDepth 4096

/-! Certificate regression fixtures, evaluated against the checked CIL extraction model. -/

namespace Tests.ThrowEvidence
open CIL CIL.Extraction

/-- The primitive assembly identity with its checked byte representation. -/
private def runtime := runtimeScope
private def owner := "Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def intType : TypeExpr := .primitive .int32

private def ctor (scope type : String) (parameters : Nat) : RawOperand := .call {
  declared := {
    convention := 0x20,
    parameters := List.replicate parameters (.object runtime "System.String") },
  method := {
    owner := .atom scope type, name := name!".ctor", hasThis := true, genericArity := 0,
    returnType := .void,
    parameters := List.replicate parameters (.object runtime "System.String") },
  name := ".ctor",
  target := .external (scope ++ "::System.Void " ++ type ++ "::.ctor(" ++
    ",".intercalate (List.replicate parameters "System.String") ++ ")"), typeArguments := [],
  parameterCount := parameters, returnsValue := false }
private def argument := ctor runtime "System.ArgumentException" 1
private def divide := ctor runtime "System.DivideByZeroException" 0

private def i (opcode : Nat) (operand : RawOperand := .none) : RawInstruction := ⟨0, opcode, operand⟩
private def raw (code : List RawInstruction) : RawMethod := {
  token := 1, owner := owner ++ "::Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := intType, parameters := [intType], locals := [], initLocals := true, maxStack := 8,
  genericParameters := [], code }
private def state (stack : List (Option W32)) : Option FeatureState := some ⟨stack, []⟩

-- The exact encoding folds; extra loads, a wrong arity or a non-runtime type do not.
example (message : String) : foldRoles [i 114 (.text message), i 115 argument, i 122] =
    [some .head, some .interior, some (.raise .argument)] := rfl
example : foldRoles [i 115 divide, i 122] = [some .head, some (.raise .divideByZero)] := by
  decide
example (message : String) : foldRoles [i 20, i 114 (.text message), i 115 argument, i 122] =
    [none, some .head, some .interior, some (.raise .argument)] := rfl
example : throwFold [i 115 argument, i 122] = none := by decide
example : throwFold [i 115 (ctor owner "Fixture.Failure" 0), i 122] = none := by decide
example : throwFold [i 115 divide, i 38, i 122] = none := by decide

/-- A throw message has the operand of a string or null load. -/
theorem message_operands (text : String) :
    throwFold [i 114, i 115 argument, i 122] = none ∧
    throwFold [i 20 (.text text), i 115 argument, i 122] = none := ⟨rfl, rfl⟩
#print axioms message_operands

/-- An ordinary string load retains its text, while the thrown type is independent of the message. -/
theorem string_and_throw (ordinary message : String) :
    let closed := raw [i 114 (.text ordinary), i 38, i 114 (.text message), i 115 argument, i 122]
    methodCode .scalar {} [] (List.replicate 5 true) closed =
      [.ldstr ordinary, .pop, .nop, .nop, .throw (some .argument)] := rfl
#print axioms string_and_throw

/-- The two string loads and constructor preceding the range exception's throw. -/
private def rangeCode (parameterName message : String) : List Instruction :=
  let constructor := ctor runtime "System.ArgumentOutOfRangeException" 2
  let closed := raw [i 114 (.text parameterName), i 114 (.text message), i 115 constructor, i 122]
  methodCode .scalar {} [] (List.replicate 4 true) closed

/-- Every parameter name and message yield the same range exception at the original throw. -/
theorem range_throw (parameterName message : String) (memory : Safety.Memory) :
    let method : Method := {
      code := rangeCode parameterName message
      locals := []
      returnsValue := false }
    Safety.invoke [method] 5 0 [] memory = .error ⟨0, 3, .thrown .argumentOutOfRange⟩ := rfl
#print axioms range_throw

/-- Rejecting an oversized message prefix still discovers an admitted fold in its suffix. -/
theorem long_prefix_suffix :
    foldRoles ([i 20, i 20, i 20] ++
      [i 115 (ctor runtime "System.ArgumentException" 2), i 122]) =
      [none, some .head, some .interior, some .interior,
        some (.raise .argument)] := by decide +kernel
#print axioms long_prefix_suffix

/-- A long message-only body never invents a constructor or throw. -/
theorem message_only_body : foldRoles (List.replicate 128 (i 20)) =
    List.replicate 128 none := by decide +kernel
#print axioms message_only_body

theorem rejects_non_exception : throwFold [i 115 (ctor runtime "System.Object" 0), i 122] = none := by decide
#print axioms rejects_non_exception

theorem rejects_missing_constructor (first second : String) :
    throwFold [i 114 (.text first), i 114 (.text second), i 115 (ctor runtime "System.DivideByZeroException" 2), i 122] = none := rfl
#print axioms rejects_missing_constructor

private def wrongParameter : RawOperand := .call {
  declared := { convention := 0x20, parameters := [intType] },
  method := {
    owner := .atom runtime "System.DivideByZeroException", name := name!".ctor", hasThis := true,
    genericArity := 0, returnType := .void, parameters := [] },
  name := ".ctor",
  target := .external (runtime ++ "::System.Void System.DivideByZeroException::.ctor(\
    System.Int32)"),
  typeArguments := [], parameterCount := 1, returnsValue := false }

/-- A constructor whose declared parameter count differs from its closed parameters is refused. -/
theorem rejects_parameter_count (message : String) :
    throwFold [i 114 (.text message), i 115 wrongParameter, i 122] = none := rfl
#print axioms rejects_parameter_count

/-- The call operand with one field of its site changed. -/
private def changeSite (operand : RawOperand) (change : CallSite → CallSite) : RawOperand :=
  match operand with
  | .call site => .call (change site)
  | other => other

/-- Changes to a nongeneric exception constructor that retain the printed external target. -/
private def alteredConstructors : List RawOperand := [
  changeSite divide fun site => { site with declared.convention := 0x25 },
  changeSite divide fun site => { site with declared.convention := 0x60 },
  changeSite divide fun site => { site with declared.returnType := intType },
  changeSite divide fun site => { site with declared.parameters := [intType] },
  changeSite divide fun site => { site with method.genericArity := 1 },
  changeSite divide fun site => { site with method.methodArguments := [intType] },
  changeSite divide fun site => { site with ownerArgumentCount := 1 },
  changeSite divide fun site => { site with staticVirtualInterfaceSlot := true }]

/-- The ordinary instance signature is required at the instruction that constructs the exception. -/
theorem exact_exception_signatures :
    throwFold [i 115 divide, i 122] = some (0, .divideByZero) ∧
    alteredConstructors.all (fun operand => (throwFold [i 115 operand, i 122]).isNone) := by
  decide +kernel
#print axioms exact_exception_signatures

/-- The checked feature flow accepts the ordinary constructor and refuses each altered MemberRef. -/
theorem exact_exception_certificate :
    let accepts := fun operand => FeatureFlowValid #[] (fun _ => none) (fun _ => none)
      (raw [i 115 operand, i 122]) .scalar [state [], state [none]] [true, true]
      [.nop, .throw (some .divideByZero)]
    accepts divide ∧ ∀ operand ∈ alteredConstructors, ¬ accepts operand := by decide +kernel
#print axioms exact_exception_certificate

/-- An Int32 parameter outside the allowlisted constructor signatures is refused. -/
theorem rejects_int32_parameter (message : String) :
    throwFold [i 114 (.text message), i 115 (changeSite wrongParameter fun site =>
      { site with method.parameters := [intType] }), i 122] = none := rfl
#print axioms rejects_int32_parameter

/-- An allowlisted exception name in another scope raises nothing, whether the owner or the
    external target names the other scope. -/
theorem rejects_foreign_exception :
    throwFold [i 115 (ctor "Fixture" "System.DivideByZeroException" 0), i 122] = none ∧
    throwFold [i 115 (changeSite divide fun site =>
      { site with method.owner := .atom "Fixture" "System.DivideByZeroException" }), i 122] =
      none := by decide
#print axioms rejects_foreign_exception

/-- The constructor is identified by its metadata name, so a site whose display text alone says
    .ctor raises nothing. -/
theorem rejects_named_other_member :
    throwFold [i 115 divide, i 122] = some (0, .divideByZero) ∧
    throwFold [i 115 (changeSite divide fun site =>
      { site with method.name := name!"Other" }), i 122] = none := by decide
#print axioms rejects_named_other_member

theorem accepts_two_strings (message : String) :
    throwFold [i 20, i 114 (.text message), i 115 (ctor runtime "System.ArgumentOutOfRangeException" 2), i 122] =
      some (2, .argumentOutOfRange) := rfl
#print axioms accepts_two_strings

theorem rejects_non_exception_certificate :
    ∀ claimed ∈ ExceptionType.all, ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none)
        (raw [i 115 (ctor runtime "System.Object" 0), i 122]) .scalar
      [state [], state [none]] [true, true] [.nop, .throw claimed] := by decide +kernel
#print axioms rejects_non_exception_certificate

-- 0: ldarg.0; 1: brtrue 5; 2: ldstr; 3: newobj ArgumentException(string); 4: throw; 5: ldarg.0; 6: ret
private def guardRaw (message : String) := raw [i 2, i 45 (.target 5), i 114 (.text message), i 115 argument, i 122, i 2, i 42]
private def guardStates : FeatureCertificate :=
  [state [], state [none], state [], state [none], state [none], state [], state [none]]
private def guardCode : List Instruction :=
  [.ldarg 0, .brtrue 5, .nop, .nop, .throw (some .argument), .ldarg 0, .ret]

example (message : String) : FeatureFlowValid #[] (fun _ => none) (fun _ => none) (guardRaw message) .scalar guardStates
    (List.replicate 7 true) guardCode := by
  apply of_decide_eq_true
  with_unfolding_all rfl
-- The raised type is the constructed one, and the fold cannot be emitted as a hole.
set_option maxHeartbeats 1500000 in
example (message : String) : ∀ other ∈ ExceptionType.all, other ≠ .argument → ¬ FeatureFlowValid #[] (fun _ => none)
    (fun _ => none)
    (guardRaw message) .scalar guardStates (List.replicate 7 true)
    (guardCode.set 4 (.throw other)) := by
  apply of_decide_eq_true
  with_unfolding_all rfl
example (message : String) : ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none)
    (guardRaw message) .scalar guardStates (List.replicate 7 true)
    (guardCode.set 4 (.unadmitted 122)) := by
  apply of_decide_eq_true
  with_unfolding_all rfl

-- A branch to the raw `throw` would raise whatever object it carries, so it is rejected.
private def enteredRaw (message : String) := raw [i 2, i 37, i 45 (.target 6), i 38, i 114 (.text message), i 115 argument, i 122]
example (message : String) : ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) (enteredRaw message) .scalar
    [state [], state [none], state [none, none], state [none], state [], state [none], state [none]]
    (List.replicate 7 true) [.ldarg 0, .dup, .brtrue 6, .pop, .nop, .nop,
        .throw (some .argument)] := by
  apply of_decide_eq_true
  with_unfolding_all rfl

/-- The raw decoder binds the null load and the throw independently, including a separated pair. -/
theorem null_throw_encoding (text : String) :
    foldRoles [i 20, i 122] = [none, none] ∧
    FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [i 20, i 122]) .scalar
      [state [], state [none]] [true, true] [.ldnull, .throw] ∧
    ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [i 20, i 122]) .scalar
      [state [], state [none]] [true, true] [.nop, .throw] ∧
    ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [i 22, i 122]) .scalar
      [state [], state [some 0]] [true, true] [.ldnull, .throw] ∧
    ¬ FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [i 20 (.text text), i 122])
      .scalar
      [state [], state [none]] [true, true] [.ldnull, .throw] ∧
    FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw [i 20, i 0, i 122]) .scalar
      [state [], state [none], state [none]] [true, true, true]
      [.ldnull, .nop, .throw] := by
  apply of_decide_eq_true
  with_unfolding_all rfl
#print axioms null_throw_encoding


/-- A branch can carry an already loaded null directly to the throw instruction. -/
theorem null_throw_entry :
    FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw
      [i 20, i 43 (.target 2), i 20, i 122]) .scalar
      [state [], state [none], state [none], state [none, none]]
      [true, true, true, true]
      [.ldnull, .br 2, .ldnull, .throw] ∧
    FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw
      [i 20, i 43 (.target 3), i 20, i 122]) .scalar
      [state [], state [none], none, state [none]] [true, true, false, true]
      [.ldnull, .br 3, .unadmitted 20, .throw] :=
  by decide +kernel
#print axioms null_throw_entry

/-- A direct edge or switch arm into the throw disables just the entered fold. -/
theorem decoded_throw_entry :
    let source := fun edge => raw
      [i 2, i 45 (.target 4), i 20, edge, i 115 divide, i 122, i 115 divide, i 122]
    let mask := List.replicate 8 true
    let decode := fun edge => (Method.ofRaw? .scalar {} [] mask (source edge) []).map
      fun body => (body.code[5]?, body.code[7]?)
    let refused := fun edge =>
      let code := methodCode .scalar {} [] mask (source edge)
      decode edge = none ∧ code[5]? = some (.unadmitted 122) ∧
        code[7]? = some (.throw (some .divideByZero))
    let raised := some (Instruction.throw (some .divideByZero))
    decode (i 43 (.target 4)) = some (raised, raised) ∧
      refused (i 43 (.target 5)) ∧ refused (i 69 (.targets [4, 5])) := by decide +kernel

#print axioms decoded_throw_entry

-- A bare throw cannot carry a folded type, including NullReferenceException itself.
example : ∀ kind ∈ ExceptionType.all, ¬ FeatureFlowValid #[]
    (fun _ => none) (fun _ => none) (raw [i 20, i 122]) .scalar [state [], state [none]] [true,
      true]
    [.ldnull, .throw (some kind)] := by decide +kernel

/-- Types outside the constructor allowlist cannot form a throw fold. -/
theorem rejects_unadmitted_owners :
    foldRoles [i 115 (ctor runtime "System.PlatformNotSupportedException" 0), i 122] =
      [none, none] ∧
    foldRoles [i 115 (ctor runtime "System.InvalidCastException" 0), i 122] = [none, none] ∧
    exceptionOwner? (.atom runtimeScope "System.Object") = none := by decide +kernel
#print axioms rejects_unadmitted_owners

section
open CIL.Safety

/-- A live object pushed by a string load is a valid constructor argument. -/
private theorem argument_of_literal {text : String} {memory : Safety.Memory}
    {reference : Reference} (frame : Safety.Frame)
    (loaded : stringLiteralInstruction text [] memory =
      .ok (memory, [.object (.address reference)])) :
    callArgument frame memory (.object (.address reference)) =
      .ok (.object (.address reference)) := by
  cases bound : memory.literals.lookup text with
  | none => simp [stringLiteralInstruction, literalObject, bound, bind, Except.bind] at loaded
  | some actual =>
    cases formed : formObject memory (.address actual) with
    | error fault =>
      simp [stringLiteralInstruction, literalObject, bound, formed, bind, Except.bind] at loaded
    | ok value =>
      have same := formObject_returns_input formed
      subst value
      have equal : actual = reference := by
        simpa [stringLiteralInstruction, literalObject, bound, formed, bind, Except.bind,
          pure, Except.pure] using loaded
      subst actual
      exact callArgument_of_checked (checkedValue_object memory _ formed)
#print axioms argument_of_literal

/-- Once both literal arguments load, a linked class constructor still needs space for its
    instance. With zero modeled heap budget the original newobj fails before the constructor. -/
theorem literal_constructor_allocation (name message : String) (nameRef messageRef : Reference)
    (memory : Safety.Memory) (budget : memory.heapBudget = some 0) (method : MethodRef)
    (arguments : method.parameters.length = 2) (constructor : Nat) (bases : List TypeExpr)
    (size : Nat) (positive : 0 < size) (body : Method) (pc : Nat) (frame : Safety.Frame)
    (nameLoaded : stringLiteralInstruction name [] memory =
      .ok (memory, [.object (.address nameRef)]))
    (messageLoaded : stringLiteralInstruction message [] memory =
      .ok (memory, [.object (.address messageRef)])) :
    newobjStep (some (.object constructor bases size)) method body pc frame
      [.object (.address messageRef), .object (.address nameRef)] memory =
      .error (.allocationFailure size 0) := by
  have firstArg := argument_of_literal frame nameLoaded
  have secondArg := argument_of_literal frame messageLoaded
  simp [newobjStep, arguments, constructObject, firstArg, secondArg, allocateObject, budget,
    positive, List.mapM_cons, List.mapM_nil, bind, Except.bind, pure, Except.pure]
#print axioms literal_constructor_allocation

/-- The two literal loads, linked constructor call and raw throw raise the owner's exception
    if both literals load, the instance fits and the constructor returns normally. -/
theorem literal_constructor_throw (program : CIL.Program) (entry pc callee fuel : Nat)
    (body : Method) (method : MethodRef) (bases : List TypeExpr) (size : Nat)
    (frame : Safety.Frame) (args : List Safety.Value) (memory final : Safety.Memory)
    (name message : String) (nameRef messageRef : Reference) (raised : ExceptionType)
    (found : program[entry]? = some body) (first : body.code[pc]? = some (.ldstr name))
    (second : body.code[pc + 1]? = some (.ldstr message))
    (construct : body.code[pc + 2]? = some (.newobj method))
    (linked : body.linkAt (pc + 2) = some (.object callee bases size))
    (throws : body.code[pc + 3]? = some .throw) (arity : method.parameters.length = 2)
    (owner : runtimeException? method.owner = some raised)
    (formed : memory.WellFormed) (affordable : size ≤ memory.heapBudget.getD size)
    (bounded : size < nativeLimit)
    (nameLoaded : literalObject memory name = .ok (.object (.address nameRef)))
    (messageLoaded : literalObject memory message = .ok (.object (.address messageRef)))
    (returned : invoke program (fuel + 1) callee
      [.object (.address ⟨memory.nextIdentity, 0⟩), .object (.address nameRef),
       .object (.address messageRef)] (objectMemory memory ⟨method.owner, bases⟩ size) =
        .ok (final, []))
        (free : HandlerFree program := by handler_free) :
    run program (fuel + 4) entry pc args frame [] memory =
      .error ⟨entry, pc + 3, .thrown raised⟩ := by
  let receiver : Reference := ⟨memory.nextIdentity, 0⟩
  let created : Safety.Value := .object (.address receiver)
  let allocated := objectMemory memory ⟨method.owner, bases⟩ size
  have load (site : Nat) (stack : List Safety.Value) (text : String) (reference : Reference)
      (bound : literalObject memory text = .ok (.object (.address reference))) :
      step body (.ldstr text) site args frame stack memory =
        .ok (.next (site + 1) (.object (.address reference) :: stack) frame memory) := by
    rw [step_ldstr_eq, bound]
    rfl
  have argument (text : String) (reference : Reference)
      (bound : literalObject memory text = .ok (.object (.address reference))) :=
    argument_of_literal frame (text := text) (memory := memory) (reference := reference)
      (by rw [stringLiteralInstruction, bound]; rfl)
  rw [run_next found first (load pc [] name nameRef nameLoaded)]
  rw [run_next found second (load (pc + 1) _ message messageRef messageLoaded)]
  have make : step body (.newobj method) (pc + 2) args frame
      [.object (.address messageRef), .object (.address nameRef)] memory =
        .ok (.call callee [created, .object (.address nameRef), .object (.address messageRef)]
          [created] allocated) := by
    simp [step_newobj_eq, linked, arity, unspecifiedOperands, Safety.Value.hasUnspecified,
      argument _ _ nameLoaded, argument _ _ messageLoaded,
      allocateObject_ok formed _ affordable bounded, created, receiver,
      allocated, List.mapM_cons, List.mapM_nil, bind, Except.bind, pure, Except.pure]
  apply run_call_of_invoke found construct make returned
  have kept := (invoke_preserves_caller_allocations _ _ _ _ _ _ _ returned).lookup
    memory.nextIdentity (by simp [objectMemory])
  have object : ExceptionObject final receiver raised := by
    refine ⟨rfl, ⟨⟨method.owner, bases⟩, ?_, owner⟩⟩
    simp [runtimeTypeOf, receiver, liveAllocation, kept, objectMemory, checkedAt,
      bind, Except.bind, pure, Except.pure, Except.mapError]
  have fault := object.thrown []
  change run program (fuel + 1) entry (pc + 3) args frame [created] final = _
  simp only [run_succ _ _ _ _ _ _ _ _ (free.unprotected entry (pc + 3)), found, throws]
  change Except.error (α := Safety.Memory × List Safety.Value)
    (LocatedFault.mk entry (pc + 3) (throwFault final [created])) = _
  rw [fault]

#print axioms literal_constructor_throw

/-- A method body with the given evaluation-stack instructions. -/
private def throwBody (ops : List Instruction) : Method :=
  { code := ops, locals := [], returnsValue := false }

/-- A displaced throw raises at its own pc and accepts null across a control-flow edge. -/
theorem null_sites :
    invoke [throwBody [.ldnull, .nop, .throw]] 12 0 [] Safety.Memory.empty =
      .error ⟨0, 2, .thrown .nullReference⟩ ∧
    invoke [throwBody [.ldnull, .br 3, .unadmitted 0, .throw]] 12 0 [] Safety.Memory.empty =
      .error ⟨0, 3, .thrown .nullReference⟩ ∧
    invoke [throwBody [.throw]] 12 0 [] Safety.Memory.empty = .error ⟨0, 0, .invalidState⟩ ∧
    invoke [throwBody [.ldc_i4 1, .throw]] 12 0 [] Safety.Memory.empty =
      .error ⟨0, 1, .invalidState⟩ := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms null_sites

/-- One live object of the supplied runtime class. -/
private def exceptionMemory (type : TypeExpr) : Safety.Memory :=
  { Safety.Memory.empty with
    nextIdentity := 1
    allocations := fun id => if id = 0 then some ⟨.object ⟨type, []⟩, ⟨8, 8, []⟩, true, []⟩
      else none }

/-- A CoreLib exception raises its type. A caller's same-named class is inconclusive. -/
theorem scoped_object :
    let raise := fun type => invoke [throwBody [.ldarg 0, .throw]] 12 0
      [.object (.address ⟨0, 0⟩)] (exceptionMemory type)
    raise (.object coreLibraryScope "System.ArgumentException") =
      .error ⟨0, 1, .thrown .argument⟩ ∧
    (raise (.object "Other" "System.ArgumentException") matches
      .error ⟨0, 1, .unsupported _⟩) = true := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms scoped_object
end

end Tests.ThrowEvidence
