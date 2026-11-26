import CIL.Safety.StepComposition
import CIL.Extraction.KernelEquation

/-! Managed pointer values retain exact signatures and cannot be forged from integers. An
indirect call selects its body through `indirectTarget`, which a kernel-checked fact decides,
so a call through a pointer with a long owner steps without the elaborator comparing owners. -/

namespace Tests.ManagedPointerValues

open CIL CIL.Safety

private def signature : ManagedSignature :=
  ⟨.primitive .int32, [.primitive .int32]⟩
private def identity : ManagedIdentity := ⟨"Handlers", 1, []⟩
private def other : ManagedIdentity := ⟨"Handlers", 2, []⟩
private def memory : CIL.Safety.Memory :=
  { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }
private def frame : Frame := { activation := 0, locals := [], owned := [] }

/-- A table lookup retains stable identity rather than turning it into a numeric address. -/
theorem table_provenance :
    instruction (.ldelem .i)
      [.scalar (.i32 1),
        .methodTable ⟨signature, some #[other, identity], none, 2, by decide⟩] memory =
        .ok (memory, [.methodPointer ⟨signature, some identity⟩]) := rfl
#print axioms table_provenance

/-- The typed `ldelem` of a table's own pointer type reads the same entry; an element type of
    another signature is an ill-typed state, and a null table throws the named access fault. -/
theorem typed_table_provenance :
    typedElementInstruction (.method signature) false
      [.scalar (.i32 1),
        .methodTable ⟨signature, some #[other, identity], none, 2, by decide⟩] memory =
        .ok (memory, [.methodPointer ⟨signature, some identity⟩]) ∧
    typedElementInstruction (.method ⟨signature.result, []⟩) false
      [.scalar (.i32 1),
        .methodTable ⟨signature, some #[other, identity], none, 2, by decide⟩] memory =
        .error .invalidState ∧
    typedElementInstruction (.method signature) false [.scalar (.i32 0), .object .null] memory =
      .error (.thrown .nullReference) ∧
    typedElementInstruction (.method signature) true
      [.methodPointer ⟨signature, some identity⟩, .scalar (.i32 1),
        .methodTable ⟨signature, some #[other, identity], none, 2, by decide⟩] memory =
        .error .invalidState :=
  ⟨rfl, rfl, rfl, rfl⟩
#print axioms typed_table_provenance

/-- A numerical value is never callable, even when it equals an admitted program index. -/
theorem numeric_pointer_rejected :
    calliStep signature true (some (.indirect [⟨identity, 1⟩])) frame
      [.scalar (.i64 1), .scalar (.i32 42)] memory = .error .invalidState := rfl
#print axioms numeric_pointer_rejected

/-- A well-typed pointer still needs its exact identity in the admitted target catalog. -/
theorem foreign_target_rejected :
    calliStep signature true (some (.indirect [⟨identity, 1⟩])) frame
      [.methodPointer ⟨signature, some other⟩, .scalar (.i32 42)] memory =
        .error .invalidState := rfl
#print axioms foreign_target_rejected

/-- A successful indirect tail call uses the existing frame-retiring driver action. -/
theorem checked_tail_target :
    calliStep signature true (some (.indirect [⟨identity, 1⟩])) frame
      [.methodPointer ⟨signature, some identity⟩, .scalar (.i32 42)] memory =
        .ok (.tailCall 1 [.scalar (.i32 42)] memory) := rfl
#print axioms checked_tail_target

/-- A null array an ordinary helper returns in place of a table throws the named access fault
    from `ldlen`, and from `ldelem.i` at a well-formed index; at an index of another width
    `ldelem.i` is an ill-typed state, as for a null value array. -/
theorem literal_null_table_rejected :
    instruction .ldlen [.object .null] memory = .error (.thrown .nullReference) ∧
    instruction (.ldelem .i) [.scalar (.i32 0), .object .null] memory =
      .error (.thrown .nullReference) ∧
    instruction (.ldelem .i) [.scalar (.i8 0), .object .null] memory = .error .invalidState :=
  ⟨rfl, rfl, rfl⟩
#print axioms literal_null_table_rejected

/-- The selection `indirectTarget` names is the comparison the call arm made in place over the
    catalog of the site's link: a pointer of another signature, a null pointer and a target
    outside the catalog all fault alike. -/
theorem call_selection_unchanged (signature : ManagedSignature)
    (catalog : List ManagedTarget) (tail : Bool) (frame : Frame)
    (pointer : MethodPointer) (values : List CIL.Safety.Value) (memory : CIL.Safety.Memory) :
    calliStep signature tail (some (.indirect catalog)) frame
        (.methodPointer pointer :: values) memory =
      (do
        if pointer.signature != signature then .error .invalidState else pure ()
        let some identity := pointer.target | .error .invalidState
        let some target := catalog.find? (·.identity == identity) | .error .invalidState
        let count := signature.parameters.length
        if (if tail then values.length != count else values.length < count) then
          .error .invalidState else pure ()
        let arguments ← (values.take count).reverse.mapM (callArgument frame memory)
        if tail then return FrameAction.tailCall target.method arguments memory
        else return .call target.method arguments (values.drop count) memory) := by
  simp only [calliStep, indirectTarget]
  cases pointer.signature != signature with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases pointer.target with
    | none => rfl
    | some identity =>
      simp only [Option.bind]
      cases catalog.find? (·.identity == identity) <;> rfl
#print axioms call_selection_unchanged

/-- An owner of 400 bytes: an assembly-qualified generic type over three assembly-qualified
    arguments, longer than the elaborator can compare within its recursion limit. -/
private def longIdentity : ManagedIdentity :=
  ⟨"Examples, Version=1.0.0.0, Culture=neutral, \
      PublicKeyToken=null::Examples.Dispatching.IndirectHandlers`3<System.Runtime, \
      Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a::System.UInt64,\
      System.Runtime, Version=11.0.0.0, Culture=neutral, \
      PublicKeyToken=b03f5f7f11d50a3a::System.UInt64,System.Runtime, Version=11.0.0.0, \
      Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a::System.Boolean>", 6, []⟩

/-- A catalog whose second entry is the long owner's body, method 1. -/
private def longCatalog : List ManagedTarget := [⟨other, 2⟩, ⟨longIdentity, 1⟩]

/-- A body for the step; the indirect call arm reads only its link at pc 1. -/
private def caller : Method :=
  { returnsValue := true, locals := [], code := [], links := [(1, .indirect longCatalog)] }

/-- The call site's link, as an extraction states it. -/
private theorem caller_link : caller.linkAt 1 = some (.indirect longCatalog) := rfl

/-- The call site's signature takes one argument. -/
private theorem parameter_count : signature.parameters.length = 1 := rfl

/-- The kernel decides the selection. Closed by `rfl`, the same statement stops at the
    elaborator's recursion limit while it compares the two owners. -/
private theorem long_selected :
    indirectTarget signature longCatalog ⟨signature, some longIdentity⟩ = some 1 := by
  cil_kernel_rfl
#print axioms long_selected

/-- A call through a pointer to the long owner steps by `step_managed_call_eq` and the kernel's
    fact, whatever lies below its argument. -/
theorem long_owner_call (rest : List CIL.Safety.Value) :
    step caller (.calli signature false) 1 [] frame
      (.methodPointer ⟨signature, some longIdentity⟩ :: .scalar (.i32 42) :: rest) memory =
      .ok (.call 1 [.scalar (.i32 42)] rest memory) := by
  simp only [cil_step, caller_link, long_selected, parameter_count]
  simp [unspecifiedOperands, CIL.Safety.Value.hasUnspecified, CIL.Value.hasUnspecified]
  rfl
#print axioms long_owner_call

/-- A program whose entry takes the long owner's address and calls it through the pointer. -/
private def longProgram : Program :=
  [{ returnsValue := true, locals := [],
      links := [(1, .address 1), (2, .indirect longCatalog)],
      code := [.ldarg 0, .ldftn longIdentity signature,
        .calli signature false, .ret] },
    { returnsValue := true, locals := [], code := [.ldarg 0, .ret] }]

/-- A whole run through the long owner, closed as an extraction's proofs of indirect calls are:
    the kernel evaluates the run, including both owner comparisons. -/
theorem long_owner_run :
    (invoke longProgram 16 0 [.scalar (.i32 42)] Memory.empty).map Prod.snd =
      .ok [.scalar (.i32 42)] := by
  cil_kernel_rfl
#print axioms long_owner_run

end Tests.ManagedPointerValues
