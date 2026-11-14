import CIL.Safety.ObjectSteps
import CIL.Safety.ObjectFields
import CIL.Safety.ReferenceSegments
import CIL.Safety.ClassCatalog
import CIL.Safety.SymbolicExecution
import CIL.Observe

/-! Object references form only at offset 0 of a live object allocation, compare by identity
    and test presence only against null, and reach fields only of their own runtime type; every
    other shape is rejected. A proof stuck on an object step names the object fact it lacks in its
    failure record. -/

namespace Tests.Objects

open CIL CIL.Safety

private def account : RuntimeType := ⟨.object "Examples" "Examples.Account", []⟩

/-- Allocation 0 holds an object, 1 is an expired object and 2 is a caller stack buffer. -/
private def memory : CIL.Safety.Memory :=
  { allocations := fun identity => match identity with
      | 0 => some ⟨.object account, ⟨0, 1, []⟩, true, []⟩
      | 1 => some ⟨.object account, ⟨0, 1, []⟩, false, []⟩
      | 2 => some ⟨.callerStack, ⟨8, 1, []⟩, true, []⟩
      | _ => none
    cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 3 }
private def frame : Frame := { activation := 0, locals := [], owned := [] }
private def body : CIL.Method := { returnsValue := true, locals := [], code := [] }
private def live : ManagedReference := .address ⟨0, 0⟩

/-- A live object allocation at offset 0 forms as itself. -/
theorem live_object_forms : formObject memory live = .ok (.object live) := rfl
#print axioms live_object_forms

/-- An interior offset of an object allocation is not an object reference. -/
theorem interior_offset_rejected :
    formObject memory (.address ⟨0, 1⟩) = .error .invalidState := rfl
#print axioms interior_offset_rejected

/-- A byte buffer cannot be reinterpreted as an object. -/
theorem buffer_not_object :
    formObject memory (.address ⟨2, 0⟩) = .error .invalidState := rfl
#print axioms buffer_not_object

/-- An expired object faults with the allocation's lifetime rule. -/
theorem expired_object_faults :
    formObject memory (.address ⟨1, 0⟩) =
      .error (.memory .expiredLifetime (.address ⟨1, 0⟩) 0) := rfl
#print axioms expired_object_faults

/-- `ceq` of an object with itself is 1 and with null is 0. -/
theorem identity_comparisons :
    CIL.Safety.step body .ceq 0 [] frame [.object live, .object live] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) ∧
    CIL.Safety.step body .ceq 0 [] frame [.object .null, .object live] memory =
      .ok (.next 1 [.scalar (.i32 0)] frame memory) := ⟨rfl, rfl⟩
#print axioms identity_comparisons

/-- `cgt.un` on two objects is defined only against null. -/
theorem ordering_rejected :
    CIL.Safety.step body .cgt_un 0 [] frame [.object live, .object live] memory =
      .error .invalidState := rfl
#print axioms ordering_rejected

/-- Object and byref nulls are distinct: neither compares with the other. -/
theorem byref_null_not_object :
    CIL.Safety.step body .ceq 0 [] frame [.object .null, .reference .null] memory =
      .error .invalidState ∧
    storeLocal memory (.object none) (.reference .null) = .error .invalidState := ⟨rfl, rfl⟩
#print axioms byref_null_not_object

/-- An object home never exposes an address. -/
theorem object_local_has_no_address :
    localAddress memory (.object (some live)) =
      .error (.unsupported "Address of object reference local") := rfl
#print axioms object_local_has_no_address

/-- A field access checks the object's runtime type against the field's declaring class. -/
theorem field_owner_checked :
    objectFieldAddress memory live (.object "Examples" "Examples.Other") 0 =
      .error (.unsupported "Field owner is not the object's class or a base of it") := rfl
#print axioms field_owner_checked

private def shape : CIL.Extraction.TypeExpr := .object "Examples" "Examples.Shape"
private def circle : RuntimeType := ⟨.object "Examples" "Examples.Circle", [shape]⟩

/-- Allocation 0 is a 16-byte `Circle` deriving from `Shape`; allocation 1 a bare `Shape`. -/
private def shapes : CIL.Safety.Memory :=
  { allocations := fun identity => match identity with
      | 0 => some ⟨.object circle, ⟨16, 8, []⟩, true, [16]⟩
      | 1 => some ⟨.object ⟨shape, []⟩, ⟨8, 8, []⟩, true, [8]⟩
      | _ => none
    cells := fun _ _ => ⟨0, true⟩, views := [], nextIdentity := 2 }

/-- A derived instance reaches the fields its base declares and its own; an instance of the base
    reaches no field the derived class declares. -/
theorem base_fields_reached :
    objectFieldAddress shapes (.address ⟨0, 0⟩) shape 0 = .ok ⟨0, 0⟩ ∧
    objectFieldAddress shapes (.address ⟨0, 0⟩) circle.identity 8 = .ok ⟨0, 8⟩ ∧
    objectFieldAddress shapes (.address ⟨1, 0⟩) circle.identity 8 =
      .error (.unsupported "Field owner is not the object's class or a base of it") :=
  ⟨rfl, rfl, rfl⟩
#print axioms base_fields_reached

/-- A field access through null throws, as `ldfld` and `stfld` do at run time. -/
theorem null_field_throws :
    objectFieldAddress memory .null account.identity 0 =
      .error (.thrown "System.NullReferenceException") := rfl
#print axioms null_field_throws

/-- Byte storage that is not an object has no fields, whatever offset is asked for. -/
theorem buffer_has_no_fields :
    objectFieldAddress memory (.address ⟨2, 0⟩) account.identity 0 = .error .invalidState := rfl
#print axioms buffer_has_no_fields

/-- Caller memory granting 16 bytes of object budget and no other storage. -/
private def budgeted : CIL.Safety.Memory := { memory with heapBudget := 16 }

/-- An allocation within budget takes the next identity and consumes its size. -/
theorem allocation_charges_budget :
    (allocateObject budgeted account 8).map (fun result => (result.1, result.2.heapBudget,
      result.2.nextIdentity)) = .ok (⟨3, 0⟩, 8, 4) := rfl
#print axioms allocation_charges_budget

/-- An allocation over budget fails with the model resource fault, not a CLR exception. -/
theorem allocation_over_budget :
    allocateObject budgeted account 24 = .error (.allocationFailure 24 16) := rfl
#print axioms allocation_over_budget

/-- `newobj` with no arguments calls constructor 1 with the fresh instance as its receiver,
    which then also waits on the caller's stack. -/
private def creator : CIL.Method :=
  { returnsValue := true, locals := [],
    code := [.newObject 1 0 account.identity [] 8, .ret none] }
private def constructor : CIL.Method :=
  { returnsValue := false, locals := [], code := [.ret none] }

/-- The constructed instance is returned to the caller and outlives the constructor's frame. -/
theorem construction_returns_instance :
    (invoke [creator, constructor] 8 0 [] budgeted).map Prod.snd =
      .ok [.object (.address ⟨3, 0⟩)] := rfl
#print axioms construction_returns_instance

/-- Without budget the construction stops at `newobj`, before the constructor runs. -/
theorem construction_over_budget :
    invoke [creator, constructor] 8 0 [] memory = .error ⟨0, 0, .allocationFailure 8 0⟩ := rfl
#print axioms construction_over_budget

private def node : RuntimeType := ⟨.object "Examples" "Examples.Node", []⟩

/-- Allocations 0 and 1 are 16-byte nodes, 1 read-only; 2 is a caller stack buffer. -/
private def nodes : CIL.Safety.Memory :=
  { allocations := fun identity => match identity with
      | 0 | 1 => some ⟨.object node, ⟨16, 8, []⟩, true, [16]⟩
      | 2 => some ⟨.callerStack, ⟨8, 1, []⟩, true, []⟩
      | _ => none
    cells := fun _ _ => ⟨0, true⟩
    views := [⟨0, 0, 16, true, true⟩, ⟨1, 0, 16, true, false⟩]
    nextIdentity := 3 }
private def first : ManagedReference := .address ⟨0, 0⟩
private def second : ManagedReference := .address ⟨1, 0⟩

/-- A class-typed field holds the stored reference itself; no byte of the object changes. -/
theorem reference_field_reads_back :
    ((objectFieldInstruction (.setObjectReferenceField node.identity 8)
        [.object second, .object first] nodes).bind fun stored =>
      objectFieldInstruction (.objectReferenceField node.identity 8) [.object first]
        stored.1).map Prod.snd = .ok [.object second] ∧
    (objectFieldInstruction (.setObjectReferenceField node.identity 8)
        [.object second, .object first] nodes).map (fun stored => stored.1.cells 0 8) =
      .ok ⟨0, true⟩ := ⟨rfl, rfl⟩
#print axioms reference_field_reads_back

/-- A fresh field holds null. -/
theorem reference_field_starts_null :
    (objectFieldInstruction (.objectReferenceField node.identity 8) [.object first] nodes).map
      Prod.snd = .ok [.object .null] := rfl
#print axioms reference_field_starts_null

/-- A null receiver throws on both the load and the store, before the value is checked. -/
theorem reference_field_null_receiver_throws :
    objectFieldInstruction (.objectReferenceField node.identity 8) [.object .null] nodes =
      .error (.thrown "System.NullReferenceException") ∧
    objectFieldInstruction (.setObjectReferenceField node.identity 8)
        [.object (.address ⟨2, 0⟩), .object .null] nodes =
      .error (.thrown "System.NullReferenceException") := ⟨rfl, rfl⟩
#print axioms reference_field_null_receiver_throws

/-- Only an object or null may be stored: a byte buffer is not one. -/
theorem reference_field_rejects_buffer :
    objectFieldInstruction (.setObjectReferenceField node.identity 8)
        [.object (.address ⟨2, 0⟩), .object first] nodes = .error .invalidState := rfl
#print axioms reference_field_rejects_buffer

/-- A store needs write authority over the field's slot, and the slot must lie in the object. -/
theorem reference_field_checks_slot :
    objectFieldInstruction (.setObjectReferenceField node.identity 8)
        [.object first, .object second] nodes =
      .error (.memory .unwritable (.address ⟨1, 8⟩) 8) ∧
    objectFieldInstruction (.objectReferenceField node.identity 16) [.object first] nodes =
      .error (.memory .outsideAllocation (.address ⟨0, 16⟩) 8) := ⟨rfl, rfl⟩
#print axioms reference_field_checks_slot

/-! ## Failure records of object steps -/

/-- `callvirt` of method 4 on argument 0. -/
@[cil_code] def depositing : CIL.Method :=
  { returnsValue := false, locals := [], code := [.arg 0, .callInstance 4 1, .ret] }
/-- `ldfld` of a scalar field of argument 0. -/
@[cil_code] def fieldReading : CIL.Method :=
  { returnsValue := true, locals := [],
    code := [.arg 0, .memory (.objectField account.identity 0 8 false), .ret] }
/-- `ldfld` of a class-typed field of argument 0. -/
@[cil_code] def slotReading : CIL.Method :=
  { returnsValue := true, locals := [],
    code := [.arg 0, .memory (.objectReferenceField account.identity 8), .ret] }
/-- `newobj` of an 8-byte instance whose constructor is method 4. -/
@[cil_code] def creating : CIL.Method :=
  { returnsValue := true, locals := [], code := [.newObject 4 0 account.identity [] 8, .ret] }
/-- A constructor or instance method that does nothing. -/
@[cil_code] def doingNothing : CIL.Method :=
  { returnsValue := false, locals := [], code := [.ret] }
/-- The methods above, by index. -/
@[cil_code] def observed : CIL.Program :=
  [depositing, fieldReading, slotReading, creating, doingNothing]

-- A walk stopped at a receiver-checked call lacks the callee's contract, as at a direct call.
/-- "instruction":"CIL.Instruction.callInstance 4 1","method":0,"missing":"calleeContract" -/
#guard_msgs (substring := true) in
set_option cil.diagnostics true in
example (memory : CIL.Safety.Memory) (object : Reference) (frame : Frame)
    (formed : formObject memory (.address object) = .ok (.object (.address object)))
    (result : Except LocatedFault (CIL.Safety.Memory × List CIL.Safety.Value)) :
    run observed 100 0 0 [.object (.address object)] frame [] memory = result := by
  cil_checked_steps 1 [formed]

-- A field load stopped on an unknown object lacks the field's address.
/-- "method":1,"missing":"objectForm" -/
#guard_msgs (substring := true) in
set_option cil.diagnostics true in
example (memory : CIL.Safety.Memory) (object : Reference) (frame : Frame)
    (formed : formObject memory (.address object) = .ok (.object (.address object)))
    (result : Except LocatedFault (CIL.Safety.Memory × List CIL.Safety.Value)) :
    run observed 100 1 0 [.object (.address object)] frame [] memory = result := by
  cil_checked_steps [formed]

-- Given the field's address, a reference field load lacks what its slot holds.
/-- "method":2,"missing":"objectSlot" -/
#guard_msgs (substring := true) in
set_option cil.diagnostics true in
example (memory : CIL.Safety.Memory) (object field : Reference) (frame : Frame)
    (formed : formObject memory (.address object) = .ok (.object (.address object)))
    (located : objectFieldAddress memory (.address object) account.identity 8 = .ok field)
    (result : Except LocatedFault (CIL.Safety.Memory × List CIL.Safety.Value)) :
    run observed 100 2 0 [.object (.address object)] frame [] memory = result := by
  cil_checked_steps [formed, located]

-- A construction lacks the allocation against the heap budget.
/-- "missing":"objectAllocation" -/
#guard_msgs (substring := true) in
set_option cil.diagnostics true in
example (memory : CIL.Safety.Memory) (frame : Frame)
    (result : Except LocatedFault (CIL.Safety.Memory × List CIL.Safety.Value)) :
    run observed 100 3 0 [] frame [] memory = result := by
  cil_checked_steps

-- An invocation lacks the formation of each object argument, which the entry checks.
/-- "instruction":null,"method":0,"missing":"objectForm" -/
#guard_msgs (substring := true) in
set_option cil.diagnostics true in
example (memory : CIL.Safety.Memory) (object : Reference) :
    invoke observed 100 0 [.object (.address object)] memory =
      .error ⟨0, 1, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps

/-- A signed `ldfld` of a 16-bit field holding `0xFFFF` pushes -1, sign-extended to 32 bits, and
    an unsigned one pushes 65535: `signedFacts` and `facts` must not be interchangeable. -/
theorem narrow_field_loads_extend_by_sign {memory : CIL.Safety.Memory} {object : Reference}
    {field : WordField 2} (readable : field.Readable memory object)
    (held : field.of memory object = 0xFFFF) :
    CIL.Safety.step body (.memory (.objectField field.owner field.offset 2 true)) 0 [] frame
        [.object (.address object)] memory =
      .ok (.next 1 [.scalar (.i32 0xFFFFFFFF)] frame memory) ∧
    CIL.Safety.step body (.memory (.objectField field.owner field.offset 2 false)) 0 [] frame
        [.object (.address object)] memory =
      .ok (.next 1 [.scalar (.i32 0xFFFF)] frame memory) := by
  obtain ⟨_, located, signedLoad⟩ := readable.signedFacts
  obtain ⟨_, _, unsignedLoad⟩ := readable.facts
  rw [held] at signedLoad unsignedLoad
  constructor <;> rw [step_objectField_2_eq] <;>
    simp only [located, signedLoad, unsignedLoad, Bind.bind, Except.bind, Pure.pure,
      Except.pure] <;> rfl
#print axioms narrow_field_loads_extend_by_sign

/-- The return check forms an object the method created, or any other object its frame does
    not own, in memory after the frame is left. -/
theorem unowned_object_returns (memory : CIL.Safety.Memory) (object : Reference) (frame : Frame)
    (formed : formObject memory (.address object) = .ok (.object (.address object)))
    (notOwned : object.allocation ∉ frame.owned) :
    [Value.object (.address object)].mapM (checkedValue (leaveFrame frame memory)) =
      .ok [.object (.address object)] := by
  cil_checked_side [formed, notOwned]
#print axioms unowned_object_returns

/-- A method record with no code, owned by `owner`, with the given receiver kind and bases. -/
private def classMethod (owner : String) (receiver : Bool) (bases : List CIL.Extraction.TypeExpr) :
    CIL.Extraction.RawMethod :=
  { token := 0, owner, hasThis := true, explicitThis := false, callingConvention := 0,
    attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
    initLocals := false, maxStack := 0, genericParameters := [], code := [],
    objectReceiver := receiver, objectBases := bases }

/-- A class method's owner `scope::name` declares that class with its bases; an owner without
    exactly one `::`, or a method without an object receiver, declares none. -/
theorem declared_class_read :
    declaredClass (classMethod "Examples::Examples.Circle" true [shape]) = some circle ∧
    declaredClass (classMethod "Examples.Circle" true []) = none ∧
    declaredClass (classMethod "Examples::Outer::Circle" true []) = none ∧
    declaredClass (classMethod "Examples::Examples.Circle" false []) = none := by
  decide +kernel
#print axioms declared_class_read

/-- A derived instance and an instance of its base agree with a catalog naming both. -/
theorem shapes_consistent : shapes.ClassesConsistent [⟨shape, []⟩, circle] := by
  intro id allocation type present kind
  match id, present with
  | 0, present => cases present; cases kind; unfold RuntimeType.ConsistentWith; decide
  | 1, present => cases present; cases kind; unfold RuntimeType.ConsistentWith; decide
#print axioms shapes_consistent

private def order : RuntimeType := ⟨.object "Examples" "Examples.Order", []⟩
private def customer : RuntimeType := ⟨.object "Examples" "Examples.Customer", []⟩

/-- Allocation 0 claims two unrelated classes in one lineage, as no CLR object can. -/
private def confused : CIL.Safety.Memory :=
  { allocations := fun identity => match identity with
      | 0 => some ⟨.object ⟨order.identity, [customer.identity]⟩, ⟨16, 8, []⟩, true, [16]⟩
      | _ => none
    cells := fun _ _ => ⟨0, true⟩, views := [], nextIdentity := 1 }

/-- Memory may hold an object located as an instance of two unrelated classes, so their objects
    are distinct only under the catalog premise, which rejects that lineage. -/
theorem unrelated_classes_need_catalog :
    objectFieldAddress confused (.address ⟨0, 0⟩) order.identity 0 = .ok ⟨0, 0⟩ ∧
    objectFieldAddress confused (.address ⟨0, 0⟩) customer.identity 8 = .ok ⟨0, 8⟩ ∧
    ¬ confused.ClassesConsistent [order, customer] := by
  refine ⟨rfl, rfl, fun consistent => ?_⟩
  have tail := consistent 0 _ _ rfl rfl order (by decide) (by decide)
  exact absurd tail (by decide)
#print axioms unrelated_classes_need_catalog

/-- A one-method program whose only `newobj` creates an instance of `type`. -/
private def createsOne (type : RuntimeType) : CIL.Program :=
  [{ returnsValue := true, locals := [],
     code := [.newObject 1 0 type.identity type.bases 16, .ret] }]

/-- The site check accepts a program creating a cataloged class with its own chain, and rejects
    one whose `newobj` records the lineage no CLR object can have, so execution of it is not
    covered by `run_preserves_classes`. -/
theorem object_sites_checked :
    ObjectSitesConsistent [order, customer] (createsOne order) ∧
    ¬ ObjectSitesConsistent [order, customer]
      (createsOne ⟨order.identity, [customer.identity]⟩) := by
  decide
#print axioms object_sites_checked

/-- A node linked to itself heads no segment to null, whatever nodes it names: a segment is a
    finite path, so a walk that would never reach null cannot claim a termination measure. -/
theorem self_linked_no_segment {field : ReferenceField} {linked : CIL.Safety.Memory}
    {node : Reference}
    (looped : field.of linked node = .address node) (nodes : List Reference) :
    ¬ field.Segment linked (.address node) .null nodes := by
  induction nodes with
  | nil =>
    intro segment
    obtain ⟨_, same, -⟩ := segment.next
    cases same
  | cons _ tail shorter =>
    intro segment
    obtain ⟨rest, same, -, next⟩ := segment.next
    cases same
    rw [looped] at next
    exact shorter next
#print axioms self_linked_no_segment

/-- A reference load followed by a word load through the object it produced. -/
@[cil_code] def linkedReading : CIL.Method :=
  { returnsValue := true, locals := [], code := [.arg 0,
      .memory (.objectReferenceField account.identity 8),
      .memory (.objectField account.identity 0 8 false), .ret] }

/-- The linked-object reader alone. -/
@[cil_code] def linkedProgram : CIL.Program := [linkedReading]

/-- The checked reference load makes its target's field evidence reachable even when the
    goal does not name the target or its value before stepping. -/
theorem loaded_reference_evidence (memory : CIL.Safety.Memory) (source target : Reference)
    (frame : Frame)
    (link : (ReferenceField.mk account.identity 8).Readable memory source)
    (held : (ReferenceField.mk account.identity 8).of memory source = .address target)
    (value : (WordField.mk account.identity 0 : WordField 8).Readable memory target) :
    ∃ result, run linkedProgram 20 0 0 [.object (.address source)] frame [] memory =
      .ok (leaveFrame frame memory, [result]) := by
  refine ⟨?_, ?_⟩
  case refine_2 => cil_checked_steps [link.facts held value.live]
#print axioms loaded_reference_evidence

/-- Named checked loads also expose their produced object's evidence, without collecting
    a field of an unrelated object or a field stated at a different memory. -/
theorem named_reference_load_evidence (memory otherMemory : CIL.Safety.Memory)
    (source target unrelated : Reference) (frame : Frame)
    (link : (ReferenceField.mk account.identity 8).Readable memory source)
    (held : (ReferenceField.mk account.identity 8).of memory source = .address target)
    (value : (WordField.mk account.identity 0 : WordField 8).Readable memory target)
    (irrelevant : (WordField.mk account.identity 0 : WordField 8).Readable memory unrelated)
    (stale : (WordField.mk account.identity 0 : WordField 8).Readable otherMemory target) :
    ∃ result, run linkedProgram 20 0 0 [.object (.address source)] frame [] memory =
      .ok (leaveFrame frame memory, [result]) := by
  have loaded := link.load_live held value.live
  refine ⟨?_, ?_⟩
  case refine_2 =>
    run_tac Lean.Elab.Tactic.withMainContext do
      let gathered ← gatherEvidenceFacts #[]
      let unrelated ← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `unrelated)
      let otherMemory ← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `otherMemory)
      for fact in gathered do
        Lean.Elab.Tactic.withMainContext do
          let proof ← Lean.Elab.Term.elabTerm fact none
          let type ← Lean.Meta.inferType proof
          if type.hasAnyFVar (fun id => id == unrelated || id == otherMemory) then
            throwError "Unreachable object evidence entered the step facts"
    cil_checked_steps
#print axioms named_reference_load_evidence

/-- A receiver check selects a Boolean-returning instance call or an explicit exception. -/
@[cil_code] private def checkedReceiverProgram : CIL.Program := [
  { returnsValue := true, locals := [], code := [
    .arg 0, .brtrue 3, .throw "MissingReceiver", .arg 0, .ldc_i4 1,
    .callInstance 1 2, .ret (some .unsigned8)] },
  { returnsValue := true, locals := [], code := [.arg 1, .ret (some .unsigned8)] }]

/-- A symbolic live receiver decides the branch and passes the call's closed argument guard. -/
theorem checked_receiver_call (memory : CIL.Safety.Memory) (receiver : Reference)
    (frame : Frame)
    (formed : formObject memory (.address receiver) = .ok (.object (.address receiver))) :
    run checkedReceiverProgram 12 0 0 [.object (.address receiver)] frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 1)]) := by
  cil_checked_steps [formed]
#print axioms checked_receiver_call

/-- A null receiver takes the explicit exception path without entering the callee. -/
theorem checked_receiver_throws (memory : CIL.Safety.Memory) (frame : Frame) :
    run checkedReceiverProgram 12 0 0 [.object .null] frame [] memory =
      .error ⟨0, 2, .thrown "MissingReceiver"⟩ := by
  cil_checked_steps
#print axioms checked_receiver_throws

/-- A narrow Boolean parameter is written through its receiver's one-byte field. -/
@[cil_code] private def narrowStoreProgram (kind : NarrowKind) : CIL.Program := [
  { returnsValue := false, locals := [], code := [
    .arg 0, .arg 1 (some kind), .memory (.setObjectField account.identity 0 1), .ret] }]

/-- Narrowing a literal Boolean preserves the payload of a supplied checked field write. -/
theorem narrowed_boolean_store (kind : NarrowKind) (memory stored : CIL.Safety.Memory)
    (receiver : Reference) (frame : Frame)
    (formed : formObject memory (.address receiver) = .ok (.object (.address receiver)))
    (written : memoryInstruction (.setObjectField account.identity 0 1)
      [.scalar (.i32 1), .object (.address receiver)] memory = .ok (stored, [])) :
    run (narrowStoreProgram kind) 5 0 0 [.object (.address receiver), .scalar (.i32 1)]
      frame [] memory = .ok (leaveFrame frame stored, []) := by
  cil_checked_steps [formed, written]
#print axioms narrowed_boolean_store

end Tests.Objects
