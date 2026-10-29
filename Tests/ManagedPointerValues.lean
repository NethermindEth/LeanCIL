import CIL.Safety.Execution

/-! Managed pointer values retain exact signatures and cannot be forged from integers. -/

namespace Tests.ManagedPointerValues

open CIL CIL.Safety

private def signature : ManagedSignature :=
  ⟨.atom Extraction.runtimeScope "System.Int32", [.atom Extraction.runtimeScope "System.Int32"]⟩
private def identity : ManagedIdentity := ⟨"Handlers", 1, []⟩
private def other : ManagedIdentity := ⟨"Handlers", 2, []⟩
private def memory : CIL.Safety.Memory :=
  { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }
private def frame : Frame := { activation := 0, locals := [], owned := [] }

/-- A table lookup retains stable identity rather than turning it into a numeric address. -/
theorem table_provenance :
    managedStep (.tableElement signature) 0 frame
      [.scalar (.i32 1), .methodTable ⟨signature, some [other, identity]⟩] memory =
        .ok (.next 1 [.methodPointer ⟨signature, some identity⟩] frame memory) := rfl
#print axioms table_provenance

/-- A numerical value is never callable, even when it equals an admitted program index. -/
theorem numeric_pointer_rejected :
    managedStep (.call signature [⟨identity, 1⟩] true) 0 frame
      [.scalar (.i64 1), .scalar (.i32 42)] memory = .error .invalidState := rfl
#print axioms numeric_pointer_rejected

/-- A well-typed pointer still needs its exact identity in the admitted target catalog. -/
theorem foreign_target_rejected :
    managedStep (.call signature [⟨identity, 1⟩] true) 0 frame
      [.methodPointer ⟨signature, some other⟩, .scalar (.i32 42)] memory =
        .error .invalidState := rfl
#print axioms foreign_target_rejected

/-- A successful indirect tail call uses the existing frame-retiring driver action. -/
theorem checked_tail_target :
    managedStep (.call signature [⟨identity, 1⟩] true) 0 frame
      [.methodPointer ⟨signature, some identity⟩, .scalar (.i32 42)] memory =
        .ok (.tailCall 1 [.scalar (.i32 42)] memory) := rfl
#print axioms checked_tail_target

end Tests.ManagedPointerValues
