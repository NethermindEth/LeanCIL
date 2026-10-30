import CIL.Safety.Execution

/-! Native handler tables preserve opaque identities across checked backing-memory accesses. -/

namespace Tests.NativeMethodTables

open CIL CIL.Safety

private def signature : ManagedSignature :=
  ⟨.atom Extraction.runtimeScope "System.Int32", [.atom Extraction.runtimeScope "System.Int32"]⟩

private def first : ManagedIdentity := ⟨"Handlers", 1, []⟩
private def second : ManagedIdentity := ⟨"Handlers", 2, []⟩

private def memory : CIL.Safety.Memory :=
  { allocations := fun index => if index == 0 then
      some { kind := .immutableStatic, layout := ⟨16, 8, []⟩ } else none
    cells := fun _ _ => ⟨0, true⟩
    views := [⟨0, 0, 16, true, false⟩]
    nextIdentity := 1
    staticBindings := [(42, ⟨0, 0⟩)] }

private def table : NativeMethodTable := ⟨signature, #[first, second], ⟨0, 0⟩, ⟨0, 0⟩⟩

/-- Adding an entry stride selects the next authenticated identity. -/
theorem native_load :
    (do let next ← table.addBytes memory 8; next.load memory) =
      .ok ⟨signature, some second⟩ := by rfl
#print axioms native_load

/-- Backing address bytes do not choose an identity, even if all bytes are zero. -/
theorem zero_bytes_keep_identity : table.load memory = .ok ⟨signature, some first⟩ := by
  rfl
#print axioms zero_bytes_keep_identity

/-- A one-past native cursor may be formed, but cannot be dereferenced. -/
theorem end_cursor :
    (table.addBytes memory 16).isOk = true ∧
      (do let ending ← table.addBytes memory 16; ending.load memory) =
        .error .outsideAllocation := ⟨rfl, rfl⟩
#print axioms end_cursor

/-- Byte arithmetic does not silently round an interior address to an entry boundary. -/
theorem misaligned_cursor :
    (do let next ← table.addBytes memory 1; next.load memory) =
      .error .alignment := by rfl
#print axioms misaligned_cursor

/-- Native underflow cannot leave the authenticated table. -/
theorem before_origin : table.addBytes memory (-1) = .error .invalidReference := by rfl
#print axioms before_origin

/-- The backing allocation must remain live at load time. -/
theorem expired_backing :
    table.load { memory with allocations := (fun _ =>
      some { kind := .immutableStatic, layout := ⟨16, 8, []⟩, live := false }) } =
        .error .expiredLifetime := by rfl
#print axioms expired_backing

/-- A matching byte range without read authority does not permit table access. -/
theorem unreadable_backing :
    table.load { memory with views := [] } = .error .unreadable := by rfl
#print axioms unreadable_backing

/-- An authenticated identity never excuses an uninitialized backing read. -/
theorem uninitialized_backing :
    table.load { memory with cells := fun _ _ => ⟨0, false⟩ } =
      .error .uninitialized := by rfl
#print axioms uninitialized_backing

/-- Mutable native storage cannot borrow an immutable table's identities. -/
theorem mutable_backing :
    table.load { memory with allocations := (fun _ =>
      some { kind := .managedHeap, layout := ⟨16, 8, []⟩ }) } =
        .error .unsupportedLayout := by rfl
#print axioms mutable_backing

/-- A cursor into a different allocation cannot select the table's entries. -/
theorem unrelated_cursor :
    { table with cursor := ⟨1, 0⟩ }.load memory = .error .invalidReference := by rfl
#print axioms unrelated_cursor

private def opaqueTable : MethodTable :=
  ⟨signature, some #[first, second], some ⟨42, 0⟩⟩

private def frame : Frame := { activation := 0, locals := [], owned := [] }

/-- The native `add` followed by `ldind.i` preserves a checked, callable identity. -/
theorem native_dispatch_load :
    managedStep .tableOffset 0 frame [.scalar (.i64 8), .methodTable opaqueTable] memory =
      .ok (.next 1 [.methodTable { opaqueTable with backing := some ⟨42, 8⟩ }] frame memory) ∧
    managedStep (.tableLoad signature) 1 frame
      [.methodTable { opaqueTable with backing := some ⟨42, 8⟩ }] memory =
        .ok (.next 2 [.methodPointer ⟨signature, some second⟩] frame memory) := ⟨rfl, rfl⟩
#print axioms native_dispatch_load

/-- Commuted native table addition uses the same checked cursor operation for every offset. -/
theorem native_add_commutes (offset : CIL.Value) (table : MethodTable)
    (memory : CIL.Safety.Memory) (frame : Frame) (rest : List CIL.Safety.Value) (pc : Nat) :
    managedStep .tableOffset pc frame (.methodTable table :: .scalar offset :: rest) memory =
      managedStep .tableOffset pc frame (.scalar offset :: .methodTable table :: rest) memory := by
  cases offset <;> rfl
#print axioms native_add_commutes

/-- Commuting the operands cannot admit a cursor outside the authenticated allocation. -/
theorem commuted_invalid_offset :
    (managedStep .tableOffset 0 frame [.methodTable opaqueTable, .scalar (.i64 24)] memory).isOk =
      false := by rfl
#print axioms commuted_invalid_offset

/-- A native array element load validates the same backing storage as pointer loading. -/
theorem native_array_load :
    managedStep (.tableElement signature) 0 frame
      [.scalar (.i32 1), .methodTable opaqueTable] memory =
        .ok (.next 1 [.methodPointer ⟨signature, some second⟩] frame memory) := rfl
#print axioms native_array_load

/-- An opaque table cannot manufacture a native cursor without a valid storage binding. -/
theorem missing_binding :
    loadNativeTable opaqueTable { memory with staticBindings := [] } =
      .error .missingAllocation := rfl
#print axioms missing_binding

/-- A scalar address remains uncallable after the new native load operation is introduced. -/
theorem numeric_load_rejected :
    managedStep (.tableLoad signature) 0 frame [.scalar (.i64 0)] memory =
      .error .invalidState := rfl
#print axioms numeric_load_rejected

end Tests.NativeMethodTables
