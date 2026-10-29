import CIL.Safety.NativeMethodTables

/-! Native handler tables preserve opaque identities across checked backing-memory accesses. -/

namespace Tests.NativeMethodTables

open CIL CIL.Safety

private def signature : ManagedSignature :=
  ⟨.atom Extraction.runtimeScope "System.Int32", [.atom Extraction.runtimeScope "System.Int32"]⟩

private def first : ManagedIdentity := ⟨"Handlers", 1, []⟩
private def second : ManagedIdentity := ⟨"Handlers", 2, []⟩

private def memory : Memory :=
  { allocations := fun index => if index == 0 then
      some { kind := .immutableStatic, layout := ⟨16, 8, []⟩ } else none
    cells := fun _ _ => ⟨0, true⟩
    views := [⟨0, 0, 16, true, false⟩]
    nextIdentity := 1 }

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

end Tests.NativeMethodTables

