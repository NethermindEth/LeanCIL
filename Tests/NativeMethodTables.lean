import CIL.Safety.MemorySteps
import CIL.Extraction.Scalars

/-! Native handler tables preserve opaque identities across checked backing-memory accesses, and
the scalar transfer admits a managed table only to `ldlen` and its pointer-typed element reads. -/

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

private def table : NativeMethodTable := ⟨signature, #[first, second], ⟨0, 0⟩, ⟨0, 0⟩, 2, rfl⟩

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
  { signature, targets := some #[first, second], backing := some ⟨42, 0⟩, entryCount := 2 }

private def frame : Frame := { activation := 0, locals := [], owned := [] }

/-- A body with no code; `step` reads only its profile and its static and link tables. -/
private def body : CIL.Method := { code := [], locals := [], returnsValue := false }

/-- The opaque table with its cursor `byteOffset` bytes past the table origin. -/
private def cursorAt (byteOffset : Nat) : MethodTable :=
  { opaqueTable with backing := some ⟨42, byteOffset⟩ }

/-- One decoded `add` over `stack` at pc 0 in `storage`. -/
private def addStep (stack : List CIL.Safety.Value) (storage : CIL.Safety.Memory := memory) :
    ExecutionResult FrameAction :=
  step body .add 0 [] frame stack storage

/-- A native table fault, attributed to a null reference and the eight-byte entry width. -/
private def tableFault (rule : Fault) : ExecutionResult FrameAction :=
  .error (.memory rule .null nativeMethodWidth)

/-- The native `add` followed by `ldind.i` preserves a checked, callable identity. -/
theorem native_dispatch_load :
    addStep [.scalar (.i64 8), .methodTable opaqueTable] =
      .ok (.next 1 [.methodTable (cursorAt 8)] frame memory) ∧
    step body (.ldind .i) 1 [] frame [.methodTable (cursorAt 8)] memory =
      .ok (.next 2 [.methodPointer ⟨signature, some second⟩] frame memory) := ⟨rfl, rfl⟩
#print axioms native_dispatch_load

/-- Both operand orders and both offset widths select the same cursor. -/
theorem native_add_orders :
    addStep [.scalar (.i32 8), .methodTable opaqueTable] =
      .ok (.next 1 [.methodTable (cursorAt 8)] frame memory) ∧
    addStep [.methodTable opaqueTable, .scalar (.i32 8)] =
      .ok (.next 1 [.methodTable (cursorAt 8)] frame memory) ∧
    addStep [.methodTable opaqueTable, .scalar (.i64 8)] =
      .ok (.next 1 [.methodTable (cursorAt 8)] frame memory) := ⟨rfl, rfl, rfl⟩
#print axioms native_add_orders

/-- A negative int32 offset is sign-extended and moves a nonzero cursor back to the origin. -/
theorem native_add_negative :
    addStep [.scalar (.i32 (-8)), .methodTable (cursorAt 8)] =
      .ok (.next 1 [.methodTable (cursorAt 0)] frame memory) := rfl
#print axioms native_add_negative

/-- Commuted native table addition is the same step for every offset, including rejected ones. -/
theorem native_add_commutes (offset : CIL.Value) (table : MethodTable) (code : CIL.Method)
    (memory : CIL.Safety.Memory) (frame : Frame) (args rest : List CIL.Safety.Value) (pc : Nat) :
    step code .add pc args frame (.methodTable table :: .scalar offset :: rest) memory =
      step code .add pc args frame (.scalar offset :: .methodTable table :: rest) memory := by
  cases offset <;> rfl
#print axioms native_add_commutes

/-- Cursor arithmetic cannot leave the table in either operand order: underflow and a cursor
    past the one-past position fault with the cursor rule. -/
theorem native_add_out_of_range :
    addStep [.scalar (.i32 (-8)), .methodTable opaqueTable] = tableFault .invalidReference ∧
    addStep [.scalar (.i64 24), .methodTable opaqueTable] = tableFault .invalidReference ∧
    addStep [.methodTable opaqueTable, .scalar (.i64 24)] = tableFault .invalidReference :=
  ⟨rfl, rfl, rfl⟩
#print axioms native_add_out_of_range

/-- A one-past cursor and a misaligned interior cursor can be formed but not loaded. -/
theorem native_add_unloadable :
    addStep [.scalar (.i64 16), .methodTable opaqueTable] =
      .ok (.next 1 [.methodTable (cursorAt 16)] frame memory) ∧
    step body (.ldind .i) 1 [] frame [.methodTable (cursorAt 16)] memory =
      tableFault .outsideAllocation ∧
    addStep [.scalar (.i32 1), .methodTable opaqueTable] =
      .ok (.next 1 [.methodTable (cursorAt 1)] frame memory) ∧
    step body (.ldind .i) 1 [] frame [.methodTable (cursorAt 1)] memory =
      tableFault .alignment := ⟨rfl, rfl, rfl, rfl⟩
#print axioms native_add_unloadable

/-- Addition checks the storage binding and allocation, but not read authority or
    initialization, which the following load checks. -/
theorem native_add_storage :
    addStep [.scalar (.i64 8), .methodTable opaqueTable]
        { memory with allocations := (fun _ =>
          some { kind := .immutableStatic, layout := ⟨16, 8, []⟩, live := false }) } =
      tableFault .expiredLifetime ∧
    addStep [.scalar (.i64 8), .methodTable opaqueTable]
        { memory with allocations := (fun _ =>
          some { kind := .managedHeap, layout := ⟨16, 8, []⟩ }) } =
      tableFault .unsupportedLayout ∧
    addStep [.scalar (.i64 8), .methodTable { opaqueTable with backing := none }] =
      tableFault .invalidReference ∧
    addStep [.scalar (.i64 8),
        .methodTable { opaqueTable with targets := none, counted := nofun }] =
      tableFault .nullDereference ∧
    addStep [.scalar (.i64 8), .methodTable opaqueTable] { memory with staticBindings := [] } =
      tableFault .missingAllocation ∧
    addStep [.scalar (.i64 8), .methodTable opaqueTable] { memory with views := [] } =
      .ok (.next 1 [.methodTable (cursorAt 8)] frame { memory with views := [] }) ∧
    step body (.ldind .i) 1 [] frame [.methodTable (cursorAt 8)]
        { memory with views := [] } = tableFault .unreadable ∧
    addStep [.scalar (.i64 8), .methodTable opaqueTable]
        { memory with cells := fun _ _ => ⟨0, false⟩ } =
      .ok (.next 1 [.methodTable (cursorAt 8)] frame
        { memory with cells := fun _ _ => ⟨0, false⟩ }) ∧
    step body (.ldind .i) 1 [] frame [.methodTable (cursorAt 8)]
        { memory with cells := fun _ _ => ⟨0, false⟩ } = tableFault .uninitialized :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms native_add_storage

/-- Offsets other than int32 and int64, short stacks and two tables are rejected; unspecified
    offset bits are rejected before the offset is read. -/
theorem native_add_rejected :
    addStep [.scalar (.i8 8), .methodTable opaqueTable] = .error .invalidState ∧
    addStep [.methodTable opaqueTable, .scalar (.i8 8)] = .error .invalidState ∧
    addStep [.scalar (.v128Low64 8), .methodTable opaqueTable] =
      .error (.unsupported "Instruction observes unspecified vector bits") ∧
    addStep [.methodTable opaqueTable] = .error .invalidState ∧
    addStep [.methodTable opaqueTable, .methodTable opaqueTable] = .error .invalidState :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
#print axioms native_add_rejected

/-- A native array element load validates the same backing storage as pointer loading. -/
theorem native_array_load :
    instruction (.ldelem .i) [.scalar (.i32 1), .methodTable opaqueTable] memory =
      .ok (memory, [.methodPointer ⟨signature, some second⟩]) := rfl
#print axioms native_array_load

/-- A caller's signature that differs from the table's. -/
private def otherSignature : ManagedSignature :=
  ⟨.atom Extraction.runtimeScope "System.Int64", [.atom Extraction.runtimeScope "System.Int32"]⟩

/-- An unhomed table argument loads an entry under the table's own signature, and a call under
    any other signature selects no target from it. -/
theorem argument_table_load :
    let argumentLoad : CIL.Method :=
      { code := [.ldarg 0, .ldind .i, .ret], locals := [], returnsValue := true }
    step argumentLoad (.ldarg 0) 0 [.methodTable (cursorAt 8)] frame [] memory =
      .ok (.next 1 [.methodTable (cursorAt 8)] frame memory) ∧
    step argumentLoad (.ldind .i) 1 [.methodTable (cursorAt 8)] frame
      [.methodTable (cursorAt 8)] memory =
      .ok (.next 2 [.methodPointer ⟨signature, some second⟩] frame memory) ∧
    indirectTarget otherSignature [{ identity := second, method := 0 }]
      ⟨signature, some second⟩ = none := ⟨rfl, rfl, rfl⟩
#print axioms argument_table_load

/-- An opaque table cannot manufacture a native cursor without a valid storage binding. -/
theorem missing_binding :
    loadNativeTable opaqueTable { memory with staticBindings := [] } =
      .error .missingAllocation := rfl
#print axioms missing_binding

/-- A native load of a scalar address is refused rather than producing a callable identity. -/
theorem numeric_load_rejected :
    (step body (.ldind .i) 0 [] frame [.scalar (.i64 0)] memory).isOk = false := rfl
#print axioms numeric_load_rejected

section Admission

open CIL.Extraction

/-- The extraction stack kind of a pointer into the native table of `signature`. -/
private def nativeKind : ScalarKind := .nativeMethodTable signature

/-- Native table addition admits only a decoded `add` without a raw operand and with an int32 or
    native offset in either order; ordinary integer addition keeps its admission. -/
theorem native_add_admission :
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [.word32, nativeKind] .add = true ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [nativeKind, .native] .add = true ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [.native, nativeKind] .add = true ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [nativeKind, .word32] .add = true ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .local 0⟩ [.word32, nativeKind] .add = false ∧
    scalarEmissionMatches #[] none none ⟨0, 89, .none⟩ [.word32, nativeKind] .add = false ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [.word32, nativeKind] .sub = false ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [.word32, nativeKind] .add_ovf = false ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [.word64, nativeKind] .add = false ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [.other, nativeKind] .add = false ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [nativeKind, .word64] .add = false ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [nativeKind, .other] .add = false ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [nativeKind, .reference] .add = false ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [nativeKind, nativeKind] .add = false ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [.word32, .methodTable signature]
      .add = false ∧
    scalarEmissionMatches #[] none none ⟨0, 88, .none⟩ [.word32, .word32] .add = true := by
  decide +kernel
#print axioms native_add_admission

/-- A load through a native table cursor admits only the decoded `ldind.i`. -/
theorem native_load_admission :
    scalarEmissionMatches #[] none none ⟨0, 77, .none⟩ [nativeKind] (.ldind .i) = true ∧
    scalarEmissionMatches #[] none none ⟨0, 77, .none⟩ [nativeKind] (.ldind .i8) = false := by
  decide +kernel
#print axioms native_load_admission

end Admission

section TableTransfer

open CIL.Extraction

/-- A static method without arguments; the transfers below read none of its fields. -/
private def holder : RawMethod := {
  token := 0x06000001, owner := "Scope::Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
  parameters := [], locals := [], initLocals := true, maxStack := 3, genericParameters := [],
  code := [] }

/-- The extraction stack kind of a managed handler table of `signature`. -/
private def tableKind : ScalarKind := .methodTable signature

/-- The stack kinds the raw instruction `opcode` with `operand` leaves on `stack`. -/
private def transfer (opcode : Nat) (operand : RawOperand) (stack : List ScalarKind) :
    Option (List ScalarKind) :=
  scalarTransfer holder ⟨0, opcode, operand⟩ stack

/-- `ldlen` of a handler table gives a native int, and `ldelem.i` or `ldelem` of the table's
    own pointer type at an int32 or native index gives a pointer of the table's signature. -/
theorem table_reads_admitted :
    transfer 142 .none [tableKind] = some [.native] ∧
    transfer 151 .none [.word32, tableKind] = some [.methodPointer signature] ∧
    transfer 151 .none [.native, tableKind] = some [.methodPointer signature] ∧
    transfer 163 (.type signature.typeExpr) [.word32, tableKind] =
      some [.methodPointer signature] ∧
    transfer 163 (.type signature.typeExpr) [.native, tableKind] =
      some [.methodPointer signature] := by
  decide +kernel
#print axioms table_reads_admitted

/-- An element read at an index that is not an int32 or native int is refused. -/
theorem table_index_kinds_refused :
    [ScalarKind.word64, .other, .reference, .object, .nullObject, .methodPointer signature,
        tableKind].all (fun index =>
      transfer 151 .none [index, tableKind] == none &&
        transfer 163 (.type signature.typeExpr) [index, tableKind] == none) = true := by
  decide +kernel
#print axioms table_index_kinds_refused

/-- `ldelem` must name the table's own pointer type: another signature, a non-pointer type and a
    missing type operand are refused. -/
theorem table_element_type_refused :
    transfer 163 (.type otherSignature.typeExpr) [.word32, tableKind] = none ∧
    transfer 163 (.type (.atom runtimeScope "System.IntPtr")) [.word32, tableKind] = none ∧
    transfer 163 .none [.word32, tableKind] = none := by
  decide +kernel
#print axioms table_element_type_refused

/-- No other array opcode reads or writes a handler table: the sized loads, `ldelem.ref`,
    `ldelema` and every store are refused. -/
theorem table_other_array_opcodes_refused :
    ([144, 145, 146, 147, 148, 149, 150, 154].all (fun opcode =>
      transfer opcode .none [.word32, tableKind] == none) &&
    transfer 143 (.type signature.typeExpr) [.word32, tableKind] == none &&
    [155, 156, 157, 158, 159, 162].all (fun opcode =>
      [ScalarKind.native, .word32, .word64, .methodPointer signature].all (fun value =>
        transfer opcode .none [value, .word32, tableKind] == none)) &&
    transfer 164 (.type signature.typeExpr) [.methodPointer signature, .word32, tableKind] ==
      none) = true := by
  decide +kernel
#print axioms table_other_array_opcodes_refused

/-- A native table cursor is no managed table: `ldlen` and the element reads refuse it. -/
theorem native_cursor_table_reads_refused :
    transfer 142 .none [nativeKind] = none ∧
    transfer 151 .none [.word32, nativeKind] = none ∧
    transfer 163 (.type signature.typeExpr) [.word32, nativeKind] = none := by
  decide +kernel
#print axioms native_cursor_table_reads_refused

/-- `ldlen`, `ldelem.i` and `ldelem` of a handler table emit their decoded instructions, not
    another instruction's decoding. -/
theorem table_reads_emit_decoded :
    scalarEmissionMatches #[] none none ⟨0, 142, .none⟩ [tableKind] .ldlen = true ∧
    scalarEmissionMatches #[] none none ⟨0, 151, .none⟩ [.word32, tableKind] (.ldelem .i) = true ∧
    scalarEmissionMatches #[] none none ⟨0, 163, .type signature.typeExpr⟩ [.word32, tableKind]
      (.ldelem_any signature.typeExpr) = true ∧
    scalarEmissionMatches #[] none none ⟨0, 151, .none⟩ [.word32, tableKind]
      (.ldelem_any signature.typeExpr) = false ∧
    scalarEmissionMatches #[] none none ⟨0, 163, .type signature.typeExpr⟩ [.word32, tableKind]
      (.ldelem .i) = false := by
  decide +kernel
#print axioms table_reads_emit_decoded

end TableTransfer

section EntryCount

/-- `NativeMethodTable.check` reading the entry count by walking `targets`. -/
private def walkedCheck (table : NativeMethodTable) (memory : CIL.Safety.Memory) :
    Checked Unit := do
  let allocation ← liveAllocation memory table.origin.allocation
  if allocation.kind != .immutableStatic then .error .unsupportedLayout else pure ()
  if table.targets.size >= 2^31 ||
      table.origin.offset + nativeMethodWidth * table.targets.size > allocation.layout.size then
    .error .outsideAllocation else pure ()
  if allocation.layout.alignment % nativeMethodWidth != 0 ||
      table.origin.offset % nativeMethodWidth != 0 then .error .alignment else pure ()
  if table.cursor.allocation != table.origin.allocation ||
      table.cursor.offset < table.origin.offset ||
      table.cursor.offset > table.origin.offset + nativeMethodWidth * table.targets.size then
    .error .invalidReference else pure ()

/-- `NativeMethodTable.addBytes` with `walkedCheck`. -/
private def walkedAddBytes (table : NativeMethodTable) (memory : CIL.Safety.Memory)
    (offset : BitVec 64) : Checked NativeMethodTable := do
  walkedCheck table memory
  let cursor := { table.cursor with offset :=
    (BitVec.ofNat 64 table.cursor.offset + offset).toNat }
  let result := { table with cursor }
  walkedCheck result memory
  return result

/-- `NativeMethodTable.load` with `walkedCheck`, reading the entry with `targets[index]?`, whose
    bound check walks `targets`. -/
private def walkedLoadView (table : NativeMethodTable) (memory : CIL.Safety.Memory) :
    Checked CIL.MethodPointer := do
  walkedCheck table memory
  let relative := table.cursor.offset - table.origin.offset
  if relative % nativeMethodWidth != 0 then .error .alignment else pure ()
  let index := relative / nativeMethodWidth
  let some identity := table.targets[index]? | .error .outsideAllocation
  let _ ← read memory table.cursor nativeMethodWidth nativeMethodWidth
  return ⟨table.signature, some identity⟩

/-- `nativeTableView` counting the view's entries by walking them; it reads no table count. -/
private def walkedView (table : MethodTable) (memory : CIL.Safety.Memory) :
    Checked NativeMethodTable := do
  let some targets := table.targets | .error .nullDereference
  let some backing := table.backing | .error .invalidReference
  let some (_, origin) := memory.staticBindings.find? (·.1 == backing.identity) |
    .error .missingAllocation
  let view : NativeMethodTable := ⟨table.signature, targets, origin,
    { origin with offset := origin.offset + backing.byteOffset }, targets.size, rfl⟩
  walkedCheck view memory
  return view

/-- `addNativeTable` over the walked view and checks. -/
private def walkedAdd (table : MethodTable) (memory : CIL.Safety.Memory) (offset : BitVec 64) :
    Checked MethodTable := do
  let view ← walkedView table memory
  let moved ← walkedAddBytes view memory offset
  let some backing := table.backing | .error .invalidReference
  return { table with backing := some { backing with
    byteOffset := moved.cursor.offset - moved.origin.offset } }

/-- `loadNativeTable` over the walked view and checks. -/
private def walkedLoad (table : MethodTable) (memory : CIL.Safety.Memory) :
    Checked CIL.MethodPointer := do
  let view ← walkedView table memory
  walkedLoadView view memory

/-- A view's carried count is its entries' size, so its geometry check is the walked one. -/
private theorem check_eq_walked (view : NativeMethodTable) (memory : CIL.Safety.Memory) :
    view.check memory = walkedCheck view memory := by
  rcases view with ⟨signature, targets, origin, cursor, count, counted⟩
  subst counted
  rfl

/-- The view a table resolves to is the one that counts its entries by walking them. -/
private theorem nativeTableView_eq_walked (table : MethodTable) (memory : CIL.Safety.Memory) :
    nativeTableView table memory = walkedView table memory := by
  rcases table with ⟨signature, _ | entries, _ | backing, count, counted⟩
  · rfl
  · rfl
  · rfl
  · obtain rfl : entries.size = count := counted entries rfl
    unfold nativeTableView walkedView
    cases found : memory.staticBindings.find? (·.1 == backing.identity) with
    | none => simp [found]
    | some binding => simp [found, check_eq_walked]

/-- Reading the carried entry count moves a native cursor exactly as walking the entries does,
    for every table, memory and offset. -/
theorem addNativeTable_eq_walked : addNativeTable = walkedAdd := by
  funext table memory offset
  unfold addNativeTable walkedAdd NativeMethodTable.addBytes walkedAddBytes
  simp only [nativeTableView_eq_walked, check_eq_walked]
  rfl
#print axioms addNativeTable_eq_walked

/-- Bounding the entry index by the carried count loads exactly the entry, or the fault, that the
    walked bound check gives, for every view and memory. -/
theorem load_eq_walked : NativeMethodTable.load = walkedLoadView := by
  funext view memory
  rcases view with ⟨signature, targets, origin, cursor, count, counted⟩
  subst counted
  unfold NativeMethodTable.load walkedLoadView
  simp only [check_eq_walked]
  by_cases inside : (cursor.offset - origin.offset) / nativeMethodWidth < targets.size
  · simp only [inside, dite_true, Array.getElem?_eq_getElem]
  · simp only [inside, dite_false, Array.getElem?_eq_none (Nat.le_of_not_lt inside)]
#print axioms load_eq_walked

/-- Reading the carried entry count loads a native entry exactly as walking the entries does. -/
theorem loadNativeTable_eq_walked : loadNativeTable = walkedLoad := by
  funext table memory
  unfold loadNativeTable walkedLoad
  simp only [nativeTableView_eq_walked, load_eq_walked]
#print axioms loadNativeTable_eq_walked

/-- An int32 offset added to a native table steps as the addition that walks the entries. -/
theorem step_add_table_i32_walked (code : CIL.Method) (offset : CIL.W32) (table : MethodTable)
    (memory : CIL.Safety.Memory) (frame : Frame) (args rest : List CIL.Safety.Value) (pc : Nat) :
    step code .add pc args frame (.scalar (.i32 offset) :: .methodTable table :: rest) memory = do
      let selected ← checkedAt .null nativeMethodWidth
        (walkedAdd table memory (offset.signExtend 64))
      return .next (pc + 1) (.methodTable selected :: rest) frame memory := by
  rw [step_add_table_i32_eq, addNativeTable_eq_walked]
#print axioms step_add_table_i32_walked

/-- A native-int offset added to a native table steps as the addition that walks the entries. -/
theorem step_add_table_i64_walked (code : CIL.Method) (offset : CIL.W64) (table : MethodTable)
    (memory : CIL.Safety.Memory) (frame : Frame) (args rest : List CIL.Safety.Value) (pc : Nat) :
    step code .add pc args frame (.scalar (.i64 offset) :: .methodTable table :: rest) memory = do
      let selected ← checkedAt .null nativeMethodWidth (walkedAdd table memory offset)
      return .next (pc + 1) (.methodTable selected :: rest) frame memory := by
  rw [step_add_table_i64_eq, addNativeTable_eq_walked]
#print axioms step_add_table_i64_walked

end EntryCount

end Tests.NativeMethodTables
