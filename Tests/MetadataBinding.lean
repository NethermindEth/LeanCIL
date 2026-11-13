import Tests.MetadataWorld

/-!
# Metadata binding tests

A hand-built world of two pinned assemblies: `T`, which carries the operands under test, and
`Lib`, which defines the class `Lib.Box` that `T` calls into. Every operand of `T` that the
extractor can state is checked against its metadata and must pass. Each rejection then changes
one fact of the metadata or of the operand and asserts the exact error.
-/

namespace Tests.MetadataBinding

open CIL CIL.Extraction Tests.MetadataBuilder Tests.MetadataWorld


/-- Whether checking an operand against a pair of slices gives these facts. -/
private def passes (ownSlice libSlice : MetadataSlice) (token : Nat) (operand : RawOperand)
    (arity : Nat := 0) : Bool :=
  match (do
    let env : MetadataEnv := { slices := [← ownSlice.index, ← libSlice.index] }
    checkEntry env arity token operand) with
  | .ok _ => true
  | .error _ => false

/-- Whether checking an operand fails with exactly this error. -/
private def rejects (ownSlice libSlice : MetadataSlice) (token : Nat) (operand : RawOperand)
    (error : MetadataError) (arity : Nat := 0) : Bool :=
  match (do
    let env : MetadataEnv := { slices := [← ownSlice.index, ← libSlice.index] }
    checkEntry env arity token operand) with
  | .error found => found == error
  | .ok _ => false

/-- Replace the bytes of a row of a slice. -/
private def mutateRow (slice : MetadataSlice) (token : Nat) (change : List Nat → List Nat) :
    MetadataSlice :=
  { slice with rows := slice.rows.map fun (key, bytes) =>
      if key == token then (key, change bytes) else (key, bytes) }

/-- Replace the bytes of a blob of a slice. -/
private def mutateBlob (slice : MetadataSlice) (offset : Nat) (change : List Nat → List Nat) :
    MetadataSlice :=
  { slice with blobs := slice.blobs.map fun (key, bytes) =>
      if key == offset then (key, change bytes) else (key, bytes) }

/-! ## Operands that match their metadata -/

theorem accepts_type_operand :
    passes own.1 lib tokens.objectRef (.type (.atom runtimeScope "System.Object")) = true := by
  decide +kernel
theorem accepts_external_call :
    passes own.1 lib tokens.writeLine (.call writeLineSite) = true := by decide +kernel
theorem accepts_managed_call :
    passes own.1 lib tokens.getRef (.call getSite) = true := by decide +kernel
theorem accepts_generic_call :
    passes own.1 lib tokens.idSpec (.call idSite) = true := by decide +kernel
theorem accepts_string :
    passes own.1 lib tokens.hello (.text "hi") = true := by decide +kernel
theorem accepts_indirect :
    passes own.1 lib tokens.indirect (.indirectCall .void [int32] false false 0) = true := by
  decide +kernel
theorem accepts_fields :
    passes own.1 lib tokens.totalField
      (.field (.atom "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Program")
        1 int32 true) = true ∧
    passes own.1 lib tokens.countField countOperand = true := by decide +kernel
/-! ## Operands whose metadata or claim changed -/

/-- The bytes of a row of a slice. -/
private def rowOf (slice : MetadataSlice) (token : Nat) : List Nat :=
  (slice.rows.lookup token).getD []

/-- The offset of the blob entry with a payload, assuming a one-byte length prefix. -/
private def blobOffset (slice : MetadataSlice) (payload : List Nat) : Nat :=
  match slice.blobs.find? (fun entry => entry.2.drop 1 == payload) with
  | some (offset, _) => offset
  | none => 0

/-- A row whose two bytes at `position` are copied from another row of the slice. -/
private def borrow (slice : MetadataSlice) (token source position : Nat) : MetadataSlice :=
  mutateRow slice token fun bytes =>
    bytes.take position ++ ((rowOf slice source).drop position).take 2 ++ bytes.drop (position + 2)

/-- A type token whose name column names another string that is present: `Console` becomes
    `Object`. -/
private def renamedConsole : MetadataSlice := borrow own.1 tokens.consoleRef tokens.objectRef 2

/-- A type token whose name offset has no entry. -/
private def dangling : MetadataSlice :=
  mutateRow own.1 tokens.consoleRef fun bytes => bytes.take 2 ++ [0xFF, 0x7F] ++ bytes.drop 4

theorem rejects_a_row_byte_that_names_another_string :
    rejects renamedConsole lib tokens.consoleRef (.type (.atom runtimeScope "System.Console"))
      (.operandMismatch tokens.consoleRef) = true := by decide +kernel
#print axioms rejects_a_row_byte_that_names_another_string

theorem rejects_a_signature_byte_that_changes_a_parameter :
    rejects (mutateBlob own.1 (blobOffset own.1 [0x00, 0x01, 0x01, 0x08]) fun bytes =>
        bytes.set 4 0x0A) lib tokens.writeLine (.call writeLineSite)
      (.operandMismatch tokens.writeLine) = true := by decide +kernel
#print axioms rejects_a_signature_byte_that_changes_a_parameter

theorem rejects_a_heap_offset_with_no_entry :
    rejects dangling lib tokens.consoleRef (.type (.atom runtimeScope "System.Console"))
      (.missingHeap 0 0x7FFF) = true := by decide +kernel
#print axioms rejects_a_heap_offset_with_no_entry

theorem rejects_a_generic_argument_that_differs_from_the_specification :
    rejects own.1 lib tokens.idSpec (.call { idSite with typeArguments := [uint64] })
      (.genericMismatch tokens.idSpec) = true := by decide +kernel
#print axioms rejects_a_generic_argument_that_differs_from_the_specification

/-- `System.Console` as an assembly of version 9 would define it. -/
private def olderConsole : TypeExpr :=
  .atom "System.Runtime, Version=9.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
    "System.Console"

theorem rejects_an_owner_scope_with_another_version :
    rejects own.1 lib tokens.writeLine (.call { writeLineSite with declaringType := olderConsole })
      (.scopeMismatch tokens.writeLine) = true := by decide +kernel
#print axioms rejects_an_owner_scope_with_another_version

theorem rejects_a_field_index_the_metadata_does_not_give :
    rejects own.1 lib tokens.countField
      (.field (.atom ownIdentity "Program") 1 int32 false)
      (.fieldIndexMismatch tokens.countField 1 0) = true := by decide +kernel
#print axioms rejects_a_field_index_the_metadata_does_not_give

theorem rejects_a_static_field_claimed_as_an_instance_field :
    rejects own.1 lib tokens.totalField
      (.field (.atom ownIdentity "Program") 1 int32 false)
      (.operandMismatch tokens.totalField) = true := by decide +kernel
#print axioms rejects_a_static_field_claimed_as_an_instance_field

/-- The local variable types of the signature at `tokens.localsSignature`. -/
private def localsFail (slice : MetadataSlice) (locals : List TypeExpr) (error : MetadataError) :
    Bool :=
  match (do
    let env : MetadataEnv := { slices := [← slice.index, ← lib.index] }
    checkLocals env 0 tokens.localsSignature locals) with
  | .error found => found == error
  | .ok _ => false

theorem accepts_the_locals_the_signature_names :
    (match (do
      let env : MetadataEnv := { slices := [← own.1.index, ← lib.index] }
      checkLocals env 0 tokens.localsSignature [uint64]) with
    | .ok _ => true
    | .error _ => false) = true := by decide +kernel
#print axioms accepts_the_locals_the_signature_names

theorem rejects_a_local_of_another_type :
    localsFail own.1 [uint32] (.localMismatch 0) = true ∧
    localsFail own.1 [uint64, uint64] (.localMismatch 1) = true ∧
    localsFail own.1 [] (.localMismatch 0) = true := by decide +kernel
#print axioms rejects_a_local_of_another_type

theorem rejects_a_pinned_local :
    localsFail (mutateBlob own.1 (blobOffset own.1 [0x07, 0x01, 0x0B]) fun _ =>
      [4, 0x07, 0x01, 0x45, 0x0B]) [uint64] (.unsupportedSignature 2 0x45) = true := by
  decide +kernel
#print axioms rejects_a_pinned_local

/-! ## Rows and heap entries the decoder refuses -/

theorem rejects_a_row_of_the_wrong_length :
    rejects (mutateRow own.1 tokens.consoleRef fun bytes => bytes.take 5) lib tokens.consoleRef
      (.type (.atom runtimeScope "System.Console")) (.rowLength tokens.consoleRef 6 5) = true := by
  decide +kernel
#print axioms rejects_a_row_of_the_wrong_length

theorem rejects_row_zero :
    rejects own.1 lib 0x01000000 (.type (.atom runtimeScope "System.Console"))
      (.tokenOutOfScope 0x01000000) = true := by decide +kernel
#print axioms rejects_row_zero

theorem rejects_a_duplicate_token :
    (match { own.1 with rows := own.1.rows ++ own.1.rows.take 1 }.index with
      | .error found => found == .duplicateEntry (own.1.rows.headD (0, [])).1
      | .ok _ => false) = true := by decide +kernel
#print axioms rejects_a_duplicate_token

theorem rejects_a_wrong_user_string_terminal_byte :
    rejects { own.1 with userStrings := own.1.userStrings.map fun (offset, bytes) =>
        (offset, bytes.set (bytes.length - 1) 1) } lib tokens.hello (.text "hi")
      (.malformedUserString (tokens.hello - 0x70000000)) = true := by decide +kernel
#print axioms rejects_a_wrong_user_string_terminal_byte

theorem rejects_another_string_than_the_user_string :
    rejects own.1 lib tokens.hello (.text "ho") (.operandMismatch tokens.hello) = true := by
  decide +kernel
#print axioms rejects_another_string_than_the_user_string

/-! ## Calls into a pinned assembly -/

theorem rejects_a_pinned_callee_with_another_name :
    rejects (borrow own.1 tokens.getRef tokens.writeLine 2) lib
      tokens.getRef (.call { getSite with name := "WriteLine" })
      (.unresolvedMember tokens.getRef) = true := by decide +kernel
#print axioms rejects_a_pinned_callee_with_another_name

theorem rejects_a_pinned_callee_with_no_link :
    rejects { own.1 with links := own.1.links.filter (·.source != tokens.getRef) } lib
      tokens.getRef (.call getSite) (.unresolvedMember tokens.getRef) = true := by decide +kernel
#print axioms rejects_a_pinned_callee_with_no_link

theorem rejects_a_managed_target_other_than_the_definition :
    rejects own.1 lib tokens.getRef (.call { getSite with target := .managed 0x06000002 })
      (.operandMismatch tokens.getRef) = true := by decide +kernel
#print axioms rejects_a_managed_target_other_than_the_definition

/-- The identity of `WriteLine(long)`, which the `WriteLine(int)` token does not name. -/
private def longWriteLine : MethodId :=
  .external (runtimeScope ++ "::System.Void System.Console::WriteLine(System.Int64)")

theorem rejects_an_external_identity_other_than_the_member :
    rejects own.1 lib tokens.writeLine (.call { writeLineSite with target := longWriteLine })
      (.operandMismatch tokens.writeLine) = true := by decide +kernel
#print axioms rejects_an_external_identity_other_than_the_member

/-! ## The use of a token -/

theorem rejects_a_field_access_that_disagrees_with_the_field_row :
    checkSite 0x7E { staticField := some false } countOperand = false ∧
    checkSite 0x7B { staticField := some true } countOperand = false ∧
    checkSite 0x7B { staticField := some false } countOperand = true ∧
    checkSite 0x7B { staticField := some false }
      (.field (.atom ownIdentity "Program") 0 int32 false) = true ∧
    checkSite 0x7E { staticField := some true }
      (.field (.atom ownIdentity "Program") 1 int32 true) = true := by decide +kernel
#print axioms rejects_a_field_access_that_disagrees_with_the_field_row

/-! ## The method definition -/

/-- `T.Program.Main`, a public static method with no parameters. -/
private def mainMethod : RawMethod :=
  { token := tokens.main, owner := ownIdentity ++ "::Program", hasThis := false,
    explicitThis := false, callingConvention := 0, attributes := 0x96, implementation := 0,
    returnType := .void, parameters := [], locals := [], initLocals := false, maxStack := 8,
    genericParameters := [], code := [] }

/-- Whether the method definition is accepted, or refused with this error. -/
private def identity (slice : MetadataSlice) (pin : String) (method : RawMethod) :
    Except MetadataError Unit := do
  let env : MetadataEnv := { slices := [← slice.index, ← lib.index] }
  methodIdentityValid env { identity := pin } method

private def identityFails (slice : MetadataSlice) (pin : String) (method : RawMethod)
    (error : MetadataError) : Bool :=
  match identity slice pin method with
  | .error found => found == error
  | .ok _ => false

theorem accepts_the_method_definition_its_row_gives :
    (match identity own.1 ownIdentity mainMethod with
      | .ok _ => true
      | .error _ => false) = true := by decide +kernel
#print axioms accepts_the_method_definition_its_row_gives

theorem rejects_a_method_definition_that_differs_from_its_row :
    identityFails own.1 ownIdentity { mainMethod with attributes := 0x97 }
      (.methodMismatch tokens.main) = true ∧
    identityFails own.1 ownIdentity { mainMethod with implementation := 1 }
      (.methodMismatch tokens.main) = true ∧
    identityFails own.1 ownIdentity { mainMethod with hasThis := true }
      (.methodMismatch tokens.main) = true ∧
    identityFails own.1 ownIdentity { mainMethod with returnType := int32 }
      (.methodMismatch tokens.main) = true ∧
    identityFails own.1 ownIdentity { mainMethod with parameters := [int32] }
      (.methodMismatch tokens.main) = true ∧
    identityFails own.1 ownIdentity { mainMethod with owner := libScope ++ "::Program" }
      (.methodMismatch tokens.main) = true ∧
    identityFails own.1 ownIdentity
      { mainMethod with genericParameters := [{ flags := 0, types := [] }] }
      (.methodMismatch tokens.main) = true := by decide +kernel
#print axioms rejects_a_method_definition_that_differs_from_its_row

theorem rejects_a_pin_of_another_version :
    identityFails own.1 "T, Version=2.0.0.0, Culture=neutral, PublicKeyToken=null" mainMethod
      .identityMismatch = true := by decide +kernel
#print axioms rejects_a_pin_of_another_version

/-- A method row whose address differs from the one the body was read at is accepted: where a body
    sits in the image is not part of the default check. -/
theorem ignores_the_body_address :
    (match identity { own.1 with rows := own.1.rows.map fun (token, bytes) =>
        (token, if token == tokens.main then 7 :: bytes.drop 1 else bytes) } ownIdentity mainMethod with
      | .ok _ => true
      | .error _ => false) = true := by decide +kernel
#print axioms ignores_the_body_address
end Tests.MetadataBinding
