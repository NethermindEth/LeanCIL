import CIL.Extraction.Translation

/-! Checks static readonly values against literal, method and constructor evidence. -/

namespace Tests.StaticValueEvidence
open CIL CIL.Extraction

private def zeros : List (BitVec 8) := [0, 0]

/-- Returns its zero-initialized two-byte aggregate local. -/
private def initializer : Method := {
  code := [.ldloc 0, .ret], locals := [.aggregate zeros], localKinds := [.aggregate 2],
  returnsValue := true }

private def descriptor (bytes : List (BitVec 8)) (init : Option StaticInitializer) : StaticDescriptor :=
  { identity := 0, fieldName := "Fixture::Zero", bytes, initializer := init }

/-- The static field the fixtures load, as the raw operand of `rawStatic` names it. -/
private def field : FieldRef :=
  { owner := .atom "Fixture" "Holder", index := 0, type := .atom "Fixture" "Pair",
    name := name!"Zero" }

/-- A second field of the same holder and type. -/
private def otherField : FieldRef := { field with index := 1, name := name!"One" }

/-- The field's index on another holder. -/
private def otherOwner : FieldRef := { field with owner := .atom "Fixture" "Other" }

/-- The field's holder and index with another stored type. -/
private def otherType : FieldRef := { field with type := .atom "Fixture" "Word" }

private def loader (bytes : List (BitVec 8)) (init : Option StaticInitializer) : Method :=
  { code := [.ldsfld field, .ret], locals := [], returnsValue := true,
    staticSites := [(0, descriptor bytes init)] }

private def load (bytes : List (BitVec 8))
    (init : Option StaticInitializer := some ⟨1, [], none, false⟩) : Program :=
  [loader bytes init, initializer]

private def run (program : Program) := (Safety.invoke program 8 0 [] initializerMemory).map Prod.snd

-- A load pushes the descriptor's bytes and leaves memory unchanged.
example : run (load zeros) = .ok [.scalar (.aggregate zeros)] := rfl
example : Safety.staticLoad (loader zeros (some ⟨1, [], none, false⟩)) 0 initializerMemory =
    .ok (initializerMemory, .scalar (.aggregate zeros)) := rfl

-- The certificate reruns the initializer: matching bytes pass, forged bytes fail.
example : StaticValuesValid (load zeros) := by decide +kernel
example : ¬ StaticValuesValid (load [1, 0]) := by decide +kernel
-- An initializer that is not in the program, or returns no value, is rejected too.
example : ¬ StaticValuesValid (load zeros (some ⟨5, [], none, false⟩)) := by decide +kernel
example : ¬ StaticValuesValid (load zeros (some ⟨0, [], none, false⟩)) := by decide +kernel

/-- Loading RVA data, a descriptor with neither initializer nor opaque value, faults: the model
    has no value for it. -/
theorem rva_value_load :
    run (load zeros none) = .error ⟨0, 0, .unsupported "Static field value is not extracted"⟩ :=
  rfl
#print axioms rva_value_load

-- RVA descriptors without an initializer impose nothing on the certificate.
example : StaticValuesValid (load [7] none) := by decide +kernel

/-- A load whose pc has no site faults instead of reading some other field's descriptor. -/
theorem missing_site_faults :
    run [{ loader zeros none with staticSites := [] }] =
      .error ⟨0, 0, .unsupported "Missing extracted static field identity"⟩ := rfl
#print axioms missing_site_faults

/-- A constructor writes through the ordinary checked aggregate temporary. -/
private def constructor : Method := {
  code := [.ldarg 0, .ldc_i4 7, .storeScalar 1, .ret]
  locals := [], returnsValue := false }

private def constructed (bytes : List (BitVec 8)) (callee : Method := constructor) : Program :=
  [loader bytes (some { method := 1, arguments := [], construct := true }), callee]

/-- Construction starts with initialized zero bytes and preserves untouched bytes. -/
theorem constructor_bytes : StaticValuesValid (constructed [7, 0]) := by decide +kernel
#print axioms constructor_bytes

/-- Changing the emitted constructor result does not change what checked execution produces. -/
theorem forged_constructor_bytes : ¬ StaticValuesValid (constructed [8, 0]) := by decide +kernel
#print axioms forged_constructor_bytes

/-- A constructor must return void, even if its returned aggregate matches the descriptor. -/
theorem returning_constructor : ¬ StaticValuesValid (constructed zeros initializer) := by
  decide +kernel
#print axioms returning_constructor

/-- A raw method whose instructions are `before` and then `opcode` naming `field`, static
    when `isStatic` holds. -/
private def rawStatic (opcode : Nat) (isStatic : Bool := true)
    (before : List RawInstruction := []) : RawMethod := {
  token := 0, owner := "Fixture", hasThis := false, explicitThis := false
  callingConvention := 0, attributes := 0, implementation := 0, returnType := .void
  parameters := [], locals := [], initLocals := true, maxStack := 1, genericParameters := []
  code := before ++ [⟨0, opcode, .field field.owner field.index field.type isStatic⟩] }

/-- Constructor-initialized addresses retain their original raw opcode. -/
theorem static_address_opcode :
    let address := { loader zeros (some ⟨1, [], none, false⟩) with code := [.ldsflda field] }
    methodShapeInstructions (rawStatic 127) address = true ∧
    methodShapeInstructions (rawStatic 126) address = false := by decide +kernel
#print axioms static_address_opcode

/-- A static instruction names the field of its raw instruction: another index, owner or stored
    type, an instance operand or another opcode is rejected, for loads, addresses and tokens. -/
theorem static_field_named :
    let method (code : List Instruction) := { loader zeros (some ⟨1, [], none, false⟩) with code }
    methodShapeInstructions (rawStatic 126) (method [.ldsfld field]) = true ∧
    methodShapeInstructions (rawStatic 126) (method [.ldsfld otherField]) = false ∧
    methodShapeInstructions (rawStatic 126) (method [.ldsfld otherOwner]) = false ∧
    methodShapeInstructions (rawStatic 126) (method [.ldsfld otherType]) = false ∧
    methodShapeInstructions (rawStatic 126 false) (method [.ldsfld field]) = false ∧
    methodShapeInstructions (rawStatic 127) (method [.ldsflda otherField]) = false ∧
    methodShapeInstructions (rawStatic 208) (method [.ldtoken (.field field)]) = true ∧
    methodShapeInstructions (rawStatic 208) (method [.ldtoken (.field otherField)]) = false ∧
    methodShapeInstructions (rawStatic 127) (method [.ldtoken (.field field)]) = false := by
  decide +kernel
#print axioms static_field_named

/-- Raw `ret`. -/
private def rawRet : RawInstruction := ⟨0, 42, .none⟩

/-- An `stsfld` after `ret` names its raw field and validates; stepping it faults, since no
    static field is writable. -/
theorem stsfld_faults :
    let stored : Method := { loader zeros none with code := [.ret, .stsfld field] }
    let frame : Safety.Frame := { activation := 0, locals := [], owned := [] }
    methodShapeInstructions (rawStatic 128 true [rawRet]) stored = true ∧
    methodShapeInstructions (rawStatic 128 true [rawRet])
      { stored with code := [.ret, .stsfld otherField] } = false ∧
    Safety.step stored (.stsfld field) 1 [] frame [.scalar (.i32 0)] initializerMemory =
      .error (.unsupported "Static field store") := by
  refine ⟨by decide +kernel, by decide +kernel, rfl⟩
#print axioms stsfld_faults

end Tests.StaticValueEvidence
