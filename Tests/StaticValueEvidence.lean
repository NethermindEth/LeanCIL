import CIL.Extraction.Translation

/-! Checks static readonly values against literal, method and constructor evidence. -/

namespace Tests.StaticValueEvidence
open CIL CIL.Extraction

private def zeros : List (BitVec 8) := [0, 0]

/-- Returns its zero-initialized two-byte aggregate local. -/
private def initializer : Method := {
  code := [.ldloc 0, .ret], locals := [.aggregate zeros], localKinds := [.aggregate 2],
  returnsValue := true }

/-- The static field the fixtures load, as the raw operand of `rawStatic` names it. -/
private def field : FieldRef :=
  { owner := .atom "Fixture" "Holder" .classType, index := 0,
      type := .atom "Fixture" "Pair" .valueType,
    name := name!"Zero" }

private def descriptor (bytes : List (BitVec 8)) (init : Option StaticInitializer) :
    StaticDescriptor :=
  { identity := 0, field, bytes, initializer := init }

/-- A second field of the same holder and type. -/
private def otherField : FieldRef := { field with index := 1, name := name!"One" }

/-- The field's index on another holder. -/
private def otherOwner : FieldRef := { field with owner := .atom "Fixture" "Other" .classType }

/-- The field's holder and index with another stored type. -/
private def otherType : FieldRef := { field with type := .atom "Fixture" "Word" .valueType }

/-- The field's holder, index and type under another name. -/
private def otherName : FieldRef := { field with name := name!"Other" }

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
  code := [.ldarg 0, .ldc_i4 7, .stind .i1, .ret]
  locals := [], returnsValue := false }

private def constructed (bytes : List (BitVec 8)) (callee : Method := constructor) : Program :=
  [loader bytes (some { method := 1, arguments := [], construct := true }), callee]

/-- Construction starts with initialized zero bytes and preserves untouched bytes. -/
theorem constructor_bytes : StaticValuesValid (constructed [7, 0]) := by decide +kernel
#print axioms constructor_bytes

/-- Changing the emitted constructor result does not change what checked execution produces. -/
theorem forged_constructor_bytes : ¬ StaticValuesValid (constructed [8, 0]) := by decide +kernel
#print axioms forged_constructor_bytes

/-- A method loading the field with the descriptor supplied at that site. -/
private def reading (site : StaticDescriptor) : Method :=
  { code := [.ldsfld site.field, .ret], locals := [], returnsValue := true,
    staticSites := [(0, site)] }

/-- The four-byte literal stored in one static field. -/
private def literalSite (byte : BitVec 8) : StaticDescriptor :=
  { identity := 0, field := { field with type := .primitive .uint32 },
    bytes := [byte, 0, 0, 0], scalar := some false,
    initializer := some ⟨0, [], some (.i32 (byte.zeroExtend 32)), false⟩ }

/-- Each literal reproduces its own bytes. Two methods can share the same descriptor or load
    different fields, but conflicting descriptors for one identity fail validation. -/
theorem descriptor_agreement :
    let first := literalSite 7
    let second := literalSite 8
    let otherField := { second.field with index := 1, name := name!"One" }
    let other := { second with identity := 1, field := otherField }
    StaticValuesValid [reading first, reading first] ∧
    StaticValuesValid [reading first, reading other] ∧
    StaticValuesValid [reading first, reading other, reading first] ∧
    ¬ StaticValuesValid [reading first, reading other, reading second] ∧
    ¬ StaticValuesValid [reading first, reading { first with field := otherField }] ∧
    ¬ StaticValuesValid [reading first, reading second] ∧
    ¬ StaticValuesValid [reading first, reading { first with alignment := 4 }] ∧
    ¬ StaticValuesValid [reading first, reading { first with initializer := none }] := by
  decide +kernel
#print axioms descriptor_agreement

/-- One initializer shared by every load in a method. -/
private def repeatedLoads (count : Nat) : Program :=
  let site := descriptor zeros (some ⟨1, [], none, false⟩)
  [{ code := (List.replicate count [.ldsfld field, .pop]).flatten ++ [.ret],
     staticSites := (List.range count).map (fun index => (2 * index, site)),
     locals := [], returnsValue := false }, initializer]

open Lean Elab Command Meta in
set_option maxHeartbeats 0 in
run_cmd do
  let cost (count : Nat) := do
    let claim ← `(decide (StaticValuesValid (repeatedLoads $(quote count))) = true)
    let statement ← liftTermElabM do
      instantiateMVars (← Term.elabTermAndSynthesize claim (some (mkSort 0)))
    let proof := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    let start ← IO.getNumHeartbeats
    match Kernel.check (← getEnv) {} (Expr.letE `checked statement proof (.bvar 0) false) with
    | .error error => throwKernelException error
    | .ok _ => return (← IO.getNumHeartbeats) - start
  let one ← cost 1
  let eight ← cost 8
  let many ← cost 64
  logInfo m!"static initializer check at 1, 8 and 64 loads: {one}, {eight}, {many} heartbeats"
  -- The first repeat pays for descriptor equality. Later sites only look up and compare.
  let maxPerAdditionalLoad := 1600
  if one ≥ eight || eight ≥ many || many - eight > (64 - 8) * maxPerAdditionalLoad then
    throwError "static initializer checks exceeded the kernel work budget per additional load"

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
  code := before ++ [⟨0, opcode, .field field.owner field.index field.type field.name isStatic⟩] }

/-- Constructor-initialized addresses retain their original raw opcode. -/
theorem static_address_opcode :
    let address := { loader zeros (some ⟨1, [], none, false⟩) with code := [.ldsflda field] }
    methodShapeInstructions (rawStatic 127) address = true ∧
    methodShapeInstructions (rawStatic 126) address = false := by decide +kernel
#print axioms static_address_opcode

/-- A static instruction names the field of its raw instruction: another index, owner, stored
    type or name, an instance operand or another opcode is rejected, for loads, addresses and
    tokens. -/
theorem static_field_named :
    let method (code : List Instruction) := { loader zeros (some ⟨1, [], none, false⟩) with code }
    methodShapeInstructions (rawStatic 126) (method [.ldsfld field]) = true ∧
    methodShapeInstructions (rawStatic 126) (method [.ldsfld otherField]) = false ∧
    methodShapeInstructions (rawStatic 126) (method [.ldsfld otherOwner]) = false ∧
    methodShapeInstructions (rawStatic 126) (method [.ldsfld otherType]) = false ∧
    methodShapeInstructions (rawStatic 126) (method [.ldsfld otherName]) = false ∧
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
