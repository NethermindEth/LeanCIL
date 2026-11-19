import CIL.Extraction.DecodedDefinition
import CIL.Extraction.DecodedMethod

/-! Decoder refusal tests for incomplete method-token operands. -/

namespace Tests.LoweredCallRefusal
open CIL CIL.Extraction

/-- A managed member with no runtime model, embedded in a static caller. -/
private def body (opcode : Nat) (owner : TypeExpr) (member : MetadataName) (name : String) :
    RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false, callingConvention := 0,
  attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
  initLocals := false, maxStack := 0, genericParameters := [],
  code := [⟨0, opcode, .call {
    method := {
      owner, name := member, hasThis := opcode != 40, genericArity := 0,
      returnType := .void, parameters := [] },
    declared := { convention := if opcode == 40 then 0 else 0x20 }, name, target := .managed 2,
    typeArguments := [], parameterCount := 0, returnsValue := false }⟩] }

/-- Removing a managed member's direct link leaves a hole tagged with its own opcode. -/
private def withoutLink (opcode : Nat) (member : MetadataName) (name : String) : Bool := Id.run do
  let source := body opcode (.object "Fixture" "Fixture") member name
  let some raw := source.code.head? | return false
  let requirement := fun link => runtimeCatalog.callRequirement
    (LayoutEnvironment.callLayouts {}) .scalar link none raw
  return (requirement (some (.direct 0)) matches .linked) &&
    decide ((Method.ofRaw? .scalar {} [] [true] source []).map Method.code =
      some [.unadmitted opcode]) &&
    (requirement none).accepts false (.unadmitted opcode) &&
    !(requirement none).accepts true (.unadmitted opcode)

/-- A direct managed call requires its link. -/
theorem unclaimed : withoutLink 40 name!"Run" "Run" = true := rfl
#print axioms unclaimed

/-- A virtual managed call requires its dispatch binding. -/
theorem virtualCall : withoutLink 111 name!"Run" "Run" = true := rfl
#print axioms virtualCall

/-- A managed constructor requires its construction binding. -/
theorem construction : withoutLink 115 name!".ctor" ".ctor" = true := rfl
#print axioms construction

/-- Both helpers use the same scoped vector type in each occurrence of their type argument. -/
private def vectorSite (read : Bool) (element : String) : RawInstruction := Id.run do
  let vector := fun name => TypeExpr.apply (.constructor intrinsicsScope
    "System.Runtime.Intrinsics.Vector128`1") (.atom runtimeScope name)
  let source := vector element
  let target := vector "System.UInt64"
  let arguments := if read then [source] else [source, target]
  let byteRef := TypeExpr.byref (.atom runtimeScope "System.Byte")
  let signature := if read then
    "!!0 System.Runtime.CompilerServices.Unsafe::ReadUnaligned(System.Byte&)"
    else "!!1 System.Runtime.CompilerServices.Unsafe::BitCast(!!0)"
  return ⟨0, 40, .call {
    method := {
      owner := .atom runtimeScope "System.Runtime.CompilerServices.Unsafe",
      name := if read then name!"ReadUnaligned" else name!"BitCast", hasThis := false,
      genericArity := arguments.length, methodArguments := arguments,
      parameters := [if read then byteRef else source],
      returnType := if read then source else target }
    declared := {
      convention := 0x10, returnType := .parameter (if read then 0 else 1),
      parameters := [if read then byteRef else .parameter 0] }
    name := if read then "ReadUnaligned" else "BitCast", typeArguments := arguments,
    target := .external s!"{runtimeScope}::{signature}", parameterCount := 1,
    returnsValue := true }⟩

/-- A change of vector element alone is sufficient to refuse either transfer. -/
theorem integerVectorTransfers :
    let decode := fun raw => methodCode .scalar {} [] [true]
      { body 40 .void name!"Run" "Run" with code := [raw] }
    let control := vectorSite false "System.Byte"
    (match control.operand with
      | .call site => decide (decode control = [.call site.method {}])
      | _ => false) = true ∧
      decode (vectorSite false "System.Double") = [.unadmitted 40] ∧
      (match (vectorSite true "System.Byte").operand with
       | .call site => decide (decode (vectorSite true "System.Byte") = [.call site.method {}])
       | _ => false) = true ∧
      decode (vectorSite true "System.Double") = [.unadmitted 40] := by decide +kernel

#print axioms integerVectorTransfers

/-- The one-instruction decoder exposes the hole's opcode even at a reachable call. -/
private def arithmeticCode (env : LayoutEnvironment) (site : CallSite) :=
  (Method.ofRaw? .scalar env [] [true]
    { body 40 .void name!"Run" "Run" with code := [⟨0, 40, .call site⟩] } []).map Method.code

/-- Both arithmetic members bind the raw operand and the closed signature independently. -/
private def arithmeticChecks (env : LayoutEnvironment) (site : CallSite)
    (unsupported : CallSite) (expected : RuntimeModel) : Bool :=
  let method := site.method
  let wrong := TypeExpr.atom runtimeScope "System.Boolean"
  let refusals := [
    { site with method.owner := .atom "Fixture" "System.Math" },
    { site with method.name := name!"Wrong" }, { site with name := "Wrong" },
    { site with method.genericArity := 1 }, { site with method.hasThis := true },
    { site with parameterCount := site.parameterCount + 1 },
    { site with method.parameters := method.parameters.set 0 wrong },
    { site with method.returnType := wrong }, { site with declared.convention := 0x20 },
    { site with target := .external "Wrong" }, unsupported]
  runtimeModel env .call method == some expected &&
    decide (arithmeticCode env site = some [.call method {}]) &&
    refusals.all fun changed => decide (arithmeticCode env changed = some [.unadmitted 40])

/-- A signed widening multiply accepts int32 input and rejects an int16 widening signature. -/
theorem bigMulBinding :
    let site := fun (element : String) =>
      let word := TypeExpr.atom runtimeScope element
      let method : MethodRef := {
        owner := .atom runtimeScope "System.Math", name := name!"BigMul", hasThis := false,
        genericArity := 0, returnType := .atom runtimeScope "System.Int64",
        parameters := [word, word] }
      let target := s!"System.Int64 System.Math::BigMul({element},{element})"
      ({ method, name := "BigMul", declared := method.signature 0,
         target := .external s!"{runtimeScope}::{target}",
         typeArguments := [], parameterCount := 2, returnsValue := true } : CallSite)
    arithmeticChecks {} (site "System.Int32") (site "System.Int16")
      (.intrinsic (.scalar (.bigMul32 true)) 2) = true := by decide +kernel

#print axioms bigMulBinding

/-- DivRem binds the tuple's indexed declaration, both field types, packing and alignment. -/
theorem divRemTupleLayout :
    let pair := "System.ValueTuple`2<System.UInt64,System.UInt64>"
    let identity := s!"{runtimeScope}::{pair}"
    let word := TypeExpr.atom runtimeScope "System.UInt64"
    let method : MethodRef := {
      owner := .atom runtimeScope "System.Math", name := name!"DivRem",
      genericArity := 0, hasThis := false, returnType := .aggregate identity 1,
      parameters := [word, word] }
    let site : CallSite := {
      method, declared := method.signature 0, name := "DivRem",
      target := .external s!"{identity} System.Math::DivRem(System.UInt64,System.UInt64)",
      typeArguments := [], parameterCount := 2, returnsValue := true }
    let row : RawLayout := {
      identity, auto := true, explicit := false, declaredSize := 0,
      packing := 0, fields := [⟨.unsigned64, none⟩, ⟨.unsigned64, none⟩] }
    let env := fun (raw : RawLayout) alignment =>
      let computed := (⟨⟨16, [⟨0, 8, false⟩, ⟨8, 8, false⟩]⟩, alignment⟩ : ComputedLayout)
      ({ rawLayouts := [{ row with identity := "Fixture" }, raw],
         layouts := #[computed, computed] } : LayoutEnvironment)
    let refused := fun raw alignment =>
      arithmeticCode (env raw alignment) site = some [.unadmitted 40]
    let boolean := TypeExpr.atom runtimeScope "System.Boolean"
    let result := "System.ValueTuple`2<System.Boolean,System.Boolean>"
    let invalid := { method with
      parameters := [boolean, boolean]
      returnType := .aggregate (runtimeScope ++ "::" ++ result) 1 }
    let target := s!"{result} System.Math::DivRem(System.Boolean,System.Boolean)"
    let unsupported := { site with
      method := invalid, declared := invalid.signature 0,
      target := .external (runtimeScope ++ "::" ++ target) }
    arithmeticChecks (env row 8) site unsupported (.intrinsic (.scalar (.divRem 64 false)) 2) ∧
      arithmeticCode (env row 8) { site with declared.returnType := .aggregate identity 0 } =
        some [.unadmitted 40] ∧
      refused { row with fields := row.fields.set 0 ⟨.signed64, none⟩ } 8 ∧
      refused { row with fields := row.fields.set 1 ⟨.signed64, none⟩ } 8 ∧
      refused { row with fields := List.replicate 512 ⟨.unsigned64, none⟩ } 8 ∧
      refused { row with packing := 1 } 8 ∧ refused row 1 := by decide +kernel

#print axioms divRemTupleLayout

/-- The open vector parameter of Sum belongs to the method. -/
theorem sumDeclaration :
    let owner := "System.Runtime.Intrinsics.Vector128"
    let vector := TypeExpr.apply (.constructor intrinsicsScope (owner ++ "`1"))
    let word := TypeExpr.atom runtimeScope "System.UInt64"
    let site : CallSite := {
      method := {
        owner := .atom intrinsicsScope owner, name := name!"Sum", hasThis := false,
        genericArity := 1, methodArguments := [word], returnType := word,
        parameters := [vector word] }
      name := "Sum", parameterCount := 1, returnsValue := true, typeArguments := [word],
      declared := {
        convention := 0x10, returnType := .parameter 0, parameters := [vector (.parameter 0)] }
      target := .external s!"{intrinsicsScope}::!!0 {owner}::Sum({owner}`1<!!0>)" }
    let resolve := fun operand => LoweredFamily.hardware.resolve
      (LayoutEnvironment.callLayouts {}) .scalar none ⟨0, 40, .call operand⟩
    resolve site = some (.intrinsic (.vector (.sum64 128)) 1) ∧
      resolve { site with declared.parameters := [vector (.ownerParameter 0)] } = none := by
  decide +kernel

#print axioms sumDeclaration

/-- The empty layout environment of the method with an unknown call. -/
private def emptyEnvironment : LayoutEnvironment := {}

cil_decoded_method unknownMethod := Method.ofRaw? .scalar emptyEnvironment [] [true]
  (body 40 (.atom "Fixture" "Fixture") name!"Missing" "Missing") []

/-- The generated code contains exactly the hole for the unresolved member. -/
theorem unknownMethodCode : unknownMethod.code = [.unadmitted 40] := rfl

#print axioms unknownMethodCode

/-- The linked instance slot takes the receiver type from the preceding constrained prefix. -/
private def constrainedSlot : CallSite := {
  method := {
    owner := .object "Fixture" "Fixture.Interface", name := name!"Read",
    hasThis := true, genericArity := 0, returnType := .void, parameters := [] },
  declared := { convention := 0x20 }, name := "Read", target := .managed 1, typeArguments := [],
  parameterCount := 0, returnsValue := false }

/-- Closed decoding preserves a constrained receiver at a linked call and refuses an unowned pc. -/
theorem constrainedLinkCode :
    let receiver := TypeExpr.atom runtimeScope "System.Int32"
    let source := { body 111 constrainedSlot.declaringType name!"Read" "Read" with
      code := [⟨0, 0xFE16, .type receiver⟩, ⟨6, 111, .call constrainedSlot⟩] }
    let decode := fun links =>
      (Method.ofRaw? .scalar {} links [true, true] source []).map Method.code
    decode [(1, .direct 1)] = some [.nop, .call constrainedSlot.method
      { constrained := some receiver }] ∧ decode [] = some [.nop, .unadmitted 111] := by
  exact ⟨rfl, rfl⟩

#print axioms constrainedLinkCode

/-- Every resolved family rejects every instruction other than its exact result. -/
theorem otherInstructionRefused (family : LoweredFamily) (environment : LayoutEnvironment)
    (profile : FeatureProfile) (raw : RawInstruction) (role : Option FoldRole)
    (expected emitted : Instruction) (called : methodTokenCall raw.opcode = true)
    (claimed : siteClaim loweredCallFamily environment none raw = .lowered family)
    (resolved : family.resolve environment.callLayouts profile role raw = some expected)
    (other : emitted ≠ expected) :
    runtimeCatalog.siteAgrees environment profile raw emitted none role true = false := by
  change siteClaim loweredCallFamily environment none raw runtimeCatalog.table.claims =
    .lowered family at claimed
  simp [ModelCatalog.siteAgrees, ModelCatalog.agreesAt, called,
    ModelCatalog.callRequirement, claimed, resolved,
    CallRequirement.accepts, other]

#print axioms otherInstructionRefused

/-- A missing overload requires its own opcode's hole and is refused at a live site. -/
theorem missingOverloadRefused (family : LoweredFamily) (environment : LayoutEnvironment)
    (profile : FeatureProfile) (raw : RawInstruction) (role : Option FoldRole)
    (emitted : Instruction) (called : methodTokenCall raw.opcode = true)
    (claimed : siteClaim loweredCallFamily environment none raw = .lowered family)
    (missing : family.resolve environment.callLayouts profile role raw = none) :
    runtimeCatalog.siteAgrees environment profile raw emitted none role true = false ∧
    (runtimeCatalog.siteAgrees environment profile raw emitted none role false = true ↔
      emitted = .unadmitted raw.opcode) := by
  change siteClaim loweredCallFamily environment none raw runtimeCatalog.table.claims =
    .lowered family at claimed
  simp [ModelCatalog.siteAgrees, ModelCatalog.agreesAt, called,
    ModelCatalog.callRequirement, claimed, missing,
    CallRequirement.accepts]

#print axioms missingOverloadRefused

end Tests.LoweredCallRefusal
