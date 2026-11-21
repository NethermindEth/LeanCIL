import CIL.Safety.Execution
import CIL.Safety.ValueSteps
import CIL.Resolution

/-!
# Declared return narrowing

The return instruction obtains its narrowing from the method's declared metadata. A body in the
emitted form, with a struct return and a non-empty layout environment, still evaluates by `rfl`
under the default recursion limit, as generated boundary claims are proved.
-/

namespace Tests.ReturnOpcode

open CIL CIL.Safety

/-- A byte-returning method whose stack value exceeds the declared storage width. -/
private def byteBody : Method :=
  { code := [.ldc_i4 300, .ret], locals := [], returnsValue := true,
    declared := { returnType := .atom Extraction.runtimeScope "System.Byte" } }

/-- A return narrows the result according to the method declaration. -/
theorem byte_return (pc : Nat) (args : List Safety.Value) (frame : Frame)
    (memory : Safety.Memory) :
    Safety.step byteBody .ret pc args frame [.scalar (.i32 300)] memory =
      .ok (.returned [.scalar (.i32 44)] memory) := by
  rfl

#print axioms byte_return

/-- Handwritten bodies simplify return storage without generated projection facts. -/
theorem byte_return_simplified (frame : Frame) (memory : Safety.Memory) :
    Safety.step byteBody .ret 0 [] frame [.scalar (.i32 300)] memory =
      .ok (.returned [.scalar (.i32 44)] memory) := by
  simp only [step_ret_eq, cil_step, show byteBody.returnsValue = true from rfl]
  rfl
#print axioms byte_return_simplified

/-- A one-instruction method with a declared primitive return type. -/
private def primitiveBody (type : PrimitiveType) : Method :=
  { code := [.ret], locals := [], returnsValue := true,
    declared := { returnType := type.typeExpr } }

/-- Each primitive's return storage is applied by the checked dispatcher. -/
theorem primitive_return (type : PrimitiveType) (bits : W32) (frame : Frame)
    (memory : Safety.Memory) :
    Safety.step (primitiveBody type) .ret 0 [] frame [.scalar (.i32 bits)]
      memory = .ok (.returned
        [.scalar (.i32 (match type.narrow with | some kind => kind.extend bits | none => bits))]
        memory) := by
  cases type <;> rfl
#print axioms primitive_return

/-- A declared narrow return requires exactly one 32-bit integer. -/
theorem invalid_narrow_returns (frame : Frame) (memory : Safety.Memory) :
    Safety.step byteBody .ret 0 [] frame [] memory = .error .invalidState ∧
    Safety.step byteBody .ret 0 [] frame [.scalar (.i64 300)] memory = .error .invalidState ∧
    Safety.step byteBody .ret 0 [] frame [.scalar (.i32 1), .scalar (.i32 2)] memory =
      .error .invalidState := by
  exact ⟨rfl, rfl, rfl⟩
#print axioms invalid_narrow_returns

/-- Void methods ignore declared narrow metadata and require an empty return stack. -/
theorem void_return (frame : Frame) (memory : Safety.Memory) :
    Safety.step { byteBody with returnsValue := false } .ret 0 [] frame [] memory =
      .ok (.returned [] memory) ∧
    Safety.step { byteBody with returnsValue := false } .ret 0 [] frame
      [.scalar (.i32 1)] memory = .error .invalidState := by
  exact ⟨rfl, rfl⟩
#print axioms void_return

/-- Unspecified vector bits are rejected before return storage conversion. -/
theorem unspecified_return (frame : Frame) (memory : Safety.Memory) :
    Safety.step byteBody .ret 0 [] frame [.scalar (.v128Low64 0)] memory =
      .error (.unsupported "Instruction observes unspecified vector bits") := rfl
#print axioms unspecified_return

/-- The reference interpreter receives narrowing explicitly. -/
theorem reference_return :
    CIL.step .ret true (some .unsigned8) 0 [.i32 300] (fun _ => none) .scalar =
      some (.returned [.i32 44] (fun _ => none)) := rfl
#print axioms reference_return

/-- Both standalone interpreters reject a narrow return paired with void arity. -/
theorem inconsistent_void_return (memory : Safety.Memory) :
    CIL.step .ret false (some .unsigned8) 0 [] (fun _ => none) .scalar = none ∧
    returnFrom (some .unsigned8) false [.scalar (.i32 1)] memory = .error .invalidState :=
  ⟨rfl, rfl⟩
#print axioms inconsistent_void_return

/-- Returning a reference still checks that its allocation exists. -/
theorem invalid_reference_return (frame : Frame) :
    Safety.step (primitiveBody .int32) .ret 0 [] frame [.reference (.address ⟨0, 0⟩)]
      Safety.Memory.empty = .error (.memory .missingAllocation (.address ⟨0, 0⟩) 0) := rfl
#print axioms invalid_reference_return

/-- A byte declaration cannot satisfy the full-width bitwise helper's return premise. -/
theorem byte_not_full_width :
    byteBody.declared.returnType ≠ .atom Extraction.runtimeScope "System.Int32" := by
  decide
#print axioms byte_not_full_width

/-- A struct of two 32-bit fields, recorded with the generic identity an extraction writes;
    the identity is as long as a closed generic struct's, whose comparison once exhausted the
    elaborator's recursion limit. -/
private def pairLayouts : List Extraction.RawLayout := [
  { identity := "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null::\
      Examples.StaticPair`1<System.Runtime, Version=11.0.0.0, Culture=neutral, \
      PublicKeyToken=b03f5f7f11d50a3a::System.UInt32>",
    explicit := false, auto := true, packing := -1, declaredSize := -1,
    fields := [{ type := .signed32, offset := none }, { type := .signed32, offset := none }] }]

/-- The layout environment an extraction records for `pairLayouts`. -/
private def pairEnvironment : LayoutEnvironment :=
  { rawLayouts := pairLayouts, layouts := #[⟨⟨8, [⟨0, 4, false⟩, ⟨4, 4, false⟩]⟩, 4⟩] }

/-- `Math.DivRem(int, int)` in the emitted form: a declared struct return over a non-empty
    environment, with the identity written out as a literal as an extraction writes it. -/
private def pairDivRem : Method :=
  { profile := .scalar, returnsValue := true, locals := [], environment := pairEnvironment,
    declared := {
      parameters := [.atom Extraction.runtimeScope "System.Int32",
        .atom Extraction.runtimeScope "System.Int32"],
      returnType := .aggregate "Examples, Version=1.0.0.0, Culture=neutral, \
        PublicKeyToken=null::Examples.StaticPair`1<System.Runtime, Version=11.0.0.0, \
        Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a::System.UInt32>" 0 }
    code := [.ldarg 0, .ldarg 1, .intrinsic (.scalar (.divRem 32 true)) 2, .ret] }

/-- A generated boundary claim about a struct-returning body is proved by evaluation, with the
    proof term a generated fixture uses and the default recursion limit. -/
theorem pair_return_evaluates :
    (invoke [pairDivRem] 8 0 [.scalar (.i32 7), .scalar (.i32 2)] Memory.empty).map Prod.snd =
      .ok [.scalar (.aggregate [3, 0, 0, 0, 1, 0, 0, 0])] := by
  rfl
#print axioms pair_return_evaluates

/-- The existential form of a generated struct claim elaborates by the same evaluation. -/
theorem pair_return_exists :
    ∃ bytes, (invoke [pairDivRem] 8 0 [.scalar (.i32 7), .scalar (.i32 2)]
      Memory.empty).map Prod.snd = .ok [.scalar (.aggregate bytes)] ∧ bytes.length = 8 :=
  ⟨_, rfl, by decide⟩
#print axioms pair_return_exists

private def remainderField : Extraction.FieldRef :=
  { owner := .aggregate "SBytePair" 0, index := 1, name := name!"Item2",
    type := .atom Extraction.runtimeScope "System.SByte" }

/-- `Math.DivRem(sbyte, sbyte).Remainder` over a two-byte struct layout, whose
    narrowing return compares only its runtime scope and primitive name. -/
private def sbyteRemainder : Method :=
  { pairDivRem with
    environment := {
      rawLayouts := [
        { identity := "SBytePair", explicit := false, packing := 0, declaredSize := 0,
          fields := [{ type := .signed8 }, { type := .signed8 }] }]
      layouts := #[⟨⟨2, [⟨0, 1, false⟩, ⟨1, 1, false⟩]⟩, 1⟩] }
    declared := {
      parameters := [.atom Extraction.runtimeScope "System.SByte",
        .atom Extraction.runtimeScope "System.SByte"],
      returnType := .atom Extraction.runtimeScope "System.SByte" }
    code := [.ldarg 0, .ldarg 1,
      .intrinsic (.scalar (.divRem 8 true)) 2, .ldfld remainderField, .ret] }

/-- A narrowing return over a non-empty environment is proved by evaluation, and the remainder
    of -7 by 2 comes back sign-extended. -/
theorem sbyte_return_evaluates :
    (invoke [sbyteRemainder] 8 0 [.scalar (.i32 4294967289), .scalar (.i32 2)]
      Memory.empty).map Prod.snd = .ok [.scalar (.i32 4294967295)] := by
  rfl
#print axioms sbyte_return_evaluates

end Tests.ReturnOpcode
