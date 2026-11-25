import CIL.Extraction.ObjectOperands
import CIL.Safety.Execution

/-! Exact integer-vector object encodings, independently of generated source or DLL hashes. -/

namespace Tests.VectorStorage
open CIL CIL.Extraction

/-- The admitted integer element types shared by vector storage operations. -/
private def elements : List PrimitiveType := [.byte, .int32, .uint32, .int64, .uint64]

/-- Exact runtime metadata for one integer-vector width and element. -/
private def vectorType (bits : Nat) (element : PrimitiveType) : TypeExpr :=
  .apply (.constructor intrinsicsScope s!"System.Runtime.Intrinsics.Vector{bits}`1")
    (.primitive element)

/-- Each object instruction retains its exact type operand. -/
private def operations (type : TypeExpr) : List (Nat × Instruction) :=
  [(0x70, .cpobj type), (0xfe15, .initobj type), (0xfe1c, .sizeof type),
    (0x71, .ldobj type), (0x81, .stobj type)]

/-- Every supported integer element decodes to an operation on the vector of that width. -/
theorem integer_storage_checked :
    [128, 256, 512].all (fun bits => elements.all fun element =>
      let type := vectorType bits element
      let shape := ({} : LayoutEnvironment).valueShape type
      shape == .vector (bits / 8) && (operations type).all fun (opcode, operation) =>
        valueEncodingMatches none ⟨0, opcode, .type type⟩ operation &&
          objectShapeAdmitted opcode type shape) = true := by decide +kernel
#print axioms integer_storage_checked

/-- Site binding rejects altered widths. Admission checks element types and scopes. -/
theorem altered_storage_rejected :
    [128, 256, 512].all (fun bits =>
      let type := vectorType bits .uint32
      let other := vectorType (if bits == 128 then 256 else 128) .uint32
      let wrong := TypeExpr.apply
        (.constructor "forged" s!"System.Runtime.Intrinsics.Vector{bits}`1")
        (.primitive .uint32)
      (operations type).all fun (opcode, operation) =>
        !valueEncodingMatches none ⟨0, opcode, .type other⟩ operation &&
        !valueEncodingMatches none ⟨0, opcode, .none⟩ operation &&
        [vectorType bits .int16, vectorType bits .double, wrong].all fun operand =>
          !objectShapeAdmitted opcode operand (({} : LayoutEnvironment).valueShape operand)) =
      true := by
  decide +kernel
#print axioms altered_storage_rejected

/-- A different transfer with the same stack depth fails the literal site's encoding check. -/
theorem changed_object_meaning_rejected :
    let type := vectorType 128 .uint32
    !valueEncodingMatches none ⟨0, 0x71, .type type⟩ (.ldobj (vectorType 256 .uint32)) &&
      !valueEncodingMatches none ⟨0, 0xfe15, .type type⟩ .nop &&
      !valueEncodingMatches none ⟨0, 0x71, .type type⟩ (.initobj type) := by decide +kernel
#print axioms changed_object_meaning_rejected

/-- Whole-vector operations reject incomplete 512-bit snapshots and wrong-width opaque values. -/
theorem incomplete_vector512_rejected :
    Safety.checkedIntrinsic (.vector (.equalsAll 512))
        [.snapshot .vector512 (List.replicate 63 (0, true) ++ [(0, false)]), .v512 0] =
      .error .invalidState ∧
    Safety.checkedIntrinsic (.vector (.band 512)) [.v128Low64 0, .v512 0] =
      .error (.unsupported "Intrinsic observes unspecified vector bits") := ⟨rfl, rfl⟩
#print axioms incomplete_vector512_rejected

end Tests.VectorStorage
