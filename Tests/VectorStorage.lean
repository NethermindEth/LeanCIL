import CIL.Extraction.VectorInitialization

/-! Exact integer-vector object encodings, independently of generated source or DLL hashes. -/

namespace Tests.VectorStorage
open CIL CIL.Extraction

/-- The admitted integer element types shared by vector storage operations. -/
private def elements :=
  ["System.Byte", "System.Int32", "System.UInt32", "System.Int64", "System.UInt64"]

/-- Exact runtime metadata for one integer-vector width and element. -/
private def vectorType (bits : Nat) (element : String) : TypeExpr :=
  .apply (.constructor intrinsicsScope s!"System.Runtime.Intrinsics.Vector{bits}`1")
    (.atom runtimeScope element)

/-- Each object opcode paired with the operation for its validated vector width. -/
private def operations (bytes : Nat) : List (Nat × Op) :=
  [(0x70, .copyObject bytes), (0xfe15, .initAggregate bytes),
   (0xfe1c, .const32 (BitVec.ofNat 32 bytes)),
   (0x71, .memory (if bytes == 16 then .load128 else if bytes == 32 then .load256 else .load512)),
   (0x81, .memory (if bytes == 16 then .store128 else if bytes == 32 then .store256 else .store512))]

/-- All admitted integer types use the same checked bit storage at each vector width. -/
theorem integer_storage_checked :
    [16, 32, 64].all (fun bytes => elements.all fun element =>
      (operations bytes).all fun (opcode, operation) =>
        vectorInitializationMatches ⟨0, opcode, .type (vectorType (bytes * 8) element)⟩
          operation) = true := by decide +kernel

#print axioms integer_storage_checked

/-- Wrong widths, primitive substitution, unsupported elements and scopes cannot certify. -/
theorem altered_storage_rejected :
    [16, 32, 64].all (fun bytes =>
      (operations bytes).all fun (opcode, operation) =>
        !(vectorInitializationMatches
          ⟨0, opcode, .type (vectorType (if bytes == 16 then 256 else 128) "System.UInt32")⟩
          operation) &&
        !(vectorInitializationMatches
          ⟨0, opcode, .type (vectorType (bytes * 8) "System.Int16")⟩ operation) &&
        !(vectorInitializationMatches ⟨0, opcode, .type
          (.apply (.constructor "forged" s!"System.Runtime.Intrinsics.Vector{bytes * 8}`1")
            (.atom runtimeScope "System.UInt32"))⟩ operation) &&
        !(vectorInitializationMatches ⟨0, opcode, .none⟩ operation)) = true := by
  decide +kernel

#print axioms altered_storage_rejected

/-- Stack-effect-equivalent primitive and incorrect object operations are rejected directly. -/
theorem changed_object_meaning_rejected :
    vectorInitializationMatches ⟨0, 0x71, .type (.atom runtimeScope "System.UInt64")⟩
      (.memory .load128) = false ∧
    vectorInitializationMatches ⟨0, 0x70, .type (.atom runtimeScope "System.UInt64")⟩
      (.copyObject 16) = false ∧
    vectorInitializationMatches ⟨0, 0xfe15, .type (vectorType 128 "System.UInt32")⟩
      .nop = false ∧
    vectorInitializationMatches ⟨0, 0x71, .type (vectorType 128 "System.UInt32")⟩
      (.initAggregate 16) = false := by decide +kernel

#print axioms changed_object_meaning_rejected

end Tests.VectorStorage
