import CIL.Extraction.Translation

/-! Regression checks for indexed homes, opaque locals and static-load evidence. -/

namespace Tests.ExtractionHomeIndexes
open CIL CIL.Extraction

/-- Duplicate references, invalid indexes and a truncated mask retain the old home set. -/
theorem home_edges : requiredHomeIndices
    ⟨List.replicate 4 .reference, [], [.store 3, .address 1, .store 3, .store 9, .store 0]⟩
    [true, true, true, true] = [1, 3] := by decide +kernel
#print axioms home_edges

/-- Duplicate home claims keep the first appended slot, and absent homes have no slot. -/
theorem home_slots : (argumentHomeIndex [2, 0, 2] 5)[2]? = some 5 ∧
    (argumentHomeIndex [2, 0, 2] 5)[0]? = some 6 ∧
    (argumentHomeIndex [2, 0, 2] 5)[1]? = none := by decide +kernel
#print axioms home_slots

/-- Indexed argument validation rejects missing arguments, incorrect slots and short masks. -/
theorem argument_bounds :
    argumentInstructionsValid ⟨[.field .unsigned64], [], [.store 1]⟩ [1]
      [true] [.setLocal 0] = false ∧
    argumentInstructionsValid ⟨[.field .unsigned64], [], [.store 0]⟩ [0]
      [true] [.setLocal 1] = false ∧
    argumentInstructionsValid ⟨[.field .unsigned64], [], [.store 0]⟩ [0]
      [] [.setLocal 0] = false := by decide +kernel
#print axioms argument_bounds

/-- Pruned instructions must remain unsupported, even when their indexes are invalid. -/
theorem pruned_argument :
    argumentInstructionsValid ⟨[], [], [.load 99]⟩ []
      [false] [.unsupported "dead"] = true ∧
    argumentInstructionsValid ⟨[], [], [.load 99]⟩ [] [false] [.arg 99] = false := by
  decide +kernel
#print axioms pruned_argument
/-- A minimal raw body for metadata-only validation. -/
def raw : RawMethod := {
  token := 1, owner := "Indexes", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := true, maxStack := 1,
  genericParameters := [], code := [] }

/-- Whole-vector locals are eligible only when no instruction takes their address. -/
def vectorType : TypeExpr := .apply
  (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1")
  (.atom runtimeScope "System.UInt64")

/-- Both address encodings exclude locals, even in unreachable raw code. -/
theorem opaque_edges : opaqueLocalIndices { raw with
    locals := [vectorType, vectorType, .void, vectorType, vectorType],
    code := [⟨0, 18, .local 1⟩, ⟨1, 65037, .local 3⟩, ⟨2, 18, .local 99⟩] } = [0, 4] := by
  decide +kernel
#print axioms opaque_edges

/-- A one-byte unsigned static field descriptor. -/
def descriptor : StaticDescriptor := ⟨0, "Field", [0], none, some false, ""⟩

/-- The matching raw static field load. -/
def load : RawInstruction :=
  ⟨0, 126, .field .void 0 (.atom runtimeScope "System.Byte") true⟩

/-- An emitted scalar load with caller-provided static metadata. -/
def body (sites : List (Nat × StaticDescriptor)) : Method := {
  code := [.memory (.staticValue [0])], locals := [], returnsValue := false, staticSites := sites }

/-- Duplicate static sites use the first descriptor, rather than overwriting it. -/
theorem first_static_wins :
    methodShapeInstructions [] { raw with code := [load] }
      (body [(0, descriptor), (0, { descriptor with scalar := some true })]) = true ∧
    methodShapeInstructions [] { raw with code := [load] }
      (body [(0, { descriptor with scalar := some true }), (0, descriptor)]) = false := by
  decide +kernel
#print axioms first_static_wins

/-- Missing raw instructions, absent descriptors and wrong raw opcodes cannot pass. -/
theorem missing_static_rejects :
    methodShapeInstructions [] raw (body [(0, descriptor)]) = false ∧
    methodShapeInstructions [] { raw with code := [load] } (body []) = false ∧
    methodShapeInstructions [] { raw with code := [{ load with opcode := 0 }] }
      (body [(0, descriptor)]) = false := by decide +kernel
#print axioms missing_static_rejects

/-- Sparse homes retain ascending order and discard out-of-range references. -/
theorem sparse_homes : requiredHomeIndices
    ⟨List.replicate 1024 (.field .unsigned64), [],
      [.store 1000, .address 2, .store 1000, .store 1024, .store 0]⟩
    [true, true, true, true, false] = [2, 1000] := by decide +kernel
#print axioms sparse_homes
end Tests.ExtractionHomeIndexes
