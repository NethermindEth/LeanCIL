import Tests.Support.EnumIdentity
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

/-- Indexed argument validation accepts a store to a homed argument and rejects missing
    arguments, incorrect indexes, a store to the home slot and short masks. -/
theorem argument_bounds :
    argumentInstructionsValid ⟨[.field .unsigned64], [], [.store 0]⟩ [0]
      [true] [.starg 0] = true ∧
    argumentInstructionsValid ⟨[.field .unsigned64], [], [.store 1]⟩ [1]
      [true] [.starg 1] = false ∧
    argumentInstructionsValid ⟨[.field .unsigned64], [], [.store 0]⟩ [0]
      [true] [.starg 1] = false ∧
    argumentInstructionsValid ⟨[.field .unsigned64], [], [.store 0]⟩ [0]
      [true] [.stloc 0] = false ∧
    argumentInstructionsValid ⟨[.field .unsigned64], [], [.store 0]⟩ [0]
      [] [.starg 0] = false := by decide +kernel
#print axioms argument_bounds

/-- Pruned instructions must be holes, even when their indexes are invalid. -/
theorem pruned_argument :
    argumentInstructionsValid ⟨[], [], [.load 99]⟩ []
      [false] [.unadmitted 0x0E] = true ∧
    argumentInstructionsValid ⟨[], [], [.load 99]⟩ [] [false] [.ldarg 99] = false := by
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
  (.primitive .uint64)

/-- Both address encodings exclude locals, even in unreachable raw code. -/
theorem opaque_edges : opaqueLocalIndices { raw with
    locals := [vectorType, vectorType, .void, vectorType, vectorType],
    code := [⟨0, 18, .local 1⟩, ⟨1, 65037, .local 3⟩, ⟨2, 18, .local 99⟩] } = [0, 4] := by
  decide +kernel
#print axioms opaque_edges

/-- The matching raw static field load. -/
def load : RawInstruction :=
  ⟨0, 126, .field .void 0 (.primitive .byte) name!"Value" true⟩

/-- The field `load` names. -/
def loaded : FieldRef :=
  { owner := .void, index := 0, type := .primitive .byte, name := name!"Value" }

/-- A one-byte unsigned static field descriptor of `loaded`. -/
def descriptor : StaticDescriptor := ⟨0, loaded, [0], none, some false, 1, false⟩

/-- An emitted scalar load with caller-provided static metadata. -/
def body (sites : List (Nat × StaticDescriptor)) : Method := {
  code := [.ldsfld loaded], locals := [], returnsValue := false, staticSites := sites }

/-- Duplicate static sites use the first descriptor, rather than overwriting it. -/
theorem first_static_wins :
    methodShapeInstructions { raw with code := [load] }
      (body [(0, descriptor), (0, { descriptor with scalar := some true })]) = true ∧
    methodShapeInstructions { raw with code := [load] }
      (body [(0, { descriptor with scalar := some true }), (0, descriptor)]) = false := by
  decide +kernel
#print axioms first_static_wins

/-- A scalar static load with matching enum identities and a descriptor of the given width. -/
private def enumLoad (storage : EnumStorage) (width : Nat)
    (scalar : Option Bool := some false) :
    Bool :=
  let field := { loaded with type := .enum (Tests.enumIdentity "E") storage }
  let operand := RawOperand.field field.owner field.index field.type field.name true
  let site := { descriptor with field, bytes := List.replicate width 0, scalar }
  methodShapeInstructions { raw with code := [{ load with operand }] }
    { body [(0, site)] with code := [.ldsfld field] }

/-- The load admits an enum whose descriptor width is its storage's and refuses another width or
    a descriptor without the scalar flag. -/
theorem staticEnumWidthFollowsStorage :
    [enumLoad .signed32 4, enumLoad .unsigned8 1, enumLoad .signed64 8, enumLoad .signed32 8,
      enumLoad .signed32 4 none] =
      [true, true, true, false, false] := by decide +kernel
#print axioms staticEnumWidthFollowsStorage

/-- Missing raw instructions, absent descriptors and wrong raw opcodes cannot pass. -/
theorem missing_static_rejects :
    methodShapeInstructions raw (body [(0, descriptor)]) = false ∧
    methodShapeInstructions { raw with code := [load] } (body []) = false ∧
    methodShapeInstructions { raw with code := [{ load with opcode := 0 }] }
      (body [(0, descriptor)]) = false := by decide +kernel
#print axioms missing_static_rejects

/-- Sparse homes retain ascending order and discard out-of-range references. -/
theorem sparse_homes : requiredHomeIndices
    ⟨List.replicate 1024 (.field .unsigned64), [],
      [.store 1000, .address 2, .store 1000, .store 1024, .store 0]⟩
    [true, true, true, true, false] = [2, 1000] := by decide +kernel
#print axioms sparse_homes
end Tests.ExtractionHomeIndexes
