import CIL.Extraction.ModelTable
import CIL.Extraction.SpanCalls

/-! Runtime models for endian-aware integer reads and writes on byte spans. -/

namespace CIL.Extraction

/-- A fixed integer transfer on the 64-bit target. Native integers occupy eight bytes. -/
private structure EndianMember where
  key : MetadataName
  integer : PrimitiveType
  big : Bool
  read : Bool
  trying : Bool

/-- All admitted endian members have fixed, nongeneric declarations. -/
private def endianMembers : List EndianMember := [
  ⟨name!"ReadInt16BigEndian", .int16, true, true, false⟩,
  ⟨name!"ReadInt16LittleEndian", .int16, false, true, false⟩,
  ⟨name!"TryReadInt16BigEndian", .int16, true, true, true⟩,
  ⟨name!"TryReadInt16LittleEndian", .int16, false, true, true⟩,
  ⟨name!"WriteInt16BigEndian", .int16, true, false, false⟩,
  ⟨name!"WriteInt16LittleEndian", .int16, false, false, false⟩,
  ⟨name!"TryWriteInt16BigEndian", .int16, true, false, true⟩,
  ⟨name!"TryWriteInt16LittleEndian", .int16, false, false, true⟩,
  ⟨name!"ReadUInt16BigEndian", .uint16, true, true, false⟩,
  ⟨name!"ReadUInt16LittleEndian", .uint16, false, true, false⟩,
  ⟨name!"TryReadUInt16BigEndian", .uint16, true, true, true⟩,
  ⟨name!"TryReadUInt16LittleEndian", .uint16, false, true, true⟩,
  ⟨name!"WriteUInt16BigEndian", .uint16, true, false, false⟩,
  ⟨name!"WriteUInt16LittleEndian", .uint16, false, false, false⟩,
  ⟨name!"TryWriteUInt16BigEndian", .uint16, true, false, true⟩,
  ⟨name!"TryWriteUInt16LittleEndian", .uint16, false, false, true⟩,
  ⟨name!"ReadInt32BigEndian", .int32, true, true, false⟩,
  ⟨name!"ReadInt32LittleEndian", .int32, false, true, false⟩,
  ⟨name!"TryReadInt32BigEndian", .int32, true, true, true⟩,
  ⟨name!"TryReadInt32LittleEndian", .int32, false, true, true⟩,
  ⟨name!"WriteInt32BigEndian", .int32, true, false, false⟩,
  ⟨name!"WriteInt32LittleEndian", .int32, false, false, false⟩,
  ⟨name!"TryWriteInt32BigEndian", .int32, true, false, true⟩,
  ⟨name!"TryWriteInt32LittleEndian", .int32, false, false, true⟩,
  ⟨name!"ReadUInt32BigEndian", .uint32, true, true, false⟩,
  ⟨name!"ReadUInt32LittleEndian", .uint32, false, true, false⟩,
  ⟨name!"TryReadUInt32BigEndian", .uint32, true, true, true⟩,
  ⟨name!"TryReadUInt32LittleEndian", .uint32, false, true, true⟩,
  ⟨name!"WriteUInt32BigEndian", .uint32, true, false, false⟩,
  ⟨name!"WriteUInt32LittleEndian", .uint32, false, false, false⟩,
  ⟨name!"TryWriteUInt32BigEndian", .uint32, true, false, true⟩,
  ⟨name!"TryWriteUInt32LittleEndian", .uint32, false, false, true⟩,
  ⟨name!"ReadInt64BigEndian", .int64, true, true, false⟩,
  ⟨name!"ReadInt64LittleEndian", .int64, false, true, false⟩,
  ⟨name!"TryReadInt64BigEndian", .int64, true, true, true⟩,
  ⟨name!"TryReadInt64LittleEndian", .int64, false, true, true⟩,
  ⟨name!"WriteInt64BigEndian", .int64, true, false, false⟩,
  ⟨name!"WriteInt64LittleEndian", .int64, false, false, false⟩,
  ⟨name!"TryWriteInt64BigEndian", .int64, true, false, true⟩,
  ⟨name!"TryWriteInt64LittleEndian", .int64, false, false, true⟩,
  ⟨name!"ReadUInt64BigEndian", .uint64, true, true, false⟩,
  ⟨name!"ReadUInt64LittleEndian", .uint64, false, true, false⟩,
  ⟨name!"TryReadUInt64BigEndian", .uint64, true, true, true⟩,
  ⟨name!"TryReadUInt64LittleEndian", .uint64, false, true, true⟩,
  ⟨name!"WriteUInt64BigEndian", .uint64, true, false, false⟩,
  ⟨name!"WriteUInt64LittleEndian", .uint64, false, false, false⟩,
  ⟨name!"TryWriteUInt64BigEndian", .uint64, true, false, true⟩,
  ⟨name!"TryWriteUInt64LittleEndian", .uint64, false, false, true⟩,
  ⟨name!"ReadIntPtrBigEndian", .intPtr, true, true, false⟩,
  ⟨name!"ReadIntPtrLittleEndian", .intPtr, false, true, false⟩,
  ⟨name!"TryReadIntPtrBigEndian", .intPtr, true, true, true⟩,
  ⟨name!"TryReadIntPtrLittleEndian", .intPtr, false, true, true⟩,
  ⟨name!"WriteIntPtrBigEndian", .intPtr, true, false, false⟩,
  ⟨name!"WriteIntPtrLittleEndian", .intPtr, false, false, false⟩,
  ⟨name!"TryWriteIntPtrBigEndian", .intPtr, true, false, true⟩,
  ⟨name!"TryWriteIntPtrLittleEndian", .intPtr, false, false, true⟩,
  ⟨name!"ReadUIntPtrBigEndian", .uintPtr, true, true, false⟩,
  ⟨name!"ReadUIntPtrLittleEndian", .uintPtr, false, true, false⟩,
  ⟨name!"TryReadUIntPtrBigEndian", .uintPtr, true, true, true⟩,
  ⟨name!"TryReadUIntPtrLittleEndian", .uintPtr, false, true, true⟩,
  ⟨name!"WriteUIntPtrBigEndian", .uintPtr, true, false, false⟩,
  ⟨name!"WriteUIntPtrLittleEndian", .uintPtr, false, false, false⟩,
  ⟨name!"TryWriteUIntPtrBigEndian", .uintPtr, true, false, true⟩,
  ⟨name!"TryWriteUIntPtrLittleEndian", .uintPtr, false, false, true⟩
]

/-- The integer's checked primitive width fixes the number of bytes transferred. -/
private def EndianMember.operation (member : EndianMember) (reader : CallLayouts)
    (integer : TypeExpr) : Option MemoryOp := do
  let .primitive width _ := reader.valueShape integer | none
  if member.read then
    let signed := member.integer ∈ [.int16, .int32, .int64, .intPtr]
    return .binaryRead width signed member.big member.trying
  return .binaryWrite width member.big member.trying

/-- The byte span, integer representation, result and external identity of this member. -/
private def EndianMember.entry (member : EndianMember) : ModelEntry :=
  let owner := "System.Buffers.Binary.BinaryPrimitives"
  let tryName := if member.trying then "Try" else ""
  let action := if member.read then "Read" else "Write"
  let order := if member.big then "BigEndian" else "LittleEndian"
  let name := s!"{tryName}{action}{member.integer.simpleName}{order}"
  let integerName := member.integer.display
  let integer := TypeExpr.primitive member.integer
  let spanName := if member.read then "System.ReadOnlySpan`1" else "System.Span`1"
  let byte := TypeExpr.primitive .byte
  let span := TypeExpr.apply (.constructor runtimeScope spanName) byte
  let single := member.read && !member.trying
  let parameters := if single then [span]
    else [span, if member.read then .byref integer else integer]
  let result := if member.trying then TypeExpr.primitive .boolean
    else if member.read then integer else .void
  let resultName := if member.trying then "System.Boolean" else if member.read then integerName
    else "System.Void"
  let suffix := if single then "" else "," ++ integerName ++ (if member.read then "&" else "")
  let arguments := s!"{spanName}<System.Byte>{suffix}"
  let target := s!"{spanMemoryScope}::{resultName} {owner}::{name}({arguments})"
  let expected : MethodRef :=
    { owner := .atom spanMemoryScope owner, name := member.key, hasThis := false,
      genericArity := 0, parameters, returnType := result }
  { opcode := .call, owner := expected.owner, name := member.key, ownsName := true,
    overloads := [
      { operand := .external (fun _ => expected.signature 0) name (fun _ => some target),
        accepts := (· == expected),
        resolve := fun reader _ => RuntimeModel.memory <$> member.operation reader integer }] }

/-- The endian transfer entries of BinaryPrimitives. -/
def binaryEntries : List ModelEntry := endianMembers.map EndianMember.entry

/-- Every endian member executes a checked memory operation. -/
theorem binaryEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation)) :
    ∀ entry ∈ binaryEntries, entry.Yields property := by
  intro entry listed reader method model found
  obtain ⟨member, _, rfl⟩ := List.mem_map.mp listed
  obtain ⟨row, selected, resolved⟩ := Option.bind_eq_some_iff.mp found
  have listedRow := ModelEntry.select?_mem selected
  simp only [EndianMember.entry, List.mem_singleton] at listedRow
  subst row
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp resolved
  exact memory _

#print axioms binaryEntries_yields

end CIL.Extraction
