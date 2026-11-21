import CIL.Extraction.ModelTable
import CIL.Extraction.SpanCalls

/-! Runtime models for endian-aware integer reads and writes on byte spans. -/

namespace CIL.Extraction

/-- A fixed integer transfer on the 64-bit target. Native integers occupy eight bytes. -/
private structure EndianMember where
  key : MetadataName
  integer : String
  big : Bool
  read : Bool
  trying : Bool

/-- All admitted endian members have fixed, nongeneric declarations. -/
private def endianMembers : List EndianMember := [
  ⟨name!"ReadInt16BigEndian", "Int16", true, true, false⟩,
  ⟨name!"ReadInt16LittleEndian", "Int16", false, true, false⟩,
  ⟨name!"TryReadInt16BigEndian", "Int16", true, true, true⟩,
  ⟨name!"TryReadInt16LittleEndian", "Int16", false, true, true⟩,
  ⟨name!"WriteInt16BigEndian", "Int16", true, false, false⟩,
  ⟨name!"WriteInt16LittleEndian", "Int16", false, false, false⟩,
  ⟨name!"TryWriteInt16BigEndian", "Int16", true, false, true⟩,
  ⟨name!"TryWriteInt16LittleEndian", "Int16", false, false, true⟩,
  ⟨name!"ReadUInt16BigEndian", "UInt16", true, true, false⟩,
  ⟨name!"ReadUInt16LittleEndian", "UInt16", false, true, false⟩,
  ⟨name!"TryReadUInt16BigEndian", "UInt16", true, true, true⟩,
  ⟨name!"TryReadUInt16LittleEndian", "UInt16", false, true, true⟩,
  ⟨name!"WriteUInt16BigEndian", "UInt16", true, false, false⟩,
  ⟨name!"WriteUInt16LittleEndian", "UInt16", false, false, false⟩,
  ⟨name!"TryWriteUInt16BigEndian", "UInt16", true, false, true⟩,
  ⟨name!"TryWriteUInt16LittleEndian", "UInt16", false, false, true⟩,
  ⟨name!"ReadInt32BigEndian", "Int32", true, true, false⟩,
  ⟨name!"ReadInt32LittleEndian", "Int32", false, true, false⟩,
  ⟨name!"TryReadInt32BigEndian", "Int32", true, true, true⟩,
  ⟨name!"TryReadInt32LittleEndian", "Int32", false, true, true⟩,
  ⟨name!"WriteInt32BigEndian", "Int32", true, false, false⟩,
  ⟨name!"WriteInt32LittleEndian", "Int32", false, false, false⟩,
  ⟨name!"TryWriteInt32BigEndian", "Int32", true, false, true⟩,
  ⟨name!"TryWriteInt32LittleEndian", "Int32", false, false, true⟩,
  ⟨name!"ReadUInt32BigEndian", "UInt32", true, true, false⟩,
  ⟨name!"ReadUInt32LittleEndian", "UInt32", false, true, false⟩,
  ⟨name!"TryReadUInt32BigEndian", "UInt32", true, true, true⟩,
  ⟨name!"TryReadUInt32LittleEndian", "UInt32", false, true, true⟩,
  ⟨name!"WriteUInt32BigEndian", "UInt32", true, false, false⟩,
  ⟨name!"WriteUInt32LittleEndian", "UInt32", false, false, false⟩,
  ⟨name!"TryWriteUInt32BigEndian", "UInt32", true, false, true⟩,
  ⟨name!"TryWriteUInt32LittleEndian", "UInt32", false, false, true⟩,
  ⟨name!"ReadInt64BigEndian", "Int64", true, true, false⟩,
  ⟨name!"ReadInt64LittleEndian", "Int64", false, true, false⟩,
  ⟨name!"TryReadInt64BigEndian", "Int64", true, true, true⟩,
  ⟨name!"TryReadInt64LittleEndian", "Int64", false, true, true⟩,
  ⟨name!"WriteInt64BigEndian", "Int64", true, false, false⟩,
  ⟨name!"WriteInt64LittleEndian", "Int64", false, false, false⟩,
  ⟨name!"TryWriteInt64BigEndian", "Int64", true, false, true⟩,
  ⟨name!"TryWriteInt64LittleEndian", "Int64", false, false, true⟩,
  ⟨name!"ReadUInt64BigEndian", "UInt64", true, true, false⟩,
  ⟨name!"ReadUInt64LittleEndian", "UInt64", false, true, false⟩,
  ⟨name!"TryReadUInt64BigEndian", "UInt64", true, true, true⟩,
  ⟨name!"TryReadUInt64LittleEndian", "UInt64", false, true, true⟩,
  ⟨name!"WriteUInt64BigEndian", "UInt64", true, false, false⟩,
  ⟨name!"WriteUInt64LittleEndian", "UInt64", false, false, false⟩,
  ⟨name!"TryWriteUInt64BigEndian", "UInt64", true, false, true⟩,
  ⟨name!"TryWriteUInt64LittleEndian", "UInt64", false, false, true⟩,
  ⟨name!"ReadIntPtrBigEndian", "IntPtr", true, true, false⟩,
  ⟨name!"ReadIntPtrLittleEndian", "IntPtr", false, true, false⟩,
  ⟨name!"TryReadIntPtrBigEndian", "IntPtr", true, true, true⟩,
  ⟨name!"TryReadIntPtrLittleEndian", "IntPtr", false, true, true⟩,
  ⟨name!"WriteIntPtrBigEndian", "IntPtr", true, false, false⟩,
  ⟨name!"WriteIntPtrLittleEndian", "IntPtr", false, false, false⟩,
  ⟨name!"TryWriteIntPtrBigEndian", "IntPtr", true, false, true⟩,
  ⟨name!"TryWriteIntPtrLittleEndian", "IntPtr", false, false, true⟩,
  ⟨name!"ReadUIntPtrBigEndian", "UIntPtr", true, true, false⟩,
  ⟨name!"ReadUIntPtrLittleEndian", "UIntPtr", false, true, false⟩,
  ⟨name!"TryReadUIntPtrBigEndian", "UIntPtr", true, true, true⟩,
  ⟨name!"TryReadUIntPtrLittleEndian", "UIntPtr", false, true, true⟩,
  ⟨name!"WriteUIntPtrBigEndian", "UIntPtr", true, false, false⟩,
  ⟨name!"WriteUIntPtrLittleEndian", "UIntPtr", false, false, false⟩,
  ⟨name!"TryWriteUIntPtrBigEndian", "UIntPtr", true, false, true⟩,
  ⟨name!"TryWriteUIntPtrLittleEndian", "UIntPtr", false, false, true⟩
]

/-- The integer's checked primitive width fixes the number of bytes transferred. -/
private def EndianMember.operation (member : EndianMember) (reader : CallLayouts)
    (integer : TypeExpr) : Option MemoryOp := do
  let .primitive width _ := reader.valueShape integer | none
  if member.read then
    let signed := ["Int16", "Int32", "Int64", "IntPtr"].contains member.integer
    return .binaryRead width signed member.big member.trying
  return .binaryWrite width member.big member.trying

/-- The byte span, integer representation, result and external identity of this member. -/
private def EndianMember.entry (member : EndianMember) : ModelEntry :=
  let owner := "System.Buffers.Binary.BinaryPrimitives"
  let tryName := if member.trying then "Try" else ""
  let action := if member.read then "Read" else "Write"
  let order := if member.big then "BigEndian" else "LittleEndian"
  let name := s!"{tryName}{action}{member.integer}{order}"
  let integerName := "System." ++ member.integer
  let integer := TypeExpr.atom runtimeScope integerName
  let spanName := if member.read then "System.ReadOnlySpan`1" else "System.Span`1"
  let byte := TypeExpr.atom runtimeScope "System.Byte"
  let span := TypeExpr.apply (.constructor runtimeScope spanName) byte
  let single := member.read && !member.trying
  let parameters := if single then [span]
    else [span, if member.read then .byref integer else integer]
  let result := if member.trying then TypeExpr.atom runtimeScope "System.Boolean"
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
