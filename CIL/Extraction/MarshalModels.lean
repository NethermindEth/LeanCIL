import CIL.Extraction.ModelTable
import CIL.Extraction.TransferKinds

/-!
# MemoryMarshal runtime models

GetReference, AsBytes, Cast, CreateSpan and CreateReadOnlySpan take primitive integers,
Boolean, Char, enums with integer storage, supported integer vectors and checked structs.
GetArrayDataReference also requires an array element. Read, TryRead, Write and TryWrite
transfer these elements as scalars or snapshots. Each size comes from the checked layouts.
-/

namespace CIL.Extraction

/-- A static member of the exact runtime MemoryMarshal type. -/
private inductive Member where
  | getReference | getArrayDataReference | asBytes | cast | createSpan | createReadOnlySpan
  | read | tryRead | write | tryWrite
  deriving DecidableEq

/-- The type declaring the marshal operations. -/
private def owner := TypeExpr.atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal"
    .classType

/-- The writable or readonly runtime span constructor applied to its element. -/
private def spanOf (writable : Bool) (element : TypeExpr) : TypeExpr :=
  let name := if writable then "System.Span`1" else "System.ReadOnlySpan`1"
  .apply (.constructor runtimeScope name) element

/-- The member's parameter and result types at the given instantiation. -/
private def Member.signature (member : Member) (source target : TypeExpr) (writable : Bool) :
    OpenSignature :=
  let view := spanOf writable
  let byte := TypeExpr.primitive .byte
  let integer := TypeExpr.primitive .int32
  let boolean := TypeExpr.primitive .boolean
  let sig (result : TypeExpr) (parameters : List TypeExpr) : OpenSignature :=
    { convention := 0x10, returnType := result, parameters }
  match member with
  | .getReference => sig (.byref source) [view source]
  | .getArrayDataReference => sig (.byref source) [.array source]
  | .asBytes => sig (view byte) [view source]
  | .cast => sig (view target) [view source]
  | .createSpan => sig (spanOf true source) [.byref source, integer]
  | .createReadOnlySpan => sig (spanOf false source) [.byref source, integer]
  | .read => sig source [spanOf false byte]
  | .tryRead => sig boolean [spanOf false byte, .byref source]
  | .write => sig .void [spanOf true byte, .byref source]
  | .tryWrite => sig boolean [spanOf true byte, .byref source]

/-- Whether the declaration has a writable span as its first parameter. -/
private def writableInput (parameters : List TypeExpr) : Bool :=
  match parameters with
  | .apply (.constructor _ name) _ :: _ => name == "System.Span`1"
  | _ => false

/-- The closed operation, including the element widths and signedness from the layouts. -/
private def Member.operation (member : Member) (reader : CallLayouts)
    (method : MethodRef) : Option MemoryOp := do
  guard (!method.hasThis && method.owner == owner)
  let (source, target) ← match member, method.methodArguments with
    | .cast, [source, target] => some (source, target)
    | .cast, _ => none
    | _, [source] => some (source, .void)
    | _, _ => none
  guard (method.genericArity == method.methodArguments.length)
  let writable := writableInput method.parameters
  guard (method.signature 0x10 == member.signature source target writable)
  guard ((arrayElementType source).isSome)
  let kind ← transferKind? reader source
  match member with
  | .getReference =>
    let _ ← reader.storage (spanOf writable source)
    return .spanReference
  | .getArrayDataReference =>
    let _ ← reader.storage (.array source)
    return .observeView .arrayData
  | .asBytes =>
    let _ ← reader.storage (spanOf writable source)
    return .spanReinterpret kind.width 1 writable
  | .cast =>
    guard ((arrayElementType target).isSome)
    let _ ← reader.storage (spanOf writable source)
    let _ ← reader.storage (spanOf writable target)
    return .spanReinterpret kind.width (← transferKind? reader target).width writable
  | .createSpan | .createReadOnlySpan =>
    let _ ← reader.storage (spanOf (member == .createSpan) source)
    return .spanFromReference kind.width (member == .createSpan)
  | .read | .tryRead => return .marshalRead kind (member == .tryRead)
  | .write | .tryWrite =>
    return .marshalWrite kind (member == .tryWrite)

/-- The call entry binds the uninstantiated declaration as well as the closed reference. -/
private def entry (name : MetadataName) (member : Member) : ModelEntry :=
  .single .call owner name (.declaration fun sig =>
    sig == member.signature (.parameter 0) (.parameter 1) (writableInput sig.parameters))
    (fun reader method => RuntimeModel.memory <$> member.operation reader method)

/-- The runtime MemoryMarshal entries, one for each member name. -/
def marshalEntries : List ModelEntry :=
  [entry name!"GetReference" .getReference,
   entry name!"GetArrayDataReference" .getArrayDataReference,
   entry name!"AsBytes" .asBytes, entry name!"Cast" .cast, entry name!"CreateSpan" .createSpan,
   entry name!"CreateReadOnlySpan" .createReadOnlySpan, entry name!"Read" .read,
   entry name!"TryRead" .tryRead, entry name!"Write" .write, entry name!"TryWrite" .tryWrite]

/-- Every marshal entry resolves to a memory operation. -/
theorem marshalEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation)) :
    ∀ candidate ∈ marshalEntries, candidate.Yields property := by
  intro candidate listed environment method model resolved
  simp only [marshalEntries, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp resolved <;> exact memory _

#print axioms marshalEntries_yields

end CIL.Extraction
