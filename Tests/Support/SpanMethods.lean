import CIL.Extraction.RuntimeModels

/-! Closed span member references used by the checked memory and loop fixtures. -/

namespace Tests.SpanMethods
open CIL CIL.Extraction

/-- The index and length type of span members. -/
def int32 := TypeExpr.primitive .int32

/-- The element type of the word-summing loop. -/
def uint64 := TypeExpr.primitive .uint64

private def span (writable : Bool) (element : TypeExpr) :=
  TypeExpr.apply (.constructor runtimeScope (if writable then "System.Span`1" else
    "System.ReadOnlySpan`1")) element

private def readOnlyMember (element : TypeExpr) (name : MetadataName) (result : TypeExpr)
    (parameters : List TypeExpr) : MethodRef :=
  { owner := span false element, name, hasThis := true, genericArity := 0,
    returnType := result, parameters }

/-- The readonly indexer carries the required modifier on its returned reference. -/
def item (element : TypeExpr) := readOnlyMember element name!"get_Item"
  (.spelledModified runtimeScope "!0& modreq(System.Runtime.InteropServices.InAttribute)") [int32]

/-- The selected Slice overload takes a start and optionally a length. -/
def slice (element : TypeExpr) (counted : Bool) := readOnlyMember element name!"Slice"
  (span false element) (if counted then [int32, int32] else [int32])

/-- Length of the closed readonly span. -/
def length (element : TypeExpr) := readOnlyMember element name!"get_Length" int32 []

/-- The generic factory constructs a writable span over a managed reference and length. -/
def createInt32 : MethodRef :=
  { owner := .atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal" .classType,
    name := name!"CreateSpan", hasThis := false, genericArity := 1, methodArguments := [int32],
    returnType := span true int32, parameters := [.byref int32, int32] }

end Tests.SpanMethods