import CIL.Extraction.DecodedMethod
import CIL.Safety.StepComposition

/-!
# Core span call agreement

The fixtures instantiate the MemberRef signatures on a primitive, an enum, an integer vector
and an aggregate. Each overload has a distinct declaration mutation with unchanged closed types.
-/

namespace Tests.SpanModels
open CIL CIL.Extraction

/-- The fixture's primitive and span type identities. -/
private def int32 : TypeExpr := .atom runtimeScope "System.Int32"

/-- A closed or open span of the specified element. -/
private def span (writable : Bool) (element : TypeExpr) : TypeExpr :=
  let name := if writable then "System.Span`1" else "System.ReadOnlySpan`1"
  .apply (.constructor runtimeScope name) element

/-- One overload with its closed method, declaration, forged declaration and memory operation. -/
private structure Overload where
  name : String
  method : MethodRef
  declared : OpenSignature
  forged : OpenSignature
  operation : MemoryOp

/-- Genuine span signatures and single substitutions in an open result or parameter. -/
private def overloads (writable : Bool) (element : TypeExpr) (width : Nat) : List Overload :=
  let owner := span writable element
  let var := TypeExpr.ownerParameter 0
  let openOwner := span writable var
  let boolean := TypeExpr.atom runtimeScope "System.Boolean"
  let modified := fun type => TypeExpr.modified true runtimeScope
    "System.Runtime.InteropServices.InAttribute" (.byref type)
  let openRef := if writable then TypeExpr.byref var else modified var
  let closedRef := if writable then TypeExpr.byref element else
    .atom runtimeScope "!0& modreq(System.Runtime.InteropServices.InAttribute)"
  let row (text : String) (name : MetadataName) (convention : Nat)
      (result : TypeExpr) (params : List TypeExpr) (declared forged : OpenSignature)
      (op : MemoryOp) : Overload :=
    ⟨text, ⟨owner, name, convention == 0x20, 0, result, params, []⟩, declared, forged, op⟩
  [row "get_Item" name!"get_Item" 0x20 closedRef [int32] ⟨0x20, openRef, [int32]⟩
      ⟨0x20, if writable then modified var else .byref var, [int32]⟩ (.spanItem width),
   row "get_Length" name!"get_Length" 0x20 int32 [] ⟨0x20, int32, []⟩
      ⟨0x20, var, []⟩ .spanLength,
   row "Slice" name!"Slice" 0x20 owner [int32] ⟨0x20, openOwner, [int32]⟩
      ⟨0x20, span (!writable) var, [int32]⟩ (.spanSlice false),
   row "Slice" name!"Slice" 0x20 owner [int32, int32] ⟨0x20, openOwner, [int32, int32]⟩
      ⟨0x20, openOwner, [int32, var]⟩ (.spanSlice true),
   row "get_IsEmpty" name!"get_IsEmpty" 0x20 boolean [] ⟨0x20, boolean, []⟩
      ⟨0x20, int32, []⟩ (.observeView .spanEmpty),
   row "GetPinnableReference" name!"GetPinnableReference" 0x20 closedRef [] ⟨0x20, openRef, []⟩
      ⟨0x20, if writable then .byref (.parameter 0) else modified (.parameter 0), []⟩
      (.observeView .spanPinnable),
   row "get_Empty" name!"get_Empty" 0 owner [] ⟨0, openOwner, []⟩
      ⟨0, span writable (.parameter 0), []⟩ (.spanEmpty width writable)] ++
  [row "op_Implicit" name!"op_Implicit" 0 owner [.array element] ⟨0, openOwner, [.array var]⟩
    ⟨0, openOwner, [.array (.parameter 0)]⟩
    (.arraySpan ((arrayElementType element width).getD .signed32) writable .whole)] ++
  (if writable then [row "op_Implicit" name!"op_Implicit" 0 (span false element) [owner]
    ⟨0, span false var, [openOwner]⟩ ⟨0, span false var, [span true (.parameter 0)]⟩
    .spanReadOnly] else [])

/-- Both owners' model operations for the same element. -/
private def rows (element : TypeExpr) (width : Nat) : List Overload :=
  overloads true element width ++ overloads false element width

/-- A nominal aggregate whose size differs between the two checked layout environments. -/
private def aggregate : TypeExpr := .aggregate "Fixture::Words" 0

/-- The raw and computed layout for an aggregate containing the given number of int32 fields. -/
private def environment (count : Nat) (byRefLike := false) : LayoutEnvironment :=
  let raw : List RawLayout := [{
    identity := "Fixture::Words", explicit := false, packing := 0,
    declaredSize := 0, byRefLike, fields := List.replicate count ⟨.unsigned32, none⟩ }]
  { rawLayouts := raw, layouts := (computeLayouts raw).getD #[] }

/-- Resolution gives the expected memory operation at every overload. -/
private def resolves (env : LayoutEnvironment) (element : TypeExpr) (width : Nat) : Bool :=
  (rows element width).all fun row =>
    runtimeModel env .call row.method == some (.memory row.operation)

/-- Primitive, enum, vector and aggregate elements retain their own storage widths. -/
theorem elementWidths :
    resolves {} int32 4 ∧
    resolves {} (.enum "Fixture::Small" (.atom runtimeScope "System.Byte")) 1 ∧
    resolves {} (.apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1")
      int32) 16 ∧ resolves (environment 1) aggregate 4 ∧
    resolves (environment 3) aggregate 12 := by
  decide +kernel

#print axioms elementWidths

/-- Every rejected element, including an unbound aggregate, misses the production model table. -/
theorem unsupportedElements :
    ([TypeExpr.void, .object runtimeScope "System.String", .byref int32, .array int32,
      .atom runtimeScope "System.Double", .atom "Fixture" "System.Int32",
      .enum "Fixture::Bad" (.atom runtimeScope "System.Boolean"),
      .apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1")
        (.atom runtimeScope "System.Single"), .aggregate "Other::Words" 0,
      .aggregate "Fixture::Words" 1].all fun type =>
        (rows type 0).all fun row => (runtimeModel (environment 1) .call row.method).isNone) := by
  decide +kernel

#print axioms unsupportedElements

/-- The external signature spelling of an open type in the fixtures. -/
private def spelling : TypeExpr → String
  | .array (.ownerParameter 0) => "!0[]"
  | .byref (.ownerParameter 0) => "!0&"
  | .modified true _ name (.byref (.ownerParameter 0)) => s!"!0& modreq({name})"
  | .apply (.constructor _ owner) (.ownerParameter 0) => s!"{owner}<!0>"
  | .atom _ name => name
  | _ => "?"

/-- The raw call operand used to check a live emission and its metadata declaration. -/
private def Overload.raw (row : Overload) (declared : OpenSignature) : RawInstruction :=
  let owner := String.ofList ((ownerTypeName 0 row.method.owner).getD [])
  let result := spelling row.declared.returnType
  let params := ",".intercalate (row.declared.parameters.map spelling)
  ⟨0, 40, .call {
    method := row.method, declared, name := row.name, typeArguments := [],
    target := .external s!"{runtimeScope}::{result} {owner}::{row.name}({params})",
    parameterCount := row.method.parameters.length, returnsValue := true }⟩

/-- The single decoded instruction in a caller of the given runtime member. -/
private def decoded (raw : RawInstruction) (layouts : LayoutEnvironment := {}) :
    Option (List Instruction) :=
  let body : RawMethod := {
    token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
    callingConvention := 0,
    attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
    initLocals := false, maxStack := 3, genericParameters := [], code := [raw] }
  (Method.ofRaw? .scalar layouts [] [true] body []).map Method.code

/-- Only array conversions reject an otherwise valid byref-like aggregate layout. -/
theorem byRefLikeArrays :
    (rows aggregate 4).all (fun row =>
      let raw := row.raw row.declared
      let call := Instruction.call row.method {}
      let expected := match row.operation with
        | .arraySpan .. => Instruction.unadmitted 40
        | _ => call
      decide (decoded raw (environment 1) = some [call]) &&
        decide (decoded raw (environment 1 true) = some [expected])) = true := by
  decide +kernel

#print axioms byRefLikeArrays

/-- A closed operand in the wrong slot or with the wrong calling convention has no model. -/
theorem closedRefusals :
    ((rows int32 4).all fun row =>
      let method := row.method
      let misses := fun reference => (runtimeModel {} .call reference).isNone
      (runtimeModel {} .newobj method).isNone &&
        misses { method with hasThis := !method.hasThis } &&
        misses { method with genericArity := 1 } &&
        misses { method with methodArguments := [int32] } &&
        misses { method with owner := .apply (.constructor runtimeScope "Another") int32 } &&
        misses { method with owner := .apply (.constructor "Fixture" "System.Span`1") int32 }) ∧
    (runtimeModel {} .call {
      owner := span false int32, name := name!"op_Implicit", hasThis := false, genericArity := 0,
      parameters := [span false int32], returnType := span false int32 }).isNone := by
  decide +kernel

#print axioms closedRefusals

/-- A live site requires the kept call and the open declaration. Wrong conventions and a
    forged declaration cannot retain the call or substitute its lowered memory operation. -/
theorem liveAgreement :
    ((rows int32 4).all fun row =>
      let accepts := fun sig op =>
        runtimeCatalog.siteAgrees {} .scalar (row.raw sig) op none none true
      let call := Instruction.call row.method {}
      accepts row.declared call && !accepts row.declared (.memory row.operation) &&
        !accepts row.forged call && !accepts row.forged (.memory row.operation) &&
        ([0, 0x20, 1, 0x10, 0x11, 0x30, 0x40, 0x50, 0x60, 0x70].all fun header =>
          header == row.declared.convention ||
            !accepts { row.declared with convention := header } call)) := by
  decide +kernel

#print axioms liveAgreement

/-- Changing only the declaration of a resolving call yields an opcode-tagged hole. -/
theorem decodedOverloads :
    ((rows int32 4).all fun row =>
      decide (decoded (row.raw row.declared) = some [.call row.method {}]) &&
        decide (decoded (row.raw row.forged) = some [.unadmitted 40])) := by
  decide +kernel

#print axioms decodedOverloads

/-- A mismatched target, name, stack count or type argument gives an opcode-tagged hole. -/
theorem operandRefusals :
    ((rows int32 4).all fun row => Id.run do
      let raw := row.raw row.declared
      let .call site := raw.operand | return false
      return [{ site with target := .external "Fixture::Other" }, { site with name := "Other" },
        { site with parameterCount := site.parameterCount + 1 },
        { site with returnsValue := false },
        { site with typeArguments := [int32] }, { site with ownerArgumentCount := 1 }].all
          fun changed => decide (decoded { raw with operand := .call changed } =
            some [.unadmitted 40])) := by
  decide +kernel

#print axioms operandRefusals

/-- Every resolved span call has its memory instruction's exact frame, stack, memory and fault
    for all receiver values, including those from argument homes, local addresses and byrefs. -/
theorem stepOfSpanCall (body : Method) (pc : Nat) (args : List Safety.Value) (frame : Safety.Frame)
    (memory : Safety.Memory) (stack : List Safety.Value) (row : Overload)
    (link : body.linkAt pc = none)
    (found : runtimeModel body.environment .call row.method = some (.memory row.operation)) :
    Safety.step body (.call row.method {}) pc args frame stack memory =
      Safety.step body (.memory row.operation) pc args frame stack memory :=
  Safety.step_call_memory body pc args frame memory link found rfl stack

#print axioms stepOfSpanCall

end Tests.SpanModels
