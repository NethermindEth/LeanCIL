import CIL.Extraction.MarshalCalls
import CIL.Extraction.LoweredCalls
import CIL.Extraction.HardwareCalls

/-!
# Resolution of lowered calls

Each named family computes its instruction from the call operand, the checked layout
environment and profile, and its role in a fold of the raw method.
-/

namespace CIL.Extraction

/-- A closed generic helper with one of the admitted value storage representations. -/
private def unsafeReferenceInstruction (environment : CallLayouts) (raw : RawInstruction)
    (site : CallSite) : Option Instruction := do
  let [element] := site.typeArguments | none
  _root_.guard ((environment.valueShape element).size?.isSome)
  return (← unsafeReferenceHelper raw).instruction

/-- Only a nominal aggregate needs a layout-table width in the span signature matchers. -/
private def aggregateWidth (environment : CallLayouts) (type : TypeExpr) : Option Nat :=
  match type with
  | .aggregate .. => (environment.valueShape type).size?
  | _ => some 0

/-- A span call binds its element sizes and its local destination, when a fold supplies one. -/
private def spanInstruction (environment : CallLayouts) (role : Option FoldRole)
    (raw : RawInstruction) (site : CallSite) : Option Instruction := do
  let first := match site.declaringType with
    | .apply _ element => element
    | _ => site.typeArguments.headD .void
  let source ← aggregateWidth environment first
  if raw.opcode == 40 && site.name == ".ctor" then
    let some (.spanConstructor index _) := role | none
    return .initializeSpanLocal index (← spanLocalConstructor site source)
  if byteSpanConstructor raw.opcode site then return .memory .spanCreate
  return (← spanCall raw source).instruction

/-- A runtime field handle produces a read-only span of an admitted scalar element width. -/
private def staticSpanInstruction (site : CallSite) : Option Instruction := do
  let [element] := site.typeArguments | none
  let .primitive width _ := LayoutEnvironment.valueShape {} element | none
  let result := TypeExpr.apply (.constructor runtimeScope "System.ReadOnlySpan`1") element
  _root_.guard (staticRuntimeCall site runtimeScope ("System.ReadOnlySpan`1<!!0> " ++
    "System.Runtime.CompilerServices.RuntimeHelpers::CreateSpan(System.RuntimeFieldHandle)")
    result [.atom runtimeScope "System.RuntimeFieldHandle"] [element])
  return .memory (.createSpan width)

/-- The instruction of this raw member, or no instruction when its overload cannot resolve. -/
def LoweredFamily.resolve (family : LoweredFamily) (environment : CallLayouts)
    (profile : FeatureProfile) (role : Option FoldRole) (raw : RawInstruction) :
    Option Instruction := do
  let .call site := raw.operand | none
  match family with
  | .hardware => hardwareInstruction environment profile raw site
  | .vectorCreate =>
    if byteSpanCreateFamily site then
      let v128 := TypeExpr.atom intrinsicsScope
        (metadata_text% "System.Runtime.Intrinsics.Vector128")
      let kind := if site.declaringType == v128
        then TransferKind.snapshot .vector128 else .snapshot .vector256
      _root_.guard (byteSpanCreateMatches raw kind)
      return .memory (.marshalRead kind false)
    hardwareInstruction environment profile raw site
  | .vectorTransfer =>
    let (write, offset) ← vector128UnsafeCall raw
    return .memory (.vector128Unsafe write offset)
  | .integerMath => integerMathInstruction environment site
  | .span => spanInstruction environment role raw site
  | .staticSpan => staticSpanInstruction site
  | .view =>
    let element := match site.declaringType with
      | .apply _ type => type
      | _ => site.typeArguments.headD .void
    let _ ← aggregateWidth environment element
    return .memory (.observeView (← viewObservation raw))
  | .binary => binaryInstruction raw
  | .guard => guardInstruction raw
  | .unsafeReference => unsafeReferenceInstruction environment raw site
  | .unsafeOffset =>
    _root_.guard (unsafeElementOffset raw)
    let [element] := site.typeArguments | none
    let width ← (environment.valueShape element).size?
    let stride := if site.name == "Subtract" then subtractionStride width else width
    let signed := site.parameterTypes[1]? != some (.atom runtimeScope "System.UIntPtr")
    return .memory (.add stride signed)
  | .unsafeBlock =>
    let (copy, alignment) ← unsafeBlockCall raw
    return .memory (if copy then .copyBlock alignment else .initBlock alignment)
  | .platform => return .ldc_i4 (← platformConstant site)
  | .referenceContent =>
    return .ldc_i4 (← referenceContentConstant environment.indexedRaw site)
  | .feature => return .feature (← featureGetter site)
  | .typeTest => match role with
    | some .interior => some .nop
    | some (.result value) => some (.ldc_i4 (if value then 1 else 0))
    | _ => none
  | .throwConstructor => match role with
    | some .head | some .interior => some .nop
    | _ => none

end CIL.Extraction
