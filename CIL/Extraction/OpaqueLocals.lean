import CIL.Extraction.Features
import CIL.Extraction.RuntimeModels
import Std.Data.TreeSet.Lemmas
import Lean.Elab.Tactic.BuiltinTactic

/-! Whole-vector local storage preserves the unspecified lanes of scalar-unsafe vectors. -/

namespace CIL.Extraction

/-- Whether a raw local is the whole-vector type eligible for opaque storage. -/
private def opaqueLocalType : Option TypeExpr → Bool
  | some (.apply (.constructor scope "System.Runtime.Intrinsics.Vector128`1")
      (.primitive .uint64)) =>
    scope == intrinsicsScope
  | _ => false

/-- Every eligible local, in index order; addresses are taken by `ldloca` (18 or 0xFE0D). -/
def opaqueLocalIndices (closed : RawMethod) : List Nat :=
  let addressed := Std.TreeSet.ofList (closed.code.filterMap fun instruction =>
    if instruction.opcode == 18 || instruction.opcode == 65037 then localIndex instruction else none)
  ((closed.locals.zipIdx).filter fun (type, index) =>
    opaqueLocalType (some type) && !addressed.contains index).map Prod.snd

/-- Indexed opaque-local discovery agrees with direct local lookup and address membership. -/
theorem opaqueLocalIndices_eq_scan (closed : RawMethod) :
    opaqueLocalIndices closed = (List.range closed.locals.length).filter (fun index =>
      (match (closed.locals[index]? : Option TypeExpr) with
      | some (.apply (.constructor scope "System.Runtime.Intrinsics.Vector128`1")
          (.primitive .uint64)) =>
        scope == intrinsicsScope
      | _ => false) && !(closed.code.filterMap (fun instruction =>
        if instruction.opcode == 18 || instruction.opcode == 65037 then localIndex instruction
        else none)).contains index) := by
  simp only [opaqueLocalIndices, Std.TreeSet.contains_ofList]
  rw [List.range_eq_range', ← List.zipIdx_map_snd 0 closed.locals, List.filter_map]
  congr 1
  apply List.filter_congr
  intro entry present
  have found := List.mem_zipIdx_iff_getElem?.mp present
  simp only [Function.comp_def, found]
  rfl

#print axioms opaqueLocalIndices_eq_scan

/-- A live direct call to the exact scalar-unsafe creator needs whole-vector local storage. -/
private def hasRawScalarUnsafe : List RawInstruction → List Bool → Bool
  | raw :: rest, live :: mask =>
    (live && raw.opcode == 40 && (match raw.operand with
      | .call site => site.method == createScalarUnsafeMethod &&
          site.declared == createScalarUnsafeMethod.signature 0
      | _ => false)) || hasRawScalarUnsafe rest mask
  | _, _ => false

/-- The closed body and its live mask determine the opaque vector slots in its frame. -/
def rawOpaqueLocals (closed : RawMethod) (reachable : List Bool) : List Nat :=
  if closed.locals.any (fun type => opaqueLocalType (some type)) &&
      hasRawScalarUnsafe closed.code reachable then opaqueLocalIndices closed else []

/-- Every claimed opaque local has the emitted whole-vector slot kind. -/
private def opaqueKindsValid (method : Method) : Bool :=
  let kinds := FlowIndex.ofList method.localKinds
  method.opaqueVectorLocals.all fun index => kinds.get? index == some .vector128

/-- No emitted address operation exposes an opaque local's unspecified bytes. -/
private def opaqueAddressesValid (method : Method) : Bool :=
  let slots := Std.TreeSet.ofList method.opaqueVectorLocals
  method.code.all fun operation => match operation with
    | .ldloca index => !slots.contains index
    | _ => true
/-- Whether `operation` calls a method whose runtime model in `environment` is
    `CreateScalarUnsafe`. -/
def createsScalarUnsafe (environment : LayoutEnvironment) : Instruction → Bool
  | .call method _ =>
    runtimeModel environment .call method == some (.intrinsic (.vector .createScalarUnsafe64) 1)
  | _ => false

/-- A live scalar-unsafe creation requires opaque storage for each eligible vector local. -/
def expectedOpaqueLocals (environment : LayoutEnvironment) (closed : RawMethod)
    (code : List Instruction) : List Nat :=
  if code.any (createsScalarUnsafe environment) then opaqueLocalIndices closed else []

/-- The opaque locals are exactly the eligible ones when the method calls
    `CreateScalarUnsafe` and none otherwise; each is a 128-bit vector slot whose address the
    emitted code never takes. -/
def OpaqueLocalsValid (closed : RawMethod) (method : Method) : Prop :=
  method.opaqueVectorLocals = expectedOpaqueLocals method.environment closed method.code ∧
  opaqueKindsValid method = true ∧ opaqueAddressesValid method = true

/-- Indexed opaque-local checks preserve the original kind and no-address obligations. -/
theorem OpaqueLocalsValid_iff_scan (closed : RawMethod) (method : Method) :
    OpaqueLocalsValid closed method ↔
      method.opaqueVectorLocals = (if method.code.any (createsScalarUnsafe method.environment)
        then opaqueLocalIndices closed else []) ∧
      method.opaqueVectorLocals.all (fun index => method.localKinds[index]? == some .vector128) =
        true ∧
      method.code.all (fun operation => match operation with
        | .ldloca index => !(index ∈ method.opaqueVectorLocals)
        | _ => true) = true := by
  simp only [OpaqueLocalsValid, expectedOpaqueLocals, opaqueKindsValid, opaqueAddressesValid,
    FlowIndex.get?_ofList, Std.TreeSet.contains_ofList, List.contains_eq_mem]

#print axioms OpaqueLocalsValid_iff_scan
instance (closed : RawMethod) (method : Method) : Decidable (OpaqueLocalsValid closed method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end CIL.Extraction
