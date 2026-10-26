import CIL.Extraction.Constrained
import CIL.Extraction.DivisionIntrinsics

/-! Standalone comparisons between indexed and streaming sequential metadata checks. -/
namespace Tests.StreamingValidationScaling
open CIL CIL.Extraction
set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-- Raw metadata shell for an isolated instruction workload. -/
def raw (code : List RawInstruction) : RawMethod := {
  token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := true, maxStack := 1,
  genericParameters := [], code := code }

/-- Every instruction is reachable, even when it needs no constrained resolution. -/
def nops (count : Nat) := raw (List.replicate count ⟨0, 0, .none⟩)

/-- Matching emitted code. -/
def body (count : Nat) : Method := {
  locals := [], returnsValue := false, code := List.replicate count .nop }

/-- Previous implementation using indexed lookup for each sequential position. -/
def indexedConstrained (raw : RawMethod) (reachable : List Bool) (emitted : Method) : Prop :=
  raw.code.length = reachable.length ∧ raw.code.length = emitted.code.length ∧
    (List.range raw.code.length).all (constrainedSiteCheck [] (FlowIndex.ofList []).get?
      (FlowIndex.ofList raw.code).get? (FlowIndex.ofList reachable).get?
      (FlowIndex.ofList emitted.code).get?
      (Std.TreeSet.ofList (constrainedBranchTargets raw.code)).contains) = true

/-- Eligible vector-local metadata. -/
def vector : TypeExpr := .apply
  (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1")
  (.atom runtimeScope "System.UInt64")

/-- No address instructions obscure the positional local lookup cost. -/
def locals (count : Nat) := { raw [] with locals := List.replicate count vector }

/-- Previous opaque-local enumeration through positional lookup. -/
def indexedOpaque (closed : RawMethod) : List Nat :=
  let addressed := Std.TreeSet.ofList (closed.code.filterMap fun instruction =>
    if instruction.opcode == 18 || instruction.opcode == 65037 then localIndex instruction else none)
  let types := FlowIndex.ofList closed.locals
  (List.range closed.locals.length).filter fun index =>
    (match types.get? index with
      | some (.apply (.constructor scope "System.Runtime.Intrinsics.Vector128`1")
          (.atom elementScope "System.UInt64")) =>
        scope == intrinsicsScope && elementScope == runtimeScope
      | _ => false) && !addressed.contains index

/-- Indexed reference at 128 instructions. -/
theorem constrainedIndexed128 : indexedConstrained (nops 128)
    (List.replicate 128 true) (body 128) := by unfold indexedConstrained; decide +kernel
#print axioms constrainedIndexed128
/-- Streaming check at 128 instructions. -/
theorem constrainedStream128 : ConstrainedCallsValid [] [] (nops 128)
    (List.replicate 128 true) (body 128) := by decide +kernel
#print axioms constrainedStream128
/-- Indexed reference at 128 locals. -/
theorem opaqueIndexed128 : indexedOpaque (locals 128) = List.range 128 := by decide +kernel
#print axioms opaqueIndexed128
/-- Streaming enumeration at 128 locals. -/
theorem opaqueStream128 : opaqueLocalIndices (locals 128) = List.range 128 := by decide +kernel
#print axioms opaqueStream128

/-- Indexed reference at 512 instructions. -/
theorem constrainedIndexed512 : indexedConstrained (nops 512)
    (List.replicate 512 true) (body 512) := by unfold indexedConstrained; decide +kernel
#print axioms constrainedIndexed512
/-- Streaming check at 512 instructions. -/
theorem constrainedStream512 : ConstrainedCallsValid [] [] (nops 512)
    (List.replicate 512 true) (body 512) := by decide +kernel
#print axioms constrainedStream512
/-- Indexed reference at 512 locals. -/
theorem opaqueIndexed512 : indexedOpaque (locals 512) = List.range 512 := by decide +kernel
#print axioms opaqueIndexed512
/-- Streaming enumeration at 512 locals. -/
theorem opaqueStream512 : opaqueLocalIndices (locals 512) = List.range 512 := by decide +kernel
#print axioms opaqueStream512

end Tests.StreamingValidationScaling
