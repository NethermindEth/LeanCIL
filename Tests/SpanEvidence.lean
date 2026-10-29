import CIL.Extraction.Features
import CIL.Extraction.SpanCalls

set_option maxRecDepth 4096

/-! Certificate regression fixtures, evaluated against the checked CIL extraction model. -/

namespace Tests.SpanEvidence
open CIL CIL.Extraction

/-- The primitive assembly identity with its checked byte representation. -/
private def runtime := runtimeScope
private def owner := "Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
private def intType : TypeExpr := .atom runtime "System.Int32"
private def span (scope element : String) : TypeExpr :=
  .apply (.constructor scope "System.ReadOnlySpan`1") (.atom runtime element)
private def words := span runtime "System.UInt32"

private def getItem : RawOperand := .call {
  declaringType := words, name := "get_Item",
  target := .external (runtime ++ "::!0& modreq(System.Runtime.InteropServices.InAttribute) System.ReadOnlySpan`1<System.UInt32>::get_Item(System.Int32)"),
  typeArguments := [], parameterCount := 1, hasThis := true, returnsValue := true }

private def i (opcode : Nat) (operand : RawOperand := .none) : RawInstruction := ⟨0, opcode, operand⟩
private def raw (locals : List TypeExpr) (code : List RawInstruction) : RawMethod := {
  token := 1, owner := owner ++ "::Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := intType, parameters := [words, intType], locals, initLocals := true, maxStack := 8,
  genericParameters := [], code }
private def state (stack : List (Option W32)) : Option FeatureState := some ⟨stack, [none]⟩

-- Only a primitive runtime span names a span local.
example : spanLocal words ∧ spanLocal (span runtime "System.Byte") := by decide
example : ¬ spanLocal (span owner "System.UInt32") ∧ ¬ spanLocal (span runtime "System.Double") ∧
    ¬ spanLocal intType := by decide

/-- Native integers and the two small primitive types retain their physical element widths. -/
theorem primitive_span_widths :
    spanStorage (span runtime "System.IntPtr") = some (.span 8 false) ∧
    spanStorage (span runtime "System.UIntPtr") = some (.span 8 false) ∧
    spanStorage (span runtime "System.Char") = some (.span 2 false) ∧
    spanStorage (span runtime "System.Boolean") = some (.span 1 false) := by decide
#print axioms primitive_span_widths

/-- A closed int32 array extension call with its exact defining assembly. -/
private def arraySpanCall : CallSite := {
  declaringType := .atom spanMemoryScope "System.MemoryExtensions"
  name := "AsSpan"
  target := .external (spanMemoryScope ++
    "::System.Span`1<!!0> System.MemoryExtensions::AsSpan(!!0[],System.Int32)")
  typeArguments := [intType], parameterCount := 2, hasThis := false, returnsValue := true
  returnType := .apply (.constructor runtime "System.Span`1") intType
  parameterTypes := [.array intType, intType] }

/-- Array conversion certificates bind element identity, range arity and all call metadata. -/
theorem exact_array_span_call :
    spanCallMatches (i 40 (.call arraySpanCall))
      (.memory (.arraySpan .signed32 true .fromStart)) = true ∧
    spanCallMatches (i 40 (.call arraySpanCall))
      (.memory (.arraySpan .unsigned32 true .fromStart)) = false ∧
    spanCallMatches (i 40 (.call arraySpanCall))
      (.memory (.arraySpan .signed32 false .fromStart)) = false ∧
    spanCallMatches (i 40 (.call arraySpanCall))
      (.memory (.arraySpan .signed32 true .whole)) = false ∧
    spanCallMatches (i 115 (.call arraySpanCall))
      (.memory (.arraySpan .signed32 true .fromStart)) = false ∧
    spanCallMatches (i 40 (.call { arraySpanCall with hasThis := true }))
      (.memory (.arraySpan .signed32 true .fromStart)) = false ∧
    spanCallMatches (i 40 (.call { arraySpanCall with
      declaringType := .atom runtime "System.MemoryExtensions" }))
      (.memory (.arraySpan .signed32 true .fromStart)) = false ∧
    spanCallMatches (i 40 (.call { arraySpanCall with parameterTypes := [intType, intType] }))
      (.memory (.arraySpan .signed32 true .fromStart)) = false := by decide
#print axioms exact_array_span_call

-- 0: ldarg.0; 1: stloc.0; 2: ldloca.s 0; 3: ldarg.1; 4: get_Item; 5: ldind.u4; 6: ret
private def itemCode := [i 2, i 10, i 18 (.local 0), i 3, i 40 getItem, i 74, i 42]
private def itemStates : FeatureCertificate :=
  [state [], state [none], state [], state [none], state [none, none], state [none], state [none]]
private def itemOps : List Op :=
  [.arg 0, .nop, .nop, .arg 1, .memory (.spanItem 4), .loadScalar 4, .ret none]

example : foldRoles [words] itemCode = [none, some .head, some .interior, none, none, none, none] := by decide
example : foldRoles [intType] itemCode = List.replicate 7 none := by decide
example : foldRoles [words] [i 10, i 18 (.local 1)] = [none, none] := by decide

/-- A third decoded local use disallows receiver folding anywhere in the body. -/
theorem extra_local_use : foldRoles [words] (itemCode ++ [i 6]) =
    List.replicate 8 none := by decide +kernel
#print axioms extra_local_use

/-- A malformed local-load operand does not count as a decoded use of local zero. -/
theorem malformed_local_operand :
    foldRoles [words] (itemCode ++ [i 65036 (.argument 0)]) =
      [none, some .head, some .interior, none, none, none, none, none] := by decide +kernel
#print axioms malformed_local_operand
-- Only the store may be entered from elsewhere.
example : foldEntry (foldRoles [words] itemCode)[1]? ∧
    ¬ foldEntry (foldRoles [words] itemCode)[2]? := by decide

example : FeatureFlowValid (raw [words] itemCode) .scalar itemStates (List.replicate 7 true) itemOps := by decide
-- The receiver must stay on the stack: a real store or address is not the fold.
example : ¬ FeatureFlowValid (raw [words] itemCode) .scalar itemStates (List.replicate 7 true)
    (itemOps.set 1 (.setLocal 0 none)) := by decide
example : ¬ FeatureFlowValid (raw [words] itemCode) .scalar itemStates (List.replicate 7 true)
    (itemOps.set 2 (.localAddr 0)) := by decide

-- Span locals outside a receiver fold retain ordinary load/store flow.
private def loadCode := [i 2, i 10, i 6, i 42]
private def loadOps : List Op := [.arg 0, .setLocal 0 none, .local 0 none, .ret none]
private def loadStates : FeatureCertificate := [state [], state [none], state [], state [none]]
example : FeatureFlowValid (raw [intType] loadCode) .scalar loadStates (List.replicate 4 true) loadOps := by decide
example : FeatureFlowValid (raw [words] loadCode) .scalar loadStates (List.replicate 4 true) loadOps := by decide

-- `ldtoken` of a field is static data; only a type handle belongs to a type test.
example : ¬ typeTestInstruction (i 208 (.field (.atom owner "<PrivateImplementationDetails>") 0 intType true)) ∧
    typeTestInstruction (i 208 (.type intType)) := by decide

/-- The exact writable int32 span member used by whole-region initialization. -/
private def fillCall : CallSite := {
  declaringType := .apply (.constructor runtime "System.Span`1") intType
  name := "Fill"
  target := .external (runtime ++ "::System.Void System.Span`1<System.Int32>::Fill(!0)")
  typeArguments := [], parameterCount := 1, hasThis := true, returnsValue := false
  returnType := .void, parameterTypes := [intType] }

/-- Whole-span stores bind the operation, element width, mutability and complete signature. -/
theorem exact_span_fill_call :
    spanCallMatches (i 40 (.call fillCall)) (.memory (.spanFill 4 false)) = true ∧
    spanCallMatches (i 40 (.call fillCall)) (.memory (.spanFill 8 false)) = false ∧
    spanCallMatches (i 40 (.call fillCall)) (.memory (.spanFill 4 true)) = false ∧
    spanCallMatches (i 40 (.call fillCall)) (.memory (.spanSlice false)) = false ∧
    spanCallMatches (i 40 (.call { fillCall with
      declaringType := .apply (.constructor runtime "System.ReadOnlySpan`1") intType }))
      (.memory (.spanFill 4 false)) = false ∧
    spanCallMatches (i 40 (.call { fillCall with
      parameterTypes := [.atom runtime "System.UInt32"] }))
      (.memory (.spanFill 4 false)) = false ∧
    spanCallMatches (i 40 (.call { fillCall with hasThis := false }))
      (.memory (.spanFill 4 false)) = false ∧
    spanCallMatches (i 40 (.call { fillCall with returnType := intType, returnsValue := true }))
      (.memory (.spanFill 4 false)) = false := by decide +kernel
#print axioms exact_span_fill_call

end Tests.SpanEvidence
