import CIL.Extraction.Features

set_option maxRecDepth 4096

namespace Tests.FeatureEvidence
open CIL CIL.Extraction

private def intType : TypeExpr := .atom
  "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" "System.Int32"
private def getter : CallSite := {
  target := .external "System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51::System.Boolean System.Runtime.Intrinsics.X86.Sse2::get_IsSupported()"
  typeArguments := [], parameterCount := 0, hasThis := false, returnsValue := true }
private def intrinsic (member : String) : CallSite :=
  { getter with target := .external ("System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51::System.Boolean System.Runtime.Intrinsics." ++ member ++ "()") }

-- Each getter binds to its own flag; Vector128 has no IsSupported.
example : featureGetter (intrinsic "X86.X86Base/X64::get_IsSupported") = some .x86Base64 := by decide
example : featureGetter (intrinsic "Vector128::get_IsHardwareAccelerated") = some .vector128Accelerated := by decide
example : featureGetter (intrinsic "Vector128::get_IsSupported") = none := by decide
-- Every x86 ISA class derives from X86Base, and X86Base.X64 exists only on x64.
example : ¬ ({ architecture := .x64, bmi2 := true } : FeatureProfile).Valid := by decide
example : ¬ ({ architecture := .x64, bmi2 := true, x86Base64 := true } : FeatureProfile).Valid := by decide
example : ¬ ({ architecture := .arm64, x86Base64 := true } : FeatureProfile).Valid := by decide
example : ¬ ({ architecture := .arm64, vector128Accelerated := true } : FeatureProfile).Valid := by decide

private def v3 : FeatureProfile := {
  architecture := .x64, x86Base64 := true, sse2 := true, ssse3 := true, sse41 := true, sse42 := true
  avx := true, avx2 := true, bmi1 := true, bmi2 := true, vector128Accelerated := true, vector256Accelerated := true }
example : v3.Valid := by decide
example : { v3 with vector256Accelerated := false }.Valid := by decide
example : ¬ { v3 with bmi1 := false }.Valid := by decide
example : ¬ { v3 with bmi2 := false }.Valid := by decide
example : ¬ { v3 with sse42 := false }.Valid := by decide
example : ¬ { v3 with avx512F := true, avx512FVL := true }.Valid := by decide
example : ({ architecture := .arm64, armBase64 := true, advSimd := true, vector128Accelerated := true } : FeatureProfile).Valid := by decide
example : ¬ ({ architecture := .arm64, armBase64 := true } : FeatureProfile).Valid := by decide
example : ¬ ({ architecture := .arm64, vector256Accelerated := true } : FeatureProfile).Valid := by decide

private def raw (code : List RawInstruction) (locals : List TypeExpr := [])
    (returnType : TypeExpr := intType) : RawMethod := {
  token := 1, owner := "Fixture", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType, parameters := [], locals, initLocals := true, maxStack := 8,
  genericParameters := [], code }
private def i (opcode : Nat) (operand : RawOperand := .none) : RawInstruction := ⟨0, opcode, operand⟩
private def state (stack : List (Option W32)) (locals : List (Option W32) := []) : Option FeatureState :=
  some ⟨stack, locals⟩
private def branchRaw := raw [i 40 (.call getter), i 45 (.target 4), i 22, i 42, i 23, i 42]
private def branchStates : FeatureCertificate := [state [], state [some 0], state [], state [some 0], none, none]
private def branchCode : List Op := [.feature .sse2, .brnonzero 4, .const32 0, .ret, .unsupported "pruned", .unsupported "pruned"]
private def branchMask := [true, true, true, true, false, false]

example : FeatureFlowValid #[] branchRaw .scalar branchStates branchMask branchCode := by decide
-- A forged incoming constant cannot justify deleting the actual fallthrough.
example : ¬ FeatureFlowValid #[] branchRaw .scalar (branchStates.set 1 (state [some 1]))
    branchMask branchCode := by decide
example : ¬ FeatureFlowValid #[] branchRaw .scalar (branchStates.set 2 none)
    (branchMask.set 2 false) (branchCode.set 2 (.unsupported "false pruning")) := by decide
example : ¬ FeatureFlowValid #[] branchRaw .scalar branchStates branchMask
    (branchCode.set 0 (.feature .avx2)) := by decide
example : ¬ FeatureFlowValid #[] branchRaw .scalar branchStates branchMask
    (branchCode.set 1 (.brnonzero 5)) := by decide
example : ¬ FeatureFlowValid #[] branchRaw .scalar (branchStates.set 0 (state [none]))
    branchMask branchCode := by decide
example : ¬ FeatureFlowValid #[] branchRaw .scalar branchStates (branchMask.set 0 false)
    branchCode := by decide

-- A backedge changes a local from zero to one. The join must forget the constant,
-- so the branch keeps both successors even though the first iteration is false.
private def loopRaw := raw
  [i 22, i 10, i 6, i 22, i 51 (.target 8), i 23, i 10, i 43 (.target 2), i 42] [intType] .void
private def loopStates : FeatureCertificate := [state [] [none], state [some 0] [none],
  state [] [none], state [none] [none], state [some 0, none] [none],
  state [] [none], state [some 1] [none],
  state [] [some 1], state [] [none]]
private def loopCode : List Op := [.const32 0, .setLocal 0, .local 0, .const32 0, .bne 8,
  .const32 1, .setLocal 0, .branch 2, .ret]
example : FeatureFlowValid #[] loopRaw .scalar loopStates (List.replicate 9 true) loopCode := by decide
example : ¬ FeatureFlowValid #[] loopRaw .scalar (loopStates.set 2 (state [] [some 0]))
    (List.replicate 9 true) loopCode := by decide
example : ¬ FeatureFlowValid #[] loopRaw .scalar (loopStates.set 8 none)
    [true, true, true, true, true, true, true, true, false]
    (loopCode.set 8 (.unsupported "pruned backedge exit")) := by decide
-- Taking a local's address anywhere invalidates constant facts for that local.
example : ¬ FeatureFlowValid #[]
    { loopRaw with code := loopRaw.code ++ [i 18 (.local 0)] }
    .scalar (loopStates ++ [none]) ((List.replicate 9 true) ++ [false])
    (loopCode ++ [.unsupported "unreachable address"]) := by decide

private def switchRaw := raw [i 2, i 69 (.targets [4, 6]), i 23, i 42, i 24, i 42, i 25, i 42]
private def switchStates : FeatureCertificate := [state [], state [none], state [], state [some 1],
  state [], state [some 2], state [], state [some 3]]
private def switchCode : List Op := [.arg 0, .switch [4, 6], .const32 1, .ret, .const32 2, .ret, .const32 3, .ret]
example : FeatureFlowValid #[] switchRaw .scalar switchStates (List.replicate 8 true) switchCode := by decide
example : ¬ FeatureFlowValid #[] switchRaw .scalar (switchStates.set 6 none)
    [true, true, true, true, true, true, false, true] (switchCode.set 6 (.unsupported "missing switch edge")) := by decide

-- Bitwise feature expressions preserve exact int32 words, including negative
-- constants. Unknown operands remain unknown; ceq never guesses equality.
example : featureTransfer #[] branchRaw .scalar (i 95) ⟨[some 3, some 1], []⟩ = some ⟨[some 1], []⟩ := by decide
example : featureTransfer #[] branchRaw .scalar (i 96) ⟨[some 2, some 1], []⟩ = some ⟨[some 3], []⟩ := by decide
example : featureTransfer #[] branchRaw .scalar (i 97) ⟨[some 1, some 1], []⟩ = some ⟨[some 0], []⟩ := by decide
example : featureTransfer #[] branchRaw .scalar (i 65025) ⟨[some 1, some 1], []⟩ = some ⟨[some 1], []⟩ := by decide
example : featureTransfer #[] branchRaw .scalar (i 65025) ⟨[none, some 1], []⟩ = some ⟨[none], []⟩ := by decide
example : featureTransfer #[] branchRaw .scalar (i 95) ⟨[], []⟩ = none := by decide
-- Native operand normalization does not change a binary branch destination.
example : featureOpMatches #[] branchRaw (i 48 (.target 2)) (.nativeBinary (.bgt 2)) = true := by decide
example : featureOpMatches #[] branchRaw (i 48 (.target 2)) (.nativeBinary (.bgt 3)) = false := by decide

-- A stack-changing replacement for nop used to forge the value at a following
-- branch while the raw-body analysis still justified pruning its taken edge.
private def nopRaw := raw [i 22, i 0, i 45 (.target 5), i 22, i 42, i 23, i 42]
private def nopStates : FeatureCertificate := [state [], state [some 0], state [some 0],
  state [], state [some 0], none, none]
private def nopCode : List Op := [.const32 0, .nop, .brnonzero 5, .const32 0, .ret,
  .unsupported "pruned", .unsupported "pruned"]
example : FeatureFlowValid #[] nopRaw .scalar nopStates [true, true, true, true, true, false, false] nopCode := by decide
example : ¬ FeatureFlowValid #[] nopRaw .scalar nopStates [true, true, true, true, true, false, false]
    (nopCode.set 1 (.const32 1)) := by decide
example : featureOpMatches #[] loopRaw (i 0) (.setLocal 0) = false := by decide
example : featureOpMatches #[] loopRaw (i 38) (.setLocal 0) = false := by decide
example : featureOpMatches #[] loopRaw (i 0) (.bgt 7) = false := by decide
example : featureOpMatches #[] loopRaw (i 0) (.ret) = false := by decide
example : featureOpMatches #[] loopRaw (i 0) (.nativeBinary (.bgt 7)) = false := by decide
example : featureOpMatches #[] loopRaw (i 33 (.integer 0)) (.localAddr 0) = false := by decide
example : featureOpMatches #[] loopRaw (i 33 (.integer 0)) (.vectorLocalAddr 0) = false := by decide
example : featureOpMatches #[] loopRaw (i 33 (.integer 0)) (.vectorArgAddr 0) = false := by decide
example : featureOpMatches #[] loopRaw (i 10) (.setLocal 1) = false := by decide
example : featureOpMatches #[] loopRaw (i 18 (.local 0)) (.localAddr 1) = false := by decide
example : featureOpMatches #[] loopRaw (i 122) (.pop) = false := by decide
example : featureOpMatches #[] loopRaw (i 65050) (.nop) = false := by decide
example : featureOpMatches #[] loopRaw (i 220) (.nop) = false := by decide
example : featureOpMatches #[] loopRaw (i 65041) (.pop) = false := by decide
example : featureOpMatches #[] loopRaw (i 39) (.nop) = false := by decide
-- Unknown-result operations still have to preserve the rest of the stack.
example : featureOpMatches #[] branchRaw (i 88) (.add) = true := by decide
example : featureOpMatches #[] branchRaw (i 88) (.nop) = false := by decide
example : emittedFeatureEffect (.memory (.copyBlock 8)) false = some (3, 0) := by decide
example : emittedFeatureEffect (.newAggregate 1 2 ⟨8, by decide⟩) false = some (2, 1) := by decide
/-- Indexed facts retain boolean bounds, exact type identity, address exclusions and absence. -/
theorem indexed_local_eligibility :
    let types := [intType, .atom runtimeScope "System.Boolean",
      .atom "Wrong.Runtime" "System.Int32", .byref intType]
    let locals := FeatureLocalIndex.ofRaw (raw [i 18 (.local 0), i 65037 (.local 3)] types)
    locals.eligible 0 (some 1) = false ∧ locals.eligible 0 none = true ∧
    locals.eligible 1 (some 0) = true ∧ locals.eligible 1 (some 1) = true ∧
    locals.eligible 1 (some 2) = false ∧ locals.eligible 2 (some 0) = false ∧
    locals.eligible 3 (some 0) = false ∧ locals.eligible 99 (some 0) = false ∧
    locals.eligible 99 none = true := by decide +kernel
#print axioms indexed_local_eligibility

/-- A malformed address operand neither invents an index nor excludes an unrelated local. -/
theorem indexed_malformed_address :
    let locals := FeatureLocalIndex.ofRaw (raw [i 18 (.integer 0), i 65037 (.local 99)] [intType])
    locals.eligible 0 (some 42) = true ∧ locals.eligible 99 (some 42) = false := by decide +kernel
#print axioms indexed_malformed_address

/-- Signed and unsigned boundary decisions agree in both short and long branch encodings. -/
theorem constant_branch_boundaries :
    ([( -1, 0, [false, false, false, true, true, true, true, true, false, false]),
      (0, -1, [false, true, true, false, false, true, false, false, true, true]),
      (-2147483648, 2147483647,
        [false, false, false, true, true, true, true, true, false, false]),
      (2147483647, -2147483648,
        [false, true, true, false, false, true, false, false, true, true]),
      (-1, -1, [true, true, false, true, false, false, true, false, true, false])] :
        List (Int × Int × List Bool)).all (fun (left, right, expected) =>
          [46, 59].all fun first => (List.range 10).all fun index =>
            featureSuccessors none 2 (i (first + index) (.target 5))
              ⟨[some (BitVec.ofInt 32 right), some (BitVec.ofInt 32 left)], []⟩ ==
                some [if expected[index]?.getD false then 5 else 3]) = true := by decide +kernel
#print axioms constant_branch_boundaries

/-- An unknown operand keeps both comparison edges; no argument fact is guessed. -/
theorem unknown_comparison_edges :
    [46, 59].all (fun first => (List.range 10).all fun index =>
      [([none, some 0] : List (Option W32)), [some 0, none], [none, none]].all fun stack =>
        featureSuccessors none 2 (i (first + index) (.target 5)) ⟨stack, []⟩ == some [5, 3]) =
          true := by decide +kernel
#print axioms unknown_comparison_edges

/-- A known signed comparison prunes only its untaken edge in the independent flow certificate. -/
theorem comparison_certificate :
    let body := raw [i 21, i 22, i 50 (.target 5), i 22, i 42, i 23, i 42]
    let facts := [state [], state [some (-1)], state [some 0, some (-1)], none, none,
      state [], state [some 1]]
    let code := [.const32 (-1), .const32 0, .blt 5, .unsupported "pruned", .unsupported "pruned",
      .const32 1, .ret]
    FeatureFlowValid #[] body .scalar facts [true, true, true, false, false, true, true] code ∧
    ¬ FeatureFlowValid #[] body .scalar facts [true, true, true, false, false, true, true]
      (code.set 2 (.bltu 5)) ∧
    ¬ FeatureFlowValid #[] body .scalar (facts.set 5 none)
      [true, true, true, false, false, false, true] code := by decide +kernel
#print axioms comparison_certificate

/-- Comparison results preserve unknowns and distinguish signed from unsigned ordering. -/
theorem comparison_results :
    ([65025, 65026, 65027, 65028, 65029].zip [0, 0, 1, 1, 0]).all
      (fun (opcode, expected) =>
        featureTransfer #[] (raw []) .scalar (i opcode) ⟨[some 0, some (-1)], []⟩ ==
          some ⟨[some expected], []⟩ &&
        featureTransfer #[] (raw []) .scalar (i opcode) ⟨[none, some (-1)], []⟩ ==
          some ⟨[none], []⟩) = true := by decide +kernel
#print axioms comparison_results

/-- Widening an int32 constant does not create a native-width fact in the int32 domain. -/
theorem widened_comparison_unknown :
    featureTransfer #[] (raw []) .scalar (i 211) ⟨[some (-1)], []⟩ = some ⟨[none], []⟩ ∧
    featureTransfer #[] (raw []) .scalar (i 224) ⟨[some (-1)], []⟩ = some ⟨[none], []⟩ ∧
    featureSuccessors none 2 (i 51 (.target 5)) ⟨[none, some (-1)], []⟩ = some [5, 3] :=
  by decide +kernel
#print axioms widened_comparison_unknown

/-- Switch indices are unsigned int32 values; unknowns preserve every encoded successor. -/
theorem constant_switch_successors :
    featureSuccessors none 1 (i 69 (.targets [4, 6])) ⟨[some 0], []⟩ = some [4] ∧
    featureSuccessors none 1 (i 69 (.targets [4, 6])) ⟨[some 1], []⟩ = some [6] ∧
    featureSuccessors none 1 (i 69 (.targets [4, 4])) ⟨[some 1], []⟩ = some [4] ∧
    featureSuccessors none 1 (i 69 (.targets [4, 6])) ⟨[some 2], []⟩ = some [2] ∧
    featureSuccessors none 1 (i 69 (.targets [4, 6])) ⟨[some (-1)], []⟩ = some [2] ∧
    featureSuccessors none 1 (i 69 (.targets [])) ⟨[some 0], []⟩ = some [2] ∧
    featureSuccessors none 1 (i 69 (.targets [4, 6])) ⟨[none], []⟩ = some [2, 4, 6] :=
  by decide +kernel
#print axioms constant_switch_successors

/-- Unselected switch targets still belong to the method and must match the emitted table. -/
theorem switch_certificate_targets :
    let body := raw [i 22, i 69 (.targets [4, 6]), i 23, i 42, i 24, i 42, i 25, i 42]
    let facts := [state [], state [some 0], none, none, state [], state [some 2], none, none]
    let code := [.const32 0, .switch [4, 6], .unsupported "pruned", .unsupported "pruned",
      .const32 2, .ret, .unsupported "pruned", .unsupported "pruned"]
    let mask := [true, true, false, false, true, true, false, false]
    FeatureFlowValid #[] body .scalar facts mask code ∧
    ¬ FeatureFlowValid #[] body .scalar facts mask (code.set 1 (.switch [4, 5])) ∧
    ¬ FeatureFlowValid #[] { body with code := body.code.set 1 (i 69 (.targets [4, 100])) }
      .scalar facts mask (code.set 1 (.switch [4, 100])) ∧
    ¬ FeatureFlowValid #[] body .scalar (facts.set 4 none) (mask.set 4 false)
      (code.set 4 (.unsupported "false pruning")) := by decide +kernel
#print axioms switch_certificate_targets

/-- An unselected table arm or untaken comparison cannot enter a tail transfer after its prefix. -/
theorem pruned_tail_entry_rejected :
    let tail := [i 65044, i 40 (.call { getter with target := .managed 0 }), i 42]
    let switchBody := raw ([i 22, i 69 (.targets [2, 5]), i 23, i 42] ++ tail)
    let switchFacts := [state [], state [some 0], state [], state [some 1], none, none, none]
    let switchCode := [.const32 0, .switch [2, 5], .const32 1, .ret,
      .unsupported "pruned", .unsupported "pruned", .unsupported "pruned"]
    let branchBody := raw ([i 22, i 22, i 51 (.target 6), i 23, i 42] ++ tail)
    let branchFacts := [state [], state [some 0], state [some 0, some 0], state [], state [some 1],
      none, none, none]
    let branchCode := [.const32 0, .const32 0, .bne 6, .const32 1, .ret,
      .unsupported "pruned", .unsupported "pruned", .unsupported "pruned"]
    FeatureFlowValid #[] { switchBody with code := switchBody.code.set 1 (i 69 (.targets [2, 4])) }
      .scalar switchFacts [true, true, true, true, false, false, false]
      (switchCode.set 1 (.switch [2, 4])) ∧
    ¬ FeatureFlowValid #[] switchBody .scalar switchFacts
      [true, true, true, true, false, false, false] switchCode ∧
    FeatureFlowValid #[] { branchBody with code := branchBody.code.set 2 (i 51 (.target 5)) }
      .scalar branchFacts [true, true, true, true, true, false, false, false]
      (branchCode.set 2 (.bne 5)) ∧
    ¬ FeatureFlowValid #[] branchBody .scalar branchFacts
      [true, true, true, true, true, false, false, false] branchCode := by decide +kernel
#print axioms pruned_tail_entry_rejected

/-- A switch selector weakened by a backedge cannot retain the first iteration's chosen arm. -/
theorem switch_backedge_weakening :
    let body := raw [i 22, i 10, i 6, i 69 (.targets [4, 7]), i 23, i 10,
      i 43 (.target 2), i 42] [intType] .void
    let facts := [state [] [none], state [some 0] [none], state [] [none], state [none] [none],
      state [] [none], state [some 1] [none], state [] [some 1], state [] [none]]
    let code := [.const32 0, .setLocal 0, .local 0, .switch [4, 7], .const32 1, .setLocal 0,
      .branch 2, .ret]
    FeatureFlowValid #[] body .scalar facts (List.replicate 8 true) code ∧
    ¬ FeatureFlowValid #[] body .scalar (facts.set 2 (state [] [some 0]))
      (List.replicate 8 true) code ∧
    ¬ FeatureFlowValid #[] body .scalar (facts.set 7 none)
      [true, true, true, true, true, true, true, false]
      (code.set 7 (.unsupported "pruned backedge exit")) := by decide +kernel
#print axioms switch_backedge_weakening

end Tests.FeatureEvidence
