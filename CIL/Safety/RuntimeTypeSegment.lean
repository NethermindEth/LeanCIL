import CIL.Safety.Segment

/-! Run-to-run summaries for the original token loads and System.Type calls of a closed typeof comparison. -/

namespace CIL.Safety

/-- The actual getter converts the handle at the top of the stack to its runtime type. -/
theorem step_getTypeFromHandle {body : CIL.Method} {member : CIL.Extraction.MethodRef}
    {pc : Nat} {args stack : List Value} {frame : Frame} {memory : Memory}
    (link : body.linkAt pc = none)
    (getter : CIL.Extraction.runtimeModel body.environment .call member = some .typeFromHandle)
    (type : CIL.Extraction.TypeExpr) :
    step body (.call member {}) pc args frame (.typeHandle type :: stack) memory =
      .ok (.next (pc + 1) (.runtimeType type :: stack) frame memory) := by
  rw [step_call_model (link := link) (found := getter) (direct := rfl)]
  rfl
#print axioms step_getTypeFromHandle

/-- An ldtoken and its checked getter preserve the continuation, frame and caller memory. -/
theorem SegmentRun.loadRuntimeType {program : CIL.Program} {body : CIL.Method}
    {method pc : Nat} {type : CIL.Extraction.TypeExpr} {member : CIL.Extraction.MethodRef}
    (found : program[method]? = some body)
    (token : body.code[pc]? = some (.ldtoken (.type type)))
    (call : body.code[pc + 1]? = some (.call member {}))
    (link : body.linkAt (pc + 1) = none)
    (getter : CIL.Extraction.runtimeModel body.environment .call member = some .typeFromHandle)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory) :
    SegmentRun program method pc (pc + 2) 2 args ⟨frame, stack, memory⟩
      ⟨frame, .runtimeType type :: stack, memory⟩ := by
  intro fuel
  exact (run_next (fuel := fuel + 1) found token
    (step_ldtoken_type_eq body pc args frame memory type stack)).trans
    (run_next (fuel := fuel) found call (step_getTypeFromHandle link getter type))
#print axioms SegmentRun.loadRuntimeType

/-- A checked equality or inequality operator consumes the two types and pushes an i32. -/
theorem step_runtimeTypeComparison {body : CIL.Method} {member : CIL.Extraction.MethodRef}
    {pc : Nat} {args stack : List Value} {frame : Frame} {memory : Memory}
    {left right : CIL.Extraction.TypeExpr} {equal same : Bool}
    (link : body.linkAt pc = none)
    (model : CIL.Extraction.runtimeModel body.environment .call member = some (.typeEquality equal))
    (identity : CIL.Extraction.sameRuntimeType left right = some same) :
    step body (.call member {}) pc args frame (.runtimeType right :: .runtimeType left :: stack) memory =
      .ok (.next (pc + 1) (.scalar (.i32 (if same == equal then 1 else 0)) :: stack) frame memory) := by
  rw [step_call_model (link := link) (found := model) (direct := rfl)]
  change (do
    let answer ← runtimeTypeEqual left right
    pure (FrameAction.next (pc + 1) (.scalar (.i32 (if answer == equal then 1 else 0)) :: stack)
      frame memory)) = _
  simp only [runtimeTypeEqual, identity, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms step_runtimeTypeComparison

/-- Two token/getter pairs and a comparison call preserve the remaining stack and memory. -/
theorem SegmentRun.compareRuntimeTypes {program : CIL.Program} {body : CIL.Method}
    {method pc : Nat} {left right : CIL.Extraction.TypeExpr}
    {getter comparison : CIL.Extraction.MethodRef} {equal same : Bool}
    (found : program[method]? = some body)
    (leftToken : body.code[pc]? = some (.ldtoken (.type left)))
    (leftCall : body.code[pc + 1]? = some (.call getter {}))
    (rightToken : body.code[pc + 2]? = some (.ldtoken (.type right)))
    (rightCall : body.code[pc + 3]? = some (.call getter {}))
    (test : body.code[pc + 4]? = some (.call comparison {}))
    (leftLink : body.linkAt (pc + 1) = none) (rightLink : body.linkAt (pc + 3) = none)
    (testLink : body.linkAt (pc + 4) = none)
    (handle : CIL.Extraction.runtimeModel body.environment .call getter = some .typeFromHandle)
    (model : CIL.Extraction.runtimeModel body.environment .call comparison = some (.typeEquality equal))
    (identity : CIL.Extraction.sameRuntimeType left right = some same)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory) :
    SegmentRun program method pc (pc + 5) 5 args ⟨frame, stack, memory⟩
      ⟨frame, .scalar (.i32 (if same == equal then 1 else 0)) :: stack, memory⟩ := by
  intro fuel
  exact (SegmentRun.loadRuntimeType found leftToken leftCall leftLink handle args frame stack memory
    (fuel + 3)).trans <| (SegmentRun.loadRuntimeType found rightToken rightCall rightLink handle
      args frame (.runtimeType left :: stack) memory (fuel + 1)).trans <|
    run_next (fuel := fuel) found test (step_runtimeTypeComparison testLink model identity)
#print axioms SegmentRun.compareRuntimeTypes

end CIL.Safety
