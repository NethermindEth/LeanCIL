import CIL.Extraction.ValueDecoding
import CIL.Extraction.RuntimeSignatures

/-!
# Object operand admission

Live object instructions use the storage shape of their closed type operand. A span load
requires a direct address of the same view, and a span reset requires a folded local constructor.
-/

namespace CIL.Extraction

/-- The storage shapes that an object opcode admits. -/
def objectShapeAdmitted (opcode : Nat) (shape : ValueShape) : Bool :=
  match shape with
  | .span => opcode == 0x71
  | .unsupported _ => false
  | _ => opcode ∈ [0x70, 0x71, 0x81, 0xfe15, 0xfe1c]

/-- The type of the span home loaded or addressed immediately before a span copy. -/
private def spanCopySource (parameter localAt : Nat → Option TypeExpr)
    (previous : RawInstruction) : Option TypeExpr := do
  match argumentOperation previous with
  | some (.load index) =>
    let .byref type ← parameter index | none
    return type
  | some (.address index) => parameter index
  | _ =>
    if previous.opcode ∉ [18, 65037] then none else
      localAt (← encodedLocal previous)

/-- The distinct live opcode and type pairs, after checking span provenance and reset folds. -/
def objectOperands (raw : RawMethod) (reachable : List Bool) (method : Method) :
    Option (List (Nat × TypeExpr)) := do
  let targets := Std.TreeSet.ofList (branchTargets raw.code) compare
  let parameters := FlowIndex.ofList raw.parameters
  let locals := FlowIndex.ofList raw.locals
  let parameter := fun index => if raw.hasThis && index == 0 then none else
    parameters.get? (index - raw.hasThis.toNat)
  let mut seen : Std.TreeMap (List (List UInt8)) (List TypeExpr) compare := ∅
  let mut operands := []
  let mut previous := none
  let mut pc := 0
  for (current, live, emitted) in raw.code.zip (reachable.zip method.code) do
    if live && current.opcode ∈ [0x70, 0x71, 0x81, 0xfe15, 0xfe1c] then
      let .type type := current.operand | return ← none
      if current.opcode == 0xfe15 && spanLocal type then
        unless emitted matches .initializeSpanLocal _ (.empty ..) do return ← none
      else
        if current.opcode == 0x71 && spanLocal type then
          let source := previous.bind (spanCopySource parameter locals.get?)
          unless !targets.contains pc && source == some type do
            return ← none
        let key := keyBytes (toString current.opcode) :: typeKeyInto type []
        let bucket := seen.getD key []
        unless bucket.contains type do
          seen := seen.insert key (type :: bucket)
          operands := (current.opcode, type) :: operands
    previous := some current
    pc := pc + 1
  return operands

/-- The method admits each distinct live object operand and every span copy source. -/
def ObjectOperandsValid (raw : RawMethod) (reachable : List Bool) (method : Method) : Prop :=
  let indexed := method.environment.callLayouts
  method.profile.Valid ∧ raw.code.length = reachable.length ∧
    raw.code.length = method.code.length ∧
    (objectOperands raw reachable method).any (fun operands =>
      operands.all fun (opcode, type) =>
        objectShapeAdmitted opcode (indexed.valueShape type)) = true

/-- The named operands at all live sites suffice when their method shape facts admit each pair. -/
theorem ObjectOperandsValid.of_sites {raw : RawMethod} {reachable : List Bool} {method : Method}
    (operands : List (Nat × TypeExpr))
    (sites : objectOperands raw reachable method = some operands)
    (lengths : method.profile.Valid ∧ raw.code.length = reachable.length ∧
      raw.code.length = method.code.length)
    (shapes : operands.all (fun (opcode, type) =>
      objectShapeAdmitted opcode (method.valueShape type)) = true) :
    ObjectOperandsValid raw reachable method := by
  refine ⟨lengths.1, lengths.2.1, lengths.2.2, ?_⟩
  rw [sites]
  simpa only [Option.any, CallLayouts.valueShape_eq, Method.valueShape] using shapes
#print axioms ObjectOperandsValid.of_sites

instance (raw : RawMethod) (reachable : List Bool) (method : Method) :
    Decidable (ObjectOperandsValid raw reachable method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end CIL.Extraction
