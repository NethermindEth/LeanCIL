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

/-- The live opcode and type pairs in instruction order, after checking span copies and resets. -/
def objectSites (raw : RawMethod) (reachable : List Bool) (method : Method) :
    Option (List (Nat × TypeExpr)) := do
  let targets := Std.TreeSet.ofList (branchTargets raw.code) compare
  let parameters := FlowIndex.ofList raw.parameters
  let locals := FlowIndex.ofList raw.locals
  let parameter := fun index => if raw.hasThis && index == 0 then none else
    parameters.get? (index - raw.hasThis.toNat)
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
        operands := (current.opcode, type) :: operands
    previous := some current
    pc := pc + 1
  return operands.reverse

/-- Collect first occurrences in reverse order, checking full types within a bucket. -/
private def distinctOperands (seen : Std.TreeMap (List (List UInt8)) (List TypeExpr) compare) :
    List (Nat × TypeExpr) → List (Nat × TypeExpr) → List (Nat × TypeExpr)
  | kept, [] => kept
  | kept, (opcode, type) :: rest =>
    let key := keyBytes (toString opcode) :: typeKeyInto type []
    let bucket := seen.getD key []
    if bucket.contains type then distinctOperands seen kept rest
    else distinctOperands (seen.insert key (type :: bucket)) ((opcode, type) :: kept) rest

/-- Every selected operand was already collected or occurs among the remaining live sites. -/
private theorem distinctOperands_mem (seen kept sites) {pair : Nat × TypeExpr}
    (member : pair ∈ distinctOperands seen kept sites) : pair ∈ kept ∨ pair ∈ sites := by
  induction sites generalizing seen kept with
  | nil => exact Or.inl member
  | cons site rest ih =>
    obtain ⟨opcode, type⟩ := site
    simp only [distinctOperands] at member
    split at member
    · exact (ih _ _ member).imp_right (List.mem_cons_of_mem _)
    · rcases ih _ _ member with earlier | later
      · rcases List.mem_cons.mp earlier with rfl | kept
        · exact Or.inr (.head _)
        · exact Or.inl kept
      · exact Or.inr (.tail _ later)
#print axioms distinctOperands_mem

/-- The distinct live pairs in reverse order of first occurrence. -/
def objectOperands (raw : RawMethod) (reachable : List Bool) (method : Method) :
    Option (List (Nat × TypeExpr)) :=
  (objectSites raw reachable method).map (distinctOperands ∅ [])

/-- The method admits each distinct live object operand and every span copy source. -/
def ObjectOperandsValid (raw : RawMethod) (reachable : List Bool) (method : Method) : Prop :=
  let indexed := method.environment.callLayouts
  method.profile.Valid ∧ raw.code.length = reachable.length ∧
    raw.code.length = method.code.length ∧
    (objectOperands raw reachable method).any (fun operands =>
      operands.all fun (opcode, type) =>
        objectShapeAdmitted opcode (indexed.valueShape type)) = true

/-- A live object instruction and the checked shape of its named type operand. -/
structure ObjectSiteShape (method : Method) where
  opcode : Nat
  type : TypeExpr
  shape : ValueShape
  resolved : method.valueShape type = shape

/-- Shape facts for the live instruction sequence suffice for all its distinct operands. -/
theorem ObjectOperandsValid.of_sites {raw : RawMethod} {reachable : List Bool} {method : Method}
    (operands : List (ObjectSiteShape method))
    (sites : objectSites raw reachable method = some (operands.map fun s => (s.opcode, s.type)))
    (lengths : method.profile.Valid ∧ raw.code.length = reachable.length ∧
      raw.code.length = method.code.length)
    (shapes : operands.all (fun s => objectShapeAdmitted s.opcode s.shape) = true) :
    ObjectOperandsValid raw reachable method := by
  refine ⟨lengths.1, lengths.2.1, lengths.2.2, ?_⟩
  simp only [objectOperands, sites, Option.map_some, Option.any_some, List.all_eq_true]
  intro pair member
  have live := (distinctOperands_mem _ _ _ member).resolve_left List.not_mem_nil
  obtain ⟨site, atSite, rfl⟩ := List.mem_map.mp live
  rw [CallLayouts.valueShape_eq]
  simpa only [← site.resolved, Method.valueShape] using List.all_eq_true.mp shapes site atSite
#print axioms ObjectOperandsValid.of_sites

instance (raw : RawMethod) (reachable : List Bool) (method : Method) :
    Decidable (ObjectOperandsValid raw reachable method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end CIL.Extraction
