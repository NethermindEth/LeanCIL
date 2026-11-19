import CIL.Extraction.ValueDecoding
import CIL.Extraction.Scalars
import CIL.Extraction.CallLayouts

/-!
# Object operand admission

Live object instructions use the storage shape of their closed type operand. A span load or reset
requires a direct address of the same view, and a span constructor call requires the address of
its constructed type before its argument pushes.
-/

namespace CIL.Extraction

/-- The storage shapes that an object opcode admits. -/
def objectShapeAdmitted (opcode : Nat) (type : TypeExpr) (shape : ValueShape) : Bool :=
  objectApplicationAdmitted type && match shape with
  | .span => opcode == 0x71
  | .unsupported _ => false
  | _ => objectOpcode opcode

/-- The declared type of the local or parameter whose home `instruction` addresses. -/
private def addressedType (parameter localAt : Nat → Option TypeExpr)
    (instruction : RawInstruction) : Option TypeExpr :=
  match argumentOperation instruction with
  | some (.address index) => parameter index
  | _ => if instruction.opcode ∉ [18, 65037] then none else (encodedLocal instruction).bind localAt

/-- The type of the span home loaded or addressed immediately before a span copy. -/
private def spanCopySource (parameter localAt : Nat → Option TypeExpr)
    (previous : RawInstruction) : Option TypeExpr := do
  match argumentOperation previous with
  | some (.load index) =>
    let .byref type ← parameter index | none
    return type
  | _ => addressedType parameter localAt previous

/-- Raw pushes of one value that read no memory: argument and local loads, `ldnull` and int32
    constants. -/
private def purePush (opcode : Nat) : Bool :=
  opcode ∈ [2, 3, 4, 5, 14, 65033, 6, 7, 8, 9, 17, 65036,
    20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]

/-- A span constructor call at `pc` runs on the home its raw window names: one pure push per
    parameter, at most three, after the address of a local or parameter of the constructed type,
    and no branch target after that address. `recent` holds the raw instructions before the
    call, nearest first. -/
private def spanConstructorWindow (parameter localAt : Nat → Option TypeExpr)
    (targeted : Nat → Bool) (pc : Nat) (recent : List RawInstruction) (site : CallSite) : Bool :=
  let count := site.parameterCount
  let pushes := recent.take count
  count ≤ 3 && pushes.length == count && pushes.all (purePush ·.opcode) &&
    (recent[count]?).bind (addressedType parameter localAt) == some site.declaringType &&
    (List.range (count + 1)).all fun offset => !targeted (pc - offset)

/-- The live opcode and type pairs in instruction order, after checking span copies, resets and
    constructor calls. -/
def objectSites (raw : RawMethod) (reachable : List Bool) (method : Method) :
    Option (List (Nat × TypeExpr)) := do
  let targets := Std.TreeSet.ofList (branchTargets raw.code) compare
  let parameters := FlowIndex.ofList raw.parameters
  let locals := FlowIndex.ofList raw.locals
  let parameter := fun index => if raw.hasThis && index == 0 then none else
    parameters.get? (index - raw.hasThis.toNat)
  let mut operands := []
  let mut previous := none
  let mut recent := []
  let mut pc := 0
  for (current, live, _) in raw.code.zip (reachable.zip method.code) do
    if live && current.opcode == 40 then
      if let .call site := current.operand then
        if site.name == ".ctor" && spanLocal site.declaringType then
          unless spanConstructorWindow parameter locals.get? targets.contains pc recent site do
            return ← none
    if live && objectOpcode current.opcode then
      let .type type := current.operand | return ← none
      if current.opcode == 0xfe15 && spanLocal type then
        unless !targets.contains pc &&
            previous.bind (addressedType parameter locals.get?) == some type do
          return ← none
      else
        if current.opcode == 0x71 && spanLocal type then
          let source := previous.bind (spanCopySource parameter locals.get?)
          unless !targets.contains pc && source == some type do
            return ← none
        operands := (current.opcode, type) :: operands
    previous := some current
    recent := (current :: recent).take 4
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
        objectShapeAdmitted opcode type (indexed.valueShape type)) = true

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
    (shapes : operands.all (fun s => objectShapeAdmitted s.opcode s.type s.shape) = true) :
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
