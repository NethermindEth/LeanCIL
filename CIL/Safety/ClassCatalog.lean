import CIL.Safety.ObjectFields
import CIL.Safety.HeapObjectFacts
import CIL.Extraction.Translation
import CIL.Safety.ExecutionClasses

/-!
# Class catalogs and distinct objects

Memory a caller passes may record any runtime type, so nothing in `Memory.WellFormed` stops one
allocation from claiming to be an instance of two unrelated classes, and a proof cannot tell an
`ItemPool` from a `PooledItem` by the fields it reads. The extraction knows better: each method
taking an object receiver records its class and that class's admitted bases, as metadata states
them (`declaredClasses`). `Memory.ClassesConsistent catalog memory` says every object's lineage
agrees with those chains: a cataloged class in a lineage carries its whole base chain as the
lineage's tail, which single inheritance makes true of every CLR object. Under it, an object
located as an instance of one cataloged class and an object located as an instance of an
unrelated one lie in different allocations (`ClassesConsistent.allocation_ne`).
-/

namespace CIL.Safety

/-- `scope::name` split at its first `::`, the scope read so far kept reversed in the first
    argument; structural, so the kernel evaluates it on an extraction's owners. -/
def splitScope : List Char → List Char → Option (List Char × List Char)
  | scope, ':' :: ':' :: name => some (scope.reverse, name)
  | scope, char :: rest => splitScope (char :: scope) rest
  | _, [] => none

/-- The class a method's metadata declares it on, with that class's admitted bases nearest first,
    when the method takes an object receiver and its owner spells `scope::name` with exactly one
    `::`. -/
def declaredClass (method : CIL.Extraction.RawMethod) : Option RuntimeType :=
  if method.objectReceiver then
    match splitScope [] method.owner.toList with
    | some (scope, name) => if (splitScope [] name).isSome then none else
        some ⟨.object (String.ofList scope) (String.ofList name), method.objectBases⟩
    | none => none
  else none

/-- The classes, with their base chains, that the methods of an extraction declare. -/
def declaredClasses (evidence : List CIL.Extraction.MethodEvidence) : List RuntimeType :=
  evidence.filterMap fun method => declaredClass method.original


/-- Two cataloged classes in one consistent lineage are related: one derives from the other. -/
theorem RuntimeType.ConsistentWith.related {catalog : List RuntimeType} {type : RuntimeType}
    (consistent : type.ConsistentWith catalog) {first second : RuntimeType}
    (firstKnown : first ∈ catalog) (secondKnown : second ∈ catalog)
    (firstIn : first.identity ∈ type.lineage) (secondIn : second.identity ∈ type.lineage) :
    first.identity ∈ second.lineage ∨ second.identity ∈ first.lineage := by
  rcases List.suffix_or_suffix_of_suffix (consistent first firstKnown firstIn)
      (consistent second secondKnown secondIn) with tail | tail
  · exact Or.inl (tail.subset (RuntimeType.identity_mem_lineage first))
  · exact Or.inr (tail.subset (RuntimeType.identity_mem_lineage second))
#print axioms RuntimeType.ConsistentWith.related

/-- A located field's object is a live allocation whose runtime type has the field's class in
    its lineage. -/
theorem objectFieldAddress_lineage {memory : Memory} {object field : Reference}
    {owner : CIL.Extraction.TypeExpr} {offset : Nat}
    (located : objectFieldAddress memory (.address object) owner offset = .ok field) :
    ∃ allocation type, memory.allocations object.allocation = some allocation ∧
      allocation.kind = .object type ∧ owner ∈ type.lineage := by
  simp only [objectFieldAddress, Bind.bind, Except.bind, checkedAt, Except.mapError] at located
  cases live : liveAllocation memory object.allocation with
  | error => simp only [live] at located; cases located
  | ok allocation =>
    simp only [live] at located
    have present := (liveAllocation_ok _ _ _ live).1
    cases kind : allocation.kind <;> simp only [kind] at located <;> try cases located
    rename_i type
    by_cases typed : owner ∈ type.lineage
    · exact ⟨allocation, type, present, kind, typed⟩
    · by_cases origin : object.offset = 0 <;>
        simp only [origin, typed, ne_eq, not_true_eq_false, not_false_eq_true, ite_true,
          ite_false] at located <;> cases located
#print axioms objectFieldAddress_lineage

/-- Objects located as instances of two unrelated cataloged classes lie in different
    allocations, in memory whose objects agree with the catalog. -/
theorem Memory.ClassesConsistent.allocation_ne {catalog : List RuntimeType} {memory : Memory}
    (consistent : memory.ClassesConsistent catalog) {first second : RuntimeType}
    (firstKnown : first ∈ catalog) (secondKnown : second ∈ catalog)
    (unrelated : first.identity ∉ second.lineage ∧ second.identity ∉ first.lineage)
    {left right leftField rightField : Reference} {leftOffset rightOffset : Nat}
    (leftLocated : objectFieldAddress memory (.address left) first.identity leftOffset =
      .ok leftField)
    (rightLocated : objectFieldAddress memory (.address right) second.identity rightOffset =
      .ok rightField) :
    left.allocation ≠ right.allocation := by
  intro same
  obtain ⟨allocation, type, present, kind, firstIn⟩ := objectFieldAddress_lineage leftLocated
  obtain ⟨other, otherType, otherPresent, otherKind, secondIn⟩ :=
    objectFieldAddress_lineage rightLocated
  rw [← same, present] at otherPresent
  cases otherPresent
  rw [kind] at otherKind
  cases otherKind
  rcases (consistent _ _ _ present kind).related firstKnown secondKnown firstIn secondIn with
    related | related
  · exact unrelated.1 related
  · exact unrelated.2 related
#print axioms Memory.ClassesConsistent.allocation_ne

end CIL.Safety
