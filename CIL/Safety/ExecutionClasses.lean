import CIL.Safety.ExecutionInvariants

/-!
# Runtime types agree with a class catalog throughout a run

Memory a caller passes may record any runtime type, so a proof that tells instances of two
classes apart (`CIL/Safety/ClassCatalog.lean`) needs every object's lineage to agree with the
class chains the extraction declares: `Memory.ClassesConsistent catalog memory`. The caller
establishes it once, at entry. The program keeps it when each of its `newobj` and class `newarr`
sites records a type that agrees with the catalog (`ObjectSitesConsistent`), a property of the
program text alone that `decide` checks once per extraction. Under that premise,
`step_preserves_classes` up to `invoke_preserves_classes` carry the agreement through every step,
nested call and frame exit, following `StepEffect`: no other instruction creates an instance.
-/

namespace CIL.Safety

/-- A runtime type agrees with a catalog: every cataloged class in its lineage brings that
    class's own lineage as the lineage's tail. -/
def RuntimeType.ConsistentWith (catalog : List RuntimeType) (type : RuntimeType) : Prop :=
  ∀ known ∈ catalog, known.identity ∈ type.lineage → known.lineage <:+ type.lineage

instance (catalog : List RuntimeType) (type : RuntimeType) :
    Decidable (type.ConsistentWith catalog) :=
  inferInstanceAs (Decidable (∀ known ∈ catalog, _ → _))

/-- Every object in memory has a runtime type that agrees with the catalog. Expired objects
    count too: a stale reference may still name one. -/
def Memory.ClassesConsistent (catalog : List RuntimeType) (memory : Memory) : Prop :=
  ∀ id allocation type, memory.allocations id = some allocation →
    allocation.kind = .object type → type.ConsistentWith catalog

/-- An instruction creates no instance, or creates one whose type agrees with the catalog. -/
def SiteConsistent (catalog : List RuntimeType) (operation : CIL.Op) : Prop :=
  match objectSiteType operation with
  | some type => type.ConsistentWith catalog
  | none => True

instance (catalog : List RuntimeType) (operation : CIL.Op) :
    Decidable (SiteConsistent catalog operation) := by
  unfold SiteConsistent
  split <;> infer_instance

/-- Every allocating site of `program` records a runtime type that agrees with the catalog. -/
def ObjectSitesConsistent (catalog : List RuntimeType) (program : CIL.Program) : Prop :=
  ∀ body ∈ program, ∀ operation ∈ body.code, SiteConsistent catalog operation

instance (catalog : List RuntimeType) (program : CIL.Program) :
    Decidable (ObjectSitesConsistent catalog program) :=
  inferInstanceAs (Decidable (∀ body ∈ program, ∀ operation ∈ body.code, _))

/-- A step that creates no instance keeps the catalog's agreement. -/
theorem Memory.ClassesConsistent.kept {catalog : List RuntimeType} {before after : Memory}
    (consistent : before.ClassesConsistent catalog) (kept : ObjectsKept before after) :
    after.ClassesConsistent catalog := by
  intro id allocation type present kind
  obtain ⟨earlier, found, earlierKind⟩ := kept id allocation type present kind
  exact consistent id earlier type found earlierKind

#print axioms Memory.ClassesConsistent.kept

/-- An ordinary memory instruction creates no instance. -/
theorem InstructionEffect.objectsKept {before after : Memory}
    (effect : InstructionEffect before after) : ObjectsKept before after := by
  cases effect with
  | unchanged => exact .refl _
  | write written => exact write_objectsKept written
  | snapshot written => exact writeSnapshot_objectsKept written
  | slot stored =>
    obtain ⟨-, -, rfl⟩ := storeSlot_ok stored
    exact .of_allocations rfl

/-- Resolving a static field binds its existing storage or allocates an immutable static. -/
theorem staticReference_objectsKept {descriptor : CIL.StaticDescriptor} {before after : Memory}
    {reference : Reference}
    (success : staticReference descriptor before = .ok (after, reference)) :
    ObjectsKept before after := by
  cases cached : before.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    obtain ⟨name, address⟩ := binding
    obtain ⟨rfl, _, _⟩ := cached_static_reference_checked _ _ _ _ _ _ cached success
    exact .refl _
  | none =>
    simp only [staticReference, cached] at success
    split at success
    · cases success
    cases allocated : allocate before
        ⟨.immutableStatic,
          ⟨descriptor.bytes.length, descriptor.alignment, []⟩, true, [descriptor.bytes.length]⟩ <;>
      simp only [allocated, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at success
    · cases success
    · cases success
      have kept := allocate_objectsKept (fun _ => StorageKind.noConfusion) allocated
      exact kept

/-- Static and ordinary memory instructions create no instance. -/
theorem StaticInstructionEffect.objectsKept {body : CIL.Method} {before after : Memory}
    (effect : StaticInstructionEffect body before after) : ObjectsKept before after := by
  cases effect with
  | ordinary effect => exact effect.objectsKept
  | reference _ success => exact staticReference_objectsKept success

/-- Dynamic stack storage is a frame home, not an instance. -/
theorem StackAllocationEffect.objectsKept {before after : Memory} {frame final : Frame}
    {reference : ManagedReference}
    (effect : StackAllocationEffect before frame reference final after) :
    ObjectsKept before after := by
  cases effect with
  | empty => exact .refl _
  | fresh allocated initialized =>
    rcases initialized with rfl | written
    · exact allocateHome_objectsKept allocated
    · exact (allocateHome_objectsKept allocated).trans (write_objectsKept written)

/-- An array is heap storage, not an instance. -/
theorem ArrayAllocationEffect.objectsKept {before after : Memory} {view : ArrayView}
    (effect : ArrayAllocationEffect before view after) : ObjectsKept before after := by
  cases effect with
  | fresh _ _ allocation =>
    have kept := allocate_objectsKept (fun _ => StorageKind.noConfusion) allocation
    exact kept

/-- Object creation keeps the catalog's agreement when the created type agrees with it. -/
theorem ObjectAllocationEffect.classesConsistent {catalog : List RuntimeType}
    {before after : Memory} {type : RuntimeType} {object : Reference}
    (effect : ObjectAllocationEffect before type object after)
    (agrees : type.ConsistentWith catalog) (consistent : before.ClassesConsistent catalog) :
    after.ClassesConsistent catalog := by
  intro id allocation created present kind
  rcases effect.objects present kind with rfl | ⟨earlier, found, earlierKind⟩
  · exact agrees
  · exact consistent id earlier created found earlierKind

/-- Every checked dispatcher effect keeps the catalog's agreement when the executed instruction's
    object site does. -/
theorem StepEffect.classesConsistent {catalog : List RuntimeType} {body : CIL.Method}
    {operation : CIL.Op} {frame final : Frame} {before after : Memory}
    (effect : StepEffect body operation frame before final after)
    (site : SiteConsistent catalog operation) (consistent : before.ClassesConsistent catalog) :
    after.ClassesConsistent catalog := by
  cases effect with
  | arrayAllocation effect => exact consistent.kept effect.objectsKept
  | objectAllocation effect created =>
    unfold SiteConsistent at site
    rw [created] at site
    exact effect.classesConsistent site consistent
  | stackAllocation effect => exact consistent.kept effect.objectsKept
  | memory effect => exact consistent.kept effect.objectsKept
  | store _ stored => exact consistent.kept (storeLocal_objectsKept stored)
  | valueHome allocated stored =>
    exact consistent.kept ((allocateHome_objectsKept allocated).trans
      (storeValue_effect _ _ _ _ stored).objectsKept)
  | localHome allocated stored =>
    exact consistent.kept ((allocateHome_objectsKept allocated).trans
      (storeLocal_objectsKept stored))

#print axioms StepEffect.classesConsistent

theorem step_preserves_classes {catalog : List RuntimeType} (body : CIL.Method)
    (operation : CIL.Op) (pc : Nat) (args : List Value) (frame : Frame) (stack : List Value)
    (m : Memory) (action : FrameAction) (site : SiteConsistent catalog operation)
    (consistent : m.ClassesConsistent catalog)
    (h : step body operation pc args frame stack m = .ok action) :
    action.memory.ClassesConsistent catalog :=
  (step_effect _ _ _ _ _ _ _ _ h).classesConsistent site consistent

#print axioms step_preserves_classes

theorem programStep_preserves_classes {catalog : List RuntimeType} {program : CIL.Program}
    {method pc : Nat} {args : List Value} {frame : Frame} {stack : List Value} {m : Memory}
    {action : FrameAction} (sites : ObjectSitesConsistent catalog program)
    (consistent : m.ClassesConsistent catalog)
    (hs : ProgramStep program method pc args frame stack m action) :
    action.memory.ClassesConsistent catalog := by
  obtain ⟨body, operation, found, fetched, stepped⟩ := hs
  exact step_preserves_classes _ _ _ _ _ _ _ _
    (sites body (List.mem_of_getElem? found) operation (List.mem_of_getElem? fetched))
    consistent stepped

/-- A frame exit only expires storage, so it keeps the catalog's agreement. -/
theorem leaveFrame_preserves_classes {catalog : List RuntimeType} (frame : Frame) {m : Memory}
    (consistent : m.ClassesConsistent catalog) :
    (leaveFrame frame m).ClassesConsistent catalog :=
  consistent.kept (expireAll_objectsKept frame.owned m)

/-- A successful run of a program whose object sites agree with the catalog, including every
    nested call and frame exit, keeps agreement from its starting memory. -/
theorem run_preserves_classes {catalog : List RuntimeType} {program : CIL.Program}
    {fuel method pc : Nat} {args : List Value} {frame : Frame} {stack : List Value}
    {m final : Memory} {values : List Value} (sites : ObjectSitesConsistent catalog program)
    (consistent : m.ClassesConsistent catalog)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    final.ClassesConsistent catalog := by
  have trace := run_success_trace program fuel method pc args frame stack m final values h
  clear h
  induction trace with
  | next step _ ih => exact ih (programStep_preserves_classes sites consistent step)
  | returned step _ =>
    exact leaveFrame_preserves_classes _ (programStep_preserves_classes sites consistent step)
  | tailCall step _ _ _ _ enter _ _ ih =>
    exact ih ((leaveFrame_preserves_classes _
      (programStep_preserves_classes sites consistent step)).kept (enterFrame_objectsKept enter))
  | call step _ enter _ _ _ childIH ih
  | construct step _ enter _ _ _ _ childIH ih =>
    exact ih (childIH ((programStep_preserves_classes sites consistent step).kept
      (enterFrame_objectsKept enter)))

#print axioms run_preserves_classes

/-- A successful invocation of a program whose object sites agree with the catalog keeps the
    agreement the caller established. -/
theorem invoke_preserves_classes {catalog : List RuntimeType} {program : CIL.Program}
    {fuel method : Nat} {args values : List Value} {m final : Memory}
    (sites : ObjectSitesConsistent catalog program) (consistent : m.ClassesConsistent catalog)
    (h : invoke program fuel method args m = .ok (final, values)) :
    final.ClassesConsistent catalog := by
  obtain ⟨_, _, _, _, _, _, setup, executed⟩ := invoke_success_setup h
  exact run_preserves_classes sites (consistent.kept (enterFrame_objectsKept setup)) executed

#print axioms invoke_preserves_classes

end CIL.Safety
