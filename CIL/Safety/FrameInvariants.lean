import CIL.Safety.ExecutionStaticWorld
import CIL.Safety.ExecutionClasses

/-!
# Frame invariants

The memory invariants every successful call or construction keeps, whatever the callee's
contract states: the result memory is well formed, a valid static world stays valid, and objects
that agree with a class catalog keep agreeing when the program's object sites do. All three are
reflexive and transitive, so the invariants of consecutive steps compose.
-/

namespace CIL.Safety

/-- If the static fields of `program` are valid in `before`, they are valid in `after`. -/
abbrev StaticWorldPreserved (program : CIL.Program) (before after : Memory) : Prop :=
  StaticWorldValid (programStaticDescriptors program) before →
    StaticWorldValid (programStaticDescriptors program) after

theorem StaticWorldPreserved.refl (program : CIL.Program) (memory : Memory) :
    StaticWorldPreserved program memory memory :=
  fun world => world

theorem StaticWorldPreserved.trans {program : CIL.Program} {first middle last : Memory}
    (left : StaticWorldPreserved program first middle)
    (right : StaticWorldPreserved program middle last) :
    StaticWorldPreserved program first last :=
  fun world => right (left world)

/-- For every catalog the object sites of `program` agree with, if the objects of `before` agree
    with it, so do the objects of `after`. -/
abbrev ClassesPreserved (program : CIL.Program) (before after : Memory) : Prop :=
  ∀ catalog, ObjectSitesConsistent catalog program →
    before.ClassesConsistent catalog → after.ClassesConsistent catalog

theorem ClassesPreserved.refl (program : CIL.Program) (memory : Memory) :
    ClassesPreserved program memory memory :=
  fun _ _ consistent => consistent

theorem ClassesPreserved.trans {program : CIL.Program} {first middle last : Memory}
    (left : ClassesPreserved program first middle)
    (right : ClassesPreserved program middle last) :
    ClassesPreserved program first last :=
  fun catalog sites consistent => right catalog sites (left catalog sites consistent)

/-- `after` is well formed, preserves the static world of `before` and keeps its objects'
    agreement with any catalog the program's object sites agree with. -/
abbrev FrameInvariants (program : CIL.Program) (before after : Memory) : Prop :=
  after.WellFormed ∧ StaticWorldPreserved program before after ∧
    ClassesPreserved program before after

theorem FrameInvariants.formed {program : CIL.Program} {before after : Memory}
    (kept : FrameInvariants program before after) : after.WellFormed :=
  kept.1

theorem FrameInvariants.staticWorld {program : CIL.Program} {before after : Memory}
    (kept : FrameInvariants program before after) : StaticWorldPreserved program before after :=
  kept.2.1

theorem FrameInvariants.classes {program : CIL.Program} {before after : Memory}
    (kept : FrameInvariants program before after) : ClassesPreserved program before after :=
  kept.2.2

theorem FrameInvariants.refl (program : CIL.Program) {memory : Memory}
    (formed : memory.WellFormed) :
    FrameInvariants program memory memory :=
  ⟨formed, StaticWorldPreserved.refl program memory, ClassesPreserved.refl program memory⟩

theorem FrameInvariants.trans {program : CIL.Program} {first middle last : Memory}
    (left : FrameInvariants program first middle) (right : FrameInvariants program middle last) :
    FrameInvariants program first last :=
  ⟨right.formed, left.staticWorld.trans right.staticWorld, left.classes.trans right.classes⟩

end CIL.Safety
