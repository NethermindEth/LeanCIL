import CIL.Safety.ExecutionStaticWorld

namespace CIL.Safety

abbrev StaticWorldPreserved (program : CIL.Program) (before after : Memory) : Prop :=
  StaticWorldValid (programStaticDescriptors program) before →
    StaticWorldValid (programStaticDescriptors program) after

theorem StaticWorldPreserved.refl (program : CIL.Program) (memory : Memory) :
    StaticWorldPreserved program memory memory :=
  fun world => world

theorem StaticWorldPreserved.trans {program : CIL.Program} {first middle last : Memory}
    (left : StaticWorldPreserved program first middle) (right : StaticWorldPreserved program middle last) :
    StaticWorldPreserved program first last :=
  fun world => right (left world)

abbrev FrameInvariants (program : CIL.Program) (before after : Memory) : Prop :=
  after.WellFormed ∧ StaticWorldPreserved program before after

theorem FrameInvariants.formed {program : CIL.Program} {before after : Memory}
    (kept : FrameInvariants program before after) : after.WellFormed :=
  kept.1

theorem FrameInvariants.staticWorld {program : CIL.Program} {before after : Memory}
    (kept : FrameInvariants program before after) : StaticWorldPreserved program before after :=
  kept.2

theorem FrameInvariants.refl (program : CIL.Program) {memory : Memory} (formed : memory.WellFormed) :
    FrameInvariants program memory memory :=
  ⟨formed, StaticWorldPreserved.refl program memory⟩

theorem FrameInvariants.trans {program : CIL.Program} {first middle last : Memory}
    (left : FrameInvariants program first middle) (right : FrameInvariants program middle last) :
    FrameInvariants program first last :=
  ⟨right.formed, left.staticWorld.trans right.staticWorld⟩

end CIL.Safety
