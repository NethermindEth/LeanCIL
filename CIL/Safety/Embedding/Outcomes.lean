import CIL.Safety.Embedding.Simulation
import CIL.Safety.OutcomeContract

/-!
Outcome contracts transfer along a program embedding: a named exception is raised by
the actual program exactly as by the expected one, and a normal return keeps its
result, memory and footprint. Fault locations are not part of `Raises`.
-/

namespace CIL.Safety

open CIL.Embedding

theorem Raises.of_refines {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) {method : Nat} {args : List Value} {memory : Memory}
    {exception : String} (raised : Raises expected method args memory exception) :
    Raises actual method args memory exception := by
  obtain ⟨fuel, fault, invoked, thrown⟩ := raised
  exact ⟨fuel, _, invoke_raise_refines refines invoked thrown, thrown⟩

theorem RunRaises.of_refines {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) {method pc : Nat} {args : List Value} {frame : Frame}
    {stack : List Value} {memory : Memory} {exception : String}
    (raised : RunRaises expected method pc args frame stack memory exception) :
    RunRaises actual method (maps method pc) args frame stack memory exception := by
  obtain ⟨fuel, fault, ran, thrown⟩ := raised
  exact ⟨fuel, _, run_raise_refines refines ran thrown, thrown⟩

/-- Both outcomes of a contract transfer: `Raises` by the thrown simulation, normal return by `invoke_refines`. -/
theorem OutcomeContract.Holds.of_refines {Input Output : Type} {c : OutcomeContract Input Output}
    {expected actual : CIL.Program} {maps : Nat → Nat → Nat} (refines : ProgramRefines expected actual maps)
    {method : Nat} (holds : c.Holds expected method) : c.Holds actual method := by
  intro input initial permitted
  have outcome := holds input initial permitted
  split
  · rename_i raised
    rw [raised] at outcome
    exact Raises.of_refines refines outcome
  · rename_i raised
    rw [raised] at outcome
    obtain ⟨fuel, final, values, invoked, confined, returns⟩ := outcome
    exact ⟨fuel, final, values, invoke_refines refines invoked, confined, returns⟩

/-- Normal-return contracts transfer by `invoke_refines`; they say nothing about throws. -/
theorem MethodContract.Holds.of_refines {Input Output : Type} {c : MethodContract Input Output}
    {expected actual : CIL.Program} {maps : Nat → Nat → Nat} (refines : ProgramRefines expected actual maps)
    {method : Nat} (holds : c.Holds expected method) : c.Holds actual method := by
  intro input initial permitted
  obtain ⟨fuel, final, values, invoked, confined, returns⟩ := holds input initial permitted
  exact ⟨fuel, final, values, invoke_refines refines invoked, confined, returns⟩

/-- A method contract proved with `expected` in place of method `index` holds for `program`. -/
theorem _root_.CIL.MethodEmbeds.method_holds {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {index : Nat} {expected : CIL.Method} (embeds : MethodEmbeds program index expected)
    {method : Nat} (holds : c.Holds (program.set index expected) method) : c.Holds program method := by
  obtain ⟨_, refines⟩ := embeds.refines
  exact holds.of_refines refines

#print axioms MethodContract.Holds.of_refines
#print axioms CIL.MethodEmbeds.method_holds

theorem _root_.CIL.MethodEmbeds.raises {program : CIL.Program} {index : Nat} {expected : CIL.Method}
    (embeds : MethodEmbeds program index expected) {method : Nat} {args : List Value} {memory : Memory}
    {exception : String} (raised : Raises (program.set index expected) method args memory exception) :
    Raises program method args memory exception := by
  obtain ⟨_, refines⟩ := embeds.refines
  exact raised.of_refines refines

/-- An outcome contract proved with `expected` in place of method `index` holds for `program`. -/
theorem _root_.CIL.MethodEmbeds.holds {Input Output : Type} {c : OutcomeContract Input Output}
    {program : CIL.Program} {index : Nat} {expected : CIL.Method} (embeds : MethodEmbeds program index expected)
    {method : Nat} (holds : c.Holds (program.set index expected) method) : c.Holds program method := by
  obtain ⟨_, refines⟩ := embeds.refines
  exact holds.of_refines refines

end CIL.Safety
