import CIL.Safety.Execution

namespace CIL.Extraction

/-- Initializers run from this memory: no allocations, views or loaded fields. -/
def initializerMemory : Safety.Memory where
  allocations := fun _ => none
  cells := fun _ _ => ⟨0, false⟩
  views := []
  nextIdentity := 0

/-- Initializers are generous bounded runs; exhausting this fuel fails the certificate. -/
def initializerFuel : Nat := 65536

/-- Constructor-fixed sites removed, so no initializer can read a value it justifies. -/
def withoutStaticValues (program : Program) : Program :=
  program.map fun body => { body with staticSites := body.staticSites.filter (·.2.initializer.isNone) }

/-- The initializer call returns exactly the descriptor's bytes; RVA descriptors have none. -/
def initializerYields (program : Program) (descriptor : StaticDescriptor) : Bool :=
  match descriptor.initializer with
  | none => true
  | some init =>
    match Safety.invoke (withoutStaticValues program) initializerFuel init.method
        (init.arguments.map .scalar) initializerMemory with
    | .ok (_, [.scalar (.aggregate bytes)]) => bytes == descriptor.bytes
    | _ => false

/-- Every constructor-fixed static value in the program is the result of its initializer. -/
def StaticValuesValid (program : Program) : Prop :=
  (program.flatMap fun body => body.staticSites.map Prod.snd).all (initializerYields program) = true

instance (program : Program) : Decidable (StaticValuesValid program) :=
  inferInstanceAs (Decidable (_ = _))

end CIL.Extraction
