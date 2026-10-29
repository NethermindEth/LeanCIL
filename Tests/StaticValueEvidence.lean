import CIL.Extraction.Translation

/-! Checks static readonly values against literal, method and constructor evidence. -/

namespace Tests.StaticValueEvidence
open CIL CIL.Extraction

private def zeros : List (BitVec 8) := [0, 0]

/-- Returns its zero-initialized two-byte aggregate local. -/
private def initializer : Method := {
  code := [.local 0, .ret none], locals := [.aggregate zeros], localKinds := [.aggregate 2], returnsValue := true }

private def descriptor (bytes : List (BitVec 8)) (init : Option StaticInitializer) : StaticDescriptor :=
  { identity := 0, fieldName := "Fixture::Zero", bytes, initializer := init }

private def loader (op bytes : List (BitVec 8)) (init : Option StaticInitializer) : Method :=
  { code := [.memory (.staticValue op), .ret none], locals := [], returnsValue := true,
    staticSites := [(0, descriptor bytes init)] }

private def load (op bytes : List (BitVec 8))
    (init : Option StaticInitializer := some ⟨1, [], none, false⟩) : Program :=
  [loader op bytes init, initializer]

private def run (program : Program) := (Safety.invoke program 8 0 [] initializerMemory).map Prod.snd

-- A load pushes the descriptor's bytes and leaves memory unchanged.
example : run (load zeros zeros) = .ok [.scalar (.aggregate zeros)] := rfl
example : Safety.staticInstruction (loader zeros zeros (some ⟨1, [], none, false⟩)) 0 (.staticValue zeros) [] initializerMemory =
    .ok (initializerMemory, [.scalar (.aggregate zeros)]) := rfl

-- The certificate reruns the initializer: matching bytes pass, forged bytes fail.
example : StaticValuesValid (load zeros zeros) := by decide +kernel
example : ¬ StaticValuesValid (load [1, 0] [1, 0]) := by decide +kernel
-- An initializer that is not in the program, or returns no value, is rejected too.
example : ¬ StaticValuesValid (load zeros zeros (some ⟨5, [], none, false⟩)) := by decide +kernel
example : ¬ StaticValuesValid (load zeros zeros (some ⟨0, [], none, false⟩)) := by decide +kernel

-- The emitted bytes must equal the descriptor's, and the descriptor must name an initializer.
example : run (load [1, 0] zeros) = .error ⟨0, 0, .invalidState⟩ := rfl
example : run (load zeros zeros none) = .error ⟨0, 0, .invalidState⟩ := rfl
-- RVA descriptors without an initializer impose nothing on the certificate.
example : StaticValuesValid (load zeros [7] none) := by decide +kernel

/-- A constructor writes through the ordinary checked aggregate temporary. -/
private def constructor : Method := {
  code := [.arg 0, .const32 7, .storeScalar 1, .ret none]
  locals := [], returnsValue := false }

private def constructed (bytes : List (BitVec 8)) (callee : Method := constructor) : Program :=
  [loader bytes bytes (some { method := 1, arguments := [], construct := true }), callee]

/-- Construction starts with initialized zero bytes and preserves untouched bytes. -/
theorem constructor_bytes : StaticValuesValid (constructed [7, 0]) := by decide +kernel
#print axioms constructor_bytes

/-- Changing the emitted constructor result does not change what checked execution produces. -/
theorem forged_constructor_bytes : ¬ StaticValuesValid (constructed [8, 0]) := by decide +kernel
#print axioms forged_constructor_bytes

/-- A constructor must return void, even if its returned aggregate matches the descriptor. -/
theorem returning_constructor : ¬ StaticValuesValid (constructed zeros initializer) := by
  decide +kernel
#print axioms returning_constructor

end Tests.StaticValueEvidence
