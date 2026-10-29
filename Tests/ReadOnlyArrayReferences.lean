import CIL.Safety.Execution
import CIL.Extraction.Translation

/-! # Readonly element references retain their restriction through frames and certificates -/

namespace Tests.ReadOnlyArrayReferences
open CIL.Safety

private def memory : Memory := {
  allocations := fun identity => if identity == 0 then
    some ⟨.managedHeap, ⟨8, 4, []⟩, true, [8]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 8, true, true⟩]
  nextIdentity := 1 }

/-- The prefix restricts the returned reference even with writable backing storage. -/
theorem restricted_address :
    memoryInstruction (.arrayAddress .signed32 false)
      [.scalar (.i32 1), .array ⟨.address ⟨0, 0⟩, 2, .signed32⟩] memory =
      .ok (memory, [.readOnlyReference (.address ⟨0, 4⟩)]) := rfl
#print axioms restricted_address

/-- A byref local preserves its readonly tag when reloaded. -/
theorem local_preserves_restriction :
    (do let (slot, stored) ← storeLocal memory (.root none)
          (.readOnlyReference (.address ⟨0, 4⟩))
        loadLocal stored slot) = .ok (.readOnlyReference (.address ⟨0, 4⟩)) := rfl
#print axioms local_preserves_restriction

/-- Stores through restricted references fail despite the backing allocation's write authority. -/
theorem restricted_store_rejected :
    instruction (.storeScalar 4)
      [.scalar (.i32 7), .readOnlyReference (.address ⟨0, 4⟩)] memory =
      .error (.memory .unwritable (.address ⟨0, 4⟩) 4) := rfl
#print axioms restricted_store_rejected

/-- Restricted references still permit initialized scalar reads. -/
theorem restricted_load :
    instruction (.loadScalar 4 false) [.readOnlyReference (.address ⟨0, 4⟩)] memory =
      .ok (memory, [.scalar (.i32 0)]) := rfl
#print axioms restricted_load

/-- Readonly views observe writes through other authorized aliases; they do not promise immutability. -/
theorem alias_update_visible :
    (do let stored ← checkedAt (.address ⟨0, 4⟩) 4
          (write memory ⟨0, 4⟩ (numberBytes 7 4) 1)
        let (_, values) ← instruction (.loadScalar 4 false)
          [.readOnlyReference (.address ⟨0, 4⟩)] stored
        pure values) = (Except.ok [.scalar (.i32 7)] : ExecutionResult (List Value)) := rfl
#print axioms alias_update_visible

/-- An unsafe reference adapter cannot silently remove the restriction. -/
theorem asRef_cannot_strip_restriction :
    memoryInstruction .asRef [.readOnlyReference (.address ⟨0, 4⟩)] memory =
      .error .invalidState := rfl
#print axioms asRef_cannot_strip_restriction

private def intType : CIL.Extraction.TypeExpr := .atom CIL.Extraction.runtimeScope "System.Int32"
private def raw (target : Nat) : CIL.Extraction.RawMethod := {
  token := 1, owner := "Readonly", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .byref intType, parameters := [.array intType, intType],
  locals := [], initLocals := true, maxStack := 2, genericParameters := [],
  code := [⟨0, 2, .none⟩, ⟨1, 3, .none⟩, ⟨2, 65054, .none⟩,
    ⟨4, 143, .type intType⟩, ⟨9, 42, .none⟩, ⟨10, 43, .target target⟩] }
private def features : CIL.Extraction.FeatureCertificate :=
  [some ⟨[], []⟩, some ⟨[none], []⟩, some ⟨[none, none], []⟩,
    some ⟨[none, none], []⟩, some ⟨[none], []⟩, none]
private def states : CIL.Extraction.ScalarCertificate :=
  [some [], some [.array .signed32], some [.word32, .array .signed32],
    some [.word32, .array .signed32], some [.reference], none]
private def code (writable : Bool) : List CIL.Op :=
  [.arg 0, .arg 1, .nop, .memory (.arrayAddress .signed32 writable), .ret,
    .unsupported "unreachable"]

/-- A branch to the prefix itself does not bypass the restriction. -/
theorem prefix_certificate : CIL.Extraction.ScalarFlowValid #[] (raw 2) features states (code false) :=
  by decide +kernel
#print axioms prefix_certificate

/-- Independently forging a writable address under the same readonly raw CIL fails. -/
theorem writable_forgery_rejected :
    ¬ CIL.Extraction.ScalarFlowValid #[] (raw 2) features states (code true) := by decide +kernel
#print axioms writable_forgery_rejected

/-- Changing only the branch target to skip the prefix is rejected, even for a dead branch. -/
theorem branch_into_address_rejected :
    ¬ CIL.Extraction.ScalarFlowValid #[] (raw 3) features states (code false) := by decide +kernel
#print axioms branch_into_address_rejected

end Tests.ReadOnlyArrayReferences
