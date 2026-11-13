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

/-- A readonly view's `GetReference` keeps the restriction instead of granting a `ref T`. -/
theorem view_reference_restricted :
    memoryInstruction .spanReference [.bufferSpan ⟨.address ⟨0, 4⟩, 1, 4, false⟩] memory =
      .ok (memory, [.readOnlyReference (.address ⟨0, 4⟩)]) := rfl
#print axioms view_reference_restricted

/-- An empty readonly view still yields its own reference once its extent validates. -/
theorem empty_view_reference :
    memoryInstruction .spanReference [.bufferSpan ⟨.address ⟨0, 8⟩, 0, 4, false⟩] memory =
      .ok (memory, [.readOnlyReference (.address ⟨0, 8⟩)]) := rfl
#print axioms empty_view_reference

/-- A readonly view whose extent leaves the allocation forms no reference. -/
theorem view_reference_outside :
    memoryInstruction .spanReference [.bufferSpan ⟨.address ⟨0, 4⟩, 2, 4, false⟩] memory =
      .error (.memory .outsideAllocation (.address ⟨0, 4⟩) 0) := rfl
#print axioms view_reference_outside

/-- Field loads and field addresses through a restricted reference stay readable and restricted. -/
theorem restricted_field_reads :
    instruction (.fieldAt 4 4 false) [.readOnlyReference (.address ⟨0, 0⟩)] memory =
      .ok (memory, [.scalar (.i32 0)]) ∧
    instruction (.fieldAddress 4) [.readOnlyReference (.address ⟨0, 0⟩)] memory =
      .ok (memory, [.readOnlyReference (.address ⟨0, 4⟩)]) ∧
    instruction (.aggregateFieldAt 4 4) [.readOnlyReference (.address ⟨0, 0⟩)] memory =
      .ok (memory, [.scalar (.aggregate [0, 0, 0, 0])]) := ⟨rfl, rfl, rfl⟩
#print axioms restricted_field_reads

/-- Field stores through a restricted reference fail, naming the struct reference and field
    width, despite the backing allocation's write authority. -/
theorem restricted_field_stores_rejected :
    instruction (.setFieldAt 4 4) [.scalar (.i32 7), .readOnlyReference (.address ⟨0, 0⟩)]
      memory = .error (.memory .unwritable (.address ⟨0, 0⟩) 4) ∧
    instruction (.setAggregateFieldAt 4 4)
      [.scalar (.aggregate [7, 0, 0, 0]), .readOnlyReference (.address ⟨0, 0⟩)] memory =
      .error (.memory .unwritable (.address ⟨0, 0⟩) 4) := ⟨rfl, rfl⟩
#print axioms restricted_field_stores_rejected

/-- A readonly field access through null faults before any field offset is formed. -/
theorem restricted_null_field :
    instruction (.fieldAt 4 4 false) [.readOnlyReference .null] memory =
      .error (.memory .nullDereference .null 0) ∧
    instruction (.fieldAddress 4) [.readOnlyReference .null] memory =
      .error (.memory .nullDereference .null 0) := ⟨rfl, rfl⟩
#print axioms restricted_null_field

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
private def code (writable : Bool) : List CIL.Instruction :=
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

/-- The readonly rule as `ScalarFlowValid` evaluates it, over a body's indexed instructions and
    collected branch destinations. -/
private def readOnlyAt (body : CIL.Extraction.RawMethod) :=
  CIL.Extraction.readOnlySiteWindow (CIL.Extraction.FlowIndex.ofList body.code).get?
    (Std.TreeSet.ofList (CIL.Extraction.branchTargets body.code) compare).contains

/-- The accepted certificate passes the readonly rule at its prefix and its element address. -/
theorem prefix_sites_accepted :
    readOnlyAt (raw 2) 2 ⟨2, 65054, .none⟩ .nop = true ∧
    readOnlyAt (raw 2) 3 ⟨4, 143, .type intType⟩ (.memory (.arrayAddress .signed32 false)) =
      true := by decide +kernel
#print axioms prefix_sites_accepted

/-- A writable address under the prefix fails the readonly rule at the address itself. -/
theorem writable_address_site_rejected :
    readOnlyAt (raw 2) 3 ⟨4, 143, .type intType⟩ (.memory (.arrayAddress .signed32 true)) =
      false := by decide +kernel
#print axioms writable_address_site_rejected

/-- The accepted body with only its prefix given an operand. -/
private def operandRaw : CIL.Extraction.RawMethod :=
  { raw 2 with code := (raw 2).code.set 2 ⟨2, 65054, .integer 0⟩ }

/-- A prefix that carries an operand fails the readonly rule at the prefix while its address
    still passes, and the certificate is rejected. -/
theorem prefix_operand_rejected :
    readOnlyAt operandRaw 2 ⟨2, 65054, .integer 0⟩ .nop = false ∧
    readOnlyAt operandRaw 3 ⟨4, 143, .type intType⟩ (.memory (.arrayAddress .signed32 false)) =
      true ∧
    ¬ CIL.Extraction.ScalarFlowValid #[] operandRaw features states (code false) := by
  decide +kernel
#print axioms prefix_operand_rejected

/-- A branch to the element address fails the readonly rule at both the prefix and the address. -/
theorem entered_sites_rejected :
    readOnlyAt (raw 3) 2 ⟨2, 65054, .none⟩ .nop = false ∧
    readOnlyAt (raw 3) 3 ⟨4, 143, .type intType⟩ (.memory (.arrayAddress .signed32 false)) =
      false := by decide +kernel
#print axioms entered_sites_rejected

end Tests.ReadOnlyArrayReferences
