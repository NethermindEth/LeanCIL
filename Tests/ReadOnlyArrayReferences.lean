import CIL.Safety.Execution
import CIL.Extraction.DecodedMethod
import Tests.Support.RawDecoding

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
    elementAddressInstruction (.value .signed32) true
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
private def code (readOnly : Bool) : List CIL.Instruction :=
  [.ldarg 0, .ldarg 1, .nop, .ldelema intType readOnly, .ret, .unadmitted 43]

/-- A branch to the prefix itself does not bypass the restriction. -/
theorem prefix_certificate :
    CIL.Extraction.ScalarFlowValid (raw 2) features states (code true) := by decide +kernel
#print axioms prefix_certificate

/-- Independently forging a writable address under the same readonly raw CIL fails. -/
theorem writable_forgery_rejected :
    ¬ CIL.Extraction.ScalarFlowValid (raw 2) features states (code false) := by decide +kernel
#print axioms writable_forgery_rejected

/-- Changing only the branch target to skip the prefix is rejected, even for a dead branch:
    the scalar check leaves branch entry to body decoding, whose `PrefixEntryFree` refuses it. -/
theorem branch_into_address_rejected :
    CIL.Extraction.ScalarFlowValid (raw 3) features states (code true) ∧
      ¬ CIL.Extraction.PrefixEntryFree (raw 3).code := by decide +kernel
#print axioms branch_into_address_rejected

/-- The accepted body with only its prefix given an operand. -/
private def operandRaw : CIL.Extraction.RawMethod :=
  { raw 2 with code := (raw 2).code.set 2 ⟨2, 65054, .integer 0⟩ }

/-- A prefix that carries an operand has no decoding, and the certificate is rejected. -/
theorem prefix_operand_rejected :
    ¬ CIL.Extraction.ScalarFlowValid operandRaw features states (code true) := by
  decide +kernel
#print axioms prefix_operand_rejected

/-! ## The decoded readonly rule

Each body below is an element address body the scalar check accepts, changed in one place; every
refusal comes from decoding, the rule that only `ldelema` follows `readonly.`, and successor
reachability. -/

section DecodedReadOnly
open CIL.Extraction

/-- A body of `ldarg.0; ldarg.1` then `rest`, with the signature of `raw`. -/
private def body (rest : List RawInstruction) : RawMethod :=
  { raw 2 with code := ⟨0, 2, .none⟩ :: ⟨1, 3, .none⟩ :: rest }

/-- Feature states at the stack depths `depths`, one pc each. -/
private def depthsOf (depths : List Nat) : FeatureCertificate :=
  depths.map fun depth => some ⟨List.replicate depth none, []⟩

/-- The scalar stacks of an address body: the array and index pushed, held through `held` pcs,
    then the reference the address leaves, returned. -/
private def addressStates (held : Nat) : ScalarCertificate :=
  [some [], some [.array .signed32]] ++ List.replicate held (some [.word32, .array .signed32]) ++
    [some [.reference]]

/-- The `readonly.` prefix, `ldelema int32` and `ret` at the offsets they hold after two
    one-byte loads. -/
private def prefixRaw : RawInstruction := ⟨2, 65054, .none⟩
private def addressRaw (offset : Nat) : RawInstruction := ⟨offset, 143, .type intType⟩
private def retRaw (offset : Nat) : RawInstruction := ⟨offset, 42, .none⟩

/-- The raw follower must be a typed ldelema even when the reachability mask excludes it. -/
theorem readonly_requires_element_address :
    let decode := fun follower =>
      (decodeRaw .scalar {} [] [true, true, true, false]
        (body [prefixRaw, follower]) []).map CIL.Method.code
    decode (addressRaw 4) = .ok [.ldarg 0, .ldarg 1, .nop, .unadmitted 143] ∧
      decode ⟨4, 0, .none⟩ = .error (.method .invalidPrefixes) := by
  exact ⟨rfl, rfl⟩
#print axioms readonly_requires_element_address

/-- Whether the scalar check accepts a body with no layouts. -/
private def accepted (body : RawMethod) (features : FeatureCertificate)
    (states : ScalarCertificate) (code : List CIL.Instruction) : Bool :=
  decide (ScalarFlowValid body features states code)

/-- A readonly and a writable element address, each emitted as it decodes, pass the check. -/
theorem decoded_addresses_accepted :
    accepted (body [prefixRaw, addressRaw 4, retRaw 9]) (depthsOf [0, 1, 2, 2, 1])
      (addressStates 2) [.ldarg 0, .ldarg 1, .nop, .ldelema intType true, .ret] ∧
    accepted (body [addressRaw 2, retRaw 7]) (depthsOf [0, 1, 2, 1]) (addressStates 1)
      [.ldarg 0, .ldarg 1, .ldelema intType false, .ret] := by
  decide +kernel
#print axioms decoded_addresses_accepted

/-- An address whose flag disagrees with the raw prefix, or whose element differs from its
    operand, is not the decoding of its raw instruction. -/
theorem forged_addresses_refused :
    !accepted (body [prefixRaw, addressRaw 4, retRaw 9]) (depthsOf [0, 1, 2, 2, 1])
      (addressStates 2) [.ldarg 0, .ldarg 1, .nop, .ldelema intType false, .ret] ∧
    !accepted (body [addressRaw 2, retRaw 7]) (depthsOf [0, 1, 2, 1]) (addressStates 1)
      [.ldarg 0, .ldarg 1, .ldelema intType true, .ret] ∧
    !accepted (body [prefixRaw, addressRaw 4, retRaw 9]) (depthsOf [0, 1, 2, 2, 1])
      (addressStates 2)
      [.ldarg 0, .ldarg 1, .nop, .ldelema (.atom runtimeScope "System.UInt32") true,
        .ret] := by
  decide +kernel
#print axioms forged_addresses_refused

/-- A reachable `readonly.` that ends the body has no `ldelema` after it to take it. -/
theorem final_prefix_refused :
    !readOnlyPrefixMatches none prefixRaw &&
      !accepted (body [prefixRaw]) (depthsOf [0, 1, 2])
        [some [], some [.array .signed32], some [.word32, .array .signed32]]
        [.ldarg 0, .ldarg 1, .nop] := by
  decide +kernel
#print axioms final_prefix_refused

/-- A second `readonly.`, a `nop` or an `ldelem` after `readonly.` does not take it, so the
    prefix site refuses it. -/
theorem wrong_followers_refused :
    [⟨4, 65054, .none⟩, ⟨4, 0, .none⟩, ⟨4, 148, .none⟩].all
      (fun following => !readOnlyPrefixMatches (some following) prefixRaw) ∧
    !accepted (body [prefixRaw, ⟨4, 65054, .none⟩, addressRaw 6, retRaw 11])
      (depthsOf [0, 1, 2, 2, 2, 1]) (addressStates 3)
      [.ldarg 0, .ldarg 1, .nop, .nop, .ldelema intType true, .ret] ∧
    !accepted (body [prefixRaw, ⟨4, 0, .none⟩, addressRaw 5, retRaw 10])
      (depthsOf [0, 1, 2, 2, 2, 1]) (addressStates 3)
      [.ldarg 0, .ldarg 1, .nop, .nop, .ldelema intType false, .ret] ∧
    !accepted (body [prefixRaw, ⟨4, 148, .none⟩, retRaw 5]) (depthsOf [0, 1, 2, 2, 1])
      [some [], some [.array .signed32], some [.word32, .array .signed32],
        some [.word32, .array .signed32], some [.word32]]
      [.ldarg 0, .ldarg 1, .nop, .ldelem .i4, .ret] := by
  decide +kernel
#print axioms wrong_followers_refused

/-- `ldelema` takes no prefix but `readonly.`: after `unaligned.` it has no decoding. -/
theorem unaligned_address_refused :
    !accepted (body [⟨2, 65042, .integer 1⟩, addressRaw 5, retRaw 10]) (depthsOf [0, 1, 2, 2, 1])
      (addressStates 2) [.ldarg 0, .ldarg 1, .nop, .ldelema intType false, .ret] := by
  decide +kernel
#print axioms unaligned_address_refused

/-- A static call of `Fixture.Sink::Take(int32)`. -/
private def takeSite : CallSite := {
  declared := { convention := 0, parameters := [intType] },
  method := {
    owner := .object "Fixture" "Fixture.Sink", name := name!"Take",
    hasThis := false, genericArity := 0, returnType := .void, parameters := [intType] },
  name := "Take", target := .managed 0x06000001, typeArguments := [], parameterCount := 1,
  returnsValue := false }

/-- A call decodes alone but not after `readonly.`, and the `readonly.` before it is refused at
    the prefix site. -/
theorem prefixed_call_refused :
    (valueEncodingMatches none ⟨4, 40, .call takeSite⟩ (.call takeSite.method) &&
      (CIL.Instruction.ofRaw? (some prefixRaw) ⟨4, 40, .call takeSite⟩).isNone &&
      !readOnlyPrefixMatches (some ⟨4, 40, .call takeSite⟩) prefixRaw) = true := by
  decide +kernel
#print axioms prefixed_call_refused

/-- A void body whose first instruction branches over a dead `readonly.` to the `ret` after it. -/
private def deadPrefixRaw : RawMethod :=
  { raw 2 with
    returnType := .void
    code := [⟨0, 43, .target 2⟩, ⟨2, 65054, .none⟩, ⟨4, 42, .none⟩] }

/-- Scalar validation refuses the return after a dead readonly modifier. Branch entry also
    fails because the branch targets the modifier's follower. -/
theorem dead_prefix_follower_refused :
    (¬ ScalarFlowValid deadPrefixRaw [some ⟨[], []⟩, none, some ⟨[], []⟩]
      [some [], none, some []] [.br 2, .unadmitted 65054, .ret]) ∧
      ¬ PrefixEntryFree deadPrefixRaw.code := by
  decide +kernel
#print axioms dead_prefix_follower_refused

end DecodedReadOnly

end Tests.ReadOnlyArrayReferences
