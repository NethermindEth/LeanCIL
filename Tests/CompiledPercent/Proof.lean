import Extracted
import Tests.PercentRuntime
import CIL.Safety.RuntimeExceptions

/-! Checked execution of the compiled Percent caller with the pinned runtime constructors. -/
namespace CompiledPercent
open CIL CIL.Extraction CIL.Safety CIL.Safety.LiteralImage Tests.PercentRuntime

set_option maxRecDepth 65536
set_option maxHeartbeats 30000000

/-- MemberRef operand of the compiled exception constructor. -/
def memberToken (body : BodyEvidence) : Option Nat :=
  body.tokens.operands.findSome? fun (token, operand) => match operand with
    | .call _ => some token
    | _ => none

/-- Caller-local constructor token, declaring type and referenced types. -/
def references (body : BodyEvidence) : Option (Nat × Nat × List Nat) := do
  let token ← memberToken body
  let env ← body.environment.toOption
  let slice ← (env.slice 0 token).toOption
  let member ← (slice.memberRef token).toOption
  let refs := (body.metadata.own.rows.map Prod.fst).filterMap fun key =>
    if metadataTableOf key == Table.typeRef then some key else none
  return (token, member.parent, refs)


/-- Add pinned facade and CoreLib resolution evidence to the packaged method's own rows. -/
def pinnedCaller : Option BodyEvidence := do
  let original := Extracted.method0Body
  let (token, owner, refs) ← references original
  let [root] := refs.filter (· != owner) | none
  let own := original.metadata.own
  -- System.Object and ArgumentOutOfRangeException have fixed rows in the two pinned images.
  let links : List MetadataLink :=
    [⟨linkDefinition, root, 2, 0x020000A2⟩, ⟨linkDefinition, owner, 2, 0x020000F3⟩,
     ⟨linkDefinition, token, 2, Core.RangeCtor.definition.token⟩] ++ own.links ++
    [⟨linkForwarder, root, 1, 0x270001AB⟩, ⟨linkForwarder, owner, 1, 0x27000026⟩]
  let metadata := { original.metadata with own := { own with links }, others := Source.rows.others }
  let operands := original.tokens.operands.map fun (key, operand) =>
    (key, if key == token then .call Source.member else operand)
  let tables ← metadata.tables.toOption
  return { original with
    metadata, tables, identities := Source.source.identities, pinned := Source.source.pinned
    tokens := { operands } }

/-- Pinned definition selected by the caller’s actual constructor token. -/
def binding := do
  let body ← pinnedCaller
  let env ← body.environment.toOption
  let token ← memberToken Extracted.method0Body
  let site ← (env.methodSite token).toOption
  return site.definition

/-- Original instructions decoded with the checked cross-assembly environment. -/
def decoded := do
  let body ← pinnedCaller
  let env ← body.environment.toOption
  (decodeBody env 0 0 body).toOption

/-- The method token carried in this compilation resolves to the actual CoreLib constructor. -/
theorem bound : binding = some (some (2, Core.RangeCtor.definition.token)) := by cil_kernel_rfl

/-- Caller evidence consumed by the executable and its decoding proof. -/
def body := pinnedCaller.getD Extracted.method0Body
/-- Extracted method declaration paired with the scoped decoding of its original bytes. -/
def raw : RawMethod :=
  { Extracted.method0Original with code := (CompiledPercent.decoded.map DecodedBody.code).getD [] }

/-- The original caller bytes, names, signature and scoped metadata are bound with both
additional assembly identities and the relocated constructor token. -/
theorem callerEvidence :
    pinnedCaller = some body ∧
    BodyDecodes (Extracted.assemblies ++ [⟨runtimeScope⟩, ⟨coreLibraryScope⟩])
      Extracted.platformDefinitions Extracted.assembly0 body raw [] Extracted.method0Signature := by
  refine ⟨by cil_kernel_rfl, ?_⟩
  refine ⟨.cons Extracted.assembly0_identified (.cons Source.image1_identified
    (.cons Source.image2_identified .nil)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | cil_kernel_rfl | decide +kernel | cil_body_decodes

/-- Decoded caller linked to the seven CoreLib method bodies reached by Percent. -/
def linkedProgram : Option Program := do
  let body ← pinnedCaller
  let code ← decoded
  let raw := { Extracted.method0Original with code := code.code }
  let table : List SpecializedMethod :=
    ⟨[], raw, Extracted.assembly0⟩ ::
      (coreBytes.map Prod.snd ++ [Core.RangeResource.raw]).map (⟨[], ·, ⟨coreLibraryScope⟩⟩)
  let entry ← Method.ofBody? .scalar {} (links table raw)
    (List.replicate raw.code.length true) body raw []
  let constructors ← coreBytes.mapM fun (evidence, method) => Method.ofBody? .scalar {}
    (links table method) (List.replicate method.code.length true) evidence method []
  return entry :: constructors

/-- Original method operands used to initialize the runtime string table. -/
def inputs := Extracted.method0Original :: coreBytes.map Prod.snd

/-- Decoded execution for every unsigned input at a caller-selected allocation budget. -/
theorem outcome (budget : Option Nat) :
    ∃ executable initial, linkedProgram = some executable ∧
      initialMemory inputs budget = .ok initial ∧
      ∀ value : W32, invoke executable 66 0 [.scalar (.i32 value)] initial =
        if value ≤ 100 then .ok (initial, [.scalar (.i32 value)])
        else if budget.getD 128 < 128 then .error ⟨0, 5, .allocationFailure 128 (budget.getD 128)⟩
        else .error ⟨0, 6, .thrown .argumentOutOfRange⟩ := by
  let texts := operands inputs
  let name := texts[0]?.getD ""
  let message := texts[1]?.getD ""
  have actual : linkedProgram = some (program name message) := by
    dsimp only [name, message, texts]
    cil_kernel_rfl
  have sites : operands inputs = [name, message] := by
    dsimp only [name, message, texts]
    cil_kernel_rfl
  have fitsName : (CIL.utf16Units name).length ≤ 0x7fffffff := by
    dsimp only [name, texts]
    decide +kernel
  have fitsMessage : (CIL.utf16Units message).length ≤ 0x7fffffff := by
    dsimp only [message, texts]
    decide +kernel
  obtain ⟨first, final, installed, repeated, run⟩ :=
    initializedPercentAtBudget budget name message fitsName fitsMessage
  refine ⟨_, atBudget budget final, actual, ?_, run⟩
  simp [initialMemory, sites, List.foldlM_cons, installed, repeated, atBudget,
    Functor.map, Except.map, bind, Except.bind, pure, Except.pure]


#print axioms outcome

/-- With ordinary heap availability, the original CIL returns every input through 100 and
throws the range exception for every larger input, starting with just the loaded image. -/
def ordinaryExecution : Prop :=
  ∃ executable initial, linkedProgram = some executable ∧
    initialMemory inputs = .ok initial ∧
    ∀ value : W32, invoke executable 66 0 [.scalar (.i32 value)] initial =
      if value ≤ 100 then .ok (initial, [.scalar (.i32 value)])
      else .error ⟨0, 6, .thrown .argumentOutOfRange⟩

/-- The checked caller satisfies its ordinary contract after loading the original image. -/
theorem ordinary : ordinaryExecution := by
  simpa [ordinaryExecution] using outcome none
#print axioms ordinary

/-- After image startup, every out-of-range input raises the specified CLR exception exactly
when the deployment budget covers this pinned constructor's allocation. -/
theorem rangeExceptionAtEntry {executable : Program} {initial : Safety.Memory} {heapBytes : Nat}
    (extracted : linkedProgram = some executable)
    (loaded : initialMemory inputs heapBytes = .ok initial) (value : W32) (outside : 100 < value) :
    RaisesCLR executable 0 [.scalar (.i32 value)] initial .argumentOutOfRange ↔ 128 ≤ heapBytes := by
  obtain ⟨actual, start, linked, initialized, ran⟩ := outcome heapBytes
  have sameProgram := Option.some.inj (linked.symm.trans extracted)
  have sameMemory := Except.ok.inj (initialized.symm.trans loaded)
  subst executable
  subst initial
  have branch := ran value
  simp only [Option.getD_some] at branch
  rw [ite_eq_right (BitVec.not_le.mpr outside)] at branch
  by_cases short : heapBytes < 128
  · rw [ite_eq_left short] at branch
    have settled : Settled (.error ⟨0, 5, .allocationFailure 128 heapBytes⟩ :
        Except LocatedFault (Safety.Memory × List Safety.Value)) := by
      change true ≠ false
      decide
    have refused := RaisesCLR.not_of_invoke (exception := .argumentOutOfRange) settled branch
      (by change none ≠ some ExceptionType.argumentOutOfRange; decide)
    exact iff_of_false refused (Nat.not_le.mpr short)
  · rw [ite_eq_right short] at branch
    exact iff_of_true (RaisesCLR.of_invoke branch rfl) (Nat.le_of_not_lt short)
#print axioms rangeExceptionAtEntry

/-- Original packaged caller evidence and its complete decoded outcome under the image quota. -/
theorem verified (heapBytes : Nat) :
    ordinaryExecution ∧
    binding = some (some (2, Core.RangeCtor.definition.token)) ∧
    (pinnedCaller = some body ∧
      BodyDecodes (Extracted.assemblies ++ [⟨runtimeScope⟩, ⟨coreLibraryScope⟩])
        Extracted.platformDefinitions Extracted.assembly0 body raw [] Extracted.method0Signature) ∧
    ∃ executable initial, linkedProgram = some executable ∧
      initialMemory inputs heapBytes = .ok initial ∧
      (∀ value : W32, invoke executable 66 0 [.scalar (.i32 value)] initial =
        if value ≤ 100 then .ok (initial, [.scalar (.i32 value)])
        else if heapBytes < 128 then .error ⟨0, 5, .allocationFailure 128 heapBytes⟩
        else .error ⟨0, 6, .thrown .argumentOutOfRange⟩) ∧
      ∀ value : W32, 100 < value →
        (RaisesCLR executable 0 [.scalar (.i32 value)] initial .argumentOutOfRange ↔
          128 ≤ heapBytes) := by
  obtain ⟨executable, initial, linked, loaded, runs⟩ := outcome heapBytes
  exact ⟨ordinary, bound, callerEvidence, executable, initial, linked, loaded, runs,
    rangeExceptionAtEntry linked loaded⟩
#print axioms verified
end CompiledPercent
