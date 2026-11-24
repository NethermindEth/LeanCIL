import Extracted
import Tests.PercentRuntime
import CIL.Safety.RuntimeExceptions

/-! Checked execution of the compiled Percent caller with the pinned runtime constructors. -/
namespace CompiledPercent
open CIL CIL.Extraction CIL.Safety CIL.Safety.LiteralImage CIL.Runtime.Net11WinX64 Tests.PercentRuntime

set_option maxRecDepth 65536
set_option maxHeartbeats 30000000

private def physicalEntry := Extracted.managedPackage.map ProgramEntry.range

/-- The audited entry selects the same methods as the caller's physical package. -/
private theorem entry_eq :
    Extracted.translation_valid.entry .net11WinX64 = physicalEntry := by cil_kernel_rfl
#print axioms entry_eq

/-- MemberRef operand of the compiled exception constructor. -/
def memberToken (body : BodyEvidence) : Option Nat :=
  body.constructorTokenAt? 0 0 5

/-- Bind the packaged caller using the facade and CoreLib rows carried with the runtime. -/
def pinnedCaller : Option BodyEvidence :=
  match physicalEntry with
  | some (.range image) => some image.caller.body
  | _ => none

/-- The neighboring throw, a missing defining image, the facade with the same MethodDef
number, a different MethodDef and a mismatched constructor signature are all refused. -/
theorem rejectsInvalidBindings :
    let bindCtor := Extracted.method0Body.bindConstructor? Extracted.method0Original 5
    let callee : SpecializedMethod := ⟨[], Core.RangeCtor.definition, ⟨coreLibraryScope⟩⟩
    (Extracted.method0Body.constructorTokenAt? 0 0 6).isNone ∧
    (bindCtor [] callee).isNone ∧
    (bindCtor rangeDependencies
      { callee with assembly := ⟨runtimeScope⟩ }).isNone ∧
    (bindCtor rangeDependencies
      { callee with closed := { callee.closed with token := Core.ArgumentCtor.definition.token } }).isNone ∧
    (bindCtor rangeDependencies
      { callee with closed := { callee.closed with parameters := [] } }).isNone := by
  repeat' constructor
  all_goals cil_kernel_rfl
#print axioms rejectsInvalidBindings

/-- The Windows x64 constructor image requires a compatible target and the actual newobj. -/
theorem rejectsOtherTarget :
    (Extracted.translation_valid.entry .portable).isNone ∧
    (rangeImage? (.ofEvidence (Extracted.methodEvidence[0]'(by decide))) 5
      { Extracted.profile with architecture := .arm64 } Extracted.environment).isNone ∧
    (rangeImage? (.ofEvidence (Extracted.methodEvidence[0]'(by decide))) 6
      Extracted.profile Extracted.environment).isNone := by
  repeat' constructor
  all_goals cil_kernel_rfl
#print axioms rejectsOtherTarget

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
  have images : body.metadata.slices.map (·.assembly) =
      [Extracted.assembly0Metadata, facadeAssembly, CoreLib.assembly] := by
    cil_kernel_rfl
  have ids : body.identities = [Extracted.assembly0Identity, facadeIdentity, coreIdentity] := by
    cil_kernel_rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold AssembliesIdentified
    rw [images, ids]
    exact .cons Extracted.assembly0_identified (.cons facadeIdentified
      (.cons coreIdentified .nil))
  all_goals first | cil_kernel_rfl | decide +kernel | cil_body_decodes

/-- The managed method and its evidence as returned by the runtime binder. -/
private def managedCaller := do
  let some (.range image) := physicalEntry | none
  return (image.caller, ← image.methods[0]?)

private def callerPair := managedCaller.getD (Extracted.methodEvidence[0]'(by decide),
  { code := [], locals := [], returnsValue := false })

private def managedTargets : List SpecializedMethod :=
  ⟨[], raw, Extracted.assembly0⟩ ::
    (coreBytes.map fun pair => ⟨[], pair.2, ⟨coreLibraryScope⟩⟩)

/-- The caller's only call-family operand resolves inside the method table for any import list. -/
private theorem callerCalls :
    (fun slots : List ImportSlot => decide (ManagedCallsValid managedTargets slots
      (callModelled callerPair.2) (lowerConstrainedRaw callerPair.1.dispatchTypes
        callerPair.1.closed) callerPair.1.reachable callerPair.2)) = fun _ => true := by
  cil_kernel_rfl
#print axioms callerCalls

private theorem callerBody :
    BodyDecodes (Extracted.assemblies ++ [⟨runtimeScope⟩, ⟨coreLibraryScope⟩])
      Extracted.platformDefinitions callerPair.1.assembly callerPair.1.body callerPair.1.original
      callerPair.1.arguments callerPair.1.signature := by
  rw [show callerPair.1.assembly = Extracted.assembly0 by cil_kernel_rfl,
      show callerPair.1.body = body by cil_kernel_rfl,
      show callerPair.1.original = raw by cil_kernel_rfl,
      show callerPair.1.arguments = [] by cil_kernel_rfl,
      show callerPair.1.signature = Extracted.method0Signature by cil_kernel_rfl]
  exact callerEvidence.2
#print axioms callerBody

/-- The ordinary per-method validator accepts the rebound caller, including its object
stack at both string loads, its managed construction link and its stack-based throw. The
surrounding table supplies the seven resolved callees, with no scalar constant summaries. -/
def ManagedCallerValid : Prop :=
    ∃ item method, managedCaller = some (item, method) ∧
      ∀ (all : List MethodEvidence) (slots : List ImportSlot),
        specializationTable all = ⟨[], raw, Extracted.assembly0⟩ ::
          (coreBytes.map fun pair => ⟨[], pair.2, ⟨coreLibraryScope⟩⟩) →
        evidenceConstants all = (fun _ => none) →
        (ImportSlotIndex.ofList slots).forLinks all.length method.links = {} →
        MethodEvidenceValid Extracted.rawLayouts Extracted.computedLayouts
          (Extracted.assemblies ++ [⟨runtimeScope⟩, ⟨coreLibraryScope⟩])
          Extracted.platformDefinitions all slots item method

/-- The evidence emitted by the runtime binder passes each ordinary caller validator. -/
theorem managedCallerValid : ManagedCallerValid := by
  have selected : managedCaller = some callerPair := by cil_kernel_rfl
  refine ⟨_, _, selected, ?_⟩
  intro all slots targets constants imports
  unfold MethodEvidenceValid
  rw [targets, constants, imports]
  refine ⟨?_, ?_, ?_, ?_, of_decide_eq_true (congrFun callerCalls slots), ?_, ?_, ?_, ?_, ?_,
    ?_, ⟨?_, ?_⟩, ?_, callerBody, ?_, ?_, ?_, ?_⟩
  all_goals first | cil_kernel_rfl | decide +kernel

#print axioms managedCallerValid

/-- Decoded caller linked to the seven CoreLib method bodies reached by Percent. -/
def linkedProgram : Option Program := physicalEntry.map (·.methods)

/-- Original bodies used by the package's image loader. -/
def inputs : List RawMethod := (physicalEntry.map (·.originals)).getD []

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

/-- The generated image loads and executes from empty caller storage, including for an
explicit deployment quota. Neither the caller nor the proof supplies runtime method bodies. -/
def imageExecution (budget : Option Nat) : Prop :=
  ∃ image initial, Extracted.translation_valid.entry .net11WinX64 = some image ∧
    image.initialMemory budget = .ok initial ∧
    ∀ value : W32, image.invoke 66 [.scalar (.i32 value)] budget = .ok
      (if value ≤ 100 then .ok (initial, [.scalar (.i32 value)])
       else if budget.getD 128 < 128 then .error ⟨0, 5, .allocationFailure 128 (budget.getD 128)⟩
       else .error ⟨0, 6, .thrown .argumentOutOfRange⟩)

theorem imageFromEmpty (budget : Option Nat) : imageExecution budget := by
  obtain ⟨executable, initial, generated, loaded, runs⟩ := outcome budget
  unfold imageExecution
  rw [entry_eq]
  cases found : physicalEntry with
  | none => simp [linkedProgram, found] at generated
  | some image =>
    have same : image.methods = executable := by simpa [linkedProgram, found] using generated
    have ready : image.initialMemory budget = .ok initial := by
      simpa [ProgramEntry.initialMemory, inputs, found] using loaded
    refine ⟨image, initial, found, ready, ?_⟩
    intro value
    rw [ProgramEntry.invoke, ready, same]
    exact congrArg Except.ok (runs value)
#print axioms imageFromEmpty

/-- Original packaged caller evidence and its complete decoded outcome under the image quota. -/
theorem verified (heapBytes : Nat) :
    ManagedCallerValid ∧ imageExecution none ∧ imageExecution heapBytes ∧ ordinaryExecution ∧
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
  exact ⟨managedCallerValid, imageFromEmpty none, imageFromEmpty heapBytes, ordinary, bound,
    callerEvidence, executable, initial, linked, loaded, runs,
    rangeExceptionAtEntry linked loaded⟩
#print axioms verified
end CompiledPercent
