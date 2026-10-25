import CIL.Safety.AllocationRefinement
import Tests.AllocationRenaming

/-!
# Complete executions with private dead locals

Two live numeric locals are separated by private target homes. A nested call allocates its own
homes before the caller allocates dynamic storage, resumes its retained locals and returns
or throws.
-/

namespace Tests.AllocationExecutionRenaming

open CIL.Safety

/-- Caller-owned storage grants an explicit 64-byte dynamic stack quota for each activation. -/
def initial : Memory := { AllocationRenaming.caller with stackLimit := 64 }

/-- Granting the resource quota leaves the existing caller storage well formed. -/
theorem initial_formed : initial.WellFormed := AllocationRenaming.caller_formed
#print axioms initial_formed

/-- Two retained declarations are interleaved with three private numeric homes. -/
def indices : LocalIndexMap := .skip (.keep (.skip (.keep (.skip .nil))))

/-- The source retains one initialized word32 home and one initialized by its code. -/
def sourceBody (code : List CIL.Op) : CIL.Method := {
  returnsValue := true
  locals := [.i32 7, .unmodeled]
  localKinds := [.word32, .word32]
  code }

/-- Initialized private word64 homes precede, separate and follow the retained word32 homes. -/
def targetBody (code : List CIL.Op) : CIL.Method := {
  returnsValue := true
  locals := [.i64 17, .i32 7, .i64 23, .unmodeled, .i64 31]
  localKinds := [.word64, .word32, .word64, .word32, .word64]
  code := code.map indices.operation }

/-- Retained local operands, all method metadata and exact frame declarations match. -/
theorem bodies_related (code : List CIL.Op) :
    Nonempty (MethodRenaming (sourceBody code) (targetBody code)) := by
  refine ⟨⟨indices, ⟨rfl, rfl, rfl⟩,
    .skip _ _ (by simp [InitializerFits]) (.keep _ _ (.skip _ _ (by simp [InitializerFits])
      (.keep _ _ (.skip _ _ (by simp [InitializerFits]) .nil)))), ?_, ?_, rfl⟩⟩
  all_goals constructor <;> first
    | rfl
    | (intro kind member
       simp only [sourceBody, targetBody, List.mem_cons, List.not_mem_nil, or_false] at member
       rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [localWidth, nativeLimit])
#print axioms bodies_related

/-- Changing a retained initializer cannot satisfy the declaration correspondence. -/
theorem changed_initializer_rejected :
    ¬ LocalDeclarations indices [.word32, .word32] [.i32 7, .unmodeled]
      [.word64, .word32, .word64, .word32, .word64]
      [.i64 17, .i32 8, .i64 23, .unmodeled, .i64 31] := by
  intro declarations
  cases declarations
  rename_i retained
  cases retained
#print axioms changed_initializer_rejected

/-- Incompatible inserted word widths cannot establish the declaration relation. -/
theorem incompatible_dead_initializer_rejected :
    ¬ LocalDeclarations (.skip .nil) [] [] [.word32] [.i64 0] := by
  intro declarations
  cases declarations with
  | skip kind initial fits rest => simp [InitializerFits] at fits
#print axioms incompatible_dead_initializer_rejected

/-- Initializer compatibility retains width, aggregate-length and unspecified-bit checks. -/
theorem invalid_dead_initializers_rejected :
    ¬ InitializerFits .byte (.i32 256) ∧
    ¬ InitializerFits (.aggregate 2) (.aggregate [0]) ∧
    ¬ InitializerFits .vector128 (.v128Low64 0) ∧
    ¬ InitializerFits (.span 3 false) .nullRef := by simp [InitializerFits]
#print axioms invalid_dead_initializers_rejected

/-- The child reads seven from its retained initializer after allocating its numeric homes. -/
def childCode : List CIL.Op := [.local 0, .ret]

/-- The inserted nonzero initializer really writes the fresh private home during frame entry. -/
theorem private_initializer_readback :
    (enterFrame (targetBody childCode) [] initial).map
      (fun result => read result.2 ⟨1, 0⟩ 8 1) = .ok (.ok (numberBytes 17 8)) := by rfl
#print axioms private_initializer_readback

/-- A returned child value is stored before later dynamic allocation changes fresh identities. -/
def allocationPrefix : List CIL.Op :=
  [.const32 9, .setLocal 0, .call 1 0, .setLocal 1, .const32 4, .stackAlloc false, .pop]

/-- The resumed caller reads both retained homes after its child and dynamic allocation. -/
def returningCode : List CIL.Op := allocationPrefix ++ [.local 0, .local 1, .add, .ret]

/-- The exceptional fixture raises after both the nested call and dynamic allocation finish. -/
def throwingCode : List CIL.Op := allocationPrefix ++ [.throw "AfterNestedAllocation"]

/-- Both methods use the same declaration transformation and preserve their callable indices. -/
def sourceProgram (code : List CIL.Op) : CIL.Program := [sourceBody code, sourceBody childCode]

/-- The actual program relocates every local operand in both caller and child. -/
def targetProgram (code : List CIL.Op) : CIL.Program := [targetBody code, targetBody childCode]

/-- The complete program satisfies the checked method correspondence, including its child. -/
theorem programs_related (code : List CIL.Op) :
    ProgramRenaming (sourceProgram code) (targetProgram code) := by
  intro method body found
  cases method with
  | zero =>
    cases found
    exact ⟨_, rfl, bodies_related code⟩
  | succ method =>
    cases method with
    | zero =>
      cases found
      exact ⟨_, rfl, bodies_related childCode⟩
    | succ method => cases found
#print axioms programs_related

/-- The fixture reserves enough interpreter fuel for the caller and its child. -/
def fuel : Nat := 24

/-- The source result memory is named from its independently evaluated invocation. -/
def sourceFinal : Memory :=
  match invoke (sourceProgram returningCode) fuel 0 [] initial with
  | .ok (memory, _) => memory
  | .error _ => initial

/-- The actual source interpreter returns sixteen, rather than an assumed method summary. -/
theorem source_returns :
    invoke (sourceProgram returningCode) fuel 0 [] initial =
      .ok (sourceFinal, [.scalar (.i32 16)]) := by rfl
#print axioms source_returns

/-- Source execution leaves the existing caller byte, descriptor and authority unchanged. -/
theorem source_confined : MemoryBelow 1 initial sourceFinal := by
  constructor <;> intro identity bound
  all_goals have same : identity = 0 := by omega
  all_goals subst identity
  all_goals repeat intro
  all_goals rfl
#print axioms source_confined

/-- The actual source raises at the instruction after the nested allocation sequence. -/
theorem source_throws :
    invoke (sourceProgram throwingCode) fuel 0 [] initial =
      .error ⟨0, 7, .thrown "AfterNestedAllocation"⟩ := by rfl
#print axioms source_throws

/-- The source has consumed five fresh identities across both frames and dynamic storage. -/
theorem source_allocation_count : sourceFinal.nextIdentity = 6 := rfl
#print axioms source_allocation_count

/-- Independent target execution consumes eleven identities, including six private dead homes. -/
theorem target_allocation_count :
    (invoke (targetProgram returningCode) fuel 0 [] initial).map
      (fun result => result.1.nextIdentity) = .ok 12 := rfl
#print axioms target_allocation_count

/-- The checked public transfer proves actual target execution and its caller-memory postcondition.
    -/
theorem transferred_return : ∃ final,
    invoke (targetProgram returningCode) fuel 0 [] initial =
      .ok (final, [.scalar (.i32 16)]) ∧ MemoryBelow 1 initial final :=
  (programs_related returningCode).invoke_confined initial_formed
    (by intro binding member; cases member) (values := [.i32 16]) source_returns source_confined
#print axioms transferred_return

/-- The checked public exception transfer covers a throw after nested and dynamic allocation. -/
theorem transferred_exception :
    Raises (targetProgram throwingCode) 0 [] initial "AfterNestedAllocation" :=
  (programs_related throwingCode).raises initial_formed
    (by intro binding member; cases member) (by intro value member; cases member)
    ⟨fuel, _, source_throws, rfl⟩
#print axioms transferred_exception

/-- The contract returns sixteen and preserves caller memory with an unchanged empty footprint. -/
def scalarContract : MethodContract Unit CIL.W32 := {
  args := fun _ => []
  results := fun output => [.scalar (.i32 output)]
  pre := fun _ memory => memory = initial
  footprint := fun _ => []
  post := fun _ before after output => output = 16 ∧ MemoryBelow 1 before after }

/-- The source contract follows from its actual interpreter result and caller-memory proof. -/
theorem source_contract : scalarContract.Holds (sourceProgram returningCode) 0 := by
  intro input memory permitted
  change memory = initial at permitted
  subst memory
  exact ⟨fuel, sourceFinal, [.scalar (.i32 16)], source_returns,
    Confined.ofMemoryBelow source_confined (by decide)
      (invoke_preserves_caller_allocations _ _ _ _ _ _ _ source_returns).next,
    16, rfl, rfl, source_confined⟩
#print axioms source_contract

/-- Full Holds transfers the same contract, precondition, output encoding and empty footprint. -/
theorem transferred_contract : scalarContract.Holds (targetProgram returningCode) 0 := by
  apply source_contract.of_allocationRenaming (programs_related returningCode)
  · intro input memory permitted
    change memory = initial at permitted
    subst memory
    exact ⟨initial_formed, by intro binding member; cases member⟩
  · intro output
    exact ⟨[.i32 output], rfl⟩
  · intro input before sourceFinal targetFinal output permitted related post
    change before = initial at permitted
    subst before
    exact ⟨post.1, post.2.trans related⟩
#print axioms transferred_contract

/-- The default zero resource quota still rejects the same nonzero dynamic allocation. -/
theorem zero_quota_rejected :
    invoke (sourceProgram returningCode) fuel 0 [] AllocationRenaming.caller =
      .error ⟨0, 5, .stackAllocationFailure 16 0⟩ := rfl
#print axioms zero_quota_rejected

/-- Leaving the first local operand unrelocated violates the exact instruction equation. -/
theorem unchanged_operand_rejected :
    ([.local 0] : List CIL.Op) ≠ [.local 0].map indices.operation := by intro equal; cases equal
#print axioms unchanged_operand_rejected

/-- Replacing the nested call target violates the exact instruction equation. -/
theorem changed_callee_rejected :
    ([.call 0 0] : List CIL.Op) ≠ [.call 1 0].map indices.operation := by intro equal; cases equal
#print axioms changed_callee_rejected

end Tests.AllocationExecutionRenaming

namespace Tests.InitializedLocalControls
open CIL.Safety

/-- A compact method has no local declarations and returns a fixed scalar. -/
def compact : CIL.Method := {
  locals := [], returnsValue := true, code := [.const32 7, .ret] }

/-- The target inserts exactly one unused declaration with its supplied initializer. -/
def inserted (kind : CIL.LocalKind) (initial : CIL.Value) : CIL.Method := {
  compact with localKinds := [kind], locals := [initial] }

/-- The compact method's checked execution succeeds for arbitrary caller memory. -/
theorem compact_returns (memory : Memory) :
    invoke [compact] 3 0 [] memory = .ok (memory, [.scalar (.i32 7)]) := by rfl
#print axioms compact_returns

/-- A valid initializer supplies the existing ordinary-frame width requirements. -/
theorem inserted_ready (kind : CIL.LocalKind) (initial : CIL.Value)
    (fits : InitializerFits kind initial) : OrdinaryFrame (inserted kind initial) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro selected member
  have same : selected = kind := List.mem_singleton.mp member
  subst selected
  refine ⟨localWidth_bounded kind, ?_⟩
  intro width writable same
  subst kind
  exact fits.1
#print axioms inserted_ready

/-- The exact operand map permits any admitted initializer for the one deleted declaration. -/
theorem inserted_related (kind : CIL.LocalKind) (initial : CIL.Value)
    (fits : InitializerFits kind initial) :
    ProgramRenaming [compact] [inserted kind initial] := by
  intro method body found
  cases method with
  | zero =>
    cases found
    refine ⟨inserted kind initial, rfl, ⟨⟨.skip .nil, ⟨rfl, rfl, rfl⟩,
      .skip kind initial fits .nil, ?_, inserted_ready kind initial fits, rfl⟩⟩⟩
    exact ⟨rfl, rfl, rfl, by intro selected member; cases member⟩
  | succ method => cases found
#print axioms inserted_related

/-- Every admitted initializer, including arbitrary zero or nonzero words, preserves the caller.
    No initializer value is observed by the constant-returning method. -/
theorem inserted_preserves_caller (kind : CIL.LocalKind) (initial : CIL.Value)
    (fits : InitializerFits kind initial)
    (memory : Memory) (formed : memory.WellFormed) (statics : memory.StaticBindingsBounded) :
    ∃ final, invoke [inserted kind initial] 3 0 [] memory =
      .ok (final, [.scalar (.i32 7)]) ∧ MemoryBelow memory.nextIdentity memory final := by
  exact (inserted_related kind initial fits).invoke_confined formed statics
    (values := [.i32 7]) (compact_returns memory) (.refl _ _)
#print axioms inserted_preserves_caller

end Tests.InitializedLocalControls
