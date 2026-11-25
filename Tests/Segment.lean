import Tests.Support.IntrinsicMethods
import CIL.Safety.SegmentLocals

/-!
# Composable placed-segment contracts

Checked prefixes are composed through exact intermediate states. The vector-input slices
mirror a 256-bit Add's reference prefix and Multiply's AVX input loads; placements, formation
and successful memory operations remain explicit premises.
-/

namespace Tests.Segment
open CIL.Safety

/-- The byref overload of Unsafe.AsRef closed over UInt64. -/
def asRefUInt64 : CIL.Extraction.MethodRef :=
  let element := CIL.Extraction.TypeExpr.primitive .uint64
  { owner := CIL.Extraction.unsafeOwner, name := name!"AsRef", hasThis := false,
    genericArity := 1, methodArguments := [element], parameters := [.byref element],
    returnType := .byref element }

/-- Both AsRef calls in the placed prefix use the runtime model. -/
def prefixUnlinked (body : CIL.Method) (start : Nat) : Prop :=
  body.linkAt (start + 1) = none ∧ body.linkAt (start + 2) = none

/-- The argument formation sequence used by the vector input prefixes. -/
def referencePrefix (index : Nat) : List CIL.Instruction :=
  [.ldarg index, .call asRefUInt64, .call asRefUInt64]

/-- A linked-table miss and a resolved AsRef preserve an already formed reference. -/
private theorem asRef_step (body : CIL.Method) (pc : Nat) (arguments stack : List Value)
    (frame : Frame) (memory : Memory) (reference : Reference) (unlinked : body.linkAt pc = none)
    (model : CIL.Extraction.runtimeModel body.environment .call asRefUInt64 = some (.memory .asRef))
    (formed : form memory reference = .ok reference) :
    step body (.call asRefUInt64) pc arguments frame (.reference (.address reference) :: stack) memory =
      .ok (.next (pc + 1) (.reference (.address reference) :: stack) frame memory) := by
  rw [step_call_model _ _ _ _ _ unlinked model rfl _]
  cil_checked_step [formed]

/-- Argument formation is a reusable segment at any placed position. -/
theorem reference_prefix {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body) (index : Nat)
    (placed : CodeAt body start (referencePrefix index))
    (unlinked : prefixUnlinked body start)
    (model : CIL.Extraction.runtimeModel body.environment .call asRefUInt64 = some (.memory .asRef))
    (plain : body.argumentAccess index = .value none)
    (arguments : List Value) (frame : Frame) (stack : List Value)
    (memory : Memory) (reference : Reference)
    (argument : arguments[index]? = some (.reference (.address reference)))
    (formed : form memory reference = .ok reference) :
    Segment program method start (start + 3)
      (SegmentState.exact arguments ⟨frame, stack, memory⟩)
      (SegmentState.exact arguments ⟨frame, .reference (.address reference) :: stack, memory⟩) := by
  apply Segment.ofRun (cost := 3)
  intro fuel
  have load : step body (.ldarg index) start arguments frame stack memory =
      .ok (.next (start + 1) (.reference (.address reference) :: stack) frame memory) := by
    cil_checked_step [plain, argument, formed]
  exact (run_next (fuel := fuel + 2) found (placed.lookup 0 rfl) load).trans
    ((run_next (fuel := fuel + 1) found (placed.lookup 1 rfl)
      (asRef_step _ _ _ _ _ _ _ unlinked.1 model formed)).trans
      (run_next (fuel := fuel) found (placed.lookup 2 rfl)
        (asRef_step _ _ _ _ _ _ _ unlinked.2 model formed)))

#print axioms reference_prefix

/-- Saving the right reference and duplicating the left finishes Add's eight-op prefix. -/
theorem save_right {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body)
    (placed : CodeAt body start [.stloc 0, .dup])
    (arguments : List Value) (frame : Frame) (slots : List LocalSlot)
    (initial : Option ManagedReference) (memory : Memory) (left right : Reference)
    (layout : frame.locals = .root initial :: slots)
    (rightFormed : form memory right = .ok right) :
    Segment program method start (start + 2)
      (SegmentState.exact arguments ⟨frame,
        [.reference (.address right), .reference (.address left)], memory⟩)
      (SegmentState.exact arguments
        ⟨{ frame with locals := .root (some (.address right)) :: slots },
          [.reference (.address left), .reference (.address left)], memory⟩) := by
  cil_segment 2 [found, placed, layout, rightFormed, storeLocal]

#print axioms save_right

/-- The positional Add Vector128 reference signature is a composition of three contracts. -/
theorem add_vector128_inputs {program : CIL.Program} {method : Nat} {body : CIL.Method}
    (found : program[method]? = some body)
    (leftUnlinked : prefixUnlinked body 0) (rightUnlinked : prefixUnlinked body 3)
    (model : CIL.Extraction.runtimeModel body.environment .call asRefUInt64 = some (.memory .asRef))
    (placed : CodeAt body 0 (referencePrefix 0 ++ referencePrefix 1 ++ [.stloc 0, .dup]))
    (leftPlain : body.argumentAccess 0 = .value none)
    (rightPlain : body.argumentAccess 1 = .value none)
    (arguments : List Value) (frame : Frame) (slots : List LocalSlot)
    (initial : Option ManagedReference) (memory : Memory) (left right : Reference)
    (layout : frame.locals = .root initial :: slots)
    (leftArgument : arguments[0]? = some (.reference (.address left)))
    (rightArgument : arguments[1]? = some (.reference (.address right)))
    (leftFormed : form memory left = .ok left) (rightFormed : form memory right = .ok right) :
    Segment program method 0 8 (SegmentState.exact arguments ⟨frame, [], memory⟩)
      (SegmentState.exact arguments
        ⟨{ frame with locals := .root (some (.address right)) :: slots },
          [.reference (.address left), .reference (.address left)], memory⟩) := by
  have first := reference_prefix found 0 placed.append_left.append_left leftUnlinked model leftPlain arguments
    frame [] memory left leftArgument leftFormed
  have second := reference_prefix found 1 placed.append_left.append_right rightUnlinked model rightPlain arguments
    frame [.reference (.address left)] memory right rightArgument rightFormed
  have third := save_right found placed.append_right arguments frame slots initial memory
    left right layout rightFormed
  exact (first.trans second).trans third

#print axioms add_vector128_inputs



/-- A placed input-reference formation and Vector256 load uses the original checked read. -/
theorem load256_prefix {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body) (index : Nat)
    (placed : CodeAt body start (referencePrefix index ++ [.ldobj Tests.IntrinsicMethods.vector256UInt64]))
    (unlinked : prefixUnlinked body start)
    (model : CIL.Extraction.runtimeModel body.environment .call asRefUInt64 = some (.memory .asRef))
    (plain : body.argumentAccess index = .value none)
    (arguments : List Value) (frame : Frame) (memory : Memory) (reference : Reference)
    (vector : BitVec 256)
    (argument : arguments[index]? = some (.reference (.address reference)))
    (formed : form memory reference = .ok reference)
    (loaded : loadValue memory (.address reference) 32 = .ok (.v256 vector)) :
    Segment program method start (start + 4)
      (SegmentState.exact arguments ⟨frame, [], memory⟩)
      (SegmentState.exact arguments ⟨frame, [.scalar (.v256 vector)], memory⟩) := by
  apply (reference_prefix found index placed.append_left unlinked model plain arguments frame []
    memory reference argument formed).trans
  apply Segment.ofRun (cost := 1)
  intro fuel
  apply run_next found (placed.lookup 3 rfl)
  rw [step_ldobj_vector32 _ _ _ _ _ (by rfl) _]
  cil_checked_step [loaded]

#print axioms load256_prefix

/-- One local store retains its actual checked step equation and memory transition. -/
theorem store256 {program : CIL.Program} {method start index : Nat} {body : CIL.Method}
    (found : program[method]? = some body) (placed : CodeAt body start [.stloc index])
    (arguments : List Value) (frame : Frame) (before after : Memory) (vector : BitVec 256)
    (stored : step body (.stloc index) start arguments frame [.scalar (.v256 vector)] before =
      .ok (.next (start + 1) [] frame after)) :
    Segment program method start (start + 1)
      (SegmentState.exact arguments ⟨frame, [.scalar (.v256 vector)], before⟩)
      (SegmentState.exact arguments ⟨frame, [], after⟩) := by
  cil_segment 1 [found, placed, stored]

#print axioms store256

/-- The Multiply AVX2 left-input stage composes load and store at the original positions. -/
theorem multiply_left_input {program : CIL.Program} {method : Nat} {body : CIL.Method}
    (found : program[method]? = some body)
    (leftUnlinked : prefixUnlinked body 44)
    (model : CIL.Extraction.runtimeModel body.environment .call asRefUInt64 = some (.memory .asRef))
    (placed : CodeAt body 44 (referencePrefix 0 ++ [.ldobj Tests.IntrinsicMethods.vector256UInt64, .stloc 23]))
    (plain : body.argumentAccess 0 = .value none)
    (arguments : List Value) (frame : Frame) (before after : Memory) (left : Reference)
    (vector : BitVec 256)
    (argument : arguments[0]? = some (.reference (.address left)))
    (formed : form before left = .ok left)
    (loaded : loadValue before (.address left) 32 = .ok (.v256 vector))
    (stored : step body (.stloc 23) 48 arguments frame [.scalar (.v256 vector)] before =
      .ok (.next 49 [] frame after)) :
    Segment program method 44 49 (SegmentState.exact arguments ⟨frame, [], before⟩)
      (SegmentState.exact arguments ⟨frame, [], after⟩) := by
  have split : CodeAt body 44 ((referencePrefix 0 ++ [.ldobj Tests.IntrinsicMethods.vector256UInt64]) ++ [.stloc 23]) :=
    placed
  exact (load256_prefix found 0 split.append_left leftUnlinked model plain arguments frame before left vector
    argument formed loaded).trans
      (store256 found split.append_right arguments frame before after vector stored)

#print axioms multiply_left_input


/-- The AVX2 permutation stage retains availability and exact intrinsic semantics. -/
theorem reverse256 {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body)
    (placed : CodeAt body start [.ldc_i4 27, .call Tests.IntrinsicMethods.permute])
    (unlinked : body.linkAt (start + 1) = none)
    (arguments : List Value) (frame : Frame) (memory : Memory) (vector reversed : BitVec 256)
    (available : (CIL.Intrinsic.avx2 .permute4x64).available body.profile = true)
    (permuted : checkedIntrinsic (.avx2 .permute4x64) [.v256 vector, .i32 27] =
      .ok (.v256 reversed)) :
    Segment program method start (start + 2)
      (SegmentState.exact arguments ⟨frame, [.scalar (.v256 vector)], memory⟩)
      (SegmentState.exact arguments ⟨frame, [.scalar (.v256 reversed)], memory⟩) := by
  apply Segment.ofRun (cost := 2)
  have reversedStep : step body (.call Tests.IntrinsicMethods.permute) (start + 1)
      arguments frame [.scalar (.i32 27), .scalar (.v256 vector)] memory =
      .ok (.next (start + 2) [.scalar (.v256 reversed)] frame memory) := by
    rw [step_call_intrinsic _ _ _ _ _ unlinked (Tests.IntrinsicMethods.permute_model _) rfl]
    simp only [intrinsicCall, available, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    change (do
      let value ← checkedIntrinsic (.avx2 .permute4x64) [.v256 vector, .i32 27]
      let checked ← checkedValue memory (.scalar value)
      pure (FrameAction.next (start + 2) [checked] frame memory)) = _
    rw [permuted]
    rfl
  cil_segment_steps [found, placed, reversedStep, unlinked]
  all_goals exact run_next found (placed.lookup 1 rfl) reversedStep

#print axioms reverse256

/-- Multiply's two vector input stages compose through the checked intermediate memory. -/
theorem multiply_inputs {program : CIL.Program} {method : Nat} {body : CIL.Method}
    (found : program[method]? = some body)
    (unlinked : body.linkAt 54 = none)
    (leftUnlinked : prefixUnlinked body 44) (rightUnlinked : prefixUnlinked body 49)
    (model : CIL.Extraction.runtimeModel body.environment .call asRefUInt64 = some (.memory .asRef))
    (leftPlaced : CodeAt body 44 (referencePrefix 0 ++ [.ldobj Tests.IntrinsicMethods.vector256UInt64, .stloc 23]))
    (rightPlaced : CodeAt body 49 (referencePrefix 1 ++ [.ldobj Tests.IntrinsicMethods.vector256UInt64,
      .ldc_i4 27, .call Tests.IntrinsicMethods.permute, .stloc 24]))
    (leftPlain : body.argumentAccess 0 = .value none)
    (rightPlain : body.argumentAccess 1 = .value none)
    (arguments : List Value) (frame : Frame) (before middle after : Memory)
    (left right : Reference) (leftVector rightVector reversed : BitVec 256)
    (leftArgument : arguments[0]? = some (.reference (.address left)))
    (rightArgument : arguments[1]? = some (.reference (.address right)))
    (leftFormed : form before left = .ok left) (rightFormed : form middle right = .ok right)
    (leftLoaded : loadValue before (.address left) 32 = .ok (.v256 leftVector))
    (rightLoaded : loadValue middle (.address right) 32 = .ok (.v256 rightVector))
    (leftStored : step body (.stloc 23) 48 arguments frame [.scalar (.v256 leftVector)] before =
      .ok (.next 49 [] frame middle))
    (rightStored : step body (.stloc 24) 55 arguments frame [.scalar (.v256 reversed)] middle =
      .ok (.next 56 [] frame after))
    (available : (CIL.Intrinsic.avx2 .permute4x64).available body.profile = true)
    (permuted : checkedIntrinsic (.avx2 .permute4x64) [.v256 rightVector, .i32 27] =
      .ok (.v256 reversed)) :
    Segment program method 44 56 (SegmentState.exact arguments ⟨frame, [], before⟩)
      (SegmentState.exact arguments ⟨frame, [], after⟩) := by
  have first := multiply_left_input found leftUnlinked model leftPlaced leftPlain arguments frame before middle left
    leftVector leftArgument leftFormed leftLoaded leftStored
  have split : CodeAt body 49 (((referencePrefix 1 ++ [.ldobj Tests.IntrinsicMethods.vector256UInt64]) ++
      [.ldc_i4 27, .call Tests.IntrinsicMethods.permute]) ++ [.stloc 24]) := rightPlaced
  have loaded := load256_prefix found 1 split.append_left.append_left rightUnlinked model rightPlain arguments
    frame middle right rightVector rightArgument rightFormed rightLoaded
  have reversed := reverse256 found split.append_left.append_right unlinked arguments frame middle
    rightVector reversed available permuted
  have stored := store256 found split.append_right arguments frame middle after _ rightStored
  exact ((first.trans loaded).trans reversed).trans stored

#print axioms multiply_inputs








/-- Two actual vector stores preserve every other remembered local in one frame-rule use. -/
theorem multiply_untouched {body : CIL.Method} {before middle after entered : Memory}
    {boundary : Nat}
    {kinds : List CIL.LocalKind} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} {leftHome rightHome : Reference}
    (homes : WritableHomes entered boundary kinds slots)
    (snapshots : LocalSnapshots before slots known)
    (leftSlot : slots[23]? = some (.bytes .vector256 leftHome))
    (rightSlot : slots[24]? = some (.bytes .vector256 rightHome))
    (leftVector rightVector : BitVec 256)
    (leftWritten : write before leftHome (numberBytes leftVector.toNat 32) 1 = .ok middle)
    (rightWritten : write middle rightHome (numberBytes rightVector.toNat 32) 1 = .ok after) :
    LocalSnapshots after slots (untouchedLocals body [.stloc 23, .stloc 24] known) := by
  have first : SegmentLocalEffects body [.stloc 23] slots before middle :=
    .store 23 .vector256 leftHome _ 1 (by simp [segmentStores]) leftSlot leftWritten
  have second : SegmentLocalEffects body [.stloc 24] slots middle after :=
    .store 24 .vector256 rightHome _ 1 (by simp [segmentStores]) rightSlot rightWritten
  exact (first.append second).frame homes snapshots.untouched

#print axioms multiply_untouched

/-- Aliased byte homes cannot supply the separation premise of the frame rule. -/
theorem aliased_homes_rejected (memory : Memory) (boundary : Nat) (home : Reference) :
    ¬ WritableHomes memory boundary [.word64, .word64]
      [.bytes .word64 home, .bytes .word64 home] := by
  intro homes
  exact homes.distinct 0 1 .word64 .word64 home home (by decide) rfl rfl rfl

#print axioms aliased_homes_rejected

/-- A region with no direct stores cannot certify a hidden memory mutation. -/
theorem no_hidden_write {body : CIL.Method} {slots : List LocalSlot} {before after : Memory}
    (effects : SegmentLocalEffects body [.stind .i8] slots before after) : before = after := by
  induction effects with
  | refl => rfl
  | store index kind home bytes alignment destination => simp [segmentStores] at destination
  | trans _ _ first second => exact first.trans second

#print axioms no_hidden_write

/-- A declared destination cannot preserve its own old snapshot through the frame mask. -/
theorem stored_local_not_framed (body : CIL.Method) (known : Nat → Option CIL.Value) :
    untouchedLocals body [.stloc 23, .stloc 24] known 23 = none ∧
      untouchedLocals body [.stloc 23, .stloc 24] known 7 = known 7 := by
  simp [untouchedLocals, segmentStores]

#print axioms stored_local_not_framed

/-- A body whose one argument has its home in slot 0, as a store to the argument requires. -/
private def homedArgumentBody : CIL.Method :=
  { locals := [], parameterHomes := [(0, .word32)], returnsValue := false,
    code := [.ldc_i4 7, .starg 0, .ret] }

/-- A store to a homed argument names its home slot: its write is a segment effect, and the
    slot's old snapshot is not framed, as for the `stloc` of that slot. -/
theorem argument_store_effect {slots : List LocalSlot} {before after : Memory}
    {home : Reference} {bytes : List (BitVec 8)} {alignment : Nat}
    (known : Nat → Option CIL.Value) (slot : slots[0]? = some (.bytes .word32 home))
    (written : write before home bytes alignment = .ok after) :
    SegmentLocalEffects homedArgumentBody [.ldc_i4 7, .starg 0] slots before after ∧
      untouchedLocals homedArgumentBody [.ldc_i4 7, .starg 0] known 0 = none :=
  ⟨.store 0 .word32 home bytes alignment (by decide) slot written,
    by rw [untouchedLocals, if_pos (by decide)]⟩

#print axioms argument_store_effect

/-- Segment composition requires the exact intermediate position and postcondition. -/
theorem composition_boundaries {program : CIL.Program} {method : Nat}
    {pre middle post other : List Value → SegmentState → Prop}
    (_first : Segment program method 0 3 pre middle)
    (_wrongPosition : Segment program method 4 6 middle post)
    (_wrongState : Segment program method 3 6 other post) : True := by
  fail_if_success have : Segment program method 0 6 pre post := _first.trans _wrongPosition
  fail_if_success have : Segment program method 0 6 pre post := _first.trans _wrongState
  trivial

#print axioms composition_boundaries

/-- Wrong opcodes, endpoint states and missing memory facts do not yield a segment proof. -/
theorem checked_boundaries {program : CIL.Program} {method : Nat} {body : CIL.Method}
    (_found : program[method]? = some body) (_placed : CodeAt body 0 [.ldarg 0])
    (_frame : Frame) (_memory : Memory) : True := by
  fail_if_success
    have : (SegmentRun program method 0 1 1 [.scalar (.i64 4)]
      ⟨_frame, [], _memory⟩ ⟨_frame, [.scalar (.i64 5)], _memory⟩) := by
      cil_segment_steps [_found, _placed]
      done
  fail_if_success
    have : (SegmentRun program method 0 1 0 [.scalar (.i64 4)]
      ⟨_frame, [], _memory⟩ ⟨_frame, [.scalar (.i64 4)], _memory⟩) := by
      cil_segment_steps [_found, _placed]
      done
  trivial

#print axioms checked_boundaries






/-- A placed numeric-store contract gains untouched snapshots from its actual write effect. -/
theorem framed_store {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body) (placed : CodeAt body start [.stloc 23])
    (arguments : List Value) (frame : Frame) (before after entered : Memory)
    (boundary : Nat) (kinds : List CIL.LocalKind) (home : Reference) (vector : BitVec 256)
    (known : Nat → Option CIL.Value)
    (homes : WritableHomes entered boundary kinds frame.locals)
    (snapshots : LocalSnapshots before frame.locals known)
    (slot : frame.locals[23]? = some (.bytes .vector256 home))
    (written : write before home (numberBytes vector.toNat 32) 1 = .ok after)
    (stored : step body (.stloc 23) start arguments frame [.scalar (.v256 vector)] before =
      .ok (.next (start + 1) [] frame after)) :
    Segment program method start (start + 1)
      (SegmentState.exact arguments ⟨frame, [.scalar (.v256 vector)], before⟩)
      (fun actual state => SegmentState.exact arguments ⟨frame, [], after⟩ actual state ∧
        LocalSnapshots state.memory state.frame.locals
          (untouchedLocals body [.stloc 23] known)) := by
  apply Segment.frameLocals found placed rfl homes snapshots
  apply (store256 found placed arguments frame before after vector stored).consequence
    (fun _ _ valid => valid)
  intro actual state valid
  refine ⟨valid, ?_⟩
  rcases valid with ⟨rfl, rfl⟩
  exact ⟨rfl, .store 23 .vector256 home _ 1 (by simp [segmentStores]) slot written⟩

#print axioms framed_store

/-- A frame-rule placement must belong to the running method and match its end boundary. -/
theorem framing_boundaries {program : CIL.Program} {method start : Nat}
    {body other : CIL.Method} (found : program[method]? = some body)
    (_wrongBody : CodeAt other start [.stloc 23])
    (placed : CodeAt body start [.stloc 23])
    {entered initial : Memory} {boundary : Nat} {kinds : List CIL.LocalKind}
    {slots : List LocalSlot} {known : Nat → Option CIL.Value}
    {pre post : List Value → SegmentState → Prop}
    (homes : WritableHomes entered boundary kinds slots)
    (snapshots : LocalSnapshots initial slots known)
    (contract : Segment program method start (start + 1) pre fun arguments state =>
      post arguments state ∧ state.frame.locals = slots ∧
        SegmentLocalEffects body [.stloc 23] slots initial state.memory)
    (_wrongEnd : Segment program method start (start + 2) pre fun arguments state =>
      post arguments state ∧ state.frame.locals = slots ∧
        SegmentLocalEffects body [.stloc 23] slots initial state.memory) :
    Segment program method start (start + 1) pre fun arguments state =>
      post arguments state ∧ LocalSnapshots state.memory state.frame.locals
        (untouchedLocals body [.stloc 23] known) := by
  fail_if_success
    have := Segment.frameLocals found _wrongBody rfl homes snapshots contract
  fail_if_success
    have := Segment.frameLocals found placed (by omega) homes snapshots _wrongEnd
  exact Segment.frameLocals found placed rfl homes snapshots contract
#print axioms framing_boundaries

end Tests.Segment
