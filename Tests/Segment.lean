import CIL.Safety.SegmentLocals

/-!
# Composable placed-segment contracts

Checked prefixes are composed through exact intermediate states. The vector-input slices
mirror UInt256 Add's reference prefix and Multiply's AVX input loads; placements, formation
and successful memory operations remain explicit premises.
-/

namespace Tests.Segment
open CIL.Safety

/-- The argument formation sequence used by the vector input prefixes. -/
def referencePrefix (index : Nat) : List CIL.Op :=
  [.arg index, .memory .asRef, .memory .asRef]

/-- Argument formation is a reusable segment at any placed position. -/
theorem reference_prefix {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body) (index : Nat)
    (placed : CodeAt body start (referencePrefix index))
    (arguments : List Value) (frame : Frame) (stack : List Value)
    (memory : Memory) (reference : Reference)
    (argument : arguments[index]? = some (.reference (.address reference)))
    (formed : form memory reference = .ok reference) :
    Segment program method start (start + 3)
      (SegmentState.exact arguments ⟨frame, stack, memory⟩)
      (SegmentState.exact arguments ⟨frame, .reference (.address reference) :: stack, memory⟩) := by
  cil_segment 3 [found, placed, argument, formed]

#print axioms reference_prefix

/-- Saving the right reference and duplicating the left finishes Add's eight-op prefix. -/
theorem save_right {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body)
    (placed : CodeAt body start [.setLocal 0, .dup])
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
    (placed : CodeAt body 0 (referencePrefix 0 ++ referencePrefix 1 ++ [.setLocal 0, .dup]))
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
  have first := reference_prefix found 0 placed.append_left.append_left arguments frame []
    memory left leftArgument leftFormed
  have second := reference_prefix found 1 placed.append_left.append_right arguments frame
    [.reference (.address left)] memory right rightArgument rightFormed
  have third := save_right found placed.append_right arguments frame slots initial memory
    left right layout rightFormed
  exact (first.trans second).trans third

#print axioms add_vector128_inputs



/-- A placed input-reference formation and Vector256 load uses the original checked read. -/
theorem load256_prefix {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body) (index : Nat)
    (placed : CodeAt body start (referencePrefix index ++ [.memory .load256]))
    (arguments : List Value) (frame : Frame) (memory : Memory) (reference : Reference)
    (vector : BitVec 256)
    (argument : arguments[index]? = some (.reference (.address reference)))
    (formed : form memory reference = .ok reference)
    (loaded : loadValue memory (.address reference) 32 = .ok (.v256 vector)) :
    Segment program method start (start + 4)
      (SegmentState.exact arguments ⟨frame, [], memory⟩)
      (SegmentState.exact arguments ⟨frame, [.scalar (.v256 vector)], memory⟩) := by
  cil_segment 4 [found, placed, argument, formed, loaded]

#print axioms load256_prefix

/-- One local store retains its actual checked step equation and memory transition. -/
theorem store256 {program : CIL.Program} {method start index : Nat} {body : CIL.Method}
    (found : program[method]? = some body) (placed : CodeAt body start [.setLocal index])
    (arguments : List Value) (frame : Frame) (before after : Memory) (vector : BitVec 256)
    (stored : step body (.setLocal index) start arguments frame [.scalar (.v256 vector)] before =
      .ok (.next (start + 1) [] frame after)) :
    Segment program method start (start + 1)
      (SegmentState.exact arguments ⟨frame, [.scalar (.v256 vector)], before⟩)
      (SegmentState.exact arguments ⟨frame, [], after⟩) := by
  cil_segment 1 [found, placed, stored]

#print axioms store256

/-- The Multiply AVX2 left-input stage composes load and store at the original positions. -/
theorem multiply_left_input {program : CIL.Program} {method : Nat} {body : CIL.Method}
    (found : program[method]? = some body)
    (placed : CodeAt body 44 (referencePrefix 0 ++ [.memory .load256, .setLocal 23]))
    (arguments : List Value) (frame : Frame) (before after : Memory) (left : Reference)
    (vector : BitVec 256)
    (argument : arguments[0]? = some (.reference (.address left)))
    (formed : form before left = .ok left)
    (loaded : loadValue before (.address left) 32 = .ok (.v256 vector))
    (stored : step body (.setLocal 23) 48 arguments frame [.scalar (.v256 vector)] before =
      .ok (.next 49 [] frame after)) :
    Segment program method 44 49 (SegmentState.exact arguments ⟨frame, [], before⟩)
      (SegmentState.exact arguments ⟨frame, [], after⟩) := by
  have split : CodeAt body 44 ((referencePrefix 0 ++ [.memory .load256]) ++ [.setLocal 23]) :=
    placed
  exact (load256_prefix found 0 split.append_left arguments frame before left vector
    argument formed loaded).trans
      (store256 found split.append_right arguments frame before after vector stored)

#print axioms multiply_left_input


/-- The AVX2 permutation stage retains availability and exact intrinsic semantics. -/
theorem reverse256 {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body)
    (placed : CodeAt body start [.const32 27, .intrinsic (.avx2 .permute4x64) 2])
    (arguments : List Value) (frame : Frame) (memory : Memory) (vector reversed : BitVec 256)
    (available : (CIL.Intrinsic.avx2 .permute4x64).available body.profile = true)
    (permuted : checkedIntrinsic (.avx2 .permute4x64) [.v256 vector, .i32 27] =
      .ok (.v256 reversed)) :
    Segment program method start (start + 2)
      (SegmentState.exact arguments ⟨frame, [.scalar (.v256 vector)], memory⟩)
      (SegmentState.exact arguments ⟨frame, [.scalar (.v256 reversed)], memory⟩) := by
  apply Segment.ofRun (cost := 2)
  have reversedStep : step body (.intrinsic (.avx2 .permute4x64) 2) (start + 1)
      arguments frame [.scalar (.i32 27), .scalar (.v256 vector)] memory =
      .ok (.next (start + 2) [.scalar (.v256 reversed)] frame memory) := by
    rw [step_intrinsic_eq]
    simp only [available, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    change (do
      let value ← checkedIntrinsic (.avx2 .permute4x64) [.v256 vector, .i32 27]
      let checked ← checkedValue memory (.scalar value)
      pure (FrameAction.next (start + 2) [checked] frame memory)) = _
    rw [permuted]
    rfl
  cil_segment_steps [found, placed, reversedStep]

#print axioms reverse256

/-- Multiply's two vector input stages compose through the checked intermediate memory. -/
theorem multiply_inputs {program : CIL.Program} {method : Nat} {body : CIL.Method}
    (found : program[method]? = some body)
    (leftPlaced : CodeAt body 44 (referencePrefix 0 ++ [.memory .load256, .setLocal 23]))
    (rightPlaced : CodeAt body 49 (referencePrefix 1 ++ [.memory .load256,
      .const32 27, .intrinsic (.avx2 .permute4x64) 2, .setLocal 24]))
    (arguments : List Value) (frame : Frame) (before middle after : Memory)
    (left right : Reference) (leftVector rightVector reversed : BitVec 256)
    (leftArgument : arguments[0]? = some (.reference (.address left)))
    (rightArgument : arguments[1]? = some (.reference (.address right)))
    (leftFormed : form before left = .ok left) (rightFormed : form middle right = .ok right)
    (leftLoaded : loadValue before (.address left) 32 = .ok (.v256 leftVector))
    (rightLoaded : loadValue middle (.address right) 32 = .ok (.v256 rightVector))
    (leftStored : step body (.setLocal 23) 48 arguments frame [.scalar (.v256 leftVector)] before =
      .ok (.next 49 [] frame middle))
    (rightStored : step body (.setLocal 24) 55 arguments frame [.scalar (.v256 reversed)] middle =
      .ok (.next 56 [] frame after))
    (available : (CIL.Intrinsic.avx2 .permute4x64).available body.profile = true)
    (permuted : checkedIntrinsic (.avx2 .permute4x64) [.v256 rightVector, .i32 27] =
      .ok (.v256 reversed)) :
    Segment program method 44 56 (SegmentState.exact arguments ⟨frame, [], before⟩)
      (SegmentState.exact arguments ⟨frame, [], after⟩) := by
  have first := multiply_left_input found leftPlaced arguments frame before middle left
    leftVector leftArgument leftFormed leftLoaded leftStored
  have split : CodeAt body 49 (((referencePrefix 1 ++ [.memory .load256]) ++
      [.const32 27, .intrinsic (.avx2 .permute4x64) 2]) ++ [.setLocal 24]) := rightPlaced
  have loaded := load256_prefix found 1 split.append_left.append_left arguments frame middle
    right rightVector rightArgument rightFormed rightLoaded
  have reversed := reverse256 found split.append_left.append_right arguments frame middle
    rightVector reversed available permuted
  have stored := store256 found split.append_right arguments frame middle after _ rightStored
  exact ((first.trans loaded).trans reversed).trans stored

#print axioms multiply_inputs








/-- Two actual vector stores preserve every other remembered local in one frame-rule use. -/
theorem multiply_untouched {before middle after entered : Memory} {boundary : Nat}
    {kinds : List CIL.LocalKind} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} {leftHome rightHome : Reference}
    (homes : WritableHomes entered boundary kinds slots)
    (snapshots : LocalSnapshots before slots known)
    (leftSlot : slots[23]? = some (.bytes .vector256 leftHome))
    (rightSlot : slots[24]? = some (.bytes .vector256 rightHome))
    (leftVector rightVector : BitVec 256)
    (leftWritten : write before leftHome (numberBytes leftVector.toNat 32) 1 = .ok middle)
    (rightWritten : write middle rightHome (numberBytes rightVector.toNat 32) 1 = .ok after) :
    LocalSnapshots after slots (untouchedLocals [.setLocal 23, .setLocal 24] known) := by
  have first : SegmentLocalEffects [.setLocal 23] slots before middle :=
    .store 23 .vector256 leftHome _ 1 (by simp [segmentStores]) leftSlot leftWritten
  have second : SegmentLocalEffects [.setLocal 24] slots middle after :=
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
theorem no_hidden_write {slots : List LocalSlot} {before after : Memory}
    (effects : SegmentLocalEffects [.store64] slots before after) : before = after := by
  induction effects with
  | refl => rfl
  | store index kind home bytes alignment destination => simp [segmentStores] at destination
  | trans _ _ first second => exact first.trans second

#print axioms no_hidden_write

/-- A declared destination cannot preserve its own old snapshot through the frame mask. -/
theorem stored_local_not_framed (known : Nat → Option CIL.Value) :
    untouchedLocals [.setLocal 23, .setLocal 24] known 23 = none ∧
      untouchedLocals [.setLocal 23, .setLocal 24] known 7 = known 7 := by
  simp [untouchedLocals, segmentStores]

#print axioms stored_local_not_framed

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
    (_found : program[method]? = some body) (_placed : CodeAt body 0 [.arg 0])
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
    (found : program[method]? = some body) (placed : CodeAt body start [.setLocal 23])
    (arguments : List Value) (frame : Frame) (before after entered : Memory)
    (boundary : Nat) (kinds : List CIL.LocalKind) (home : Reference) (vector : BitVec 256)
    (known : Nat → Option CIL.Value)
    (homes : WritableHomes entered boundary kinds frame.locals)
    (snapshots : LocalSnapshots before frame.locals known)
    (slot : frame.locals[23]? = some (.bytes .vector256 home))
    (written : write before home (numberBytes vector.toNat 32) 1 = .ok after)
    (stored : step body (.setLocal 23) start arguments frame [.scalar (.v256 vector)] before =
      .ok (.next (start + 1) [] frame after)) :
    Segment program method start (start + 1)
      (SegmentState.exact arguments ⟨frame, [.scalar (.v256 vector)], before⟩)
      (fun actual state => SegmentState.exact arguments ⟨frame, [], after⟩ actual state ∧
        LocalSnapshots state.memory state.frame.locals (untouchedLocals [.setLocal 23] known)) := by
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
    (_wrongBody : CodeAt other start [.setLocal 23])
    (placed : CodeAt body start [.setLocal 23])
    {entered initial : Memory} {boundary : Nat} {kinds : List CIL.LocalKind}
    {slots : List LocalSlot} {known : Nat → Option CIL.Value}
    {pre post : List Value → SegmentState → Prop}
    (homes : WritableHomes entered boundary kinds slots)
    (snapshots : LocalSnapshots initial slots known)
    (contract : Segment program method start (start + 1) pre fun arguments state =>
      post arguments state ∧ state.frame.locals = slots ∧
        SegmentLocalEffects [.setLocal 23] slots initial state.memory)
    (_wrongEnd : Segment program method start (start + 2) pre fun arguments state =>
      post arguments state ∧ state.frame.locals = slots ∧
        SegmentLocalEffects [.setLocal 23] slots initial state.memory) :
    Segment program method start (start + 1) pre fun arguments state =>
      post arguments state ∧ LocalSnapshots state.memory state.frame.locals
        (untouchedLocals [.setLocal 23] known) := by
  fail_if_success
    have := Segment.frameLocals found _wrongBody rfl homes snapshots contract
  fail_if_success
    have := Segment.frameLocals found placed (by omega) homes snapshots _wrongEnd
  exact Segment.frameLocals found placed rfl homes snapshots contract
#print axioms framing_boundaries

end Tests.Segment
