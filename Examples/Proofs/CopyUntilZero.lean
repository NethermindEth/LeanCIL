import Extracted
import CIL.Verification
import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.LoopScaffold
import CIL.Safety.LoopFrames
import CIL.Safety.SpanContents

/-! `CopyUntilZero` copies the words of a readonly span before its first zero to a caller
    buffer through the `Stamp` helper, and returns their count with bit 31 set when a zero ended
    the copy. The proof covers every span length and contents, uses only `Stamp`'s contract at the
    call, and shows the method changes no caller byte outside the copied words. -/

open CIL.Safety
open CIL (W32)
namespace ExampleProof

bind_method copy copyBody :=
  "System.UInt32 Examples.Loops::CopyUntilZero(System.ReadOnlySpan`1<System.UInt32>,System.UInt32&)"
bind_callee stamp stampBody := "System.Void Examples.Loops::Stamp(System.UInt32&,System.UInt32)"
  from copyBody
bind_call stampSite := stamp from copyBody

/-- A reference with checked access is well formed. -/
theorem form_of_access {memory : Memory} {reference : Reference} {width alignment : Nat}
    {writing : Bool} (accessible : access memory reference width alignment writing = .ok ()) :
    form memory reference = .ok reference := by
  cases formed : form memory reference with
  | error fault => simp [access, formed, Bind.bind, Except.bind] at accessible
  | ok result => rw [form_returns_input _ _ _ formed]

/-- `Stamp` stores one word at `slot`, given write authority over it, and touches nothing else. -/
def stampContract : MethodContract (Reference × W32) Unit where
  args input := [.reference (.address input.1), .scalar (.i32 input.2)]
  results _ := []
  pre input memory := Writable memory input.1 4 0 1
  footprint input := [(input.1, 4)]
  post input _ final _ := Contents final input.1 4 [input.2]

/-- `Stamp` meets its contract; the caller proof below never unfolds its body. -/
theorem stamp_holds : stampContract.Holds Extracted.program stamp := by
  rintro ⟨slot, value⟩ memory writable
  dsimp only [stampContract] at writable ⊢
  have formed := form_of_access (by simpa using writable 0 (by decide))
  obtain ⟨after, wrote⟩ := writable.write_succeeds (value : BitVec (8 * 4))
  have filled :=
    ((Filled.start writable).push (x := (value : BitVec (8 * 4))) (by simpa using wrote)).complete
  have wrote : write memory slot (numberBytes value.toNat 4) 1 = .ok after := by simpa using wrote
  refine ⟨8, after, [], ?_, Confined.write wrote (by simp), (), rfl, by simpa using filled⟩
  have stored : ∀ body pc args frame rest, step body (.storeScalar 4) pc args frame
      (.scalar (.i32 value) :: .reference (.address slot) :: rest) memory =
        .ok (.next (pc + 1) rest frame after) := by
    intro body pc args frame rest
    rw [step_storeScalar_i32_4_eq]
    simp [referenceAt, checkedAt, ordinaryAccessAlignment, wrote, Bind.bind, Except.bind,
      Pure.pure, Except.pure, Except.mapError]
  cil_checked_steps [stored, formed]

/-- The words copied: those before the first zero, or all of them. -/
def copied (values : List W32) : List W32 := values.takeWhile (· ≠ 0)

/-- The count of copied words, with bit 31 set exactly when a zero ended the copy. -/
def result (values : List W32) : W32 :=
  let count := BitVec.ofNat 32 (copied values).length
  if (0 : W32) ∈ values then count ||| 0x80000000 else count

/-- Copying is unaffected by a nonzero prefix. -/
theorem copied_append {done : List W32} (nonzero : (0 : W32) ∉ done) (rest : List W32) :
    copied (done ++ rest) = done ++ copied rest :=
  List.takeWhile_append_of_pos fun word mem => by
    simpa using fun same : word = 0 => nonzero (same ▸ mem)

/-- An addressed view's bytes share none with `entry`. -/
def SpanApart (view : SpanView) (entry : Reference × Nat) : Prop :=
  ∀ base, view.reference = .address base → Apart base (4 * view.length) entry

/-- A successful slice depends on memory only through the validity of both views. -/
theorem slice_moved {view sliced : SpanView} {before after : Memory} {start length : Nat}
    (cut : view.slice before start length = .ok sliced)
    (viewValid : view.validate after = .ok ()) (slicedValid : sliced.validate after = .ok ()) :
    view.slice after start length = .ok sliced := by
  have viewBefore := view.slice_valid sliced before start length cut
  unfold SpanView.slice at cut ⊢
  by_cases fits : (decide (start ≤ view.length) && decide (length ≤ view.length - start)) = true
  · cases reference : view.reference <;>
      simp only [reference, fits, viewValid, ite_true, Bind.bind, Except.bind, Pure.pure,
        Except.pure] at cut ⊢ <;>
      split at cut <;> (try contradiction) <;> split at cut <;> (try contradiction) <;>
      (cases cut; simp only [slicedValid])
  · simp only [fits, Bool.false_eq_true, ite_false, Bind.bind, Except.bind] at cut
    split at cut <;> contradiction

/-- A checked span stays checked across changes confined away from its bytes. -/
theorem span_after_confined {caller current : Memory} {view : SpanView}
    {words : List W32} {entry : Reference × Nat}
    (span : CheckedSpan caller view 4 false words) (formed : caller.WellFormed)
    (confined : Confined [entry] caller current) (apart : SpanApart view entry) :
    CheckedSpan current view 4 false words := by
  refine ⟨view.validate_preserved span.valid formed ⟨confined.grows, confined.allocations⟩,
    span.mode, span.contents.elementWidth, span.contents.length, ?_⟩
  have held := span.contents.contents
  revert held
  cases reference : view.reference with
  | null => exact id
  | address base =>
    intro held
    refine held.after_confined confined formed ?_
    simpa [span.contents.length] using apart base reference

bind_entry entry (memory : Memory) (view : SpanView) (output : Reference)
    (wellFormed : memory.WellFormed) (valid : view.validate memory = .ok ())
    (width : view.width = 4) (readOnly : view.writable = false) := copyBody
  with [.bufferSpan view, .reference (.address output)] from memory allocating wellFormed
  simplifying [valid, width, readOnly]
bind_loop loop := copyBody

/-- The unread suffix, the copied count and the last word read, with the frame facts. -/
private abbrev State (memory : Memory) (output : Reference) (room : Nat)
    (home0 home1 : Reference) :=
  FrameState [(output, 4 * room)] memory [.aggregate 8, .word32, .span 4 false]
    (SpanSuffix memory 4 false × W32 × W32)
    (fun state => [.bytes (.aggregate 8) home0, .bytes .word32 home1,
      .span 4 false (some state.1.view)])
    fun state => [some (.aggregate (Extracted.layout0.encode [.i32 state.2.1, .i32 0])),
      some (.i32 state.2.2), none]

-- The loop guard observes the remaining span length.
bind_cutpoint header (memory : Memory) (output : Reference) (room : Nat)
    (home0 home1 : Reference) (state : State memory output room home0 home1) :=
  copyBody at loop.latch matching (· matches .brnonzero _)
  with entry.frame memory state.values.1.view home0 home1,
    [.scalar (.i32 (BitVec.ofNat 32 state.values.1.view.length))], state.memory

/-- The words read so far are nonzero, counted, and stored at the start of `output`. -/
def Invariant (values : List W32) (output : Reference) {memory : Memory} {room : Nat}
    {home0 home1 : Reference} (state : State memory output room home0 home1) : Prop :=
  ∃ done, values = done ++ state.values.1.values ∧ (0 : W32) ∉ done ∧
    state.values.2.1.toNat = done.length ∧
    Filled state.memory output 4 done (copied state.values.1.values).length ∧
    SpanApart state.values.1.view (output, 4 * room)

/-- For every valid readonly span and every output with write authority over the words it will
    receive, apart from the span, `CopyUntilZero` returns `result values`, leaves `copied values`
    at `output`, and changes no caller memory outside those words. -/
theorem correctness (memory : Memory) (view : SpanView) (values : List W32) (output : Reference)
    (wellFormed : memory.WellFormed) (valid : view.validate memory = .ok ())
    (readOnly : view.writable = false) (contents : SpanContents memory view 4 values)
    (formed : form memory output = .ok output)
    (writable : Writable memory output 4 0 (copied values).length)
    (apart : SpanApart view (output, 4 * (copied values).length)) :
    ∃ fuel final, invoke Extracted.program fuel copy
        [.bufferSpan view, .reference (.address output)] memory =
      .ok (final, [.scalar (.i32 (result values))]) ∧
      Contents final output 4 (copied values) ∧
      Confined [(output, 4 * (copied values).length)] memory final := by
  obtain ⟨home0, home1, entered, setup, -, -, -, entryFrame⟩ :=
    entry.checked memory view output wellFormed valid contents.elementWidth readOnly
  refine invoke_loop_induction copy.found ?_ setup
    (header memory output (copied values).length home0 home1) (Invariant values output)
    (·.values.1.values.length) (fun start => ?_) ?_
  · simp [cil_checked, valid, checkedValue, formValue, checkedAt, formed, Except.mapError,
      Pure.pure, Except.pure]
  · obtain ⟨zeroed, zeroStep, zeroFrame, -⟩ :=
      (entryFrame [(output, 4 * (copied values).length)]).zero_aggregate 0 Extracted.layout0
        [.i32 0, .i32 0]
    have zeroValid := view.validate_preserved valid wellFormed
      ⟨zeroFrame.confined.grows, zeroFrame.confined.allocations⟩
    have zeroLoad := entry.load2 zeroed view zeroValid contents.elementWidth readOnly
    cil_loop_recurse start (⟨view, values, ⟨valid, readOnly, contents⟩⟩, 0, 0)
    exact ⟨[], by simp, by simp, rfl,
      ⟨Contents.nil, writable.after_confined zeroFrame.confined wellFormed⟩, apart⟩
  rintro ⟨⟨⟨suffix, remaining, span⟩, count, last⟩, current, frame⟩
    ⟨done, split, nonzero, counted, filled, spanApart⟩ recurse
  dsimp only at split counted filled spanApart
  have now := span_after_confined span wellFormed frame.confined spanApart
  have old := wellFormed.form_bound formed
  cases remaining with
  | nil =>
    simp only [List.append_nil] at split
    subst split
    have whole : copied values = values := by
      simpa [copied] using copied_append nonzero []
    obtain ⟨framed, below⟩ := frame.leave setup
    have kept := filled.1.after_below below old
    have answer : result values = count := by
      simp only [result, whole, nonzero, ite_false, ← counted, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
    cil_loop_finish
    exact loop_terminates_return copy.found (by first | (simp only [cil_code]; rfl) | rfl)
      (by cil_checked_step [CIL.truth]) rfl
      ⟨⟨by simpa [whole, leaveFrame, entry.frame] using kept, framed⟩, by rw [answer]⟩
  | cons value rest =>
    obtain ⟨item, -, found, element⟩ := now.head (by decide)
    obtain ⟨m1, stored1, frame1, below1⟩ := frame.store 1 (.i32 value) rfl
    by_cases zero : value = 0
    · subst zero split
      have whole : copied (done ++ 0 :: rest) = done := by
        rw [copied_append nonzero]
        simp [copied]
      obtain ⟨m2, stored2, frame2, below2⟩ :=
        frame1.store_field 0 Extracted.layout0_valid 1 (.i32 1)
      obtain ⟨framed, below⟩ := frame2.leave setup
      have kept :=
        ((filled.1.after_below below1 old).after_below below2 old).after_below below old
      have answer : result (done ++ 0 :: rest) = count ||| 2147483648#32 := by
        unfold result
        rw [whole, ← counted, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        simp
      cil_loop_finish
      exact loop_terminates_return copy.found (by first | (simp only [cil_code]; rfl) | rfl)
        (by cil_checked_step [CIL.truth]) rfl
        ⟨⟨by rw [whole]; simpa [leaveFrame, entry.frame] using kept,
          by simpa [leaveFrame, entry.frame] using framed⟩, by rw [answer]⟩
    · have room : (copied (value :: rest)).length = 1 + (copied rest).length := by
        have nz : ¬value = 0#32 := zero
        simp [copied, nz, Nat.add_comm]
      have short : values.length < 2 ^ 31 :=
        contents.length ▸ SpanView.length_bounded view memory valid
      have lengths : done.length + 1 + rest.length = values.length := by
        simp [split]; omega
      obtain ⟨here, later⟩ := Writable.append.mp (room ▸ filled.2)
      have here1 := here.after_below below1 old
      have form1 := frame1.form formed old
      have access1 : access m1 (output.element 4 count.toNat) 4 1 true = .ok () := by
        simpa [counted] using here1 0 (by decide)
      have offset := add_int_element frame1.wellFormed form1 (by omega) access1
      cil_loop_advance [offset]
      have slotForm := form_of_access access1
      have total : (copied values).length = done.length + (copied (value :: rest)).length := by
        rw [split, copied_append nonzero, List.length_append]
      have inside : ∀ entry ∈ stampContract.footprint (output.element 4 count.toNat, value),
          ∃ outer, outer ∈ [(output, 4 * (copied values).length)] ∧ Within entry outer := by
        intro entry mem
        simp only [stampContract, List.mem_singleton] at mem
        subst mem
        refine ⟨_, List.mem_singleton_self _, rfl, ?_, ?_⟩ <;> simp only [Reference.element] <;>
          omega
      have older : ∀ entry ∈ stampContract.footprint (output.element 4 count.toNat, value),
          entry.1.allocation < memory.nextIdentity := by
        simpa [stampContract, Reference.element] using old
      -- The call goes through `stampContract` alone; its footprint lies in the frame's.
      cil_loop_call stamp_holds (output.element 4 count.toNat, value) at stampSite [slotForm]
      · intro index small
        have one := here1 index small
        simp only [Reference.element, counted] at one ⊢
        simpa [Nat.mul_add, Nat.add_assoc] using one
      have calledWF := invoke_preserves_wellFormed _ _ _ _ _ _ _ frame1.wellFormed invoked
      have calledFrame := frame1.after_confined confined calledWF inside older
      simp only [List.set, localResult] at calledFrame
      obtain ⟨m3, stored3, frame3, below3⟩ :=
        calledFrame.store_field 0 Extracted.layout0_valid 0 (.i32 (count + 1))
      obtain ⟨sliced, cut, nextSpan⟩ := span.tail
      have slicedApart : SpanApart sliced (output, 4 * (copied values).length) := by
        intro base' reference'
        cases reference : suffix.reference with
        | null =>
          have bad := span.valid
          simp [SpanView.validate, reference, span.contents.length,
            span.contents.elementWidth] at bad
          split at bad <;> simp [Bind.bind, Except.bind] at bad
        | address base =>
          rw [SpanView.slice_reference suffix sliced memory 1 _ base reference cut] at reference'
          cases reference'
          have whole := spanApart base reference
          rw [span.contents.length] at whole
          rw [nextSpan.contents.length, span.contents.elementWidth]
          simpa using whole.sub (start := 4) (count := 4 * rest.length) (by simp; omega)
      have now3 := span_after_confined span wellFormed frame3.confined spanApart
      have next3 := span_after_confined nextSpan wellFormed frame3.confined slicedApart
      have cut3 := slice_moved cut now3.valid next3.valid
      have store4 := entry.store2 m3 (some suffix) sliced next3.valid next3.contents.elementWidth
        next3.mode
      have load4 := entry.load2 m3 sliced next3.valid next3.contents.elementWidth next3.mode
      have frame4 : LoopFrame [(output, 4 * (copied values).length)] memory m3
          [.aggregate 8, .word32, .span 4 false]
          [.bytes (.aggregate 8) home0, .bytes .word32 home1, .span 4 false (some sliced)]
          (knownLocals [some (.aggregate (Extracted.layout0.encode [.i32 (count + 1), .i32 0])),
            some (.i32 value), none]) := by
        simpa [List.set] using frame3.set_local 2 (.span 4 false (some sliced))
      refine loop_reaches_terminates (target := header memory output (copied values).length
        home0 home1 ⟨(⟨sliced, rest, nextSpan⟩, count + 1, value), m3, frame4⟩) ?_
        (recurse _ ?_ ?_)
      · cil_loop_steps [stored3, store4, load4, cut3]
      · refine ⟨done ++ [value], by simp [split], by
          simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨nonzero, fun same => zero same.symm⟩, ?_, ?_,
          slicedApart⟩
        · simp only [List.length_append, List.length_singleton, ← counted]
          rw [BitVec.toNat_add]
          simp
          omega
        · have apartSlot :
              ∀ entry ∈ stampContract.footprint (output.element 4 count.toNat, value),
                Apart output (4 * done.length) entry := by
            intro entry mem
            simp only [stampContract, List.mem_singleton] at mem
            subst mem
            right; left
            simp only [Reference.element]
            omega
          have prefix3 : Contents m3 output 4 done :=
            (((filled.1.after_below below1 old).after_confined confined frame1.wellFormed
              apartSlot).after_below below3 old)
          have slot3 : Contents m3 (output.element 4 done.length) 4 [value] := by
            have moved := returned.after_below below3 (by simpa [Reference.element] using old)
            simpa [counted] using moved
          have room3 : Writable m3 output 4 (done.length + 1) (copied rest).length :=
            ((later.after_below below1 old).after_confined confined frame1.wellFormed).after_below
              below3 old
          exact ⟨Contents.append.mpr ⟨prefix3, slot3⟩, by simpa using room3⟩
      · simp
#print axioms correctness

end ExampleProof
