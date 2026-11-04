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
  obtain ⟨after, wrote, formed, confined, filled⟩ := writable.write_one value
  refine ⟨8, after, [], ?_, confined, (), rfl, filled⟩
  cil_checked_steps [step_storeScalar_of_write wrote, formed]

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
  · simp [cil_checked, valid, formed]
  · cil_loop_recurse start (⟨view, values, ⟨valid, readOnly, contents⟩⟩, 0, 0)
    exact ⟨[], by simp, by simp, rfl, ⟨Contents.nil, writable⟩, apart⟩
  rintro ⟨⟨⟨suffix, remaining, span⟩, count, last⟩, current, frame⟩
    ⟨done, split, nonzero, counted, filled, spanApart⟩ recurse
  dsimp only at split counted filled spanApart
  cases remaining with
  | nil =>
    simp only [List.append_nil] at split
    subst split
    have whole : copied values = values := by simpa [copied] using copied_append nonzero []
    have answer : result values = count := by
      simp only [result, whole, nonzero, ite_false, ← counted, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
    cil_loop_finish [answer]
    simpa [whole] using filled.1
  | cons value rest =>
    obtain ⟨item, -, found, element⟩ := (span.within wellFormed frame).head (by decide)
    by_cases zero : value = 0
    · subst zero
      have whole : copied values = done := by
        rw [split, copied_append nonzero]
        simp [copied]
      have answer : result values = count ||| 0x80000000 := by
        unfold result
        rw [whole, ← counted, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        simp [split]
      cil_loop_finish [answer]
      simpa [whole] using filled.1
    · have room : (copied (value :: rest)).length = (copied rest).length + 1 := by
        simp -bitVecOfNat [copied, zero]
      have short := contents.length ▸ SpanView.length_bounded view memory valid
      have lengths : done.length + 1 + rest.length = values.length := by simp [split]; omega
      have total : (copied values).length = done.length + (copied (value :: rest)).length := by
        rw [split, copied_append nonzero, List.length_append]
      have offset := writable.add_int wellFormed formed
        (index := count) (by omega) (by omega) (by omega)
      have slot := filled.2.sub (index := count.toNat) (length := 1) (by omega) (by omega)
      obtain ⟨sliced, cut, next⟩ := span.tail
      cil_loop_advance
      cil_loop_call stamp_holds (output.element 4 count.toNat, value) at stampSite
      cil_loop_recurse recurse (⟨sliced, rest, next⟩, count + 1, value)
      case invariant =>
        refine ⟨done ++ [value], by simp [split], by simpa using ⟨nonzero, Ne.symm zero⟩, ?_,
          (room ▸ filled).extend returned counted, spanApart.slice cut⟩
        simp only [List.length_append, List.length_singleton, ← counted, BitVec.toNat_add]
        simp
        omega
      case measure => simp
#print axioms correctness

end ExampleProof
