import CIL.Safety.CallingFields
import CIL.Safety.LoopFrames

/-!
# Checked by-reference field evidence

These fixtures take two four-word inputs and a writable output, with arbitrary overlap.
The stepper obtains field reads and formed references from `ValidCall` itself.
-/

namespace Tests.CallingFields
open CIL.Safety

/-- A four-word argument range. -/
def words (reference : Reference) : ArgumentView := ⟨reference, 32⟩

/-- Read every input field before any output could be written. -/
@[cil_code] def reader : CIL.Method :=
  { locals := [], returnsValue := true, code := [
    .arg 2, .skipInit,
    .arg 0, .fieldAt 0 8, .arg 1, .fieldAt 0 8, .add,
    .arg 0, .fieldAt 8 8, .arg 1, .fieldAt 8 8, .add, .add,
    .arg 0, .fieldAt 16 8, .arg 1, .fieldAt 16 8, .add, .add,
    .arg 0, .fieldAt 24 8, .arg 1, .fieldAt 24 8, .add, .add, .ret] }

/-- Field evidence is gathered with no per-field hypotheses or stepper arguments. -/
theorem reads_four_words (memory : Memory) (left right output : Reference)
    (call : ValidCall memory [words left, words right] [words output]) :
    WP (fun fuel => invoke [reader] fuel 0
      [.reference (.address left), .reference (.address right), .reference (.address output)] memory)
      (fun final values => final = memory ∧ values = [.scalar (.i64 (
        ((words left).word memory 0 + (words right).word memory 0) +
        ((words left).word memory 8 + (words right).word memory 8) +
        ((words left).word memory 16 + (words right).word memory 16) +
        ((words left).word memory 24 + (words right).word memory 24)))]) := by
  cil_contract_steps []
  exact ⟨rfl, rfl⟩

#print axioms reads_four_words

/-- The same proof allows the output to be exactly the left input. -/
theorem overlapping_read (memory : Memory) (left right : Reference)
    (call : ValidCall memory [words left, words right] [words left]) :
    WP (fun fuel => invoke [reader] fuel 0
      [.reference (.address left), .reference (.address right), .reference (.address left)] memory)
      (fun final _ => final = memory) :=
  (reads_four_words memory left right left call).consequence (fun _ _ result => result.1)

#print axioms overlapping_read

/-- Sum all input words and write the result only after reading every input. -/
@[cil_code] def writer : CIL.Method :=
  { locals := [], returnsValue := false,
    code := [.arg 2] ++ reader.code.dropLast ++ [.store64, .ret] }

/-- The checksum uses the original input snapshots, including when output overlaps an input. -/
def checksum (memory : Memory) (left right : Reference) : CIL.W64 :=
  ((words left).word memory 0 + (words right).word memory 0) +
  ((words left).word memory 8 + (words right).word memory 8) +
  ((words left).word memory 16 + (words right).word memory 16) +
  ((words left).word memory 24 + (words right).word memory 24)

/-- Output requires write access, not initial contents or separation from either input. -/
theorem writes_after_reads (memory : Memory) (left right output : Reference)
    (call : ValidCall memory [words left, words right] [words output]) :
    WP (fun fuel => invoke [writer] fuel 0
      [.reference (.address left), .reference (.address right), .reference (.address output)] memory)
      (fun final values => values = [] ∧
        read final output 8 1 = .ok (numberBytes (checksum memory left right).toNat 8) ∧
        ValidCall final [words left, words right] [words output]) := by
  have ready : access memory output 8 1 true = .ok () := by
    simpa only [words, Nat.add_zero] using
      call.output_slice (words output) (by simp) 0 8 (by decide) (by simp [words])
  obtain ⟨final, written, _, readback⟩ := store_word64 (checksum memory left right) ready
  have stored := step_store64_of_write written
  simp only [checksum, words] at stored
  cil_contract_steps [stored]
  exact ⟨rfl, readback, call.after_write written⟩

#print axioms writes_after_reads

end Tests.CallingFields
