import Extracted
import CIL.Safety.MethodContract
import CIL.Safety.BufferContents

/-!
# Contract for `MemoryMarshal.GetReference` over a readonly span reference

`SpanReferences::Word(in ReadOnlySpan<ulong>)` dereferences `MemoryMarshal.GetReference` of its
readonly view. The reference it obtains is readonly-restricted, and the ordinary symbolic span
contents prove the load of the first element.
-/

namespace Tests.SpanReferenceWordContract
open CIL CIL.Safety

/-- A word sequence in caller storage whose first word a caller names. -/
structure WordInput where
  base : Reference
  words : List (BitVec (8 * 8))
  first : BitVec (8 * 8)

/-- The readonly view of the complete input sequence. -/
def WordInput.view (input : WordInput) : SpanView :=
  ⟨.address input.base, input.words.length, 8, false⟩

/-- Dereferencing the start of a nonempty readonly view returns its first word and changes
    nothing. -/
def wordContract : MethodContract WordInput (BitVec (8 * 8)) where
  args input := [.bufferSpan input.view]
  results value := [.scalar (.i64 value)]
  pre input memory := input.view.validate memory = .ok () ∧
    Contents memory input.base 8 input.words ∧ input.words[0]? = some input.first
  footprint _ := []
  post input before after value := after = before ∧ value = input.first

/-- The compiled `Word` satisfies the contract for every caller sequence and storage. -/
theorem word_holds : wordContract.Holds Extracted.program 0 := by
  intro input memory permitted
  obtain ⟨valid, contents, selected⟩ := permitted
  have loaded := contents 0 input.first selected
  simp only [Reference.element_zero] at loaded
  have formed := access_reference_valid _ _ _ _ _ (read_access loaded)
  have word := contents.load_word selected
  simp only [Reference.element_zero] at word
  refine ⟨5, memory, [.scalar (.i64 input.first)], ?_, Confined.refl _ _,
    input.first, rfl, rfl, rfl⟩
  dsimp only [wordContract]
  simp only [Safety.invoke, Extracted.lookup0]
  simp [checkedValue, valid, enterFrame, Extracted.method0, makeLocals,
    makeArgumentHomes, makeParameterHomes, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure, List.mapM_cons, List.mapM_nil]
  cil_checked_steps [wordContract, WordInput.view, valid, word, formed]

#print axioms word_holds

end Tests.SpanReferenceWordContract
