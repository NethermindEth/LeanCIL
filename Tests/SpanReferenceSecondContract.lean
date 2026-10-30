import Extracted
import CIL.Safety.MethodContract
import CIL.Safety.BufferContents

/-!
# Contract for an element offset from a readonly span reference

`SpanReferences::Second(in ReadOnlySpan<ulong>)` reads
`Unsafe.Add(ref MemoryMarshal.GetReference(values), 1)`. The offset keeps the readonly
restriction and the writable reference's bounds check, so the symbolic span contents and
`add_element` prove the load of the second element.
-/

namespace Tests.SpanReferenceSecondContract
open CIL CIL.Safety

/-- A word sequence in caller storage whose second word a caller names. -/
structure SecondInput where
  base : Reference
  words : List (BitVec (8 * 8))
  second : BitVec (8 * 8)

/-- The readonly view of the complete input sequence. -/
def SecondInput.view (input : SecondInput) : SpanView :=
  ⟨.address input.base, input.words.length, 8, false⟩

/-- Reading the second element of a readonly view returns that word and changes nothing. -/
def secondContract : MethodContract SecondInput (BitVec (8 * 8)) where
  args input := [.bufferSpan input.view]
  results value := [.scalar (.i64 value)]
  pre input memory := memory.WellFormed ∧ input.view.validate memory = .ok () ∧
    Contents memory input.base 8 input.words ∧ input.words[1]? = some input.second
  footprint _ := []
  post input before after value := after = before ∧ value = input.second

/-- The compiled `Second` satisfies the contract for every caller sequence and storage. -/
theorem second_holds : secondContract.Holds Extracted.program 0 := by
  intro input memory permitted
  obtain ⟨wellFormed, valid, contents, selected⟩ := permitted
  have firstWord : ∃ first, input.words[0]? = some first := by
    cases words : input.words with
    | nil => simp [words] at selected
    | cons first _ => exact ⟨first, rfl⟩
  obtain ⟨first, found⟩ := firstWord
  have formed := access_reference_valid _ _ _ _ _ (read_access (contents 0 first found))
  simp only [Reference.element_zero] at formed
  have offset := add_element wellFormed formed (read_access (contents 1 input.second selected))
  have word := contents.load_word selected
  refine ⟨7, memory, [.scalar (.i64 input.second)], ?_, Confined.refl _ _,
    input.second, rfl, rfl, rfl⟩
  dsimp only [secondContract]
  simp only [Safety.invoke, Extracted.lookup0]
  simp [checkedValue, valid, enterFrame, Extracted.method0, makeLocals,
    makeArgumentHomes, makeParameterHomes, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure, List.mapM_cons, List.mapM_nil]
  cil_checked_steps [secondContract, SecondInput.view, checkedValue, numericValue, instruction,
    staticInstruction, valid, word, formed, offset, formValue, observerCount, unspecifiedOperands,
    referenceAt, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms second_holds

end Tests.SpanReferenceSecondContract
