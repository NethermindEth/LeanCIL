import CIL.Safety.CallingFields
import CIL.Safety.LoopFrames

/-!
# Operand-load, helper-call and result-store segments

One segment rule composes any proved helper with the scalar argument and result convention.
Input and output references may overlap. Both input words are read before the helper or store;
the helper's complete contract and the actual checked write reach the continuation.
-/

namespace CIL.Safety

/-- Load two input words, call a binary scalar helper, and store its result to the output. -/
def loadCallStoreCode (callee : Nat) : List CIL.Instruction :=
  [.arg 2, .arg 0, .fieldAt 0 8, .arg 1, .fieldAt 0 8, .call callee 2, .store64]

/-- Compose a load/call/store segment once for any proved helper with scalar encodings.
    The continuation receives the real call result and checked write, not an assumed summary. -/
theorem WP.load_call_store {Input Output : Type} {contract : MethodContract Input Output}
    {program : CIL.Program} {method start callee : Nat} {body : CIL.Method}
    {frame : Frame} {memory : Memory} {post : (Memory × List Value) → Prop}
    (holds : contract.Holds program callee) (input : Input) (decode : Output → CIL.W64)
    (left right output : Reference)
    (found : program[method]? = some body)
    (placed : CodeAt body start (loadCallStoreCode callee))
    (call : ValidCall memory [⟨left, 8⟩, ⟨right, 8⟩] [⟨output, 8⟩])
    (encoded : contract.args input =
      [.scalar (.i64 ((⟨left, 8⟩ : ArgumentView).word memory 0)),
       .scalar (.i64 ((⟨right, 8⟩ : ArgumentView).word memory 0))])
    (permitted : contract.pre input memory)
    (results : ∀ value, contract.results value = [.scalar (.i64 (decode value))])
    (suffix : ∀ middle value after,
      CallResult contract program callee input memory middle value →
      write middle output (numberBytes (decode value).toNat 8) 1 = .ok after →
      WP (Execution (fun fuel => run program fuel method (start + 7)
        [.reference (.address left), .reference (.address right), .reference (.address output)]
        frame [] after)) post) :
    WP (Execution (fun fuel => run program fuel method start
      [.reference (.address left), .reference (.address right), .reference (.address output)]
      frame [] memory)) post := by
  cil_contract_steps [found, placed]
  apply run_call_of_contract holds input found
    (by cil_lookup [placed]) (by cil_checked_step []) encoded.symm permitted
  intro middle value result
  have writable : access middle output 8 1 true = .ok () :=
    (result.framed.access_write output
      (call.output_bound (output := ⟨output, 8⟩) (by simp)) 8 1).trans
      (call.writable ⟨output, 8⟩ (by simp))
  obtain ⟨after, written, _, _⟩ := store_word64 (decode value) writable
  have stored := step_store64_of_write written
  rw [results]
  cil_contract_steps [found, placed, stored] until suffix middle value after result written

#print axioms WP.load_call_store

end CIL.Safety
