import CIL.Extraction.KernelEquation
import CIL.Extraction.MetadataBytes

/-!
# Kernel equations between names and bytes

`cil_kernel_rfl` closes an equation only when the kernel accepts it, and says which two sides it
compared when it does not. These tests check that a name read from heap bytes equals the literal
an extraction states, that one wrong byte on the heap side and one wrong character on the literal
side are each refused with both sides in the message, also under the default options a generated
module is compiled with, and that bytes which are not UTF-8 spell no name. A name that the
checker accepted for malformed bytes would let a different name pass.
-/

namespace Tests.KernelEquation

open CIL.Extraction

/-- The UTF-8 bytes of `Examples.Arithmetic`. -/
private def arithmeticBytes : List Nat :=
  [69, 120, 97, 109, 112, 108, 101, 115, 46, 65, 114, 105, 116, 104, 109, 101, 116, 105, 99]

theorem ascii_name_spelled :
    spelled? arithmeticBytes = some "Examples.Arithmetic" := by cil_kernel_rfl
/-- info: 'Tests.KernelEquation.ascii_name_spelled' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ascii_name_spelled

/-- `café` and `日本` and `😀`: two, three and four byte characters. -/
theorem non_ascii_name_spelled :
    spelled? [99, 97, 102, 195, 169, 230, 151, 165, 230, 156, 172, 240, 159, 152, 128] =
      some "café日本😀" := by cil_kernel_rfl
/-- info: 'Tests.KernelEquation.non_ascii_name_spelled' depends on axioms: [propext] -/
#guard_msgs in
#print axioms non_ascii_name_spelled

-- A wrong byte on the heap side: `Eyamples` is not `Examples`.
/--
error: cil_kernel_rfl: the kernel does not accept the two sides as equal
left:
  spelled? (arithmeticBytes.set 1 121)
right:
  some "Examples.Arithmetic"
-/
#guard_msgs in
theorem wrong_heap_byte :
    spelled? (arithmeticBytes.set 1 121) = some "Examples.Arithmetic" := by cil_kernel_rfl

-- A wrong character on the literal side.
/--
error: cil_kernel_rfl: the kernel does not accept the two sides as equal
left:
  spelled? arithmeticBytes
right:
  some "Examples.Arithmetid"
-/
#guard_msgs in
theorem wrong_literal_character :
    spelled? arithmeticBytes = some "Examples.Arithmetid" := by cil_kernel_rfl

open Lean Elab Tactic Meta in
/-- Run `cil_kernel_rfl` on the equation `type` under the options this module is compiled with and
    require its own refusal. `#guard_msgs` checks declarations synchronously, so a tactic that left
    the kernel check to an asynchronous task would pass there and assign an unchecked proof here. -/
elab "refused_under_module_options " type:term : tactic => do
  unless Elab.async.get (← getOptions) do
    throwError "the module must be elaborated with the default asynchronous kernel checks"
  let equation ← Term.elabTerm type (some (mkSort .zero))
  let goal ← mkFreshExprMVar equation
  let saved ← getGoals
  setGoals [goal.mvarId!]
  let refusal ← try
      evalTactic (← `(tactic| cil_kernel_rfl))
      pure none
    catch error => pure (some (← error.toMessageData.toString))
  setGoals saved
  match refusal with
  | none => throwError "cil_kernel_rfl accepted a wrong equation{indentExpr equation}"
  | some message =>
    unless message.startsWith "cil_kernel_rfl: the kernel does not accept the two sides as equal" do
      throwError "cil_kernel_rfl failed with another message:\n{message}"

/-- A wrong character on the literal side and a wrong byte on the heap side are refused by the
    tactic itself under the default options, outside `#guard_msgs`. -/
example : True := by
  refused_under_module_options spelled? arithmeticBytes = some "Examples.Arithmetid"
  refused_under_module_options spelled? (arithmeticBytes.set 1 121) = some "Examples.Arithmetic"
  trivial

/-- An overlong encoding of NUL, a surrogate, a truncated character and a stray continuation
    byte spell nothing. -/
theorem malformed_bytes_spell_nothing :
    spelled? [0xC0, 0x80] = none ∧ spelled? [0xED, 0xA0, 0x80] = none ∧
      spelled? [0xE6, 0x97] = none ∧ spelled? [0x80] = none ∧
      spelled? [0xF4, 0x90, 0x80, 0x80] = none ∧ spelled? [0xE0, 0x80, 0x80] = none :=
  ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl,
    by cil_kernel_rfl, by cil_kernel_rfl⟩

-- Malformed bytes are not an empty name.
/--
error: cil_kernel_rfl: the kernel does not accept the two sides as equal
left:
  spelled? [192, 128]
right:
  some ""
-/
#guard_msgs in
theorem malformed_bytes_are_not_the_empty_name : spelled? [0xC0, 0x80] = some "" := by
  cil_kernel_rfl

/-- The spelling of a string's own bytes is the string, so a name accepted through `spelled?` is
    the name `bytesOf` would have compared. -/
theorem spelling_inverts_bytes :
    ["", "System.Private.CoreLib", "café日本😀", "A`1", "Outer/Inner"].all
      (fun name => spelled? (bytesOf name) == some name) = true := by decide +kernel
/-- info: 'Tests.KernelEquation.spelling_inverts_bytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms spelling_inverts_bytes

end Tests.KernelEquation
