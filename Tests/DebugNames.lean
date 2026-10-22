import CIL.Embedding.Tactic

/-! Synthetic PDB data: the extractor writes `ExtractedSymbols` only from a matching PDB. -/
namespace ExtractedSymbols

def locals : List (List (Nat × Nat × Nat × String)) := [
  [],
  -- `carry` is reused by two sibling blocks with different slots; `x` is shadowed by an inner scope.
  [(0, 0, 20, "x"), (1, 2, 8, "carry"), (2, 10, 16, "carry"), (3, 4, 6, "x")]]
def points : List (List (Nat × String × Nat × Nat)) := [
  [],
  [(0, "src/Math.cs", 10, 9), (3, "src/Math.cs", 11, 13), (5, "src/Math.cs", 12, 13)]]

end ExtractedSymbols

namespace Tests.DebugNames

open CIL

example : local_named 1 "carry" at 3 = 1 ∧ local_named 1 "carry" at 12 = 2 := ⟨rfl, rfl⟩
-- The innermost scope wins; outside it the outer slot applies.
example : local_named 1 "x" at 5 = 3 ∧ local_named 1 "x" at 1 = 0 ∧ local_named 1 "x" at 6 = 0 := ⟨rfl, rfl, rfl⟩

/--
error: local "carry" names 2 slots in method 1; select one with `at pc`:
  slot 1 "carry", pc 2 until 8
  slot 2 "carry", pc 10 until 16
-/
#guard_msgs in
example : local_named 1 "carry" = 1 := rfl

/--
error: no scope of local "carry" in method 1 contains pc 9:
  slot 1 "carry", pc 2 until 8
  slot 2 "carry", pc 10 until 16
-/
#guard_msgs in
example : local_named 1 "carry" at 9 = 1 := rfl

/--
error: method 1 has no local named "borrow"; its named locals:
  slot 0 "x", pc 0 until 20
  slot 1 "carry", pc 2 until 8
  slot 2 "carry", pc 10 until 16
  slot 3 "x", pc 4 until 6
-/
#guard_msgs in
example : local_named 1 "borrow" = 0 := rfl

def body (target : Nat) : Method :=
  { code := [.arg 0, .arg 0, .brzero target, .arg 0, .ret, .arg 0, .ret], locals := [], returnsValue := true }
def program : Program := [{ code := [.ret], locals := [], returnsValue := false }, body 5]

-- A failing binding names the source of the first differing pc, after the unchanged report.
/--
error: cil_body: rfl could not prove the method-body binding
method index 1
field code: first difference at index 2 (left length 7, right length 7)
  left:  CIL.Op.brzero 5
  right: CIL.Op.brzero 3
source of actual pc 2: src/Math.cs:10:9
-/
#guard_msgs (substring := true) in
example : program[1]? = some (body 3) := by cil_body

/--
error: cil_embed: the expected body does not embed into the extracted method
method index 1
expected pc 3 maps to actual pc 3
  expected: CIL.Op.const32 0x00000001#32
  actual:   CIL.Op.arg 0 none
  the instructions differ
  expected pc 2 falls through to it, so it must be actual pc 3
source of actual pc 3: src/Math.cs:11:13
-/
#guard_msgs in
example : MethodEmbeds program 1 { body 5 with code := [.arg 0, .arg 0, .brzero 5, .const32 1, .ret, .arg 0, .ret] } := by cil_embed

-- Methods without sequence points add nothing.
run_meta do
  unless (← CIL.DebugNames.sourceLine 0 0).isEmpty do throwError "method 0 has no points"

end Tests.DebugNames
