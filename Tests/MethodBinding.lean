import CIL.MethodBinding

namespace Tests.MethodBinding

open CIL

/-- An extraction-independent body whose branch target depends on a shift. -/
def body (shift : Nat) (locals : List Value := [.i32 0]) : Method := {
  code := [.arg 0, .brzero (4 + shift), .arg 1, .ret, .arg 1, .ret]
  locals, returnsValue := true }

def program : Program := [{ code := [.ret], locals := [], returnsValue := false }, body 6]

theorem bound : program[1]? = some (body 6) := by cil_body

-- Only rfl may close the goal; the diagnostic is never proof evidence.
run_cmd do
  let some (.thmInfo info) := (<- Lean.getEnv).find? ``bound | throwError "missing theorem"
  unless info.value.isAppOf ``Eq.refl do throwError "cil_body produced a proof other than Eq.refl"

-- A shifted branch target is reported by method, instruction index and both instructions.
/--
error: cil_body: rfl could not prove the method-body binding
method index 1
field code: first difference at index 1 (left length 6, right length 6)
  left:  CIL.Op.brzero 10
  right: CIL.Op.brzero 4
-/
#guard_msgs (substring := true) in
example : program[1]? = some (body 0) := by cil_body

/--
error: cil_body: rfl could not prove the method-body binding
method index 1
field locals: first difference at index 0 (left length 1, right length 1)
  left:  CIL.Value.i32 0x00000000#32
  right: CIL.Value.i64 0x0000000000000000#64
-/
#guard_msgs (substring := true) in
example : program[1]? = some (body 6 [.i64 0]) := by cil_body

/--
error: cil_body: rfl could not prove the method-body binding
method index 2
left side is none (the program has 2 methods), right side is some method
-/
#guard_msgs (substring := true) in
example : program[2]? = some (body 6) := by cil_body

/--
error: cil_body: rfl could not prove the method-body binding
field code: first difference at index 6 (left length 6, right length 7)
  left:  (past the end)
  right: CIL.Op.nop
-/
#guard_msgs (substring := true) in
example : body 6 = { body 6 with code := (body 6).code ++ [.nop] } := by cil_body

end Tests.MethodBinding
