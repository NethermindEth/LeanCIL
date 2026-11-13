import CIL.MethodBinding

namespace Tests.MethodBinding

open CIL

/-- An extraction-independent body whose branch target depends on a shift. -/
def body (shift : Nat) (locals : List Value := [.i32 0]) : Method := {
  code := [.arg 0, .brfalse (4 + shift), .arg 1, .ret, .arg 1, .ret]
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
  left:  CIL.Instruction.brfalse 10
  right: CIL.Instruction.brfalse 4
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
  right: CIL.Instruction.nop
-/
#guard_msgs (substring := true) in
example : body 6 = { body 6 with code := (body 6).code ++ [.nop] } := by cil_body

/-- The static field the fixtures below read. -/
def field : StaticDescriptor :=
  { identity := 1, fieldName := "Fixture::Value", bytes := List.replicate 8 0 }

/-- An extracted method whose call sits at pc 2, behind a branch, and which reads no static. -/
def calling : Method := {
  code := [.arg 0, .br 2, .call 7 1, .ret], locals := [], returnsValue := true }

/-- An extracted method that reads a static at pc 0 and calls at pc 3. -/
def reading : Method := {
  code := [.memory (.staticAddress (List.replicate 8 0)), .pop, .arg 0, .call 7 1, .ret]
  locals := [], returnsValue := true, staticSites := [(0, field)] }

/-- Another method whose frame fields a body is built on, with a call and a static at other pcs. -/
def donor : Method := {
  code := [.arg 0, .memory (.staticAddress (List.replicate 8 0)), .pop, .arg 0, .call 3 1, .ret]
  locals := [], returnsValue := true, staticSites := [(1, field)] }

def withCodeProgram : Program := [calling, reading]

/-- The body is the extraction's method: the donor's call link and static site, keyed by the
    donor's pcs, are replaced by the ones the new code implies. -/
theorem with_code_binds : withCodeProgram[0]? = some (donor.withCode calling.code) := by cil_body

#print axioms with_code_binds

-- A structure update keeps the donor's links and static sites, and the binding names both.
#guard ((MethodBinding.methodDifferences calling { donor with code := calling.code }).map
    fun line => (line.takeWhile (· != ':')).toString) == ["field staticSites", "field links"]

-- A body that reads a static is not bound by `withCode` alone, which resets the sites.
example : (donor.withCode reading.code).staticSites = [] := rfl

#guard ((MethodBinding.methodDifferences reading (donor.withCode reading.code)).map
    fun line => (line.takeWhile (· != ':')).toString) == ["field staticSites"]

#guard ((MethodBinding.methodDifferences reading (donor.withCode reading.code)).map
    fun line => (line.splitOn "Method.withCode").length) == [2]

/-- Setting the sites after `withCode` binds it. -/
theorem with_code_sites_bind :
    withCodeProgram[1]? =
      some { donor.withCode reading.code with staticSites := [(0, field)] } := by
  cil_body

#print axioms with_code_sites_bind

end Tests.MethodBinding
