import CIL.MethodBinding
import CIL.Extraction.TemplateCode
import Tests.Support

namespace Tests.MethodBinding

open CIL

/-- An extraction-independent body whose branch target depends on a shift. -/
def body (shift : Nat) (locals : List Value := [.i32 0]) : Method := {
  code := [.ldarg 0, .brfalse (4 + shift), .ldarg 1, .ret, .ldarg 1, .ret]
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

/-- An extracted method whose call sits at pc 2, behind a branch, and which reads no static. -/
def calling : Method := {
  code := [.ldarg 0, .br 2, .call (Tests.callee 1) {}, .ret], links := [(2, .direct 7)],
  locals := [], returnsValue := true }

/-- A tail-prefixed call with a managed operand and its own target slot. -/
private def tailCall (slot : Nat) : Method :=
  { calling with
    code := [.nop, .call (Tests.callee 1) { tail := true }, .ret]
    links := [(1, .direct slot)] }

-- Relocation retains the operand and the prefix, and only the managed target index changes.
#guard ((tailCall 3).relocate (fun _ => 1)).code == (tailCall 1).code
#guard MethodBinding.firstCodeOrLinkDifference
  ((tailCall 3).relocate (fun _ => 1)) (tailCall 1) == none
#guard MethodBinding.firstCodeOrLinkDifference (tailCall 3) (tailCall 1) == some 1

/-- Templates rename the definition named by an address as well as indirect call targets. -/
theorem reindexed_address (newIndex : Nat) :
    (({ calling with links := [(2, .address 3)] } : Method).reindexLinks
      (fun _ => newIndex)).links = [(2, .address newIndex)] := rfl
#print axioms reindexed_address

#guard MethodBinding.firstCodeOrLinkDifference calling { calling with links := [] } == some 2
#guard MethodBinding.firstCodeOrLinkDifference { calling with links := [] } calling == some 2
#guard MethodBinding.firstCodeOrLinkDifference calling
  { calling with links := [(3, .direct 7)] } == some 2
#guard MethodBinding.firstCodeOrLinkDifference calling
  { calling with code := [.nop], links := [] } == some 0
#guard MethodBinding.firstCodeOrLinkDifference calling
  { calling with code := calling.code ++ [.nop], links := [] } == some 2

/-- The field operand of the static reads below. -/
def fieldRef : CIL.Extraction.FieldRef :=
  { owner := .atom "Fixture" "Fixture", index := 0, type := .atom "Fixture" "System.Int64",
    name := name!"Value" }

/-- The static field the fixtures below read. -/
def field : StaticDescriptor :=
  { identity := 1, field := fieldRef, bytes := List.replicate 8 0 }

/-- An extracted method that reads a static at pc 0 and calls at pc 3. -/
def reading : Method := {
  code := [.ldsflda fieldRef, .pop, .ldarg 0, .call (Tests.callee 1) {}, .ret],
  links := [(3, .direct 7)]
  locals := [], returnsValue := true, staticSites := [(0, field)] }

/-- Another method whose frame fields a body is built on, with a call and a static at other pcs. -/
def donor : Method := {
  code := [.ldarg 0, .ldsflda fieldRef, .pop, .ldarg 0, .call (Tests.callee 1) {}, .ret],
  links := [(4, .direct 3)]
  locals := [], returnsValue := true, staticSites := [(1, field)] }

def withCodeProgram : Program := [calling, reading]

/-- The body is the extraction's method: `withCode` drops the donor's call link and static site,
    keyed by the donor's pcs, and the call's link is written for the new code. -/
theorem with_code_binds :
    withCodeProgram[0]? = some { donor.withCode calling.code with links := [(2, .direct 7)] } := by
  cil_body

#print axioms with_code_binds

-- A structure update keeps the donor's links and static sites, and the binding names both.
#guard ((MethodBinding.methodDifferences calling { donor with code := calling.code }).map
    fun line => (line.takeWhile (· != ':')).toString) == ["field staticSites", "field links"]

-- `withCode` alone drops a call's link, which its code does not imply, and the binding says so.
#guard ((MethodBinding.methodDifferences calling (donor.withCode calling.code)).map
    fun line => (line.takeWhile (· != ':')).toString) == ["field links"]

#guard ((MethodBinding.methodDifferences calling (donor.withCode calling.code)).map
    fun line => (line.splitOn "links := [(pc, link), ...]").length) == [2]

/-- `reading`'s code under `withCode`, with its call's link. -/
def readingLinked : Method := { donor.withCode reading.code with links := [(3, .direct 7)] }

-- A body that reads a static is not bound by `withCode` alone, which resets the sites.
example : readingLinked.staticSites = [] := rfl

#guard ((MethodBinding.methodDifferences reading readingLinked).map
    fun line => (line.takeWhile (· != ':')).toString) == ["field staticSites"]

#guard ((MethodBinding.methodDifferences reading readingLinked).map
    fun line => (line.splitOn "Method.withCode").length) == [2]

/-- Setting the sites after `withCode` binds it. -/
theorem with_code_sites_bind :
    withCodeProgram[1]? =
      some { readingLinked with staticSites := [(0, field)] } := by
  cil_body

#print axioms with_code_sites_bind

end Tests.MethodBinding
