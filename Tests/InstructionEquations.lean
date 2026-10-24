import CIL.InstructionEquations
import CIL.Safety.SymbolicExecution

/-!
# Instruction equations for a parametric body

`cil_instruction_equations` on a hand-written body over two feature flags and a callee index,
shaped like `if (Avx2.IsSupported) { ... } else { ... }`. The equations keep each
feature-dependent instruction as an `if`, fetch instructions from a body that cannot be
unfolded, and decide the `if` from facts about symbolic flags or from literal flags. A run
proved once over the flags is then bound to concrete profiles without restating the body.
-/

namespace Tests.InstructionEquations

/-- The instruction a profile extraction emits for code its feature tests exclude. -/
abbrev unreachable : CIL.Op := .unsupported "Unreachable under selected profile"

/-- `if (Avx2.IsSupported) return Callee(a, b); return Sse42.IsSupported ? b : a;` with the
    paths of the other profile padded as `unreachable`, so every profile has the same pcs. -/
def dispatchBody (sse42 avx2 : Bool) (callee : Nat) : CIL.Method :=
  { profile := { sse42, avx2 }, returnsValue := true, locals := [], code := [
    .feature .avx2,
    .brzero 6,
    if avx2 then .arg 0 else unreachable,
    if avx2 then .arg 1 else unreachable,
    if avx2 then .call callee 2 else unreachable,
    if avx2 then .ret else unreachable,
    if avx2 then unreachable else if sse42 then .arg 1 else .arg 0,
    if avx2 then unreachable else .ret] }

cil_instruction_equations dispatchBody

-- The statement keeps the feature test and the callee parameter as the body writes them.
/--
info: Tests.InstructionEquations.dispatchBody_instruction4 (sse42 avx2 : Bool) (callee : Nat) :
  (dispatchBody sse42 avx2 callee).code[4]? =
    some (if avx2 = true then CIL.Op.call callee 2 else unreachable)
-/
#guard_msgs (whitespace := lax) in #check dispatchBody_instruction4

-- `propext` comes from the list lookup instance, as for the extractor's equations.
/-- info: 'Tests.InstructionEquations.dispatchBody_instruction4' depends on axioms: [propext] -/
#guard_msgs in #print axioms dispatchBody_instruction4

-- Every pc of the eight-instruction body has its equation, using only the axioms of the
-- list lookup itself.
open Lean in
run_cmd do
  for pc in [0:8] do
    let name := Name.appendAfter `Tests.InstructionEquations.dispatchBody s!"_instruction{pc}"
    unless (← getEnv).contains name do throwError "missing {name}"
    let axioms ← collectAxioms name
    unless axioms.all (· == ``propext) do throwError "{name} depends on {axioms}"

-- One equation per pc and no more: pc 7 is the last instruction.
example : ∀ sse42 avx2 callee, (dispatchBody sse42 avx2 callee).code[7]? =
    some (if avx2 then unreachable else .ret) := dispatchBody_instruction7
/-- error: Unknown identifier `dispatchBody_instruction8` -/
#guard_msgs in #check dispatchBody_instruction8

section Sealed

-- With the body sealed, reduction cannot fetch an instruction; only the equations can.
attribute [local irreducible] dispatchBody

-- `cil_lookup` closes a lookup through the `@[cil_code]` equations where `rfl` cannot.
example (sse42 avx2 : Bool) (callee : Nat) :
    ∃ op, (dispatchBody sse42 avx2 callee).code[1]? = some op ∧ op = .brzero 6 :=
  ⟨_, by (fail_if_success rfl); cil_lookup [], by with_reducible rfl⟩

-- Symbolic flags: a fact about each flag decides the instruction's feature test.
example (sse42 avx2 : Bool) (callee : Nat) (wide : avx2 = true) :
    (dispatchBody sse42 avx2 callee).code[4]? = some (.call callee 2) := by
  simp only [dispatchBody_instruction4, wide, ↓reduceIte]

example (sse42 avx2 : Bool) (callee : Nat) (scalar : avx2 = false) (narrow : sse42 = true) :
    (dispatchBody sse42 avx2 callee).code[6]? = some (.arg 1) := by
  simp only [dispatchBody_instruction6, scalar, narrow, Bool.false_eq_true, ↓reduceIte]

-- Concrete profiles: literal flags decide the test with no fact.
example : (dispatchBody true false 3).code[6]? = some (.arg 1) := by
  simp only [cil_code, Bool.false_eq_true, ↓reduceIte]

example : (dispatchBody false true 3).code[4]? = some (.call 3 2) := by
  simp only [cil_code, ↓reduceIte]

end Sealed

/-- The scalar path, proved once over the SSE4.2 flag and the callee index. -/
theorem scalar_returns (program : CIL.Program) (index callee : Nat) (sse42 : Bool)
    (found : program[index]? = some (dispatchBody sse42 false callee))
    (memory : CIL.Safety.Memory) (left right : CIL.W32) :
    CIL.Safety.invoke program 5 index [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 (if sse42 then right else left))]) := by
  cases sse42 <;> cil_checked_steps

/-- info: 'Tests.InstructionEquations.scalar_returns' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scalar_returns

-- The same theorem binds the scalar and SSE4.2 profiles without restating the body.
example (memory : CIL.Safety.Memory) (left right : CIL.W32) :
    CIL.Safety.invoke [dispatchBody false false 0] 5 0
      [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 left)]) :=
  scalar_returns _ 0 0 false rfl memory left right

example (memory : CIL.Safety.Memory) (left right : CIL.W32) :
    CIL.Safety.invoke [dispatchBody true false 0] 5 0
      [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 right)]) :=
  scalar_returns _ 0 0 true rfl memory left right

/-- A body composed from a padding block and a helper list, as transcriptions are written. -/
def composedBody (avx2 : Bool) : CIL.Method :=
  { returnsValue := false, locals := [],
    code := List.replicate 2 unreachable ++ tailCode avx2 }
where
  /-- The instructions after the padding. -/
  tailCode (avx2 : Bool) : List CIL.Op := [if avx2 then .nop else unreachable, .ret]

cil_instruction_equations composedBody

example (avx2 : Bool) :
    (composedBody avx2).code[2]? = some (if avx2 then .nop else unreachable) :=
  composedBody_instruction2 avx2
example (avx2 : Bool) : (composedBody avx2).code[3]? = some .ret :=
  composedBody_instruction3 avx2
/-- error: Unknown identifier `composedBody_instruction4` -/
#guard_msgs in #check composedBody_instruction4

/-- Not a method, so it has no instructions. -/
def notMethod (_avx2 : Bool) : Nat := 0

/-- error: cil_instruction_equations: Tests.InstructionEquations.notMethod does not define a
CIL.Method -/
#guard_msgs (whitespace := lax) in cil_instruction_equations notMethod

/-- A body whose code length depends on a parameter, which has no per-pc equations. -/
def lengthDependsBody (avx2 : Bool) : CIL.Method :=
  { returnsValue := false, locals := [], code := if avx2 then [.ret] else [.nop, .ret] }

/--
error: cil_instruction_equations: the instruction at pc 0 of
Tests.InstructionEquations.lengthDependsBody is not determined by its parameters; state each
feature-dependent instruction as an `if` on the instruction, padding the shorter side with
`.unsupported`, so every profile has the same pcs
-/
#guard_msgs (whitespace := lax) in cil_instruction_equations lengthDependsBody

end Tests.InstructionEquations
