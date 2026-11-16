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
abbrev unreachable : CIL.Instruction := .unadmitted 0

/-- `if (Avx2.IsSupported) return Callee(a, b); return Sse42.IsSupported ? b : a;` with the
    paths of the other profile padded as `unreachable`, so every profile has the same pcs. -/
def dispatchBody (sse42 avx2 : Bool) (callee : Nat) : CIL.Method :=
  { profile := { sse42, avx2 }, returnsValue := true, locals := [], code := [
    .feature .avx2,
    .brfalse 6,
    if avx2 then .ldarg 0 else unreachable,
    if avx2 then .ldarg 1 else unreachable,
    if avx2 then .call callee 2 else unreachable,
    if avx2 then .ret else unreachable,
    if avx2 then unreachable else if sse42 then .ldarg 1 else .ldarg 0,
    if avx2 then unreachable else .ret] }

cil_instruction_equations dispatchBody

-- The statement keeps the feature test and the callee parameter as the body writes them.
/--
info: Tests.InstructionEquations.dispatchBody_instruction4 (sse42 avx2 : Bool) (callee : Nat) :
  (dispatchBody sse42 avx2 callee).code[4]? =
    some (if avx2 = true then CIL.Instruction.call callee 2 else unreachable)
-/
#guard_msgs (whitespace := lax) in #check dispatchBody_instruction4

-- `propext` comes from the list lookup instance, as for the extractor's equations.
/-- info: 'Tests.InstructionEquations.dispatchBody_instruction4' depends on axioms: [propext] -/
#guard_msgs in #print axioms dispatchBody_instruction4

open Lean in
/-- Fails unless `body` has an equation for each of its `length` pcs, each using only the
    axioms of the list lookup itself. -/
def auditEquations (body : Name) (length : Nat) : CoreM Unit := do
  for pc in [0:length] do
    let name := body.appendAfter s!"_instruction{pc}"
    unless (← getEnv).contains name do throwError "missing {name}"
    let axioms ← collectAxioms name
    unless axioms.all (· == ``propext) do throwError "{name} depends on {axioms}"

run_cmd Lean.Elab.Command.liftCoreM (auditEquations ``dispatchBody 8)

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
    ∃ op, (dispatchBody sse42 avx2 callee).code[1]? = some op ∧ op = .brfalse 6 :=
  ⟨_, by (fail_if_success rfl); cil_lookup [], by with_reducible rfl⟩

-- Symbolic flags: a fact about each flag decides the fetched instruction's feature test.
example (sse42 avx2 : Bool) (callee : Nat) (wide : avx2 = true) :
    ∃ op, (dispatchBody sse42 avx2 callee).code[4]? = some op ∧ op = .call callee 2 :=
  ⟨_, by cil_lookup [wide], by with_reducible rfl⟩

example (sse42 avx2 : Bool) (callee : Nat) (scalar : avx2 = false) (narrow : sse42 = true) :
    ∃ op, (dispatchBody sse42 avx2 callee).code[6]? = some op ∧ op = .ldarg 1 :=
  ⟨_, by cil_lookup [scalar, narrow], by with_reducible rfl⟩

-- Concrete profiles: literal flags decide the test with no fact.
example : ∃ op, (dispatchBody true false 3).code[6]? = some op ∧ op = .ldarg 1 :=
  ⟨_, by cil_lookup [], by with_reducible rfl⟩

example : ∃ op, (dispatchBody false false 3).code[6]? = some op ∧ op = .ldarg 0 :=
  ⟨_, by cil_lookup [], by with_reducible rfl⟩

example : ∃ op, (dispatchBody false true 3).code[4]? = some op ∧ op = .call 3 2 :=
  ⟨_, by cil_lookup [], by with_reducible rfl⟩

end Sealed

/-- The scalar path from a fact about a symbolic AVX2 flag: the `.ret` at pc 7 is fetched
    decided, so the run returns instead of stopping on an undecided `if`. -/
theorem sse42_returns (program : CIL.Program) (index callee : Nat) (avx2 : Bool)
    (scalar : avx2 = false) (found : program[index]? = some (dispatchBody true avx2 callee))
    (memory : CIL.Safety.Memory) (left right : CIL.W32) :
    CIL.Safety.invoke program 5 index [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 right)]) := by
  cil_checked_steps [scalar]

/-- info: 'Tests.InstructionEquations.sse42_returns' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sse42_returns

/-- The scalar path over both flags and the callee index; only the result's own `if` on the
    SSE4.2 flag is split. -/
theorem scalar_returns (program : CIL.Program) (index callee : Nat) (sse42 avx2 : Bool)
    (scalar : avx2 = false) (found : program[index]? = some (dispatchBody sse42 avx2 callee))
    (memory : CIL.Safety.Memory) (left right : CIL.W32) :
    CIL.Safety.invoke program 5 index [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 (if sse42 then right else left))]) := by
  cases sse42 <;> cil_checked_steps [scalar]

/-- info: 'Tests.InstructionEquations.scalar_returns' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scalar_returns

-- The same theorem binds the scalar and SSE4.2 profiles without restating the body.
example (memory : CIL.Safety.Memory) (left right : CIL.W32) :
    CIL.Safety.invoke [dispatchBody false false 0] 5 0
      [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 left)]) :=
  scalar_returns _ 0 0 false false rfl rfl memory left right

example (memory : CIL.Safety.Memory) (left right : CIL.W32) :
    CIL.Safety.invoke [dispatchBody true false 0] 5 0
      [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 right)]) :=
  scalar_returns _ 0 0 true false rfl rfl memory left right

/-- `return Callee(a);` with the callee index as a parameter: its call site's link is
    determined by its instruction, so the command states it. -/
def callingBody (callee : Nat) : CIL.Method :=
  { returnsValue := true, locals := [], code := [.ldarg 0, .call callee 1, .ret] }

cil_instruction_equations callingBody

/--
info: Tests.InstructionEquations.callingBody_link1 (callee : Nat) :
  (callingBody callee).linkAt 1 = some (CIL.Link.direct callee)
-/
#guard_msgs (whitespace := lax) in #check callingBody_link1

-- A pc that is not a call site, and a call a feature flag decides, get no link fact.
/-- error: Unknown identifier `callingBody_link0` -/
#guard_msgs in #check callingBody_link0
/-- error: Unknown identifier `dispatchBody_link4` -/
#guard_msgs in #check dispatchBody_link4

section SealedCall

attribute [local irreducible] callingBody

/-- With the body sealed, the call enters its parameter callee by the link fact alone. -/
theorem sealed_call (callee : Nat) (args : List CIL.Safety.Value) (frame : CIL.Safety.Frame)
    (memory : CIL.Safety.Memory) (argument : CIL.W64) :
    CIL.Safety.step (callingBody callee) (.call callee 1) 1 args frame
        [.scalar (.i64 argument)] memory =
      .ok (.call callee [.scalar (.i64 argument)] [] memory) := by
  cil_checked_step []

/-- info: 'Tests.InstructionEquations.sealed_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sealed_call

end SealedCall

section ExtractedLinks

/-- The links of an extraction's call sites, named and tagged as the extractor writes them. -/
@[cil_code] def namedDirect : CIL.Link := .direct 1
/-- The link of a constructor call site, as the extractor writes it. -/
@[cil_code] def namedAggregate : CIL.Link := .aggregate 1 8

/-- An extracted body: an explicit table and one generated fact per call site. -/
def linkedBody : CIL.Method :=
  { returnsValue := true, locals := [],
    code := [.ldarg 0, .call 1 1, .newobj (.arity 0), .ret],
    links := [(1, namedDirect), (2, namedAggregate)] }

@[cil_code] theorem linkedBody_link1 : linkedBody.linkAt 1 = some namedDirect := rfl
@[cil_code] theorem linkedBody_link2 : linkedBody.linkAt 2 = some namedAggregate := rfl

-- Sealed, so each step below reads its link from the facts and not by evaluating the table.
attribute [local irreducible] linkedBody

/-- A call enters the method its site's fact and tagged link name. -/
theorem linked_call (args : List CIL.Safety.Value) (frame : CIL.Safety.Frame)
    (memory : CIL.Safety.Memory) (argument : CIL.W64) :
    CIL.Safety.step linkedBody (.call 1 1) 1 args frame [.scalar (.i64 argument)] memory =
      .ok (.call 1 [.scalar (.i64 argument)] [] memory) := by
  cil_checked_step []

/-- A call at a site linked to a constructor faults, which needs the link's constructor form. -/
theorem constructor_link_faults (args : List CIL.Safety.Value) (frame : CIL.Safety.Frame)
    (memory : CIL.Safety.Memory) (argument : CIL.W64) :
    CIL.Safety.step linkedBody (.call 1 1) 2 args frame [.scalar (.i64 argument)] memory =
      .error CIL.Safety.unlinkedCall := by
  cil_checked_step []

/-- info: 'Tests.InstructionEquations.linked_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms linked_call
/--
info: 'Tests.InstructionEquations.constructor_link_faults' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms constructor_link_faults

end ExtractedLinks

/-- A call site its table omits. -/
def unlinkedBody : CIL.Method :=
  { returnsValue := true, locals := [], code := [.ldarg 0, .call 0 1, .ret], links := [] }

cil_instruction_equations unlinkedBody

/-- The run faults at the call's pc, before any callee runs. -/
theorem unlinked_call_faults (memory : CIL.Safety.Memory) (argument : CIL.W64) :
    CIL.Safety.invoke [unlinkedBody] 4 0 [.scalar (.i64 argument)] memory =
      .error ⟨0, 1, CIL.Safety.unlinkedCall⟩ := by
  cil_checked_steps []

/--
info: 'Tests.InstructionEquations.unlinked_call_faults' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms unlinked_call_faults

/-- A body composed from a padding block and a helper list, as transcriptions are written. -/
def composedBody (avx2 : Bool) : CIL.Method :=
  { returnsValue := false, locals := [],
    code := List.replicate 2 unreachable ++ tailCode avx2 }
where
  /-- The instructions after the padding. -/
  tailCode (avx2 : Bool) : List CIL.Instruction := [if avx2 then .nop else unreachable, .ret]

cil_instruction_equations composedBody

example (avx2 : Bool) :
    (composedBody avx2).code[2]? = some (if avx2 then .nop else unreachable) :=
  composedBody_instruction2 avx2
example (avx2 : Bool) : (composedBody avx2).code[3]? = some .ret :=
  composedBody_instruction3 avx2
run_cmd Lean.Elab.Command.liftCoreM (auditEquations ``composedBody 4)
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
Tests.InstructionEquations.lengthDependsBody is not determined by its parameters, or the body
does not unfold; state each feature-dependent instruction as an `if` on the instruction,
padding the shorter side with `.unadmitted`, so every profile has the same pcs
-/
#guard_msgs (whitespace := lax) in cil_instruction_equations lengthDependsBody

/-- A body that agrees on its first instruction but not on its length. -/
def tailDependsBody (avx2 : Bool) : CIL.Method :=
  { returnsValue := false, locals := [], code := .nop :: if avx2 then [.ret] else [.nop, .ret] }

-- The walk fails at pc 1, and the command declares nothing, not even pc 0.
/--
error: cil_instruction_equations: the instruction at pc 1 of
Tests.InstructionEquations.tailDependsBody is not determined by its parameters, or the body
does not unfold; state each feature-dependent instruction as an `if` on the instruction,
padding the shorter side with `.unadmitted`, so every profile has the same pcs
-/
#guard_msgs (whitespace := lax) in cil_instruction_equations tailDependsBody
/-- error: Unknown identifier `tailDependsBody_instruction0` -/
#guard_msgs in #check tailDependsBody_instruction0

/-- A body with no parameters, as the extractor's own methods are. -/
def fixedBody : CIL.Method := { returnsValue := false, locals := [], code := [.nop, .ret] }

cil_instruction_equations fixedBody

example : fixedBody.code[1]? = some .ret := fixedBody_instruction1
example : ∃ op, fixedBody.code[0]? = some op ∧ op = .nop :=
  ⟨_, by cil_lookup [], by with_reducible rfl⟩

/-- A body with an implicit width and a hypothesis about it, both kept as parameters. -/
def guardedBody {width : Nat} (_wide : 32 < width) : CIL.Method :=
  { returnsValue := true, locals := [], code := [.ldc_i4 (BitVec.ofNat 32 width), .ret] }

cil_instruction_equations guardedBody

/--
info: Tests.InstructionEquations.guardedBody_instruction0 {width : Nat} (_wide : 32 < width) :
  (guardedBody _wide).code[0]? = some (CIL.Instruction.ldc_i4 (BitVec.ofNat 32 width))
-/
#guard_msgs (whitespace := lax) in #check guardedBody_instruction0

example (wide : 32 < 40) :
    ∃ op, (guardedBody wide).code[0]? = some op ∧ op = .ldc_i4 (BitVec.ofNat 32 40) :=
  ⟨_, by cil_lookup [], by with_reducible rfl⟩

end Tests.InstructionEquations
