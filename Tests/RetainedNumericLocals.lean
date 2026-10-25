import CIL.Embedding.Tactic
import CIL.Safety.Embedding.Outcomes

/-!
# Retaining dead numeric declarations during embedding

Numeric locals remain in both bodies, including slots before and after a live reference
local. This keeps frame and callee allocation identities exact while dead code moves.
-/

namespace Tests.RetainedNumericLocals

open CIL

/-- Empty caller storage used to expose the exact number of frame allocations. -/
def empty : Safety.Memory := {
  allocations := fun _ => none
  cells := fun _ _ => ⟨0, false⟩
  views := []
  nextIdentity := 0 }

/-- The expected body keeps both unused numeric homes around its live reference local. -/
def expected : Method := {
  locals := [.unmodeled, .nullRef, .unmodeled]
  localKinds := [.word32, .reference, .word64]
  returnsValue := true
  code := [.branch 3, .unsupported "dead", .unsupported "dead",
    .local 1, .pop, .call 1 0, .ret] }

/-- A separately specified body moves the live block past extra unreachable instructions. -/
def actual : Method := {
  locals := [.unmodeled, .nullRef, .unmodeled]
  localKinds := [.word32, .reference, .word64]
  returnsValue := true
  code := [.branch 4, .const32 9, .pop, .nop, .local 1, .pop, .call 1 0, .ret] }

/-- The child allocates its own numeric home after the parent's retained dead homes. -/
def child : Method := {
  locals := [.i64 7]
  localKinds := [.word64]
  returnsValue := true
  code := [.local 0, .ret] }

/-- Retained numeric declarations need ordinary method embedding, even when interspersed. -/
theorem embeds : MethodEmbeds [actual, child] 0 expected := by cil_embed
#print axioms embeds

/-- A proved invocation transports with exactly the same final memory and returned values. -/
theorem transfer {fuel : Nat} {memory final : Safety.Memory} {values : List Safety.Value}
    (ran : Safety.invoke [expected, child] fuel 0 [] memory = .ok (final, values)) :
    Safety.invoke [actual, child] fuel 0 [] memory = .ok (final, values) :=
  embeds.invoke ran
#print axioms transfer

/-- Both parent numeric homes and the later child home allocate, despite the dead code. -/
theorem expected_allocations :
    (Safety.invoke [expected, child] 10 0 [] empty).map
      (fun result => (result.1.nextIdentity, result.2)) =
        .ok (3, [.scalar (.i64 7)]) := rfl
#print axioms expected_allocations

/-- The independently specified actual body has the same three allocations and scalar result. -/
theorem actual_allocations :
    (Safety.invoke [actual, child] 10 0 [] empty).map
      (fun result => (result.1.nextIdentity, result.2)) =
        .ok (3, [.scalar (.i64 7)]) := rfl
#print axioms actual_allocations

/-- Removing the first unused numeric local requires renumbering the live local operand. -/
def removed : Method := {
  locals := [.nullRef, .unmodeled]
  localKinds := [.reference, .word64]
  returnsValue := true
  code := [.branch 3, .unsupported "dead", .unsupported "dead",
    .local 0, .pop, .call 1 0, .ret] }

/-- Deleting a dead numeric local changes later allocation identities despite equal scalars. -/
theorem removed_allocations :
    (Safety.invoke [removed, child] 10 0 [] empty).map
      (fun result => (result.1.nextIdentity, result.2)) =
        .ok (2, [.scalar (.i64 7)]) := rfl
#print axioms removed_allocations

/-- Ordinary embedding correctly rejects the numeric deletion instead of erasing its effects. -/
theorem deletion_rejected (map : List Nat) : ¬ Embeds removed actual map := by
  intro embedded
  have length := congrArg List.length embedded.locals
  simp [removed, actual] at length
#print axioms deletion_rejected

/-- A child that allocates a home before raising a named exception. -/
def thrower : Method := {
  locals := [.unmodeled]
  localKinds := [.word64]
  returnsValue := true
  code := [.throw "System.InvalidOperationException"] }

/-- The same parent embedding also transports calls to a throwing child. -/
theorem throwing_embeds : MethodEmbeds [actual, thrower] 0 expected := by cil_embed
#print axioms throwing_embeds

/-- The expected invocation raises from the allocated child frame. -/
theorem expected_raises :
    Safety.Raises [expected, thrower] 0 [] empty "System.InvalidOperationException" :=
  ⟨10, ⟨1, 0, .thrown "System.InvalidOperationException"⟩, rfl, rfl⟩
#print axioms expected_raises

/-- Named exceptions transfer with the retained numeric allocation layout. -/
theorem actual_raises :
    Safety.Raises [actual, thrower] 0 [] empty "System.InvalidOperationException" :=
  throwing_embeds.raises expected_raises
#print axioms actual_raises

end Tests.RetainedNumericLocals
