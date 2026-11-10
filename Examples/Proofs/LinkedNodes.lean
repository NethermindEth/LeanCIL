import Extracted
import CIL.MethodIdentity
import CIL.Safety.ObjectFields
import CIL.Safety.AllocationRefinement

/-!
# Linked nodes

`Examples.Node` holds a `ulong` `Value` and a `Next` reference to another node. `Link(node,
next)` stores `next` into `node.Next`, `SecondValue(node)` reads `node.Next.Value`, and
`LinkedValue(node, next)` calls both. A reference lives in its field's slot, not in bytes, so
`Link` changes one slot, which is its whole footprint. Proved: each method's contract,
`LinkedValue` returning `next.Value` whether or not `next` is `node`, the
`NullReferenceException` of `SecondValue` at each field load, `Link` keeping every other node's
`Next` and every node's `Value`, and `Link`'s contract transferring to any program that renames
its fresh allocations.
-/

open CIL.Safety
open CIL (W64)
open Extracted.Classes
namespace ExampleProof

bind_method linkedValue linkedValueBody :=
  "System.UInt64 Examples.Objects::LinkedValue(Examples.Node,Examples.Node)"
bind_callee link linkBody :=
  "System.Void Examples.Objects::Link(Examples.Node,Examples.Node)" from linkedValueBody
bind_callee secondValue secondValueBody :=
  "System.UInt64 Examples.Objects::SecondValue(Examples.Node)" from linkedValueBody

/-- `Link(node, next)` stores `next` into `node.Next`; its footprint is that slot alone, so no
    byte and no other field changes. -/
def linkContract : MethodContract (Reference × Reference) where
  args := fun (node, next) => [.object (.address node), .object (.address next)]
  pre := fun (node, next) memory => Node.Next.Owned memory node ∧ LiveObject memory next
  footprint := fun (node, _) => [Node.Next.entry node]
  post := fun (node, next) _ final values => values = [] ∧
    Node.Next.Holds final node (.address next)

/-- `SecondValue(node)` returns the `Value` of the node `node.Next` holds and changes nothing. -/
def secondValueContract : MethodContract Reference W64 where
  args node := [.object (.address node)]
  results value := [.scalar (.i64 value)]
  pre node memory := Node.Next.Readable memory node ∧
    ∃ next, Node.Next.of memory node = .address next ∧ Node.Value.Readable memory next
  footprint _ := []
  post node initial final result := final = initial ∧
    ∀ next, Node.Next.of initial node = .address next → result = Node.Value.of initial next

/-- `Link` meets its contract: one `stfld` into the `Next` slot. -/
theorem link_holds : linkContract.Holds Extracted.program link := by
  rintro ⟨node, next⟩ memory ⟨owned, nextLive⟩
  obtain ⟨stored, framed, held⟩ := owned.store nextLive
  refine MethodContract.Holds.intro _ [] ?_ framed ⟨rfl, held⟩
  cil_checked_steps [stored]

#print axioms link_holds

/-- `SecondValue` meets its contract: two field loads, through the `Next` slot. -/
theorem secondValue_holds : secondValueContract.Holds Extracted.program secondValue := by
  rintro node memory ⟨readable, next, held, valueReadable⟩
  refine MethodContract.Holds.intro memory (Node.Value.of memory next) ?_ (Confined.refl _ _)
    ⟨rfl, fun other otherHeld => by rw [held] at otherHeld; cases otherHeld; rfl⟩
  cil_checked_steps [readable.facts held valueReadable.live]

#print axioms secondValue_holds

/-- A null node throws `NullReferenceException` at `SecondValue`'s first field load, pc 1. -/
theorem secondValue_null_node_throws (memory : Memory) :
    ∃ fuel, invoke Extracted.program fuel secondValue [.object .null] memory =
      .error ⟨secondValue, 1, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps

#print axioms secondValue_null_node_throws

/-- A node whose `Next` is null throws `NullReferenceException` at the second field load, pc 2:
    the first load succeeds and pushes the null it reads. -/
theorem secondValue_null_next_throws (memory : Memory) (node : Reference)
    (readable : Node.Next.Readable memory node) (held : Node.Next.of memory node = .null) :
    ∃ fuel, invoke Extracted.program fuel secondValue [.object (.address node)] memory =
      .error ⟨secondValue, 2, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps [readable.load_null held]

#print axioms secondValue_null_next_throws

/-- A call confined to `node.Next` keeps the `Value` of every node, `node` included: a `Value`
    is the first field, which lies before the `Next` slot. -/
theorem value_after_link {memory final : Memory} {node other : Reference}
    (readable : Node.Value.Readable memory other)
    (framed : Confined [Node.Next.entry node] memory final) :
    Node.Value.Readable final other ∧ Node.Value.of final other = Node.Value.of memory other :=
  readable.frame framed fun _ member =>
    List.mem_singleton.mp member ▸ apart_of_offsets (Or.inl (Nat.le_refl _))

#print axioms value_after_link

/-- A call confined to `node.Next` keeps what `Next` holds in every other node. -/
theorem next_after_link {memory final : Memory} {node other : Reference}
    (nodeLive : LiveObject memory node) (otherReadable : Node.Next.Readable memory other)
    (framed : Confined [Node.Next.entry node] memory final) (distinct : node ≠ other) :
    Node.Next.of final other = Node.Next.of memory other :=
  (otherReadable.frame framed fun _ member => List.mem_singleton.mp member ▸
    apart_of_objects otherReadable.live nodeLive distinct rfl).2

#print axioms next_after_link

/-- `Link`'s postcondition names only caller identities, so it holds of any execution whose
    caller memory agrees: the premise `MethodContract.Holds.of_allocationRenaming` asks for to
    transfer `linkContract` to a program that allocates different private storage. -/
theorem link_post_stable (input : Reference × Reference) (initial source target : Memory)
    (output : List Value) (pre : linkContract.pre input initial)
    (bytes : BytesBelow initial.nextIdentity source target)
    (agree : SlotsAgreeBelow initial.nextIdentity source target)
    (grows : initial.nextIdentity ≤ target.nextIdentity)
    (post : linkContract.post input initial source output) :
    linkContract.post input initial target output := by
  obtain ⟨node, next⟩ := input
  obtain ⟨owned, nextLive⟩ := pre
  obtain ⟨returned, held⟩ := post
  exact ⟨returned, held.of_agree bytes agree owned.old nextLive.old grows⟩

#print axioms link_post_stable

/-- `Link` meets its contract in any program that renames this one's private storage, such as one
    whose locals take more homes, from every initial memory a caller can hold: well-formed, with
    bounded static bindings and string literals. -/
theorem link_holds_renamed {target : CIL.Program}
    (programs : ProgramRenaming Extracted.program target) :
    linkContract.fromReadyMemory.Holds target link :=
  link_holds.fromReadyMemory.of_allocationRenaming programs
    (fun _ _ ready => ⟨ready.1, ready.2.1, ready.2.2.1⟩)
    (fun _ _ _ _ _ post => ⟨[], post.1⟩)
    (fun input initial _ _ output ready bytes agree grows post =>
      link_post_stable input initial _ _ output ready.2.2.2 bytes agree grows post)

#print axioms link_holds_renamed

/-- `LinkedValue(node, next)` returns `next.Value` and leaves `next` in `node.Next`, whether or
    not `next` is `node`; its footprint is the one slot `Link` writes. -/
def linkedValueContract : MethodContract (Reference × Reference) W64 where
  args := fun (node, next) => [.object (.address node), .object (.address next)]
  results value := [.scalar (.i64 value)]
  pre := fun (node, next) memory => Node.Next.Owned memory node ∧ Node.Value.Readable memory next
  footprint := fun (node, _) => [Node.Next.entry node]
  post := fun (node, next) initial final result => result = Node.Value.of initial next ∧
    Node.Next.Holds final node (.address next)

/-- `LinkedValue` meets its contract given only the contracts of `Link` and `SecondValue`: the
    `Value` of `next` is framed across `Link`'s footprint. -/
theorem linkedValue_holds (linked : linkContract.Holds Extracted.program link)
    (second : secondValueContract.Holds Extracted.program secondValue) :
    linkedValueContract.Holds Extracted.program linkedValue := by
  rintro ⟨node, next⟩ memory ⟨owned, nextReadable⟩
  have nextLive := nextReadable.live
  cil_contract_steps [linked, linkContract, owned, nextLive]
    with middle values linkCall
  obtain ⟨rfl, held⟩ := linkCall.post
  have linkFramed := linkCall.framed
  have kept := value_after_link nextReadable linkFramed
  have linked : secondValueContract.pre node middle := ⟨held.1.toReadable, next, held.2, kept.1⟩
  cil_contract_steps [second, secondValueContract, linked]
    with final result secondCall
  obtain ⟨rfl, returned⟩ := secondCall.post
  exact MethodContract.Holds.returns
    (linkFramed.trans (secondCall.framed.widen (by simp [secondValueContract])))
    ⟨(returned next held.2).trans kept.2, held⟩

#print axioms linkedValue_holds

/-- `LinkedValue` meets its contract, with `Link` and `SecondValue` discharged by their proofs. -/
theorem correctness : linkedValueContract.Holds Extracted.program linkedValue :=
  linkedValue_holds link_holds secondValue_holds

#print axioms correctness

/-- Linking a node to itself makes it its own successor: `LinkedValue(node, node)` returns
    `node.Value`. -/
theorem linkedValue_self (memory : Memory) (node : Reference)
    (owned : Node.Next.Owned memory node) (readable : Node.Value.Readable memory node) :
    ∃ fuel final, invoke Extracted.program fuel linkedValue
        [.object (.address node), .object (.address node)] memory =
      .ok (final, [.scalar (.i64 (Node.Value.of memory node))]) ∧
      Node.Next.of final node = .address node := by
  obtain ⟨final, result, call⟩ := correctness.result (node, node) ⟨owned, readable⟩
  obtain ⟨returned, held⟩ := call.post
  subst returned
  rw [exists_comm]
  simp only [exists_and_right]
  exact ⟨final, call.invoked, held.2⟩

#print axioms linkedValue_self

end ExampleProof
