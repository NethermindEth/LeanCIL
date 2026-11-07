import Extracted
import CIL.MethodIdentity
import CIL.Safety.ObjectFraming
import CIL.Safety.RenamedMemoryBelow

/-!
# Linked nodes

`Examples.Node` holds a `ulong` `Value` and a `Next` reference to another node. `Link(node,
next)` stores `next` into `node.Next`, `SecondValue(node)` reads `node.Next.Value`, and
`LinkedValue(node, next)` calls both. A reference lives in its field's slot, not in bytes, so
`Link` changes one slot, which is its whole footprint. Proved: each method's contract,
`LinkedValue` returning `next.Value` whether or not `next` is `node`, the
`NullReferenceException` of `SecondValue` at each field load, `Link` keeping every other node's
`Next` and every node's `Value`, and `Link`'s postcondition surviving a renaming of fresh
allocations.
-/

open CIL.Safety
open CIL (W64)
namespace ExampleProof

/-- The runtime type of `Examples.Node` instances. -/
def nodeType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Node"

bind_method linkedValue linkedValueBody :=
  "System.UInt64 Examples.Objects::LinkedValue(Examples.Node,Examples.Node)"
bind_callee link linkBody :=
  "System.Void Examples.Objects::Link(Examples.Node,Examples.Node)" from linkedValueBody
bind_callee secondValue secondValueBody :=
  "System.UInt64 Examples.Objects::SecondValue(Examples.Node)" from linkedValueBody

/-- The `Next` field of the live node `node`, its second field: located 8 bytes into the node,
    with a readable and writable slot. -/
def NextSlot (memory : Memory) (node : Reference) : Prop :=
  objectFieldAddress memory (.address node) nodeType 8 = .ok ⟨node.allocation, 8⟩ ∧
    access memory ⟨node.allocation, 8⟩ 8 1 false = .ok () ∧
    access memory ⟨node.allocation, 8⟩ 8 1 true = .ok ()

/-- The `Value` field of the live node `node`, its first field, holds `value`. -/
def ValueWord (memory : Memory) (node : Reference) (value : W64) : Prop :=
  objectFieldAddress memory (.address node) nodeType 0 = .ok node ∧
    read memory node 8 1 = .ok (numberBytes value.toNat 8)

/-- `node.Next` is a slot holding some live node whose `Value` is a word. -/
def LinkedWord (memory : Memory) (node : Reference) : Prop :=
  NextSlot memory node ∧
    ∃ next value, memory.slots node.allocation 8 = .address next ∧ ValueWord memory next value

/-- `Link(node, next)` stores `next` into `node.Next`; the slot stays readable, and its
    footprint is that slot alone, so no byte and no other field changes. -/
def linkContract : MethodContract (Reference × Reference) where
  args input := [.object (.address input.1), .object (.address input.2)]
  pre input memory := memory.WellFormed ∧ NextSlot memory input.1 ∧
    formObject memory (.address input.2) = .ok (.object (.address input.2))
  footprint input := [(⟨input.1.allocation, 8⟩, 8)]
  post input _ final values := values = [] ∧
    final.slots input.1.allocation 8 = .address input.2 ∧
    access final ⟨input.1.allocation, 8⟩ 8 1 false = .ok ()

/-- `SecondValue(node)` returns the `Value` of the node `node.Next` holds and changes nothing. -/
def secondValueContract : MethodContract Reference W64 where
  args node := [.object (.address node)]
  results value := [.scalar (.i64 value)]
  pre node memory := LinkedWord memory node
  footprint _ := []
  post node initial final result := final = initial ∧
    ∀ next value, initial.slots node.allocation 8 = .address next →
      read initial next 8 1 = .ok (numberBytes value.toNat 8) → result = value

/-- Two reads of one word give the same value. -/
theorem word_unique {memory : Memory} {reference : Reference} {left right : W64}
    (leftRead : read memory reference 8 1 = .ok (numberBytes left.toNat 8))
    (rightRead : read memory reference 8 1 = .ok (numberBytes right.toNat 8)) : left = right := by
  have leftLoaded := load_word64_of_read leftRead
  rw [load_word64_of_read rightRead] at leftLoaded
  cases leftLoaded
  rfl

#print axioms word_unique

/-- `Link` meets its contract: one `stfld` into the `Next` slot. -/
theorem link_holds : linkContract.Holds Extracted.program link := by
  rintro ⟨node, next⟩ memory ⟨-, ⟨located, readable, writable⟩, nextFormed⟩
  dsimp only [linkContract] at *
  have nodeFormed := formObject_of_objectFieldAddress located
  have stored := storeSlot_of_access (value := .address next) writable nextFormed
  refine ⟨CIL.executionBound Extracted.program link,
    setSlot memory ⟨node.allocation, 8⟩ (.address next), [], ?_,
    Confined.setSlot _ (List.mem_singleton_self _) (by decide), [], rfl, rfl,
    setSlot_slots_same memory ⟨node.allocation, 8⟩ _, readable⟩
  cil_checked_steps [nodeFormed, nextFormed, located, stored, nodeType]

#print axioms link_holds

/-- `SecondValue` meets its contract: two field loads, through the `Next` slot. -/
theorem secondValue_holds : secondValueContract.Holds Extracted.program secondValue := by
  rintro node memory ⟨⟨located, readable, -⟩, next, value, held, nextLocated, loaded⟩
  dsimp only [secondValueContract] at *
  have nodeFormed := formObject_of_objectFieldAddress located
  have nextFormed := formObject_of_objectFieldAddress nextLocated
  have slot := loadSlot_of_access readable
  have word := load_word64_of_read loaded
  refine ⟨CIL.executionBound Extracted.program secondValue, memory, [.scalar (.i64 value)], ?_,
    Confined.refl _ _, value, rfl, rfl, ?_⟩
  · cil_checked_steps [nodeFormed, located, slot, held, nextFormed, nextLocated, word, nodeType]
  · intro other otherValue otherHeld otherLoaded
    rw [held] at otherHeld
    cases otherHeld
    exact word_unique loaded otherLoaded

#print axioms secondValue_holds

/-- A null node throws `NullReferenceException` at `SecondValue`'s first field load, pc 1. -/
theorem secondValue_null_node_throws (memory : Memory) :
    ∃ fuel, invoke Extracted.program fuel secondValue [.object .null] memory =
      .error ⟨secondValue, 1, .thrown "System.NullReferenceException"⟩ := by
  refine ⟨CIL.executionBound Extracted.program secondValue, ?_⟩
  cil_checked_steps [objectFieldAddress]

#print axioms secondValue_null_node_throws

/-- A node whose `Next` is null throws `NullReferenceException` at the second field load, pc 2:
    the first load succeeds and pushes the null it reads. -/
theorem secondValue_null_next_throws (memory : Memory) (node : Reference)
    (located : objectFieldAddress memory (.address node) nodeType 8 = .ok ⟨node.allocation, 8⟩)
    (readable : access memory ⟨node.allocation, 8⟩ 8 1 false = .ok ())
    (held : memory.slots node.allocation 8 = .null) :
    ∃ fuel, invoke Extracted.program fuel secondValue [.object (.address node)] memory =
      .error ⟨secondValue, 2, .thrown "System.NullReferenceException"⟩ := by
  have nodeFormed := formObject_of_objectFieldAddress located
  have slot := loadSlot_of_access readable
  have nullThrows : objectFieldAddress memory .null nodeType 0 =
      .error (.thrown "System.NullReferenceException") := rfl
  refine ⟨CIL.executionBound Extracted.program secondValue, ?_⟩
  cil_checked_steps [nodeFormed, located, slot, held, formObject_null, nullThrows, nodeType]

#print axioms secondValue_null_next_throws

/-- A call confined to `node.Next` keeps the `Value` of every node, `node` included: a `Value`
    is the first field, which lies before the `Next` slot. -/
theorem value_after_link {memory final : Memory} {node other : Reference} {value : W64}
    (formed : memory.WellFormed) (otherValue : ValueWord memory other value)
    (framed : Confined [(⟨node.allocation, 8⟩, 8)] memory final) :
    ValueWord final other value := by
  obtain ⟨otherLocated, loaded⟩ := otherValue
  have old := (formed.allocations _ _ (objectFieldAddress_allocated otherLocated).choose_spec).1
  refine ⟨objectFieldAddress_of_confined framed formed otherLocated,
    (framed.read_eq other old 8 1 (Outside.of_apart ?_)).trans loaded⟩
  intro entry member
  simp only [List.mem_singleton] at member
  subst member
  obtain ⟨-, origin⟩ := objectFieldAddress_position otherLocated
  right
  left
  simp only at origin ⊢
  omega

#print axioms value_after_link

/-- A call confined to `node.Next` keeps what `Next` holds in every other node. -/
theorem next_after_link {memory final : Memory} {node other : Reference}
    (formed : memory.WellFormed) (nodeSlot : NextSlot memory node)
    (otherSlot : NextSlot memory other)
    (framed : Confined [(⟨node.allocation, 8⟩, 8)] memory final) (distinct : node ≠ other) :
    final.slots other.allocation 8 = memory.slots other.allocation 8 :=
  framed.objectSlot_of_ne
    (formed.allocations _ _ (objectFieldAddress_allocated otherSlot.1).choose_spec).1
    nodeSlot.1 otherSlot.1 fun equal => distinct (ManagedReference.address.inj equal)

#print axioms next_after_link

/-- `Link`'s postcondition names only caller identities, so it holds of any execution whose
    caller memory agrees: the premise `MethodContract.Holds.of_allocationRenaming` asks for to
    transfer `linkContract` to a program that allocates different private storage. -/
theorem link_post_stable (input : Reference × Reference) (initial source target : Memory)
    (output : List Value) (pre : linkContract.pre input initial)
    (bytes : BytesBelow initial.nextIdentity source target)
    (agree : SlotsAgreeBelow initial.nextIdentity source target)
    (post : linkContract.post input initial source output) :
    linkContract.post input initial target output := by
  obtain ⟨node, next⟩ := input
  obtain ⟨formed, ⟨located, -, -⟩, nextFormed⟩ := pre
  obtain ⟨returned, held, readable⟩ := post
  have old := (formed.allocations _ _ (objectFieldAddress_allocated located).choose_spec).1
  refine ⟨returned, agree.held old held (formObject_issued nextFormed formed), ?_⟩
  rw [bytes.access _ old]
  exact readable

#print axioms link_post_stable

/-- `LinkedValue(node, next)` returns `next.Value` and leaves `next` in `node.Next`, whether or
    not `next` is `node`; its footprint is the one slot `Link` writes. -/
def linkedValueContract : MethodContract (Reference × Reference × W64) W64 where
  args input := [.object (.address input.1), .object (.address input.2.1)]
  results value := [.scalar (.i64 value)]
  pre input memory := memory.WellFormed ∧ NextSlot memory input.1 ∧
    ValueWord memory input.2.1 input.2.2
  footprint input := [(⟨input.1.allocation, 8⟩, 8)]
  post input _ final result := result = input.2.2 ∧
    final.slots input.1.allocation 8 = .address input.2.1

/-- `LinkedValue` meets its contract given only the contracts of `Link` and `SecondValue`: the
    `Value` of `next` and the `Next` slot of `node` are framed across `Link`'s footprint. -/
theorem linkedValue_holds (linked : linkContract.Holds Extracted.program link)
    (second : secondValueContract.Holds Extracted.program secondValue) :
    linkedValueContract.Holds Extracted.program linkedValue := by
  rintro ⟨node, next, value⟩ memory ⟨formed, nodeSlot, nextValue⟩
  dsimp only [linkedValueContract]
  have nodeFormed := formObject_of_objectFieldAddress nodeSlot.1
  have nextFormed := formObject_of_objectFieldAddress nextValue.1
  cil_contract_steps [linked, linkContract, formed, nodeSlot, nodeFormed, nextFormed]
  rename_i middle linkFramed values linkPost _
  obtain ⟨rfl, held, readable⟩ := linkPost
  have old :=
    (formed.allocations _ _ (objectFieldAddress_allocated nodeSlot.1).choose_spec).1
  have middleSlot : NextSlot middle node :=
    ⟨objectFieldAddress_of_confined linkFramed formed nodeSlot.1, readable,
      (linkFramed.access_write _ old 8 1).trans nodeSlot.2.2⟩
  have middleWord : LinkedWord middle node :=
    ⟨middleSlot, next, value, held, value_after_link formed nextValue linkFramed⟩
  have nodeFormedMiddle := formObject_of_objectFieldAddress middleSlot.1
  cil_contract_steps [second, secondValueContract, middleWord, nodeFormedMiddle]
  rename_i final unchanged result secondPost _
  obtain ⟨rfl, returned⟩ := secondPost
  change Confined _ memory final ∧ linkedValueContract.Returns _ memory final _
  refine ⟨linkFramed.trans (unchanged.widen (by simp [secondValueContract])), result, rfl,
    returned next value held (value_after_link formed nextValue linkFramed).2, held⟩

#print axioms linkedValue_holds

/-- `LinkedValue` meets its contract, with `Link` and `SecondValue` discharged by their proofs. -/
theorem correctness : linkedValueContract.Holds Extracted.program linkedValue :=
  linkedValue_holds link_holds secondValue_holds

#print axioms correctness

/-- Linking a node to itself makes it its own successor: `LinkedValue(node, node)` returns
    `node.Value`. -/
theorem linkedValue_self (memory : Memory) (node : Reference) (value : W64)
    (formed : memory.WellFormed) (nodeSlot : NextSlot memory node)
    (nodeValue : ValueWord memory node value) :
    ∃ fuel final, invoke Extracted.program fuel linkedValue
        [.object (.address node), .object (.address node)] memory =
      .ok (final, [.scalar (.i64 value)]) ∧ final.slots node.allocation 8 = .address node := by
  obtain ⟨fuel, final, values, invoked, -, result, encoded, returned, held⟩ :=
    correctness (node, node, value) memory ⟨formed, nodeSlot, nodeValue⟩
  dsimp only [linkedValueContract] at invoked encoded returned held
  subst returned
  exact ⟨fuel, final, encoded ▸ invoked, held⟩

#print axioms linkedValue_self

end ExampleProof
