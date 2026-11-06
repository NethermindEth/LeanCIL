import Extracted
import CIL.MethodIdentity
import CIL.Safety.ObjectFraming
import CIL.Safety.MethodContract

/-!
# Instance calls through `callvirt`

`Objects.DepositBoth(first, second, amount)` calls the instance method `Account.Deposit` on each
account. C# compiles both calls as `callvirt`, which checks the receiver for null before the
call; `Deposit` is not virtual, so the call has one target. The proof composes both calls through
`depositContract` and frames the second account across the first call, as `BumpBoth` does for a
static method. A null receiver throws `NullReferenceException` at the `callvirt` in the caller,
before `Deposit` runs.
-/

open CIL.Safety
open CIL (W64)
namespace ExampleProof

/-- The runtime type of `Examples.Account` instances. -/
def accountType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Account"

bind_method depositBoth depositBothBody :=
  "System.Void Examples.Objects::DepositBoth(Examples.Account,Examples.Account,System.UInt64)"
bind_callee deposit depositBody :=
  "System.Void Examples.Account::Deposit(System.UInt64)" from depositBothBody [0]

/-- `Balance` of the live account at `account` is a writable word holding some value, and is
    located at the account's own reference, being its first field. -/
def BalanceWord (memory : Memory) (account : Reference) : Prop :=
  objectFieldAddress memory (.address account) accountType 0 = .ok account ∧
    (∃ balance : W64, read memory account 8 1 = .ok (numberBytes balance.toNat 8)) ∧
    access memory account 8 1 true = .ok ()

/-- `account.Deposit(amount)` adds `amount` to `Balance` and writes no other byte. -/
def depositContract : MethodContract (Reference × W64) where
  args input := [.object (.address input.1), .scalar (.i64 input.2)]
  pre input memory := BalanceWord memory input.1
  footprint input := [(input.1, 8)]
  post input initial final values := values = [] ∧
    ∀ balance : W64, read initial input.1 8 1 = .ok (numberBytes balance.toNat 8) →
      read final input.1 8 1 = .ok (numberBytes (balance + input.2).toNat 8)

/-- Two reads of one word give the same value. -/
theorem word_unique {memory : Memory} {reference : Reference} {left right : W64}
    (leftRead : read memory reference 8 1 = .ok (numberBytes left.toNat 8))
    (rightRead : read memory reference 8 1 = .ok (numberBytes right.toNat 8)) : left = right := by
  have leftLoaded := load_word64_of_read leftRead
  rw [load_word64_of_read rightRead] at leftLoaded
  cases leftLoaded
  rfl

#print axioms word_unique

/-- `Deposit` meets its contract for every live account and amount. -/
theorem deposit_holds : depositContract.Holds Extracted.program deposit := by
  rintro ⟨account, amount⟩ memory ⟨located, ⟨balance, loaded⟩, writable⟩
  dsimp only [depositContract] at *
  obtain ⟨after, written, -, readback⟩ := store_word64 (balance + amount) writable
  have formed := formObject_of_objectFieldAddress located
  have value := load_word64_of_read loaded
  refine ⟨CIL.executionBound Extracted.program deposit, after, [], ?_,
    Confined.write written (by simp [numberBytes]), [], rfl, rfl, ?_⟩
  · cil_checked_steps [formed, located, value, written, accountType]
  · intro old oldLoaded
    rw [← word_unique loaded oldLoaded]
    exact readback

#print axioms deposit_holds

/-- `DepositBoth(first, second, amount)` adds `amount` to each account's `Balance`, twice to one
    account passed as both, and writes no other byte. -/
def depositBothContract : MethodContract (Reference × Reference × W64) where
  args input := [.object (.address input.1), .object (.address input.2.1),
    .scalar (.i64 input.2.2)]
  pre input memory := memory.WellFormed ∧ BalanceWord memory input.1 ∧
    BalanceWord memory input.2.1
  footprint input := [(input.1, 8), (input.2.1, 8)]
  post input initial final values := values = [] ∧
    ∀ first second : W64, read initial input.1 8 1 = .ok (numberBytes first.toNat 8) →
      read initial input.2.1 8 1 = .ok (numberBytes second.toNat 8) →
      if input.1 = input.2.1 then
        read final input.1 8 1 = .ok (numberBytes (first + input.2.2 + input.2.2).toNat 8)
      else
        read final input.1 8 1 = .ok (numberBytes (first + input.2.2).toNat 8) ∧
          read final input.2.1 8 1 = .ok (numberBytes (second + input.2.2).toNat 8)

/-- After `Deposit` on `first`, the balance of `second` is still a writable word: unchanged when
    the accounts differ, the deposited value when they are the same. -/
theorem balance_after_deposit {memory middle : Memory} {first second : Reference} {amount : W64}
    (formedMemory : memory.WellFormed) (firstWord : BalanceWord memory first)
    (secondWord : BalanceWord memory second)
    (framed : Confined [(first, 8)] memory middle)
    (deposited : ∀ balance : W64, read memory first 8 1 = .ok (numberBytes balance.toNat 8) →
      read middle first 8 1 = .ok (numberBytes (balance + amount).toNat 8)) :
    BalanceWord middle second := by
  obtain ⟨firstLocated, -, -⟩ := firstWord
  obtain ⟨secondLocated, ⟨secondBalance, secondLoaded⟩, secondWritable⟩ := secondWord
  have old := (formedMemory.1 _ _ (objectFieldAddress_allocated secondLocated).choose_spec).1
  refine ⟨objectFieldAddress_of_confined framed formedMemory secondLocated, ?_,
    (framed.access_write second old 8 1).trans secondWritable⟩
  by_cases same : first = second
  · subst same
    exact ⟨_, deposited _ secondLoaded⟩
  · exact ⟨_, framed.objectField_read_of_ne old firstLocated secondLocated
      (fun equal => same (ManagedReference.address.inj equal)) secondLoaded⟩

#print axioms balance_after_deposit

/-- `DepositBoth` meets its contract given only the contract of `Deposit`: each `callvirt` passes
    its null check on a live account and is composed through `depositContract`, and the second
    balance is framed across the first call. -/
theorem depositBoth_holds (holds : depositContract.Holds Extracted.program deposit) :
    depositBothContract.Holds Extracted.program depositBoth := by
  rintro ⟨first, second, amount⟩ memory ⟨formedMemory, firstWord, secondWord⟩
  dsimp only [depositBothContract]
  have firstFormed := formObject_of_objectFieldAddress firstWord.1
  have secondFormed := formObject_of_objectFieldAddress secondWord.1
  cil_contract_steps [holds, depositContract, firstWord, firstFormed, secondFormed]
  rename_i middle firstFramed values firstPost _
  obtain ⟨rfl, firstDeposited⟩ := firstPost
  have secondMiddle := balance_after_deposit formedMemory firstWord secondWord firstFramed
    firstDeposited
  have secondFormedMiddle := formObject_of_objectFieldAddress secondMiddle.1
  dsimp only [depositContract]
  cil_contract_steps [holds, depositContract, secondMiddle, secondFormedMiddle]
  rename_i final secondFramed values secondPost _
  obtain ⟨rfl, secondDeposited⟩ := secondPost
  dsimp only [depositContract] at firstFramed firstDeposited secondFramed secondDeposited ⊢
  cil_contract_steps []
  change Confined _ memory final ∧ depositBothContract.Returns _ memory final []
  obtain ⟨firstLocated, -, -⟩ := firstWord
  obtain ⟨secondLocated, -, -⟩ := secondWord
  have firstOld := (formedMemory.1 _ _ (objectFieldAddress_allocated firstLocated).choose_spec).1
  have secondOld :=
    (formedMemory.1 _ _ (objectFieldAddress_allocated secondLocated).choose_spec).1
  refine ⟨(firstFramed.widen (by simp)).trans (secondFramed.widen (by simp)), [], rfl, rfl, ?_⟩
  intro firstBalance secondBalance firstLoaded secondLoaded
  dsimp only
  split
  · rename_i same
    subst same
    exact secondDeposited _ (firstDeposited _ firstLoaded)
  · rename_i distinct
    have apart : ManagedReference.address first ≠ .address second :=
      fun equal => distinct (ManagedReference.address.inj equal)
    refine ⟨secondFramed.objectField_read_of_ne (Nat.lt_of_lt_of_le firstOld firstFramed.grows)
      (objectFieldAddress_of_confined firstFramed formedMemory secondLocated)
      (objectFieldAddress_of_confined firstFramed formedMemory firstLocated) (Ne.symm apart)
      (firstDeposited _ firstLoaded), secondDeposited _ ?_⟩
    exact firstFramed.objectField_read_of_ne secondOld firstLocated secondLocated apart
      secondLoaded

#print axioms depositBoth_holds

/-- `DepositBoth` meets its contract, with `Deposit` discharged by its own proof. -/
theorem correctness : depositBothContract.Holds Extracted.program depositBoth :=
  depositBoth_holds deposit_holds

#print axioms correctness

/-- A null `first` throws `NullReferenceException` at the first `callvirt`, pc 2 of
    `DepositBoth` itself, whatever `second` is: the receiver check runs in the caller, so
    `Deposit` is never entered, unlike a null account passed to a static method. -/
theorem first_null_throws (memory : Memory) (second : Reference) (amount : W64)
    (secondFormed : formObject memory (.address second) = .ok (.object (.address second))) :
    ∃ fuel, invoke Extracted.program fuel depositBoth
        [.object .null, .object (.address second), .scalar (.i64 amount)] memory =
      .error ⟨depositBoth, 2, .thrown "System.NullReferenceException"⟩ := by
  refine ⟨CIL.executionBound Extracted.program depositBoth, ?_⟩
  cil_checked_steps [secondFormed]

#print axioms first_null_throws
end ExampleProof
