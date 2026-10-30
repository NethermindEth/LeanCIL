import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.ConstructContract
import CIL.Safety.WordMemory
import CIL.Safety.ReturnMemory

/-! The C# fixture's bodies: `Root(x, y) => new Pair(x, y).High + new Word(y, 1, 2, x).U3`. -/
namespace Extracted

open CIL

def method0Signature : String := "System.UInt64 Constructs.Calls::Root(System.UInt64,System.UInt64)"
def method1Signature : String := "System.Void Constructs.Word::.ctor(System.UInt64,System.UInt64,System.UInt64,System.UInt64)"
def method2Signature : String := "System.Void Constructs.Pair::.ctor(System.UInt64,System.UInt64)"
@[cil_code] def method0 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .arg 1, .newAggregate 2 2 16, .fieldAt 8 8, .arg 1, .const32 1, .convI8, .const32 2, .convI8, .arg 0,
    .newAggregate 1 4 32, .fieldAt 24 8, .add, .ret] }
@[cil_code] def method1 : Method := { returnsValue := false, locals := [], code :=
  [.arg 0, .arg 1, .setFieldAt 0 8, .arg 0, .arg 2, .setFieldAt 8 8, .arg 0, .arg 3, .setFieldAt 16 8,
    .arg 0, .arg 4, .setFieldAt 24 8, .ret] }
@[cil_code] def method2 : Method := { returnsValue := false, locals := [], code :=
  [.arg 0, .arg 1, .setFieldAt 0 8, .arg 0, .arg 2, .setFieldAt 8 8, .ret] }
@[cil_code] def program : Program := [method0, method1, method2]
def signatures : List String := [method0Signature, method1Signature, method2Signature]

end Extracted

namespace Tests.ConstructContract

open CIL.Safety

bind_method root rootBody := "System.UInt64 Constructs.Calls::Root(System.UInt64,System.UInt64)"
bind_method pair pairBody := "System.Void Constructs.Pair::.ctor(System.UInt64,System.UInt64)"
bind_method word wordBody := "System.Void Constructs.Word::.ctor(System.UInt64,System.UInt64,System.UInt64,System.UInt64)"

structure PairInput where
  this : Reference
  low : CIL.W64
  high : CIL.W64

def pairBytes (input : PairInput) : List (BitVec 8) :=
  numberBytes input.low.toNat 8 ++ numberBytes input.high.toNat 8

/-- `newobj` supplies formed, writable storage; the constructor fixes every byte of it. -/
def pairContract : MethodContract PairInput Unit where
  args input := [.reference (.address input.this), .scalar (.i64 input.low), .scalar (.i64 input.high)]
  results _ := []
  pre input m := m.WellFormed ∧ access m input.this 16 1 true = .ok ()
  footprint input := [(input.this, 16)]
  post input _ final _ := read final input.this 16 1 = .ok (pairBytes input)

theorem pair_constructs : pairContract.Constructs 16 PairInput.this fun input _ => pairBytes input :=
  ⟨fun _ => rfl, fun _ _ _ _ readback => readback⟩

structure WordInput where
  this : Reference
  u0 : CIL.W64
  u1 : CIL.W64
  u2 : CIL.W64
  u3 : CIL.W64

def wordBytes (input : WordInput) : List (BitVec 8) :=
  numberBytes input.u0.toNat 8 ++ numberBytes input.u1.toNat 8 ++ numberBytes input.u2.toNat 8 ++
    numberBytes input.u3.toNat 8

/-- The 32-byte, four-limb layout of a `UInt256`. -/
def wordContract : MethodContract WordInput Unit where
  args input := [.reference (.address input.this), .scalar (.i64 input.u0), .scalar (.i64 input.u1),
    .scalar (.i64 input.u2), .scalar (.i64 input.u3)]
  results _ := []
  pre input m := m.WellFormed ∧ access m input.this 32 1 true = .ok ()
  footprint input := [(input.this, 32)]
  post input _ final _ := read final input.this 32 1 = .ok (wordBytes input)

theorem word_constructs : wordContract.Constructs 32 WordInput.this fun input _ => wordBytes input :=
  ⟨fun _ => rfl, fun _ _ _ _ readback => readback⟩

def rootContract : MethodContract (CIL.W64 × CIL.W64) CIL.W64 where
  args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
  results v := [.scalar (.i64 v)]
  pre _ m := m.WellFormed
  footprint _ := []
  post input _ _ v := v = input.2 + input.1

theorem pair_holds : pairContract.Holds Extracted.program pair := by
  rintro ⟨⟨id, offset⟩, low, high⟩ m ⟨formed, writable⟩
  dsimp only [pairContract] at *
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have length : ∀ v : CIL.W64, (numberBytes v.toNat 8).length = 8 := by simp [numberBytes]
  have first := ready.slice formed 0 8 (by decide) (by decide)
  obtain ⟨m1, w1⟩ := write_succeeds (bytes := numberBytes low.toNat 8) (by simpa only [length] using first.access)
  have formed1 := write_preserves_wellFormed _ _ _ _ _ formed w1
  have ready1 := ready.after_write w1
  have second := ready1.slice formed1 8 8 (by decide) (by decide)
  obtain ⟨m2, w2⟩ := write_succeeds (bytes := numberBytes high.toNat 8) (by simpa only [length] using second.access)
  have a1 := ready.add_slice formed 1 0 8 (by decide) (by decide)
  have a2 := ready1.add_slice formed1 1 8 8 (by decide) (by decide)
  have f0 := access_reference_valid _ _ _ _ _ writable
  have f1 := access_reference_valid _ _ _ _ _ ready1.access
  simp only [Nat.add_zero, Nat.one_mul] at a1 a2 w1
  have low1 := write_readback _ _ _ _ _ w1
  have low2 := write_preserves_disjoint_read w2 low1 (Or.inr (Or.inl (by simp [length])))
  have high2 := write_readback _ _ _ _ _ w2
  rw [length] at low2 high2
  have readback := read_append (left := 8) (right := 8) ((ready1.after_write w2).access) low2 high2
  have c1 : Confined [(⟨id, offset⟩, 16)] m m1 :=
    Confined.write_within w1 ⟨_, List.mem_singleton_self _, rfl, by simp, by simp [length]⟩
  have c2 : Confined [(⟨id, offset⟩, 16)] m1 m2 :=
    Confined.write_within w2 ⟨_, List.mem_singleton_self _, rfl, by simp, by simp [length]⟩
  refine ⟨8, m2, [], ?_, c1.trans c2, (), rfl, readback⟩
  cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
    f0, f1, a1, a2, w1, w2, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem word_holds : wordContract.Holds Extracted.program word := by
  rintro ⟨⟨id, offset⟩, u0, u1, u2, u3⟩ m ⟨formed, writable⟩
  dsimp only [wordContract] at *
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have length : ∀ v : CIL.W64, (numberBytes v.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨m1, w1⟩ := write_succeeds (bytes := numberBytes u0.toNat 8)
    (by simpa only [length] using (ready.slice formed 0 8 (by decide) (by decide)).access)
  have formed1 := write_preserves_wellFormed _ _ _ _ _ formed w1
  have ready1 := ready.after_write w1
  obtain ⟨m2, w2⟩ := write_succeeds (bytes := numberBytes u1.toNat 8)
    (by simpa only [length] using (ready1.slice formed1 8 8 (by decide) (by decide)).access)
  have formed2 := write_preserves_wellFormed _ _ _ _ _ formed1 w2
  have ready2 := ready1.after_write w2
  obtain ⟨m3, w3⟩ := write_succeeds (bytes := numberBytes u2.toNat 8)
    (by simpa only [length] using (ready2.slice formed2 16 8 (by decide) (by decide)).access)
  have formed3 := write_preserves_wellFormed _ _ _ _ _ formed2 w3
  have ready3 := ready2.after_write w3
  obtain ⟨m4, w4⟩ := write_succeeds (bytes := numberBytes u3.toNat 8)
    (by simpa only [length] using (ready3.slice formed3 24 8 (by decide) (by decide)).access)
  have formed4 := write_preserves_wellFormed _ _ _ _ _ formed3 w4
  have ready4 := ready3.after_write w4
  have a1 := ready.add_slice formed 1 0 8 (by decide) (by decide)
  have a2 := ready1.add_slice formed1 1 8 8 (by decide) (by decide)
  have a3 := ready2.add_slice formed2 1 16 8 (by decide) (by decide)
  have a4 := ready3.add_slice formed3 1 24 8 (by decide) (by decide)
  have f0 := access_reference_valid _ _ _ _ _ writable
  have f1 := access_reference_valid _ _ _ _ _ ready1.access
  have f2 := access_reference_valid _ _ _ _ _ ready2.access
  have f3 := access_reference_valid _ _ _ _ _ ready3.access
  simp only [Nat.add_zero, Nat.one_mul] at a1 a2 a3 a4 w1
  have r1 := write_readback _ _ _ _ _ w1
  have r2 := write_readback _ _ _ _ _ w2
  have r3 := write_readback _ _ _ _ _ w3
  have r4 := write_readback _ _ _ _ _ w4
  rw [length] at r1 r2 r3 r4
  -- Each limb survives the later, disjoint limb writes.
  have later : ∀ {a b : Memory} {r : Reference} {bytes old : List (BitVec 8)} {start : Nat},
      write a { allocation := id, offset := offset + start } bytes 1 = .ok b →
      read a r 8 1 = .ok old → r.offset + 8 ≤ offset + start → read b r 8 1 = .ok old :=
    fun written readable before => write_preserves_disjoint_read written readable (Or.inr (Or.inl before))
  have two := read_append (left := 8) (right := 8) (ready4.slice formed4 0 16 (by decide) (by decide)).access
    (later w4 (later w3 (later w2 r1 (by simp)) (by simp)) (by simp)) (later w4 (later w3 r2 (by simp)) (by simp))
  have three := read_append (left := 16) (right := 8) (ready4.slice formed4 0 24 (by decide) (by decide)).access
    (by simpa using two) (later w4 r3 (by simp))
  have readback := read_append (left := 24) (right := 8) ready4.access (by simpa using three) r4
  have covered : ∀ {a b : Memory} {start : Nat} {bytes : List (BitVec 8)},
      write a { allocation := id, offset := offset + start } bytes 1 = .ok b → start + bytes.length ≤ 32 →
      Confined [(⟨id, offset⟩, 32)] a b :=
    fun written inside => Confined.write_within written ⟨_, List.mem_singleton_self _, rfl, by simp, by simp; omega⟩
  refine ⟨14, m4, [], ?_, (covered (start := 0) w1 (by simp [length])).trans ((covered w2 (by simp [length])).trans
    ((covered w3 (by simp [length])).trans (covered w4 (by simp [length])))), (), rfl, ?_⟩
  · cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
      f0, f1, f2, f3, a1, a2, a3, a4, w1, w2, w3, w4, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simpa [wordBytes, List.append_assoc] using readback

/-- Uses only the constructors' contracts at their `newobj` sites; neither constructor body is unfolded. -/
theorem root_holds (pairHolds : pairContract.Holds Extracted.program pair)
    (wordHolds : wordContract.Holds Extracted.program word) : rootContract.Holds Extracted.program root := by
  rintro ⟨x, y⟩ m formed
  dsimp only [rootContract, MethodContract.Returns] at *
  cil_contract_steps [checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cil_contract_construct pairHolds pair_constructs (fun this => ⟨this, x, y⟩) []
  · exact formed
  · exact fun _ _ storage => ⟨storage.formed, storage.writable⟩
  intro t1 m1 final1 _ storage1 _ formed1 _ framed1 _
  have length : ∀ n, (numberBytes n 8).length = 8 := by simp [numberBytes]
  have size1 : (pairBytes ⟨t1, x, y⟩).length = 16 := by simp [pairBytes, length]
  have high1 : ((pairBytes ⟨t1, x, y⟩).drop 8).take 8 = numberBytes y.toNat 8 := by
    simp [pairBytes, length, List.take_of_length_le]
  cil_contract_steps [checkedValue, numericValue, instruction, size1, high1, decode_word64,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cil_contract_construct wordHolds word_constructs (fun this => ⟨this, y, 1#64, 2#64, x⟩) []
  · exact formed1
  · exact fun _ _ storage => ⟨storage.formed, storage.writable⟩
  intro t2 m2 final2 _ storage2 _ formed2 _ framed2 _
  have size2 : (wordBytes ⟨t2, y, 1#64, 2#64, x⟩).length = 32 := by simp [wordBytes, length]
  have top2 : ((wordBytes ⟨t2, y, 1#64, 2#64, x⟩).drop 24).take 8 = numberBytes x.toNat 8 := by
    simp only [wordBytes, List.append_assoc]
    rw [List.drop_append, List.drop_eq_nil_of_le (by simp [length]), length, List.drop_append,
      List.drop_eq_nil_of_le (by simp [length]), length, List.drop_left' (length _)]
    simp [length, List.take_of_length_le]
  cil_contract_steps [checkedValue, numericValue, instruction, size2, top2, decode_word64,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  -- Both temporaries are fresh in the caller's frame, which expires them on return.
  have kept1 : Confined [] m final1 :=
    (storage1.confined framed1).forget_fresh (fresh := [(t1, 16)]) (by simp [storage1.fresh])
  have kept2 : Confined [] final1 final2 :=
    (storage2.confined framed2).forget_fresh (fresh := [(t2, 32)]) (by simp [storage2.fresh])
  have owned : ∀ id ∈ [t2.allocation, t1.allocation], m.nextIdentity ≤ id := by
    simp [storage1.fresh, storage2.fresh, kept1.grows]
  exact ⟨(kept1.trans kept2).after_leaveFrame owned, _, rfl, rfl⟩

theorem root_correct : rootContract.Holds Extracted.program root := root_holds pair_holds word_holds

/-! `newobj` zeroes its storage first, so an unassigned `High` reads back as zero, not uninitialized. -/
namespace Defaults

@[cil_code] def caller : CIL.Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .newAggregate 1 1 16, .fieldAt 8 8, .ret] }
@[cil_code] def lowOnly : CIL.Method := { returnsValue := false, locals := [], code :=
  [.arg 0, .arg 1, .setFieldAt 0 8, .ret] }
@[cil_code] def program : CIL.Program := [caller, lowOnly]

structure LowInput where
  this : Reference
  low : CIL.W64

def lowBytes (input : LowInput) : List (BitVec 8) := numberBytes input.low.toNat 8 ++ List.replicate 8 0

/-- The precondition includes the zeroed storage that `newobj` supplies. -/
def lowContract : MethodContract LowInput Unit where
  args input := [.reference (.address input.this), .scalar (.i64 input.low)]
  results _ := []
  pre input m := m.WellFormed ∧ access m input.this 16 1 true = .ok () ∧
    read m input.this 16 1 = .ok (List.replicate 16 0)
  footprint input := [(input.this, 16)]
  post input _ final _ := read final input.this 16 1 = .ok (lowBytes input)

theorem low_constructs : lowContract.Constructs 16 LowInput.this fun input _ => lowBytes input :=
  ⟨fun _ => rfl, fun _ _ _ _ readback => readback⟩

theorem low_holds : lowContract.Holds program 1 := by
  rintro ⟨⟨id, offset⟩, low⟩ m ⟨formed, writable, zeroed⟩
  dsimp only [lowContract] at *
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have length : ∀ n, (numberBytes n 8).length = 8 := by simp [numberBytes]
  obtain ⟨m1, w1⟩ := write_succeeds (bytes := numberBytes low.toNat 8)
    (by simpa only [length] using (ready.slice formed 0 8 (by decide) (by decide)).access)
  have a1 := ready.add_slice formed 1 0 8 (by decide) (by decide)
  have f0 := access_reference_valid _ _ _ _ _ writable
  simp only [Nat.add_zero, Nat.one_mul] at a1 w1
  have assigned := write_readback _ _ _ _ _ w1
  rw [length] at assigned
  have untouched := write_preserves_disjoint_read w1 (read_slice_bytes formed zeroed 8 8 (by decide) (by decide))
    (Or.inr (Or.inr (by simp [length])))
  have readback := read_append (left := 8) (right := 8) (ready.after_write w1).access assigned untouched
  refine ⟨5, m1, [], ?_, Confined.write_within w1 ⟨_, List.mem_singleton_self _, rfl, by simp, by simp [length]⟩,
    (), rfl, by simpa [lowBytes] using readback⟩
  cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
    f0, a1, w1, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

def callerContract : MethodContract CIL.W64 CIL.W64 where
  args x := [.scalar (.i64 x)]
  results v := [.scalar (.i64 v)]
  pre _ m := m.WellFormed
  footprint _ := []
  post _ _ _ v := v = 0

theorem caller_holds (lowHolds : lowContract.Holds program 1) : callerContract.Holds program 0 := by
  intro x m formed
  dsimp only [callerContract, MethodContract.Returns] at *
  cil_contract_steps [checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cil_contract_construct lowHolds low_constructs (fun this => ⟨this, x⟩) []
  · exact formed
  · exact fun _ _ storage => ⟨storage.formed, storage.writable, storage.zeroed⟩
  intro t m1 final _ storage _ _ _ framed _
  have size : (lowBytes ⟨t, x⟩).length = 16 := by simp [lowBytes, numberBytes]
  have high : ((lowBytes ⟨t, x⟩).drop 8).take 8 = List.replicate 8 0 := by
    simp [lowBytes, numberBytes, List.take_of_length_le]
  have zero : BitVec.ofNat 64 (byteNumber (List.replicate 8 (0 : BitVec 8))) = 0 := by decide
  cil_contract_steps [checkedValue, numericValue, instruction, size, high, zero,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have kept : Confined [] m final :=
    (storage.confined framed).forget_fresh (fresh := [(t, 16)]) (by simp [storage.fresh])
  exact ⟨kept.after_leaveFrame (by simp [storage.fresh]), _, rfl, rfl⟩

theorem caller_correct : callerContract.Holds program 0 := caller_holds low_holds

end Defaults

/-! Contracts without write authority, with writes outside the footprint, or with a narrower readback fail. -/
namespace Rejected

/-- Initialized, readable storage without write authority. -/
def readOnly : Memory := {
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨16, 1, []⟩, true, [16]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 16, true, false⟩]
  nextIdentity := 1 }

theorem readOnly_formed : readOnly.WellFormed := by
  refine ⟨fun id allocation found => ?_, fun view member => ?_⟩
  · by_cases zero : id = 0
    · subst zero
      simp only [readOnly, ite_true, Option.some.injEq] at found
      subst found
      exact ⟨by decide, by decide, by simp, by simp⟩
    · simp [readOnly, zero] at found
  · simp only [readOnly, List.mem_singleton] at member
    subst member
    exact ⟨_, rfl, by decide⟩

/-- `pairContract` without the write authority that `newobj` supplies. -/
def unguardedContract : MethodContract PairInput Unit :=
  { pairContract with pre := fun input m => m.WellFormed ∧ read m input.this 16 1 = .ok (List.replicate 16 0) }

/-- Readable, zeroed storage is not enough: the constructor's first store faults without write authority. -/
theorem missing_authority_rejected : ¬ unguardedContract.Holds Extracted.program pair := by
  intro holds
  obtain ⟨fuel, final, values, ran, -⟩ := holds ⟨⟨0, 0⟩, 0, 0⟩ readOnly ⟨readOnly_formed, rfl⟩
  have faulted : invoke Extracted.program 8 pair (unguardedContract.args ⟨⟨0, 0⟩, 0, 0⟩) readOnly =
      .error ⟨2, 2, .memory .unwritable (.address ⟨0, 0⟩) 8⟩ := rfl
  have up := invoke_mono _ _ 8 _ _ _ (.ok (final, values)) trivial ran
  have down := invoke_mono _ _ fuel _ _ _ _ (by simp [Settled]) faulted
  rw [Nat.add_comm] at down
  cases up.symm.trans down

/-- `Logged(ref ulong log, ulong value) { log = 1; Value = value; }` -/
@[cil_code] def logged : CIL.Method := { returnsValue := false, locals := [], code :=
  [.arg 1, .const64 1, .store64, .arg 0, .arg 2, .setFieldAt 0 8, .ret] }
@[cil_code] def loggedProgram : CIL.Program := [logged]

structure LoggedInput where
  this : Reference
  log : Reference
  value : CIL.W64

/-- Claims the constructor writes only its own 8 bytes. -/
def loggedContract : MethodContract LoggedInput Unit where
  args input := [.reference (.address input.this), .reference (.address input.log), .scalar (.i64 input.value)]
  results _ := []
  pre input m := m.WellFormed ∧ access m input.this 8 1 true = .ok () ∧ access m input.log 8 1 true = .ok ()
  footprint input := [(input.this, 8)]
  post input _ final _ := read final input.this 8 1 = .ok (numberBytes input.value.toNat 8)

/-- One writable allocation holding the struct at offset 0 and `log` at offset 8. -/
def shared : Memory := { readOnly with views := [⟨0, 0, 16, true, true⟩] }

theorem shared_formed : shared.WellFormed :=
  ⟨readOnly_formed.1, fun view member => by
    simp only [shared, List.mem_singleton] at member
    subst member
    exact ⟨_, rfl, by decide⟩⟩

/-- The write through `log` lands outside the footprint, so the contract is refuted by a concrete run. -/
theorem stray_write_rejected : ¬ loggedContract.Holds loggedProgram 0 := by
  intro holds
  obtain ⟨_, final, values, ran, framed, -⟩ := holds ⟨⟨0, 0⟩, ⟨0, 8⟩, 0⟩ shared ⟨shared_formed, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (invoke_ok_unique ran (rfl : invoke loggedProgram 8 0
    (loggedContract.args ⟨⟨0, 0⟩, ⟨0, 8⟩, 0⟩) shared = .ok _))
  have kept := framed.cells 0 (by decide) 8 (by simp [Outside, loggedContract])
  exact absurd kept (by decide)

/-- Reads back only `Low`, half of the 16-byte storage. -/
def halfContract : MethodContract PairInput Unit :=
  { pairContract with post := fun input _ final _ => read final input.this 8 1 = .ok (numberBytes input.low.toNat 8) }

theorem half_constructs : halfContract.Constructs 8 PairInput.this fun input _ => numberBytes input.low.toNat 8 :=
  ⟨fun _ => rfl, fun _ _ _ _ readback => readback⟩

/-- Storage whose first 8 bytes alone are initialized. -/
def lowInitialized : Memory := { readOnly with cells := fun _ offset => ⟨0, decide (offset < 8)⟩ }

/-- An 8-byte readback cannot supply the full 16-byte readback a `Pair` site needs. -/
theorem half_width_rejected (value : PairInput → Unit → List (BitVec 8)) :
    ¬ halfContract.Constructs 16 PairInput.this value := by
  intro constructs
  have readback := constructs.readback ⟨⟨0, 0⟩, 0, 0⟩ lowInitialized lowInitialized () rfl
  have uninitialized : read lowInitialized ⟨0, 0⟩ 16 1 = .error .uninitialized := rfl
  nomatch uninitialized.symm.trans readback

set_option pp.mvars false in
/--
error: Tactic `rfl` failed: The left-hand side
  [CIL.Op.arg 0, CIL.Op.arg 1, CIL.Op.newAggregate 2 2 16, CIL.Op.fieldAt 8 8, CIL.Op.arg 1, CIL.Op.const32 1,
      CIL.Op.convI8, CIL.Op.const32 2, CIL.Op.convI8, CIL.Op.arg 0, CIL.Op.newAggregate 1 4 32, CIL.Op.fieldAt 24 8,
      CIL.Op.add, CIL.Op.ret][2]?
is not definitionally equal to the right-hand side
  some (CIL.Op.newAggregate 2 ?_ 8)
-/
#guard_msgs (substring := true) in
/-- The tactic refuses an 8-byte constructor contract at the 16-byte `newobj` site. -/
example (halfHolds : halfContract.Holds Extracted.program pair) : rootContract.Holds Extracted.program root := by
  rintro ⟨x, y⟩ m formed
  dsimp only [rootContract, MethodContract.Returns] at *
  cil_contract_steps [checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cil_contract_construct halfHolds half_constructs (fun this => ⟨this, x, y⟩) []

end Rejected

#print axioms pair_holds
#print axioms word_holds
#print axioms root_holds
#print axioms root_correct
#print axioms Defaults.low_holds
#print axioms Defaults.caller_holds
#print axioms Defaults.caller_correct
#print axioms Rejected.missing_authority_rejected
#print axioms Rejected.stray_write_rejected
#print axioms Rejected.half_width_rejected

end Tests.ConstructContract
