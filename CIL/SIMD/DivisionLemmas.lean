import CIL.SIMD.VectorLemmas
import CIL.Safety.FrameSetupLemmas
import CIL.Safety.Execution

namespace CIL.Vector

@[simp] theorem lane512_0 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 0 = a0 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind

@[simp] theorem lane512_1 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 1 = a1 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind

@[simp] theorem lane512_2 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 2 = a2 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind

@[simp] theorem lane512_3 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 3 = a3 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind

@[simp] theorem lane512_4 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 4 = a4 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind

@[simp] theorem lane512_5 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 5 = a5 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind

@[simp] theorem lane512_6 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 6 = a6 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind

@[simp] theorem lane512_7 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 7 = a7 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind

theorem lane64_and (left right : BitVec width) (index : Nat) :
    lane64 (left &&& right) index = lane64 left index &&& lane64 right index := by
  ext bit bound
  simp [lane64, BitVec.getElem_extractLsb'] <;> grind

theorem lane64_or (left right : BitVec width) (index : Nat) :
    lane64 (left ||| right) index = lane64 left index ||| lane64 right index := by
  ext bit bound
  simp [lane64, BitVec.getElem_extractLsb'] <;> grind

theorem lane64_xor (left right : BitVec width) (index : Nat) :
    lane64 (left ^^^ right) index = lane64 left index ^^^ lane64 right index := by
  ext bit bound
  simp [lane64, BitVec.getElem_extractLsb'] <;> grind

theorem lane64_andNot (left right : BitVec width) (index : Nat) (_bounded : 64 * (index + 1) ≤ width) :
    lane64 ((~~~left) &&& right) index = (~~~lane64 left index) &&& lane64 right index := by
  ext bit bound
  simp [lane64, BitVec.getElem_extractLsb'] <;> grind

theorem zip512_lane (operation : W64 → W64 → W64) (left right : V512)
    (index : Nat) (bound : index < 8) :
    lane64 (zip512 operation left right) index = operation (lane64 left index) (lane64 right index) := by
  have alternatives : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
  rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [zip512]

theorem map256_lane (operation : W64 → W64) (value : V256) (index : Nat) (bound : index < 4) :
    lane64 (map256 operation value) index = operation (lane64 value index) := by
  have alternatives : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases alternatives with rfl | rfl | rfl | rfl <;> simp [map256]

theorem shiftLeftCount64_lane (value : V256) (count : W64) (index : Nat) (bound : index < 4) :
    lane64 (shiftLeftCount64 value count) index =
      if count.toNat >= 64 then 0 else lane64 value index <<< count.toNat := by
  unfold shiftLeftCount64
  split
  · simp [lane64]
  · exact map256_lane _ _ _ bound

theorem shiftRightCount64_lane (value : V256) (count : W64) (index : Nat) (bound : index < 4) :
    lane64 (shiftRightCount64 value count) index =
      if count.toNat >= 64 then 0 else lane64 value index >>> count.toNat := by
  unfold shiftRightCount64
  split
  · simp [lane64]
  · exact map256_lane _ _ _ bound

end CIL.Vector

namespace CIL

def Vector128Represents (value : Value) (concrete : Vector.V128) : Prop :=
  match value with
  | .v128 bits => concrete = bits
  | .v128Low64 low => Vector.lane64 concrete 0 = low
  | _ => False

theorem scalarUnsafe_represents_every_upper (low upper : W64) :
    Vector128Represents (.v128Low64 low) (Vector.pack128 low upper) := by
  simp [Vector128Represents]

theorem scalarUnsafe_no_fixed_upper (low upper : W64) :
    ¬ ∀ concrete, Vector128Represents (.v128Low64 low) concrete → Vector.lane64 concrete 1 = upper := by
  intro fixed
  have zero := fixed (Vector.pack128 low 0) (scalarUnsafe_represents_every_upper low 0)
  have one := fixed (Vector.pack128 low 1) (scalarUnsafe_represents_every_upper low 1)
  simp only [Vector.lane128_1] at zero one
  have impossible : (0 : W64) = 1 := zero.trans one.symm
  exact (by decide : (0 : W64) ≠ 1) impossible

theorem scalarUnsafe_extract_all_concretizations (low : W64) (concrete : Vector.V128)
    (represents : Vector128Represents (.v128Low64 low) concrete) :
    evalIntrinsic (.vector (.extract64 128)) [.v128 concrete, .i32 0] = some (.i64 low) := by
  change Vector.lane64 concrete 0 = low at represents
  change some (Value.i64 (Vector.lane64 concrete 0)) = some (Value.i64 low)
  exact congrArg (fun lane => some (Value.i64 lane)) represents

theorem scalarUnsafe_reinterpret_preserves (low : W64) :
    evalIntrinsic (.vector (.reinterpret 128)) [.v128Low64 low] = some (.v128Low64 low) := rfl

theorem scalarUnsafe_shiftLeft_all_concretizations (value : Vector.V256) (low : W64)
    (concrete : Vector.V128) (represents : Vector128Represents (.v128Low64 low) concrete) :
    evalIntrinsic (.avx2 .shl64Count) [.v256 value, .v128 concrete] =
      evalIntrinsic (.avx2 .shl64Count) [.v256 value, .v128Low64 low] := by
  change Vector.lane64 concrete 0 = low at represents
  change some (Value.v256 (Vector.shiftLeftCount64 value (Vector.lane64 concrete 0))) =
    some (Value.v256 (Vector.shiftLeftCount64 value low))
  exact congrArg
    (fun count => some (Value.v256 (Vector.shiftLeftCount64 value count))) represents

theorem scalarUnsafe_shiftRight_all_concretizations (value : Vector.V256) (low : W64)
    (concrete : Vector.V128) (represents : Vector128Represents (.v128Low64 low) concrete) :
    evalIntrinsic (.avx2 .shr64Count) [.v256 value, .v128 concrete] =
      evalIntrinsic (.avx2 .shr64Count) [.v256 value, .v128Low64 low] := by
  change Vector.lane64 concrete 0 = low at represents
  change some (Value.v256 (Vector.shiftRightCount64 value (Vector.lane64 concrete 0))) =
    some (Value.v256 (Vector.shiftRightCount64 value low))
  exact congrArg
    (fun count => some (Value.v256 (Vector.shiftRightCount64 value count))) represents

/-- `concrete` is a value the runtime may hold where the model holds `value`. -/
def Concretizes (value concrete : Value) : Prop :=
  match value with
  | .v128Low64 _ => ∃ bits, concrete = .v128 bits ∧ Vector128Represents value bits
  | _ => concrete = value

def ConcretizesAll : List Value → List Value → Prop
  | [], [] => True
  | value :: values, concrete :: concretes => Concretizes value concrete ∧ ConcretizesAll values concretes
  | _, _ => False

/-- Whatever the unspecified upper lanes hold, the ISA result agrees with the model result. -/
theorem evalUnspecifiedIntrinsic_concretizations {op : Intrinsic} {args concrete : List Value} {result : Value}
    (evaluated : evalUnspecifiedIntrinsic op args = some result)
    (represents : ConcretizesAll args concrete) :
    ∃ value, evalIntrinsic op concrete = some value ∧ Concretizes result value := by
  unfold evalUnspecifiedIntrinsic at evaluated
  split at evaluated
  · cases evaluated
    rcases concrete with _ | ⟨first, _ | ⟨_, _⟩⟩ <;> simp only [ConcretizesAll, and_false, and_true] at represents
    obtain ⟨bits, rfl, lane⟩ := represents
    exact ⟨.v128 bits, rfl, bits, rfl, lane⟩
  · rename_i low index
    rcases concrete with _ | ⟨first, _ | ⟨second, _ | ⟨_, _⟩⟩⟩ <;>
      simp only [ConcretizesAll, and_false, and_true] at represents
    obtain ⟨⟨bits, rfl, lane⟩, rfl⟩ := represents
    change Vector.lane64 bits 0 = low at lane
    split at evaluated
    · rename_i zero
      cases evaluated
      have zero : index.toNat = 0 := Nat.eq_of_beq_eq_true zero
      refine ⟨.i64 low, ?_, rfl⟩
      show (if index.toNat < 2 then some (Value.i64 (Vector.lane64 bits index.toNat)) else none) = _
      rw [zero, lane]
      rfl
    · cases evaluated
  all_goals first
    | cases evaluated
      rcases concrete with _ | ⟨first, _ | ⟨second, _ | ⟨_, _⟩⟩⟩ <;>
        simp only [ConcretizesAll, and_false, and_true] at represents
      obtain ⟨rfl, bits, rfl, lane⟩ := represents
      change Vector.lane64 bits 0 = _ at lane
      exact ⟨_, rfl, by simp only [Concretizes, lane]⟩
    | cases evaluated

/-- The checked and the plain evaluator agree wherever unspecified lanes are consumed. -/
theorem evalUnspecifiedIntrinsic_sound {op : Intrinsic} {args : List Value} {result : Value}
    (evaluated : evalUnspecifiedIntrinsic op args = some result) : evalIntrinsic op args = some result := by
  unfold evalUnspecifiedIntrinsic at evaluated
  split at evaluated
  all_goals first | (cases evaluated; rfl) | (cases evaluated) | exact evaluated

end CIL

namespace CIL.Safety

/-- Every intrinsic the checked semantics evaluates on unspecified lanes agrees with every
    runtime concretisation of them; no other operation can succeed on such operands. -/
theorem checkedIntrinsic_unspecified {op : CIL.Intrinsic} {operands concrete : List CIL.Value} {result : CIL.Value}
    (unspecified : operands.any CIL.Value.hasUnspecified = true)
    (checked : checkedIntrinsic op operands = .ok result)
    (represents : CIL.ConcretizesAll operands concrete) :
    ∃ value, CIL.evalIntrinsic op concrete = some value ∧ CIL.Concretizes result value := by
  unfold checkedIntrinsic at checked
  simp only [unspecified, ite_true] at checked
  split at checked
  · cases checked
    exact CIL.evalUnspecifiedIntrinsic_concretizations (by assumption) represents
  · cases checked

theorem opaque128_load (memory : Memory) (value : Opaque128Value) :
    loadLocal memory (.opaque128 (some value)) = .ok (.scalar value.value) := rfl

theorem opaque128_store_load (memory : Memory) (before : Option Opaque128Value) (value : Opaque128Value) :
    storeLocal memory (.opaque128 before) (.scalar value.value) = .ok (.opaque128 (some value), memory) ∧
    loadLocal memory (.opaque128 (some value)) = .ok (.scalar value.value) := by
  cases value <;> exact ⟨rfl, rfl⟩

theorem opaque128_store_memory_identity (memory result : Memory) (before : Option Opaque128Value)
    (value : Value) (slot : LocalSlot)
    (stored : storeLocal memory (.opaque128 before) value = .ok (slot, result)) : result = memory := by
  cases value with
  | scalar value =>
    cases value with
    | v128 bits =>
      change (Except.ok (.opaque128 (some (.known bits)), memory) : ExecutionResult (LocalSlot × Memory)) =
        .ok (slot, result) at stored
      exact (congrArg Prod.snd (Except.ok.inj stored)).symm
    | v128Low64 low =>
      change (Except.ok (.opaque128 (some (.low64 low)), memory) : ExecutionResult (LocalSlot × Memory)) =
        .ok (slot, result) at stored
      exact (congrArg Prod.snd (Except.ok.inj stored)).symm
    | _ => cases stored
  | reference _ => cases stored
  | span _ _ => cases stored

theorem opaque128_init_zero (memory : Memory) :
    makeOpaque128 (.v128 0) memory = .ok (.opaque128 (some (.known 0)), [], memory) := rfl

theorem opaque128_init_unknown (memory : Memory) :
    makeOpaque128 .unmodeled memory = .ok (.opaque128 none, [], memory) ∧
    loadLocal memory (.opaque128 none) = .error (.unsupported "Uninitialized opaque vector local") := ⟨rfl, rfl⟩

theorem opaque128_store_preserves_world (memory result : Memory) (before : Option Opaque128Value)
    (value : Value) (slot : LocalSlot)
    (stored : storeLocal memory (.opaque128 before) value = .ok (slot, result)) :
    result.allocations = memory.allocations ∧ result.cells = memory.cells ∧
      result.views = memory.views ∧ result.staticBindings = memory.staticBindings := by
  rw [opaque128_store_memory_identity _ _ _ _ _ stored]
  exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms opaque128_store_load
#print axioms opaque128_store_memory_identity
#print axioms opaque128_store_preserves_world
end CIL.Safety

#print axioms CIL.scalarUnsafe_represents_every_upper
#print axioms CIL.scalarUnsafe_no_fixed_upper
#print axioms CIL.scalarUnsafe_shiftLeft_all_concretizations
#print axioms CIL.scalarUnsafe_shiftRight_all_concretizations
#print axioms CIL.Vector.zip512_lane
#print axioms CIL.Vector.shiftLeftCount64_lane
#print axioms CIL.Vector.shiftRightCount64_lane
#print axioms CIL.Vector.lane512_0
#print axioms CIL.Vector.lane512_1
#print axioms CIL.Vector.lane512_2
#print axioms CIL.Vector.lane512_3
#print axioms CIL.Vector.lane512_4
#print axioms CIL.Vector.lane512_5
#print axioms CIL.Vector.lane512_6
#print axioms CIL.Vector.lane512_7
#print axioms CIL.Vector.lane64_and
#print axioms CIL.Vector.lane64_or
#print axioms CIL.Vector.lane64_xor
#print axioms CIL.Vector.lane64_andNot
#print axioms CIL.Vector.map256_lane
#print axioms CIL.scalarUnsafe_extract_all_concretizations
#print axioms CIL.scalarUnsafe_reinterpret_preserves
#print axioms CIL.evalUnspecifiedIntrinsic_concretizations
#print axioms CIL.evalUnspecifiedIntrinsic_sound
#print axioms CIL.Safety.checkedIntrinsic_unspecified
#print axioms CIL.Safety.opaque128_load
#print axioms CIL.Safety.opaque128_init_zero
#print axioms CIL.Safety.opaque128_init_unknown
