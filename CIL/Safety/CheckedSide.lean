import CIL.Safety.CheckedHomes
import CIL.Safety.FrameLemmas
import CIL.Safety.WordMemory
import CIL.SymbolicExecution

/-!
# Checked side-condition normalization

The closed `cil_side` set normalizes argument and result checks after an opcode equation has
selected the operation. It does not unfold either instruction dispatcher. Operation and
permission facts remain explicit premises, alongside the successful checks in `cil_checked`.
-/

namespace CIL.Safety

open Lean Meta in
/-- Expose the scalar constructor returned by a helper while retaining its symbolic payload. -/
dsimproc_decl checkedScalarConstructor (Value.scalar _) := fun expression => do
  let value := expression.appArg!
  let reduced ← whnfD value
  if reduced == value then return .continue
  let some name := reduced.getAppFn.constName? | return .continue
  let some (.ctorInfo info) := (← getEnv).find? name | return .continue
  unless info.induct == ``CIL.Value do return .continue
  return .done (mkApp expression.getAppFn reduced)

attribute [cil_guard_proc] checkedScalarConstructor

/-- A numeral Boolean parameter remains one after narrowing to any supported width. -/
@[cil_side] theorem narrow_numeral_one (kind : CIL.NarrowKind) :
    kind.extend (1 : CIL.W32) = 1#32 := CIL.NarrowKind.extend_one kind
#print axioms narrow_numeral_one

/-- A numeral Boolean parameter remains zero after narrowing to any supported width. -/
@[cil_side] theorem narrow_numeral_zero (kind : CIL.NarrowKind) :
    kind.extend (0 : CIL.W32) = 0#32 := CIL.NarrowKind.extend_zero kind
#print axioms narrow_numeral_zero

/-- A null managed reference forms without consulting memory. -/
@[cil_side] theorem formValue_null (memory : Memory) :
    formValue memory .null = .ok (.reference .null) := rfl
#print axioms formValue_null

/-- Forming a concrete address uses the checked allocation and offset result. -/
@[cil_side] theorem formValue_address (memory : Memory) (reference : Reference) :
    formValue memory (.address reference) = do
      let formed ← checkedAt (.address reference) 0 (form memory reference)
      return .reference (.address formed) := rfl
#print axioms formValue_address

attribute [cil_side] List.mapM List.mapM.loop List.reverse_nil List.reverse_cons
  List.cons_append List.nil_append List.append_nil List.map_nil List.map_cons List.map_map
  List.length_cons List.length_nil List.take_succ_cons List.take_zero List.take_nil
  List.drop_succ_cons List.drop_zero List.drop_nil List.getElem?_cons_zero
  List.getElem?_cons_succ List.getElem?_nil Option.map_some Option.map_none
  List.set_cons_zero List.set_cons_succ List.set_nil
  List.replicate_succ List.replicate_zero
  List.mem_cons List.not_mem_nil or_false false_or
  Option.getD_some Option.getD_none
  Bool.false_eq_true Bool.true_eq_false not_false_eq_true not_true_eq_false ite_true ite_false
  Bool.false_or Bool.or_false Bool.true_or Bool.or_true Bool.false_and Bool.and_false
  Bool.true_and Bool.and_true Bool.not_true Bool.not_false
  Bool.true_bne Bool.false_bne Bool.bne_true Bool.bne_false Bool.true_beq Bool.false_beq
  checkedValue numericValue numericOfWidth signedOfWidth scalars checkedAt formObject_leaveFrame
  referenceAt_null referenceAt_address
  Except.mapError Bind.bind Except.bind Pure.pure Except.pure
  CIL.fin_val_three CIL.fin_mk_ofNat BitVec.ofInt_ofNat BitVec.ofNat_toNat BitVec.setWidth_eq
  CIL.NarrowKind.extend_one CIL.NarrowKind.extend_zero
  BitVec.lt_irrefl
  bne_iff_ne ne_eq beq_iff_eq decide_true decide_false

attribute [cil_side_proc] reduceCtorEq Nat.reduceAdd Nat.reduceMul Nat.reduceMod Nat.reduceLT
  Fin.reduceOfNat
  BitVec.reduceToInt BitVec.reduceOfInt BitVec.reduceOfNat BitVec.reduceToNat
  BitVec.reduceSignExtend BitVec.reduceSetWidth BitVec.reduceZeroExtend

end CIL.Safety
