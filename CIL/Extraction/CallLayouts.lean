import CIL.Resolution

/-! Indexed storage, value shape and alignment for resolving method operands. -/

namespace CIL.Extraction

/-- Positional reads into both layout tables during one method's call checks. -/
structure CallLayouts extends LayoutEnvironment where
  private mk ::

/-- The reader shares the positional index built with the method's environment. -/
def _root_.CIL.LayoutEnvironment.callLayouts (environment : LayoutEnvironment) : CallLayouts :=
  ⟨environment⟩

/-- Preparing positional reads preserves the original model environment. -/
@[simp] theorem callLayouts_environment (environment : LayoutEnvironment) :
    environment.callLayouts.toLayoutEnvironment = environment := rfl

#print axioms callLayouts_environment

/-- Storage of a closed argument under the indexed raw layout metadata. -/
def CallLayouts.storage (environment : CallLayouts) : TypeExpr → Option StorageType :=
  typeStorageAt (environment.indexedRaw[·]?)

/-- A value representation uses the same storage and computed layout as execution. -/
def CallLayouts.valueShape (environment : CallLayouts) : TypeExpr → ValueShape :=
  valueShapeAt environment.layouts environment.storage

/-- Indexed storage reads give the same result as reads from the declared metadata list. -/
theorem CallLayouts.storage_eq (environment : CallLayouts) :
    environment.storage = typeStorage environment.rawLayouts := by
  unfold CallLayouts.storage typeStorage
  rw [environment.index_eq]
  congr 1
  funext index
  simp

#print axioms CallLayouts.storage_eq

/-- The call checker and execution assign identical shapes to every type. -/
theorem CallLayouts.valueShape_eq (environment : LayoutEnvironment) (type : TypeExpr) :
    environment.callLayouts.valueShape type = environment.valueShape type := by
  rw [CallLayouts.valueShape, CallLayouts.storage_eq]
  rfl

#print axioms CallLayouts.valueShape_eq

/-- The computed alignment of the aggregate with the given identity and index. -/
def CallLayouts.alignment? (reader : CallLayouts) (type : TypeExpr) : Option Nat := do
  let .aggregate _ index := type | none
  _root_.guard (reader.storage type == some (.field (.aggregate index)))
  return (← reader.layouts[index]?).alignment

/-- Preparing the same layout environment for execution gives the validation reader. -/
@[simp] theorem CallLayouts.prepare_eq (reader : CallLayouts) :
    reader.toLayoutEnvironment.callLayouts = reader := by
  rfl

#print axioms CallLayouts.prepare_eq

end CIL.Extraction
