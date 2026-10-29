import CIL.Safety.NativeMethodTables
import CIL.Safety.MemoryEquivalence

/-! Equivalent memories give the same authenticated native handler-table observations. -/

namespace CIL.Safety

/-- Native table geometry observes only the allocation descriptors. -/
theorem Memory.Equivalent.nativeTableCheck {source target : Memory}
    (same : source.Equivalent target) (table : NativeMethodTable) :
    table.check source = table.check target := by
  unfold NativeMethodTable.check liveAllocation
  rw [same.allocations]
#print axioms Memory.Equivalent.nativeTableCheck

/-- Equivalent authority representations do not change cursor movement. -/
theorem Memory.Equivalent.nativeTableAdd {source target : Memory}
    (same : source.Equivalent target) (table : NativeMethodTable) (offset : BitVec 64) :
    table.addBytes source offset = table.addBytes target offset := by
  unfold NativeMethodTable.addBytes
  simp only [same.nativeTableCheck]
#print axioms Memory.Equivalent.nativeTableAdd

/-- Native pointer loads use the same checked read in equivalent memories. -/
theorem Memory.Equivalent.nativeTableLoad {source target : Memory}
    (same : source.Equivalent target) (table : NativeMethodTable) :
    table.load source = table.load target := by
  unfold NativeMethodTable.load
  simp only [same.nativeTableCheck, same.read]
#print axioms Memory.Equivalent.nativeTableLoad

/-- Stable immutable bindings resolve identically in equivalent memories. -/
theorem Memory.Equivalent.nativeTableView {source target : Memory}
    (same : source.Equivalent target) (table : CIL.MethodTable) :
    CIL.Safety.nativeTableView table source = CIL.Safety.nativeTableView table target := by
  unfold CIL.Safety.nativeTableView
  simp only [same.staticBindings, same.nativeTableCheck]
#print axioms Memory.Equivalent.nativeTableView

/-- Native offsets produce identical cursors in equivalent memories. -/
theorem Memory.Equivalent.addNativeTable {source target : Memory}
    (same : source.Equivalent target) (table : CIL.MethodTable) (offset : BitVec 64) :
    CIL.Safety.addNativeTable table source offset =
      CIL.Safety.addNativeTable table target offset := by
  unfold CIL.Safety.addNativeTable
  simp only [same.nativeTableView, same.nativeTableAdd]
#print axioms Memory.Equivalent.addNativeTable

/-- Native loads return the same opaque identity in equivalent memories. -/
theorem Memory.Equivalent.loadNativeTable {source target : Memory}
    (same : source.Equivalent target) (table : CIL.MethodTable) :
    CIL.Safety.loadNativeTable table source = CIL.Safety.loadNativeTable table target := by
  unfold CIL.Safety.loadNativeTable
  simp only [same.nativeTableView, same.nativeTableLoad]
#print axioms Memory.Equivalent.loadNativeTable

end CIL.Safety
