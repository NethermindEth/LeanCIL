import CIL.Safety.Execution
import CIL.Safety.StepAttribute

/-! Checked span and reference homes expose reusable value equations for proof automation. -/

namespace CIL.Safety

/-- A successful memory check keeps its value without inspecting the failure attribution. -/
@[cil_checked] theorem checkedAt_success (reference : ManagedReference) (width : Nat) (value : α) :
    checkedAt reference width (.ok value) = .ok value := rfl
#print axioms checkedAt_success

/-- Mapping a successful checked result retains its success without expanding a symbolic result. -/
@[cil_checked] theorem checked_map_success (transform : α → β) (value : α) :
    transform <$> (.ok value : ExecutionResult α) = .ok (transform value) := rfl
#print axioms checked_map_success

/-- A continuation consumes a successful checked value without inspecting any failure case. -/
@[cil_checked] theorem checked_bind_success (next : α → ExecutionResult β) (value : α) :
    (.ok value : ExecutionResult α) >>= next = next value := rfl
#print axioms checked_bind_success

/-- Validating a span stack value preserves the exact view and its capability. -/
@[cil_checked] theorem checkedValue_span (memory : Memory) (view : SpanView)
    (valid : view.validate memory = .ok ()) :
    checkedValue memory (.bufferSpan view) = .ok (.bufferSpan view) := by
  simp [checkedValue, valid, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
#print axioms checkedValue_span

/-- A span home reads the matching valid view without reading its backing bytes. -/
@[cil_checked] theorem loadLocal_span (memory : Memory) (view : SpanView)
    (width : Nat) (writable : Bool) (valid : view.validate memory = .ok ())
    (widthMatches : view.width = width) (modeMatches : view.writable = writable) :
    loadLocal memory (.span width writable (some view)) = .ok (.bufferSpan view) := by
  simp [loadLocal, valid, widthMatches, modeMatches, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms loadLocal_span

/-- Storing a valid matching span replaces the home, preserving all caller memory. -/
@[cil_checked] theorem storeLocal_span (memory : Memory) (previous : Option SpanView)
    (view : SpanView) (width : Nat) (writable : Bool) (valid : view.validate memory = .ok ())
    (widthMatches : view.width = width) (modeMatches : view.writable = writable) :
    storeLocal memory (.span width writable previous) (.bufferSpan view) =
      .ok (.span width writable (some view), memory) := by
  simp [storeLocal, valid, widthMatches, modeMatches, Value.hasUnspecified, checkedAt,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms storeLocal_span

/-- A root home loads its formed reference without granting byte access authority. -/
@[cil_checked] theorem loadLocal_root (memory : Memory) (reference : ManagedReference)
    (formed : formValue memory reference = .ok (.reference reference)) :
    loadLocal memory (.root (some reference)) = .ok (.reference reference) := formed
#print axioms loadLocal_root

/-- A readonly root retains its restriction when loading a formed reference. -/
@[cil_checked] theorem loadLocal_readOnlyRoot (memory : Memory) (reference : ManagedReference)
    (formed : formValue memory reference = .ok (.reference reference)) :
    loadLocal memory (.readOnlyRoot reference) = .ok (.readOnlyReference reference) := by
  simp [loadLocal, formed, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms loadLocal_readOnlyRoot

/-- A root replacement preserves memory and requires the new reference to form. -/
@[cil_checked] theorem storeLocal_root (memory : Memory) (previous : Option ManagedReference)
    (reference : ManagedReference)
    (formed : formValue memory reference = .ok (.reference reference)) :
    storeLocal memory (.root previous) (.reference reference) =
      .ok (.root (some reference), memory) := by
  simp [storeLocal, Value.hasUnspecified, formed, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms storeLocal_root

/-- Storing a readonly reference into a root preserves its readonly capability. -/
@[cil_checked] theorem storeLocal_root_readOnly (memory : Memory)
    (previous : Option ManagedReference) (reference : ManagedReference)
    (formed : formValue memory reference = .ok (.reference reference)) :
    storeLocal memory (.root previous) (.readOnlyReference reference) =
      .ok (.readOnlyRoot reference, memory) := by
  simp [storeLocal, Value.hasUnspecified, formed, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms storeLocal_root_readOnly

/-- Replacing a readonly root with a writable reference keeps that reference's capability. -/
@[cil_checked] theorem storeLocal_readOnlyRoot (memory : Memory)
    (previous reference : ManagedReference)
    (formed : formValue memory reference = .ok (.reference reference)) :
    storeLocal memory (.readOnlyRoot previous) (.reference reference) =
      .ok (.root (some reference), memory) := by
  simp [storeLocal, Value.hasUnspecified, formed, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms storeLocal_readOnlyRoot

/-- Replacing a readonly root with a readonly reference preserves the restriction. -/
@[cil_checked] theorem storeLocal_readOnlyRoot_readOnly (memory : Memory)
    (previous reference : ManagedReference)
    (formed : formValue memory reference = .ok (.reference reference)) :
    storeLocal memory (.readOnlyRoot previous) (.readOnlyReference reference) =
      .ok (.readOnlyRoot reference, memory) := by
  simp [storeLocal, Value.hasUnspecified, formed, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms storeLocal_readOnlyRoot_readOnly

end CIL.Safety
