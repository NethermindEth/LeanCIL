import CIL.Safety.Frames

/-!
# Bounded dynamic stack storage

Dynamic allocations belong to the current activation and expire through `leaveFrame`.
The caller supplies a per-activation resource quota through `Memory.stackLimit`; it is a
deployment premise, not a claim that every CLR thread has that much free stack space.
-/

namespace CIL.Safety

/-- Dynamic stack reservations use the 16-byte stack alignment of the admitted 64-bit targets. -/
def stackAlignment : Nat := 16

/-- The bounded model admits at most 64 KiB of dynamic stack storage per activation. -/
def maxDynamicStack : Nat := 65536

/-- Charge alignment padding as well as payload against the activation's quota. -/
def stackReservation (size : Nat) : Nat :=
  (size + stackAlignment - 1) / stackAlignment * stackAlignment

/-- Allocate bounded frame-owned storage, preserving unknown bytes unless localsinit is set.
    A zero request returns null without consuming quota or creating an allocation. -/
def allocateStack (memory : Memory) (frame : Frame) (size : Nat) (initLocals : Bool) :
    ExecutionResult (ManagedReference × Frame × Memory) := do
  if size ≥ nativeLimit || memory.stackLimit > maxDynamicStack then
    .error .invalidState else pure ()
  if size == 0 then return (.null, frame, memory)
  let reserved := stackReservation size
  let available := memory.stackLimit - frame.stackBytes
  if frame.stackBytes > memory.stackLimit || reserved > available then
    .error (.stackAllocationFailure reserved available) else pure ()
  let (reference, allocated) ← allocateHome memory frame.activation size stackAlignment
  let initialized ← if initLocals then
    checkedAt (.address reference) size
      (write allocated reference (List.replicate size 0) stackAlignment)
    else pure allocated
  return (.address reference,
    { frame with owned := reference.allocation :: frame.owned
                 stackBytes := frame.stackBytes + reserved }, initialized)

end CIL.Safety
