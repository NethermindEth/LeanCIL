import CIL.Safety.LocalOperandRenaming
import CIL.Safety.MemoryRenaming

/-!
# Checked step actions under allocation renaming

Corresponding actions retain control flow and call targets. Their values, constructor storage
and active frame ownership refer to corresponding allocations in their resulting memories.
-/

namespace CIL.Safety

/-- Step outcomes agree on control flow and relate every retained allocation-backed component. -/
inductive FrameAction.Renamed (indices : LocalIndexMap) (mapping : AllocationRenaming)
    (scopes : Nat → Nat → Prop) : FrameAction → FrameAction → Prop
  | next {sourceMemory targetMemory sourceFrame targetFrame pc stack}
      (memory : Memory.Renamed mapping scopes sourceMemory targetMemory)
      (frame : Frame.Renamed indices mapping scopes sourceFrame targetFrame) :
      Renamed indices mapping scopes (.next pc stack sourceFrame sourceMemory)
        (.next pc (stack.map mapping.value) targetFrame targetMemory)
  | call {sourceMemory targetMemory callee arguments rest}
      (memory : Memory.Renamed mapping scopes sourceMemory targetMemory) :
      Renamed indices mapping scopes (.call callee arguments rest sourceMemory)
        (.call callee (arguments.map mapping.value) (rest.map mapping.value) targetMemory)
  | tailCall {sourceMemory targetMemory callee arguments}
      (memory : Memory.Renamed mapping scopes sourceMemory targetMemory) :
      Renamed indices mapping scopes (.tailCall callee arguments sourceMemory)
        (.tailCall callee (arguments.map mapping.value) targetMemory)
  | construct {sourceMemory targetMemory sourceFrame targetFrame callee arguments rest
      temporary kind}
      (memory : Memory.Renamed mapping scopes sourceMemory targetMemory)
      (frame : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
      (temporaryBound : temporary.allocation < mapping.sourceLimit) :
      Renamed indices mapping scopes
        (.construct callee arguments rest sourceFrame temporary kind sourceMemory)
        (.construct callee (arguments.map mapping.value) (rest.map mapping.value) targetFrame
          (mapping.reference temporary) kind targetMemory)
  | returned {sourceMemory targetMemory values}
      (memory : Memory.Renamed mapping scopes sourceMemory targetMemory) :
      Renamed indices mapping scopes (.returned values sourceMemory)
        (.returned (values.map mapping.value) targetMemory)

end CIL.Safety
