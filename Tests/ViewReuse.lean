import CIL.Safety.MemoryEquivalence

namespace Tests.ViewReuse
open CIL.Safety

private def memory (views : List View) : Memory := {
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨16, 8, []⟩, true, [16]⟩ else none
  cells := fun _ _ => ⟨0, false⟩
  views
  nextIdentity := 1
}

private def bytes : List (BitVec 8) := [1, 2, 3, 4, 5, 6, 7, 8]

-- Existing authority is retained; writes still initialize the previously unknown bytes.
example :
    (write (memory [⟨0, 0, 16, true, true⟩]) ⟨0, 0⟩ bytes 1).map
      (fun m => (m.views.length, read m ⟨0, 0⟩ 8 1)) = .ok (1, .ok bytes) := rfl

-- No individual readable view covers this write, but their union does.
example :
    (write (memory [⟨0, 0, 16, false, true⟩, ⟨0, 0, 4, true, false⟩, ⟨0, 4, 4, true, false⟩])
      ⟨0, 0⟩ bytes 1).map (fun m => (m.views.length, read m ⟨0, 0⟩ 8 1)) = .ok (3, .ok bytes) := rfl

-- Partial coverage and write-only output require a new readable interval.
example :
    (write (memory [⟨0, 0, 16, false, true⟩, ⟨0, 0, 4, true, false⟩]) ⟨0, 0⟩ bytes 1).map
      (fun m => (m.views.length, read m ⟨0, 0⟩ 8 1, permitted m false ⟨0, 8⟩)) =
      .ok (3, .ok bytes, false) := rfl
example :
    (write (memory [⟨0, 0, 16, false, true⟩]) ⟨0, 0⟩ bytes 1).map
      (fun m => (m.views.length, read m ⟨0, 0⟩ 8 1, permitted m false ⟨0, 8⟩)) =
      .ok (2, .ok bytes, false) := rfl

-- Empty writes add no views, but still enforce formation, alignment and mutability.
example : (write (memory []) ⟨0, 16⟩ [] 1).map (·.views.length) = .ok 0 := rfl
example : (write (memory []) ⟨0, 17⟩ [] 1).map (·.views.length) = .error .invalidReference := rfl
example : (write (memory []) ⟨0, 1⟩ [] 8).map (·.views.length) = .error .alignment := rfl
example :
    (write { memory [] with allocations := fun _ => some ⟨.immutableStatic, ⟨16, 8, []⟩, true, [16]⟩ }
      ⟨0, 0⟩ [] 1).map (·.views.length) = .error .unwritable := rfl

-- Read permission never substitutes for write permission or allocation bounds.
example : (write (memory [⟨0, 0, 16, true, false⟩]) ⟨0, 0⟩ bytes 1).map (·.views.length) =
    .error .unwritable := rfl
example : (write (memory [⟨0, 0, 16, true, true⟩]) ⟨0, 12⟩ bytes 1).map (·.views.length) =
    .error .outsideAllocation := rfl
example :
    (write { memory [⟨0, 0, 16, true, true⟩] with
      allocations := fun _ => some ⟨.callerStack, ⟨16, 8, []⟩, false, [16]⟩ }
      ⟨0, 0⟩ bytes 1).map (·.views.length) = .error .expiredLifetime := rfl

/-- Alternate fields, so an optimization that only removes adjacent identical
    views would still grow without bound. -/
def stores (writer : Memory → Reference → List (BitVec 8) → Nat → Checked Memory) :
    Nat → Memory → Checked Memory
  | 0, m => .ok m
  | count + 1, m => do
    let after ← writer m ⟨0, 8 * (count % 2)⟩ bytes 1
    stores writer count after

def benchmarkMemory : Memory := memory [⟨0, 0, 16, true, true⟩]

example : (stores write 32 benchmarkMemory).map (·.views.length) = .ok 1 := rfl
example : (stores writeAlwaysPrepend 32 benchmarkMemory).map (·.views.length) = .ok 33 := rfl

end Tests.ViewReuse
