import CIL.Extraction.FlowIndex

/-! Fixed index construction and all-target lookup workloads for kernel profiling. -/

namespace FlowBenchmark
open CIL.Extraction
set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Reference builder repeatedly traverses each subtree list. -/
def oldBuild : Nat → List Nat → FlowIndex Nat
  | 0, _ => .empty
  | _ + 1, [] => .empty
  | _ + 1, [value] => .leaf value
  | fuel + 1, first :: second :: rest =>
    let values := first :: second :: rest
    let middle := values.length / 2
    .branch middle (oldBuild fuel (values.take middle)) (oldBuild fuel (values.drop middle))

/-- Visit every target in reverse order, including the first out-of-bounds position. -/
def checks (index : FlowIndex Nat) (count : Nat) : Bool :=
  (List.range (count + 1)).all fun offset =>
    index.get? (count - offset) == (if count - offset < count then some (count - offset) else none)

/-- Reference construction and every target are reduced by the kernel. -/
theorem baseline128 : checks (oldBuild 128 (List.range 128)) 128 = true := by decide +kernel
#print axioms baseline128
/-- Consuming construction and every target are reduced by the kernel. -/
theorem candidate128 : checks (FlowIndex.ofList (List.range 128)) 128 = true := by decide +kernel
#print axioms candidate128

/-- Reference construction and every target are reduced by the kernel. -/
theorem baseline512 : checks (oldBuild 512 (List.range 512)) 512 = true := by decide +kernel
#print axioms baseline512
/-- Consuming construction and every target are reduced by the kernel. -/
theorem candidate512 : checks (FlowIndex.ofList (List.range 512)) 512 = true := by decide +kernel
#print axioms candidate512

/-- Reference construction and every target are reduced by the kernel. -/
theorem baseline2048 : checks (oldBuild 2048 (List.range 2048)) 2048 = true := by decide +kernel
#print axioms baseline2048
/-- Consuming construction and every target are reduced by the kernel. -/
theorem candidate2048 : checks (FlowIndex.ofList (List.range 2048)) 2048 = true := by decide +kernel
#print axioms candidate2048

end FlowBenchmark
