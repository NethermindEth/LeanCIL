import CIL.StructuralLabels

/-! A synthetic extraction: `Root` calls `Step` before two loops and again after them. -/
namespace Extracted

open CIL

def method0Signature : String := "System.UInt32 Labels.Calls::Root(System.UInt32)"
def method1Signature : String := "System.UInt32 Labels.Calls::Step(System.UInt32)"
def method0 : Method :=
  { code := [.arg 0, .call 1 1, .setLocal 0,
      .local 0, .brzero 6, .branch 3,
      .local 0, .brnonzero 6,
      .arg 0, .call 1 1, .ret],
    locals := [.i32 0], returnsValue := true }
def method1 : Method := { code := [.arg 0, .ret], locals := [], returnsValue := true }
def program : Program := [method0, method1]
def signatures : List String := [method0Signature, method1Signature]

end Extracted

namespace Tests.StructuralLabels

open CIL

bind_method root rootBody := "System.UInt32 Labels.Calls::Root(System.UInt32)"

-- Two loops: an unselected label is an error listing both, never the first.
/--
error: rootBody has 2 loops; select one with [i]:
  [0] head pc 3, back edge from pc 5
  [1] head pc 6, back edge from pc 7
-/
#guard_msgs in
bind_loop loop := rootBody

bind_loop outer := rootBody [0]
bind_loop inner := rootBody [1]

example : outer = 3 ∧ outer.latch = 5 ∧ inner = 6 ∧ inner.latch = 7 := ⟨rfl, rfl, rfl, rfl⟩
example : rootBody.code[inner.latch]? = some (.brnonzero inner) := rfl
example := inner.backEdge

/--
error: rootBody has 2 loops; [2] is out of range:
  [0] head pc 3, back edge from pc 5
  [1] head pc 6, back edge from pc 7
-/
#guard_msgs in
bind_loop third := rootBody [2]

-- A forward branch alone is not a loop.
/-- error: Extracted.method1 has no loops: no branch targets the same or an earlier pc -/
#guard_msgs in
bind_loop none := Extracted.method1

-- Two calls to the same method: the site must be selected.
/--
error: rootBody calls
  System.UInt32 Labels.Calls::Step(System.UInt32)
at 2 sites; select one with [i]:
  [0] pc 1
  [1] pc 9
-/
#guard_msgs in
bind_callee step stepBody := "System.UInt32 Labels.Calls::Step(System.UInt32)" from rootBody

bind_callee step stepBody := "System.UInt32 Labels.Calls::Step(System.UInt32)" from rootBody [1]
bind_call before := step from rootBody [0]
bind_call after := step from rootBody [1]

example : rootBody.code[9]? = some (.call step 1) := step.call
example : before = 1 ∧ after = 9 := ⟨rfl, rfl⟩
example : rootBody.code[before]? = some (.call step 1) := before.call

/--
error: rootBody calls
  System.UInt32 Labels.Calls::Step(System.UInt32)
at 2 sites; select one with [i]:
  [0] pc 1
  [1] pc 9
-/
#guard_msgs in
bind_call either := step from rootBody

-- `relabel` and `targets` agree, so loop detection sees every branch `cil_embed` maps.
example : (Op.switch [3, 0, 7]).targets = [3, 0, 7] ∧ (Op.nativeBinary (.blt 2)).targets = [2] ∧ (Op.call 1 1).targets = [] :=
  ⟨rfl, rfl, rfl⟩

end Tests.StructuralLabels
