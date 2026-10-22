import CIL.MethodIdentity

/-! A synthetic extraction: `Root` calls two helpers with the same arity, `Right` first. -/
namespace Extracted

open CIL

def method0Signature : String := "System.UInt64 Examples.Identity::Root(System.UInt64)"
def method1Signature : String := "System.UInt64 Examples.Identity::Left(System.UInt64,System.UInt64)"
def method2Signature : String := "System.UInt64 Examples.Identity::Right(System.UInt64,System.UInt64)"
def method3Signature : String := "System.UInt64 Examples.Overloads::Pick(System.UInt64)"
def method4Signature : String := "System.UInt32 Examples.Overloads::Pick(System.UInt32)"
def helper (marker : Nat) : Method := { code := [.arg 0, .arg 1, .const64 (BitVec.ofNat 64 marker), .ret], locals := [], returnsValue := true }
def method0 : Method := { code := [.arg 0, .arg 0, .call 2 2, .arg 0, .call 1 2, .ret], locals := [], returnsValue := true }
def method1 : Method := helper 1
def method2 : Method := helper 2
def method3 : Method := helper 3
def method4 : Method := helper 4
def program : Program := [method0, method1, method2, method3, method4]
def signatures : List String := [method0Signature, method1Signature, method2Signature, method3Signature, method4Signature]

end Extracted

namespace Tests.MethodIdentity

open CIL

example : method_named "System.UInt64 Examples.Identity::Left(System.UInt64,System.UInt64)" = 1 := rfl

bind_method root rootBody := "System.UInt64 Examples.Identity::Root(System.UInt64)"
bind_callee left leftBody := "System.UInt64 Examples.Identity::Left(System.UInt64,System.UInt64)" from rootBody
bind_callee right rightBody := "System.UInt64 Examples.Identity::Right(System.UInt64,System.UInt64)" from rootBody

-- Same arity, called in the other order: each name still reaches its own method and site.
example : left = 1 ∧ right = 2 := ⟨rfl, rfl⟩
example : leftBody = Extracted.helper 1 ∧ rightBody = Extracted.helper 2 := ⟨rfl, rfl⟩
example : rootBody.code[4]? = some (.call left 2) := left.call
example : rootBody.code[2]? = some (.call right 2) := right.call
example : Extracted.signatures[right]? = some "System.UInt64 Examples.Identity::Right(System.UInt64,System.UInt64)" := right.signature

-- Generated bindings are kernel-checked `rfl`, never elaborator-only evidence.
run_cmd do
  for name in [``left.signature, ``left.found, ``left.call] do
    let some (.thmInfo info) := (← Lean.getEnv).find? name | throwError "missing {name}"
    unless info.value.isAppOf ``Eq.refl || info.value.isAppOf ``rfl do throwError "{name} is not rfl: {info.value}"

/--
error: no extracted method has signature
  System.UInt64 Examples.Overloads::Pick(System.Int64)
methods named Pick:
  [3] System.UInt64 Examples.Overloads::Pick(System.UInt64)
  [4] System.UInt32 Examples.Overloads::Pick(System.UInt32)
-/
#guard_msgs in
example : method_named "System.UInt64 Examples.Overloads::Pick(System.Int64)" = 3 := rfl

/--
error: no extracted method has signature
  System.Void Examples.Identity::Missing()
extracted methods:
  [0] System.UInt64 Examples.Identity::Root(System.UInt64)
  [1] System.UInt64 Examples.Identity::Left(System.UInt64,System.UInt64)
  [2] System.UInt64 Examples.Identity::Right(System.UInt64,System.UInt64)
  [3] System.UInt64 Examples.Overloads::Pick(System.UInt64)
  [4] System.UInt32 Examples.Overloads::Pick(System.UInt32)
-/
#guard_msgs in
bind_method missing missingBody := "System.Void Examples.Identity::Missing()"

-- A resolved method that the parent never calls fails at binding, naming what it does call.
/--
error: rootBody does not call
  System.UInt64 Examples.Overloads::Pick(System.UInt64)
it calls:
  [2] System.UInt64 Examples.Identity::Right(System.UInt64,System.UInt64)
  [1] System.UInt64 Examples.Identity::Left(System.UInt64,System.UInt64)
-/
#guard_msgs in
bind_callee pick pickBody := "System.UInt64 Examples.Overloads::Pick(System.UInt64)" from rootBody

-- Duplicate signatures are reported with every index, never resolved to the first match.
def duplicated : List String := [Extracted.method1Signature, Extracted.method2Signature, Extracted.method1Signature]

/--
error: 2 extracted methods have signature
  System.UInt64 Examples.Identity::Left(System.UInt64,System.UInt64)
  [0] System.UInt64 Examples.Identity::Left(System.UInt64,System.UInt64)
  [2] System.UInt64 Examples.Identity::Left(System.UInt64,System.UInt64)
-/
#guard_msgs in
run_meta discard <| CIL.MethodIdentity.resolveIn ``duplicated Extracted.method1Signature

end Tests.MethodIdentity

/-! Batch verification places each extraction in its own namespace; the innermost table wins. -/
namespace BatchCase0.Extracted

def method0Signature : String := "System.Void Examples.Batch::Only()"
def method0 : CIL.Method := { code := [.ret], locals := [], returnsValue := false }
def program : CIL.Program := [method0]
def signatures : List String := [method0Signature]

end BatchCase0.Extracted

namespace BatchCase0

bind_method only onlyBody := "System.Void Examples.Batch::Only()"
example : only = 0 ∧ onlyBody = Extracted.method0 := ⟨rfl, rfl⟩

end BatchCase0
