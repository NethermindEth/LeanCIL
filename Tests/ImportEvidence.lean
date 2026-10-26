import CIL.Extraction.Generics

/-! An external call site may emit `.call` only into a matching import slot past every extracted method. -/
namespace Tests.ImportEvidence
open CIL CIL.Extraction

def word : TypeExpr := .atom "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" "System.UInt64"
def addToIdentity : String :=
  "Library, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null::System.Void Library.Adder::AddTo(System.UInt64&,System.UInt64&,System.UInt64&)"
def callee : RawMethod := {
  token := 100663298, owner := "Test", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := word, parameters := [word], locals := [], initLocals := true, maxStack := 1,
  genericParameters := [], code := [⟨0, 2, .none⟩, ⟨1, 42, .none⟩] }
/-- One extracted method, so slot 0 is method index 1. -/
def methods : List SpecializedMethod := [⟨[], callee⟩]
def slot : ImportSlot := { identity := addToIdentity, closureDigest := "digest", parameterCount := 3, hasThis := false, returnsValue := false }
def imports : List ImportSlot := [slot]
def site : CallSite := {
  declaringType := .atom "Library, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Library.Adder", name := "AddTo",
  target := .external addToIdentity, typeArguments := [], parameterCount := 3, hasThis := false, returnsValue := false,
  returnType := .void, parameterTypes := [.byref word, .byref word, .byref word] }
def call (site : CallSite) : RawInstruction := ⟨8, 40, .call site⟩

example : validateManagedCall methods imports (call site) true (.call 1 3) = true := by decide +kernel

-- Forged slots: identity, argument count, receiver and result shape must each match the site.
example : validateManagedCall methods [{ slot with identity := addToIdentity ++ " " }] (call site) true (.call 1 3) = false := by decide +kernel
example : validateManagedCall methods [{ slot with identity := "Other::System.Void Library.Adder::AddTo(System.UInt64&,System.UInt64&,System.UInt64&)" }] (call site) true (.call 1 3) = false := by decide +kernel
example : validateManagedCall methods [{ slot with parameterCount := 2 }] (call site) true (.call 1 3) = false := by decide +kernel
example : validateManagedCall methods [{ slot with returnsValue := true }] (call site) true (.call 1 3) = false := by decide +kernel
example : validateManagedCall methods [{ slot with hasThis := true }] (call site) true (.call 1 3) = false := by decide +kernel
-- The emitted argument count must agree with the site, including the receiver.
example : validateManagedCall methods imports (call site) true (.call 1 2) = false := by decide +kernel
example : validateManagedCall methods imports (call site) true (.call 1 4) = false := by decide +kernel
example : validateManagedCall methods [{ slot with hasThis := true }] (call { site with hasThis := true }) true (.call 1 4) = true := by decide +kernel
example : validateManagedCall methods [{ slot with hasThis := true }] (call { site with hasThis := true }) true (.call 1 3) = false := by decide +kernel
-- The site's own shape is checked against the slot too.
example : validateManagedCall methods imports (call { site with returnsValue := true }) true (.call 1 3) = false := by decide +kernel
example : validateManagedCall methods imports (call { site with parameterCount := 2 }) true (.call 1 2) = false := by decide +kernel

-- A slot index inside the program, or past the import table, is never an import.
example : validateManagedCall methods imports (call site) true (.call 0 3) = false := by decide +kernel
example : validateManagedCall methods imports (call site) true (.call 2 3) = false := by decide +kernel
example : validateManagedCall [] imports (call site) true (.call 0 3) = true := by decide +kernel
example : validateManagedCall [] imports (call site) true (.call 1 3) = false := by decide +kernel
-- Without an import table the previous rule applies: an external site emits no call.
example : validateManagedCall methods [] (call site) true (.call 1 3) = false := by decide +kernel

-- Only a plain `call` of a closed method may target an import; constructors and generic sites may not.
example : validateManagedCall methods imports ⟨8, 115, .call site⟩ true (.call 1 3) = false := by decide +kernel
example : validateManagedCall methods imports ⟨8, 115, .call site⟩ true (.newAggregate 1 3 0) = false := by decide +kernel
example : validateManagedCall methods imports (call site) true (.newVector256 1 3) = false := by decide +kernel
example : validateManagedCall methods imports (call { site with typeArguments := [word] }) true (.call 1 3) = false := by decide +kernel

-- A managed site or a non-call instruction cannot reach the import range either.
example : validateManagedCall methods imports (call { site with target := .managed 100663298 }) true (.call 1 3) = false := by decide +kernel
example : validateManagedCall methods imports ⟨8, 88, .none⟩ true (.call 1 3) = false := by decide +kernel
-- A runtime-modelled external call still emits its model, and dead code is unconstrained.
example : validateManagedCall methods imports (call site) true .add = true := by decide +kernel
example : validateManagedCall methods imports (call site) false (.call 0 3) = true := by decide +kernel

/-- The whole-method check: the same forged slot is rejected at the only live call. -/
def caller : RawMethod := { callee with code := [⟨0, 2, .none⟩, ⟨1, 3, .none⟩, ⟨2, 4, .none⟩, ⟨3, 40, .call site⟩, ⟨8, 42, .none⟩] }
def emitted : Method := { returnsValue := false, locals := [], code := [.arg 0, .arg 1, .arg 2, .call 1 3, .ret] }
example : ManagedCallsValid methods imports caller [true, true, true, true, true] emitted := by decide +kernel
example : ¬ ManagedCallsValid methods [{ slot with identity := "forged" }] caller [true, true, true, true, true] emitted := by decide +kernel
example : ¬ ManagedCallsValid methods [] caller [true, true, true, true, true] emitted := by decide +kernel
example : ManagedCallsValid methods [] caller [true, true, true, false, true] emitted := by decide +kernel

-- The validator's guarantees, not only these instances.
example (raw : RawInstruction) (target count : Nat) (valid : validateManagedCall methods imports raw true (.call target count) = true) :
    target < 2 := validated_call_bound valid

/-- Imported slot zero follows all extracted methods, even with a larger indexed table. -/
theorem indexed_import_valid :
    ManagedCallsValid (List.replicate 64 ⟨[], callee⟩) imports
      { callee with code := [call site] } [true]
      { locals := [], returnsValue := false, code := [.call 64 3] } := by decide +kernel
#print axioms indexed_import_valid

/-- A target before the import table cannot borrow its slot zero by truncated subtraction. -/
theorem indexed_import_underflow_rejected :
    ¬ ManagedCallsValid (List.replicate 64 ⟨[], callee⟩) imports
      { callee with code := [call site] } [true]
      { locals := [], returnsValue := false, code := [.call 63 3] } := by decide +kernel
#print axioms indexed_import_underflow_rejected

/-- A missing imported slot is rejected rather than replaced with a default descriptor. -/
theorem indexed_import_missing_rejected :
    ¬ ManagedCallsValid (List.replicate 64 ⟨[], callee⟩) imports
      { callee with code := [call site] } [true]
      { locals := [], returnsValue := false, code := [.call 65 3] } := by decide +kernel
#print axioms indexed_import_missing_rejected
end Tests.ImportEvidence
