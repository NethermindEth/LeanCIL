import CIL.Extraction.Generics
import Tests.Support

/-! An external call site may emit `.call` only into a matching import slot past every extracted method. -/
namespace Tests.ImportEvidence
open CIL CIL.Extraction

def word : TypeExpr := .atom
  "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
  "System.UInt64"
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
  method := {
    owner := .atom "Library, Version=1.0.0.0, Culture=neutral, \
      PublicKeyToken=null" "Library.Adder", name := name!"AddTo", hasThis := false,
    genericArity := 0, returnType := .void,
    parameters := [.byref word, .byref word, .byref word] },
  name := "AddTo", target := .external addToIdentity, typeArguments := [], parameterCount := 3,
  returnsValue := false }
def call (site : CallSite) : RawInstruction := ⟨8, 40, .call site⟩

/-- The link to method or slot `target`. -/
def linked (target : Nat) : Option Link := some (.direct target)
/-- The plain `call` the extractor emits for `site`. -/
def emits (site : CallSite) : Instruction := .call site.method

example : validateManagedCall methods imports (call site) true (linked 1) (emits site) = true := by
  decide +kernel

-- Forged slots: identity, argument count, receiver and result shape must each match the site.
example : validateManagedCall methods [{ slot with identity := addToIdentity ++ " " }] (call site)
    true (linked 1) (emits site) = false := by decide +kernel
example : validateManagedCall methods [{ slot with identity := "Other::System.Void \
    Library.Adder::AddTo(System.UInt64&,System.UInt64&,System.UInt64&)" }] (call site)
    true (linked 1) (emits site) = false := by decide +kernel
example : validateManagedCall methods [{ slot with parameterCount := 2 }] (call site)
    true (linked 1) (emits site) = false := by decide +kernel
example : validateManagedCall methods [{ slot with returnsValue := true }] (call site)
    true (linked 1) (emits site) = false := by decide +kernel
example : validateManagedCall methods [{ slot with hasThis := true }] (call site)
    true (linked 1) (emits site) = false := by decide +kernel
-- The emitted call names the site's method, so its argument count is the site's, receiver
-- included.
example : validateManagedCall methods imports (call site) true (linked 1)
    (.call { site.method with parameters := [.byref word, .byref word] }) = false := by
  decide +kernel
example : validateManagedCall methods imports (call site) true (linked 1)
    (.call { site.method with hasThis := true }) = false := by decide +kernel
example : validateManagedCall methods [{ slot with hasThis := true }]
    (call { site with method.hasThis := true }) true (linked 1)
    (emits { site with method.hasThis := true }) = true := by decide +kernel
example : validateManagedCall methods [{ slot with hasThis := true }]
    (call { site with method.hasThis := true }) true (linked 1) (emits site) = false := by
  decide +kernel
-- The site's own shape is checked against the slot too.
example : validateManagedCall methods imports (call { site with returnsValue := true }) true
    (linked 1) (emits site) = false := by decide +kernel
example : validateManagedCall methods imports (call { site with parameterCount := 2 }) true
    (linked 1) (emits site) = false := by decide +kernel

-- A slot index inside the program, or past the import table, is never an import.
example : validateManagedCall methods imports (call site) true (linked 0) (emits site) = false :=
    by
  decide +kernel
example : validateManagedCall methods imports (call site) true (linked 2) (emits site) = false :=
    by
  decide +kernel
example : validateManagedCall [] imports (call site) true (linked 0) (emits site) = true := by
  decide +kernel
example : validateManagedCall [] imports (call site) true (linked 1) (emits site) = false := by
  decide +kernel
-- Without an import table the previous rule applies: an external site emits no call.
example : validateManagedCall methods [] (call site) true (linked 1) (emits site) = false := by
  decide +kernel
-- A forged link: none, or not a direct one, enters no slot.
example : validateManagedCall methods imports (call site) true none (emits site) = false := by
  decide +kernel
example : validateManagedCall methods imports (call site) true (some (.virtual [(word, 1)]))
    (emits site) = false := by decide +kernel
-- An import call takes no prefix: the call must not retire the caller's frame or be resolved on
-- a constrained type.
example : validateManagedCall methods imports (call site) true (linked 1)
    (.call site.method { tail := true }) = false := by decide +kernel
example : validateManagedCall methods imports (call site) true (linked 1)
    (.call site.method { constrained := some word }) = false := by decide +kernel

-- Only a plain `call` of a closed method may target an import; constructors and generic sites
-- may not.
example :
    validateManagedCall methods imports ⟨8, 115, .call site⟩ true (linked 1) (emits site) =
      false := by decide +kernel
example : validateManagedCall methods imports ⟨8, 115, .call site⟩ true (linked 1)
    (.newobj site.method) = false := by decide +kernel
example : validateManagedCall methods imports (call { site with typeArguments := [word] }) true
    (linked 1) (emits site) = false := by decide +kernel

-- A managed site or a non-call instruction cannot reach the import range either.
example : validateManagedCall methods imports (call { site with target := .managed 100663298 })
    true (linked 1) (emits site) = false := by decide +kernel
example : validateManagedCall methods imports ⟨8, 88, .none⟩ true (linked 1) (emits site) =
    false := by decide +kernel
-- A runtime-modelled external call still emits its model, and dead code is unconstrained.
example : validateManagedCall methods imports (call site) true none .add = true := by
  decide +kernel
example : validateManagedCall methods imports (call site) false (linked 0) (emits site) = true :=
    by
  decide +kernel

/-- The whole-method check: the same forged slot is rejected at the only live call. -/
def caller : RawMethod := { callee with code := [⟨0, 2, .none⟩, ⟨1, 3, .none⟩, ⟨2, 4, .none⟩, ⟨3, 40, .call site⟩, ⟨8, 42, .none⟩] }
def emitted : Method :=
  { returnsValue := false, locals := [], code := [.ldarg 0, .ldarg 1, .ldarg 2, emits site, .ret],
    links := [(3, .direct 1)] }
example : ManagedCallsValid methods imports (fun _ => false) caller [true, true, true, true, true]
    emitted := by decide +kernel
example : ¬ ManagedCallsValid methods [{ slot with identity := "forged" }] (fun _ => false) caller
    [true, true, true, true, true] emitted := by decide +kernel
example : ¬ ManagedCallsValid methods [] (fun _ => false) caller [true, true, true, true, true]
    emitted := by decide +kernel
example : ManagedCallsValid methods [] (fun _ => false) caller [true, true, true, false, true]
    emitted := by decide +kernel

/-- Two calls to the slot, at pcs 3 and 7, among nops. -/
def callerTwice : RawMethod := { callee with code := [⟨0, 0, .none⟩, ⟨1, 0, .none⟩,
  ⟨2, 0, .none⟩, ⟨3, 40, .call site⟩, ⟨8, 0, .none⟩, ⟨9, 0, .none⟩, ⟨10, 0, .none⟩,
  ⟨11, 40, .call site⟩, ⟨16, 42, .none⟩] }
/-- The emitted body of `callerTwice`, each call linked to the slot. -/
def emittedTwice : Method := {
  returnsValue := false, locals := [],
  code := [.nop, .nop, .nop, emits site, .nop, .nop, .nop, emits site,
    .ret], links := [(3, .direct 1), (7, .direct 1)] }
/-- Every pc of `callerTwice` is live. -/
def liveTwice : List Bool := List.replicate 9 true
/-- `emittedTwice` with the link table `links`. -/
def linkedTwice (links : List (Nat × Link)) : Method := { emittedTwice with links := links }

-- A table is accepted when its keys ascend, sit at the call pcs and give each its call's link.
example :
    ManagedCallsValid methods imports (fun _ => false) callerTwice liveTwice emittedTwice := by
  decide +kernel
example : ManagedCallsValid methods imports (fun _ => false) callerTwice liveTwice
    (linkedTwice [(3, .direct 1), (7, .direct 1)]) := by decide +kernel
-- A table that omits a call pc, even a dead one.
example : ¬ ManagedCallsValid methods imports (fun _ => false) callerTwice liveTwice
    (linkedTwice [(3, .direct 1)]) := by decide +kernel
example : ¬ ManagedCallsValid methods imports (fun _ => false) callerTwice (liveTwice.set 7 false)
    (linkedTwice [(3, .direct 1)]) := by decide +kernel
-- A key at a pc that is not a call, or past the code.
example : ¬ ManagedCallsValid methods imports (fun _ => false) callerTwice liveTwice
    (linkedTwice [(3, .direct 1), (5, .direct 1), (7, .direct 1)]) := by decide +kernel
example : ¬ ManagedCallsValid methods imports (fun _ => false) callerTwice liveTwice
    (linkedTwice [(3, .direct 1), (7, .direct 1), (9, .direct 1)]) := by decide +kernel
-- Keys out of order or repeated.
example : ¬ ManagedCallsValid methods imports (fun _ => false) callerTwice liveTwice
    (linkedTwice [(7, .direct 1), (3, .direct 1)]) := by decide +kernel
example : ¬ ManagedCallsValid methods imports (fun _ => false) callerTwice liveTwice
    (linkedTwice [(3, .direct 1), (3, .direct 1), (7, .direct 1)]) := by decide +kernel
-- Every key sits at a call pc with its call's link, but key 5 follows the larger key 7.
example : ¬ ManagedCallsValid methods imports (fun _ => false) callerTwice liveTwice
    (linkedTwice [(3, .direct 1), (7, .direct 1), (5, .direct 1)]) := by decide +kernel
-- A call pc linked to an extracted method instead of the slot its site names.
example : ¬ ManagedCallsValid methods imports (fun _ => false) callerTwice liveTwice
    (linkedTwice [(3, .direct 0), (7, .direct 1)]) := by decide +kernel


-- The validator's guarantees, not only these instances.
example (raw : RawInstruction) (method : MethodRef) (prefixes : CallPrefixes) (target : Nat)
    (valid : validateManagedCall methods imports raw true (linked target) (.call method prefixes) =
      true) :
    target < 2 := validated_call_bound valid

/-- Imported slot zero follows all extracted methods, even with a larger indexed table. -/
theorem indexed_import_valid :
    ManagedCallsValid (List.replicate 64 ⟨[], callee⟩) imports (fun _ => false)
      { callee with code := [call site] } [true]
      { locals := [], returnsValue := false, code := [emits site],
        links := [(0, .direct 64)] } := by decide +kernel
#print axioms indexed_import_valid

/-- A target before the import table cannot borrow its slot zero by truncated subtraction. -/
theorem indexed_import_underflow_rejected :
    ¬ ManagedCallsValid (List.replicate 64 ⟨[], callee⟩) imports (fun _ => false)
      { callee with code := [call site] } [true]
      { locals := [], returnsValue := false, code := [emits site],
        links := [(0, .direct 63)] } := by decide +kernel
#print axioms indexed_import_underflow_rejected

/-- A missing imported slot is rejected rather than replaced with a default descriptor. -/
theorem indexed_import_missing_rejected :
    ¬ ManagedCallsValid (List.replicate 64 ⟨[], callee⟩) imports (fun _ => false)
      { callee with code := [call site] } [true]
      { locals := [], returnsValue := false, code := [emits site],
        links := [(0, .direct 65)] } := by decide +kernel
#print axioms indexed_import_missing_rejected
end Tests.ImportEvidence