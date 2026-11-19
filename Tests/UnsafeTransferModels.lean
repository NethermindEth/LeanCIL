import CIL.Extraction.DecodedMethod
import CIL.Safety.StepComposition
import Tests.Support

/-!
# Checked Unsafe transfer calls

The entry for each overload binds its element, address and declaration at a live site.
-/

namespace Tests.UnsafeTransferModels
open CIL CIL.Extraction CIL.Safety

/-- The open pointer overload and its external target at an Unsafe call. -/
private def site (name : MetadataName) (store : Bool) (element : TypeExpr)
    (byref : Bool) (convention : Nat) : RawInstruction :=
  let address := if byref then TypeExpr.byref (.atom runtimeScope "System.Byte")
    else .pointer .void
  let addressName := if byref then "System.Byte&" else "System.Void*"
  let result := fun type => if store then TypeExpr.void else type
  let parameters := fun type => if store then [address, type] else [address]
  let method : MethodRef :=
    { owner := unsafeOwner, name, hasThis := false, genericArity := 1,
      returnType := result element, parameters := parameters element,
      methodArguments := [element] }
  let text := name.text?.getD ""
  let target := runtimeScope ++ (if store then "::System.Void " else "::!!0 ") ++
    "System.Runtime.CompilerServices.Unsafe::" ++ text ++
    "(" ++ addressName ++ (if store then ",!!0)" else ")")
  let declared : OpenSignature :=
    { convention, returnType := result (.parameter 0), parameters := parameters (.parameter 0) }
  let call : CallSite :=
    { method, declared, name := text, target := .external target, typeArguments := [element],
      parameterCount := method.parameters.length, returnsValue := !store }
  ⟨0, 40, .call call⟩

/-- The decoder's instruction at one reachable, unlinked raw site. -/
private def decoded (environment : LayoutEnvironment) (profile : FeatureProfile)
    (raw : RawInstruction) : Option (List Instruction) :=
  let method : RawMethod :=
    { token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
      attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
      initLocals := true, maxStack := 2, genericParameters := [], code := [raw] }
  (Method.ofRaw? profile environment [] [true] method []).map Method.code

/-- Floating vectors fail resolution and cannot emit their width's transfer at any Unsafe site. -/
theorem rejectedFloatingSites :
    [("128", TransferKind.snapshot .vector128, Instruction.memory .load128,
       Instruction.memory .store128, 16),
     ("256", .snapshot .vector256, .memory .load256, .memory .store256, 32),
     ("512", .snapshot .vector512, .memory .load512, .memory .store512, 64)].all
      (fun (width, kind, loadOp, storeOp, alignment) =>
        ["System.Single", "System.Double"].all fun lane =>
          let element := TypeExpr.apply
            (.constructor intrinsicsScope ("System.Runtime.Intrinsics.Vector" ++ width ++ "`1"))
            (.atom runtimeScope lane)
          [false, true].all fun byref =>
            [(name!"Read", false, Instruction.memory (.pointerTransfer kind alignment false)),
             (name!"Write", true, .memory (.pointerTransfer kind alignment true)),
             (name!"ReadUnaligned", false, loadOp), (name!"WriteUnaligned", true, storeOp)].all
              fun (name, store, op) =>
                let raw := site name store element byref 0x10
                match raw.operand with
                | .call call => (runtimeModel {} .call call.method).isNone &&
                  decide (decoded {} .scalar raw = some [.unadmitted 40]) &&
                  !runtimeCatalog.siteAgrees {} .scalar raw op none none true
                | _ => false) = true := by decide +kernel

#print axioms rejectedFloatingSites

/-- The name, access direction and address restriction of each helper. -/
private def transfers : List (MetadataName × Bool × Bool) :=
  [(name!"Read", false, true), (name!"Write", true, true),
   (name!"ReadUnaligned", false, false), (name!"WriteUnaligned", true, false)]

/-- A sequential layout of one or more words, with the supplied packing. -/
private def packet (packing words : Nat) (byRefLike := false) : LayoutEnvironment :=
  let raw : List RawLayout :=
    [{ identity := "Fixture::Packet", explicit := false, packing := packing, declaredSize := 0,
       byRefLike, fields := List.replicate words { type := .unsigned64 } }]
  { rawLayouts := raw, layouts := (computeLayouts raw).getD #[] }

/-- Each live site keeps its call in every profile, with the width and alignment of its element. -/
private def resolves (environment : LayoutEnvironment) (element : TypeExpr)
    (kind : TransferKind) (alignment : Nat) : Bool :=
  transfers.all fun (name, store, aligned) =>
    [true, false].all fun byref =>
      let raw := site name store element byref 0x10
      match raw.operand with
      | .call call =>
        let model := runtimeModel environment .call call.method
        if aligned && byref then
          model.isNone && decide (decoded environment .scalar raw = some [.unadmitted 40])
        else
        let expected := if aligned then RuntimeModel.memory (.pointerTransfer kind alignment store)
          else .typedTransfer kind store
        let emitted := if aligned then Instruction.memory (.pointerTransfer kind alignment store)
          else typedTransferInstruction kind store
        let x64 : FeatureProfile :=
          { architecture := .x64, sse2 := true, ssse3 := true,
            sse41 := true, sse42 := true, avx := true, avx2 := true, bmi1 := true, bmi2 := true,
            x86Base64 := true, vector128Accelerated := true, vector256Accelerated := true }
        let arm : FeatureProfile :=
          { architecture := .arm64, armBase64 := true, advSimd := true,
            vector128Accelerated := true }
        model == some expected && [FeatureProfile.scalar, x64, arm].all fun profile =>
          decide (decoded environment profile raw = some [.call call.method {}]) &&
          runtimeCatalog.siteAgrees environment profile raw (.call call.method {}) &&
          !runtimeCatalog.siteAgrees environment profile raw emitted
      | _ => false

/-- The integer vector of the indicated width with unsigned 64-bit elements. -/
private def vector (width : String) : TypeExpr :=
  .apply (.constructor intrinsicsScope ("System.Runtime.Intrinsics.Vector" ++ width ++ "`1"))
    (.atom runtimeScope "System.UInt64")

/-- The closed signature selects a scalar or snapshot independently of the target profile. -/
theorem integerTransfers :
    resolves {} (.atom runtimeScope "System.UInt64") (.scalar 8 false) 8 &&
    resolves {} (.atom runtimeScope "System.Int16") (.scalar 2 true) 2 &&
    resolves {} (.enum "Fixture::Flag" (.atom runtimeScope "System.SByte")) (.scalar 1 true) 1 &&
    resolves {} (vector "128") (.snapshot .vector128) 16 &&
    resolves {} (vector "256") (.snapshot .vector256) 32 &&
    resolves {} (vector "512") (.snapshot .vector512) 64 := by decide +kernel

#print axioms integerTransfers

/-- Packing and field count can change independently for the same checked struct identity. -/
theorem aggregateTransfers :
    LayoutsValid (packet 1 1).rawLayouts (packet 1 1).layouts ∧
    LayoutsValid (packet 4 3).rawLayouts (packet 4 3).layouts ∧
    resolves (packet 1 1) (.aggregate "Fixture::Packet" 0) (.snapshot (.aggregate 8)) 1 ∧
    resolves (packet 4 3) (.aggregate "Fixture::Packet" 0) (.snapshot (.aggregate 24)) 4 ∧
    resolves (packet 4 3 true) (.aggregate "Fixture::Packet" 0) (.snapshot (.aggregate 24)) 4 := by
  decide +kernel

#print axioms aggregateTransfers

/-- Packing alone changes the natural alignment of an eight-byte packet at a fixed index. -/
theorem sameSizeDifferentAlignment :
    let type := TypeExpr.aggregate "Fixture::Packet" 0
    let packed := packet 1 1
    let natural := packet 8 1
    LayoutsValid packed.rawLayouts packed.layouts ∧
      LayoutsValid natural.rawLayouts natural.layouts ∧
      packed.callLayouts.valueShape type = .aggregate 8 ∧
      natural.callLayouts.valueShape type = .aggregate 8 ∧
      resolves packed type (.snapshot (.aggregate 8)) 1 ∧
      resolves natural type (.snapshot (.aggregate 8)) 8 := by decide +kernel

#print axioms sameSizeDifferentAlignment

/-- Unsupported storage and malformed method references have no transfer model. -/
theorem refusedElementsAndReferences :
    let word := TypeExpr.atom runtimeScope "System.UInt64"
    transfers.all (fun (name, store, _) =>
      let rejected := fun (type : TypeExpr) (change : MethodRef → MethodRef) =>
        match (site name store type false 0x10).operand with
        | .call call =>
          let changed := change call.method
          let raw := site name store type false 0x10
          let changedRaw := { raw with operand := .call { call with method := changed } }
          let expected : Option (List Instruction) :=
            if type == .parameter 0 then none else some [.unadmitted 40]
          (runtimeModel {} .call changed).isNone &&
            decide (decoded {} .scalar changedRaw = expected)
        | _ => false
      [TypeExpr.apply (.constructor runtimeScope "System.Span`1") word,
       .apply (.constructor runtimeScope "System.ReadOnlySpan`1") word, .parameter 0,
       .pointer word, .byref word, .object runtimeScope "System.String", .void,
       .apply (.objectConstructor runtimeScope "System.Collections.Generic.List`1") word,
       .aggregate "Fixture::Missing" 0, .atom runtimeScope "System.Double", .array word].all
          (fun type => rejected type id) &&
      rejected word (fun method => { method with owner := .apply unsafeOwner word }) &&
      rejected word (fun method => { method with
        owner := .atom "Other" "System.Runtime.CompilerServices.Unsafe" }) &&
      rejected word (fun method => { method with hasThis := true }) &&
      rejected word (fun method => { method with genericArity := 2 }) &&
      rejected word (fun method => { method with methodArguments := [] })) = true := by
  decide +kernel

#print axioms refusedElementsAndReferences

/-- A change to the open signature alone refuses both the kept call and the typed emission. -/
theorem refusedDeclarations :
    let word := TypeExpr.atom runtimeScope "System.UInt64"
    transfers.all (fun (name, store, aligned) =>
      let raw := site name store word false 0x10
      match raw.operand with
      | .call call =>
        let denied := fun (declared : OpenSignature) =>
          let changed := { raw with operand := .call { call with declared } }
          let op := if aligned then Instruction.memory (.pointerTransfer (.scalar 8 false) 8 store)
            else typedTransferInstruction (.scalar 8 false) store
          decide (decoded {} .scalar raw = some [.call call.method {}]) &&
            decide (decoded {} .scalar changed = some [.unadmitted 40]) &&
            !runtimeCatalog.siteAgrees {} .scalar changed (.call call.method {}) &&
            !runtimeCatalog.siteAgrees {} .scalar changed op
        let byteAddress := TypeExpr.byref (.atom runtimeScope "System.Byte")
        let forged := if aligned then { call.declared with
            parameters := if store then [byteAddress, .parameter 0] else [byteAddress] }
          else if store then { call.declared with parameters := [.pointer .void, word] }
          else { call.declared with returnType := word }
        denied forged && [0x00, 0x11, 0x30, 0x50, 0x70].all fun convention =>
          denied { call.declared with convention }
      | _ => false) = true := by decide +kernel

#print axioms refusedDeclarations

/-- Each unaligned overload binds its own target and open declaration to the closed address. -/
theorem crossedOverloads :
    [false, true].all (fun store =>
      let name := if store then name!"WriteUnaligned" else name!"ReadUnaligned"
      let element := TypeExpr.atom runtimeScope "System.UInt64"
      [false, true].all fun byref =>
        let raw := site name store element byref 0x10
        match raw.operand, (site name store element (!byref) 0x10).operand with
        | .call call, .call other =>
          let hole := fun (changed : CallSite) =>
            let changedRaw := { raw with operand := .call changed }
            decide (decoded {} .scalar changedRaw = some [.unadmitted 40])
          decide (decoded {} .scalar raw = some [.call call.method {}]) &&
            hole { call with target := other.target } &&
            hole { call with declared := other.declared }
        | _, _ => false) = true := by decide +kernel

#print axioms crossedOverloads

/-- An unknown Unsafe member admits only a dead hole. -/
theorem reservedEmissions :
    let control := site name!"Read" false (.atom runtimeScope "System.UInt64") false 0x10
    let other := site name!"Unknown" false (.atom runtimeScope "System.UInt64") false 0x10
    let operations := [Instruction.loadScalar 8, .storeScalar 8, .loadAggregate 8,
      .storeAggregate 8, .memory .load128, .memory .load256, .memory .load512,
      .memory .store128, .memory .store256, .memory .store512,
      .memory (.pointerTransfer (.scalar 8 false) 8 false)]
    (match control.operand with
     | .call call => decide (decoded {} .scalar control = some [.call call.method {}])
     | _ => false) = true ∧ decoded {} .scalar other = some [.unadmitted 40] ∧
      operations.any (fun op => runtimeCatalog.siteAgrees {} .scalar other op none none true)
        = false ∧
      runtimeCatalog.siteAgrees {} .scalar other (.unadmitted 40) none none false = true ∧
      runtimeCatalog.siteAgrees {} .scalar other (.unadmitted 40) none none true = false := by
  decide +kernel

#print axioms reservedEmissions

/-- A non-call instruction cannot claim the checked pointer transfer of a runtime model. -/
theorem nonCallTransferRefused :
    let raw : RawMethod := {
      token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
      attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
      initLocals := true, maxStack := 1, genericParameters := [], code := [⟨0, 0, .none⟩] }
    UnsafeCallsValid raw [true] [.nop] ∧
      ¬ UnsafeCallsValid raw [true] [.memory (.pointerTransfer (.scalar 8 false) 8 false)] := by
  decide +kernel

#print axioms nonCallTransferRefused

/-- A transfer over a pointer or span decodes to a hole and refuses a unary replacement. -/
theorem unresolvedTransfers :
    let byte := TypeExpr.atom runtimeScope "System.Byte"
    let control := site name!"ReadUnaligned" false byte false 0x10
    (match control.operand with
     | .call call => decide (decoded {} .scalar control = some [.call call.method {}]) &&
         !runtimeCatalog.siteAgrees {} .scalar control (.memory .bitcastByteBool) none none true
     | _ => false) = true ∧
      [TypeExpr.pointer .void, .apply (.constructor runtimeScope "System.Span`1") byte].all
        (fun element =>
          let raw := site name!"ReadUnaligned" false element false 0x10
          decide (decoded {} .scalar raw = some [.unadmitted 40]) &&
            !runtimeCatalog.siteAgrees {} .scalar raw (.memory .bitcastByteBool) none none true &&
            runtimeCatalog.siteAgrees {} .scalar raw (.unadmitted 40) none none false) = true := by
  decide +kernel

#print axioms unresolvedTransfers

/-- The kept call has the lowered result, including faults, for every kind and machine state. -/
theorem callEqualsTransfer (body : Method) (method : MethodRef) (pc alignment : Nat)
    (kind : TransferKind) (aligned store : Bool) (args stack : List Safety.Value)
    (frame : Safety.Frame) (memory : Safety.Memory) (unlinked : body.linkAt pc = none)
    (model : runtimeModel body.environment .call method = some (if aligned then
      .memory (.pointerTransfer kind alignment store) else .typedTransfer kind store)) :
    step body (.call method {}) pc args frame stack memory =
      step body (if aligned then .memory (.pointerTransfer kind alignment store)
        else typedTransferInstruction kind store) pc args frame stack memory := by
  cases aligned
  · exact step_call_typedTransfer body pc args frame memory unlinked model rfl stack
  · exact step_call_memory body pc args frame memory unlinked model rfl stack

#print axioms callEqualsTransfer

/-- A misaligned pointer faults for both aligned transfers on an otherwise writable allocation. -/
theorem misalignedTransfers :
    let body : Method := { code := [], locals := [], returnsValue := false }
    let frame : Safety.Frame := { activation := 0, locals := [], owned := [] }
    let address := ManagedReference.address ⟨0, 1⟩
    let fault := ExecutionFault.memory .alignment address 8
    [false, true].all (fun store =>
      let name := if store then name!"Write" else name!"Read"
      let raw := site name store (.atom runtimeScope "System.UInt64") false 0x10
      match raw.operand with
      | .call call =>
        let stack : List Safety.Value := if store then [.scalar (.i64 0), .reference address]
          else [.reference address]
        match step body (.call call.method {}) 0 [] frame stack Tests.caller with
        | .error actual => actual == fault
        | .ok _ => false
      | _ => false) = true := by decide +kernel

#print axioms misalignedTransfers

end Tests.UnsafeTransferModels
