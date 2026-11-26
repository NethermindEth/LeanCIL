import Tests.Support.EnumIdentity
import Tests.MetadataWorld

/-!
# Metadata binding tests

A hand-built world of two pinned assemblies: `T`, which carries the operands under test, and
`Lib`, which defines the class `Lib.Box` that `T` calls into. Every operand of `T` that the
extractor can state is checked against its metadata and must pass. Each rejection then changes
one fact of the metadata or of the operand and asserts the exact error.
-/

namespace Tests.MetadataBinding

open CIL CIL.Extraction Tests.MetadataBuilder Tests.MetadataWorld


/-- The publisher token in the framework's System.Runtime AssemblyRef rows. -/
private def runtimePublisher : List Nat := [0xB0, 0x3F, 0x5F, 0x7F, 0x11, 0xD5, 0x0A, 0x3A]

/-- Whether checking an operand against a pair of slices gives these facts. -/
private def passes (ownSlice libSlice : MetadataSlice) (token : Nat) (operand : RawOperand)
    (arity : Nat := 0) : Bool :=
  match (do
    let env := MetadataEnv.ofSlices [← ownSlice.index, ← libSlice.index]
      (platform := worldPlatform)
    checkEntry env arity token operand) with
  | .ok _ => true
  | .error _ => false

/-- Whether checking an operand fails with exactly this error. -/
private def rejects (ownSlice libSlice : MetadataSlice) (token : Nat) (operand : RawOperand)
    (error : MetadataError) (arity : Nat := 0) : Bool :=
  match (do
    let env := MetadataEnv.ofSlices [← ownSlice.index, ← libSlice.index]
      (platform := worldPlatform)
    checkEntry env arity token operand) with
  | .error found => found == error
  | .ok _ => false

/-- A runtime MemberRef, optionally instantiated by a MethodSpec, in the calling assembly. -/
private def memberFixture (namespace_ owner name : String) (signature : List Nat)
    (instantiation : Option (List Nat)) (ownerArgument : Option Nat := none) :
    MetadataSlice × Nat := build (do
  let _ ← ownWorld
  let reference ← row Table.typeRef [6, ← string owner, ← string namespace_]
  let parent ← match ownerArgument with
    | none => pure (tokenRow reference * 8 + 1)
    | some code => do
      let spec ← row Table.typeSpec [← blob [0x15, 0x12, tokenRow reference * 4 + 1, 1, code]]
      pure (tokenRow spec * 8 + 4)
  let member ← row Table.memberRef [parent, ← string name, ← blob signature]
  match instantiation with
  | none => pure member
  | some arguments => row Table.methodSpec [tokenRow member * 2 + 1, ← blob arguments]
  ) (bytesOf "T")

/-- A static external call whose closed arguments and open declaration are checked separately. -/
private def memberCall (owner : TypeExpr) (name : MetadataName) (text identity : String)
    (arity : Nat) (arguments : List TypeExpr) (declared : OpenSignature) (returned : TypeExpr)
    (parameters : List TypeExpr) : CallSite :=
  { method := { owner, name, genericArity := arity, hasThis := false,
                methodArguments := arguments, returnType := returned, parameters },
    name := text, target := .external (runtimeScope ++ "::" ++ identity), declared,
    typeArguments := arguments, parameterCount := parameters.length, returnsValue := true }

/-- The SizeOf call states Int32 as its only method argument. -/
private def sizeCall (arity : Nat) (arguments : List TypeExpr) : CallSite :=
  memberCall (.atom runtimeScope "System.Runtime.CompilerServices.Unsafe") name!"SizeOf" "SizeOf"
    "System.Int32 System.Runtime.CompilerServices.Unsafe::SizeOf()" arity arguments
    { convention := 0x10, returnType := int32 } int32 []

/-- The first parameter of Object.ReferenceEquals as claimed before and after substitution. -/
private def referenceEqualsCall (declared closed : TypeExpr) : CallSite :=
  let root := TypeExpr.object runtimeScope "System.Object"
  let result := TypeExpr.primitive .boolean
  memberCall (.atom runtimeScope "System.Object") name!"ReferenceEquals" "ReferenceEquals"
    "System.Boolean System.Object::ReferenceEquals(System.Object,System.Object)" 0 []
    { convention := 0, returnType := result, parameters := [declared, root] } result [closed, root]

/-- An object parameter must name System.Object in the signature's primitive scope in both
    the open declaration and the closed call. -/
theorem binds_root_object_parameters :
  let member := memberFixture "System" "Object" "ReferenceEquals" [0, 2, 2, 0x1C, 0x1C] none
  let root := TypeExpr.object runtimeScope "System.Object"
  let wrongScope := TypeExpr.object libScope "System.Object"
  let wrongName := TypeExpr.object runtimeScope "System.String"
  passes member.1 lib member.2 (.call (referenceEqualsCall root root)) = true ∧
    [(wrongScope, root), (root, wrongScope), (wrongName, root), (root, wrongName)].all
      (fun (openType, closedType) => rejects member.1 lib member.2
        (.call (referenceEqualsCall openType closedType)) (.operandMismatch member.2)) = true
  := by decide +kernel
#print axioms binds_root_object_parameters

/-- An absent instantiation is valid for Min. A present instantiation must have positive arity. -/
private def minCall : CallSite :=
  memberCall (.atom runtimeScope "System.Math") name!"Min" "Min"
    "System.Int32 System.Math::Min(System.Int32,System.Int32)" 0 []
    { convention := 0, returnType := int32, parameters := [int32, int32] } int32 [int32, int32]

example :
    let spec := memberFixture "System.Runtime.CompilerServices" "Unsafe" "SizeOf"
      [0x10, 2, 0, 8] (some [0x0A, 1, 8])
    rejects spec.1 lib spec.2 (.call (sizeCall 2 [int32])) (.genericMismatch spec.2) := by
  decide +kernel

example :
    let member := memberFixture "System.Runtime.CompilerServices" "Unsafe" "SizeOf"
      [0x10, 1, 0, 8] none
    rejects member.1 lib member.2 (.call (sizeCall 1 [])) (.genericMismatch member.2) := by
  decide +kernel

example :
    let spec := memberFixture "System" "Math" "Min" [0, 2, 8, 8, 8] (some [0x0A, 0])
    rejects spec.1 lib spec.2 (.call minCall) (.genericMismatch spec.2) := by decide +kernel

example :
    let spec := memberFixture "System.Runtime.CompilerServices" "Unsafe" "SizeOf"
      [0x10, 1, 0, 8] (some [0x0A, 1, 8])
    let member := memberFixture "System" "Math" "Min" [0, 2, 8, 8, 8] none
    passes spec.1 lib spec.2 (.call (sizeCall 1 [int32])) &&
      passes member.1 lib member.2 (.call minCall) := by decide +kernel

/-- G<UInt64>.M<UInt64>() declares an owner or method variable as its return type. -/
private def genericOwnerCall (returned : TypeExpr) (spelling : String) : CallSite :=
  memberCall (.apply (.objectConstructor runtimeScope "System.G`1") uint64) name!"M" "M"
    (spelling ++ " System.G`1<System.UInt64>::M()") 1 [uint64]
    { convention := 0x10, returnType := returned } uint64 []

/-- Both instances return UInt64, so only the open declaration distinguishes !0 and !!0. -/
example :
    let owner := memberFixture "System" "G`1" "M" [0x10, 1, 0, 0x13, 0]
      (some [0x0A, 1, 0x0B]) (some 0x0B)
    rejects owner.1 lib owner.2 (.call (genericOwnerCall (.parameter 0) "!0"))
      (.operandMismatch owner.2) := by decide +kernel

example :
    let member := memberFixture "System" "G`1" "M" [0x10, 1, 0, 0x1E, 0]
      (some [0x0A, 1, 0x0B]) (some 0x0B)
    rejects member.1 lib member.2 (.call (genericOwnerCall (.ownerParameter 0) "!!0"))
      (.operandMismatch member.2) := by decide +kernel

example :
    let owner := memberFixture "System" "G`1" "M" [0x10, 1, 0, 0x13, 0]
      (some [0x0A, 1, 0x0B]) (some 0x0B)
    let member := memberFixture "System" "G`1" "M" [0x10, 1, 0, 0x1E, 0]
      (some [0x0A, 1, 0x0B]) (some 0x0B)
    passes owner.1 lib owner.2 (.call (genericOwnerCall (.ownerParameter 0) "!0")) &&
      passes member.1 lib member.2 (.call (genericOwnerCall (.parameter 0) "!!0")) := by
  decide +kernel

/-- The signed BigMul(int,int) operand has a concrete Int64 result before substitution. -/
private def signedProduct (declared : TypeExpr) (identity : String) : CallSite :=
  let result := TypeExpr.primitive .int64
  memberCall (.atom runtimeScope "System.Math") name!"BigMul" "BigMul"
    (identity ++ " System.Math::BigMul(System.Int32,System.Int32)") 0 []
    { convention := 0, returnType := declared, parameters := [int32, int32] } result [int32, int32]

example :
    let result := TypeExpr.primitive .int64
    let member := memberFixture "System" "Math" "BigMul" [0, 2, 0x0A, 8, 8] none
    passes member.1 lib member.2 (.call (signedProduct result "System.Int64")) := by decide +kernel

example :
    let member := memberFixture "System" "Math" "BigMul" [0, 2, 0x1E, 0, 8, 8] none
    let openCall := { signedProduct (.parameter 0) "!!0" with method.returnType := .parameter 0 }
    rejects member.1 lib member.2 (.call openCall) (.operandMismatch member.2) 1 &&
      (substituteOperand [.primitive .int64] [] 1 (.call openCall)).any
        (fun | .call site => site.method.returnType == .primitive .int64
             | _ => false) := by decide +kernel

/-- Replace the bytes of a row of a slice. -/
private def mutateRow (slice : MetadataSlice) (token : Nat) (change : List Nat → List Nat) :
    MetadataSlice :=
  { slice with rows := slice.rows.map fun (key, bytes) =>
      if key == token then (key, change bytes) else (key, bytes) }

/-- Replace the bytes of a blob of a slice. -/
private def mutateBlob (slice : MetadataSlice) (offset : Nat) (change : List Nat → List Nat) :
    MetadataSlice :=
  { slice with blobs := slice.blobs.map fun (key, bytes) =>
      if key == offset then (key, change bytes) else (key, bytes) }

/-! ## Operands that match their metadata -/

theorem accepts_type_operand :
    passes own.1 lib tokens.objectRef (.type (.atom runtimeScope "System.Object")) = true := by
  decide +kernel
theorem accepts_external_call :
    passes own.1 lib tokens.writeLine (.call writeLineSite) = true := by decide +kernel
theorem accepts_managed_call :
    passes own.1 lib tokens.getRef (.call getSite) = true := by decide +kernel
/-- A virtual interface slot requires a carried method declared on an interface. -/
theorem static_slot_requires_metadata :
    rejects own.1 lib tokens.writeLine
      (.call { writeLineSite with staticVirtualInterfaceSlot := true })
      (.operandMismatch tokens.writeLine) &&
    rejects own.1 lib tokens.getRef (.call { getSite with staticVirtualInterfaceSlot := true })
      (.operandMismatch tokens.getRef) := by decide +kernel
#print axioms static_slot_requires_metadata

/-- Both the interface owner and the virtual method flag are required for a static slot. -/
theorem static_slot_flags :
    let markInterface := fun (slice : MetadataSlice) =>
      mutateRow slice (tokenOf Table.typeDef 2) fun bytes => bytes.set 0 0xA1
    let markVirtual := fun (slice : MetadataSlice) =>
      mutateRow slice (tokenOf Table.methodDef 1) fun bytes => bytes.set 6 0xD6
    let slot := RawOperand.call { getSite with staticVirtualInterfaceSlot := true }
    passes own.1 (markVirtual (markInterface lib)) tokens.getRef slot &&
      !passes own.1 (markVirtual lib) tokens.getRef slot &&
      !passes own.1 (markInterface lib) tokens.getRef slot := by
  decide +kernel
#print axioms static_slot_flags
theorem accepts_generic_call :
    passes own.1 lib tokens.idSpec (.call idSite) = true := by decide +kernel
theorem accepts_string :
    passes own.1 lib tokens.hello (.text "hi") = true := by decide +kernel
theorem accepts_indirect :
    passes own.1 lib tokens.indirect (.indirectCall .void [int32] false false 0) = true := by
  decide +kernel
theorem accepts_fields :
    passes own.1 lib tokens.totalField
      (.field (.atom "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Program")
        1 int32 name!"total" true) = true ∧
    passes own.1 lib tokens.countField countOperand = true := by decide +kernel
/-! ## Operands whose metadata or claim changed -/

/-- The bytes of a row of a slice. -/
private def rowOf (slice : MetadataSlice) (token : Nat) : List Nat :=
  (slice.rows.lookup token).getD []

/-- The offset of the blob entry with a payload, assuming a one-byte length prefix. -/
private def blobOffset (slice : MetadataSlice) (payload : List Nat) : Nat :=
  match slice.blobs.find? (fun entry => entry.2.drop 1 == payload) with
  | some (offset, _) => offset
  | none => 0

/-- Both assemblies declare Int32 Get(Object). Lib uses a different core AssemblyRef version. -/
private def getWithObject (slice : MetadataSlice) : MetadataSlice :=
  mutateBlob slice (blobOffset slice [0, 0, 8]) fun _ => [4, 0, 1, 8, 0x1C]

/-- Primitive results and parameters bind separately to the MemberRef and MethodDef scopes. -/
theorem managed_call_binds_both_primitive_scopes :
    let caller := getWithObject own.1
    let callee := mutateRow (getWithObject lib) 0x23000001 fun row => row.set 0 10
    let scope := "System.Runtime, Version=10.0.0.0, Culture=neutral, " ++
      "PublicKeyToken=b03f5f7f11d50a3a"
    let declaredObject := TypeExpr.object runtimeScope "System.Object"
    let closedObject := TypeExpr.object scope "System.Object"
    let closedResult := TypeExpr.atom scope "System.Int32"
    let call := { getSite with
      declared.parameters := [declaredObject], parameterCount := 1
      method.parameters := [closedObject], method.returnType := closedResult }
    passes caller callee tokens.getRef (.call call) = true ∧
      [{ call with declared.parameters := [closedObject] },
       { call with method.parameters := [declaredObject] },
       { call with declared.returnType := closedResult },
       { call with method.returnType := int32 }].all (fun changed =>
         rejects caller callee tokens.getRef (.call changed) (.operandMismatch tokens.getRef)) = true
    := by decide +kernel
#print axioms managed_call_binds_both_primitive_scopes

/-- A row whose two bytes at `position` are copied from another row of the slice. -/
private def borrow (slice : MetadataSlice) (token source position : Nat) : MetadataSlice :=
  mutateRow slice token fun bytes =>
    bytes.take position ++ ((rowOf slice source).drop position).take 2 ++ bytes.drop (position + 2)

/-- A type token whose name column names another string that is present: `Console` becomes
    `Object`. -/
private def renamedConsole : MetadataSlice := borrow own.1 tokens.consoleRef tokens.objectRef 2

/-- A type token whose name offset has no entry. -/
private def dangling : MetadataSlice :=
  mutateRow own.1 tokens.consoleRef fun bytes => bytes.take 2 ++ [0xFF, 0x7F] ++ bytes.drop 4

theorem rejects_a_row_byte_that_names_another_string :
    rejects renamedConsole lib tokens.consoleRef (.type (.atom runtimeScope "System.Console"))
      (.operandMismatch tokens.consoleRef) = true := by decide +kernel
#print axioms rejects_a_row_byte_that_names_another_string

theorem rejects_a_signature_byte_that_changes_a_parameter :
    rejects (mutateBlob own.1 (blobOffset own.1 [0x00, 0x01, 0x01, 0x08]) fun bytes =>
        bytes.set 4 0x0A) lib tokens.writeLine (.call writeLineSite)
      (.operandMismatch tokens.writeLine) = true := by decide +kernel
#print axioms rejects_a_signature_byte_that_changes_a_parameter

theorem rejects_a_heap_offset_with_no_entry :
    rejects dangling lib tokens.consoleRef (.type (.atom runtimeScope "System.Console"))
      (.missingHeap 0 0x7FFF) = true := by decide +kernel
#print axioms rejects_a_heap_offset_with_no_entry

theorem rejects_a_generic_argument_that_differs_from_the_specification :
    rejects own.1 lib tokens.idSpec (.call { idSite with typeArguments := [uint64] })
      (.genericMismatch tokens.idSpec) = true := by decide +kernel
#print axioms rejects_a_generic_argument_that_differs_from_the_specification

/-- `System.Console` as an assembly of version 9 would define it. -/
private def olderConsole : TypeExpr :=
  .atom "System.Runtime, Version=9.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
    "System.Console"

theorem rejects_an_owner_scope_with_another_version :
    rejects own.1 lib tokens.writeLine (.call { writeLineSite with method.owner := olderConsole })
      (.scopeMismatch tokens.writeLine) = true := by decide +kernel
#print axioms rejects_an_owner_scope_with_another_version

theorem rejects_a_field_index_the_metadata_does_not_give :
    rejects own.1 lib tokens.countField
      (.field (.atom ownScope "Program") 1 int32 name!"count" false)
      (.fieldIndexMismatch tokens.countField 1 0) = true := by decide +kernel
#print axioms rejects_a_field_index_the_metadata_does_not_give

/-- The count field's token with the operand naming `total`, the static field after it. -/
theorem rejects_a_field_operand_named_for_another_row :
    rejects own.1 lib tokens.countField
      (.field (.atom ownScope "Program") 0 int32 name!"total" false)
      (.operandMismatch tokens.countField) = true := by decide +kernel
#print axioms rejects_a_field_operand_named_for_another_row

theorem rejects_a_static_field_claimed_as_an_instance_field :
    rejects own.1 lib tokens.totalField
      (.field (.atom ownScope "Program") 1 int32 name!"total" false)
      (.operandMismatch tokens.totalField) = true := by decide +kernel
#print axioms rejects_a_static_field_claimed_as_an_instance_field

/-- The local variable types of the signature at `tokens.localsSignature`. -/
private def localsFail (slice : MetadataSlice) (locals : List TypeExpr) (error : MetadataError) :
    Bool :=
  match (do
    let env := MetadataEnv.ofSlices [← slice.index, ← lib.index] (platform := worldPlatform)
    checkLocals env 0 tokens.localsSignature locals) with
  | .error found => found == error
  | .ok _ => false

theorem accepts_the_locals_the_signature_names :
    (match (do
      let env := MetadataEnv.ofSlices [← own.1.index, ← lib.index] (platform := worldPlatform)
      checkLocals env 0 tokens.localsSignature [uint64]) with
    | .ok _ => true
    | .error _ => false) = true := by decide +kernel
#print axioms accepts_the_locals_the_signature_names

theorem rejects_a_local_of_another_type :
    localsFail own.1 [uint32] (.localMismatch 0) = true ∧
    localsFail own.1 [uint64, uint64] (.localMismatch 1) = true ∧
    localsFail own.1 [] (.localMismatch 0) = true := by decide +kernel
#print axioms rejects_a_local_of_another_type

theorem rejects_a_pinned_local :
    localsFail (mutateBlob own.1 (blobOffset own.1 [0x07, 0x01, 0x0B]) fun _ =>
      [4, 0x07, 0x01, 0x45, 0x0B]) [uint64] (.unsupportedSignature 2 0x45) = true := by
  decide +kernel
#print axioms rejects_a_pinned_local

/-! ## Objects outside a class field -/

/-- The coded `TypeDefOrRef` index of a type reference, as a signature writes it. -/
private def typeRefCoded (token : Nat) : Nat := (token - 0x01000000) * 4 + 1

/-- The modifier's TypeRef names System.Console in a versioned external assembly. -/
private def modifiedLocal (version marker : Nat) : MetadataSlice :=
  let target := mutateRow own.1 0x23000002 fun row => row.set 0 version
  let changed := borrow target tokens.consoleRef tokens.boxRef 0
  mutateBlob changed (blobOffset own.1 [0x07, 0x01, 0x0B]) fun _ =>
    [5, 0x07, 0x01, marker, typeRefCoded tokens.consoleRef, 0x0B]

/-- A flat local name cannot bind the assembly of either kind of custom modifier. -/
theorem rejects_local_modifiers_from_either_assembly :
    [7, 8].all (fun version =>
      localsFail (modifiedLocal version 0x1F) [.atom runtimeScope "System.UInt64 modreq(System.Console)"]
        (.localMismatch 0) &&
      localsFail (modifiedLocal version 0x20) [.atom runtimeScope "System.UInt64 modopt(System.Console)"]
        (.localMismatch 0)) = true := by decide +kernel
#print axioms rejects_local_modifiers_from_either_assembly

private def externalScope (name : String) : String :=
  name ++ ", Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

private def externalValues : PlatformTable := platform_table%
  [⟨Tests.unsignedAssembly name!"Outer", [bytesOf "N", bytesOf "Wrap`1"], .genericValue 1⟩,
   ⟨Tests.unsignedAssembly name!"A", [bytesOf "N", bytesOf "Value"], .valueType⟩,
   ⟨Tests.unsignedAssembly name!"B", [bytesOf "N", bytesOf "Value"], .valueType⟩]

private def externalAggregateRows (reference : String) : Step Nat := do
  let outer ← string "Outer"
  let arg ← string reference
  let ns ← string "N"
  let wrapper ← string "Wrap`1"
  let value ← string "Value"
  let _ ← row Table.assemblyRef [1, 0, 0, 0, 0, 0, outer, 0, 0]
  let _ ← row Table.assemblyRef [1, 0, 0, 0, 0, 0, arg, 0, 0]
  let runtime ← string "System.Runtime"
  let publisher ← blob runtimePublisher
  let _ ← row Table.assemblyRef [11, 0, 0, 0, 0, publisher, runtime, 0, 0]
  modify fun builder => { builder with corlib := 3 }
  let _ ← row Table.typeRef [6, wrapper, ns]
  let _ ← row Table.typeRef [10, value, ns]
  let sig ← blob [7, 1, 0x15, 0x11, 5, 1, 0x11, 9]
  row Table.standAloneSig [sig]

private def externalAggregateLocal (reference argument : String) : Except MetadataError Unit := do
  let (slice, sig) := build (externalAggregateRows reference) (bytesOf "Caller")
  let env := MetadataEnv.ofSlices [← slice.index] (platform := externalValues)
  checkLocals env 0 sig [.aggregate (externalScope "Outer" ++ "::N.Wrap`1<" ++ argument ++ ">") 0]

/-- The IL signatures differ only in the assembly of N.Value inside the external generic. -/
theorem external_aggregate_local_binds_argument_scope :
    let mismatches := fun source name =>
      match externalAggregateLocal source name with
      | .error (.localMismatch 0) => true
      | _ => false
    let a := externalScope "A" ++ "::N.Value"
    let b := externalScope "B" ++ "::N.Value"
    (externalAggregateLocal "A" a).isOk && (externalAggregateLocal "B" b).isOk &&
      mismatches "A" b && mismatches "B" a && mismatches "A" "N.Value" && mismatches "B" "N.Value" := by decide +kernel
#print axioms external_aggregate_local_binds_argument_scope

/-- The own slice with its one local retyped to an array of the signature type `element`. -/
private def arrayLocal (element : List Nat) : MetadataSlice :=
  mutateBlob own.1 (blobOffset own.1 [0x07, 0x01, 0x0B]) fun _ =>
    [element.length + 3, 0x07, 0x01, 0x1D] ++ element

/-- Whether the locals check accepts these local types. -/
private def localsPass (slice : MetadataSlice) (locals : List TypeExpr) : Bool :=
  match (do
    let env := MetadataEnv.ofSlices [← slice.index, ← lib.index] (platform := worldPlatform)
    checkLocals env 0 tokens.localsSignature locals) with
  | .ok _ => true
  | .error _ => false

/-- A type operand names as an object a class of a carried slice or `System.String`, never an
    interface, an external class or `System.Object`, whose lineage no instance records. -/
theorem names_only_carried_classes_and_strings_as_objects :
    passes own.1 lib tokens.boxRef (.type (.object libScope "Lib.Box")) = true ∧
    passes own.1 lib tokens.stringRef (.type (.object runtimeScope "System.String")) = true ∧
    rejects own.1 lib tokens.shapeRef (.type (.object libScope "Lib.IShape"))
      (.operandMismatch tokens.shapeRef) = true ∧
    rejects own.1 lib tokens.consoleRef (.type (.object runtimeScope "System.Console"))
      (.operandMismatch tokens.consoleRef) = true ∧
    rejects own.1 lib tokens.objectRef (.type (.object runtimeScope "System.Object"))
      (.operandMismatch tokens.objectRef) = true := by decide +kernel
#print axioms names_only_carried_classes_and_strings_as_objects

/-- An array of objects holds carried classes or strings: `stelem.ref` decides a store by the
    stored instance's lineage, which never lists an interface or `System.Object`. -/
theorem holds_only_carried_classes_and_strings_in_object_arrays :
    localsPass (arrayLocal [0x12, typeRefCoded tokens.boxRef])
      [.array (.object libScope "Lib.Box")] = true ∧
    localsPass (arrayLocal [0x0E]) [.array (.object runtimeScope "System.String")] = true ∧
    localsFail (arrayLocal [0x12, typeRefCoded tokens.shapeRef])
      [.array (.object libScope "Lib.IShape")] (.localMismatch 0) = true ∧
    localsFail (arrayLocal [0x12, typeRefCoded tokens.objectRef])
      [.array (.object runtimeScope "System.Object")] (.localMismatch 0) = true ∧
    localsFail (arrayLocal [0x12, typeRefCoded tokens.consoleRef])
      [.array (.object runtimeScope "System.Console")] (.localMismatch 0) = true := by
  decide +kernel
#print axioms holds_only_carried_classes_and_strings_in_object_arrays

/-- Metadata binding refuses claims that give the instantiated member types as its declaration. -/
example : rejects own.1 lib tokens.idSpec
    (.call { idSite with declared.returnType := uint32 }) (.operandMismatch tokens.idSpec) := by
  decide +kernel
example : rejects own.1 lib tokens.idSpec
    (.call { idSite with declared.parameters := [uint32] }) (.operandMismatch tokens.idSpec) := by
  decide +kernel
example : rejects own.1 lib tokens.writeLine
    (.call { writeLineSite with declared.convention := 0x40 }) (.operandMismatch tokens.writeLine)
    := by decide +kernel

/-- `System.Console.Id<T>` as a call site instantiated with `argument`. -/
private def idWith (argument : TypeExpr) : CallSite :=
  let method := { idSite.method with
    returnType := argument, parameters := [argument], methodArguments := [argument] }
  { idSite with method := method, typeArguments := [argument] }

/-- The own slice with `Id` instantiated with the class the reference `token` names. -/
private def idInstantiatedWith (token : Nat) : MetadataSlice :=
  mutateBlob own.1 (blobOffset own.1 [0x0A, 0x01, 0x09]) fun _ =>
    [4, 0x0A, 0x01, 0x12, typeRefCoded token]

/-- A generic argument named as an object is a carried class, so substituting it into an
    element position never forms an array of interfaces or of `System.Object`. -/
theorem passes_only_carried_classes_as_object_arguments :
    passes (idInstantiatedWith tokens.boxRef) lib tokens.idSpec
      (.call (idWith (.object libScope "Lib.Box"))) = true ∧
    rejects (idInstantiatedWith tokens.shapeRef) lib tokens.idSpec
      (.call (idWith (.object libScope "Lib.IShape"))) (.genericMismatch tokens.idSpec) = true ∧
    rejects (idInstantiatedWith tokens.objectRef) lib tokens.idSpec
      (.call (idWith (.object runtimeScope "System.Object")))
      (.genericMismatch tokens.idSpec) = true := by decide +kernel
#print axioms passes_only_carried_classes_as_object_arguments

/-- The own slice with the fields `count`, `total` and `second` retyped to `held`. -/
private def fieldsHolding (held : List Nat) : MetadataSlice :=
  mutateBlob own.1 (blobOffset own.1 [0x06, 0x08]) fun _ => [held.length + 1, 0x06] ++ held

/-- The instance field `count` of the class `T.Program`, holding `held`. -/
private def countHolding (held : TypeExpr) : RawOperand :=
  .field (.object ownScope "Program") 0 held name!"count" false

/-- A class instance field keeps a reference it never reads through, so it may hold an
    interface or an external class as an object; an array it holds still holds carried classes,
    and a static field holds no such reference. -/
theorem holds_opaque_objects_only_in_class_instance_fields :
    passes (fieldsHolding [0x12, typeRefCoded tokens.shapeRef]) lib tokens.countField
      (countHolding (.object libScope "Lib.IShape")) = true ∧
    passes (fieldsHolding [0x12, typeRefCoded tokens.consoleRef]) lib tokens.countField
      (countHolding (.object runtimeScope "System.Console")) = true ∧
    rejects (fieldsHolding [0x1D, 0x12, typeRefCoded tokens.objectRef]) lib tokens.countField
      (countHolding (.array (.object runtimeScope "System.Object")))
      (.operandMismatch tokens.countField) = true ∧
    rejects (fieldsHolding [0x12, typeRefCoded tokens.shapeRef]) lib tokens.totalField
      (.field (.atom ownScope "Program") 1 (.object libScope "Lib.IShape") name!"total" true)
      (.operandMismatch tokens.totalField) = true := by decide +kernel
#print axioms holds_opaque_objects_only_in_class_instance_fields

/-! ## Rows and heap entries the decoder refuses -/

theorem rejects_a_row_of_the_wrong_length :
    rejects (mutateRow own.1 tokens.consoleRef fun bytes => bytes.take 5) lib tokens.consoleRef
      (.type (.atom runtimeScope "System.Console")) (.rowLength tokens.consoleRef 6 5) = true := by
  decide +kernel
#print axioms rejects_a_row_of_the_wrong_length

theorem rejects_row_zero :
    rejects own.1 lib 0x01000000 (.type (.atom runtimeScope "System.Console"))
      (.tokenOutOfScope 0x01000000) = true := by decide +kernel
#print axioms rejects_row_zero

theorem rejects_a_duplicate_token :
    (match { own.1 with rows := own.1.rows ++ own.1.rows.take 1 }.index with
      | .error found => found == .duplicateEntry (own.1.rows.headD (0, [])).1
      | .ok _ => false) = true := by decide +kernel
#print axioms rejects_a_duplicate_token

theorem rejects_a_wrong_user_string_terminal_byte :
    rejects { own.1 with userStrings := own.1.userStrings.map fun (offset, bytes) =>
        (offset, bytes.set (bytes.length - 1) 1) } lib tokens.hello (.text "hi")
      (.malformedUserString (tokens.hello - 0x70000000)) = true := by decide +kernel
#print axioms rejects_a_wrong_user_string_terminal_byte

theorem rejects_another_string_than_the_user_string :
    rejects own.1 lib tokens.hello (.text "ho") (.operandMismatch tokens.hello) = true := by
  decide +kernel
#print axioms rejects_another_string_than_the_user_string

/-! ## Method names -/

/-- A call site's typed fields read its method, so they keep the values the fixtures state. -/
theorem call_site_fields_read_the_method :
    writeLineSite.declaringType = .atom runtimeScope "System.Console" ∧
      writeLineSite.hasThis = false ∧ writeLineSite.returnType = .void ∧
      writeLineSite.parameterTypes = [int32] ∧ writeLineSite.method.argumentCount = 1 ∧
    getSite.declaringType = .atom libScope "Lib.Box" ∧ getSite.returnType = int32 ∧
      getSite.parameterTypes = [] ∧
    idSite.method.methodArguments = idSite.typeArguments ∧ idSite.method.genericArity = 1 := by
  decide
#print axioms call_site_fields_read_the_method

/-- The method a call operand names is the row's name read as a metadata name; a site whose
    display name still matches the row but whose typed name does not is refused. -/
theorem rejects_a_method_name_other_than_the_row :
    rejects own.1 lib tokens.writeLine
      (.call { writeLineSite with method.name := name!"WriteLin" })
      (.operandMismatch tokens.writeLine) = true ∧
    rejects own.1 lib tokens.getRef (.call { getSite with method.name := name!"Set" })
      (.operandMismatch tokens.getRef) = true ∧
    rejects own.1 lib tokens.idSpec (.call { idSite with method.name := name!"Ids" })
      (.operandMismatch tokens.idSpec) = true := by decide +kernel
#print axioms rejects_a_method_name_other_than_the_row

/-- A typed name whose code spells no byte list, the empty code or one whose leading digit is
    not 1, names no row. -/
theorem rejects_a_method_name_that_spells_no_bytes :
    rejects own.1 lib tokens.writeLine (.call { writeLineSite with method.name := ⟨0⟩ })
      (.operandMismatch tokens.writeLine) = true ∧
    rejects own.1 lib tokens.writeLine (.call { writeLineSite with method.name := ⟨767⟩ })
      (.operandMismatch tokens.writeLine) = true := by decide +kernel
#print axioms rejects_a_method_name_that_spells_no_bytes

/-- A call's typed method states the row's generic arity and the method arguments the site
    instantiates; a site that disagrees on either names another method. -/
theorem rejects_a_method_with_another_arity_or_arguments :
    rejects own.1 lib tokens.idSpec (.call { idSite with method.genericArity := 0 })
      (.genericMismatch tokens.idSpec) = true ∧
    rejects own.1 lib tokens.idSpec (.call { idSite with method.methodArguments := [int32] })
      (.genericMismatch tokens.idSpec) = true := by decide +kernel
#print axioms rejects_a_method_with_another_arity_or_arguments

/-- A string heap entry that holds a value above a byte is refused when the slice is indexed,
    so every row name the call check reads is a metadata name. -/
theorem rejects_a_row_name_that_is_not_bytes :
    rejects { own.1 with strings := own.1.strings.map fun (offset, bytes) =>
        (offset, if bytes == bytesOf "WriteLine" ++ [0] then 256 :: bytes else bytes) } lib
      tokens.writeLine (.call writeLineSite) .invalidByte = true := by decide +kernel
#print axioms rejects_a_row_name_that_is_not_bytes

/-! ## Calls into a pinned assembly -/

theorem rejects_a_pinned_callee_with_another_name :
    rejects (borrow own.1 tokens.getRef tokens.writeLine 2) lib
      tokens.getRef (.call { getSite with name := "WriteLine", method.name := name!"WriteLine" })
      (.unresolvedMember tokens.getRef) = true := by decide +kernel
#print axioms rejects_a_pinned_callee_with_another_name

theorem rejects_a_pinned_callee_with_no_link :
    rejects { own.1 with links := own.1.links.filter (·.source != tokens.getRef) } lib
      tokens.getRef (.call getSite) (.unresolvedMember tokens.getRef) = true := by decide +kernel
#print axioms rejects_a_pinned_callee_with_no_link

theorem rejects_a_managed_target_other_than_the_definition :
    rejects own.1 lib tokens.getRef (.call { getSite with target := .managed 0x06000002 })
      (.operandMismatch tokens.getRef) = true := by decide +kernel
#print axioms rejects_a_managed_target_other_than_the_definition

/-- The identity of `WriteLine(long)`, which the `WriteLine(int)` token does not name. -/
private def longWriteLine : MethodId :=
  .external (runtimeScope ++ "::System.Void System.Console::WriteLine(System.Int64)")

theorem rejects_an_external_identity_other_than_the_member :
    rejects own.1 lib tokens.writeLine (.call { writeLineSite with target := longWriteLine })
      (.operandMismatch tokens.writeLine) = true := by decide +kernel
#print axioms rejects_an_external_identity_other_than_the_member

/-- `Lib.Box` defined with namespace `Lib` and name `Box`, as the reference spells it, and the
    same type defined with an empty namespace and the name `Lib.Box`: both join to `Lib.Box`. -/
private def libWithJoinedName : MetadataSlice :=
  let joined : ByteEntry := (0x4000, bytesOf "Lib.Box" ++ [0])
  { mutateRow lib (tokenOf Table.typeDef 2) (fun bytes =>
      bytes.take 4 ++ [0x00, 0x40, 0x00, 0x00] ++ bytes.drop 8) with
    strings := lib.strings ++ [joined] }

theorem rejects_a_definition_whose_namespace_and_name_only_join_to_the_reference :
    rejects own.1 libWithJoinedName tokens.getRef (.call getSite)
      (.operandMismatch tokens.boxRef) = true := by decide +kernel
#print axioms rejects_a_definition_whose_namespace_and_name_only_join_to_the_reference

/-- Whether checking an operand against the own slice alone fails with exactly this error, when
    `Lib` is pinned: its slice is not carried. -/
private def rejectsWithoutLibSlice (token : Nat) (operand : RawOperand) (error : MetadataError) :
    Bool :=
  match (do
    let env := MetadataEnv.ofSlices [← own.1.index] (platform := worldPlatform)
      (indexPinNames [libAssembly])
    checkEntry env 0 token operand) with
  | .error found => found == error
  | .ok _ => false

/-- A reference into a pinned assembly whose slice is left out is refused, not read as a platform
    type or call. -/
theorem rejects_a_pinned_assembly_whose_slice_is_missing :
    rejectsWithoutLibSlice tokens.boxRef (.type (.atom libScope "Lib.Box"))
      (.missingSlice tokens.boxRef) = true ∧
    rejectsWithoutLibSlice tokens.getRef (.call getSite) (.missingSlice tokens.boxRef) = true := by
  decide +kernel
#print axioms rejects_a_pinned_assembly_whose_slice_is_missing

/-- The `Lib` slice with a wrong number for its core-library reference. -/
private def libWithoutCorlib : MetadataSlice := { lib with corlib := 0 }

/-- The struct is a value type from its base reference alone, whatever `corlib` says, so a claim
    that it is a class is refused with or without the number. -/
theorem decides_a_struct_without_the_corlib_number :
    passes own.1 lib tokens.pairRef (.type (.atom libScope "Lib.Pair")) = true ∧
    passes own.1 libWithoutCorlib tokens.pairRef (.type (.atom libScope "Lib.Pair")) = true ∧
    rejects own.1 lib tokens.pairRef (.type (.object libScope "Lib.Pair"))
      (.operandMismatch tokens.pairRef) = true ∧
    rejects own.1 libWithoutCorlib tokens.pairRef (.type (.object libScope "Lib.Pair"))
      (.operandMismatch tokens.pairRef) = true := by decide +kernel
#print axioms decides_a_struct_without_the_corlib_number

/-- Whether a physical AssemblyRef's name, culture and token identify a core-library family. -/
private def coreReference (family culture : String) (publisher : List Nat) : Bool :=
  let (slice, reference) := build (do
    let name ← string family
    let language ← string culture
    let key ← blob publisher
    row Table.assemblyRef [4, 0, 0, 0, 0, key, name, language, 0]) (bytesOf "T")
  (slice.index >>= (·.coreAssemblyRef reference)).toOption == some true

/-- Each core-library family retains its own publisher. An unsigned reference, a different
    culture or another platform publisher cannot stand in for System.Runtime. -/
theorem core_library_publishers :
    let ecma := [0xb7, 0x7a, 0x5c, 0x56, 0x19, 0x34, 0xe0, 0x89]
    coreReference "System.Runtime" "" runtimePublisher = true ∧
    coreReference "mscorlib" "" ecma = true ∧
    coreReference "netstandard" "" [0xcc, 0x7b, 0x13, 0xff, 0xcd, 0x2d, 0xdd, 0x51] = true ∧
    coreReference "System.Private.CoreLib" "" [0x7c, 0xec, 0x85, 0xd7, 0xbe, 0xa7, 0x79, 0x8e] =
      true ∧
    coreReference "System.Runtime" "" ecma = false ∧ coreReference "System.Runtime" "" [] = false ∧
    coreReference "System.Runtime" "fr" runtimePublisher = false := by decide +kernel
#print axioms core_library_publishers

/-- Changing the publisher of System.Runtime leaves the type and assembly names intact. -/
private def libWithOtherPublisher : MetadataSlice :=
  mutateBlob lib (blobOffset lib runtimePublisher) fun _ => [8, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Resolve the value-type marker of the caller's signature through its link to Lib.Pair. -/
private def pairSignatureKind (slice : MetadataSlice) :
    Except MetadataError Extraction.TypeKind := do
  let env := MetadataEnv.ofSlices [← own.1.index, ← slice.index] (platform := worldPlatform)
  return (← namedOf env 0 tokens.pairRef (some true)).kind

/-- A different publisher's System.ValueType cannot satisfy a value-type signature or serve
    as the slice's primitive-type assembly. -/
theorem rejects_another_publishers_value_type :
    pairSignatureKind lib = .ok .valueType ∧
    pairSignatureKind libWithOtherPublisher = .error (.operandMismatch tokens.pairRef) ∧
    (libWithOtherPublisher.index >>= MetadataIndex.corlibIdentity) =
      .error (.unsupportedAssemblyRef 0x23000001) := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms rejects_another_publishers_value_type

/-- A field of a struct in a pinned assembly is read from that assembly's slice: without the
    slice it is refused, not taken for a platform field. -/
theorem rejects_a_pinned_struct_field_whose_slice_is_missing :
    passes own.1 lib tokens.firstRef (.field (.atom libScope "Lib.Pair") 0 int32 name!"first" false)
      = true ∧
    rejectsWithoutLibSlice tokens.firstRef
      (.field (.atom libScope "Lib.Pair") 0 int32 name!"first" false)
      (.missingSlice tokens.pairRef) = true := by decide +kernel
#print axioms rejects_a_pinned_struct_field_whose_slice_is_missing

/-- `Lib.Pair` as the extractor names a struct owner, by identity and layout index. -/
private def pairOwner : TypeExpr := .aggregate (libScope ++ "::Lib.Pair") 0

/-- A field of `Lib.Pair` as an operand claims it: owner, index, held type and name. -/
private def pairFieldOf (owner : TypeExpr) (index : Nat) (held : TypeExpr) (name : MetadataName) :
    RawOperand :=
  .field owner index held name false

/-- A struct field operand states its owner as a value type, its index among the owner's
    instance fields, its held type and its name, and the token refuses each other claim: a class
    owner's index walks the struct's bases to `System.ValueType`, which no class chain has, and
    a class field's token refuses an owner named as a struct. -/
theorem checks_each_claim_of_a_struct_field :
    passes own.1 lib tokens.firstRef (pairFieldOf pairOwner 0 int32 name!"first") = true ∧
    rejects own.1 lib tokens.firstRef (pairFieldOf pairOwner 1 int32 name!"first")
      (.fieldIndexMismatch tokens.firstRef 1 0) = true ∧
    rejects own.1 lib tokens.firstRef
      (pairFieldOf (.object libScope "Lib.Pair") 0 int32 name!"first")
      (.unsupportedBase (tokenOf Table.typeDef 3)) = true ∧
    rejects own.1 lib tokens.firstRef
      (pairFieldOf (.aggregate (libScope ++ "::Lib.Box") 0) 0 int32 name!"first")
      (.operandMismatch tokens.firstRef) = true ∧
    rejects own.1 lib tokens.countField
      (pairFieldOf (.aggregate (ownScope ++ "::Program") 0) 0 int32 name!"count")
      (.operandMismatch tokens.countField) = true ∧
    rejects own.1 lib tokens.firstRef (pairFieldOf pairOwner 0 uint32 name!"first")
      (.operandMismatch tokens.firstRef) = true ∧
    rejects own.1 lib tokens.firstRef (pairFieldOf pairOwner 0 int32 name!"second")
      (.operandMismatch tokens.firstRef) = true := by decide +kernel
#print axioms checks_each_claim_of_a_struct_field

/-- `T` with the generic struct `Pair`1` and its instance field `first : !0`, referenced
    through `Pair<int>` and through a specification that gives `Pair` two arguments. -/
private def genericPairWorld : Step (Nat × Nat) := do
  let runtimeName ← string "System.Runtime"
  let publicKeyToken ← blob runtimePublisher
  let _ ← row Table.assemblyRef [11, 0, 0, 0, 0, publicKeyToken, runtimeName, 0, 0]
  modify fun builder => { builder with corlib := 1 }
  let valueTypeName ← string "ValueType"
  let systemName ← string "System"
  let valueTypeRef ← row Table.typeRef [1 * 4 + 2, valueTypeName, systemName]
  let moduleName ← string "<Module>"
  let _ ← row Table.typeDef [0, moduleName, 0, 0, 1, 1]
  let pairName ← string "Pair`1"
  let pair ← row Table.typeDef [0x101, pairName, 0, (valueTypeRef - 0x01000000) * 4 + 1, 1, 1]
  let parameterName ← string "T"
  let _ ← row Table.genericParam [0, 0, (pair - 0x02000000) * 2, parameterName]
  let firstName ← string "first"
  let parameterField ← blob [0x06, 0x13, 0x00]
  let first ← row Table.field [0x0006, firstName, parameterField]
  link linkDeclaring first 0 pair
  let pairCoded := (pair - 0x02000000) * 4
  let oneBlob ← blob [0x15, 0x11, pairCoded, 1, 0x08]
  let twoBlob ← blob [0x15, 0x11, pairCoded, 2, 0x08, 0x08]
  let oneSpec ← row Table.typeSpec [oneBlob]
  let twoSpec ← row Table.typeSpec [twoBlob]
  let oneRef ← row Table.memberRef [(oneSpec - 0x1B000000) * 8 + 4, firstName, parameterField]
  let twoRef ← row Table.memberRef [(twoSpec - 0x1B000000) * 8 + 4, firstName, parameterField]
  link linkDefinition oneRef 0 first
  link linkDefinition twoRef 0 first
  pure (oneRef, twoRef)

/-- The generic pair's slice, with its references through `Pair<int>` and `Pair<int, int>`. -/
private def genericPair : MetadataSlice × Nat × Nat :=
  build genericPairWorld (bytesOf "T")

/-- `Pair<int>` as the extractor names it, and as an owner with one argument too many. -/
private def pairOfInt : TypeExpr :=
  .aggregate (ownScope ++ "::Pair`1<" ++ runtimeScope ++ "::System.Int32>") 0
private def pairOfTwoInts : TypeExpr := .aggregate
  (ownScope ++ "::Pair`1<" ++ runtimeScope ++ "::System.Int32," ++ runtimeScope ++
    "::System.Int32>") 0

/-- A field of a generic struct instance holds its argument, read through the instance; a
    specification giving the one-parameter definition two arguments is refused by its arity, and
    an owner claiming two arguments names no instance the token gives. -/
theorem checks_the_arity_of_a_generic_struct_owner :
    passes genericPair.1 lib genericPair.2.1 (.field pairOfInt 0 int32 name!"first" false) =
      true ∧
    rejects genericPair.1 lib genericPair.2.2 (.field pairOfInt 0 int32 name!"first" false)
      (.genericMismatch 0x02000002) = true ∧
    rejects genericPair.1 lib genericPair.2.1 (.field pairOfTwoInts 0 int32 name!"first" false)
      (.operandMismatch genericPair.2.1) = true := by decide +kernel
#print axioms checks_the_arity_of_a_generic_struct_owner

/-- A void signature needs no core-library scope, and its struct owner still binds as a value
    type. An Int32 result needs the callee's primitive scope. -/
theorem rejects_a_call_naming_a_struct_as_a_class_without_the_corlib_number :
    let asVoid := fun slice => mutateBlob slice (blobOffset slice [0, 0, 8]) fun _ => [3, 0, 0, 1]
    let call := { sumSite with
      declared.returnType := .void, method.returnType := .void, returnsValue := false }
    passes own.1 lib tokens.sumRef (.call sumSite) = true ∧
    rejects own.1 libWithoutCorlib tokens.sumRef (.call sumSite)
      (.operandMismatch tokens.sumRef) = true ∧
    passes (asVoid own.1) (asVoid libWithoutCorlib) tokens.sumRef (.call call) = true ∧
    rejects (asVoid own.1) (asVoid libWithoutCorlib) tokens.sumRef
      (.call { call with method.owner := .object libScope "Lib.Pair" })
      (.operandMismatch tokens.sumRef) = true := by decide +kernel
#print axioms rejects_a_call_naming_a_struct_as_a_class_without_the_corlib_number

/-- `Lib.Holder<!!0>` and `System.Lazy<!!0>` as a method with one type parameter names them. -/
private def holderOfMethodParameter : TypeExpr :=
  .apply (.objectConstructor libScope "Lib.Holder`1") (.parameter 0)
private def lazyOfMethodParameter : TypeExpr :=
  .apply (.objectConstructor runtimeScope "System.Lazy`1") (.parameter 0)

/-- Each closed instantiation of a generic class has its own statics, so a static field named
    through `Lib.Holder<!!0>`, whose row a pinned slice carries, or through the external
    `System.Lazy<!!0>` is refused whatever type the operand gives it. -/
theorem refuses_a_static_field_of_an_instantiation :
    rejects own.1 lib tokens.holderValueRef
      (.field holderOfMethodParameter 0 (.parameter 0) name!"Value" true)
      (.instantiatedStaticField tokens.holderValueRef) (arity := 1) = true ∧
    rejects own.1 lib tokens.holderValueRef
      (.field holderOfMethodParameter 0 (.parameter 1) name!"Value" true)
      (.instantiatedStaticField tokens.holderValueRef) (arity := 1) = true ∧
    rejects own.1 lib tokens.lazyValueRef
      (.field lazyOfMethodParameter 0 (.parameter 0) name!"Value" true)
      (.instantiatedStaticField tokens.lazyValueRef) (arity := 1) = true ∧
    rejects own.1 lib tokens.lazyValueRef
      (.field lazyOfMethodParameter 0 (.parameter 1) name!"Value" true)
      (.instantiatedStaticField tokens.lazyValueRef) (arity := 1) = true := by decide +kernel
#print axioms refuses_a_static_field_of_an_instantiation

/-- No carried field list gives the position of an instance field of an unpinned type, so
    `System.Lazy<!!0>.Value` read as an instance field is refused at every index, and an operand
    named for another member is refused by its name first. -/
theorem rejects_an_unpinned_instance_field :
    rejects own.1 lib tokens.lazyValueRef
      (.field lazyOfMethodParameter 0 (.parameter 0) name!"Value" false)
      (.unboundInstanceField tokens.lazyValueRef) (arity := 1) = true ∧
    rejects own.1 lib tokens.lazyValueRef
      (.field lazyOfMethodParameter 1 (.parameter 0) name!"Value" false)
      (.unboundInstanceField tokens.lazyValueRef) (arity := 1) = true ∧
    rejects own.1 lib tokens.lazyValueRef
      (.field lazyOfMethodParameter 0 (.parameter 0) name!"Other" false)
      (.operandMismatch tokens.lazyValueRef) (arity := 1) = true := by decide +kernel
#print axioms rejects_an_unpinned_instance_field

/-- The own slice without the row of the static field between the first and the second instance
    field of `Program`: the carried rows of the type leave a gap. -/
private def ownWithGappedFields : MetadataSlice :=
  { own.1 with rows := own.1.rows.filter (·.1 != tokens.totalField) }

/-- The second instance field is index 1 when every field row before it is carried. A prefix of
    the type's fields with a missing row cannot give the count of instance fields before it, so
    the token is refused, not read as the first instance field. -/
theorem rejects_a_field_after_a_gap_in_the_carried_field_rows :
    passes own.1 lib tokens.secondField
      (.field (.atom ownScope "Program") 1 int32 name!"second" false) = true ∧
    rejects ownWithGappedFields lib tokens.secondField
      (.field (.atom ownScope "Program") 1 int32 name!"second" false)
      (.unresolvedMember tokens.secondField) = true := by decide +kernel
#print axioms rejects_a_field_after_a_gap_in_the_carried_field_rows

/-! ## The use of a token -/

theorem rejects_a_field_access_that_disagrees_with_the_field_row :
    checkSite 0x7E { staticField := some false } countOperand = false ∧
    checkSite 0x7B { staticField := some true } countOperand = false ∧
    checkSite 0x7B { staticField := some false } countOperand = true ∧
    checkSite 0x7B { staticField := some false }
      (.field (.atom ownScope "Program") 0 int32 name!"count" false) = true ∧
    checkSite 0x7E { staticField := some true }
      (.field (.atom ownScope "Program") 1 int32 name!"total" true) = true := by decide +kernel
#print axioms rejects_a_field_access_that_disagrees_with_the_field_row

/-! ## The method definition -/

/-- A method whose receiver kind follows its declaring type's metadata. -/
private def receiverWorld (baseName : String) (interfaceType hasThis generic : Bool) :
    Step Nat := do
  let runtime ← string "System.Runtime"
  let system ← string "System"
  let parentName ← string baseName
  let program ← string "Program"
  let methodName ← string "Run"
  let publicKeyToken ← blob runtimePublisher
  let _ ← row Table.assemblyRef [11, 0, 0, 0, 0, publicKeyToken, runtime, 0, 0]
  modify fun builder => { builder with corlib := 1 }
  let parent ← row Table.typeRef [6, parentName, system]
  let base := if interfaceType then 0 else (parent - 0x01000000) * 4 + 1
  let owner <- row Table.typeDef [if interfaceType then 0x21 else 1, program, 0, base, 1, 1]
  if baseName == "Enum" then
    let valueName ← string "value__"
    let fieldSignature ← blob [0x06, 0x08]
    let field ← row Table.field [0x606, valueName, fieldSignature]
    link linkDeclaring field 0 owner
  if generic then
    let parameterName ← string "T"
    let parameter ← row Table.genericParam [0, 0, (owner - 0x02000000) * 2, parameterName]
    link linkGenericParams owner 0 parameter
  let signature ← blob [if hasThis then 0x20 else 0, 0, 1]
  let method ← row Table.methodDef
    [0, 0, if hasThis then 0x86 else 0x96, methodName, signature, 1]
  link linkDeclaring method 0 owner
  pure method

/-- The complete receiver binding result for a metadata owner and a claimed receiver bit. -/
private def receiverIdentity (baseName : String) (interfaceType hasThis objectReceiver : Bool)
    (generic : Bool := false) (omitLink omitParameters : Bool := false)
    (argument : InstanceArgument := .primitive 8) (claimed : TypeExpr := int32)
    (platform := worldPlatform) :
    Except MetadataError MethodNames := do
  let fixture := build (receiverWorld baseName interfaceType hasThis generic)
    (bytesOf "T")
  let method : RawMethod :=
    { token := fixture.2, owner := ownScope ++ "::Program", hasThis := hasThis,
      explicitThis := false, callingConvention := 0, attributes := if hasThis then 0x86 else 0x96,
      implementation := 0, returnType := .void, parameters := [], locals := [],
      initLocals := false, maxStack := 8, genericParameters := [], code := [],
      ownerParameters := if generic && !omitParameters then [{ flags := 0, types := [] }] else [],
      receiverClass := if objectReceiver then
        some (.object ownScope ⟨[⟨name!"", name!"Program"⟩]⟩) else none }
  let metadata := if omitLink then
      { fixture.1 with links := fixture.1.links.filter (·.kind != linkGenericParams) }
    else fixture.1
  let env := MetadataEnv.ofSlices [← metadata.index, ← lib.index] (platform := platform)
    (exactPins := indexPins [ownAssembly, libAssembly])
  methodIdentityValid env method (if generic && !omitParameters then [argument] else [])
    (if generic && !omitParameters then [claimed] else [])

/-- Carried owner parameters remain binding when their optional link is absent. -/
theorem binds_generic_owner_without_link :
    (receiverIdentity "Object" false false false true true false).isOk = true ∧
    (receiverIdentity "Object" false false false true true true).isOk = false := by
  decide +kernel
/-- info: 'Tests.MetadataBinding.binds_generic_owner_without_link' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs in
#print axioms binds_generic_owner_without_link

/-- The carried class admits object storage. The carried interface refuses that same storage. -/
theorem instantiates_owners_with_only_carried_classes_as_objects :
    (receiverIdentity "Object" false false false true
      (argument := .named (.definition libAssembly 0x02000002))
      (claimed := .object libScope "Lib.Box")).isOk = true ∧
    (receiverIdentity "Object" false false false true
      (argument := .named (.definition libAssembly 0x02000005))
      (claimed := .object libScope "Lib.IShape")).isOk = false := by
  decide +kernel
#print axioms instantiates_owners_with_only_carried_classes_as_objects

/-- A closed owner argument names a platform enum with the storage its entry supplies. -/
theorem binds_closed_enum_argument :
    (receiverIdentity "Object" false false false true
      (argument := .named (.platform runtimeAssembly [systemNamespace, bytesOf "DayOfWeek"]))
      (claimed := .enum (Tests.enumIdentity "System.DayOfWeek" runtimeAssembly) .signed32)
      (platform := platform_table%
        [runtimeType "Object" .objectRoot, runtimeType "DayOfWeek" (.enumType 8)])).isOk =
      true := by decide +kernel
#print axioms binds_closed_enum_argument

/-- A parameter table whose entries give a parameter number and its coded owner. -/
private def parameterWorld (parameters : List (Nat × Nat)) : MetadataSlice :=
  (build (parameters.mapM fun (number, owner) =>
    row Table.genericParam [number, 0, owner, 0]) (bytesOf "T")).1

/-- Read the first type's parameters after changing the carried rows or their optional link. -/
private def parameterResult (parameters : List (Nat × Nat))
    (linkTarget : Option (Nat × Nat) := none) (omitted : List Nat := []) :
    Except MetadataError (List GenericParamRow) := do
  let metadata := parameterWorld parameters
  let metadata := { metadata with
    rows := metadata.rows.filter fun (token, _) => !omitted.contains (tokenRow token)
    links := match linkTarget with
      | none => []
      | some (position, target) => [⟨linkGenericParams, 0x02000001, position, target⟩] }
  let index := metadata.indexWith (← metadata.tables) ownAssembly
  index.genericParameters 0 0x02000001

/-- Generic owners accept complete zero-based runs and reject conflicting or incomplete rows. -/
theorem checks_all_carried_generic_parameters :
    (parameterResult []).isOk = true ∧
    (parameterResult [(0, 2), (1, 2), (0, 4)]).isOk = true ∧
    (parameterResult [(0, 3), (0, 2)]).isOk = true ∧
    (parameterResult [(0, 2)] (some (0, 0x2A000001))).isOk = true ∧
    (parameterResult [(0, 2)] (some (1, 0x2A000001))).isOk = false ∧
    (parameterResult [(0, 2), (0, 4)] (some (0, 0x2A000002))).isOk = false ∧
    (parameterResult [(0, 4)] (some (0, 0x2A000001))).isOk = false ∧
    (parameterResult [(0, 2), (1, 2)] (some (0, 0x2A000002))).isOk = false ∧
    (parameterResult [(0, 2), (1, 2)] none [1]).isOk = false ∧
    (parameterResult [(0, 2), (1, 2)] none [2]).isOk = false ∧
    (parameterResult [(0, 2), (0, 4), (1, 2)]).isOk = false ∧
    (parameterResult [(0, 2), (2, 2)]).isOk = false := by decide +kernel
/-- info: 'Tests.MetadataBinding.checks_all_carried_generic_parameters' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs in
#print axioms checks_all_carried_generic_parameters

/-- An owner's parameter count over parameter rows given as a number and a coded owner, with
    the rows at `omitted` left out; with `absentOnly`, only the check that no row names it, and
    with `declared`, as a method whose signature declares that many. -/
private def ownerResult (parameters : List (Nat × Nat)) (owner : Nat) (omitted : List Nat := [])
    (absentOnly := false) (declared : Option Nat := none) : Option Nat :=
  match (do
    let metadata := parameterWorld parameters
    let metadata := { metadata with
      rows := metadata.rows.filter fun (token, _) =>
        !(metadataTableOf token == Table.genericParam && omitted.contains (tokenRow token)) }
    let index := metadata.indexWith (← metadata.tables) ownAssembly
    if absentOnly then do index.noGenericParameters owner; pure 0
    else match declared with
      | some count => do pure (← index.methodGenericParameters 0 owner count).length
      | none => do pure (← index.genericParameters 0 owner).length) with
  | .ok count => some count
  | .error _ => none

/-- `TypeDef 2` (coded 4) and `MethodDef 2` (coded 5) as owners. -/
private def typeTwo : Nat := 0x02000002
private def methodTwo : Nat := 0x06000002

/-- An owner with no carried parameter has none only where its neighbours show it: the first
    carried row above its coded value is row 1 or follows a carried row below it, or the last
    row lies below it, or the table is empty. Coded values order a `TypeDef` before the
    `MethodDef` of the same row number. -/
theorem checks_absent_generic_parameters_by_neighbours :
    ownerResult [] typeTwo = some 0 ∧
    ownerResult [(0, 6)] typeTwo = some 0 ∧
    ownerResult [(0, 2)] typeTwo = some 0 ∧
    ownerResult [(0, 2)] typeTwo [1] = none ∧
    ownerResult [(0, 2), (0, 6)] typeTwo = some 0 ∧
    ownerResult [(0, 2), (0, 6)] typeTwo [1] = none ∧
    ownerResult [(0, 2), (0, 3), (0, 6)] typeTwo [2] = none ∧
    ownerResult [(0, 4), (0, 6)] typeTwo (absentOnly := true) = none ∧
    ownerResult [(0, 4)] typeTwo (absentOnly := true) = none ∧
    ownerResult [(0, 5)] typeTwo = some 0 ∧ ownerResult [(0, 5)] methodTwo = some 1 ∧
    ownerResult [(0, 4)] methodTwo = some 0 ∧ ownerResult [(0, 4)] typeTwo = some 1 ∧
    ownerResult [(0, 4), (0, 5)] typeTwo [1] = none ∧
    ownerResult [(0, 2), (0, 4), (0, 6)] typeTwo [2] = none := by decide +kernel
#print axioms checks_absent_generic_parameters_by_neighbours

/-- A method whose signature declares no generic parameters has none without neighbours, while
    a run carried for it is still read; one that declares parameters keeps the neighbour rule. -/
theorem reads_an_undeclared_method_run_from_its_signature :
    ownerResult [(0, 2), (0, 6)] methodTwo [1] (declared := some 0) = some 0 ∧
    ownerResult [(0, 2), (0, 6)] methodTwo [1] = none ∧
    ownerResult [(0, 2), (0, 6)] methodTwo [1] (declared := some 1) = none ∧
    ownerResult [(0, 5)] methodTwo (declared := some 0) = some 1 ∧
    ownerResult [(0, 5), (0, 6)] methodTwo (declared := some 1) = some 1 := by decide +kernel
#print axioms reads_an_undeclared_method_run_from_its_signature

/-- A slice with the generic class `Holder`1` and the class `Plain`, each declaring one static
    `int`; gives the tokens of `Holder`, its field, `Plain` and its field. -/
private def arityWorld : Step (Nat × Nat × Nat × Nat) := do
  let runtimeName ← string "System.Runtime"
  let publicKeyToken ← blob runtimePublisher
  let _ ← row Table.assemblyRef [11, 0, 0, 0, 0, publicKeyToken, runtimeName, 0, 0]
  modify fun builder => { builder with corlib := 1 }
  let objectName ← string "Object"
  let systemName ← string "System"
  let _ ← row Table.typeRef [1 * 4 + 2, objectName, systemName]
  let moduleName ← string "<Module>"
  let _ ← row Table.typeDef [0, moduleName, 0, 0, 1, 1]
  let intField ← blob [0x06, 0x08]
  let holderName ← string "Holder`1"
  let holder ← row Table.typeDef [1, holderName, 0, 1 * 4 + 1, 1, 1]
  let parameterName ← string "T"
  let _ ← row Table.genericParam [0, 0, (holder - 0x02000000) * 2, parameterName]
  let heldName ← string "V"
  let held ← row Table.field [0x0016, heldName, intField]
  link linkDeclaring held 0 holder
  let plainName ← string "Plain"
  let plain ← row Table.typeDef [1, plainName, 0, 1 * 4 + 1, 2, 1]
  let valueName ← string "W"
  let value ← row Table.field [0x0016, valueName, intField]
  link linkDeclaring value 0 plain
  pure (holder, held, plain, value)

private def arity : MetadataSlice × Nat × Nat × Nat × Nat :=
  build arityWorld (bytesOf "T")

private def holder : Nat := arity.2.1
private def held : Nat := arity.2.2.1
private def plain : Nat := arity.2.2.2.1
private def plainValue : Nat := arity.2.2.2.2

/-- Whether a step over the environment of the arity slice succeeds. -/
private def arityAccepts {α : Type} (step : MetadataEnv → Except MetadataError α) : Bool :=
  match (do step (MetadataEnv.ofSlices [← arity.1.index] (platform := objectPlatform))) with
  | .ok _ => true
  | .error _ => false

/-- One `int` argument, and two. -/
private def oneInt : SigList := .cons (.primitive 8) .nil
private def twoInts : SigList := .cons (.primitive 8) oneInt

/-- A generic definition is named only as an instance with one argument per parameter: not as
    a type alone, through a type token, or as the owner of a field token, and a non-generic one
    takes no arguments. -/
theorem generic_definitions_take_their_arguments :
    arityAccepts (·.resolve 0 (.named false plain)) = true ∧
    arityAccepts (·.resolve 0 (.named false holder)) = false ∧
    arityAccepts (·.resolve 0 (.genericInst false holder oneInt)) = true ∧
    arityAccepts (·.resolve 0 (.genericInst false holder .nil)) = false ∧
    arityAccepts (·.resolve 0 (.genericInst false holder twoInts)) = false ∧
    arityAccepts (·.resolve 0 (.genericInst false plain oneInt)) = false ∧
    arityAccepts (·.resolveToken 0 plain) = true ∧
    arityAccepts (·.resolveToken 0 holder) = false ∧
    arityAccepts (·.fieldSite plainValue) = true ∧
    arityAccepts (·.fieldSite held) = false := by decide +kernel
#print axioms generic_definitions_take_their_arguments

/-- Class receivers are objects; value and enum receivers are managed references. -/
theorem accepts_matching_receivers :
    (receiverIdentity "Object" false true true).isOk = true ∧
    (receiverIdentity "ValueType" false true false).isOk = true ∧
    (receiverIdentity "Enum" false true false).isOk = true ∧
    (receiverIdentity "ValueType" false true false true).isOk = true ∧
    (receiverIdentity "Object" false false false).isOk = true := by decide +kernel
/-- info: 'Tests.MetadataBinding.accepts_matching_receivers' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs in
#print axioms accepts_matching_receivers

/-- A rejected receiver reports the method token whose claim is inconsistent. -/
private def receiverMismatch (result : Except MetadataError MethodNames) : Bool :=
  match result with
  | .error error => error == .methodMismatch 0x06000001
  | .ok _ => false

/-- A receiver claim cannot reinterpret a class instance as a managed reference. -/
theorem rejects_mismatched_receivers :
    receiverMismatch (receiverIdentity "Object" false true false) = true ∧
    receiverMismatch (receiverIdentity "ValueType" false true true) = true ∧
    receiverMismatch (receiverIdentity "Enum" false true true) = true ∧
    receiverMismatch (receiverIdentity "Object" true true false) = true ∧
    receiverMismatch (receiverIdentity "Object" true true true) = true ∧
    receiverMismatch (receiverIdentity "Object" false false true) = true := by decide +kernel
/-- info: 'Tests.MetadataBinding.rejects_mismatched_receivers' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs in
#print axioms rejects_mismatched_receivers

/-- `T.Program.Main`, a public static method with no parameters. -/
private def mainMethod : RawMethod :=
  { token := tokens.main, owner := ownScope ++ "::Program", hasThis := false,
    explicitThis := false, callingConvention := 0, attributes := 0x96, implementation := 0,
    returnType := .void, parameters := [], locals := [], initLocals := false, maxStack := 8,
    genericParameters := [], code := [] }

/-- Whether the method definition is accepted, or refused with this error. -/
private def identity (slice : MetadataSlice) (method : RawMethod) :
    Except MetadataError MethodNames := do
  let env := MetadataEnv.ofSlices [← slice.index, ← lib.index] (platform := worldPlatform)
  methodIdentityValid env method [] []

private def identityFails (slice : MetadataSlice) (method : RawMethod) (error : MetadataError) :
    Bool :=
  match identity slice method with
  | .error found => found == error
  | .ok _ => false

theorem accepts_the_method_definition_its_row_gives :
    (match identity own.1 mainMethod with
      | .ok _ => true
      | .error _ => false) = true := by decide +kernel
#print axioms accepts_the_method_definition_its_row_gives

/-- A MethodDef taking ELEMENT_TYPE_OBJECT binds the root's scope and full name. -/
theorem binds_method_definition_object_parameter :
  let slice := mutateBlob own.1 (blobOffset own.1 [0, 0, 1]) fun _ => [4, 0, 1, 1, 0x1C]
  let claim := fun scope name => { mainMethod with parameters := [.object scope name] }
  (identity slice (claim runtimeScope "System.Object")).isOk = true ∧
    identityFails slice (claim libScope "System.Object") (.methodMismatch tokens.main) = true ∧
    identityFails slice (claim runtimeScope "System.String") (.methodMismatch tokens.main) = true
  := by decide +kernel
#print axioms binds_method_definition_object_parameter

theorem rejects_a_method_definition_that_differs_from_its_row :
    identityFails own.1 { mainMethod with attributes := 0x97 }
      (.methodMismatch tokens.main) = true ∧
    identityFails own.1 { mainMethod with implementation := 1 }
      (.methodMismatch tokens.main) = true ∧
    identityFails own.1 { mainMethod with hasThis := true }
      (.methodMismatch tokens.main) = true ∧
    identityFails own.1 { mainMethod with returnType := int32 }
      (.methodMismatch tokens.main) = true ∧
    identityFails own.1 { mainMethod with parameters := [int32] }
      (.methodMismatch tokens.main) = true ∧
    identityFails own.1 { mainMethod with genericParameters := [{ flags := 0, types := [] }] }
      (.methodMismatch tokens.main) = true := by decide +kernel
#print axioms rejects_a_method_definition_that_differs_from_its_row

/-- The names the row gives spell the owner the method states, and not another owner. -/
theorem names_spell_the_owner_the_method_states :
    (match identity own.1 mainMethod with
      | .ok names => decide (names.Spell mainMethod) &&
          !decide (names.Spell { mainMethod with owner := libScope ++ "::Program" })
      | .error _ => false) = true := by decide +kernel
#print axioms names_spell_the_owner_the_method_states

/-- A method row whose address differs from the one the body was read at is accepted: where a body
    sits in the image is not part of the default check. -/
theorem ignores_the_body_address :
    (match identity { own.1 with rows := own.1.rows.map fun (token, bytes) =>
        (token, if token == tokens.main then 7 :: bytes.drop 1 else bytes) } mainMethod with
      | .ok _ => true
      | .error _ => false) = true := by decide +kernel
#print axioms ignores_the_body_address

/-- A method's own full name spells a function pointer as Cecil does, so a method that takes a
    table of them can be selected by its signature; an external call identity still spells none,
    since the spelling leaves out the calling convention. -/
theorem spells_a_function_pointer_in_the_own_signature_only :
    instanceSignature (bytesOf "Examples.Kinds") (bytesOf "Indirect") false 0 [] (.primitive 9)
        [.szarray (.functionPointer 0 (.primitive 9) (.cons (.primitive 9) .nil)), .primitive 8,
          .primitive 9] =
      some (bytesOf ("System.UInt32 Examples.Kinds::Indirect(method System.UInt32 " ++
        "*(System.UInt32)[],System.Int32,System.UInt32)")) ∧
    cecilName false resolveFuel (.functionPointer 0 (.primitive 9) .nil) = none := by
  decide +kernel
#print axioms spells_a_function_pointer_in_the_own_signature_only

/-- `Main`'s row and the method with the flags and implementation flags changed together. -/
private def withFlags (flags implementation : Nat) : MetadataSlice × RawMethod :=
  (mutateRow own.1 tokens.main fun bytes =>
      (bytes.set 4 (implementation % 256)).set 5 (implementation / 256)
        |>.set 6 (flags % 256) |>.set 7 (flags / 256),
    { mainMethod with attributes := flags, implementation := implementation })

/-- A row whose flags say it has no IL body is refused, so no body bytes are taken for it: an
    abstract method, a platform invoke and an internal call. -/
theorem rejects_body_bytes_for_a_row_without_a_body :
    identityFails (withFlags 0x0496 0).1 (withFlags 0x0496 0).2
      (.bodyLocation tokens.main) = true ∧
    identityFails (withFlags 0x2096 0).1 (withFlags 0x2096 0).2
      (.bodyLocation tokens.main) = true ∧
    identityFails (withFlags 0x0096 0x1000).1 (withFlags 0x0096 0x1000).2
      (.bodyLocation tokens.main) = true := by decide +kernel
#print axioms rejects_body_bytes_for_a_row_without_a_body

/-- A runtime-async row is refused: its body returns the result its signature states as a task. -/
theorem rejects_a_runtime_async_row :
    identityFails (withFlags 0x0096 0x2000).1 (withFlags 0x0096 0x2000).2
      (.runtimeAsync tokens.main) = true := by decide +kernel
#print axioms rejects_a_runtime_async_row

/-- The same rewrite of the row with `Main`'s own flags is accepted, so the refusals above come
    from the flags and not from the rewrite. -/
theorem accepts_the_row_rewritten_with_its_own_flags :
    (match identity (withFlags 0x0096 0).1 (withFlags 0x0096 0).2 with
      | .ok _ => true
      | .error _ => false) = true := by decide +kernel
#print axioms accepts_the_row_rewritten_with_its_own_flags

/-! ## Which extractor types name a resolved type -/

/-- A frame whose primitive assembly is `C`, whose modified types are anchored at `A`, and whose
    method and owner have one generic parameter each. -/
private def pairFrame : Frame :=
  { corlib := some (bytesOf "C"), anchor := bytesOf "A", arity := 1, ownerArity := 1 }

/-- The type `name` of scope `scope` with the given kind. -/
private def namedIn (scope name : String) (kind : Extraction.TypeKind) (pinned := false) :
    NamedType :=
  { scope := bytesOf scope, name := bytesOf name, parts := [], kind := kind, pinned := pinned }

/-- A modified open parameter binds the modifier and the variable inside the reference. -/
example :
    let frame := { pairFrame with rawIndices := true }
    let modifier := namedIn "Library" "Modifier" (.external none)
    let type := ResolvedType.modified true modifier (.byref (.var 0))
    frame.admits type (.modified true "Library" "Modifier" (.byref (.ownerParameter 0))) &&
      !frame.admits type (.modified true "Other" "Modifier" (.byref (.ownerParameter 0))) &&
      !frame.admits type (.modified true "Library" "Modifier" (.byref (.ownerParameter 1))) &&
      !frame.admits type (.modified false "Library" "Modifier" (.byref (.ownerParameter 0))) := by
  decide +kernel

/-- `System.Int32` of the primitive assembly. -/
private def int32Atom : TypeExpr := .atom "C" "System.Int32"

/-- The tested enum declaration supplies its actual scope and both TypeDef name columns. -/
private def enumRow (kind : Extraction.TypeKind) (pinned := false) : NamedType :=
  { scope := bytesOf "L, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null",
    name := bytesOf "E", parts := [[], bytesOf "E"], kind, pinned,
    assembly := some (Tests.unsignedAssembly name!"L") }

/-- The physical type proposed for this enum row. -/
private def enumE : TypeIdentity := Tests.enumIdentity "E" (Tests.unsignedAssembly name!"L")
/-- The resolved platform enum `L::E` has 32-bit signed storage. -/
private def platformEnum : NamedType :=
  enumRow (.enumType 8)

/-- `L.G<int>`, with `L.G` of the given kind and pinning. -/
private def instanceOf (kind : Extraction.TypeKind) (pinned := false) : ResolvedType :=
  .genericInst { namedIn "L" "G`1" kind pinned with parts := [[], bytesOf "G`1"] }
    (.cons (.primitive 8) .nil)

/-- A generic application with `count` method-parameter arguments. -/
private def application : Nat → TypeExpr
  | 0 => .constructor "L" "G"
  | count + 1 => .apply (application count) (.parameter count)

/-- A resolved generic instance of the same arity. -/
private def instanceArguments (count : Nat) : ResolvedType :=
  .genericInst { namedIn "L" "G" .valueType with parts := [[], bytesOf "G"] }
    (ResolvedList.ofList ((List.range count).map ResolvedType.mvar))

/-- Splitting a whole application visits each argument once. -/
private def splitApplication (count : Nat) : Bool :=
  (appliedArguments (application count)).2.length == count

/-- Structural comparison admits the matching arguments with enough fuel for their count. -/
private def admitsApplication (count : Nat) : Bool :=
  typeAdmits { pairFrame with arity := count } (count + 4)
    (instanceArguments count) (application count)

/-- A single expected argument whose type differs from the outermost claimed argument. -/
private def refusesApplication (count : Nat) : Bool :=
  !pairFrame.admits (instanceArguments 1) (.apply (application count) .void)

open Lean Meta Elab Command in
run_cmd do
  for check in [``splitApplication, ``admitsApplication, ``refusesApplication] do
    let mut previous := 0
    for count in [16, 64, 256] do
      let (statement, proof) ← liftTermElabM do
        let decision := mkApp (mkConst check) (mkNatLit count)
        pure (← mkEq decision (mkConst ``Bool.true), ← mkEqRefl (mkConst ``Bool.true))
      let start ← IO.getNumHeartbeats
      match Kernel.check (← getEnv) {} (.letE `checked statement proof (.bvar 0) false) with
      | .error error => throwKernelException error
      | .ok _ => pure ()
      let cost := (← IO.getNumHeartbeats) - start
      logInfo m!"{check.getString!} {count} arguments: {cost} kernel heartbeats"
      let growth := if check == ``refusesApplication then 2 else 5
      if previous != 0 && cost > previous * growth then
        throwError "generic application comparison exceeded its heartbeat growth bound"
      previous := cost

/-- The carried struct `L.S<T>` closed over the given argument. -/
private def structOf (argument : ResolvedType) : ResolvedType :=
  .genericInst (namedIn "L" "S`1" .valueType true) (.cons argument .nil)

/-- The aggregate identity of `S<B>` cannot name `S<A>` even when both arguments are structs. -/
theorem refuses_another_struct_argument :
    pairFrame.admits (structOf (.named (namedIn "L" "A" .valueType true)))
      (.aggregate "L::S`1<L::B>" 1) = false := by decide +kernel
#print axioms refuses_another_struct_argument

/-- The aggregate identity shared by the class and struct spellings of the inner `G<int>`. -/
private def structOfInstance : TypeExpr := .aggregate "L::S`1<L::G`1<C::System.Int32>>" 1

/-- A class instance cannot supply the value argument of a preclosed aggregate. -/
theorem refuses_a_class_argument :
    pairFrame.admits (structOf (instanceOf .classType true)) structOfInstance = false := by
  decide +kernel
#print axioms refuses_a_class_argument

/-- Array element admission checks the generic argument of its aggregate element. -/
theorem refuses_an_array_of_structs_with_a_class_argument :
    pairFrame.admits (.szarray (structOf (instanceOf .classType true)))
      (.array structOfInstance) = false := by decide +kernel
#print axioms refuses_an_array_of_structs_with_a_class_argument

/-- Byref admission checks the generic argument of its target aggregate. -/
theorem refuses_a_byref_to_a_struct_with_a_class_argument :
    pairFrame.admits (.byref (structOf (instanceOf .classType true)))
      (.byref structOfInstance) = false := by decide +kernel
#print axioms refuses_a_byref_to_a_struct_with_a_class_argument

/-- A struct argument that itself takes a class prevents admission of the outer aggregate. -/
theorem refuses_a_class_inside_a_struct_argument :
    pairFrame.admits (structOf (structOf (instanceOf .classType true)))
      (.aggregate "L::S`1<L::S`1<L::G`1<C::System.Int32>>>" 2) = false := by decide +kernel
#print axioms refuses_a_class_inside_a_struct_argument

/-- An integer, a struct closed over an integer and a carried enum are value arguments. -/
theorem admits_aggregate_value_arguments :
    pairFrame.admits (structOf (.primitive 8)) (.aggregate "L::S`1<C::System.Int32>" 0) &&
    pairFrame.admits (structOf (instanceOf .valueType true)) structOfInstance &&
    pairFrame.admits (structOf (.named (namedIn "L" "E" (.enumType 8) true)))
      (.aggregate "L::S`1<L::E>" 0) := by decide +kernel
#print axioms admits_aggregate_value_arguments

/-- The matching identity of a struct closed over System.Void still has an invalid argument. -/
theorem refuses_a_void_aggregate_argument :
    pairFrame.admits (structOf (.primitive 0x01)) (.aggregate "L::S`1<C::System.Void>" 0) =
      false := by decide +kernel
#print axioms refuses_a_void_aggregate_argument

/-- An enum declared inside a generic type takes its enclosing type's arguments. -/
theorem admits_a_closed_nested_enum_argument :
    let nestedEnum := ResolvedType.genericInst (namedIn "L" "Outer`1/E" (.enumType 8) true)
      (.cons (.primitive 8) .nil)
    pairFrame.admits (structOf nestedEnum)
      (.aggregate "L::S`1<L::Outer`1/E<C::System.Int32>>" 1) = true := by decide +kernel
#print axioms admits_a_closed_nested_enum_argument

/-- An external head uses Cecil's spelling, including for arguments following a value argument. -/
private def externalPairAdmits (argument : ResolvedType) (name : String) : Bool :=
  let pair := ResolvedType.genericInst (namedIn "L" "Pair`2" (.external (some true)))
    (.cons (.primitive 8) (.cons argument .nil))
  pairFrame.admits pair (.aggregate ("L::Pair`2<System.Int32," ++ name ++ ">") 0)

/-- A matching Cecil spelling cannot give a reference, an address or a variable value storage. -/
theorem refuses_nonvalue_arguments_of_an_external_struct :
    ([(.named (namedIn "L" "C" .classType), "C"),
      (.named (namedIn "L" "I" .interfaceType), "I"),
      (.primitive 0x0E, "System.String"), (.primitive 0x1C, "System.Object"),
      (.szarray (.primitive 8), "System.Int32[]"), (.pointer (.primitive 8), "System.Int32*"),
      (.byref (.primitive 8), "System.Int32&"), (.var 0, "!0"), (.mvar 0, "!!0"),
      (.modified false (namedIn "L" "M" (.external none)) (.primitive 8),
        "System.Int32 modopt(M)")] :
      List (Prod ResolvedType String)).all (fun (arg, name) => !externalPairAdmits arg name) := by
  decide +kernel
#print axioms refuses_nonvalue_arguments_of_an_external_struct

/-- One pairing for each way `typeAdmits` accepts, by resolved and extractor constructor. -/
private def acceptedPairings : List (ResolvedType × TypeExpr) := [
  -- Primitives: `void`, an atom of the primitive assembly, and a string as an object.
  (.primitive 1, .void), (.primitive 8, int32Atom),
  (.primitive 0x0E, .atom "C" "System.String"), (.primitive 0x1C, .atom "C" "System.Object"),
  (.primitive 0x0E, .object "C" "System.String"),
  -- Named types: an atom unless a carried enum, an object if a carried class or the runtime's
  -- string, an aggregate if value-like, and an enum over the underlying type its carried row
  -- or its platform definition states.
  (.named (namedIn "L" "N" .valueType), .atom "L" "N"),
  (.named (namedIn "L" "N" .classType), .atom "L" "N"),
  (.named (namedIn "L" "N" (.external none)), .atom "L" "N"),
  (.named { namedIn "L" "N" .classType true with parts := [[], bytesOf "N"] }, .object "L" "N"),
  (.named { namedIn runtimeScope "System.String" (.external (some false)) with
      parts := [bytesOf "System", bytesOf "String"] }, .object runtimeScope "System.String"),
  (.named (namedIn "L" "N" .valueType), .aggregate "L::N" 0),
  (.named (namedIn "L" "N" (.external (some true))), .aggregate "L::N" 0),
  (.named (namedIn "L" "N" (.external none)), .aggregate "L::N" 0),
  (.named (enumRow (.enumType 8) true), .enum enumE .signed32),
  (.named platformEnum, .enum enumE .signed32),
  -- Generic parameters: the method's first, then the owner's.
  (.mvar 0, .parameter 0), (.var 0, .parameter 1),
  -- Element types, element by element.
  (.byref (.primitive 8), .byref int32Atom), (.pointer (.primitive 8), .pointer int32Atom),
  (.szarray (.primitive 8), .array int32Atom),
  (.szarray (.named { namedIn "L" "N" .classType true with parts := [[], bytesOf "N"] }),
    .array (.object "L" "N")),
  -- Instances: a value-like one as an aggregate, with its scoped arguments
  -- in declaration order, and any instance as an `apply` chain over a head of its kind.
  (instanceOf .valueType, .aggregate "L::G`1<System.Int32>" 0),
  (instanceOf .valueType true, .aggregate "L::G`1<C::System.Int32>" 0),
  (instanceOf .classType, .apply (.objectConstructor "L" "G`1") int32Atom),
  (instanceOf .interfaceType, .apply (.objectConstructor "L" "G`1") int32Atom),
  (instanceOf (.external (some false)), .apply (.objectConstructor "L" "G`1") int32Atom),
  (instanceOf .valueType, .apply (.constructor "L" "G`1") int32Atom),
  (instanceOf (.external (some true)), .apply (.constructor "L" "G`1") int32Atom),
  -- Function pointers, with the calling convention and receiver flags.
  (.functionPointer 0 (.primitive 8) (.cons (.primitive 8) .nil),
    .functionPointer int32Atom (.signatureParameter int32Atom .void) 0 false false),
  (.functionPointer 0x20 (.primitive 8) .nil, .functionPointer int32Atom .void 0 true false),
  -- A modified type as an atom of the anchor, spelled with its modifier.
  (.modified true (namedIn "M" "Mod" (.external none)) (.primitive 8),
    .atom "A" "System.Int32 modreq(Mod)"),
  (.modified false (namedIn "M" "Mod" (.external none)) (.primitive 8),
    .atom "A" "System.Int32 modopt(Mod)")]

/-- For each accepting arm, a pairing that changes the scope, the name, the kind, the index, the
    element, the convention or the constructor; and pairings of constructors no arm relates. -/
private def refusedPairings : List (ResolvedType × TypeExpr) := [
  -- Primitives.
  (.primitive 8, .void), (.primitive 1, .atom "C" "System.Void"),
  (.primitive 8, .atom "D" "System.Int32"), (.primitive 8, .atom "C" "System.UInt32"),
  (.primitive 0x0E, .object "C" "System.Object"), (.primitive 0x1C, .object "C" "System.Object"),
  (.primitive 8, .object "C" "System.Int32"),
  (.primitive 8,
    .enum (Tests.enumIdentity "System.Int32" (Tests.unsignedAssembly name!"C")) .signed32),
  -- Named types.
  (.named (namedIn "L" "N" .valueType), .atom "L" "M"),
  (.named (namedIn "L" "N" .valueType), .atom "K" "N"),
  (.named (namedIn "L" "N" (.enumType 8)), .atom "L" "N"),
  (.named (namedIn "L" "N" .valueType), .object "L" "N"),
  (.named (namedIn "L" "N" (.external (some true))), .object "L" "N"),
  (.named (namedIn "L" "N" .classType), .object "L" "N"),
  (.named (namedIn "L" "N" .interfaceType true), .object "L" "N"),
  (.named (namedIn "L" "N" (.external (some false))), .object "L" "N"),
  (.named (namedIn "L" "N" (.external none)), .object "L" "N"),
  (.named (namedIn "L" "System.String" (.external none)), .object "L" "System.String"),
  (.named (namedIn "L" "N" .classType), .aggregate "L::N" 0),
  (.named (namedIn "L" "N" (.external (some false))), .aggregate "L::N" 0),
  (.named (namedIn "L" "N" .valueType), .aggregate "L::M" 0),
  (.named (enumRow (.enumType 8) true), .enum enumE .signed64),
  (.named platformEnum, .enum enumE .unsigned8),
  (.named (enumRow (.external none)), .enum enumE .signed32),
  (.named (enumRow .classType), .enum enumE .signed32),
  (.named (enumRow (.external (some false))), .enum enumE .signed32),
  (.named (namedIn "L" "N" .valueType), .constructor "L" "N"),
  (.named (namedIn "L" "N" .valueType), .parameter 0),
  -- Generic parameters.
  (.var 0, .parameter 0), (.mvar 0, .parameter 1), (.primitive 8, .parameter 0),
  (.var 0, int32Atom),
  -- Element types.
  (.byref (.primitive 8), .pointer int32Atom), (.byref (.primitive 8), .array int32Atom),
  (.pointer (.primitive 8), .byref int32Atom), (.szarray (.primitive 8), .pointer int32Atom),
  (.szarray (.named (namedIn "L" "N" .interfaceType true)), .array (.object "L" "N")),
  (.byref (.primitive 9), .byref int32Atom),
  -- Instances.
  (instanceOf .valueType true, .aggregate "L::G`1<System.Int32>" 0),
  (instanceOf .classType, .aggregate "L::G`1<System.Int32>" 0),
  (instanceOf .classType, .apply (.objectConstructor "L" "G`1") (.atom "C" "System.UInt32")),
  (instanceOf .classType, .apply (.objectConstructor "K" "G`1") int32Atom),
  (instanceOf .classType, .objectConstructor "L" "G`1"),
  -- A head of the other kind, and a kind the metadata leaves open.
  (instanceOf .classType, .apply (.constructor "L" "G`1") int32Atom),
  (instanceOf .interfaceType, .apply (.constructor "L" "G`1") int32Atom),
  (instanceOf (.external (some false)), .apply (.constructor "L" "G`1") int32Atom),
  (instanceOf .valueType, .apply (.objectConstructor "L" "G`1") int32Atom),
  (instanceOf (.external (some true)), .apply (.objectConstructor "L" "G`1") int32Atom),
  (instanceOf (.external none), .apply (.constructor "L" "G`1") int32Atom),
  (instanceOf (.external none), .apply (.objectConstructor "L" "G`1") int32Atom),
  (instanceOf .classType, .atom "L" "G`1<System.Int32>"),
  -- Function pointers.
  (.functionPointer 0 (.primitive 8) (.cons (.primitive 8) .nil),
    .functionPointer int32Atom (.signatureParameter int32Atom .void) 1 false false),
  (.functionPointer 0x20 (.primitive 8) .nil, .functionPointer int32Atom .void 0 false false),
  (.functionPointer 0 (.primitive 8) .nil, int32Atom),
  -- Modified types.
  (.modified true (namedIn "M" "Mod" (.external none)) (.primitive 8),
    .atom "B" "System.Int32 modreq(Mod)"),
  (.modified true (namedIn "M" "Mod" (.external none)) (.primitive 8),
    .atom "A" "System.Int32 modopt(Mod)"),
  (.modified true (namedIn "M" "Mod" (.external none)) (.primitive 9),
    .atom "A" "System.Int32 modreq(Mod)"),
  (.modified true (namedIn "M" "Mod" (.external none)) (.primitive 8),
    .object "A" "System.Int32 modreq(Mod)")]

/-- Every listed pairing is accepted. -/
theorem admits_each_accepted_pairing :
    acceptedPairings.all (fun (type, expr) => pairFrame.admits type expr) = true := by
  decide +kernel
#print axioms admits_each_accepted_pairing

/-- Every listed pairing is refused. -/
theorem refuses_each_refused_pairing :
    refusedPairings.all (fun (type, expr) => !pairFrame.admits type expr) = true := by
  decide +kernel
#print axioms refuses_each_refused_pairing

/-- A method parameter past the method's arity is refused, so it cannot be read as the owner
    parameter whose extractor index it shares. -/
theorem refuses_a_method_parameter_past_the_arity :
    !pairFrame.admits (.mvar 1) (.parameter 1) && pairFrame.admits (.var 0) (.parameter 1) &&
      pairFrame.admits (.mvar 0) (.parameter 0) := by
  decide +kernel
#print axioms refuses_a_method_parameter_past_the_arity

/-! ## Facts read from a type's own reference -/

/-- `T` with `System.ValueTuple<int, int>` and references to its fields `Item1` and
    `Item2` whose field signatures end with the type bytes `first` and `second`. -/
private def tupleWorldWith (first second : List Nat) : Step (Nat × Nat) := do
  let _ ← ownWorld
  let tupleName ← string "ValueTuple`2"
  let systemName ← string "System"
  let firstName ← string "Item1"
  let secondName ← string "Item2"
  let tupleRef ← row Table.typeRef [1 * 4 + 2, tupleName, systemName]
  let tupleBlob ← blob [0x15, 0x11, typeRefCoded tupleRef, 2, 0x08, 0x08]
  let tupleSpec ← row Table.typeSpec [tupleBlob]
  let firstSignature ← blob (0x06 :: first)
  let secondSignature ← blob (0x06 :: second)
  let parent := (tupleSpec - 0x1B000000) * 8 + 4
  let firstRef ← row Table.memberRef [parent, firstName, firstSignature]
  let secondRef ← row Table.memberRef [parent, secondName, secondSignature]
  pure (firstRef, secondRef)

/-- The tuple world with `Item1 : !0` and `Item2 : !1`. -/
private def tupleWorld : Step (Nat × Nat) := tupleWorldWith [0x13, 0x00] [0x13, 0x01]

/-- The tuple world's slice with the given core-library number, and its field tokens. -/
private def tupleSlice (corlib : Nat) : MetadataSlice × Nat × Nat :=
  let (slice, fields) := build tupleWorld (bytesOf "T")
  ({ slice with corlib := corlib }, fields)

/-- The pair as the extractor names it. -/
private def pairTuple : TypeExpr :=
  .aggregate (s!"{runtimeScope}::System.ValueTuple`2<{runtimeScope}::System.Int32,{runtimeScope}::System.Int32>") 0

/-- The pair's instance field at `index` with `name`. -/
private def pairField (index : Nat) (name : MetadataName) : RawOperand :=
  .field pairTuple index int32 name false

/-- The pair's reference determines its field indices even without a core-library number.
    Checking the held primitive at the correct index also requires its scope. -/
theorem reads_the_pair_from_its_own_reference :
    passes (tupleSlice 1).1 lib (tupleSlice 1).2.2 (pairField 1 name!"Item2") = true ∧
    rejects (tupleSlice 0).1 lib (tupleSlice 0).2.2 (pairField 1 name!"Item2")
      (.operandMismatch (tupleSlice 0).2.2) = true ∧
    rejects (tupleSlice 0).1 lib (tupleSlice 0).2.1 (pairField 0 name!"Item1")
      (.operandMismatch (tupleSlice 0).2.1) = true ∧
    rejects (tupleSlice 1).1 lib (tupleSlice 1).2.2 (pairField 0 name!"Item2")
      (.fieldIndexMismatch (tupleSlice 1).2.2 0 1) = true ∧
    rejects (tupleSlice 0).1 lib (tupleSlice 0).2.2 (pairField 0 name!"Item2")
      (.fieldIndexMismatch (tupleSlice 0).2.2 0 1) = true := by decide +kernel
#print axioms reads_the_pair_from_its_own_reference

/-- The tuple world with `Item1` declared `int64`, and its field tokens. -/
private def wideTuple : MetadataSlice × Nat × Nat :=
  build (tupleWorldWith [0x0A] [0x13, 0x01]) (bytesOf "T")

/-- The tuple world with `Item1` declared `!1`, and its field tokens. -/
private def swappedTuple : MetadataSlice × Nat × Nat :=
  build (tupleWorldWith [0x13, 0x01] [0x13, 0x01]) (bytesOf "T")

/-- With no carried row a reference's signature is the item's only declaration, so `Item1`
    declared `int64` or `!1` is refused although the operand holds the pair's first argument. -/
theorem refuses_a_pair_item_declared_otherwise :
    rejects wideTuple.1 lib wideTuple.2.1 (pairField 0 name!"Item1")
      (.operandMismatch wideTuple.2.1) = true ∧
    rejects swappedTuple.1 lib swappedTuple.2.1 (pairField 0 name!"Item1")
      (.operandMismatch swappedTuple.2.1) = true := by decide +kernel
#print axioms refuses_a_pair_item_declared_otherwise

/-- A `Lib` whose class `Lib.Outer` encloses `Leaf` twice, with namespace columns `A` and `B`,
    and `Mid` twice, with columns `A` and `B`, each enclosing an `Inner` of its own. -/
private def nestedLibWorld : Step Unit := do
  let runtimeName ← string "System.Runtime"
  let objectName ← string "Object"
  let systemName ← string "System"
  let moduleName ← string "<Module>"
  let libName ← string "Lib"
  let outerName ← string "Outer"
  let leafName ← string "Leaf"
  let midName ← string "Mid"
  let innerName ← string "Inner"
  let first ← string "A"
  let second ← string "B"
  let key ← blob runtimePublisher
  let _ ← row Table.assemblyRef [11, 0, 0, 0, 0, key, runtimeName, 0, 0]
  modify fun builder => { builder with corlib := 1 }
  let objectRef ← row Table.typeRef [1 * 4 + 2, objectName, systemName]
  let base := (objectRef - 0x01000000) * 4 + 1
  let _ ← row Table.typeDef [0, moduleName, 0, 0, 1, 1]
  let outer ← row Table.typeDef [1, outerName, libName, base, 1, 1]
  -- Nested public types: `Leaf` and `Mid` in `Outer`, then an `Inner` in each `Mid`.
  let types := [(leafName, first, outer), (leafName, second, outer), (midName, first, outer),
    (midName, second, outer), (innerName, 0, 0x02000005), (innerName, 0, 0x02000006)]
  for (name, namespace_, enclosing) in types do
    let nested ← row Table.typeDef [2, name, namespace_, base, 1, 1]
    let nesting ← row Table.nestedClass [nested - 0x02000000, enclosing - 0x02000000]
    link linkNesting nested 1 nesting

/-- The nested `Lib` slice. -/
private def nestedLib : MetadataSlice :=
  (build nestedLibWorld (bytesOf "Lib")).1

/-- A modifier in this module is identified through its enclosing TypeDef rows. -/
private def modifierClaim (name : String) : Bool :=
  let checked := do
    let env := MetadataEnv.ofSlices [← own.1.index, ← nestedLib.index]
    let marker ← modifierNamed env 1 (tokenOf Table.typeDef 7)
    let frame := { pairFrame with rawIndices := true }
    pure (frame.admits (.modified true marker (.primitive 1)) (.modified true libScope name .void))
  checked.toOption == some true

example : modifierClaim "Inner" = false := by decide +kernel
example : modifierClaim "Lib.Outer/A.Mid/Inner" := by decide +kernel

/-- `T` with references to `Outer/Leaf` and `Outer/Mid/Inner` through namespace `A` at each
    nested level, linked to the definitions at the given `TypeDef` rows of `Lib`. -/
private def nestedOwnWorld (leaf inner : Nat) : Step (Nat × Nat) := do
  let runtimeName ← string "System.Runtime"
  let libName ← string "Lib"
  let outerName ← string "Outer"
  let leafName ← string "Leaf"
  let midName ← string "Mid"
  let innerName ← string "Inner"
  let first ← string "A"
  let key ← blob runtimePublisher
  let _ ← row Table.assemblyRef [11, 0, 0, 0, 0, key, runtimeName, 0, 0]
  let _ ← row Table.assemblyRef [1, 0, 0, 0, 0, 0, libName, 0, 0]
  modify fun builder => { builder with corlib := 1 }
  let outerRef ← row Table.typeRef [2 * 4 + 2, outerName, libName]
  let enclosedBy (reference : Nat) := (reference - 0x01000000) * 4 + 3
  let leafRef ← row Table.typeRef [enclosedBy outerRef, leafName, first]
  let midRef ← row Table.typeRef [enclosedBy outerRef, midName, first]
  let innerRef ← row Table.typeRef [enclosedBy midRef, innerName, 0]
  link linkDefinition leafRef 1 (tokenOf Table.typeDef leaf)
  link linkDefinition innerRef 1 (tokenOf Table.typeDef inner)
  pure (leafRef, innerRef)

/-- The nested own slice with the given links, and its two reference tokens. -/
private def nestedOwn (leaf inner : Nat) : MetadataSlice × Nat × Nat :=
  build (nestedOwnWorld leaf inner) (bytesOf "T")

/-- A nested type is the type of its namespace column at every level: a reference through `A`
    resolves to the definitions through `A`, and a link to the type that differs only in its own
    column, or only in an enclosing type's, is refused though both spell `Lib.Outer/Leaf` or
    `Lib.Outer/Mid/Inner`. -/
theorem tells_nested_types_apart_by_their_namespace_columns :
    passes (nestedOwn 3 7).1 nestedLib (nestedOwn 3 7).2.1
      (.type (.object libScope "Lib.Outer/A.Leaf")) = true ∧
    passes (nestedOwn 3 7).1 nestedLib (nestedOwn 3 7).2.2
      (.type (.object libScope "Lib.Outer/A.Mid/Inner")) = true ∧
    rejects (nestedOwn 4 7).1 nestedLib (nestedOwn 4 7).2.1
      (.type (.object libScope "Lib.Outer/A.Leaf")) (.operandMismatch (nestedOwn 4 7).2.1) = true ∧
    rejects (nestedOwn 3 8).1 nestedLib (nestedOwn 3 8).2.2
      (.type (.object libScope "Lib.Outer/A.Mid/Inner"))
      (.operandMismatch (nestedOwn 3 8).2.2) = true := by decide +kernel
#print axioms tells_nested_types_apart_by_their_namespace_columns

/-! ## Kinds against the extractor's constructors -/

/-- `System.Int32` of the runtime scope, by its namespace and name columns, as a type of the
    given kind. -/
private def runtimeInt32 (kind : Extraction.TypeKind) : ResolvedType :=
  .named { namedIn runtimeScope "System.Int32" kind with
    parts := [bytesOf "System", bytesOf "Int32"] }

/-- A type that cannot be a value type is never admitted as the runtime's primitive, which uses
    fixed value storage. An ordinary class keeps its atom. -/
theorem refuses_a_class_named_as_a_primitive :
    !pairFrame.admits (runtimeInt32 (.external (some false))) (.primitive .int32) &&
      !pairFrame.admits (runtimeInt32 .classType) (.primitive .int32) &&
      !pairFrame.admits (runtimeInt32 .interfaceType) (.primitive .int32) &&
      !pairFrame.admits (runtimeInt32 (.external none)) (.primitive .int32) &&
      pairFrame.admits (runtimeInt32 (.external (some true))) (.primitive .int32) &&
      pairFrame.admits (.named (namedIn runtimeScope "System.Console" .classType))
        (.atom runtimeScope "System.Console") := by
  decide +kernel
#print axioms refuses_a_class_named_as_a_primitive

/-! ## Runtime primitives are typed -/

/-- A frame whose core library is the runtime assembly. -/
private def runtimeFrame : Frame :=
  { corlib := some runtimeScopeBytes, anchor := runtimeScopeBytes, arity := 0, ownerArity := 0 }

/-- A value type whose single name column spells `System.Int32` and whose namespace is empty. -/
private def flattenedInt32 : ResolvedType :=
  .named { namedIn runtimeScope "System.Int32" (.external (some true)) with
    parts := [[], bytesOf "System.Int32"] }

/-- A runtime primitive binds only as `TypeExpr.primitive`: the runtime-scope atom of its name is
    refused for an element code, a named reference of every kind, and a flattened name, while
    an atom of another core library keeps its binding. -/
theorem runtime_primitive_atoms_are_refused :
    runtimeFrame.admits (.primitive 8) (.primitive .int32) &&
      !runtimeFrame.admits (.primitive 8) (.primitive .uint32) &&
      !runtimeFrame.admits (.primitive 8) (.atom runtimeScope "System.Int32") &&
      pairFrame.admits (.primitive 8) (.atom "C" "System.Int32") &&
      !pairFrame.admits (.primitive 8) (.primitive .int32) &&
      runtimeFrame.admits (runtimeInt32 (.external (some true))) (.primitive .int32) &&
      !runtimeFrame.admits (runtimeInt32 (.external (some true))) (.primitive .uint32) &&
      [Extraction.TypeKind.external (some true), .external (some false), .external none,
        .valueType, .classType, .interfaceType].all (fun kind =>
          !runtimeFrame.admits (runtimeInt32 kind) (.atom runtimeScope "System.Int32")) &&
      !runtimeFrame.admits flattenedInt32 (.primitive .int32) &&
      !runtimeFrame.admits flattenedInt32 (.atom runtimeScope "System.Int32") := by
  decide +kernel
#print axioms runtime_primitive_atoms_are_refused

/-- The runtime-scope atom of a primitive's name has no storage; the typed primitive and the core
    library's own atom keep theirs. -/
theorem runtime_primitive_atoms_have_no_storage :
    typeStorage [] (.atom runtimeScope "System.Int32") = none ∧
      typeStorage [] (.primitive .int32) = some (.field .signed32) ∧
      typeStorage [] (.atom coreLibraryScope "System.Int32") = some (.field .signed32) := by
  decide +kernel
#print axioms runtime_primitive_atoms_have_no_storage

/-- Every resolved type refuses the runtime-scope atom of `System.UInt64`. -/
example (frame : Frame) (fuel : Nat) (type : ResolvedType) :
    typeAdmits frame fuel type (.atom runtimeScope "System.UInt64") = false :=
  typeAdmits_runtimePrimitiveAtom (by decide +kernel)

/-- An owner parameter past the owner's arity is refused, even where its extractor index would
    follow the method's parameters. -/
theorem refuses_an_owner_parameter_past_the_owner_arity :
    !pairFrame.admits (.var 1) (.parameter 2) && pairFrame.admits (.var 0) (.parameter 1) := by
  decide +kernel
#print axioms refuses_an_owner_parameter_past_the_owner_arity

/-! ## Each reason a reference or type is refused -/

/-- A type reference scoped by a module reference, which the checker does not read. -/
private def consoleInModuleReference : MetadataSlice :=
  mutateRow own.1 tokens.consoleRef fun bytes => [5, 0] ++ bytes.drop 2

theorem refuses_a_type_reference_scoped_by_a_module_reference :
    rejects consoleInModuleReference lib tokens.consoleRef
      (.type (.atom runtimeScope "System.Console")) (.unsupportedScope tokens.consoleRef) =
      true := by decide +kernel
#print axioms refuses_a_type_reference_scoped_by_a_module_reference

/-- The links of `T` with the one from `Lib.Box`'s reference removed, or aimed at `T` itself. -/
private def ownWithoutBoxLink : MetadataSlice :=
  { own.1 with links := own.1.links.filter fun link => link.kind != linkDefinition ||
      link.source != tokens.boxRef }

private def ownWithBoxLinkIntoItself : MetadataSlice :=
  { own.1 with links := own.1.links.map fun link =>
      if link.kind == linkDefinition && link.source == tokens.boxRef then
        { link with slice := 0 } else link }

theorem refuses_a_reference_into_a_pinned_slice_without_its_definition_link :
    rejects ownWithoutBoxLink lib tokens.boxRef (.type (.atom libScope "Lib.Box"))
      (.unresolvedType tokens.boxRef) = true ∧
    rejects ownWithBoxLinkIntoItself lib tokens.boxRef (.type (.atom libScope "Lib.Box"))
      (.unresolvedType tokens.boxRef) = true := by decide +kernel
#print axioms refuses_a_reference_into_a_pinned_slice_without_its_definition_link

/-- `Program` extending a type specification, and extending `Console` instead of `Object`: the
    chain of base classes ends only at `System.Object`. -/
private def programExtends (coded : Nat) : MetadataSlice :=
  mutateRow own.1 (tokenOf Table.typeDef 2) fun bytes =>
    bytes.take 8 ++ [coded, 0] ++ bytes.drop 10

private def objectFieldOperand : RawOperand :=
  .field (.object ownScope "Program") 0 int32 name!"count" false

theorem refuses_a_base_class_chain_that_does_not_end_at_object :
    passes own.1 lib tokens.countField objectFieldOperand = true ∧
    rejects (programExtends 6) lib tokens.countField objectFieldOperand
      (.unsupportedBase (tokenOf Table.typeDef 2)) = true ∧
    rejects (programExtends 9) lib tokens.countField objectFieldOperand
      (.unsupportedBase (tokenOf Table.typeDef 2)) = true := by decide +kernel
#print axioms refuses_a_base_class_chain_that_does_not_end_at_object

/-! ## Claims that name strings stored as bytes

A claim may name a `byteString`, a string stored as its bytes, where it would write a literal. The
checks read the same value either way, so a claim naming another valid string is refused by the
check that refuses the wrong literal, with the same error. -/

/-- `System.Object`, stored as its bytes. -/
private def objectText : String := byteString
    [83, 121, 115, 116, 101, 109, 46, 79, 98, 106, 101, 99, 116]
    "System.Object" (by cil_kernel_rfl)

/-- `System.Console`, stored as its bytes. -/
private def consoleText : String := byteString
    [83, 121, 115, 116, 101, 109, 46, 67, 111, 110, 115, 111, 108, 101]
    "System.Console" (by cil_kernel_rfl)

/-- `Program`, stored as its bytes. -/
private def programText : String := byteString
    [80, 114, 111, 103, 114, 97, 109]
    "Program" (by cil_kernel_rfl)

/-- `Lib.Box`, stored as its bytes. -/
private def boxText : String := byteString
    [76, 105, 98, 46, 66, 111, 120]
    "Lib.Box" (by cil_kernel_rfl)

/-- The identity of `T`, stored as its bytes. -/
private def ownText : String := byteString
    [84, 44, 32, 86, 101, 114, 115, 105, 111, 110, 61, 49, 46, 48, 46, 48, 46, 48, 44, 32, 67,
      117, 108, 116, 117, 114, 101, 61, 110, 101, 117, 116, 114, 97, 108, 44, 32, 80, 117, 98,
      108, 105, 99, 75, 101, 121, 84, 111, 107, 101, 110, 61, 110, 117, 108, 108]
    "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" (by cil_kernel_rfl)

/-- The runtime scope of version 9, stored as its bytes. -/
private def olderRuntimeText : String := byteString
    [83, 121, 115, 116, 101, 109, 46, 82, 117, 110, 116, 105, 109, 101, 44, 32, 86, 101, 114, 115,
      105, 111, 110, 61, 57, 46, 48, 46, 48, 46, 48, 44, 32, 67, 117, 108, 116, 117, 114, 101, 61,
      110, 101, 117, 116, 114, 97, 108, 44, 32, 80, 117, 98, 108, 105, 99, 75, 101, 121, 84, 111,
      107, 101, 110, 61, 98, 48, 51, 102, 53, 102, 55, 102, 49, 49, 100, 53, 48, 97, 51, 97]
    "System.Runtime, Version=9.0.0.0, Culture=neutral, \
      PublicKeyToken=b03f5f7f11d50a3a" (by cil_kernel_rfl)

/-- `System.Int32`, stored as its bytes. -/
private def int32Text : String := byteString
    [83, 121, 115, 116, 101, 109, 46, 73, 110, 116, 51, 50]
    "System.Int32" (by cil_kernel_rfl)

/-- `System.UInt32`, stored as its bytes. -/
private def uint32Text : String := byteString
    [83, 121, 115, 116, 101, 109, 46, 85, 73, 110, 116, 51, 50]
    "System.UInt32" (by cil_kernel_rfl)

/-- The primitive assembly `C` of `pairFrame`, stored as its bytes. -/
private def primitiveScopeText : String := byteString
    [67]
    "C" (by cil_kernel_rfl)

/-- The owner of `mainMethod`, stored as its bytes. -/
private def ownerText : String := byteString
    [84, 44, 32, 86, 101, 114, 115, 105, 111, 110, 61, 49, 46, 48, 46, 48, 46, 48, 44, 32, 67,
      117, 108, 116, 117, 114, 101, 61, 110, 101, 117, 116, 114, 97, 108, 44, 32, 80, 117, 98,
      108, 105, 99, 75, 101, 121, 84, 111, 107, 101, 110, 61, 110, 117, 108, 108, 58, 58, 80, 114,
      111, 103, 114, 97, 109]
    "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null::Program" (by cil_kernel_rfl)

/-- A `Program` owner in `Lib`, stored as its bytes. -/
private def libOwnerText : String := byteString
    [76, 105, 98, 44, 32, 86, 101, 114, 115, 105, 111, 110, 61, 49, 46, 48, 46, 48, 46, 48, 44,
      32, 67, 117, 108, 116, 117, 114, 101, 61, 110, 101, 117, 116, 114, 97, 108, 44, 32, 80, 117,
      98, 108, 105, 99, 75, 101, 121, 84, 111, 107, 101, 110, 61, 110, 117, 108, 108, 58, 58, 80,
      114, 111, 103, 114, 97, 109]
    "Lib, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null::Program" (by cil_kernel_rfl)

/-- Each stored string is the literal it spells. -/
theorem stored_strings_are_their_literals :
    objectText = "System.Object" ∧ ownerText = ownScope ++ "::Program" ∧
      olderRuntimeText = "System.Runtime, Version=9.0.0.0, Culture=neutral, \
        PublicKeyToken=b03f5f7f11d50a3a" :=
  ⟨byteString_eq _, byteString_eq _, byteString_eq _⟩
#print axioms stored_strings_are_their_literals

/-- The type operand check accepts the stored name of the type and refuses another, as it
    refuses the other literal. -/
theorem type_operand_check_reads_stored_strings :
    passes own.1 lib tokens.objectRef (.type (.atom runtimeScope objectText)) = true ∧
    rejects own.1 lib tokens.objectRef (.type (.atom runtimeScope consoleText))
      (.operandMismatch tokens.objectRef) = true ∧
    rejects own.1 lib tokens.objectRef (.type (.atom runtimeScope "System.Console"))
      (.operandMismatch tokens.objectRef) = true := by decide +kernel
#print axioms type_operand_check_reads_stored_strings

/-- The call operand check accepts the stored owner of the callee and refuses a stored owner
    scope of another version, as it refuses that scope's literal. -/
theorem call_operand_check_reads_stored_strings :
    passes own.1 lib tokens.writeLine
      (.call { writeLineSite with method.owner := .atom runtimeScope consoleText }) = true ∧
    rejects own.1 lib tokens.writeLine
      (.call { writeLineSite with method.owner := .atom olderRuntimeText consoleText })
      (.scopeMismatch tokens.writeLine) = true := by decide +kernel
#print axioms call_operand_check_reads_stored_strings

/-- The field operand check accepts the stored owner of the field and refuses another stored
    owner, as it refuses the other literal. -/
theorem field_operand_check_reads_stored_strings :
    passes own.1 lib tokens.totalField
      (.field (.atom ownText programText) 1 int32 name!"total" true) = true ∧
    rejects own.1 lib tokens.totalField (.field (.atom ownText boxText) 1 int32 name!"total" true)
      (.operandMismatch tokens.totalField) = true ∧
    rejects own.1 lib tokens.totalField
      (.field (.atom ownScope "Lib.Box") 1 int32 name!"total" true)
      (.operandMismatch tokens.totalField) = true := by decide +kernel
#print axioms field_operand_check_reads_stored_strings

/-- The method definition check refuses a stored return type the row does not give, as it
    refuses the literal. -/
theorem method_definition_check_reads_stored_strings :
    identityFails own.1 { mainMethod with returnType := .atom runtimeScope int32Text }
      (.methodMismatch tokens.main) = true ∧
    identityFails own.1 { mainMethod with returnType := .atom runtimeScope "System.Int32" }
      (.methodMismatch tokens.main) = true := by decide +kernel
#print axioms method_definition_check_reads_stored_strings

/-- `Frame.admits` names a primitive by its stored name and refuses another stored name, as it
    refuses the other literal. -/
theorem admits_reads_stored_strings :
    pairFrame.admits (.primitive 8) (.atom primitiveScopeText int32Text) = true ∧
    pairFrame.admits (.primitive 8) (.atom primitiveScopeText uint32Text) = false ∧
    pairFrame.admits (.primitive 8) (.atom "C" "System.UInt32") = false := by decide +kernel
#print axioms admits_reads_stored_strings

/-- The names the row of `mainMethod` gives. -/
private def mainNames : MethodNames :=
  match identity own.1 mainMethod with
  | .ok names => names
  | .error _ => {}

/-- The names spell a stored owner through a comparison of bytes, and that comparison and `Spell`
    both refuse another stored owner, as `Spell` refuses the other literal. -/
theorem spell_reads_stored_strings : mainNames.Spell { mainMethod with owner := ownerText } :=
  MethodNames.spell_of_spelledBy (by decide +kernel)
#print axioms spell_reads_stored_strings

theorem spell_refuses_another_stored_owner :
    mainNames.spelledBy { mainMethod with owner := libOwnerText } = false ∧
    !decide (mainNames.Spell { mainMethod with owner := libOwnerText }) = true ∧
    !decide (mainNames.Spell { mainMethod with owner := libScope ++ "::Program" }) = true := by
  decide +kernel
#print axioms spell_refuses_another_stored_owner

end Tests.MetadataBinding
