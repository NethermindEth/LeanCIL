import CIL.Extraction.DecodedMethod
import CIL.Safety.StepComposition
import CIL.Runtime.Net11WinX64.CoreLib

/-!
# The native pointer displacement in ObjectHeader.GetHeaderPtr

The .NET 11 Windows x64 method subtracts four bytes from its pointer argument. Its contract
requires a representable position in the same allocation. An allocation-relative pointer to a
CLR object header and exclusive ownership of that header require separate evidence.
-/

namespace Tests.CoreHeaderPointer

open CIL CIL.Safety CIL.Extraction
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private def pointerTo (type : String) := TypeExpr.pointer (.atom coreLibraryScope type .valueType)

/-- Carried owner, method and generic-boundary rows for MethodDef 0x06003b1f. -/
private def metadata : MethodMetadata := { own := {
  assembly := CIL.Runtime.Net11WinX64.CoreLib.assembly
  rows := [(0x020000a2, fixedBytes 18 0x0120100002000000040000000000FE021C07),
    (0x02000363, fixedBytes 18 0x8001100003000000050000008802380C1F3B),
    (0x02000364, fixedBytes 18 0x02010000FFFFFFFF000000002402380C293B),
    (0x06003b1f, fixedBytes 20 0x00000000000191000100000001000000E95C0000),
    (0x2a00022d, fixedBytes 12 0x00001800C0060000FFFFFFFF),
    (0x2a00022e, fixedBytes 12 0x00000000DE060000FFFFFFFF)]
  strings := [(1, bytesOf "GetHeaderPtr" ++ [0]), (2, bytesOf "Object" ++ [0]),
    (3, bytesOf "ObjectHeader" ++ [0]), (4, bytesOf "System" ++ [0]),
    (5, bytesOf "System.Threading" ++ [0])]
  blobs := [(1, fixedBytes 7 0x0600010F080F18)], corlib := 0
  links := [⟨1,0x06003b1f,0,0x02000363⟩] } }

private def original : RawMethod := {
  token := 0x06003b1f, owner := coreLibraryScope ++ "::System.Threading.ObjectHeader"
  hasThis := false, explicitThis := false, callingConvention := 0
  attributes := 0x91, implementation := 0x100, returnType := pointerTo "System.Int32"
  parameters := [pointerTo "System.IntPtr"], locals := [], initLocals := false, maxStack := 8
  genericParameters := [], code := [⟨0,2,.none⟩, ⟨1,26,.none⟩, ⟨2,89,.none⟩, ⟨3,42,.none⟩] }

private def body : BodyEvidence := {
  bytes := [0x12,0x02,0x1a,0x59,0x2a], tokens := { operands := [] }
  metadata, tables := metadata.tables.toOption.getD [], identities := [coreLibraryAssembly]
  names := { assembly := some coreLibraryAssembly, owner := bytesOf original.owner
             signature := bytesOf ("System.Int32* System.Threading.ObjectHeader::" ++
               "GetHeaderPtr(System.IntPtr*)") }
  pinned := PinnedIndex.ofIdentities [coreLibraryAssembly] }

private def method : Method := {
  declared := { parameters := [pointerTo "System.IntPtr"], returnType := pointerTo "System.Int32"
                initLocals := false }
  locals := [], returnsValue := true, code := [.ldarg 0, .ldc_i4 4, .sub, .ret] }

/-- The physical tiny method and its two pointer types determine the canonical method. -/
theorem binding : Method.ofBody? .scalar {} [] (List.replicate 4 true) body original [] =
    some method ∧ bodyMatches body original [] = true := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms binding
/-- The displacement byte and the primitive pointee in the declared argument both bind. -/
theorem changedOperands :
    bodyMatches { body with bytes := [0x12,0x02,0x19,0x59,0x2a] } original [] = false ∧
    (Method.ofBody? .scalar {} [] (List.replicate 4 true) body
      { original with parameters := [pointerTo "System.Int32"] } []).isNone = true := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms changedOperands

private def memory : Safety.Memory := { Safety.Memory.empty with
  allocations := fun id => if id == 0 then some ⟨.callerStack, ⟨16,8,[]⟩, true, []⟩ else none
  nextIdentity := 1 }
private def arg (offset : Nat) : Safety.Value := .reference (.address ⟨0,offset⟩)
private def code (pos : Nat) := invoke [method] 5 0 [arg pos] memory
/-- Two interior pointers move back exactly four bytes without accessing storage. -/
theorem withinAllocation : code 8 = .ok (memory,[arg 4]) ∧ code 4 = .ok (memory,[arg 0]) := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms withinAllocation
/-- The helper cannot cross below the beginning of a represented allocation. -/
theorem outsideAllocation : code 0 =
    .error ⟨0,2,.memory .invalidReference (.address ⟨0,0⟩) 0⟩ := by cil_kernel_rfl
#print axioms outsideAllocation

/-- Both forwarded and exact defining scopes qualify. A different scope, unknown type and
    pointer to a reference type receive no primitive-pointer storage. -/
theorem scopeBindings :
    typeStorage [] (.pointer (.atom coreLibraryScope "System.IntPtr"
        .valueType)) = some .reference ∧
    typeStorage [] (.pointer (.primitive .intPtr)) = some .reference ∧
    typeStorage [] (.pointer (.atom "System.Private.CoreLib" "System.IntPtr" .valueType)) = none ∧
    typeStorage [] (.pointer (.atom coreLibraryScope "System.IntPtq" .valueType)) = none ∧
    typeStorage [] (.pointer (.object coreLibraryScope "System.Object")) = none := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl,
    by cil_kernel_rfl⟩
#print axioms scopeBindings

/-- The original helper retains allocation identity, views, and cells for every successful
    pointer subtraction authorized by the memory model. -/
theorem headerDisplacement (before : Safety.Memory) (input output : ManagedReference)
    (live : checkedValue before (.reference input) = .ok (.reference input))
    (moved : referenceSubtract before input (.i32 4) = .ok output)
    (valid : checkedValue before (.reference output) = .ok (.reference output)) :
    invoke [method] 5 0 [.reference input] before = .ok (before,[.reference output]) := by
  let frame : Safety.Frame := ⟨before.nextIdentity,[],[],0,[]⟩
  apply invoke_of_run (body := method) (frame := frame) (entered := before) rfl
  · simp [List.mapM_cons, List.mapM_nil, live, bind, Except.bind, pure, Except.pure]
  · with_unfolding_all rfl
  · have lookup : [method][0]? = some method := rfl
    have arg : method.code[0]? = some (.ldarg 0) := by cil_kernel_rfl
    have four : method.code[1]? = some (.ldc_i4 4) := by cil_kernel_rfl
    have sub : method.code[2]? = some .sub := by cil_kernel_rfl
    have ret : method.code[3]? = some .ret := by cil_kernel_rfl
    have access : method.argumentAccess 0 = .value none := by cil_kernel_rfl
    have args : Safety.step method (.ldarg 0) 0 [.reference input] frame [] before =
        .ok (.next 1 [.reference input] frame before) := by
      rw [step_ldarg_value_eq _ _ _ _ _ _ _ access]
      change (do let v ← checkedValue before (.reference input)
                 pure (FrameAction.next 1 [v] frame before)) = _
      rw [live]
      rfl
    rw [run_next lookup arg args]
    rw [run_next (op := .ldc_i4 4) (target := 2)
          (values := [.scalar (.i32 4), .reference input]) (nextFrame := frame)
          (updated := before) lookup four (by rfl)]
    have stepSub : Safety.step method .sub 2 [.reference input] frame [.scalar (.i32 4),.reference input]
        before = .ok (.next 3 [.reference output] frame before) := by
      change (do let adjusted ← referenceSubtract before input (.i32 4)
                 pure (FrameAction.next 3 [.reference adjusted] frame before)) = _
      rw [moved]
      rfl
    rw [run_next lookup sub stepSub]
    have narrow : method.returnNarrow = none := by cil_kernel_rfl
    have returns : method.returnsValue = true := by cil_kernel_rfl
    apply run_return (updated := before) lookup ret
    · rw [step_ret_eq, narrow, returns]
      have specified : unspecifiedOperands 1 [.reference output] = false := rfl
      simp [specified, returnFrom, List.mapM_cons, List.mapM_nil, valid, bind, Except.bind,
        pure, Except.pure]
    · change (List.mapM (checkedValue before) [.reference output]) = _
      simp [List.mapM_cons, List.mapM_nil, valid, bind, Except.bind, pure, Except.pure]
#print axioms headerDisplacement
end Tests.CoreHeaderPointer
