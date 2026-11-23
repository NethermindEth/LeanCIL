import CIL.Extraction.DecodedMethod
import CIL.Safety.StepComposition
import CIL.Safety.CheckedMemoryFacts
import Tests.CoreLibImage

/-!
# The CoreLib Monitor.Enter lockTaken argument

The original two-argument overload reads the caller's byte before either call. A successful
one-argument Enter precedes its single-byte write. Both callees are explicit parameters. Their
contracts determine whether the monitor is acquired and which exception a failing call raises.
-/

namespace Tests.CoreMonitor
open CIL CIL.Extraction CIL.Safety
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private def root := TypeExpr.object coreLibraryScope "System.Object"
private def monitor := TypeExpr.atom coreLibraryScope "System.Threading.Monitor"

private def callee (name : MetadataName) (text : String) (token : Nat)
    (parameters : List TypeExpr) : RawOperand :=
  .call {
    method := ⟨monitor, name, false, 0, .void, parameters, []⟩
    name := text, target := .managed token, typeArguments := [], ownerArgumentCount := 0
    parameterCount := parameters.length, returnsValue := false
    declared := { convention := 0, returnType := .void, parameters } }

private def reject := callee name!"ThrowLockTakenException" "ThrowLockTakenException" 0x06003d69 []
private def enter := callee name!"Enter" "Enter" 0x06003d61 [root]

/-- MethodDef 0x06003d62 and the original offsets and operands of its ten instructions. -/
private def original : RawMethod := {
  token := 0x06003d62, owner := coreLibraryScope ++ "::System.Threading.Monitor"
  hasThis := false, explicitThis := false, callingConvention := 0
  attributes := 0x96, implementation := 0x100, returnType := .void
  parameters := [root, .byref (.atom coreLibraryScope "System.Boolean")]
  locals := [], initLocals := false, maxStack := 8, genericParameters := []
  code := [⟨0,3,.none⟩, ⟨1,71,.none⟩, ⟨2,44,.target 4⟩, ⟨4,40,reject⟩, ⟨9,2,.none⟩,
           ⟨10,40,enter⟩, ⟨15,3,.none⟩, ⟨16,23,.none⟩, ⟨17,82,.none⟩, ⟨18,42,.none⟩] }

/-- Method and owner rows, MethodDef links and signature blobs carried by the extractor. -/
private def metadata : MethodMetadata := { own := {
  assembly := Tests.CoreLibImage.assembly
  rows := [
    (0x020000a2, fixedBytes 18 0x0120100003000000040000000000FE021C07),
    (0x020003a3, fixedBytes 18 0x8101100002000000050000008802DD0C5B3D),
    (0x020003a4, fixedBytes 18 0x01011000FFFFFFFF05000000F80FDD0C713D),
    (0x06003d61, fixedBytes 20 0x00000000080096000100000002000000325F0000),
    (0x06003d62, fixedBytes 20 0x00000000000196000100000003000000335F0000),
    (0x06003d69, fixedBytes 20 0x000000000000910006000000010000003F5F0000),
    (0x2a000230, fixedBytes 12 0x000000002D070000FFFFFFFF),
    (0x2a000231, fixedBytes 12 0x0000040047070000FFFFFFFF)]
  strings := [(1, bytesOf "Enter" ++ [0]), (2, bytesOf "Monitor" ++ [0]),
    (3, bytesOf "Object" ++ [0]), (4, bytesOf "System" ++ [0]),
    (5, bytesOf "System.Threading" ++ [0]), (6, bytesOf "ThrowLockTakenException" ++ [0])]
  blobs := [(1, [3,0,0,1]), (2, [4,0,1,1,0x1c]), (3, [6,0,2,1,0x1c,0x10,2])]
  corlib := 0
  links := [⟨1,0x06003d61,0,0x020003a3⟩, ⟨1,0x06003d62,0,0x020003a3⟩,
            ⟨1,0x06003d69,0,0x020003a3⟩] } }

private def body : BodyEvidence := {
  bytes := [78,3,71,44,5,40,105,61,0,6,2,40,97,61,0,6,3,23,82,42]
  tokens := { operands := [(0x06003d69, reject), (0x06003d61, enter)] }
  metadata, tables := metadata.tables.toOption.getD [], identities := [bytesOf coreLibraryScope]
  names := { owner := bytesOf original.owner
             signature := bytesOf ("System.Void System.Threading.Monitor::Enter(" ++
               "System.Object,System.Boolean&)") }
  pinned := PinnedIndex.ofIdentities [bytesOf coreLibraryScope] }

private def decoded := Method.ofBody? .scalar {} [(3,.direct 1), (5,.direct 2)]
    (List.replicate 10 true) body original []

private def wrapper : Method := decoded.getD { locals := [], returnsValue := false, code := [] }

/-- Both calls and the branch bind the physical IL and the declared parameters. -/
theorem original_body : bodyMatches body original [] = true ∧ decoded = some wrapper := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms original_body

/-- Changing the branch destination, call token, or width of the byref store breaks the binding. -/
theorem rejects_changed_body :
    bodyMatches { body with bytes := body.bytes.set 4 4 } original [] = false ∧
    bodyMatches { body with bytes := body.bytes.set 12 105 } original [] = false ∧
    bodyMatches { body with bytes := body.bytes.set 18 83 } original [] = false := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms rejects_changed_body

/-- A caller with a writable flag byte and a live object in a different allocation. -/
private def memory (flag : BitVec 8) : Safety.Memory := { Safety.Memory.empty with
  allocations := fun id => match id with
    | 0 => some ⟨.callerStack, ⟨1,1,[]⟩, true, [1]⟩
    | 1 => some ⟨.object ⟨root, []⟩, ⟨8,8,[]⟩, true, []⟩
    | _ => none
  cells := fun _ _ => ⟨flag,true⟩
  nextIdentity := 2, views := [⟨0,0,1,true,true⟩] }

private def gate : Safety.Value := .object (.address ⟨1,0⟩)
private def flagRef : Safety.Value := .reference (.address ⟨0,0⟩)
private def args := [gate,flagRef]
private def frame : Safety.Frame := ⟨2,[],[],0⟩
private def program (rejection acquire : Method) := [wrapper,rejection,acquire]

/-- An initially clear flag reaches the object overload with the original object and memory. -/
theorem clearedFlag (rejection acquire : Method) (fuel : Nat) :
    invoke (program rejection acquire) (fuel + 4) 0 args (memory 0) =
    Safety.run (program rejection acquire) fuel 0 5 args frame [gate] (memory 0) := by
  with_unfolding_all rfl
#print axioms clearedFlag

/-- An initially set flag reaches the rejection helper before the wrapper writes any memory. -/
theorem presetFlag (rejection acquire : Method) (fuel : Nat) :
    invoke (program rejection acquire) (fuel + 3) 0 args (memory 1) =
    Safety.run (program rejection acquire) fuel 0 3 args frame [] (memory 1) := by
  with_unfolding_all rfl
#print axioms presetFlag

private def callEnter : Instruction := wrapper.code[5]?.getD .ret

/-- A fault from the object overload propagates before the byte store. A return resumes at
    instruction six with the child's memory and return values. -/
theorem acquireCall (rejection acquire : Method) (fuel : Nat) (entered : Safety.Memory)
    (childFrame : Safety.Frame)
    (setup : enterFrame acquire [gate] (memory 0) = .ok (childFrame,entered)) :
    Safety.run (program rejection acquire) (fuel + 1) 0 5 args frame [gate] (memory 0) =
      (do let (afterChild, values) ←
            Safety.run (program rejection acquire) fuel 2 0 [gate] childFrame [] entered
          Safety.run (program rejection acquire) fuel 0 6 args frame values afterChild) := by
  have lookup : (program rejection acquire)[0]? = some wrapper := rfl
  have fetched : wrapper.code[5]? = some callEnter := by cil_kernel_rfl
  have called : step wrapper callEnter 5 args frame [gate] (memory 0) =
      .ok (.call 2 [gate] [] (memory 0)) := by cil_kernel_rfl
  have target : (program rejection acquire)[2]? = some acquire := rfl
  simp only [run_succ, lookup, fetched, called, target, setup, Except.mapError, Bind.bind,
    Except.bind, List.append_nil]
#print axioms acquireCall
/-- Returning from the child may change unrelated memory. The original suffix only needs its
    byref to remain live and writable and preserves the entire result of that one-byte write. -/
theorem writeReturnedFlag (reject acquire : Method) (fuel : Nat) (before after : Safety.Memory)
    (live : checkedValue before flagRef = .ok flagRef)
    (written : write before ⟨0,0⟩ [1] 1 = .ok after) :
    Safety.run (program reject acquire) (fuel + 4) 0 6 args frame [] before = .ok (after, []) := by
  have found : (program reject acquire)[0]? = some wrapper := rfl
  have arg : wrapper.code[6]? = some (.ldarg 1) := by cil_kernel_rfl
  have one : wrapper.code[7]? = some (.ldc_i4 1) := by cil_kernel_rfl
  have store : wrapper.code[8]? = some (.stind .i1) := by cil_kernel_rfl
  have ret : wrapper.code[9]? = some .ret := by cil_kernel_rfl
  have access : wrapper.argumentAccess 1 = .value none := by cil_kernel_rfl
  have load : step wrapper (.ldarg 1) 6 args frame [] before =
      .ok (.next 7 [flagRef] frame before) := by
    rw [step_ldarg_value_eq wrapper 6 args frame before 1 [] access]
    change (do let checked ← checkedValue before flagRef
               pure (FrameAction.next 7 [checked] frame before)) = _
    rw [live]
    rfl
  rw [run_next found arg load]
  rw [run_next (op := .ldc_i4 1) (target := 8)
        (values := [.scalar (.i32 1), flagRef]) (nextFrame := frame) (updated := before)
        found one (by rfl)]
  unfold flagRef
  rw [run_next (fuel := fuel + 1) found store
    (step_stind_narrow_of_write (bits := 1) .i1 written (by decide) wrapper 8 args frame [])]
  have voidReturn : wrapper.returnsValue = false := by cil_kernel_rfl
  have scalarReturn : wrapper.returnNarrow = none := by cil_kernel_rfl
  apply run_return (values := []) (updated := after) found ret
  · rw [step_ret_eq, voidReturn, scalarReturn]
    rfl
  · rfl
#print axioms writeReturnedFlag

/-- A callee fault prevents the caller's checked store. -/
theorem acquireFault (rejection acquire : Method) (fuel : Nat) (entered : Safety.Memory)
    (childFrame : Safety.Frame) (fault : LocatedFault)
    (setup : enterFrame acquire [gate] (memory 0) = .ok (childFrame,entered))
    (child : Safety.run (program rejection acquire) fuel 2 0 [gate] childFrame [] entered =
      .error fault) :
    invoke (program rejection acquire) ((fuel + 1) + 4) 0 args (memory 0) = .error fault := by
  rw [clearedFlag, acquireCall rejection acquire fuel entered childFrame setup, child]
  rfl
#print axioms acquireFault

/-- After successful acquisition the wrapper returns with exactly the child's memory updated
    by the caller-authorized one-byte store. -/
theorem acquired (rejection acquire : Method) (fuel : Nat) (entered before after : Safety.Memory)
    (childFrame : Safety.Frame)
    (setup : enterFrame acquire [gate] (memory 0) = .ok (childFrame,entered))
    (child : Safety.run (program rejection acquire) (fuel + 4) 2 0 [gate] childFrame [] entered =
      .ok (before, []))
    (live : checkedValue before flagRef = .ok flagRef)
    (written : write before ⟨0,0⟩ [1] 1 = .ok after) :
    invoke (program rejection acquire) (((fuel + 4) + 1) + 4) 0 args (memory 0) =
      .ok (after, []) := by
  rw [clearedFlag, acquireCall rejection acquire (fuel + 4) entered childFrame setup, child]
  exact writeReturnedFlag rejection acquire fuel before after live written
#print axioms acquired
end Tests.CoreMonitor
