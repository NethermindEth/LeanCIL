import CIL.Safety.LocalCalls
import CIL.Safety.LoopScaffold
import CIL.SIMD.Evaluation256Lemmas

/-!
# Vector helper output in mixed private storage

An actual checked vector helper initializes a private output beside an initialized scalar.
The caller reloads that vector and exits its allocated frame. The shared local-call rule
carries storage authority, updated contents and confinement through the helper invocation.
-/

namespace Tests.VectorLocalCalls
open CIL.Safety

/-- The helper adds four pairs of lanes and writes the vector through its output argument. -/
@[cil_code] def helper : CIL.Method :=
  { locals := [], returnsValue := false,
    code := [.arg 2, .arg 0, .arg 1, .intrinsic (.vector (.add64 256)) 2,
      .memory .store256, .ret] }

/-- The helper receives two saved vector values and one writable output reference. -/
structure Inputs where
  left : BitVec 256
  right : BitVec 256
  output : Reference

/-- Each lane wraps independently; the output need not have initialized contents. -/
def contract : MethodContract Inputs Unit where
  args input := [.scalar (.v256 input.left), .scalar (.v256 input.right),
    .reference (.address input.output)]
  results _ := []
  pre input memory := access memory input.output 32 1 true = .ok ()
  footprint input := [(input.output, 32)]
  post input _ final _ := read final input.output 32 1 =
    .ok (numberBytes (CIL.Vector.zip256 (· + ·) input.left input.right).toNat 32)

/-- The checked helper implements its lane-wise contract with the existing intrinsic and
    byte-write theorems. -/
theorem helper_holds {program : CIL.Program} {callee : Nat}
    (found : program[callee]? = some helper) : contract.Holds program callee := by
  intro input memory writable
  let value := CIL.Vector.zip256 (· + ·) input.left input.right
  obtain ⟨final, written⟩ := write_succeeds
    (bytes := numberBytes value.toNat 32)
    (by simpa only [contract, numberBytes_length] using writable)
  have formed := access_reference_valid _ _ _ _ _ writable
  have readback := write_readback _ _ _ _ _ written
  cil_contract_steps [found, formed, step_store256_of_write written,
    CIL.Vector.intrinsic_add256]
  exact ⟨Confined.write written (by simp [numberBytes_length]), (), rfl,
    by simpa only [contract, numberBytes_length] using readback⟩
#print axioms helper_holds

/-- A scalar home keeps its value while the helper initializes the adjacent vector home. -/
@[cil_code] def caller : CIL.Method :=
  { locals := [.i64 42, .unmodeled], localKinds := [.word64, .vector256],
    returnsValue := true,
    code := [.arg 0, .arg 1, .ldloca 1, .call 1 3, .local 1, .ret] }

bind_entry entry (memory : Memory) (left right : BitVec 256)
    (formed : memory.WellFormed) := caller
  with [.scalar (.v256 left), .scalar (.v256 right)] from memory allocating formed

/-- Allocating, calling, loading and leaving retain confinement to the caller's private homes. -/
theorem caller_invokes (memory : Memory) (formed : memory.WellFormed)
    (left right : BitVec 256) :
    WP (Execution (fun fuel => invoke [caller, helper] fuel 0
      [.scalar (.v256 left), .scalar (.v256 right)] memory))
      (fun (final, values) => Confined [] memory final ∧
        values = [.scalar (.v256 (CIL.Vector.zip256 (· + ·) left right))]) := by
  obtain ⟨wordHome, vectorHome, entered, setup⟩ := entry.checked memory left right formed
  have context := setup.frame []
  let frame := entry.frame memory wordHome vectorHome
  have slot : frame.locals[1]? = some (.bytes .vector256 vectorHome) := rfl
  have address := context.form_home 1 slot
  have suffix : WP (Execution (fun fuel => run [caller, helper] fuel 0 3
      [.scalar (.v256 left), .scalar (.v256 right)] frame
      [.reference (.address vectorHome), .scalar (.v256 right), .scalar (.v256 left)] entered))
      (fun (final, values) => Confined [] memory final ∧
        values = [.scalar (.v256 (CIL.Vector.zip256 (· + ·) left right))]) := by
    apply WP.local_call context (helper_holds (callee := 1) (by rfl)) ⟨left, right, vectorHome⟩
      (by rfl) (by rfl) (by cil_checked_step [address]) (context.homes.writable_at slot)
      1 .vector256 vectorHome slot rfl
      (fun _ => .v256 (CIL.Vector.zip256 (· + ·) left right))
      (fun _ => (CIL.Vector.zip256 (· + ·) left right).toNat) (fun _ => rfl)
      (fun _ _ result => result)
    intro final output result updated
    have loaded := updated.snapshots.load (index := 1)
      (.v256 (CIL.Vector.zip256 (· + ·) left right)) rfl
      (body := caller) (pc := 4)
      (args := [.scalar (.v256 left), .scalar (.v256 right)]) (stack := [])
    cil_contract_steps [loaded]
    exact ⟨(updated.leave setup.setup).1, rfl⟩
  apply WP.enter (by rfl) (by rfl) setup.setup
  cil_contract_steps [entry.frame] until suffix
#print axioms caller_invokes

end Tests.VectorLocalCalls
