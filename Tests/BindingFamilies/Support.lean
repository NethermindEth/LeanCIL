import CIL.Safety.SymbolicExecution

/-!
# Reviewed integer binding families

These small shared execution proofs are independent of extraction. Generated bindings must
prove the complete method equality, the exact managed signature and that the method reads both
arguments without narrowing before instantiation.
-/

namespace BindingSupport
open CIL CIL.Safety

/-- The fixed body of an equality or inequality method, including boolean return narrowing. -/
@[cil_code] def equalityBody (profile : FeatureProfile) (environment : LayoutEnvironment)
    (declared : DeclaredSignature) (positive : Bool) : Method := {
  profile, environment, declared, locals := [], returnsValue := true,
  code := [.ldarg 0, .ldarg 1, .ceq] ++
    (if positive then [] else [.ldc_i4 0, .ceq]) ++ [.ret] }

/-- The fixed body of one binary bitwise method. -/
@[cil_code] def bitwiseBody (profile : FeatureProfile) (environment : LayoutEnvironment)
    (declared : DeclaredSignature) (operation : Instruction) : Method := {
  profile, environment, declared, locals := [], returnsValue := true,
  code := [.ldarg 0, .ldarg 1, operation, .ret] }

/-- The equality family computes its boolean in arbitrary caller memory. -/
theorem equal32 (program : Program) (profile : FeatureProfile)
    (environment : LayoutEnvironment)
    (declared : DeclaredSignature)
    (returned : declared.returnType = .atom Extraction.runtimeScope "System.Boolean")
    (first : (equalityBody profile environment declared true).argumentAccess 0 = .value none)
    (second : (equalityBody profile environment declared true).argumentAccess 1 = .value none)
    (found : program[0]? = some (equalityBody profile environment declared true))
    (left right : W32) (memory : Safety.Memory) :
    invoke program 5 0 [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 (if left = right then 1 else 0))]) := by
  rcases declared with ⟨receiver, parameters, returnType⟩
  cases returned
  -- The stepped body is the unfolded literal, so the argument facts are stated over it too.
  simp only [cil_code, ↓reduceIte, List.cons_append, List.nil_append] at first second
  cil_checked_steps [found, first, second]
#print axioms equal32

/-- The opposite polarity computes inequality rather than weakening the equality contract. -/
theorem different64 (program : Program) (profile : FeatureProfile)
    (environment : LayoutEnvironment)
    (declared : DeclaredSignature)
    (returned : declared.returnType = .atom Extraction.runtimeScope "System.Boolean")
    (first : (equalityBody profile environment declared false).argumentAccess 0 = .value none)
    (second : (equalityBody profile environment declared false).argumentAccess 1 = .value none)
    (found : program[0]? = some (equalityBody profile environment declared false))
    (left right : W64) (memory : Safety.Memory) :
    invoke program 7 0 [.scalar (.i64 left), .scalar (.i64 right)] memory =
      .ok (memory, [.scalar (.i32 (if left ≠ right then 1 else 0))]) := by
  rcases declared with ⟨receiver, parameters, returnType⟩
  cases returned
  -- The stepped body is the unfolded literal, so the argument facts are stated over it too.
  simp only [cil_code, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
    at first second
  cil_checked_steps [found, first, second]
  all_goals (by_cases same : left = right <;> simp [same])
#print axioms different64

/-- The conjunction family computes the complete 32-bit result. -/
theorem and32 (program : Program) (profile : FeatureProfile)
    (environment : LayoutEnvironment)
    (declared : DeclaredSignature)
    (returned : declared.returnType = .atom Extraction.runtimeScope "System.Int32")
    (first : (bitwiseBody profile environment declared .and).argumentAccess 0 = .value none)
    (second : (bitwiseBody profile environment declared .and).argumentAccess 1 = .value none)
    (found : program[0]? = some (bitwiseBody profile environment declared .and))
    (left right : W32) (memory : Safety.Memory) :
    invoke program 5 0 [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 (left &&& right))]) := by
  rcases declared with ⟨receiver, parameters, returnType⟩
  cases returned
  -- The stepped body is the unfolded literal, so the argument facts are stated over it too.
  simp only [cil_code] at first second
  cil_checked_steps [found, first, second]
#print axioms and32

/-- The exclusive-or family computes the complete 64-bit result. -/
theorem xor64 (program : Program) (profile : FeatureProfile)
    (environment : LayoutEnvironment)
    (declared : DeclaredSignature)
    (returned : declared.returnType = .atom Extraction.runtimeScope "System.UInt64")
    (first : (bitwiseBody profile environment declared .xor).argumentAccess 0 = .value none)
    (second : (bitwiseBody profile environment declared .xor).argumentAccess 1 = .value none)
    (found : program[0]? = some (bitwiseBody profile environment declared .xor))
    (left right : W64) (memory : Safety.Memory) :
    invoke program 5 0 [.scalar (.i64 left), .scalar (.i64 right)] memory =
      .ok (memory, [.scalar (.i64 (left ^^^ right))]) := by
  rcases declared with ⟨receiver, parameters, returnType⟩
  cases returned
  -- The stepped body is the unfolded literal, so the argument facts are stated over it too.
  simp only [cil_code] at first second
  cil_checked_steps [found, first, second]
#print axioms xor64

/-- A byte-declared bitwise body truncates the result that the full-width helper preserves. -/
theorem byte_bitwise_truncates (memory : Safety.Memory) :
    invoke [bitwiseBody .scalar {}
      { returnType := .atom Extraction.runtimeScope "System.Byte" } .and]
      5 0 [.scalar (.i32 300), .scalar (.i32 511)] memory =
        .ok (memory, [.scalar (.i32 44)]) := rfl
#print axioms byte_bitwise_truncates

end BindingSupport
