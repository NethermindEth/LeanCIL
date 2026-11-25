import Extracted
import CIL.Safety.Execution

/-! Overloaded enum parameters bind the namespace and simple name of each physical declaration. -/

namespace ExampleProof
open CIL CIL.Extraction

/-- An enum parameter in the fixture assembly with the given TypeDef columns. -/
private def enumParam (ns name : MetadataName) : TypeExpr :=
  .enum { assembly := ⟨name!"Examples", ⟨1, 0, 0, 0⟩, name!"", none⟩,
          typeNamespace := ns, name } .signed32

/-- Substituting the other enum in both signatures must fail at the original call token. -/
private def rejectsParameter (selected replacement : TypeExpr) : Bool := Id.run do
  let body := Extracted.method0Body
  let some (token, .call site) := body.tokens.operands.find? (fun entry => match entry.2 with
    | .call site => site.parameterTypes == [selected]
    | _ => false) | return false
  let altered := RawOperand.call
    { site with method.parameters := [replacement], declared.parameters := [replacement] }
  let operands := body.tokens.operands.map fun entry =>
    if entry.1 == token then (token, altered) else entry
  return match checkBody { body with tokens := ⟨operands⟩ } Extracted.method0Original [] with
    | .error (.metadata (.operandMismatch rejected)) => rejected == token
    | _ => false

/-- Each overload rejects the other's enum, and their array elements retain the distinction. -/
theorem physicalParameters :
    let qualified := enumParam name!"Rows" name!"Choice"
    let dotted := enumParam name!"" name!"Rows.Choice"
    rejectsParameter qualified dotted = true ∧ rejectsParameter dotted qualified = true ∧
    sameRuntimeType qualified dotted = some false ∧
    (arrayElementType qualified == arrayElementType dotted) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cil_kernel_rfl
#print axioms physicalParameters

/-- Replace the Assembly row's final string index with the offset of a fresh culture entry. -/
private def withCulture (assembly : AssemblyMetadata) (culture : String) : AssemblyMetadata :=
  let width := assembly.header.widths.string
  let offset := assembly.strings.foldl (fun end_ entry => max end_ (entry.1 + entry.2.length)) 0
  let index := (List.range width).map fun i => (offset >>> (8 * i)) % 256
  let row := assembly.assemblyRow.take (assembly.assemblyRow.length - width) ++ index
  { assembly with assemblyRow := row, strings := assembly.strings ++ [(offset, bytesOf culture ++ [0])] }

/-- Check each overload's proposed assembly culture against its defining row at its call token. -/
private def checksCulture (actual : String) (claimed : MetadataName) (agree : Bool) : Bool := Id.run do
  let original := Extracted.method0Body
  let assembly := withCulture original.metadata.own.assembly actual
  let body := { original with metadata.own.assembly := assembly }
  let .ok env := body.environment | return false
  let calls := body.tokens.operands.filterMap fun (token, operand) =>
    match operand with
    | .call site => some (token, site)
    | _ => none
  return calls.length == 2 && calls.all fun (token, site) => Id.run do
    let [.enum identity underlying] := site.parameterTypes | return false
    let changed := TypeExpr.enum { identity with assembly.culture := claimed } underlying
    let operand := RawOperand.call
      { site with method.parameters := [changed], declared.parameters := [changed] }
    return match checkEntry env 0 token operand with
      | .ok _ => agree
      | .error (.operandMismatch bad) => !agree && bad == token
      | _ => false

/-- Both culture spellings are valid for a matching claim. Each substitution fails. -/
theorem physicalAssemblyCultures :
    checksCulture "" name!"" true ∧ checksCulture "neutral" name!"neutral" true ∧
      checksCulture "" name!"neutral" false ∧ checksCulture "neutral" name!"" false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cil_kernel_rfl
#print axioms physicalAssemblyCultures

/-- Both overloads execute in CLR evaluation order and return their respective digits. -/
theorem correctness :
    Safety.invoke Extracted.program 64 0 [] Safety.Memory.empty =
      .ok (Safety.Memory.empty, [.scalar (.i32 12)]) := by cil_kernel_rfl
#print axioms correctness

end ExampleProof
