import StrictBinding.PlatformEnums

/-! Follow a qualified type reference through the supplied defining and forwarding assemblies. -/

namespace StrictBinding

open CIL.Extraction

/-- A matching top-level ExportedType must be a unique forwarder to an AssemblyRef. Nested
    exports have an ExportedType as their implementation and belong to their enclosing export. -/
private def forwardedScope? (image : PreparedImage) (space name : List Nat) :
    Except AuditError (Option (Nat × List Nat)) := do
  let exportedType := 0x27
  let cell := image.layout.cellOfRow image.view exportedType
  let mut target := none
  for i in [:image.layout.rowCount exportedType] do
    let row := i + 1
    unless ← stringFound image (← cell row 2) (name ++ [0]) do continue
    unless ← stringFound image (← cell row 3) (space ++ [0]) do continue
    let implementation ← cell row 4
    if implementation % 4 == 2 then continue
    if target.isSome || implementation % 4 != 1 || implementation / 4 == 0 ||
        (← cell row 0) &&& 0x00200000 == 0 then throw (.typeDefMismatch row .typeName)
    let token ← checkedTokenOf Table.assemblyRef (implementation / 4) .rowOverflow
    let identity ← assemblyIdentityAt image.view image.layout token 0
    target := some (row, bytesOf (String.ofList (identity.map Char.ofNat)))
  return target

/-- Find each nested export by its enclosing ExportedType and its exact namespace/name pair. -/
private def nestedExports (image : PreparedImage) (parent : Nat) :
    List (List Nat) → Except AuditError Unit
  | [] => pure ()
  | space :: name :: rest => do
    unless space.isEmpty do throw (.typeDefMismatch parent .typeName)
    let cell := image.layout.cellOfRow image.view Table.exportedType
    let mut selected := none
    for i in [:image.layout.rowCount Table.exportedType] do
      let row := i + 1
      unless (← cell row 4) == parent * 4 + 2 do continue
      unless ← stringFound image (← cell row 2) (name ++ [0]) do continue
      unless ← stringFound image (← cell row 3) (space ++ [0]) do continue
      if selected.isSome || (← cell row 0) != 0 || (← cell row 1) != 0 then
        throw (.typeDefMismatch row .typeName)
      selected := some row
    let some child := selected | throw (.typeDefMismatch parent .typeName)
    nestedExports image child rest
  | _ => throw (.typeDefMismatch parent .typeName)

inductive DefinitionRoute where
  | defined (row : Nat)
  | forwarded (scope : List Nat)

/-- Resolve the outermost name in the current image. A local definition owns its nested types,
    and a forwarder carries the whole enclosing name chain to the referenced assembly. -/
def definitionRoute (image : PreparedImage) (parts : List (List Nat)) :
    Except AuditError DefinitionRoute := do
  let space :: name :: nested := parts | throw (.typeDefMismatch 0 .typeName)
  let outer ← enumDefinition? image 0 [space, name]
  let forward ← forwardedScope? image space name
  match outer, forward with
  | some row, none =>
    if nested.isEmpty then return .defined row
    let some child ← enumDefinition? image row nested | throw (.typeDefMismatch row .typeName)
    return .defined child
  | none, some (exported, target) =>
    nestedExports image exported nested
    return .forwarded target
  | _, _ => throw (.typeDefMismatch 0 .typeName)

/-- The physical definition, or an uncovered assembly when a scope on the path is missing. -/
def findPinnedDefinition (images : List PreparedImage) (parts : List (List Nat))
    (scope : List Nat) : Nat → Except AuditError (Option (PreparedImage × Nat))
  | 0 => throw (.typeDefMismatch 0 .typeName)
  | fuel + 1 => do
    let some image := images.find? (fun image => bytesOf image.identity == scope) | return none
    match ← definitionRoute image parts with
    | .defined row => return some (image, row)
    | .forwarded target => findPinnedDefinition images parts target fuel

/-- Each step uses the assembly named by the reference or preceding physical forwarder. -/
inductive PinnedDefinitionAt (images : List PreparedImage) (parts : List (List Nat)) :
    List Nat → PreparedImage → Nat → Prop where
  | here {scope image row}
      (selected : images.find? (fun candidate => bytesOf candidate.identity == scope) = some image)
      (defined : definitionRoute image parts = .ok (.defined row)) :
      PinnedDefinitionAt images parts scope image row
  | forward {scope image next target row}
      (selected : images.find? (fun candidate => bytesOf candidate.identity == scope) = some image)
      (forwarded : definitionRoute image parts = .ok (.forwarded next))
      (found : PinnedDefinitionAt images parts next target row) :
      PinnedDefinitionAt images parts scope target row

/-- A successful lookup retains the chain of physical references to the defining TypeDef. -/
theorem pinnedDefinitionAt_of_find {images : List PreparedImage} {parts : List (List Nat)}
    {scope : List Nat} {fuel : Nat} {image : PreparedImage} {row : Nat}
    (found : findPinnedDefinition images parts scope fuel = .ok (some (image, row))) :
    PinnedDefinitionAt images parts scope image row := by
  induction fuel generalizing scope with
  | zero => cases found
  | succ fuel ih =>
    simp only [findPinnedDefinition, bind, Except.bind] at found
    cases selected : images.find? (fun candidate => bytesOf candidate.identity == scope) with
    | none => simp [selected, pure, Except.pure] at found
    | some candidate =>
      simp only [selected] at found
      cases route : definitionRoute candidate parts with
      | error fault => simp [route] at found
      | ok routeValue =>
        cases routeValue with
        | defined position =>
          simp [route, pure, Except.pure] at found
          obtain ⟨rfl, rfl⟩ := found
          exact .here selected route
        | forwarded next =>
          exact .forward selected route (ih (by simpa [route] using found))
#print axioms pinnedDefinitionAt_of_find

/-- A successful traversal contains the result of every selected input. -/
theorem read_member {α β : Type} {read : α → Except AuditError β}
    {inputs : List α} {outputs : List β} {item : α} (member : item ∈ inputs)
    (checked : inputs.mapM read = .ok outputs) :
    ∃ result ∈ outputs, read item = .ok result := by
  induction inputs generalizing outputs with
  | nil => cases member
  | cons first rest ih =>
    rw [List.mapM_cons] at checked
    obtain ⟨head, firstRead, checked⟩ := CIL.Safety.except_bind_ok checked
    obtain ⟨tail, restRead, joined⟩ := CIL.Safety.except_bind_ok checked
    have same : head :: tail = outputs := Except.ok.inj joined
    subst outputs
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨head, by simp, firstRead⟩
    · obtain ⟨result, found, read⟩ := ih later restRead
      exact ⟨result, List.mem_cons_of_mem _ found, read⟩
#print axioms read_member

end StrictBinding
