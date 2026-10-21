import CIL.Extraction.Generics

namespace CIL.Extraction

private def runtimeScope : String :=
  "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"

private def plainChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '/' || c == '`'

/-- Identifier-only names exclude modifiers, arrays and other decorated metadata spellings. -/
private def plainName (name : List Char) : Bool := !name.isEmpty && name.all plainChar

private def plainScope (scope : List Char) : Bool := !scope.isEmpty && !scope.contains ':'

/-- Split `scope::name` at its first colon; any other colon makes the identity unusable. -/
private def splitIdentity : List Char → List Char → Option (List Char × List Char)
  | scope, ':' :: ':' :: name => some (scope.reverse, name)
  | scope, c :: rest => if c == ':' then none else splitIdentity (c :: scope) rest
  | _, [] => none

private def leaf (scope name : List Char) : Option (List Char × List Char) :=
  if plainScope scope && plainName name then some (scope, name) else none

/-- A named type as its referencing scope and full name. -/
def namedType : TypeExpr → Option (List Char × List Char)
  | .atom scope name | .constructor scope name => leaf scope.toList name.toList
  | .aggregate identity _ | .enum identity _ => do
    let (scope, name) ← splitIdentity [] identity.toList
    leaf scope name
  | _ => none

private def constructed : TypeExpr → Bool
  | .pointer _ | .byref _ | .apply .. => true
  | _ => false

private def both : Option Bool → Option Bool → Option Bool
  | some false, _ | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- Runtime identity of two closed metadata types, or `none` when metadata cannot decide it.
    Full names are never forwarded, but one name in two scopes may denote one type. -/
def sameRuntimeType : TypeExpr → TypeExpr → Option Bool
  | .pointer x, .pointer y | .byref x, .byref y => sameRuntimeType x y
  | .apply f x, .apply g y => both (sameRuntimeType f g) (sameRuntimeType x y)
  | a, b =>
    -- `void` is serialized without its scope, so equal spellings do not establish identity.
    if a == b then (if a == .void then none else some true) else
    match namedType a, namedType b with
    | some (scope, name), some (scope', name') =>
      if name != name' then some false else if scope == scope' then some true else none
    | _, _ =>
      if (constructed a || (namedType a).isSome) && (constructed b || (namedType b).isSome) then
        some false
      else none

private def typeHandle : RawInstruction → Option TypeExpr
  | ⟨_, 208, .type type⟩ => some type
  | _ => none

private def typeMethod (name signature : String) (parameters : Nat) : CallSite := {
  declaringType := .atom runtimeScope "System.Type", name,
  target := .external (runtimeScope ++ "::" ++ signature),
  typeArguments := [], parameterCount := parameters, hasThis := false, returnsValue := true }

private def getTypeFromHandle : CallSite :=
  typeMethod "GetTypeFromHandle" "System.Type System.Type::GetTypeFromHandle(System.RuntimeTypeHandle)" 1

private def typeFromHandle (i : RawInstruction) : Bool :=
  i.opcode == 40 && i.operand == .call getTypeFromHandle

/-- `some true` for `op_Equality`, `some false` for `op_Inequality`. -/
private def typeComparison (i : RawInstruction) : Option Bool :=
  if i.opcode != 40 then none
  else if i.operand == .call (typeMethod "op_Equality" "System.Boolean System.Type::op_Equality(System.Type,System.Type)" 2) then some true
  else if i.operand == .call (typeMethod "op_Inequality" "System.Boolean System.Type::op_Inequality(System.Type,System.Type)" 2) then some false
  else none

/-- The exact `typeof(A) == typeof(B)` encoding and its decided result. -/
def typeTest (a b c d e : RawInstruction) : Option Bool := do
  let left ← typeHandle a
  let right ← typeHandle c
  if !typeFromHandle b || !typeFromHandle d then none
  let equality ← typeComparison e
  let same ← sameRuntimeType left right
  return same == equality

/-- Raw instructions that are admitted only as part of a decided type test. -/
def typeTestInstruction (i : RawInstruction) : Bool :=
  i.opcode == 208 || match i.operand with
    | .call site => match site.declaringType with
      | .atom _ "System.Type" =>
        site.name == "GetTypeFromHandle" || site.name == "op_Equality" || site.name == "op_Inequality"
      | _ => false
    | _ => false

inductive TypeTestRole where
  /-- The first token load: emits nothing, and may be a branch target. -/
  | head
  /-- Later operand loads: emit nothing, and are entered only from the preceding instruction. -/
  | interior
  /-- The comparison: pushes the decided Boolean. -/
  | result (value : Bool)
  deriving DecidableEq, Repr

/-- Assign `pending` roles first; each step consumes one instruction, so the walk is structural. -/
def typeTestRolesFrom : List (Option TypeTestRole) → List RawInstruction → List (Option TypeTestRole)
  | _, [] => []
  | role :: pending, _ :: tail => role :: typeTestRolesFrom pending tail
  | [], a :: tail => match tail with
    | b :: c :: d :: e :: _ => match typeTest a b c d e with
      | some value => some .head ::
          typeTestRolesFrom [some .interior, some .interior, some .interior, some (.result value)] tail
      | none => none :: typeTestRolesFrom [] tail
    | _ => none :: typeTestRolesFrom [] tail

/-- Roles derived from the raw body alone; extraction evidence cannot add or move a fold. -/
def typeTestRoles (code : List RawInstruction) : List (Option TypeTestRole) := typeTestRolesFrom [] code

/-- A non-fallthrough edge may enter a type test only at its first instruction. -/
def typeTestEntry (roles : List (Option TypeTestRole)) (target : Nat) : Bool :=
  match roles[target]? with
  | some (some .interior) | some (some (.result _)) => false
  | _ => true

end CIL.Extraction
