import CIL.Extraction.MetadataResolution

/-!
# Generic contract identity components

Exact, length-framed UTF-8 components bind a generic imported contract to its open metadata
signature and its closed arguments. Definition bytes use hexadecimal inside the outer signature.
-/

namespace CIL.Extraction

/-- A UTF-8 component framed by its byte count. -/
def contractPart (bytes : List Nat) : List Nat :=
  bytesOf (toString bytes.length) ++ [58] ++ bytes

/-- Uppercase hexadecimal preserves definition bytes without signature punctuation. -/
def contractHex (bytes : List Nat) : List Nat :=
  let digit (value : Nat) := if value < 10 then 48 + value else 55 + value
  bytes.flatMap fun byte => [digit (byte / 16), digit (byte % 16)]

/-- The class/value marker carried by a named signature type, when known. -/
def contractValueKind : TypeKind → Option Bool
  | .valueType | .enumType _ => some true
  | .classType | .interfaceType => some false
  | .importedOwner => none
  | .external hint => hint

/-- The scoped named component and its signature class/value marker. -/
def contractAtom (scope name : List Nat) (valueType : Bool) : List Nat :=
  bytesOf "atom:" ++ contractPart scope ++ contractPart name ++
    [if valueType then 118 else 114]

/-- The exact supported open type key; an unknown kind or unsupported wrapper has no key. -/
def contractTypeKey (frame : Frame) : Nat → ResolvedType → Option (List Nat)
  | 0, _ => none
  | _ + 1, .primitive code => do
    let scope ← frame.corlib
    let name ← primitiveName code
    pure (contractAtom scope name (code != 1 && code != 0x0E && code != 0x1C))
  | _ + 1, .named named => do
    pure (contractAtom named.scope named.name (← contractValueKind named.kind))
  | _ + 1, .var index => some (bytesOf ("type:" ++ toString index))
  | _ + 1, .mvar index => some (bytesOf ("method:" ++ toString index))
  | fuel + 1, .byref element => do
    pure (bytesOf "byref:" ++ contractPart (← contractTypeKey frame fuel element))
  | _, _ => none

/-- The closed name of a supported contract type, with indexed method argument names. -/
def contractClosedName (argumentNames : SearchTree (List Nat)) :
    Nat → ResolvedType → Option (List Nat)
  | 0, _ => none
  | fuel + 1, type@(.primitive _) | fuel + 1, type@(.named _) =>
    cecilName false (fuel + 1) type
  | _ + 1, .mvar index => argumentNames.find? index
  | fuel + 1, .byref element =>
    (· ++ [38]) <$> contractClosedName argumentNames fuel element
  | _, _ => none

/-- The primitive integer codes admitted as closed imported method arguments. -/
def contractInteger (type : ResolvedType) : Bool :=
  match type with
  | .primitive code => (2 ≤ code && code ≤ 11) || code == 0x18 || code == 0x19
  | .named named => named.scope == runtimeScopeBytes &&
      contractValueKind named.kind == some true &&
      ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0x18, 0x19].any fun code =>
        primitiveName code == some named.name)
  | _ => false

end CIL.Extraction
