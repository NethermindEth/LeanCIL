import StrictBinding.Bind

/-! Compact JSON fields read by the strict binding audit from a pinned contracts sidecar. -/

namespace StrictBinding.ContractSidecar
open StrictBinding

/-- Compact JSON emitted by the default contracts writer. Floating-point numbers, surrogate
    pairs, non-ASCII wire bytes and insignificant whitespace are outside this checked subset. -/
inductive Node where
  | object (fields : List (String × Node))
  | array (items : List Node)
  | string (text : String)
  | integer (value : Int)
  | boolean (value : Bool)
  | null

private def hex (c : Nat) : Option Nat :=
  if 48 ≤ c && c ≤ 57 then some (c-48)
  else if 65 ≤ c && c ≤ 70 then some (c-55)
  else if 97 ≤ c && c ≤ 102 then some (c-87)
  else none

private def quoted (s : List Nat) (acc : List Char) : Option (String × List Nat) :=
  match s with
  | [] => none
  | 34 :: rest => some (String.ofList acc.reverse, rest)
  | 92 :: 117 :: a :: b :: c :: d :: rest => do
    let code := 4096 * (← hex a) + 256 * (← hex b) + 16 * (← hex c) + (← hex d)
    guard (code < 0xd800 || code > 0xdfff)
    quoted rest (Char.ofNat code :: acc)
  | 92 :: c :: rest => do
    let code ← ([(34,34),(92,92),(47,47),(98,8),(102,12),(110,10),(114,13),(116,9)]
      : List (Nat × Nat)).lookup c
    quoted rest (Char.ofNat code :: acc)
  | c :: rest => do
    guard (32 ≤ c && c < 128 && c != 92)
    quoted rest (Char.ofNat c :: acc)

private def digit (c : Nat) := 48 ≤ c && c ≤ 57

private def number (s : List Nat) : Option (Node × List Nat) := do
  let neg := s.head? == some 45
  let input := if neg then s.drop 1 else s
  let digits := input.takeWhile digit
  guard (!digits.isEmpty && (digits.head? != some 48 || digits.length == 1))
  let magnitude : Nat := digits.foldl (fun (acc : Nat) d => 10*acc + (d-48)) 0
  let n : Int := magnitude
  return (.integer (if neg then -n else n), input.drop digits.length)

mutual
  private def value : Nat → List Nat → Option (Node × List Nat)
    | 0, _ => none
    | k+1, bytes =>
      match bytes with
      | 123 :: 125 :: rest => some (.object [],rest)
      | 123 :: rest => members k rest []
      | 91 :: 93 :: rest => some (.array [],rest)
      | 91 :: rest => elements k rest []
      | 34 :: rest => do
        let (decoded,tail) ← quoted rest []
        return (.string decoded,tail)
      | 116 :: 114 :: 117 :: 101 :: rest => some (.boolean true,rest)
      | 102 :: 97 :: 108 :: 115 :: 101 :: rest => some (.boolean false,rest)
      | 110 :: 117 :: 108 :: 108 :: rest => some (.null,rest)
      | _ => number bytes

  private def members : Nat → List Nat → List (String × Node) → Option (Node × List Nat)
    | k+1, 34 :: bytes, acc => do
      let (name, 58 :: tail) ← quoted bytes [] | none
      guard (!(acc.any fun kv => kv.1 == name))
      let (node,rest) ← value k tail
      let all := (name,node) :: acc
      match rest with
      | 44 :: next => members k next all
      | 125 :: next => some (.object all.reverse,next)
      | _ => none
    | _, _, _ => none

  private def elements : Nat → List Nat → List Node → Option (Node × List Nat)
    | k+1, bytes, acc => do
      let (node,rest) ← value k bytes
      match rest with
      | 44 :: next => elements k next (node :: acc)
      | 93 :: next => some (.array (node :: acc).reverse,next)
      | _ => none
    | _, _, _ => none
end

/-- Parse exactly one complete compact document from its pinned bytes. -/
def read (image : ImageBytes) : Option Node := do
  let view ← (ImageView.ofImage image).toOption
  let bytes ← (view.bytes 0 image.length).toOption
  let (node,[]) ← value (bytes.length+1) bytes | none
  return node

/-- Select a field of an object with unique member names. -/
def field (obj : Node) (key : String) : Option Node := do
  let .object fields := obj | none
  fields.lookup key

/-- Read a string field, preserving its decoded Unicode contents. -/
def text (obj : Node) (key : String) : Option String := do
  let .string result ← field obj key | none
  return result

/-- Require a unique export with the complete selected identity. -/
def member (root : Node) (identity : String) : Option Node := do
  let .array exports ← field root "exports" | none
  let [entry] := exports.filter (fun entry => text entry "identity" == some identity) | none
  return entry

end StrictBinding.ContractSidecar
