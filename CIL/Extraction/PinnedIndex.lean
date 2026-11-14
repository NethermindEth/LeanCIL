import CIL.Extraction.MetadataResolution
import Lean

/-! Materialized package pin indexes whose complete identity binding the kernel checks. -/

namespace CIL.Extraction

open Lean Meta Elab Term

mutual

/-- Quote every prefix node with literal map children, without evaluating lookup expressions. -/
private partial def quotePrefixes : AssemblyPrefixes → MetaM Expr
  | .node terminal children => do
    let children ← quoteChildren children.inner.inner
    let number : Expr := mkConst ``Nat
    let value : Expr := mkConst ``AssemblyPrefixes
    let family := mkLambda `byte .default number value
    let order ← synthInstance (mkApp (mkConst ``Ord [.zero]) number)
    let comparator := mkApp2 (mkConst ``compare [.zero]) number order
    let dependent := mkAppN (mkConst ``Std.DTreeMap.Raw.mk [.zero, .zero])
      #[number, family, comparator, children]
    let map := mkAppN (mkConst ``Std.TreeMap.Raw.mk [.zero, .zero])
      #[number, value, comparator, dependent]
    return mkApp2 (mkConst ``AssemblyPrefixes.node) (toExpr terminal) map

/-- Quote the stored sizes, keys and subtrees of one prefix node's child map. -/
private partial def quoteChildren :
    Std.DTreeMap.Internal.Impl Nat (fun _ => AssemblyPrefixes) → MetaM Expr
  | .leaf => do
    let family := mkLambda `byte .default (mkConst ``Nat) (mkConst ``AssemblyPrefixes)
    pure (mkApp2 (mkConst ``Std.DTreeMap.Internal.Impl.leaf [.zero, .zero])
      (mkConst ``Nat) family)
  | .inner size key value left right => do
    let family := mkLambda `byte .default (mkConst ``Nat) (mkConst ``AssemblyPrefixes)
    pure (mkAppN (mkConst ``Std.DTreeMap.Internal.Impl.inner [.zero, .zero])
      #[mkConst ``Nat, family, toExpr size, toExpr key, ← quotePrefixes value,
        ← quoteChildren left, ← quoteChildren right])

end

/-- Materialize a closed package pin index; its constructor checks the complete derivation. -/
elab "cil_pin_index " identities:term : term => do
  let listType := mkApp (mkConst ``List [.zero])
    (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
  let expression ← elabTermEnsuringType identities listType
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let values ← unsafe evalExpr (List (List Nat)) listType expression
  let prefixes ← quotePrefixes ((values.map assemblyStem).foldl AssemblyPrefixes.insert {})
  let proof ← mkEqRefl prefixes
  return mkApp3 (mkConst ``PinnedIndex.mk) expression prefixes proof

end CIL.Extraction
