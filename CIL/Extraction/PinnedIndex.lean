import CIL.Extraction.MetadataResolution
import Lean

/-! Materialized package pin indexes whose complete identity binding the kernel checks. -/

namespace CIL.Extraction

open Lean Meta Elab Term

/-- Quote the shape, keys and values of a closed map so kernel lookups traverse its branches. -/
private def quoteMap {Key Value : Type} [Ord Key] (keyType valueType : Expr)
    (keyExpr : Key -> Expr) (valueExpr : Value -> MetaM Expr)
    (entries : Std.TreeMap.Raw Key Value) : MetaM Expr := do
  let family := mkLambda `key .default keyType valueType
  let rec nodes : Std.DTreeMap.Internal.Impl Key (fun _ => Value) -> MetaM Expr
    | .leaf => pure (mkApp2 (mkConst ``Std.DTreeMap.Internal.Impl.leaf [.zero, .zero])
        keyType family)
    | .inner size key value left right => do
      return mkAppN (mkConst ``Std.DTreeMap.Internal.Impl.inner [.zero, .zero])
        #[keyType, family, toExpr size, keyExpr key, <- valueExpr value, <- nodes left,
          <- nodes right]
  let order <- synthInstance (mkApp (mkConst ``Ord [.zero]) keyType)
  let comparator := mkApp2 (mkConst ``compare [.zero]) keyType order
  let tree := mkAppN (mkConst ``Std.DTreeMap.Raw.mk [.zero, .zero])
    #[keyType, family, comparator, <- nodes entries.inner.inner]
  return mkAppN (mkConst ``Std.TreeMap.Raw.mk [.zero, .zero])
    #[keyType, valueType, comparator, tree]

/-- Quote every prefix node with its literal map of byte children. -/
private partial def quotePrefixes : AssemblyPrefixes -> MetaM Expr
  | .node terminal children => do
    let map <- quoteMap (mkConst ``Nat) (mkConst ``AssemblyPrefixes) toExpr quotePrefixes children
    return mkApp2 (mkConst ``AssemblyPrefixes.node) (toExpr terminal) map

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
  let bytes := mkApp (mkConst ``List [.zero]) (mkConst ``Nat)
  let exact <- quoteMap bytes (mkConst ``Unit) toExpr (fun _ => pure (mkConst ``Unit.unit))
    (indexPins values)
  return mkAppN (mkConst ``PinnedIndex.mk) #[expression, prefixes, proof, exact, <- mkEqRefl exact]

end CIL.Extraction
