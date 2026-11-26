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

/-- Materialize a closed package pin index; its constructor checks the complete derivation. -/
elab "cil_pin_index " identities:term : term => do
  let listType := mkApp (mkConst ``List [.zero]) (mkConst ``AssemblyName)
  let expression ← elabTermEnsuringType identities listType
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let values ← unsafe evalExpr (List AssemblyName) listType expression
  let unit := fun (_ : Unit) => pure (Lean.mkConst ``Unit.unit)
  let names ← quoteMap (mkConst ``MetadataName) (mkConst ``Unit) toExpr unit
    (indexPinNames values)
  let exact ← quoteMap (mkConst ``AssemblyName) (mkConst ``Unit) toExpr unit (indexPins values)
  return mkAppN (mkConst ``PinnedIndex.mk)
    #[expression, names, ← mkEqRefl names, exact, ← mkEqRefl exact]

end CIL.Extraction
