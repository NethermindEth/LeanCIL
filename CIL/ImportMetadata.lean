import CIL.TypeExpr
import CIL.Extraction.Layout

namespace CIL.Extraction

/-- Exact closed metadata at an imported call; aggregate table indices are not public identities. -/
structure ImportSignature where
  owner : TypeExpr
  name : String
  arguments : List TypeExpr
  returnType : TypeExpr
  parameters : List TypeExpr
  deriving DecidableEq, Repr

/-- Published metadata and the independently selected DLL's metadata are checked as values. -/
structure ImportLayoutCatalog where
  published : List RawLayout := []
  actual : List RawLayout := []
  computed : Array ComputedLayout := #[]
  deriving DecidableEq, Repr

def importPrimitive : TypeExpr → Bool
  | .atom scope name =>
    scope == "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" &&
      name ∈ ["System.SByte", "System.Byte", "System.Boolean", "System.Int16", "System.UInt16",
        "System.Char", "System.Int32", "System.UInt32", "System.Int64", "System.UInt64",
        "System.IntPtr", "System.UIntPtr"]
  | _ => false

def importParameter (layouts : List RawLayout) : TypeExpr → Bool
  | .byref (.atom scope name) =>
    importPrimitive (.atom scope name) || layouts.any (fun layout => layout.identity == scope ++ "::" ++ name)
  | type => importPrimitive type

def ImportSignature.supported (signature : ImportSignature) (layouts : List RawLayout) : Bool :=
  (match signature.owner with | .atom _ _ => true | _ => false) &&
  !signature.name.isEmpty && signature.arguments.all importPrimitive &&
  (signature.returnType == .void || importPrimitive signature.returnType) &&
  signature.parameters.all (importParameter layouts)

def ImportLayoutCatalog.Valid (catalog : ImportLayoutCatalog) (architecture : Architecture) : Prop :=
  catalog.published = catalog.actual ∧ LayoutsValid catalog.actual catalog.computed architecture ∧
  (catalog.actual.map RawLayout.identity).Nodup ∧
  catalog.actual.all (fun layout => !layout.identity.isEmpty) = true

instance (catalog : ImportLayoutCatalog) (architecture : Architecture) :
    Decidable (catalog.Valid architecture) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem ImportLayoutCatalog.Valid.metadata {catalog : ImportLayoutCatalog} {architecture : Architecture}
    (valid : catalog.Valid architecture) : catalog.published = catalog.actual := valid.1

theorem ImportLayoutCatalog.Valid.layouts {catalog : ImportLayoutCatalog} {architecture : Architecture}
    (valid : catalog.Valid architecture) : LayoutsValid catalog.actual catalog.computed architecture := valid.2.1

#print axioms ImportLayoutCatalog.Valid.metadata
#print axioms ImportLayoutCatalog.Valid.layouts
end CIL.Extraction
