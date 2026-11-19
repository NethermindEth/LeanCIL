import CIL.Extraction.UnsafeModels
import CIL.Extraction.LayoutUses

/-! Runtime models for allocation-relative offsets of checked Unsafe references. -/

namespace CIL.Extraction

/-- The two references whose byte displacement is measured. -/
private def offsetPair (element : TypeExpr) : List TypeExpr := [.byref element, .byref element]

/-- Byte displacements have native signed integer type. -/
private def displacement (_ : TypeExpr) : TypeExpr := .atom runtimeScope "System.IntPtr"

/-- Unsafe.ByteOffset computes a displacement between references to a sized element. -/
def unsafeByteOffsetModel (reader : CallLayouts) (method : MethodRef) :
    Option RuntimeModel :=
  unsafeGuarded (unsafeSignature reader method offsetPair displacement) (.memory .byteOffset)

/-- The offset unit and direction of an Unsafe displacement. -/
private inductive Displacement where
  | addElements | subtractElements | addBytes | subtractBytes

/-- The four closed parameter shapes of the displacement overloads. -/
private inductive OffsetForm where
  | int32 | native | unsigned | pointer
  deriving DecidableEq

/-- The runtime type of the displacement parameter. -/
private def OffsetForm.offsetName : OffsetForm → String
  | .int32 | .pointer => "System.Int32"
  | .native => "System.IntPtr"
  | .unsigned => "System.UIntPtr"

/-- The input and result address type of the overload. -/
private def OffsetForm.address (form : OffsetForm) (element : TypeExpr) : TypeExpr :=
  if form == .pointer then .pointer .void else .byref element

/-- The parameter types of the overload at its method argument. -/
private def OffsetForm.parameters (form : OffsetForm) (element : TypeExpr) : List TypeExpr :=
  [form.address element, .atom runtimeScope form.offsetName]

/-- The method has this overload's static generic signature on the exact Unsafe owner. -/
private def OffsetForm.accepts (form : OffsetForm) (method : MethodRef) : Bool :=
  (unsafeArgument method).any fun element =>
    method.parameters == form.parameters element && method.returnType == form.address element

/-- The checked operation for the element size and signedness of the displacement. -/
private def Displacement.model (kind : Displacement) (signed : Bool) (width : Nat) :
    RuntimeModel :=
  match kind with
  | .addElements => .memory (.add width signed)
  | .subtractElements => .memory (.add (subtractionStride width) signed)
  | .addBytes => .memory (.add 1 signed)
  | .subtractBytes => .referenceSubtract

/-- One selected overload binds its open MemberRef and reads the checked size of its element. -/
private def offsetOverload (name : String) (kind : Displacement) (form : OffsetForm) :
    ModelOverload :=
  let address := if form == .pointer then "System.Void*" else "!!0&"
  { operand := unsafeOperand name address s!"{address},{form.offsetName}"
      (unsafeDeclaration form.parameters form.address)
    accepts := form.accepts
    resolve := fun reader method => do
      let element ← unsafeArgument method
      let width ← (reader.valueShape element).size?
      return kind.model (form != .unsigned) width }

/-- An offset family reserves every closed reference of its name, including unresolved members. -/
private def offsetEntry (key : MetadataName) (name : String) (kind : Displacement) : ModelEntry :=
  let forms : List OffsetForm := match kind with
    | .addElements | .subtractElements => [.int32, .native, .unsigned, .pointer]
    | .addBytes | .subtractBytes => [.native, .unsigned]
  { opcode := .call, owner := unsafeOwner, name := key, ownsName := true,
    overloads := forms.map (offsetOverload name kind) }

/-- Whether scalar flow may use the managed-reference stack kind for a void-pointer offset. -/
def pointerDisplacementSite (site : CallSite) : Bool :=
  site.method.returnType == .pointer .void &&
    ((site.method.name == name!"Add" &&
      (offsetEntry name!"Add" "Add" .addElements).bindsSite site) ||
     (site.method.name == name!"Subtract" &&
      (offsetEntry name!"Subtract" "Subtract" .subtractElements).bindsSite site))

/-- The checked offset operations that keep their call. -/
def unsafeOffsetEntries : List ModelEntry :=
  [unsafeEntry name!"ByteOffset" "ByteOffset" "System.IntPtr" "!!0&,!!0&"
      (unsafeDeclaration offsetPair displacement) unsafeByteOffsetModel,
   offsetEntry name!"Add" "Add" .addElements,
   offsetEntry name!"Subtract" "Subtract" .subtractElements,
   offsetEntry name!"AddByteOffset" "AddByteOffset" .addBytes,
   offsetEntry name!"SubtractByteOffset" "SubtractByteOffset" .subtractBytes]

/-- A unique overload selected from a family's rows belongs to that family. -/
private theorem selected_mem (rows : List ModelOverload) (method : MethodRef)
    (row : ModelOverload) (found : ModelEntry.select?.select method rows = some row) :
    row ∈ rows := by
  induction rows with
  | nil => cases found
  | cons first rest ih =>
    simp only [ModelEntry.select?.select] at found
    split at found
    · split at found
      · contradiction
      · cases found
        exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih found)

#print axioms selected_mem

/-- Every displacement overload executes a memory offset or reference subtraction. -/
private theorem offsetEntry_yields {property : RuntimeModel → Prop}
    (memory : ∀ op, property (.memory op)) (subtract : property .referenceSubtract)
    (key name kind) : (offsetEntry key name kind).Yields property := by
  intro reader method model found
  obtain ⟨row, selected, resolved⟩ := Option.bind_eq_some_iff.mp found
  have member := selected_mem _ _ _ selected
  change row ∈ List.map _ _ at member
  obtain ⟨form, _, rfl⟩ := List.mem_map.mp member
  simp only [offsetOverload, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at resolved
  obtain ⟨_, _, _, _, rfl⟩ := resolved
  cases kind <;> first | exact memory _ | exact subtract

#print axioms offsetEntry_yields

/-- The offset entries execute checked memory operations or reference subtraction. -/
theorem unsafeOffsetEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ op, property (.memory op)) (subtract : property .referenceSubtract) :
    ∀ entry ∈ unsafeOffsetEntries, entry.Yields property := by
  simp only [unsafeOffsetEntries, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨?_, offsetEntry_yields memory subtract _ _ _, offsetEntry_yields memory subtract _ _ _,
    offsetEntry_yields memory subtract _ _ _, offsetEntry_yields memory subtract _ _ _⟩
  intro environment method model found
  rw [unsafeGuarded_eq (admitted := unsafeSignature environment method offsetPair displacement)
    (model := .memory .byteOffset) found]
  exact memory _

#print axioms unsafeOffsetEntries_yields

end CIL.Extraction
