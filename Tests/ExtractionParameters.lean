import CIL.Extraction.Generics

open CIL CIL.Extraction

namespace Tests.ExtractionParameters

def raw : RawArguments := {
  arguments := List.replicate 4 (.field .unsigned32)
  locals := [.field .unsigned64]
  code := [.load 0, .store 3, .address 1, .load 3] }
def reachable : List Bool := [true, true, true, true]
def method : Method := {
  code := [.arg 0, .stloc 2, .ldloca 1, .local 2]
  locals := [.i64 0], localKinds := [.word64]
  parameterHomes := [(1, .word32), (3, .word32)]
  returnsValue := true }

example : requiredHomeIndices raw reachable = [1, 3] := by decide
example : ParameterHomesValid #[] raw reachable method := by decide
example : validateParameterHomes #[] raw reachable { method with parameterHomes := [] } = false := by decide
example : validateParameterHomes #[] raw reachable
    { method with parameterHomes := [(3, .word32), (1, .word32)] } = false := by decide
example : validateParameterHomes #[] raw reachable
    { method with code := [.arg 0, .stloc 2, .ldloca 1, .arg 3] } = false := by decide
example : validateParameterHomes #[] raw reachable
    { method with code := [.arg 0, .stloc 1, .ldloca 1, .local 2] } = false := by decide
example : validateParameterHomes #[] raw reachable
    { method with localKinds := [.word32] } = false := by decide
example : validateParameterHomes #[] raw reachable
    { method with locals := [] } = false := by decide
example : validateParameterHomes #[] raw [true, true, true] method = false := by decide
example : validateArgumentOp raw reachable .other true (.local 2) = false := by decide
example : validateArgumentOp raw reachable .other true (.arg 0) = false := by decide
-- A local operand must name one of the declared locals: two locals admit index 1 and reject 2.
def twoLocals : RawArguments := { raw with locals := [.field .unsigned64, .field .unsigned64] }
example : validateArgumentOpIn twoLocals [] .other true (.local 1) = true := by decide
example : validateArgumentOpIn twoLocals [] .other true (.local 2) = false := by decide
example : validateParameterHomes #[] { raw with code := [.load 0, .store 9, .address 1, .load 3] }
    reachable method = false := by decide

-- The address of a span parameter's home is the address instruction, whose step pushes the
-- view the home holds; a load of the home in its place is rejected.
def spanArgument : RawArguments :=
  { arguments := [.span 4 true], locals := [], code := [.address 0] }
example : validateArgumentOpIn spanArgument [0] (.address 0) true (.ldloca 0) = true := by
  decide
example : validateArgumentOpIn spanArgument [0] (.address 0) true (.local 0) = false := by
  decide

-- Dead argument stores create no home; their emitted site must actually be unsupported.
def pruned : RawArguments := {
  arguments := [.field .unsigned32], locals := [], code := [.store 0, .load 0] }
example : ParameterHomesValid #[] pruned [false, true]
    { code := [.unsupported "pruned", .arg 0], locals := [], returnsValue := true } := by decide
example : validateParameterHomes #[] pruned [false, true]
    { code := [.stloc 0, .arg 0], locals := [], returnsValue := true } = false := by decide

/-- An `Option` `mapM` relates each output entry to the input entry at the same index. -/
private theorem mapM_entry {α β : Type} {f : α → Option β} :
    ∀ {inputs : List α} {outputs : List β}, inputs.mapM f = some outputs →
      ∀ {index : Nat} {output : β}, outputs[index]? = some output →
        ∃ input, inputs[index]? = some input ∧ f input = some output
  | [], outputs, mapped, index, output, found => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at mapped
    subst mapped
    simp at found
  | input :: inputs, outputs, mapped, index, output, found => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at mapped
    obtain ⟨head, headMapped, tail, tailMapped, rfl⟩ := mapped
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact ⟨input, rfl, headMapped⟩
    | succ index => exact mapM_entry tailMapped found
#print axioms mapM_entry

/-- Whether a slot kind is a span slot. -/
private def spanSlot : LocalKind → Bool
  | .span .. => true
  | _ => false

/-- Whether metadata storage is span storage, of primitive or aggregate elements. -/
private def spanStored : StorageType → Bool
  | .span .. | .aggregateSpan .. => true
  | _ => false

/-- Only span storage gives a span slot. -/
private theorem storageKind_span {computed : Array ComputedLayout} {storage : StorageType}
    {kind : LocalKind} (bound : storageKind computed storage = some kind) :
    spanSlot kind = spanStored storage := by
  revert bound
  cases storage <;> (try cases ‹FieldType›) <;>
    simp [storageKind, spanSlot, spanStored, bind, Option.bind_eq_some_iff] <;>
    (intros; subst_vars; rfl)
#print axioms storageKind_span

/-- Native dispatch storage is never span storage, and its types are never spans. -/
private theorem nativeDispatchStorage_span {context : NativeDispatchContext} {type : TypeExpr}
    {localIndex : Option Nat} {pointer : Nat → Bool} {storage : StorageType}
    (stored : nativeDispatchStorage context type localIndex pointer = some storage) :
    spanStored storage = false ∧ spanLocal type = false := by
  revert stored
  cases type <;> simp [nativeDispatchStorage, nativeDispatchInteger, bind, Option.bind_eq_some_iff,
    spanLocal, spanStorage] <;> (intros; subst_vars; rfl)
#print axioms nativeDispatchStorage_span

/-- A generic instance's storage is span storage exactly for a span type. -/
private theorem typeStorage_apply_span {layouts : List RawLayout} {scope name : String}
    {element : TypeExpr} {storage : StorageType}
    (stored : typeStorage layouts (.apply (.constructor scope name) element) = some storage) :
    spanStored storage = spanLocal (.apply (.constructor scope name) element) := by
  unfold spanLocal
  cases spanned : spanStorage (.apply (.constructor scope name) element) with
  | none =>
    simp only [typeStorage, spanned] at stored
    simp only [Option.isSome_none]
    revert stored
    cases storage <;> simp only [spanStored] <;> (repeat' split) <;> simp
  | some span =>
    have shape : spanStored span = true := by
      revert spanned
      simp only [spanStorage, bind]
      split
      · simp
      · rw [Option.bind_eq_some_iff]
        rintro ⟨_, -, found⟩
        simp only [pure, Option.some.injEq] at found
        subst found
        rfl
    simp only [typeStorage, spanned] at stored
    simp only [Option.isSome_some]
    cases element
    case aggregate identity index =>
      revert stored
      simp only [bind, Option.bind_eq_some_iff]
      rintro ⟨_, -, found⟩
      split at found
      · simp at found
      · simp only [pure, Option.some.injEq] at found
        subst found
        rfl
    all_goals
      simp only [pure, Option.some.injEq] at stored
      subst stored
      exact shape
#print axioms typeStorage_apply_span

/-- Closed metadata storage is span storage exactly for a span type. -/
private theorem typeStorage_span {layouts : List RawLayout} {type : TypeExpr}
    {storage : StorageType} (stored : typeStorage layouts type = some storage) :
    spanStored storage = spanLocal type := by
  cases type
  case apply constructor element =>
    cases constructor
    case constructor scope name => exact typeStorage_apply_span stored
    all_goals simp [typeStorage] at stored
  all_goals unfold typeStorage at stored
  all_goals (try split at stored) <;> cases storage <;>
    simp_all [spanStored, spanLocal, spanStorage, bind, Option.bind_eq_some_iff]
  all_goals
    (try obtain ⟨_, -, stored⟩ := stored)
    (repeat' split at stored) <;> simp_all
#print axioms typeStorage_span

/-- A local's storage is span storage exactly for a span type, whether native dispatch or the
    metadata type chose it. -/
private theorem orElse_span {native : Option StorageType} {layouts : List RawLayout}
    {type : TypeExpr} {storage : StorageType}
    (nativeSpan : ∀ dispatched, native = some dispatched →
      spanStored dispatched = false ∧ spanLocal type = false)
    (chosen : (native <|> typeStorage layouts type) = some storage) :
    spanStored storage = spanLocal type := by
  cases native with
  | none => exact typeStorage_span chosen
  | some dispatched =>
    obtain ⟨notStored, notSpan⟩ := nativeSpan dispatched rfl
    cases Option.some.inj chosen
    rw [notStored, notSpan]
#print axioms orElse_span

/-- On a method whose argument storage and slot kinds bind, a local's slot is a span slot exactly
    when its declared type is a span, so the slot `localAddress` reads and the declared type the
    extractor reads agree on span locals. -/
theorem span_kind_iff_spanLocal {layouts : List RawLayout} {computed : Array ComputedLayout}
    {closed : RawMethod} {raw : RawArguments} {kinds : List LocalKind} {index : Nat}
    {type : TypeExpr} {kind : LocalKind}
    (arguments : closedArguments layouts closed = some raw)
    (bound : raw.locals.mapM (storageKind computed) = some kinds)
    (declared : closed.locals[index]? = some type) (slot : kinds[index]? = some kind) :
    spanLocal type = (kind matches .span ..) := by
  obtain ⟨storage, stored, kindOf⟩ := mapM_entry bound slot
  rw [closedArguments_eq_list] at arguments
  simp only [closedArgumentsWith, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
    at arguments
  obtain ⟨parameters, -, locals, localsMapped, code, -, rfl⟩ := arguments
  obtain ⟨⟨declaredType, position⟩, entry, chosen⟩ := mapM_entry localsMapped stored
  rw [List.getElem?_zipIdx, declared] at entry
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at entry
  obtain ⟨rfl, rfl⟩ := entry
  have storedSpan := orElse_span (fun _ dispatched => nativeDispatchStorage_span dispatched) chosen
  rw [← storedSpan, ← storageKind_span kindOf]
  cases kind <;> rfl
#print axioms span_kind_iff_spanLocal

end Tests.ExtractionParameters
