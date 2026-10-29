import CIL.Instructions

/-!
# Method embeddings

An expected method body embeds into an actual one when every live expected
instruction appears in the actual body at a mapped pc, with every code target
mapped the same way. Instructions the expected body marks `.unsupported` impose
nothing, so dead code may be inserted, removed or renumbered. Every condition is a
list equality or Boolean test the kernel decides by evaluation; no equality
instance on `Op` is involved.

`CIL.Safety.Embedding` proves that a successful run of the expected body is one of the
actual body, so a proof about a hand-written body transfers to the extracted method.
`EmbedsDeadLocals` also lets the actual body declare trailing locals that frame entry
creates without allocating.
-/

namespace CIL

/-- Replaces every code target of an instruction by its image under `r`. -/
def Op.relabel (r : Nat → Nat) : Op → Op
  | .nativeBinary op => .nativeBinary (op.relabel r)
  | .bgt t => .bgt (r t) | .ble t => .ble (r t) | .bleu t => .bleu (r t)
  | .branch t => .branch (r t) | .switch ts => .switch (ts.map r)
  | .brzero t => .brzero (r t) | .brnonzero t => .brnonzero (r t)
  | .bltu t => .bltu (r t) | .bgeu t => .bgeu (r t) | .bgtu t => .bgtu (r t)
  | .bge t => .bge (r t) | .blt t => .blt (r t) | .beq t => .beq (r t) | .bne t => .bne (r t)
  | op => op

/-- Every code target of an instruction, in operand order. -/
def Op.targets : Op → List Nat
  | .nativeBinary op => op.targets
  | .bgt t | .ble t | .bleu t | .branch t | .brzero t | .brnonzero t
  | .bltu t | .bgeu t | .bgtu t | .bge t | .blt t | .beq t | .bne t => [t]
  | .switch ts => ts
  | _ => []

-- Together these fail if a branch constructor is added to one of `relabel` and `targets` only.
theorem Op.targets_relabel (r : Nat → Nat) (op : Op) :
    (op.relabel r).targets = op.targets.map r := by
  induction op <;> simp_all [Op.relabel, Op.targets]

theorem Op.relabel_eq_self (r : Nat → Nat) (op : Op)
    (fixed : ∀ target ∈ op.targets, r target = target) :
    op.relabel r = op := by
  induction op <;> simp_all [Op.relabel, Op.targets]
  exact (List.map_congr_left fixed).trans (List.map_id _)

theorem Op.relabel_of_targets_nil (r : Nat → Nat) (op : Op) (none : op.targets = []) :
    op.relabel r = op :=
  op.relabel_eq_self r (by simp [none])

/-- False only for instructions that never resume at the next pc, including after a call. -/
def Op.continues : Op → Bool
  | .managed (.call _ _ true) => false
  | .branch _ | .tailCall .. | .ret _ | .throw _ | .unsupported _ => false
  | _ => true

/-- `.unsupported` faults whenever it executes, so it constrains nothing. -/
def Op.live : Op → Bool
  | .unsupported _ => false
  | _ => true

namespace Embedding

/-- The actual pc of expected pc `p`; pcs outside the map go to `limit`. -/
def pcAt (map : List Nat) (limit p : Nat) : Nat := map.getD p limit

/-- The pc renaming that `map` induces on a body with `limit` instructions. -/
abbrev rename (map : List Nat) (limit : Nat) : Nat → Nat := pcAt map limit

/-- A live expected instruction at `pc`, the actual pc it maps to, and the actual pc
    its successor maps to. -/
structure Site where
  pc : Nat
  image : Nat
  next : Nat
  op : Op

/-- Live sites of `code` numbered from `pc`, reading `map` in step; one pass over both lists. -/
def sites (limit : Nat) : Nat → List Op → List Nat → List Site
  | _, [], _ => []
  | pc, op :: rest, map =>
    if op.live then
      ⟨pc, map.headD limit, map.tail.headD limit, op⟩ :: sites limit (pc + 1) rest map.tail
    else sites limit (pc + 1) rest map.tail

/-- `code[q]?` for each `q`, walking `code` once while the pcs increase; `rest` is
    `code.drop start`. -/
def pick (code : List Op) : List Op → Nat → List Nat → List (Option Op)
  | _, _, [] => []
  | rest, start, q :: qs =>
    if start ≤ q then
      let tail := rest.drop (q - start)
      tail.head? :: pick code tail q qs
    else code[q]? :: pick code rest start qs

/-- The static descriptor a `staticAddress` or `staticValue` at `pc` resolves to. -/
def staticAt (body : Method) (pc : Nat) : Option StaticDescriptor :=
  (body.staticSites.find? (fun site => site.1 == pc)).map Prod.snd

end Embedding

open Embedding in
/-- `expected` embeds into `actual` under the pc map `map`. Non-code fields agree,
    except that static sites may move as long as each live instruction resolves the
    same descriptor and the program-wide descriptor list is unchanged. -/
structure Embeds (expected actual : Method) (map : List Nat) : Prop where
  profile : actual.profile = expected.profile
  returnsValue : actual.returnsValue = expected.returnsValue
  locals : actual.locals = expected.locals
  localKinds : actual.localKinds = expected.localKinds
  vectorLocals : actual.vectorLocals = expected.vectorLocals
  opaqueVectorLocals : actual.opaqueVectorLocals = expected.opaqueVectorLocals
  vectorArgs : actual.vectorArgs = expected.vectorArgs
  parameterHomes : actual.parameterHomes = expected.parameterHomes
  descriptors : actual.staticSites.map Prod.snd = expected.staticSites.map Prod.snd
  entry : rename map actual.code.length 0 = 0
  code : pick actual.code actual.code 0
      ((sites actual.code.length 0 expected.code map).map Site.image) =
    (sites actual.code.length 0 expected.code map).map
      fun site => some (site.op.relabel (rename map actual.code.length))
  statics :
    (sites actual.code.length 0 expected.code map).map (fun site => staticAt actual site.image) =
      (sites actual.code.length 0 expected.code map).map (fun site => staticAt expected site.pc)
  flow : (sites actual.code.length 0 expected.code map).all
    (fun site => !site.op.continues || site.next == site.image + 1) = true

/-- Method `index` of `program` has a body that `expected` embeds into. -/
def MethodEmbeds (program : Program) (index : Nat) (expected : Method) : Prop :=
  ∃ actual map, program[index]? = some actual ∧ Embeds expected actual map

/-- `actual` with the locals and local kinds of `expected` in place of its own. -/
def Method.withLocalsOf (actual expected : Method) : Method :=
  { actual with locals := expected.locals, localKinds := expected.localKinds }

/-- True for a local that frame entry creates without allocating memory: a reference or
    supported span initialized to its empty value or left unmodeled. -/
def rootLocal : LocalKind → Value → Bool
  | .reference, .nullRef | .reference, .unmodeled => true
  | .span width _, .nullRef | .span width _, .unmodeled => decide (0 < width ∧ width < 2^64)
  | _, _ => false

/-- True when `kinds` and `initials` describe the same number of locals, each a root local. -/
def rootLocals (kinds : List LocalKind) (initials : List Value) : Bool :=
  kinds.length == initials.length && (kinds.zip initials).all fun (kind, initial) =>
    rootLocal kind initial

open Embedding in
/-- `expected` embeds into `actual` under `map` once `actual`'s locals past `expected`'s are
    dropped. Those extra locals must be trailing root locals, which allocate nothing, so every
    other local and every allocation keeps its place; opaque locals must lie among the kept
    ones, and `actual` may have no parameter homes, which the frame places after the locals. -/
structure EmbedsDeadLocals (expected actual : Method) (map : List Nat) : Prop where
  embeds : Embeds expected (actual.withLocalsOf expected) map
  locals : actual.locals = expected.locals ++ actual.locals.drop expected.locals.length
  localKinds :
    actual.localKinds = expected.localKinds ++ actual.localKinds.drop expected.localKinds.length
  initialized : expected.localKinds.length = expected.locals.length
  dead : rootLocals (actual.localKinds.drop expected.localKinds.length)
    (actual.locals.drop expected.locals.length) = true
  opaqueVectorLocals : expected.opaqueVectorLocals.all (· < expected.localKinds.length) = true
  parameterHomes : actual.parameterHomes = []

/-- Method `index` of `program` has a body that `expected` embeds into once its trailing dead
    root locals are dropped. -/
def MethodEmbedsDeadLocals (program : Program) (index : Nat) (expected : Method) : Prop :=
  ∃ actual map, program[index]? = some actual ∧ EmbedsDeadLocals expected actual map

end CIL
