import CIL.Extraction.RuntimeModels

/-!
# Runtime models a summary relies on

A `call` or `newobj` at a pc with no link runs the model `runtimeModel` gives its method in
place of a body, so a proof that steps such a call relies on the deployment's runtime
implementing that method as the model. `Method.modelledSites` lists these sites of one body.
`ModelsListed` states that a list of calls with their models covers each site of a root and of
every method the root's links reach (`Reaches`); calls enter other methods only through links.
`ModelsResolve` states that the runtime table gives each listed call its listed model. Decoded
summaries carry a listing and take `ModelsResolve` as the premise of their contract, so their
statement names each runtime model the proof relies on, and each reuse states it.
-/

namespace CIL

/-- The method indices the link table of `body` enters, in table order. -/
def Method.callees (body : Method) : List Nat :=
  body.links.flatMap fun entry => entry.2.callees

/-- The opcode and method of a `call` or `newobj`, the instructions a pc with no link runs
    through a runtime model; `none` for every other instruction. -/
def Instruction.modelledSite? (op : Instruction) : Option (CallOpcode × Extraction.MethodRef) := by
  cases op
  case call method _ => exact some (.call, method)
  case newobj method => exact some (.newobj, method)
  all_goals exact none

end CIL

namespace CIL.Safety
open CIL.Extraction

/-- A runtime method a body calls at a pc with no link, with the model the checked interpreter
    runs in place of its body. -/
structure ModelledCall where
  /-- `call` or `newobj`. -/
  opcode : CallOpcode
  /-- The method the instruction names. -/
  method : MethodRef
  /-- The model `runtimeModel` gives the call. -/
  model : RuntimeModel
  deriving DecidableEq, Repr

/-- The opcode and method of `op` at `pc` of `body` when it is a `call` or `newobj` with no link
    there, a site at which the checked interpreter runs a runtime model. -/
def _root_.CIL.Method.modelledSiteAt (body : Method) (pc : Nat) (op : Instruction) :
    Option (CallOpcode × MethodRef) :=
  match body.linkAt pc with
  | none => op.modelledSite?
  | some _ => none

/-- The sites of `body` that run a runtime model, in code order. -/
def _root_.CIL.Method.modelledSites (body : Method) : List (CallOpcode × MethodRef) :=
  body.code.zipIdx.filterMap fun (op, pc) => body.modelledSiteAt pc op

/-- A `call` or `newobj` at a pc with no link is a modelled site of its body. -/
theorem _root_.CIL.Method.mem_modelledSites {body : Method} {pc : Nat} {op : Instruction}
    {site : CallOpcode × MethodRef} (found : body.code[pc]? = some op)
    (named : op.modelledSite? = some site) (unlinked : body.linkAt pc = none) :
    site ∈ body.modelledSites :=
  List.mem_filterMap.mpr ⟨(op, pc), List.mk_mem_zipIdx_iff_getElem?.mpr found, by
    simp only [Method.modelledSiteAt, unlinked, named]⟩

#print axioms CIL.Method.mem_modelledSites

/-- `callee` is `root` or a method the links of a method `root` reaches name. -/
inductive Reaches (program : Program) (root : Nat) : Nat → Prop
  /-- The root reaches itself. -/
  | refl : Reaches program root root
  /-- A reached method reaches each method its links name. -/
  | link {caller callee : Nat} {body : Method} (reached : Reaches program root caller)
      (present : program[caller]? = some body) (named : callee ∈ body.callees) :
      Reaches program root callee

/-- `models` has a call for the opcode and method of every modelled site of `root` and of each
    method `root` reaches. With `ModelsResolve`, the model each such site runs is the listed one
    (`ModelsListed.call`), so a proof about `root` relies on no runtime model outside `models`.
    A longer list is accepted. -/
def ModelsListed (program : Program) (root : Nat) (models : List ModelledCall) : Prop :=
  ∀ reached body, Reaches program root reached → program[reached]? = some body →
    ∀ site ∈ body.modelledSites, ∃ call ∈ models, call.opcode = site.1 ∧ call.method = site.2

/-- The runtime table gives each listed call its listed model in `environment`. A summary
    listing `models` relies on the deployment's runtime implementing each such method as its
    model, and takes this as the premise of its contract. -/
def ModelsResolve (environment : LayoutEnvironment) (models : List ModelledCall) : Prop :=
  ∀ call ∈ models, runtimeModel environment call.opcode call.method = some call.model

instance (environment : LayoutEnvironment) (models : List ModelledCall) :
    Decidable (ModelsResolve environment models) :=
  inferInstanceAs (Decidable (∀ call ∈ models, _))

/-- A summary that lists no runtime model relies on none. -/
theorem ModelsResolve.nil (environment : LayoutEnvironment) : ModelsResolve environment [] :=
  fun _ listed => nomatch listed

#print axioms ModelsResolve.nil

/-- A list resolves when its first call does and the rest do. An extraction's
    `method{n}_model{pc}` facts state the first premise for each of its modelled sites. -/
theorem ModelsResolve.cons {environment : LayoutEnvironment} {call : ModelledCall}
    {rest : List ModelledCall}
    (first : runtimeModel environment call.opcode call.method = some call.model)
    (others : ModelsResolve environment rest) : ModelsResolve environment (call :: rest) := by
  intro listed member
  rcases List.mem_cons.mp member with rfl | member
  · exact first
  · exact others listed member

#print axioms ModelsResolve.cons

/-- Each listed call of a shorter list resolves as it does in the longer one. -/
theorem ModelsResolve.mono {environment : LayoutEnvironment} {models more : List ModelledCall}
    (resolved : ModelsResolve environment more) (within : ∀ call ∈ models, call ∈ more) :
    ModelsResolve environment models :=
  fun call listed => resolved call (within call listed)

#print axioms ModelsResolve.mono

/-- The opcode and method of the site a listed call stands for. -/
def ModelledCall.site (call : ModelledCall) : CallOpcode × MethodRef :=
  (call.opcode, call.method)

/-- Whether each method at `indices` of `program` names only methods at `indices` in its
    links. It compares indices only, so `decide` settles it cheaply. -/
def linksWithin (program : Program) (indices : List Nat) : Bool :=
  indices.all fun index => (program[index]?).all fun body => body.callees.all indices.contains

/-- The modelled sites of the methods at `indices` of `program`, in index and code order. -/
def sitesAt (program : Program) (indices : List Nat) : List (CallOpcode × MethodRef) :=
  indices.flatMap fun index => (program[index]?.map Method.modelledSites).getD []

/-- A set of indices closed under links whose modelled sites are, in order, those of `models`
    lists the sites of every method a member reaches. `decide` closes `closed` and `rfl`
    closes `sites` for a concrete program: `rfl` compares method names as literals, where
    `decide` would evaluate a string comparison character by character. -/
theorem ModelsListed.of_sites {program : Program} {root : Nat} {models : List ModelledCall}
    (indices : List Nat) (member : root ∈ indices) (closed : linksWithin program indices = true)
    (sites : sitesAt program indices = models.map ModelledCall.site) :
    ModelsListed program root models := by
  have within : ∀ reached, Reaches program root reached → reached ∈ indices := by
    intro reached path
    induction path with
    | refl => exact member
    | link _ present named caller =>
      have entry := List.all_eq_true.mp closed _ caller
      simp only [present, Option.all_some, List.all_eq_true, List.contains_iff_mem] at entry
      exact entry _ named
  intro reached body path present site listed
  have gathered : site ∈ sitesAt program indices :=
    List.mem_flatMap.mpr ⟨reached, within reached path, by simpa [present] using listed⟩
  rw [sites, List.mem_map] at gathered
  obtain ⟨call, member, rfl⟩ := gathered
  exact ⟨call, member, rfl, rfl⟩

#print axioms ModelsListed.of_sites

/-- A listing remains one when more calls are added to it. -/
theorem ModelsListed.mono {program : Program} {root : Nat} {models more : List ModelledCall}
    (listed : ModelsListed program root models) (within : ∀ call ∈ models, call ∈ more) :
    ModelsListed program root more := by
  intro reached body path present site member
  obtain ⟨call, listedCall, same⟩ := listed reached body path present site member
  exact ⟨call, within call listedCall, same⟩

#print axioms ModelsListed.mono

/-- A listing carries to a program whose methods are the originals under a map that keeps each
    body's links and modelled sites, such as a change of profile. -/
theorem ModelsListed.map {program : Program} {root : Nat} {models : List ModelledCall}
    {change : Method → Method} (listed : ModelsListed program root models)
    (callees : ∀ body, (change body).callees = body.callees)
    (sites : ∀ body, (change body).modelledSites = body.modelledSites) :
    ModelsListed (program.map change) root models := by
  have back : ∀ reached, Reaches (program.map change) root reached →
      Reaches program root reached := by
    intro reached path
    induction path with
    | refl => exact .refl
    | link _ present named caller =>
      simp only [List.getElem?_map, Option.map_eq_some_iff] at present
      obtain ⟨original, found, rfl⟩ := present
      exact .link caller found (callees original ▸ named)
  intro reached body path present site member
  simp only [List.getElem?_map, Option.map_eq_some_iff] at present
  obtain ⟨original, found, rfl⟩ := present
  exact listed reached original (back reached path) found site (sites original ▸ member)

#print axioms ModelsListed.map

/-- A modelled site of a reached method runs a listed model where the listed calls resolve in
    the method's environment. -/
theorem ModelsListed.site {program : Program} {root caller pc : Nat}
    {models : List ModelledCall} {body : Method} {op : Instruction} {opcode : CallOpcode}
    {method : MethodRef} (listed : ModelsListed program root models)
    (resolved : ModelsResolve body.environment models)
    (reached : Reaches program root caller) (present : program[caller]? = some body)
    (found : body.code[pc]? = some op) (named : op.modelledSite? = some (opcode, method))
    (unlinked : body.linkAt pc = none) :
    ∃ model, runtimeModel body.environment opcode method = some model ∧
      ⟨opcode, method, model⟩ ∈ models := by
  obtain ⟨⟨callOpcode, callMethod, model⟩, member, sameOpcode, sameMethod⟩ :=
    listed caller body reached present _ (Method.mem_modelledSites found named unlinked)
  dsimp only at sameOpcode sameMethod
  subst sameOpcode sameMethod
  exact ⟨model, resolved _ member, member⟩

#print axioms ModelsListed.site

/-- At a reached method's `call` with no link, the interpreter runs a listed model. -/
theorem ModelsListed.call {program : Program} {root caller pc : Nat}
    {models : List ModelledCall} {body : Method} {method : MethodRef} {prefixes : CallPrefixes}
    (listed : ModelsListed program root models)
    (resolved : ModelsResolve body.environment models)
    (reached : Reaches program root caller) (present : program[caller]? = some body)
    (found : body.code[pc]? = some (.call method prefixes)) (unlinked : body.linkAt pc = none) :
    ∃ model, runtimeModel body.environment .call method = some model ∧
      ⟨.call, method, model⟩ ∈ models :=
  listed.site resolved reached present found rfl unlinked

#print axioms ModelsListed.call

/-- At a reached method's `newobj` with no link, the interpreter runs a listed model. -/
theorem ModelsListed.newobj {program : Program} {root caller pc : Nat}
    {models : List ModelledCall} {body : Method} {method : MethodRef}
    (listed : ModelsListed program root models)
    (resolved : ModelsResolve body.environment models)
    (reached : Reaches program root caller) (present : program[caller]? = some body)
    (found : body.code[pc]? = some (.newobj method)) (unlinked : body.linkAt pc = none) :
    ∃ model, runtimeModel body.environment .newobj method = some model ∧
      ⟨.newobj, method, model⟩ ∈ models :=
  listed.site resolved reached present found rfl unlinked

#print axioms ModelsListed.newobj

end CIL.Safety
