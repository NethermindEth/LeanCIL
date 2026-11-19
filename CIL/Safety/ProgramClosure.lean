import CIL.Safety.Linking
import CIL.Safety.DecodedSummary

/-!
# Closures of a method and their transfer between programs

`Program.closure` takes out of a program the methods a root reaches through link tables, renumbered
from the root at 0, and keeps them only when every link of the renumbered methods enters one of
them. The result is closed (`Program.closure_closed`) and relocates back into its program
(`Program.closure_relocates`), and `Program.closureEvidence` gives the evidence records that decode
to it. `Program.closure` reads each method from the list; `closureWith` takes any lookup, and
`Program.closure_eq_closureWith` lets a proof decide a closure over an index of the program, such as
`Extracted.programIndex`, instead. A contract proved for a program carries to its closure
(`MethodContract.Holds.restrict`), and `DecodedSummary.relocate` carries a summary proved over a
closure to any program that holds the closure's methods at relocated indices
(`RelocatesInto.of_decoded`).
-/

namespace CIL
open CIL.Extraction

/-- Relocating twice renames by the composition. -/
theorem Link.relocate_relocate (f g : Nat → Nat) (link : Link) :
    (link.relocate g).relocate f = link.relocate (f ∘ g) := by
  cases link <;> simp [Link.relocate, List.map_map, Function.comp_def, ManagedTarget.relocate]

#print axioms Link.relocate_relocate

/-- A renaming that fixes every method a link enters leaves the link unchanged. -/
theorem Link.relocate_of_fixes {f : Nat → Nat} {link : Link}
    (fixes : ∀ callee ∈ link.callees, f callee = callee) : link.relocate f = link := by
  cases link with
  | address method => rfl
  | direct method => simp_all [Link.relocate, Link.callees]
  | aggregate constructor size => simp_all [Link.relocate, Link.callees]
  | object constructor bases size => simp_all [Link.relocate, Link.callees]
  | virtual targets =>
    simp only [Link.callees, List.mem_map] at fixes
    simp only [Link.relocate, Link.virtual.injEq]
    conv => rhs; rw [← List.map_id targets]
    refine List.map_congr_left fun target member => ?_
    simp [fixes target.2 ⟨target, member, rfl⟩]
  | indirect catalog =>
    simp only [Link.callees, List.mem_map] at fixes
    simp only [Link.relocate, Link.indirect.injEq]
    conv => rhs; rw [← List.map_id catalog]
    refine List.map_congr_left fun target member => ?_
    simp [ManagedTarget.relocate, fixes target.method ⟨target, member, rfl⟩]

#print axioms Link.relocate_of_fixes

/-- Relocating a body twice renames its links by the composition. -/
theorem Method.relocate_relocate (f g : Nat → Nat) (body : Method) :
    (body.relocate g).relocate f = body.relocate (f ∘ g) := by
  simp [Method.relocate, List.map_map, Function.comp_def, Link.relocate_relocate]

#print axioms Method.relocate_relocate

/-- The method indices the link table of `body` enters, in table order. -/
def Method.callees (body : Method) : List Nat :=
  body.links.flatMap fun entry => entry.2.callees

/-- A renaming that fixes every method a body's links enter leaves the body unchanged. -/
theorem Method.relocate_of_fixes {f : Nat → Nat} {body : Method}
    (fixes : ∀ callee ∈ body.callees, f callee = callee) : body.relocate f = body := by
  have same : body.links.map (fun entry => (entry.1, entry.2.relocate f)) = body.links := by
    conv => rhs; rw [← List.map_id body.links]
    refine List.map_congr_left fun entry member => ?_
    rw [Link.relocate_of_fixes fun callee listed =>
      fixes callee (List.mem_flatMap.mpr ⟨entry, member, listed⟩)]
    rfl
  simp only [Method.relocate, same]

#print axioms Method.relocate_of_fixes

/-- A relocated body enters the renamed callees of the original. -/
theorem Method.callees_relocate (f : Nat → Nat) (body : Method) :
    (body.relocate f).callees = body.callees.map f := by
  simp [Method.callees, Method.relocate, List.flatMap_map, Link.callees_relocate,
    List.map_flatMap]

#print axioms Method.callees_relocate

/-- Relocating the links preserves their occupied pcs, so raw decoding relocates the method. -/
theorem Method.ofRaw?_relocate (f : Nat → Nat) (profile : FeatureProfile)
    (environment : LayoutEnvironment) (links : List (Nat × Link)) (reachable : List Bool)
    (source : RawMethod) (arguments : List TypeExpr) :
    Method.ofRaw? profile environment (links.map fun entry => (entry.1, entry.2.relocate f))
        reachable source arguments =
      (Method.ofRaw? profile environment links reachable source arguments).map
        (Method.relocate f) := by
  have occupied : ((links.map fun entry => (entry.1, entry.2.relocate f)).map Prod.fst) =
      links.map Prod.fst := by simp [List.map_map, Function.comp_def]
  have sameCode (closed : RawMethod) :
      methodCode profile environment (links.map fun e => (e.1, e.2.relocate f)) reachable closed =
        methodCode profile environment links reachable closed := by
    unfold methodCode
    rw [occupied]
  simp only [Method.ofRaw?, Method.ofClosed?, bind, pure, Option.map_bind]
  refine congrArg _ (funext fun closed => ?_)
  simp only [Function.comp_apply, Option.map_bind]
  refine congrArg _ (funext fun storage => ?_)
  simp only [Function.comp_apply, Option.map_bind]
  refine congrArg _ (funext fun localKinds => ?_)
  simp only [Function.comp_apply, Option.map_bind]
  refine congrArg _ (funext fun homes => ?_)
  simp only [Function.comp_apply]
  rw [sameCode]
  generalize (rawPrefixesValid closed.returnType closed.code &&
    argumentInstructionsValid storage
      (requiredHomeIndices storage reachable)
      reachable (methodCode profile environment links reachable closed)) = valid
  cases valid <;> rfl

#print axioms Method.ofRaw?_relocate

/-- Bytes decoded with a relocated link table give the relocated method. -/
theorem Method.ofBody?_relocate (f : Nat → Nat) (profile : FeatureProfile)
    (environment : LayoutEnvironment) (links : List (Nat × Link)) (reachable : List Bool)
    (body : BodyEvidence) (original : RawMethod) (arguments : List TypeExpr) :
    Method.ofBody? profile environment (links.map fun entry => (entry.1, entry.2.relocate f))
        reachable body original arguments =
      (Method.ofBody? profile environment links reachable body original arguments).map
        (Method.relocate f) := by
  simp only [Method.ofBody?, bind]
  cases (checkBody body original arguments).toOption with
  | none => rfl
  | some decoded =>
    simp only [Option.bind_some]
    exact Method.ofRaw?_relocate f profile environment links reachable _ arguments

#print axioms Method.ofBody?_relocate

/-- The record with its executable targets renamed by `f` and its source address bindings. -/
def Extraction.MethodEvidence.relocateLinks (f : Nat → Nat) (item : MethodEvidence) :
    MethodEvidence :=
  { item with links := item.links.map fun entry => (entry.1, entry.2.relocate f) }

/-- A record with relocated links decodes to the relocated method of the record. -/
theorem Extraction.MethodEvidence.ofBody?_relocateLinks (f : Nat → Nat) (profile : FeatureProfile)
    (environment : LayoutEnvironment) (item : MethodEvidence) :
    Method.ofBody? profile environment (item.relocateLinks f).links
        (item.relocateLinks f).reachable (item.relocateLinks f).body
        (item.relocateLinks f).original (item.relocateLinks f).arguments =
      (Method.ofBody? profile environment item.links item.reachable item.body item.original
        item.arguments).map (Method.relocate f) :=
  Method.ofBody?_relocate f profile environment item.links item.reachable item.body item.original
    item.arguments

#print axioms Extraction.MethodEvidence.ofBody?_relocateLinks

/-- Slot `slot` of a table packing `width`-bit entries into one number. -/
def packedAt (width table slot : Nat) : Nat :=
  (table >>> (slot * width)) % 2 ^ width

/-- `table` with `value` written into slot `slot`, which must be zero and `value` below
    `2 ^ width`. -/
def packedSet (width table slot value : Nat) : Nat :=
  table ||| (value <<< (slot * width))

/-- A breadth-first search of the methods a root reaches. `slots` packs, per program index, one
    more than its position in the closure (zero when unreached); `indices` packs, per position,
    the program index; `found` lists the visited methods, last visited first; `front` and the
    reversed `back` queue the methods given a position and not yet visited. The closure checks
    every packed entry it relies on, so a wrong entry gives `none` rather than a wrong closure. -/
structure ClosureSearch where
  /-- Bits per packed entry. -/
  width : Nat
  /-- Position plus one of each reached program index. -/
  slots : Nat
  /-- Program index at each position. -/
  indices : Nat
  /-- Positions given out. -/
  count : Nat
  /-- Visited program indices and their methods, last visited first. -/
  found : List (Nat × Method)
  /-- Queued indices, next first. -/
  front : List Nat
  /-- Queued indices after `front`, last queued first. -/
  back : List Nat

/-- `search` with each of `callees` in turn given the next position and queued, unless it
    already has one. -/
-- A fold over the structure costs the kernel time quadratic in the callees; matching the fields
-- at each callee keeps it linear.
def ClosureSearch.reachAll : ClosureSearch → List Nat → ClosureSearch
  | search, [] => search
  | ⟨width, slots, indices, count, found, front, back⟩, callee :: rest =>
    if packedAt width slots callee != 0 then
      reachAll ⟨width, slots, indices, count, found, front, back⟩ rest
    else
      reachAll ⟨width, packedSet width slots callee (count + 1),
        packedSet width indices count callee, count + 1, found, front, callee :: back⟩ rest

/-- `search` after visiting the method `lookup` gives at `index`, with `front` left in the
    queue; with nothing queued when `lookup` gives no method there. -/
def ClosureSearch.visit (lookup : Nat → Option Method) (search : ClosureSearch) (index : Nat)
    (front : List Nat) : ClosureSearch :=
  match lookup index with
  | some method =>
    ClosureSearch.reachAll { search with front := front, found := (index, method) :: search.found }
      method.callees
  | none => { search with front := [], back := [] }

/-- `search` after visiting at most `fuel` queued methods `lookup` gives. -/
def ClosureSearch.run (lookup : Nat → Option Method) : Nat → ClosureSearch → ClosureSearch
  | 0, search => search
  | fuel + 1, search =>
    match search.front with
    | index :: front => (search.visit lookup index front).run lookup fuel
    | [] =>
      match search.back.reverse with
      | index :: front => ({ search with back := [] }.visit lookup index front).run lookup fuel
      | [] => search

/-- The search from `root`, which holds position 0, of the `length` methods `lookup` gives. Each
    visit takes a new position, so `length` visits reach every method. -/
def closureSearchWith (lookup : Nat → Option Method) (length root : Nat) : ClosureSearch :=
  let width := length.log2 + 1
  ClosureSearch.run lookup length
    { width, slots := packedSet width 0 root 1, indices := root, count := 1, found := [],
      front := [root], back := [] }

/-- The search of `program` from `root`, reading each method by its index in the list. -/
def Program.closureSearch (program : Program) (root : Nat) : ClosureSearch :=
  closureSearchWith (program[·]?) program.length root

/-- The position `search` gave program index `callee`. -/
def ClosureSearch.position (search : ClosureSearch) (callee : Nat) : Nat :=
  packedAt search.width search.slots callee - 1

/-- The program index `search` placed at position `slot`. -/
def ClosureSearch.indexAt (search : ClosureSearch) (slot : Nat) : Nat :=
  packedAt search.width search.indices slot

/-- `search` visited one method per position, `root` first, places each at its own position,
    and gives every method a visited method's links enter a position that holds it. -/
def ClosureSearch.consistent (search : ClosureSearch) (root : Nat) : Bool :=
  let visits := search.found.reverse
  visits.length == search.count && visits.head?.map Prod.fst == some root &&
    (visits.zipIdx.all fun (visited, slot) => search.indexAt slot == visited.1) &&
    visits.all fun visited => visited.2.callees.all fun callee =>
      search.position callee < search.count && search.indexAt (search.position callee) == callee

/-- The methods `root` reaches through link tables among the `length` methods `lookup` gives,
    renumbered from `root` at 0, with the index of each; `none` unless every link of the
    renumbered methods enters one of them. A search over `n` methods with `e` link callees reads
    each method once through `lookup` and gives each callee one packed table operation. -/
def closureWith (lookup : Nat → Option Method) (length root : Nat) :
    Option (Program × List Nat) :=
  let search := closureSearchWith lookup length root
  if search.consistent root then
    some (search.found.reverse.map fun visited => visited.2.relocate search.position,
      search.found.reverse.map Prod.fst)
  else none

/-- The methods `root` reaches in `program`, as `closureWith` takes them. Read through the list,
    a closure of `n` methods costs `O(n * P)` list steps in a program of `P` methods; through
    an index of the program, `closure_eq_closureWith` brings that to `O(n * log P)`. -/
def Program.closure (program : Program) (root : Nat) : Option (Program × List Nat) :=
  closureWith (program[·]?) program.length root

/-- A lookup that gives each method of `program` at its index, with the program's length, takes
    the same closure as the list does. -/
theorem Program.closure_eq_closureWith {program : Program} {lookup : Nat → Option Method}
    {length : Nat} (agrees : ∀ index, lookup index = program[index]?)
    (counted : length = program.length) (root : Nat) :
    program.closure root = closureWith lookup length root := by
  have same : lookup = (program[·]?) := funext agrees
  subst same counted
  rfl

#print axioms Program.closure_eq_closureWith

/-- The records of the methods `Program.closure` takes out of `program`, in closure order, each
    with its links renumbered as the closure renumbers them. -/
def Program.closureEvidence (program : Program) (evidence : List MethodEvidence) (root : Nat) :
    Option (List MethodEvidence) :=
  let search := program.closureSearch root
  search.found.reverse.mapM fun visited =>
    evidence[visited.1]?.map (MethodEvidence.relocateLinks search.position)

/-- Every method `search` visited is the method at its index of `program`. -/
def ClosureSearch.Sound (program : Program) (search : ClosureSearch) : Prop :=
  ∀ visited ∈ search.found, program[visited.1]? = some visited.2

/-- Giving callees positions leaves the visited methods alone. -/
theorem ClosureSearch.reachAll_found :
    ∀ (search : ClosureSearch) (callees : List Nat), (search.reachAll callees).found = search.found
  | _, [] => rfl
  | ⟨_, _, _, _, _, _, _⟩, _ :: rest => by
    unfold ClosureSearch.reachAll
    split
    · exact reachAll_found _ rest
    · exact reachAll_found _ rest

#print axioms ClosureSearch.reachAll_found

/-- A visit records only the program's own method at the visited index. -/
theorem ClosureSearch.visit_sound {program : Program} {search : ClosureSearch}
    (sound : search.Sound program) (index : Nat) (front : List Nat) :
    (search.visit (program[·]?) index front).Sound program := by
  unfold ClosureSearch.visit
  split
  · next method found =>
    intro visited member
    rw [ClosureSearch.reachAll_found] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact found
    · exact sound visited member
  · exact sound

#print axioms ClosureSearch.visit_sound

/-- A search of `program` from a sound start visits only the program's own methods. -/
theorem ClosureSearch.run_sound (program : Program) :
    ∀ (fuel : Nat) (search : ClosureSearch), search.Sound program →
      (search.run (program[·]?) fuel).Sound program
  | 0, _, sound => sound
  | fuel + 1, search, sound => by
    unfold ClosureSearch.run
    split
    · exact run_sound program fuel _ (visit_sound sound _ _)
    · split
      · exact run_sound program fuel _
          (visit_sound (search := { search with back := [] }) sound _ _)
      · exact sound

#print axioms ClosureSearch.run_sound

/-- A closure is read off a sound search of its program that `consistent` accepts. -/
theorem Program.closure_eq_some {program lib : Program} {root : Nat} {indices : List Nat}
    (closure : program.closure root = some (lib, indices)) :
    (program.closureSearch root).Sound program ∧
      (program.closureSearch root).consistent root = true ∧
      lib = (program.closureSearch root).found.reverse.map
        (fun visited => visited.2.relocate (program.closureSearch root).position) ∧
      indices = (program.closureSearch root).found.reverse.map Prod.fst := by
  unfold Program.closure closureWith at closure
  dsimp only at closure
  split at closure
  · next consistent =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj closure)
    exact ⟨ClosureSearch.run_sound program _ _ (fun _ member => by simp at member), consistent,
      rfl, rfl⟩
  · cases closure

#print axioms Program.closure_eq_some

/-- What `consistent` checks, as propositions over the visits in order. -/
theorem ClosureSearch.consistent_spec {search : ClosureSearch} {root : Nat}
    (consistent : search.consistent root = true) :
    search.found.reverse.length = search.count ∧
      (search.found.reverse.head?.map Prod.fst) = some root ∧
      (∀ slot (bound : slot < search.found.reverse.length),
        search.indexAt slot = search.found.reverse[slot].1) ∧
      ∀ visited ∈ search.found.reverse, ∀ callee ∈ visited.2.callees,
        search.position callee < search.count ∧
          search.indexAt (search.position callee) = callee := by
  simp only [ClosureSearch.consistent, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at consistent
  obtain ⟨⟨⟨length, first⟩, placed⟩, closed⟩ := consistent
  refine ⟨length, first, fun slot bound => ?_, fun visited member callee listed => ?_⟩
  · exact placed (search.found.reverse[slot], slot)
      (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem bound))
  · simpa using closed visited member callee listed

#print axioms ClosureSearch.consistent_spec

/-- Results whose items each give them through `f` give, through `g`, the images of the items. -/
private theorem mapM_map_of {α β γ : Type} {f : α → Option β} {g : β → Option γ}
    {image : α → γ} :
    ∀ {items : List α} {results : List β}, items.mapM f = some results →
      (∀ item ∈ items, ∀ result, f item = some result → g result = some (image item)) →
      results.mapM g = some (items.map image)
  | [], results, mapped, _ => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at mapped
    subst mapped
    rfl
  | item :: items, results, mapped, step => by
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at mapped
    obtain ⟨first, given, rest, remaining, rfl⟩ := mapped
    have tail := mapM_map_of remaining fun other member =>
      step other (List.mem_cons_of_mem _ member)
    simp [List.mapM_cons, step item (List.mem_cons_self ..) first given, tail]

/-- `mapM` into `Option` gives one result per item. -/
private theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {items : List α} {results : List β}, items.mapM f = some results →
      results.length = items.length
  | [], results, mapped => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at mapped
    subst mapped
    rfl
  | item :: items, results, mapped => by
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at mapped
    obtain ⟨first, -, rest, remaining, rfl⟩ := mapped
    simp [mapM_length remaining]

/-- The methods a closure takes out of its program enter only one another. -/
theorem Program.closure_closed {program lib : Program} {root : Nat} {indices : List Nat}
    (closure : program.closure root = some (lib, indices)) : Safety.Closed lib := by
  have facts := Program.closure_eq_some closure
  generalize program.closureSearch root = search at facts
  obtain ⟨-, consistent, rfl, -⟩ := facts
  obtain ⟨length, -, -, closed⟩ := ClosureSearch.consistent_spec consistent
  intro i body found entry listed callee member
  simp only [List.getElem?_map, Option.map_eq_some_iff] at found
  obtain ⟨visited, visitedAt, rfl⟩ := found
  have entered : callee ∈ (visited.2.relocate search.position).callees :=
    List.mem_flatMap.mpr ⟨entry, listed, member⟩
  rw [Method.callees_relocate, List.mem_map] at entered
  obtain ⟨original, originalListed, rfl⟩ := entered
  rw [List.length_map, length]
  exact (closed visited (List.mem_of_getElem? visitedAt) original originalListed).1

#print axioms Program.closure_closed

/-- A closure relocates back into its program, method `slot` of the closure to index
    `indices[slot]`, and its first method is the root. -/
theorem Program.closure_relocates {program lib : Program} {root : Nat} {indices : List Nat}
    (closure : program.closure root = some (lib, indices)) :
    Safety.RelocatesInto lib program (fun slot => indices.getD slot 0) ∧
      indices[0]? = some root := by
  have facts := Program.closure_eq_some closure
  generalize program.closureSearch root = search at facts
  obtain ⟨sound, consistent, rfl, rfl⟩ := facts
  obtain ⟨length, first, placed, closed⟩ := ClosureSearch.consistent_spec consistent
  have indexed : ∀ slot (bound : slot < search.found.reverse.length),
      (search.found.reverse.map Prod.fst).getD slot 0 = search.found.reverse[slot].1 := by
    intro slot bound
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem bound]
    rfl
  refine ⟨fun i bound => ?_, ?_⟩
  · rw [List.length_map] at bound
    dsimp only
    rw [indexed i bound, List.getElem_map, Method.relocate_relocate,
      Method.relocate_of_fixes fun callee listed => ?_]
    · exact sound _ (List.mem_reverse.mp (List.getElem_mem bound))
    · obtain ⟨below, lands⟩ := closed _ (List.getElem_mem bound) callee listed
      rw [Function.comp_apply, indexed _ (length ▸ below), ← placed _ (length ▸ below), lands]
  · rw [List.getElem?_map, ← List.head?_eq_getElem?]
    exact first

#print axioms Program.closure_relocates

/-- The records of a closure, read from the records that decode to its program, decode to the
    closure. -/
theorem Program.closureEvidence_decodes {profile : FeatureProfile}
    {environment : LayoutEnvironment} {evidence libEvidence : List MethodEvidence}
    {program lib : Program} {root : Nat} {indices : List Nat}
    (decoded : decodedProgram? profile environment evidence = some program)
    (closure : program.closure root = some (lib, indices))
    (records : program.closureEvidence evidence root = some libEvidence) :
    decodedProgram? profile environment libEvidence = some lib := by
  have facts := Program.closure_eq_some closure
  unfold Program.closureEvidence at records
  dsimp only at records
  generalize program.closureSearch root = search at facts records
  obtain ⟨sound, -, rfl, -⟩ := facts
  unfold decodedProgram?
  refine mapM_map_of records fun visited member item relocated => ?_
  obtain ⟨original, recorded, rfl⟩ := Option.map_eq_some_iff.mp relocated
  rw [MethodEvidence.ofBody?_relocateLinks, Safety.decodedProgram?_getElem decoded recorded,
    sound visited (List.mem_reverse.mp member)]
  rfl

#print axioms Program.closureEvidence_decodes

end CIL

namespace CIL.Safety
open CIL.Extraction

/-- A contract that holds where a closed library relocates into a program holds in the library:
    the program runs the library's method exactly as the library does. -/
theorem MethodContract.Holds.restrict {Input Output : Type} {c : MethodContract Input Output}
    {lib linked : CIL.Program} {f : Nat → Nat} {method : Nat} (holds : c.Holds linked (f method))
    (closed : Closed lib) (relocates : RelocatesInto lib linked f) (bound : method < lib.length) :
    c.Holds lib method := by
  intro input initial permitted
  obtain ⟨fuel, ⟨final, values⟩, invoked, framed, returns⟩ := holds input initial permitted
  refine ⟨fuel, (final, values), ?_, framed, returns⟩
  dsimp only [Execution] at invoked ⊢
  rw [invoke_relocate closed relocates fuel method _ initial bound] at invoked
  cases ran : invoke lib fuel method (c.args input) initial <;>
    simp_all [Except.mapError]

#print axioms MethodContract.Holds.restrict

/-- Records whose methods decode, at the indices `f` gives, to the relocated methods of a
    library's records place the library in `target`. A map sending two library methods to one
    index is accepted when both decode to the method there, which is sound: a call into either
    runs that method, the one both denote. -/
theorem RelocatesInto.of_decoded {profile : FeatureProfile} {environment : LayoutEnvironment}
    {lib target : CIL.Program} {libEvidence targetEvidence : List MethodEvidence} {f : Nat → Nat}
    (libDecoded : decodedProgram? profile environment libEvidence = some lib)
    (targetDecoded : decodedProgram? profile environment targetEvidence = some target)
    (same : ∀ i, i < libEvidence.length → ∃ item moved, libEvidence[i]? = some item ∧
      targetEvidence[f i]? = some moved ∧
      Method.ofBody? profile environment moved.links moved.reachable moved.body moved.original
          moved.arguments =
        (Method.ofBody? profile environment item.links item.reachable item.body item.original
          item.arguments).map (Method.relocate f)) :
    RelocatesInto lib target f := by
  intro i bound
  have length : libEvidence.length = lib.length := by
    unfold decodedProgram? at libDecoded
    exact (mapM_length libDecoded).symm
  obtain ⟨item, moved, recorded, placed, decodes⟩ := same i (length ▸ bound)
  rw [← decodedProgram?_getElem targetDecoded placed, decodes,
    decodedProgram?_getElem libDecoded recorded, List.getElem?_eq_getElem bound]
  rfl

#print axioms RelocatesInto.of_decoded

/-- A summary proved over a closed library is a summary of the method `f` places in `target`,
    bound to `target`'s record there, given that record names the same pinned method at the same
    type arguments. The bytes of that record need not be the library's: `relocates` already
    states that they decode to the relocated method. `f` may send two library methods to one
    index when both decode to the method there, which is sound because a call into either runs
    the method both denote. -/
theorem DecodedSummary.relocate {Input Output : Type} {contract : MethodContract Input Output}
    {lib target : CIL.Program} {libEvidence targetEvidence : List MethodEvidence}
    {profile : FeatureProfile} {environment : LayoutEnvironment} {f : Nat → Nat}
    {index token : Nat} {pin : AssemblyPin} {arguments : List TypeExpr}
    (summary : DecodedSummary lib libEvidence profile environment index pin token arguments
      contract)
    (closed : Closed lib) (relocates : RelocatesInto lib target f)
    (targetDecoded : decodedProgram? profile environment targetEvidence = some target)
    (record : ∀ item, libEvidence[index]? = some item → ∃ moved,
      targetEvidence[f index]? = some moved ∧ moved.assembly = item.assembly ∧
        moved.original = item.original ∧ moved.arguments = item.arguments ∧
        moved.closed = item.closed) :
    DecodedSummary target targetEvidence profile environment (f index) pin token arguments
      contract := by
  obtain ⟨item, recorded, assembly, sameToken, sameArguments, instantiated, -⟩ := summary.bound
  obtain ⟨moved, placed, movedAssembly, movedOriginal, movedArguments, movedClosed⟩ :=
    record item recorded
  refine ⟨summary.holds.relocate closed relocates, moved, placed, movedAssembly.trans assembly,
    movedOriginal ▸ sameToken, movedArguments.trans sameArguments, ?_,
    decodedProgram?_getElem targetDecoded placed⟩
  rw [movedOriginal, movedClosed]
  exact instantiated

#print axioms DecodedSummary.relocate

end CIL.Safety
