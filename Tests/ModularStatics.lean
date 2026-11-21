import CIL.Safety.StaticLinking
import CIL.Safety.StaticMemoryBelow
import CIL.Safety.WordMemory
import CIL.Safety.Execution
import Tests.Support

/-! Checked static-table linking and loaded-world premises for modular consumer contracts. -/

namespace Tests.ModularStatics

open CIL CIL.Safety

/-- The field of `owner`'s table, an eight-byte static. -/
private def tableRef (owner : String) : Extraction.FieldRef :=
  { owner := .atom owner (owner ++ ".Holder"), index := 0, type := .atom owner (owner ++ ".Table"),
    name := name!"Table" }

private def appField : StaticDescriptor :=
  { identity := 101, field := tableRef "App", bytes := numberBytes 7 8 }
private def libField : StaticDescriptor :=
  { identity := 202, field := tableRef "Lib", bytes := numberBytes 17 8 }

@[cil_code] def libBody : Method :=
  { returnsValue := true, locals := [], staticSites := [(0, libField)],
    code := [.ldsflda (tableRef "Lib"), .ldind .i8, .ret] }
@[cil_code] def appBody : Method :=
  { returnsValue := true, locals := [], staticSites := [(0, appField)],
    code := [.ldsflda (tableRef "App"), .pop, .call (Tests.callee 0) {},
      .ret], links := [(2, .direct 1)] }
def library : Library := { entry := libBody }
def linked : CIL.Program := link [appBody] [library]

example : linkChecked [appBody] [library] = .ok linked := rfl
example : linkChecked [appBody] [library] = .ok linked := linkChecked_of_compatible (by decide +kernel)
example : (invoke linked 16 0 [] Memory.empty).map Prod.snd = .ok [.scalar (.i64 17)] := rfl
example : (invoke linked 16 0 [] Memory.empty).map (fun result => result.1.staticBindings.map Prod.fst) =
    .ok [202, 101] := rfl

private def afterApp : Safety.Memory :=
  ((staticReference appField Memory.empty).toOption.getD (Memory.empty, ⟨0, 0⟩)).1
private theorem app_loaded : staticReference appField Memory.empty = .ok (afterApp, ⟨0, 0⟩) := rfl
private theorem app_formed : afterApp.WellFormed :=
  staticReference_preserves_wellFormed _ _ _ _ Memory.empty_wellFormed app_loaded

private theorem app_world : StaticWorldValid [appField] afterApp :=
  staticReference_preserves_static_world _ _ _ _ _ Memory.empty_wellFormed
    (empty_static_world_valid _ _ (by simp [appField, numberBytes, nativeLimit])
      (by simp) rfl) (by simp) app_loaded

private theorem library_absent : StaticIdentitiesAbsent [202] afterApp := by
  intro binding member
  change binding ∈ [(101, (⟨0, 0⟩ : Reference))] at member
  rcases List.mem_singleton.mp member with rfl
  decide

private theorem lib_world : StaticWorldValid [libField] afterApp :=
  StaticWorldValid.of_absent _ _ (by simp [libField, numberBytes, nativeLimit])
    (by simp) app_world.2.2.1 (by simpa [libField] using library_absent)

example : StaticWorldValid [appField, libField] afterApp :=
  app_world.append lib_world (by simp [appField, libField])

-- Two exports reading one shared table compose; equal identities must name equal descriptors.
example : StaticWorldValid [libField, libField] afterApp :=
  lib_world.append lib_world (by simp)

def readTable : MethodContract Unit W64 where
  args _ := []
  results value := [.scalar (.i64 value)]
  pre _ memory := memory.WellFormed ∧ StaticRegistryValid memory ∧ StaticIdentitiesAbsent [202] memory
  footprint _ := []
  post _ _ _ output := output = 17

private theorem libBody_reads (memory : Safety.Memory) (formed : memory.WellFormed)
    (world : StaticWorldValid [libField] memory) :
    WP (Execution (fun fuel => invoke [libBody] fuel 0 [] memory))
      (fun (result, values) => values = [.scalar (.i64 17)] ∧
        Confined [] memory result ∧ result.WellFormed ∧ StaticWorldValid [libField] result) := by
  obtain ⟨result, reference, resolved, _, valid⟩ :=
    staticReference_valid_result libField [libField] memory formed world (by simp)
      (by simp [libField])
  have loaded : read result reference 8 1 = .ok (numberBytes (17#64).toNat 8) := by
    obtain ⟨bytes, readable, same⟩ := valid.2.choose_spec.2.2.2.2.2
    rw [same rfl] at readable
    simpa [libField, numberBytes] using readable
  have load := load_word64_of_read loaded
  have addressed : staticAddress libBody 0 memory =
      .ok (result, .reference (.address reference)) := staticAddress_resolved rfl resolved
  let frame : Frame := { activation := memory.nextIdentity, locals := [], owned := [] }
  have first : step libBody (.ldsflda (tableRef "Lib")) 0 [] frame [] memory =
      .ok (.next 1 [.reference (.address reference)] frame result) := by
    rw [step_ldsflda_eq, addressed]
  have second : step libBody (.ldind .i8) 1 [] frame [.reference (.address reference)] result =
      .ok (.next 2 [.scalar (.i64 17)] frame result) := by
    rw [step_ldind_eq]
    simp only [instructionStep, instruction, CIL.NumericKind.width, CIL.NumericKind.signed, load,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  have returned : step libBody .ret 2 [] frame [.scalar (.i64 17)] result =
      .ok (.returned [.scalar (.i64 17)] result) := rfl
  apply WP.enter (body := libBody) rfl rfl rfl
  apply WP.step rfl rfl first
  apply WP.step rfl rfl second
  apply WP.returned rfl rfl returned rfl
  exact ⟨rfl,
    Confined.ofMemoryBelow (staticReference_preserves_memory_below _ _ _ _ resolved)
      (Nat.le_refl _) (staticReference_extends_allocations _ _ _ _ resolved).next,
    staticReference_preserves_wellFormed _ _ _ _ formed resolved,
    staticReference_preserves_static_world _ _ _ _ _ formed world (by simp) resolved⟩

#print axioms libBody_reads

theorem readTable_holds : readTable.Holds [libBody] 0 := by
  rintro input memory ⟨formed, registry, absent⟩
  have world : StaticWorldValid [libField] memory :=
    StaticWorldValid.of_absent _ _ (by simp [libField, numberBytes, nativeLimit])
      (by simp) registry (by simpa [libField] using absent)
  exact (libBody_reads memory formed world).consequence
    fun _ ⟨encoded, confined, _, _⟩ => ⟨confined, 17, encoded, rfl⟩

-- A world precondition that the post re-establishes supports repeated calls; absence holds only before the first.
def readTableRepeat : MethodContract Unit W64 where
  args _ := []
  results value := [.scalar (.i64 value)]
  pre _ memory := memory.WellFormed ∧ StaticWorldValid [libField] memory
  footprint _ := []
  post _ _ final output := output = 17 ∧ final.WellFormed ∧ StaticWorldValid [libField] final

theorem readTableRepeat_holds : readTableRepeat.Holds [libBody] 0 := by
  rintro input memory ⟨formed, world⟩
  exact (libBody_reads memory formed world).consequence
    fun _ ⟨encoded, confined, resultFormed, resultWorld⟩ =>
      ⟨confined, 17, encoded, rfl, resultFormed, resultWorld⟩

example (memory : Safety.Memory) (permitted : readTableRepeat.pre () memory) :
    WP (Execution (fun fuel => invoke [libBody] fuel 0 [] memory))
      (fun (middle, first) => WP (Execution (fun fuel => invoke [libBody] fuel 0 [] middle))
        (fun (_, second) => first = [.scalar (.i64 17)] ∧ second = [.scalar (.i64 17)])) := by
  apply (readTableRepeat_holds () memory permitted).consequence
  rintro ⟨middle, first⟩ ⟨_, out, encoded, rfl, again⟩
  apply (readTableRepeat_holds () middle again).consequence
  rintro ⟨_, _⟩ ⟨_, out', encoded', same, _⟩
  exact ⟨encoded, same ▸ encoded'⟩

-- The table is already loaded here, so only the world form admits this call.
example : readTableRepeat.pre () afterApp := ⟨app_formed, lib_world⟩

theorem linked_readTable_holds : readTable.Holds linked 1 :=
  readTable_holds.relocate (Closed.of_check (by decide))
    (link_relocates [appBody] [library] (j := 0) (by decide))

example : readTable.pre () afterApp := ⟨app_formed, app_world.2.2.1, library_absent⟩

example : ∃ fuel result values, invoke linked fuel 1 [] afterApp = .ok (result, values) ∧
    values = [.scalar (.i64 17)] := by
  apply WP.exists_execution
  exact (linked_readTable_holds () afterApp
    ⟨app_formed, app_world.2.2.1, library_absent⟩).consequence
    fun _ ⟨_, output, encoded, same⟩ => same ▸ encoded

private def collision : Library :=
  { entry := { libBody with staticSites := [(0, { libField with identity := 101 })] } }

/-- The application's table and the library's under its identity collide, in that order. -/
theorem colliding_identity_rejected :
    linkChecked [appBody] [collision] =
      .error { left := appField, right := { libField with identity := 101 } } :=
  linkChecked_of_collision (by decide +kernel)

-- The report names both fields; the interpreter checks it, as the kernel does not reduce `repr`.
#guard match linkChecked [appBody] [collision] with
  | .error collision => collision.message == "Static identity collision 101: " ++
    reprStr (tableRef "App") ++ " and " ++ reprStr (tableRef "Lib")
  | .ok _ => false

/-- `library` with the table's bytes changed under the same identity and field. -/
private def changedTable : Library :=
  { entry := { libBody with staticSites := [(0, { libField with bytes := numberBytes 18 8 })] } }

/-- Two readers may share exactly the same static descriptor. -/
theorem shared_table_links :
    linkChecked [appBody] [library, library] = .ok (link [appBody] [library, library]) :=
  linkChecked_of_compatible (by decide +kernel)

/-- Reusing an identity with different table bytes prevents checked linking, and the collision
    is the library's descriptor beside the changed one. -/
theorem changed_shared_table_rejected :
    linkChecked [appBody] [library, changedTable] =
      .error { left := libField, right := { libField with bytes := numberBytes 18 8 } } :=
  linkChecked_of_collision (by decide +kernel)

#guard match linkChecked [appBody] [library, changedTable] with
  | .error collision => collision.message == "Static identity collision 202: " ++
    reprStr (tableRef "Lib") ++ " and " ++ reprStr (tableRef "Lib")
  | .ok _ => false

/-- A loaded table with different bytes cannot satisfy a contract's static-world premise. -/
theorem changed_loaded_table_not_valid :
    ¬ StaticWorldValid [{ appField with bytes := numberBytes 8 8 }] afterApp := by
  intro world
  have valid := world.2.2.2 { appField with bytes := numberBytes 8 8 } (by simp)
    (101, (⟨0, 0⟩ : Reference)) (by decide +kernel) rfl
  obtain ⟨_, allocation, present, live, kind, size, alignment, bytes, readable, same⟩ := valid
  have actual : read afterApp ⟨0, 0⟩ 8 1 = .ok (numberBytes 7 8) := rfl
  have incompatible : numberBytes 7 8 ≠ numberBytes 8 8 := by decide +kernel
  have stored : bytes = numberBytes 8 8 := same rfl
  subst stored
  exact incompatible (Except.ok.inj (actual.symm.trans readable))

#print axioms shared_table_links
#print axioms colliding_identity_rejected
#print axioms changed_shared_table_rejected
#print axioms changed_loaded_table_not_valid
#print axioms readTable_holds
#print axioms readTableRepeat_holds
#print axioms linked_readTable_holds

end Tests.ModularStatics
