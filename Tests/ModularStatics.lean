import CIL.Safety.StaticLinking
import CIL.Safety.StaticMemoryBelow
import CIL.Safety.WordMemory
import Examples.Support

namespace Tests.ModularStatics

open CIL CIL.Safety

private def appField : StaticDescriptor :=
  { identity := 101, assemblyIdentity := "App", fieldName := "App::Table", bytes := numberBytes 7 8 }
private def libField : StaticDescriptor :=
  { identity := 202, assemblyIdentity := "Lib", fieldName := "Lib::Table", bytes := numberBytes 17 8 }

@[cil_code] def libBody : Method :=
  { returnsValue := true, locals := [], staticSites := [(0, libField)],
    code := [.memory (.staticAddress (numberBytes 17 8)), .load64, .ret] }
@[cil_code] def appBody : Method :=
  { returnsValue := true, locals := [], staticSites := [(0, appField)],
    code := [.memory (.staticAddress (numberBytes 7 8)), .pop, .call 1 0, .ret] }
def library : Library := { entry := libBody }
def linked : CIL.Program := link [appBody] [library]

example : linkChecked [appBody] [library] = .ok linked := by decide +kernel
example : (invoke linked 16 0 [] Examples.empty).map Prod.snd = .ok [.scalar (.i64 17)] := rfl
example : (invoke linked 16 0 [] Examples.empty).map (fun result => result.1.staticBindings.map Prod.fst) =
    .ok [202, 101] := rfl

private def afterApp : Memory :=
  ((staticReference appField Examples.empty).toOption.getD (Examples.empty, ⟨0, 0⟩)).1
private theorem app_loaded : staticReference appField Examples.empty = .ok (afterApp, ⟨0, 0⟩) := rfl
private theorem empty_formed : Examples.empty.WellFormed := by
  simp [Memory.WellFormed, Examples.empty]
private theorem app_formed : afterApp.WellFormed :=
  staticReference_preserves_wellFormed _ _ _ _ empty_formed app_loaded

private theorem app_world : StaticWorldValid [appField] afterApp :=
  staticReference_preserves_static_world _ _ _ _ _ empty_formed
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

def readTable : MethodContract Unit W64 where
  args _ := []
  results value := [.scalar (.i64 value)]
  pre _ memory := memory.WellFormed ∧ StaticRegistryValid memory ∧ StaticIdentitiesAbsent [202] memory
  footprint _ := []
  post _ _ _ output := output = 17

theorem readTable_holds : readTable.Holds [libBody] 0 := by
  rintro input memory ⟨formed, registry, absent⟩
  have world : StaticWorldValid [libField] memory :=
    StaticWorldValid.of_absent _ _ (by simp [libField, numberBytes, nativeLimit])
      (by simp) registry (by simpa [libField] using absent)
  obtain ⟨result, reference, resolved, _, valid⟩ :=
    staticReference_valid_result libField [libField] memory formed world (by simp)
  have loaded : read result reference 8 1 = .ok (numberBytes (17#64).toNat 8) := by
    simpa [libField, numberBytes] using valid.2.choose_spec.2.2.2.2
  have load := load_word64_of_read loaded
  have referenceValid := staticReference_reference_valid _ _ _ _ resolved
  have addressed : staticInstruction libBody 0 (.staticAddress (numberBytes 17 8)) [] memory =
      .ok (result, [.reference (.address reference)]) := by
    simp [libBody, libField, staticInstruction, resolved, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨8, result, [.scalar (.i64 17)], ?_,
    Confined.ofMemoryBelow (staticReference_preserves_memory_below _ _ _ _ resolved)
      (Nat.le_refl _) (staticReference_extends_allocations _ _ _ _ resolved).next,
    17, rfl, rfl⟩
  cil_checked_steps [addressed, load, referenceValid]

theorem linked_readTable_holds : readTable.Holds linked 1 :=
  readTable_holds.relocate (Closed.of_check (by decide))
    (link_relocates [appBody] [library] (j := 0) (by decide))

example : readTable.pre () afterApp := ⟨app_formed, app_world.2.2.1, library_absent⟩

example : ∃ fuel result values, invoke linked fuel 1 [] afterApp = .ok (result, values) ∧
    values = [.scalar (.i64 17)] := by
  obtain ⟨fuel, result, values, ran, _, output, encoded, post⟩ :=
    linked_readTable_holds () afterApp ⟨app_formed, app_world.2.2.1, library_absent⟩
  subst output
  exact ⟨fuel, result, values, ran, encoded⟩

private def collision : Library :=
  { entry := { libBody with staticSites := [(0, { libField with identity := 101 })] } }

example : linkChecked [appBody] [collision] =
    .error "Static identity collision 101: App::App::Table and Lib::Lib::Table" := by decide +kernel

#print axioms readTable_holds
#print axioms linked_readTable_holds

end Tests.ModularStatics
