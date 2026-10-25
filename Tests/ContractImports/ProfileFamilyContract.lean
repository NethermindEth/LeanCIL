import CIL.Safety.OutcomeContract

/-! The public contract for the profile-family export acceptance fixture. -/
namespace FamilyContract

/-- A supported feature query returns one without changing caller memory. -/
def supported : CIL.Safety.MethodContract Unit where
  args _ := []
  pre _ _ := True
  footprint _ := []
  post _ _ _ values := values = [.scalar (.i32 1)]

/-- The query also has an outcome contract that rules out exceptional return. -/
def outcome : CIL.Safety.OutcomeContract Unit :=
  { supported with raises := fun _ _ => none }

end FamilyContract
