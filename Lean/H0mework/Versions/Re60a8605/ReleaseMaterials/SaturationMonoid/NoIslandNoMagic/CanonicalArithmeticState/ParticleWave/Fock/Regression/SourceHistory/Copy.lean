import H0mework.Fock.HistoryCopy.Installed

/-! Actual early actors check the unit action, the generated override, and the rejected mismatch. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.NativeCopy.Controls

open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem first_actor_unit_action :
    FullMap.defect nativeStep nativeStep (copy (Fock.material 0 0))
      (fieldPoint nativeStep fullRead (runtimeAt 0).current.visit.current) = 0 :=
  (unit_clock_defect_point_zero_iff _ _).mpr ((Fock.material_is_unit_iff 0 0).mpr rfl)

theorem later_actor_rejects_unit_action :
    FullMap.defect nativeStep nativeStep (copy (Fock.material 1 1))
      (fieldPoint nativeStep fullRead (runtimeAt 1).current.visit.current) ≠ 0 := by
  intro vanished
  have index := (Fock.material_is_unit_iff 1 1).mp ((unit_clock_defect_point_zero_iff _ _).mp vanished)
  exact Nat.one_ne_zero index

theorem later_actor_generated_action :
    FullMap.defect nativeStep (copyStep (Fock.material 1 1)) (copy (Fock.material 1 1)) = 0 :=
  generated_defect_zero _

end
end SourceOwnedObservationHistory.NativeCopy.Controls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
