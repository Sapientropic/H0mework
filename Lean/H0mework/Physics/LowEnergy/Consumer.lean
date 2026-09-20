import H0mework.Physics.LowEnergy.Normalization
import H0mework.Physics.LowEnergy.Running
import H0mework.Physics.LowEnergy.JointMassCoordinates

/-! Direct consumers of the existing positive source. These are mathematical
readouts only: no new controller, source state, vacuum, physical time, or seal. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Consumer
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
noncomputable section

theorem source_mass_entry (out : ExteriorBasisIndex 6) (inp : ExteriorBasisIndex 2) :
    (su7ExteriorBasis 6).coord out
      (exteriorYukawaMassMap (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
        (su7ExteriorBasis 2 inp)) = (JointMass.coefficient out inp : ℂ) := by
  rw [positive_sourceGeneratedVacuumBase]
  exact JointMass.coefficient_actual out inp

theorem source_inventory_beta :
    ScalarInventory.b0 .motherSU7 = 56 / 3 ∧ ScalarInventory.b0 .colorSU3 = 4 ∧
    ScalarInventory.b0 .weakSU2 = 1 / 3 ∧ ScalarInventory.b0 .p286HyperchargeU1 = -28 :=
  ScalarInventory.b0_table

theorem source_fixed_inventory_diagnostic (time : ℝ) :
    ¬ (Running.strongInverse time = Running.weakInverse time ∧
      Running.weakInverse time = Running.normalizedChargeInverse time) :=
  Running.no_common_crossing time

end
end SaturationMonoid.PhysicsCore.LowEnergy.Consumer
