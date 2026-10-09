import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Joint

/-! Original strong equations generate both interaction derivatives on their actual inverse pair. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryForcing PerturbedGreen
noncomputable section
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)

def interactionGenerator (time : ℝ) : SpatialOperators :=
  (spatialFree (-time)).comp ((localForce (gauge time) coupling (scalar time)).comp (spatialFree time))

theorem interaction_derivative (time : ℝ) (field : FullMatterL2) :
    HasDerivAt (fun t => interaction gauge continuousGauge coupling scalar continuousScalar t field)
      (interactionGenerator gauge coupling scalar time
        (interaction gauge continuousGauge coupling scalar continuousScalar time field)) time := by
  have generated := full_freeInteraction_equation gauge continuousGauge coupling scalar continuousScalar 0 time field
  simpa only [interaction,interactionGenerator,ContinuousLinearMap.comp_apply,
    ← spatialFree_add,add_neg_cancel,spatialFree_zero,localForce,add_apply,smul_apply] using! generated

theorem inverseInteraction_derivative (time : ℝ) (field : FullMatterL2) :
    HasDerivAt (fun t => inverseInteraction gauge continuousGauge coupling scalar continuousScalar t field)
      (-inverseInteraction gauge continuousGauge coupling scalar continuousScalar time
        (interactionGenerator gauge coupling scalar time field)) time := by
  apply strong_inverse_derivative
    (interaction gauge continuousGauge coupling scalar continuousScalar)
    (inverseInteraction gauge continuousGauge coupling scalar continuousScalar)
    (interaction_left gauge continuousGauge coupling scalar continuousScalar)
    (interaction_right gauge continuousGauge coupling scalar continuousScalar)
    (inverseInteraction_joint gauge continuousGauge coupling scalar continuousScalar) time field
  have fixed := interaction_derivative gauge continuousGauge coupling scalar continuousScalar time
    (inverseInteraction gauge continuousGauge coupling scalar continuousScalar time field)
  rw [interaction_right] at fixed
  exact fixed

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
