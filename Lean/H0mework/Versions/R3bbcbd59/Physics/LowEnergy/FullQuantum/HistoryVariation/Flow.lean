import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Inverse
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryForcing.Source

/-! Both interaction maps are presentations of the same generated original complete history. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryForcing PerturbedGreen
noncomputable section
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)

def interaction (time : ℝ) : SpatialOperators :=
  (spatialFree (-time)).comp (fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time)

def inverseInteraction (time : ℝ) : SpatialOperators :=
  (fullOperator gauge continuousGauge coupling scalar continuousScalar time 0).comp (spatialFree time)

theorem interaction_left (time : ℝ) (field : FullMatterL2) :
    inverseInteraction gauge continuousGauge coupling scalar continuousScalar time
      (interaction gauge continuousGauge coupling scalar continuousScalar time field)=field := by
  simp only [interaction,inverseInteraction,ContinuousLinearMap.comp_apply,← spatialFree_add,
    add_neg_cancel,spatialFree_zero,fullOperator_inverse]

theorem interaction_right (time : ℝ) (field : FullMatterL2) :
    interaction gauge continuousGauge coupling scalar continuousScalar time
      (inverseInteraction gauge continuousGauge coupling scalar continuousScalar time field)=field := by
  simp only [interaction,inverseInteraction,ContinuousLinearMap.comp_apply,fullOperator_inverse,
    ← spatialFree_add,neg_add_cancel,spatialFree_zero]

theorem interaction_apply (time : ℝ) (field : FullMatterL2) :
    interaction gauge continuousGauge coupling scalar continuousScalar time field=
      gaugeInteraction gauge continuousGauge coupling time
        (field+scalarIntegralOperator gauge continuousGauge coupling scalar continuousScalar 0 time field) := by
  rw [interaction,ContinuousLinearMap.comp_apply,fullOperator_apply,gaugeUnitary_starts]
  rfl

theorem inverseInteraction_apply (time : ℝ) (field : FullMatterL2) :
    inverseInteraction gauge continuousGauge coupling scalar continuousScalar time field=
      gaugeUnitary gauge continuousGauge coupling time 0 (spatialFree time field)-
        scalarIntegralOperator gauge continuousGauge coupling scalar continuousScalar 0 time
          (gaugeUnitary gauge continuousGauge coupling time 0 (spatialFree time field)) := by
  rw [inverseInteraction,ContinuousLinearMap.comp_apply,fullOperator_apply,gaugeUnitary_starts]
  change _+(∫ r in time..0, scalarInteraction gauge continuousGauge coupling scalar r
    (gaugeUnitary gauge continuousGauge coupling time 0 (spatialFree time field)))=
    _-(∫ r in 0..time, scalarInteraction gauge continuousGauge coupling scalar r
      (gaugeUnitary gauge continuousGauge coupling time 0 (spatialFree time field)))
  rw [intervalIntegral.integral_symm]
  simp only [sub_eq_add_neg]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
