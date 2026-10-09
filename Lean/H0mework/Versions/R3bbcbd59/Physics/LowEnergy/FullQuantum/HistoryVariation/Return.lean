import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Dynamics
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryForcing.Dual

/-! The same inverse history returns every genuine free-interaction solution to its original source. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryForcing PerturbedGreen
noncomputable section
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
attribute [local irreducible] fullOperator interaction inverseInteraction interactionGenerator

theorem returned_derivative (curve : ℝ → FullMatterL2) (time : ℝ) (source : FullMatterL2)
    (evolves : HasDerivAt (fun t => spatialFree (-t) (curve t))
      (spatialFree (-time) (localForce (gauge time) coupling (scalar time) (curve time)+inversePrincipal 0 source)) time) :
    HasDerivAt (fun t => fullOperator gauge continuousGauge coupling scalar continuousScalar t 0 (curve t))
      (fullOperator gauge continuousGauge coupling scalar continuousScalar time 0 (inversePrincipal 0 source)) time := by
  have fixed := inverseInteraction_derivative gauge continuousGauge coupling scalar continuousScalar time
    (spatialFree (-time) (curve time))
  have generated := strong_operator_product
    (inverseInteraction gauge continuousGauge coupling scalar continuousScalar)
    (inverseInteraction_joint gauge continuousGauge coupling scalar continuousScalar)
    (fun t => spatialFree (-t) (curve t)) _ _ time fixed evolves
  simp only [inverseInteraction,interactionGenerator,ContinuousLinearMap.comp_apply,
    ← spatialFree_add,add_neg_cancel,spatialFree_zero,map_add] at generated
  convert! generated using 1
  module

theorem returned_integral (curve source : ℝ → FullMatterL2) (continuousSource : Continuous source)
    (initial : FullMatterL2) (starts : curve 0=initial)
    (evolves : ∀ t, HasDerivAt (fun r => spatialFree (-r) (curve r))
      (spatialFree (-t) (localForce (gauge t) coupling (scalar t) (curve t)+inversePrincipal 0 (source t))) t)
    (time : ℝ) :
    fullOperator gauge continuousGauge coupling scalar continuousScalar time 0 (curve time)=
      initial+∫ r in (0 : ℝ)..time, fullOperator gauge continuousGauge coupling scalar continuousScalar r 0
        (inversePrincipal 0 (source r)) := by
  have integrated := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => returned_derivative gauge continuousGauge coupling scalar continuousScalar curve t (source t) (evolves t))
    ((source_kernel_continuous gauge continuousGauge coupling scalar continuousScalar source continuousSource 0).intervalIntegrable
      (μ := volume) 0 time)
  rw [starts,fullOperator_starts] at integrated
  exact (eq_add_of_sub_eq integrated.symm).trans (add_comm _ _)

theorem original_retarded_equation (curve source : ℝ → FullMatterL2) (continuousSource : Continuous source)
    (initial : FullMatterL2) (starts : curve 0=initial)
    (evolves : ∀ t, HasDerivAt (fun r => spatialFree (-r) (curve r))
      (spatialFree (-t) (localForce (gauge t) coupling (scalar t) (curve t)+inversePrincipal 0 (source t))) t)
    (time : ℝ) :
    curve time=fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time initial+
      ∫ r in (0 : ℝ)..time, fullOperator gauge continuousGauge coupling scalar continuousScalar r time
        (inversePrincipal 0 (source r)) := by
  have generated := congrArg (fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time)
    (returned_integral gauge continuousGauge coupling scalar continuousScalar curve source continuousSource initial starts evolves time)
  rw [fullOperator_inverse,map_add] at generated
  have pull := (fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time).intervalIntegral_comp_comm
    ((source_kernel_continuous gauge continuousGauge coupling scalar continuousScalar source continuousSource 0).intervalIntegrable
      (μ := volume) 0 time)
  erw [← pull] at generated
  simpa only [fullOperator_compose] using! generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
