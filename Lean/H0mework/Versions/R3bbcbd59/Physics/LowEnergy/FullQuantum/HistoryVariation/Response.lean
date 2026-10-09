import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Bounds

/-! The exact source insertion is integrated on the same complete spatial propagator. -/
set_option autoImplicit false
open MeasureTheory Set
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryForcing PerturbedGreen
noncomputable section
variable (gauge direction : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)
local notation "U" => familyOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
attribute [local irreducible] fullOperator

def insertionIntegrand (epsilon time : ℝ) (initial : FullMatterL2) (r : ℝ) : FullMatterL2 :=
  fullOperator gauge continuousGauge coupling scalar continuousScalar r time
    (localForce (direction r) coupling (scalarDirection r) (U epsilon 0 r initial))

theorem insertionIntegrand_continuous (epsilon time : ℝ) (initial : FullMatterL2) :
    Continuous (insertionIntegrand gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon time initial) := by
  let source (r : ℝ) := principal 0 (localForce (direction r) coupling (scalarDirection r) (U epsilon 0 r initial))
  have continuousSource : Continuous source := (principal 0).continuous.comp
    ((HistoryLaplace.localForce_continuous direction continuousDirection coupling scalarDirection continuousScalarDirection).clm_apply
      (familyOperator_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
        continuousScalar continuousScalarDirection epsilon 0 initial))
  have generated := source_kernel_continuous gauge continuousGauge coupling scalar continuousScalar source continuousSource time
  simpa only [source,inversePrincipal_left,insertionIntegrand] using! generated

def insertionResponse (epsilon time : ℝ) (initial : FullMatterL2) : FullMatterL2 :=
  ∫ r in (0 : ℝ)..time, insertionIntegrand gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection epsilon time initial r

theorem family_difference (epsilon time : ℝ) (initial : FullMatterL2) :
    U epsilon 0 time initial-fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time initial=
      (epsilon : ℂ) • insertionResponse gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
        continuousScalar continuousScalarDirection epsilon time initial := by
  have generated := finite_variation gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection epsilon time initial
  exact sub_eq_of_eq_add (generated.trans (add_comm _ _))

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
