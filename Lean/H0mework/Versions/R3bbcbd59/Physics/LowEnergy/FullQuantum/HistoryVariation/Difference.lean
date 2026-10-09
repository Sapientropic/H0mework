import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Fields

/-! The difference of two actual source histories is driven by the exact primitive insertion. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryForcing PerturbedGreen
noncomputable section
variable (gauge direction : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)
local notation "U" => familyOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
attribute [local irreducible] fullOperator

def variationSource (epsilon : ℝ) (initial : FullMatterL2) (time : ℝ) : FullMatterL2 :=
  (epsilon : ℂ) • principal 0
    (localForce (direction time) coupling (scalarDirection time) (U epsilon 0 time initial))

theorem variationSource_continuous (epsilon : ℝ) (initial : FullMatterL2) :
    Continuous (variationSource gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon initial) := by
  have force := (HistoryLaplace.localForce_continuous direction continuousDirection coupling scalarDirection continuousScalarDirection).clm_apply
    (familyOperator_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon 0 initial)
  simpa only [variationSource,Function.comp_def,Pi.smul_apply] using!
    (continuous_const : Continuous (fun _ : ℝ => (epsilon : ℂ))).smul ((principal 0).continuous.comp force)

theorem varied_free_equation (epsilon time : ℝ) (initial : FullMatterL2) :
    HasDerivAt (fun t => spatialFree (-t) (U epsilon 0 t initial))
      (spatialFree (-time) (localForce (gauge time) coupling (scalar time) (U epsilon 0 time initial)+
        inversePrincipal 0 (variationSource gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
          continuousScalar continuousScalarDirection epsilon initial time))) time := by
  have generated := full_freeInteraction_equation (gaugeFamily gauge direction epsilon)
    (gaugeFamily_continuous gauge direction continuousGauge continuousDirection epsilon) coupling
    (scalarFamily scalar scalarDirection epsilon)
    (scalarFamily_continuous scalar scalarDirection continuousScalar continuousScalarDirection epsilon) 0 time initial
  change HasDerivAt (fun t => spatialFree (-t) (U epsilon 0 t initial))
    (spatialFree (-time) (localForce (gaugeFamily gauge direction epsilon time) coupling
      (scalarFamily scalar scalarDirection epsilon time) (U epsilon 0 time initial))) time at generated
  rw [localForce_affine,add_apply,smul_apply] at generated
  simpa only [variationSource,map_smul,inversePrincipal_left] using! generated

theorem finite_variation (epsilon time : ℝ) (initial : FullMatterL2) :
    U epsilon 0 time initial=
      fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time initial+
        (epsilon : ℂ) • ∫ r in (0 : ℝ)..time,
          fullOperator gauge continuousGauge coupling scalar continuousScalar r time
            (localForce (direction r) coupling (scalarDirection r) (U epsilon 0 r initial)) := by
  have generated := original_retarded_equation gauge continuousGauge coupling scalar continuousScalar
    (fun t => U epsilon 0 t initial)
    (variationSource gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon initial)
    (variationSource_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon initial) initial
    (familyOperator_starts gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon 0 initial)
    (fun t => varied_free_equation gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon t initial) time
  simpa only [variationSource,map_smul,inversePrincipal_left,intervalIntegral.integral_smul] using! generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
