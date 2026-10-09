import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Derivative
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The actual reverse history has the inverse derivative in the primitive field parameter. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryVariation PerturbedGreen
noncomputable section
variable (gauge direction : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)
local notation "U" => familyOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
local notation "D" => responseOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
attribute [local irreducible] fullOperator

def familyUnit (epsilon time : ℝ) : SpatialOperatorsˣ where
  val := U epsilon 0 time
  inv := U epsilon time 0
  val_inv := by
    apply ContinuousLinearMap.ext
    intro field
    exact fullOperator_inverse _ _ _ _ _ time 0 field
  inv_val := by
    apply ContinuousLinearMap.ext
    intro field
    exact fullOperator_inverse _ _ _ _ _ 0 time field

theorem family_ringInverse (epsilon time : ℝ) : Ring.inverse (U epsilon 0 time)=U epsilon time 0 :=
  Ring.inverse_unit (familyUnit gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection epsilon time)

theorem reverse_derivative (time : ℝ) :
    HasDerivAt (fun epsilon : ℝ => U epsilon time 0)
      (-(U 0 time 0 * D time * U 0 time 0)) 0 := by
  have differentiated := (hasFDerivAt_ringInverse (𝕜 := ℝ)
    (familyUnit gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection 0 time)).comp_hasDerivAt 0
        (familyOperator_derivative gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
          continuousScalar continuousScalarDirection time)
  simpa only [familyUnit,Function.comp_def,neg_apply,ContinuousLinearMap.mulLeftRight_apply,
    family_ringInverse] using! differentiated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
