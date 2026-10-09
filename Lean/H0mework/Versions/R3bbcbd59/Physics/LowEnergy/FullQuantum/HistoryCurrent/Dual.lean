import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryCurrent.Inverse
import H0mework.Physics.LowEnergy.FullQuantum.HistoryCurrent.Adjoint

/-! The original independent dual varies through the actual inverse history and its original C0 pairing. -/
set_option autoImplicit false
open scoped InnerProductSpace
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

def dualFamily (epsilon time : ℝ) : SpatialOperators :=
  originalDualOperator (gaugeFamily gauge direction epsilon)
    (gaugeFamily_continuous gauge direction continuousGauge continuousDirection epsilon) coupling
    (scalarFamily scalar scalarDirection epsilon)
    (scalarFamily_continuous scalar scalarDirection continuousScalar continuousScalarDirection epsilon) 0 time

theorem dualFamily_apply (epsilon time : ℝ) (dual : FullMatterL2) :
    dualFamily gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon time dual=
      (inversePrincipal 0).adjoint ((U epsilon time 0).adjoint ((principal 0).adjoint dual)) := rfl

theorem dualFamily_pair (epsilon time : ℝ) (dual initial : FullMatterL2) :
    inner ℂ (dualFamily gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon time dual) (principal 0 (U epsilon 0 time initial))=
      inner ℂ dual (principal 0 initial) := original_pair_preserved _ _ _ _ _ _ _ _ _

attribute [local irreducible] fullOperator familyOperator originalDualOperator responseOperator dualFamily

theorem dualFamily_operator (epsilon time : ℝ) :
    dualFamily gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon time=
      (inversePrincipal 0).adjoint * (U epsilon time 0).adjoint * (principal 0).adjoint := by
  apply ContinuousLinearMap.ext
  intro dual
  simp only [mul_apply_eq_comp,dualFamily_apply]

theorem dualFamily_derivative (time : ℝ) :
    HasDerivAt (fun epsilon : ℝ => dualFamily gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon time)
      ((inversePrincipal 0).adjoint * (-(U 0 time 0 * D time * U 0 time 0)).adjoint * (principal 0).adjoint) 0 := by
  have reversed := reverse_derivative gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection time
  have differentiated := ((adjoint_derivative _ 0 _ reversed).const_mul (inversePrincipal 0).adjoint).mul_const (principal 0).adjoint
  simpa only [dualFamily_operator,ContinuousLinearMap.star_eq_adjoint] using! differentiated

theorem dualFamily_read (epsilon time : ℝ) (dual input : FullMatterL2) :
    inner ℂ (dualFamily gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon time dual) input=
      inner ℂ dual (principal 0 (U epsilon time 0 (inversePrincipal 0 input))) := by
  rw [dualFamily_apply]
  simp only [ContinuousLinearMap.adjoint_inner_left]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
