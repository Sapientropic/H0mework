import H0mework.Physics.Homogeneous.CoframeDifferential
import H0mework.Physics.Exterior.MotherAction

/-! The original coframe Hodge responds to every coframe direction. The
isotropic magnetic contraction retains precisely its diagonal first variation. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Dynamics.Homogeneous

open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction
open StageNineBlockwiseConstitutive StageNineCartanTangentSimplicityResponse
open EmpiricalReferenceScaleCouplingBoundary

noncomputable section

def magneticHodgeTrace (coframe : LorentzianCoframe) : ℝ :=
  gaugeOperatorCoefficient (coframeGaugeSpacetimeHodgeLinear coframe) 3 0 +
    gaugeOperatorCoefficient (coframeGaugeSpacetimeHodgeLinear coframe) 4 1 +
    gaugeOperatorCoefficient (coframeGaugeSpacetimeHodgeLinear coframe) 5 2

theorem magneticHodgeTangent_trace (lapse : ℝ) (nonzero : lapse ≠ 0)
    (direction : LorentzianCoframe) :
    coframeHodgeTangent (homogeneousCoframe lapse) direction (fun i => if i = 0 then 1 else 0) 3 +
      coframeHodgeTangent (homogeneousCoframe lapse) direction (fun i => if i = 1 then 1 else 0) 4 +
      coframeHodgeTangent (homogeneousCoframe lapse) direction (fun i => if i = 2 then 1 else 0) 5 =
      lapse * (direction 1 1 + direction 2 2 + direction 3 3) - 3 * direction 0 0 := by
  simp only [coframeHodgeTangent, homogeneousCoframe_inv lapse nonzero]
  simp [coframeTwoFormTangent, coframeWedgeTangent, coframeTwoFormLinear,
    lorentzianCoframeHodge, coframeWedge, homogeneousCoframe, pairFirst, pairSecond,
    Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_six]
  field_simp
  ring

theorem magneticHodgeTrace_line_hasDerivAt (lapse : ℝ) (positive : 0 < lapse)
    (direction : LorentzianCoframe) :
    HasDerivAt (fun t : ℝ => magneticHodgeTrace (homogeneousCoframe lapse + t • direction))
      (lapse * (direction 1 1 + direction 2 2 + direction 3 3) - 3 * direction 0 0) 0 := by
  have first := coframeHodge_line_hasDerivAt (homogeneousCoframe lapse) direction
    (homogeneousCoframe_nondegenerate lapse positive) (fun i => if i = 0 then 1 else 0) 3
  have second := coframeHodge_line_hasDerivAt (homogeneousCoframe lapse) direction
    (homogeneousCoframe_nondegenerate lapse positive) (fun i => if i = 1 then 1 else 0) 4
  have third := coframeHodge_line_hasDerivAt (homogeneousCoframe lapse) direction
    (homogeneousCoframe_nondegenerate lapse positive) (fun i => if i = 2 then 1 else 0) 5
  have total := (first.add second).add third
  rw [magneticHodgeTangent_trace lapse (ne_of_gt positive)] at total
  convert! total using 1

end
end SaturationMonoid.PhysicsCore.Stage9C.Dynamics.Homogeneous
