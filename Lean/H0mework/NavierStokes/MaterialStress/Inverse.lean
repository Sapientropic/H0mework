import H0mework.Physics.Cauchy.CoframeHolonomicCauchySafeRealization
import H0mework.Physics.Coframe.CoframeLocalDifferentiability

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise Topology

namespace SaturationMonoid.NavierStokes.NativeCoframeInverseAction

open PhysicsCore Filter
open StageNineCoframeVariation StageNineCoframeHolonomicCauchySafeRealization

noncomputable section

def inverseLinear (frame : LorentzianCoframe) : LorentzianCoframe →ₗ[ℝ] LorentzianCoframe where
  toFun direction := -(frame⁻¹ * direction * frame⁻¹)
  map_add' := by intro first second; simp [mul_add, add_mul, add_comm]
  map_smul' := by intro scalar direction; simp

def inverseDerivative (frame : LorentzianCoframe) : LorentzianCoframe →L[ℝ] LorentzianCoframe :=
  (inverseLinear frame).toContinuousLinearMap

theorem inverseDerivative_apply (frame direction : LorentzianCoframe) :
    inverseDerivative frame direction = -(frame⁻¹ * direction * frame⁻¹) := rfl

/-- The actual nonsingular inverse is differentiated in the repository's coframe norm. -/
theorem inverse_hasFDerivAt (frame : LorentzianCoframe) (nondegenerate : frame.det ≠ 0) :
    HasFDerivAt (fun candidate : LorentzianCoframe => candidate⁻¹) (inverseDerivative frame) frame := by
  let derivative := fderiv ℝ (fun candidate : LorentzianCoframe => candidate⁻¹) frame
  have inverseDifferentiable : HasFDerivAt (fun candidate : LorentzianCoframe => candidate⁻¹) derivative frame :=
    ((coframe_inv_contDiffAt frame nondegenerate).differentiableAt (by simp)).hasFDerivAt
  have productDerivative := coframeMatrixRealMulBilinear.toContinuousBilinearMap.hasFDerivAt_of_bilinear
    (hasFDerivAt_id frame) inverseDifferentiable
  have locally : (fun candidate : LorentzianCoframe => candidate * candidate⁻¹) =ᶠ[𝓝 frame]
      (fun _ => 1) := by
    filter_upwards [coframe_det_contDiff.continuous.continuousAt.eventually_ne nondegenerate] with candidate invertible
    exact Matrix.mul_nonsing_inv candidate (isUnit_iff_ne_zero.mpr invertible)
  have constantDerivative : HasFDerivAt (fun candidate : LorentzianCoframe => candidate * candidate⁻¹) 0 frame :=
    (hasFDerivAt_const (𝕜 := ℝ) (1 : LorentzianCoframe) frame).congr_of_eventuallyEq locally
  have derivativeZero := productDerivative.unique constantDerivative
  have explicit : derivative = inverseDerivative frame := by
    ext direction row column
    have evaluated := congrArg (fun linear : LorentzianCoframe →L[ℝ] LorentzianCoframe => linear direction) derivativeZero
    change frame * derivative direction + direction * frame⁻¹ = 0 at evaluated
    have solved := congrArg (fun matrix : LorentzianCoframe => frame⁻¹ * matrix) evaluated
    rw [mul_add, ← mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr nondegenerate), one_mul,
      mul_zero, ← mul_assoc] at solved
    have value : derivative direction = -(frame⁻¹ * direction * frame⁻¹) := eq_neg_of_add_eq_zero_left solved
    exact congrFun (congrFun value row) column
  rw [explicit] at inverseDifferentiable
  exact inverseDifferentiable

end
end SaturationMonoid.NavierStokes.NativeCoframeInverseAction
