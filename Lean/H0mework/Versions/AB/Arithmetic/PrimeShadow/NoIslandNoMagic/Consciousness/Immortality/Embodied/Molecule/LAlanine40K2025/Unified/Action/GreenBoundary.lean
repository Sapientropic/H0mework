import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.CutoffSupport
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenDecay
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open MeasureTheory Metric BasinRefinement SourceGaussianModel
noncomputable section

def boundaryError (radius : ℝ) (point : Point) : ℝ := sourcePotential point^2*gradientSquare (cutoff radius) point

def boundaryConstant : ℝ := 192*potentialDecayConstant^2*cutoffDerivativeBound^2

theorem boundaryError_nonnegative (radius : ℝ) (point : Point) : 0 ≤ boundaryError radius point :=
  mul_nonneg (sq_nonneg _) (gradientSquare_nonnegative _ _)

theorem boundaryError_continuous (radius : ℝ) : Continuous (boundaryError radius) :=
  (sourcePotential_smooth.continuous.pow 2).mul (gradientSquare_continuous (cutoff_smooth radius))

theorem boundaryError_zero_outside (radius : ℝ) (positive : 0 < radius) (point : Point)
    (outside : point ∉ closedBall (0 : Point) (2*radius)) : boundaryError radius point = 0 := by
  have far : 2*radius < ‖point‖ := by simpa using outside
  simp only [boundaryError, cutoff_gradient_zero_outside radius positive point far, mul_zero]

theorem boundaryError_integrable (radius : ℝ) (positive : 0 < radius) : Integrable (boundaryError radius) :=
  ((boundaryError_continuous radius).locallyIntegrable.integrableOn_isCompact (isCompact_closedBall (0 : Point) (2*radius))).integrable_of_forall_notMem_eq_zero
    (boundaryError_zero_outside radius positive)

theorem boundaryError_point_bound (radius : ℝ) (positive : 0 < radius) (point : Point) :
    boundaryError radius point ≤ (potentialDecayConstant/radius)^2*(3*(cutoffDerivativeBound/radius)^2) := by
  by_cases inside : ‖point‖ < radius
  · simp only [boundaryError, cutoff_gradient_zero_inside radius positive point inside, mul_zero]
    positivity
  · have potential := sourcePotential_far_bound radius positive point (le_of_not_gt inside)
    have squared := (sq_le_sq₀ (norm_nonneg _) (div_nonneg potentialDecayConstant_nonnegative positive.le)).mpr potential
    simp only [Real.norm_eq_abs, sq_abs] at squared
    exact mul_le_mul squared (cutoff_gradient_bound radius positive point)
      (gradientSquare_nonnegative _ _) (sq_nonneg _)

theorem cutoff_box_volume (radius : ℝ) (positive : 0 < radius) :
    volume.real (closedBall (0 : Point) (2*radius)) = (4*radius)^3 := by
  rw [MeasureTheory.measureReal_def,
    Real.volume_pi_closedBall (0 : Fin 3 → ℝ) (show 0 ≤ 2*radius by positivity), Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]
  ring

theorem boundary_error_bound (radius : ℝ) (positive : 0 < radius) :
    (∫ point : Point, boundaryError radius point) ≤ boundaryConstant/radius := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (boundaryError_zero_outside radius positive)]
  have finite : volume (closedBall (0 : Point) (2*radius)) < ⊤ := (isCompact_closedBall _ _).measure_lt_top
  have bound := norm_setIntegral_le_of_norm_le_const finite
    (fun point _ => show ‖boundaryError radius point‖ ≤ _ from
      (Real.norm_of_nonneg (boundaryError_nonnegative radius point)) ▸ boundaryError_point_bound radius positive point)
  rw [cutoff_box_volume radius positive] at bound
  apply (le_abs_self _).trans
  apply bound.trans_eq
  unfold boundaryConstant
  field_simp
  ring

theorem boundaryConstant_nonnegative : 0 ≤ boundaryConstant := by unfold boundaryConstant; positivity

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
