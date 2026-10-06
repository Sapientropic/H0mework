import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.CutoffLaplacian
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenBoundary

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open MeasureTheory Metric BasinRefinement SourceGaussianModel
noncomputable section

def laplacianBoundary (radius : ℝ) (point : Point) : ℝ := sourcePotential point^2*spatialLap (cutoff radius) point
def laplacianBoundaryConstant : ℝ := 64*potentialDecayConstant^2*cutoffLaplacianBound

theorem laplacianBoundary_continuous (radius : ℝ) : Continuous (laplacianBoundary radius) :=
  (sourcePotential_smooth.continuous.pow 2).mul (spatialLap_smooth (cutoff_smooth radius)).continuous

theorem laplacianBoundary_zero_outside (radius : ℝ) (positive : 0 < radius) (point : Point)
    (outside : point ∉ closedBall (0 : Point) (2*radius)) : laplacianBoundary radius point = 0 := by
  have far : 2*radius < ‖point‖ := by simpa using outside
  simp only [laplacianBoundary, cutoff_laplacian_zero_outside radius positive point far, mul_zero]

theorem laplacianBoundary_integrable (radius : ℝ) (positive : 0 < radius) : Integrable (laplacianBoundary radius) :=
  ((laplacianBoundary_continuous radius).locallyIntegrable.integrableOn_isCompact (isCompact_closedBall (0 : Point) (2*radius))).integrable_of_forall_notMem_eq_zero
    (laplacianBoundary_zero_outside radius positive)

theorem cutoffLaplacianBound_positive : 0 < cutoffLaplacianBound := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem laplacianBoundary_point_bound (radius : ℝ) (positive : 0 < radius) (point : Point) :
    ‖laplacianBoundary radius point‖ ≤ (potentialDecayConstant/radius)^2*(radius⁻¹^2*cutoffLaplacianBound) := by
  by_cases inside : ‖point‖ < radius
  · simp only [laplacianBoundary, cutoff_laplacian_zero_inside radius positive point inside, mul_zero, norm_zero]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) cutoffLaplacianBound_positive.le)
  · have potential := sourcePotential_far_bound radius positive point (le_of_not_gt inside)
    have squared := (sq_le_sq₀ (norm_nonneg _) (div_nonneg potentialDecayConstant_nonnegative positive.le)).mpr potential
    rw [laplacianBoundary, norm_mul, norm_pow]
    exact mul_le_mul squared (cutoff_laplacian_bound radius point) (norm_nonneg _) (sq_nonneg _)

theorem laplacian_boundary_bound (radius : ℝ) (positive : 0 < radius) :
    ‖∫ point : Point, laplacianBoundary radius point‖ ≤ laplacianBoundaryConstant/radius := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (laplacianBoundary_zero_outside radius positive)]
  have finite : volume (closedBall (0 : Point) (2*radius)) < ⊤ := (isCompact_closedBall _ _).measure_lt_top
  have bound := norm_setIntegral_le_of_norm_le_const finite (fun point _ => laplacianBoundary_point_bound radius positive point)
  rw [cutoff_box_volume radius positive] at bound
  apply bound.trans_eq
  unfold laplacianBoundaryConstant
  field_simp
  ring

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
