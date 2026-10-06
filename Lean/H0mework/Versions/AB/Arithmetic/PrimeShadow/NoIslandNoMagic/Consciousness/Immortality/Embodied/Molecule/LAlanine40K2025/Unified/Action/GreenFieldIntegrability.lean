import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenBoundary
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenInteraction
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open MeasureTheory Metric Filter BasinRefinement SourceGaussianModel
noncomputable section

theorem source_current_potential_integrable : Integrable (fun point => sourceCurrent point*sourcePotential point) :=
  current_potential_integrable sourceCurrent sourceCurrent_integrable _ sourceCurrent_bound

def couplingMass : ℝ := ∫ point : Point, ‖sourceCurrent point*sourcePotential point‖

def cutoffCoupling (radius : ℝ) (point : Point) : ℝ :=
  sourceCurrent point*(cutoff radius point*cutoff radius point*sourcePotential point)

theorem cutoffCoupling_bound (radius : ℝ) (point : Point) :
    ‖cutoffCoupling radius point‖ ≤ ‖sourceCurrent point*sourcePotential point‖ := by
  have square : cutoff radius point*cutoff radius point ≤ 1 := by
    nlinarith [cutoff_nonnegative radius point, cutoff_le_one radius point]
  have same : cutoffCoupling radius point = (cutoff radius point*cutoff radius point)*(sourceCurrent point*sourcePotential point) := by
    unfold cutoffCoupling; ring
  rw [same, norm_mul, Real.norm_of_nonneg (mul_nonneg (cutoff_nonnegative radius point) (cutoff_nonnegative radius point))]
  exact mul_le_of_le_one_left (norm_nonneg _) square

theorem cutoffCoupling_integrable (radius : ℝ) : Integrable (cutoffCoupling radius) := by
  apply source_current_potential_integrable.norm.mono' ?_ (Eventually.of_forall (cutoffCoupling_bound radius))
  exact (sourceCurrent_smooth.continuous.mul
    (((cutoff_smooth radius).continuous.mul (cutoff_smooth radius).continuous).mul sourcePotential_smooth.continuous)).aestronglyMeasurable

theorem cutoffCoupling_integral_bound (radius : ℝ) : ‖∫ point : Point, cutoffCoupling radius point‖ ≤ couplingMass :=
  (norm_integral_le_integral_norm _).trans
    (integral_mono (cutoffCoupling_integrable radius).norm source_current_potential_integrable.norm (cutoffCoupling_bound radius))

def fieldEnergyBound : ℝ := couplingMass/(2*lapse)+boundaryConstant

theorem cutoff_energy_uniform (radius : ℝ) (large : 1 ≤ radius) :
    (∫ point : Point, gradientSquare (fun p => cutoff radius p*sourcePotential p) point) ≤ fieldEnergyBound := by
  have positive : 0 < radius := lt_of_lt_of_le zero_lt_one large
  have identity := original_D3_cutoff_energy (cutoff radius) (cutoff_smooth radius) (cutoff_compact radius positive)
  change lapse*(_) = -(1/2)*(∫ point, cutoffCoupling radius point)+lapse*(∫ point, boundaryError radius point) at identity
  have boundary := boundary_error_bound radius positive
  have bound : boundaryConstant/radius ≤ boundaryConstant := by
    apply (div_le_iff₀ positive).mpr
    nlinarith [mul_le_mul_of_nonneg_left large boundaryConstant_nonnegative]
  have current := neg_le_abs (∫ point, cutoffCoupling radius point)
  have currentBound := cutoffCoupling_integral_bound radius
  rw [Real.norm_eq_abs] at currentBound
  have lapsePositive := lapse_pos
  unfold fieldEnergyBound
  have division : lapse*(couplingMass/(2*lapse)) = couplingMass/2 := by field_simp
  apply (mul_le_mul_iff_right₀ lapsePositive).mp
  nlinarith

theorem source_gradient_integrable : Integrable (gradientSquare sourcePotential) := by
  let balls : AECover volume atTop (fun radius : ℝ => closedBall (0 : Point) radius) := aecover_closedBall tendsto_id
  apply balls.integrable_of_integral_bounded_of_nonneg_ae fieldEnergyBound
  · intro radius
    exact (gradientSquare_continuous sourcePotential_smooth).locallyIntegrable.integrableOn_isCompact (isCompact_closedBall _ _)
  · exact Eventually.of_forall (gradientSquare_nonnegative sourcePotential)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with radius nonnegative
    have positive : 0 < radius+1 := by linarith
    have same : (∫ point in closedBall (0 : Point) radius, gradientSquare sourcePotential point) =
        ∫ point in closedBall (0 : Point) radius, gradientSquare (fun p => cutoff (radius+1) p*sourcePotential p) point := by
      apply setIntegral_congr_fun measurableSet_closedBall
      intro point member
      have inside : ‖point‖ < radius+1 := lt_of_le_of_lt (by simpa using member) (by linarith)
      exact (cutoff_product_gradient_inside sourcePotential sourcePotential_smooth (radius+1) positive point inside).symm
    rw [same]
    apply (setIntegral_le_integral
      (gradientSquare_integrable ((cutoff_smooth (radius+1)).mul sourcePotential_smooth) (cutoff_compact (radius+1) positive).mul_right)
      (Eventually.of_forall (gradientSquare_nonnegative _))).trans
    exact cutoff_energy_uniform (radius+1) (by linarith)

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
