import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.CutoffEnergy
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory Metric
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel
open scoped ContDiff Topology
noncomputable section

def cutoffSeed : ContDiffBump (0 : Point) := ⟨1, 2, by norm_num, by norm_num⟩

theorem cutoffSeed_smooth : ContDiff ℝ ∞ (cutoffSeed : Point → ℝ) := cutoffSeed.contDiff

theorem cutoffSeed_derivative_bounded : ∃ bound : ℝ, ∀ point : Point,
    ‖fderiv ℝ (cutoffSeed : Point → ℝ) point‖ ≤ bound :=
  (cutoffSeed.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (contDiff_infty_iff_fderiv.mp cutoffSeed_smooth).2.continuous

def cutoffDerivativeBound : ℝ := max 1 cutoffSeed_derivative_bounded.choose

theorem cutoffDerivativeBound_positive : 0 < cutoffDerivativeBound :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem cutoffSeed_derivative_bound (point : Point) :
    ‖fderiv ℝ (cutoffSeed : Point → ℝ) point‖ ≤ cutoffDerivativeBound :=
  (cutoffSeed_derivative_bounded.choose_spec point).trans (le_max_right _ _)

def cutoff (radius : ℝ) (point : Point) : ℝ := cutoffSeed (radius⁻¹ • point)

theorem cutoff_smooth (radius : ℝ) : ContDiff ℝ ∞ (cutoff radius) :=
  cutoffSeed_smooth.comp (((radius⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ Point)).contDiff)

theorem cutoff_compact (radius : ℝ) (positive : 0 < radius) : HasCompactSupport (cutoff radius) :=
  cutoffSeed.hasCompactSupport.comp_smul (inv_ne_zero positive.ne')

theorem cutoff_nonnegative (radius : ℝ) (point : Point) : 0 ≤ cutoff radius point := cutoffSeed.nonneg
theorem cutoff_le_one (radius : ℝ) (point : Point) : cutoff radius point ≤ 1 := cutoffSeed.le_one

theorem cutoff_one (radius : ℝ) (positive : 0 < radius) (point : Point) (inside : ‖point‖ ≤ radius) :
    cutoff radius point = 1 := by
  apply cutoffSeed.one_of_mem_closedBall
  change dist (radius⁻¹ • point) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_pos.mpr positive).le]
  exact (mul_le_mul_of_nonneg_left inside (inv_pos.mpr positive).le).trans_eq (inv_mul_cancel₀ positive.ne')

theorem cutoff_zero (radius : ℝ) (positive : 0 < radius) (point : Point) (outside : 2*radius ≤ ‖point‖) :
    cutoff radius point = 0 := by
  change cutoffSeed (radius⁻¹ • point) = 0
  apply Function.notMem_support.mp
  rw [cutoffSeed.support_eq]
  change ¬ dist (radius⁻¹ • point) 0 < 2
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_pos.mpr positive).le, not_lt]
  have bound := mul_le_mul_of_nonneg_left outside (inv_pos.mpr positive).le
  have cancel : radius⁻¹*(2*radius) = 2 := by field_simp
  rw [cancel] at bound
  exact bound

theorem cutoff_first (radius : ℝ) (point : Point) (index : Fin 3) :
    spatialFirst (cutoff radius) index point = radius⁻¹*spatialFirst cutoffSeed index (radius⁻¹ • point) := by
  have generated := ((cutoffSeed_smooth.differentiable (by simp)) (radius⁻¹ • point)).hasFDerivAt.comp point
    ((radius⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ Point)).hasFDerivAt
  change HasFDerivAt (cutoff radius) _ point at generated
  unfold spatialFirst
  rw [generated.fderiv]
  simp

theorem axis_norm (index : Fin 3) : ‖axis index‖ = 1 := by
  rw [axis, Pi.norm_single]
  norm_num

theorem cutoff_first_bound (radius : ℝ) (positive : 0 < radius) (point : Point) (index : Fin 3) :
    ‖spatialFirst (cutoff radius) index point‖ ≤ cutoffDerivativeBound/radius := by
  rw [cutoff_first, norm_mul, Real.norm_of_nonneg (inv_pos.mpr positive).le]
  have bound : ‖spatialFirst cutoffSeed index (radius⁻¹ • point)‖ ≤ cutoffDerivativeBound := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    simpa only [axis_norm, mul_one] using cutoffSeed_derivative_bound (radius⁻¹ • point)
  simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left bound (inv_pos.mpr positive).le

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
