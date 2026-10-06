import H0mework.Chemistry.LAlanineBandGlobalSource.Decay.Term
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.SourceCoulomb
open SourceGaussianModel GlobalSource MeasureTheory Set Metric
open scoped BigOperators
noncomputable section

/-- Cartesian Bohr coordinates use the Euclidean Coulomb distance, including its integrable singularity. -/
def distance (x : Point) : ℝ := Real.sqrt (∑ i : Fin 3, x i ^ 2)
def kernel (x : Point) : ℝ := (distance x)⁻¹

theorem distance_nonnegative (x : Point) : 0 ≤ distance x := Real.sqrt_nonneg _
theorem kernel_nonnegative (x : Point) : 0 ≤ kernel x := inv_nonneg.mpr (distance_nonnegative x)

theorem pi_norm_le_distance (x : Point) : ‖x‖ ≤ distance x := by
  apply (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))).mpr
  exact pi_norm_sq_le_sum_sq x

theorem kernel_le_norm_inverse (x : Point) : kernel x ≤ ‖x‖⁻¹ := by
  by_cases h : x = 0
  · simp [h,kernel,distance]
  · exact inv_anti₀ (norm_pos_iff.mpr h) (pi_norm_le_distance x)

theorem distance_continuous : Continuous distance := by
  unfold distance
  fun_prop

theorem kernel_measurable : Measurable kernel := distance_continuous.measurable.inv

theorem kernel_ball_integrable (r : ℝ) : IntegrableOn kernel (ball 0 r) := by
  apply integrableOn_ball_of_norm_le_rpow
    (by norm_num : 1 ≤ Module.finrank ℝ Point) (α := 1) (C := 1)
    (by norm_num : (1 : ℝ) < Module.finrank ℝ Point) _ kernel_measurable.aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs,abs_of_nonneg (kernel_nonnegative x),one_mul,Real.rpow_neg_one]
    using kernel_le_norm_inverse x

theorem kernel_le_one_outside (x : Point) (outside : x ∉ ball (0 : Point) 1) : kernel x ≤ 1 := by
  have h : 1 ≤ ‖x‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using outside
  exact (kernel_le_norm_inverse x).trans (inv_le_one_of_one_le₀ h)

end
end LAlanine40K2025.BasinRefinement.SourceCoulomb
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
