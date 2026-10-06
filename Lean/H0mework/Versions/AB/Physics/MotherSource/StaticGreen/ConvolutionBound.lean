import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Potential

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
noncomputable section

def nearMass : ℝ := ∫ point : Point, ‖nearKernel point‖

theorem norm_kernel_bound (point : Point) : ‖point‖*kernel point ≤ 1 := by
  by_cases zero : point = 0
  · simp [zero]
  · calc
      _ ≤ ‖point‖*‖point‖⁻¹ := mul_le_mul_of_nonneg_left (kernel_le_norm_inverse point) (norm_nonneg _)
      _ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.mpr zero)

theorem kernel_integral_bound (f : Point → ℝ) (integrable : Integrable f)
    (bound : ℝ) (bounded : ∀ point, ‖f point‖ ≤ bound) :
    (∫ point, ‖f point*kernel point‖) ≤ bound*nearMass+∫ point, ‖f point‖ := by
  have domination (point : Point) : ‖f point*kernel point‖ ≤ bound*‖nearKernel point‖+‖f point‖ := by
    rw [← kernel_parts point, mul_add]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (bounded point) (norm_nonneg _)
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (far_bound point)
  have comparison := integral_mono (integrable_mul_kernel f integrable bound bounded).norm
    ((near_integrable.norm.const_mul bound).add integrable.norm) domination
  simp only [Pi.add_apply] at comparison
  rw [integral_add (near_integrable.norm.const_mul bound) integrable.norm, integral_const_mul] at comparison
  exact comparison

theorem convolution_uniform_bound (f : Point → ℝ) (integrable : Integrable f)
    (bound : ℝ) (bounded : ∀ point, ‖f point‖ ≤ bound) (position : Point) :
    ‖∫ point, f (position-point)*kernel point‖ ≤ bound*nearMass+∫ point, ‖f point‖ := by
  apply (norm_integral_le_integral_norm _).trans
  have result := kernel_integral_bound (fun point => f (position-point))
    (integrable.comp_sub_left position) bound (fun point => bounded (position-point))
  rw [integral_sub_left_eq_self (fun point => ‖f point‖) volume position] at result
  exact result

theorem convolution_weighted_bound (f : Point → ℝ) (integrable : Integrable f)
    (bound : ℝ) (bounded : ∀ point, ‖f point‖ ≤ bound)
    (momentIntegrable : Integrable (fun point => ‖point‖*‖f point‖))
    (momentBound : ℝ) (momentBounded : ∀ point, ‖point‖*‖f point‖ ≤ momentBound) (position : Point) :
    ‖position‖*‖∫ point, f (position-point)*kernel point‖ ≤
      momentBound*nearMass+(∫ point, ‖point‖*‖f point‖)+(∫ point, ‖f point‖) := by
  have weightedBounded (point : Point) : ‖‖point‖*‖f point‖‖ ≤ momentBound := by
    simpa only [norm_mul, norm_norm] using momentBounded point
  have weightedIntegral := integrable_mul_kernel _ (momentIntegrable.comp_sub_left position)
    momentBound (fun point => weightedBounded (position-point))
  have unweightedIntegral := integrable_mul_kernel _ (integrable.comp_sub_left position)
    bound (fun point => bounded (position-point))
  have pointwise (point : Point) : ‖position‖*‖f (position-point)*kernel point‖ ≤
      (‖position-point‖*‖f (position-point)‖)*kernel point+‖f (position-point)‖ := by
    rw [norm_mul, Real.norm_of_nonneg (kernel_nonnegative point)]
    have triangle : ‖position‖ ≤ ‖position-point‖+‖point‖ := by
      simpa only [sub_add_cancel] using norm_add_le (position-point) point
    have times := mul_le_mul_of_nonneg_right triangle
      (mul_nonneg (norm_nonneg (f (position-point))) (kernel_nonnegative point))
    have kernel := mul_le_mul_of_nonneg_right (norm_kernel_bound point) (norm_nonneg (f (position-point)))
    nlinarith
  calc
    _ ≤ ‖position‖*(∫ point, ‖f (position-point)*kernel point‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = ∫ point, ‖position‖*‖f (position-point)*kernel point‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ point, (‖position-point‖*‖f (position-point)‖)*kernel point+‖f (position-point)‖ :=
      integral_mono (unweightedIntegral.norm.const_mul _) (weightedIntegral.add (integrable.comp_sub_left position).norm) pointwise
    _ = (∫ point, (‖position-point‖*‖f (position-point)‖)*kernel point)+(∫ point, ‖f point‖) := by
      rw [integral_add weightedIntegral (integrable.comp_sub_left position).norm,
        integral_sub_left_eq_self (fun point => ‖f point‖) volume position]
    _ ≤ _ := by
      have result := convolution_uniform_bound _ momentIntegrable momentBound weightedBounded position
      simp only [norm_mul, norm_norm] at result
      exact add_le_add ((le_abs_self _).trans result) le_rfl

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
