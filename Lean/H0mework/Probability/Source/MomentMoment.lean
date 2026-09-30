import H0mework.Probability.Source.ConditionalNext

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceVectorMoment

open scoped InnerProductSpace
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population (pmf_sum_toReal)
noncomputable section
universe u v w
variable {ι : Type u} [Fintype ι] (p : PMF ι)
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def mean (value : ι → E) : E := ∑ i, ((p i).toReal : ℂ) • value i

def error (value : ι → E) (guess : E) : ℝ := ∑ i, (p i).toReal * ‖value i - guess‖ ^ 2

def variance (value : ι → E) : ℝ := error p value (mean p value)

theorem weights : (∑ i, ((p i).toReal : ℂ)) = 1 := by
  exact_mod_cast pmf_sum_toReal p

theorem centered_sum (value : ι → E) :
    (∑ i, ((p i).toReal : ℂ) • (value i - mean p value)) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, weights, one_smul]
  exact sub_self _

theorem centered_inner (value : ι → E) (test : E) :
    (∑ i, (p i).toReal * (inner ℂ (value i - mean p value) test).re) = 0 := by
  have paid := congrArg Complex.re (congrArg (fun x => inner ℂ x test) (centered_sum p value))
  simp only [sum_inner, inner_zero_left, Complex.re_sum] at paid
  calc
    _ = ∑ i, (inner ℂ (((p i).toReal : ℂ) • (value i - mean p value)) test).re := by
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_smul_left]
      simp
    _ = 0 := paid

theorem error_decomposition (value : ι → E) (guess : E) :
    error p value guess = variance p value + ‖mean p value - guess‖ ^ 2 := by
  have point (i : ι) :
      ‖value i - guess‖ ^ 2 = ‖value i - mean p value‖ ^ 2 +
        2 * (inner ℂ (value i - mean p value) (mean p value - guess)).re +
          ‖mean p value - guess‖ ^ 2 := by
    convert norm_add_sq (𝕜 := ℂ) (value i - mean p value) (mean p value - guess) using 2 <;> abel
  calc
    error p value guess =
        (∑ i, (p i).toReal * ‖value i - mean p value‖ ^ 2) +
        2 * (∑ i, (p i).toReal * (inner ℂ (value i - mean p value) (mean p value - guess)).re) +
        (∑ i, (p i).toReal) * ‖mean p value - guess‖ ^ 2 := by
      simp only [error, point, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = variance p value + ‖mean p value - guess‖ ^ 2 := by
      rw [centered_inner, pmf_sum_toReal]
      simp only [variance, error, mul_zero, add_zero, one_mul]

theorem optimal (value : ι → E) (guess : E) : variance p value ≤ error p value guess := by
  rw [error_decomposition]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem unique_optimal (value : ι → E) (guess : E) :
    error p value guess = variance p value ↔ guess = mean p value := by
  rw [error_decomposition, add_eq_left, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero, eq_comm]

theorem mean_map {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (map : E →ₗ[ℂ] F) (value : ι → E) : mean p (map ∘ value) = map (mean p value) := by
  simp only [mean, Function.comp_apply, map_sum, map_smul]

end
end SourceVectorMoment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
