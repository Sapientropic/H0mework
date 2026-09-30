import H0mework.Probability.Source.MomentMoment

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceVectorMoment

open SourceWeightedRecovery (observed_supported)
open SourceConditionalHistory (conditional)
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population (pmf_sum_toReal)
noncomputable section
universe u v
variable {ι : Type u} [Fintype ι] {Observed : Type v}

theorem conditional_average (p : PMF ι) (read : ι → Observed) (positive : ∀ i, i ∈ p.support)
    (cost : ι → Observed → ℝ) :
    (∑ left, (p left).toReal * ∑ right,
      (conditional p read (read left) (observed_supported p read left (positive left)) right).toReal * cost right (read left)) =
        ∑ right, (p right).toReal * cost right (read right) := by
  have swap (left right : ι) :
      (p left).toReal * (conditional p read (read left) (observed_supported p read left (positive left)) right).toReal *
          cost right (read left) =
        (p right).toReal * (conditional p read (read right) (observed_supported p read right (positive right)) left).toReal *
          cost right (read right) := by
    simp only [SourceConditionalHistory.conditional_apply]
    by_cases same : read right = read left
    · simp only [same, if_true, ENNReal.toReal_mul]
      ring
    · simp only [same, Ne.symm same, if_false, ENNReal.toReal_zero, mul_zero, zero_mul]
  calc
    _ = ∑ left, ∑ right, (p right).toReal *
        (conditional p read (read right) (observed_supported p read right (positive right)) left).toReal * cost right (read right) := by
      apply Finset.sum_congr rfl
      intro left _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro right _
      exact (mul_assoc _ _ _).symm.trans (swap left right)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← Finset.mul_sum, pmf_sum_toReal, mul_one]

theorem conditional_error {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (p : PMF ι) (read : ι → Observed) (positive : ∀ i, i ∈ p.support)
    (value : ι → E) (decoder : Observed → E) :
    (∑ i, (p i).toReal * ‖value i - decoder (read i)‖ ^ 2) =
      (∑ i, (p i).toReal * variance (conditional p read (read i) (observed_supported p read i (positive i))) value) +
      (∑ i, (p i).toReal * ‖mean (conditional p read (read i) (observed_supported p read i (positive i))) value - decoder (read i)‖ ^ 2) := by
  rw [← conditional_average p read positive (fun i y => ‖value i - decoder y‖ ^ 2)]
  calc
    _ = ∑ i, (p i).toReal *
        (variance (conditional p read (read i) (observed_supported p read i (positive i))) value +
          ‖mean (conditional p read (read i) (observed_supported p read i (positive i))) value - decoder (read i)‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg ((p i).toReal * ·) (error_decomposition _ value (decoder (read i)))
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib]

end
end SourceVectorMoment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
