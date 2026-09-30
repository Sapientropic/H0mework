import H0mework.Probability.Source.MomentMoment

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceVectorMoment

open scoped Classical
noncomputable section
universe u v w
variable {ι : Type u} [Fintype ι] {Observed : Type v}

theorem filtered_mean {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (p : PMF ι) (read : ι → Observed) (value : ι → E) (output : Observed)
    (supported : output ∈ (p.map read).support) :
    ((p.map read output).toReal : ℂ) • mean (SourceConditionalHistory.conditional p read output supported) value =
      mean p (fun i => if read i = output then value i else 0) := by
  classical
  rw [mean, Finset.smul_sum, mean]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, ← Complex.ofReal_mul, ← ENNReal.toReal_mul,
    SourceConditionalHistory.weighted_conditional]
  by_cases same : read i = output <;> simp only [same, if_true, if_false, ENNReal.toReal_zero, Complex.ofReal_zero, zero_smul, smul_zero]

theorem filtered_error {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (p : PMF ι) (read : ι → Observed) (value : ι → E) (output : Observed)
    (supported : output ∈ (p.map read).support) (guess : E) :
    (p.map read output).toReal * error (SourceConditionalHistory.conditional p read output supported) value guess =
      ∑ i, (p i).toReal * (if read i = output then ‖value i - guess‖ ^ 2 else 0) := by
  classical
  rw [error, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, ← ENNReal.toReal_mul, SourceConditionalHistory.weighted_conditional]
  by_cases same : read i = output <;> simp only [same, if_true, if_false, ENNReal.toReal_zero, zero_mul, mul_zero]

end
end SourceVectorMoment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
