import H0mework.Probability.HistoryWord.Core

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryWord

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
noncomputable section

def lift (bound : Nat) (sourceWord : Nat →₀ ℂ) : Space (historyPMF bound) :=
  taskValue (historyPMF bound) (fun index => (Real.sqrt (bound + 1 : ℝ) : ℂ) * sourceWord index.val)

theorem lift_coefficient (bound : Nat) (sourceWord : Nat →₀ ℂ) (index : Fin (bound + 1)) :
    coefficient bound index (lift bound sourceWord) = sourceWord index.val := by
  rw [coefficient_value, lift, taskValue_at _ _ index (source_positive bound index), coefficient_scale]
  have positive : (Real.sqrt (bound + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < bound + 1)).ne'
  push_cast
  field_simp

theorem word_lift (bound : Nat) (sourceWord : Nat →₀ ℂ)
    (supported : ∀ index ∈ sourceWord.support, index < bound + 1) :
    word bound (lift bound sourceWord) = sourceWord := by
  apply Finsupp.ext
  intro index
  by_cases inside : index < bound + 1
  · exact (word_at bound (lift bound sourceWord) ⟨index, inside⟩).trans (lift_coefficient bound sourceWord ⟨index, inside⟩)
  · rw [word_outside bound _ index (Nat.le_of_not_gt inside)]
    exact (Finsupp.notMem_support_iff.mp (fun present => inside (supported index present))).symm

end
end SourceHistoryWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
