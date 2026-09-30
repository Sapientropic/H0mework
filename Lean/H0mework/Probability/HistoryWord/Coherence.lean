import H0mework.Probability.HistoryWord.Hilbert
import H0mework.Probability.HistoryGrowth.Retention

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryWord

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceSuccessorBoundary
open scoped Classical
noncomputable section

variable {old fresh : Nat} (retained : old ≤ fresh)

theorem coefficient_preserve (value : Space (historyPMF old)) (index : Fin (old + 1)) :
    coefficient fresh (SourceHistoryGrowth.includeActor retained index) (SourceHistoryGrowth.extend retained value) =
      Real.sqrt (SourceHistoryGrowth.fraction old fresh) • coefficient old index value := by
  rw [coefficient_value, SourceHistoryGrowth.extend_at, SourceHistoryGrowth.mass_relation,
    Real.sqrt_mul (SourceHistoryGrowth.fraction_pos old fresh).le, Complex.ofReal_mul, coefficient_value]
  simp only [Complex.real_smul]
  ring

theorem word_preserve (value : Space (historyPMF old)) :
    word fresh (SourceHistoryGrowth.extend retained value) =
      Real.sqrt (SourceHistoryGrowth.fraction old fresh) • word old value := by
  apply Finsupp.ext
  intro index
  rw [Finsupp.smul_apply]
  by_cases prior : index < old + 1
  · let before : Fin (old + 1) := ⟨index, prior⟩
    change word fresh (SourceHistoryGrowth.extend retained value)
      (SourceHistoryGrowth.includeActor retained before).val =
        Real.sqrt (SourceHistoryGrowth.fraction old fresh) • word old value before.val
    rw [word_at, word_at, coefficient_preserve]
  · rw [word_outside old value index (Nat.le_of_not_gt prior), smul_zero]
    by_cases now : index < fresh + 1
    · let current : Fin (fresh + 1) := ⟨index, now⟩
      change word fresh (SourceHistoryGrowth.extend retained value) current.val = 0
      rw [word_at, coefficient_value, SourceHistoryGrowth.extend_at_new retained value current
        (Nat.le_of_not_gt prior), mul_zero]
    · exact word_outside fresh (SourceHistoryGrowth.extend retained value) index (Nat.le_of_not_gt now)

theorem normalized_word (value : Space (historyPMF old)) :
    word fresh (SourceHistoryGrowth.normalizedInclusion retained value) = word old value := by
  change word fresh ((Real.sqrt (SourceHistoryGrowth.fraction old fresh))⁻¹ •
    SourceHistoryGrowth.extend retained value) = _
  rw [LinearMap.map_smul_of_tower, word_preserve, smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (SourceHistoryGrowth.fraction_pos old fresh)).ne', one_smul]

theorem word_reconstruction (value : Space (historyPMF fresh)) :
    word fresh value =
      Real.sqrt (SourceHistoryGrowth.fraction old fresh) • word old (SourceHistoryGrowth.restrict retained value) +
        word fresh (SourceHistoryGrowth.remainder retained value) := by
  have original : SourceHistoryGrowth.extend retained (SourceHistoryGrowth.restrict retained value) +
      SourceHistoryGrowth.remainder retained value = value := by
    rw [SourceHistoryGrowth.remainder_eq]
    exact add_sub_cancel _ _
  calc
    _ = word fresh (SourceHistoryGrowth.extend retained (SourceHistoryGrowth.restrict retained value) +
        SourceHistoryGrowth.remainder retained value) := congrArg (word fresh) original.symm
    _ = _ := by rw [map_add, word_preserve]

theorem normalized_joint (value : Space (historyPMF old)) :
    joint fresh (SourceHistoryGrowth.normalizedInclusion retained value) = joint old value :=
  congrArg SourceMassCompletion.jointRead (normalized_word retained value)

theorem joint_reconstruction (value : Space (historyPMF fresh)) :
    joint fresh value =
      Real.sqrt (SourceHistoryGrowth.fraction old fresh) • joint old (SourceHistoryGrowth.restrict retained value) +
        joint fresh (SourceHistoryGrowth.remainder retained value) := by
  have generated := congrArg SourceMassCompletion.jointRead (word_reconstruction retained value)
  simpa only [map_add, LinearMap.map_smul_of_tower, joint, LinearMap.comp_apply] using generated

end
end SourceHistoryWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
