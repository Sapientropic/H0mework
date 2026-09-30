import H0mework.Probability.Source.HistoryGrowth
import H0mework.Probability.SourceShift.Word
import H0mework.Probability.MassCompletion.Carrier

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryWord

open SourceWeightedRecovery SourceGeneratedAtomicObservation SourceGeneratedRuntimeHistoryProbability
open SourceUniformFibreVariance SourceSuccessorBoundary
open scoped Classical
noncomputable section

def coefficient (bound : Nat) (index : Fin (bound + 1)) : Space (historyPMF bound) →ₗ[ℂ] ℂ :=
  ((Real.sqrt (historyPMF bound index).toReal : ℝ) : ℂ) •
    evalAt (historyPMF bound) index (source_positive bound index)

theorem coefficient_value (bound : Nat) (index : Fin (bound + 1)) (value : Space (historyPMF bound)) :
    coefficient bound index value = (Real.sqrt (historyPMF bound index).toReal : ℂ) * value index := rfl

theorem coefficient_scale (bound : Nat) (index : Fin (bound + 1)) :
    Real.sqrt (historyPMF bound index).toReal = 1 / Real.sqrt (bound + 1 : ℝ) := by
  rw [source_weight, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]

def word (bound : Nat) : Space (historyPMF bound) →ₗ[ℂ] Nat →₀ ℂ :=
  ∑ index : Fin (bound + 1), (Finsupp.lsingle index.val).comp (coefficient bound index)

theorem word_sum (bound : Nat) (value : Space (historyPMF bound)) :
    word bound value = ∑ index : Fin (bound + 1), Finsupp.single index.val (coefficient bound index value) := by
  simp only [word, LinearMap.sum_apply, LinearMap.comp_apply, Finsupp.lsingle_apply]

theorem word_at (bound : Nat) (value : Space (historyPMF bound)) (index : Fin (bound + 1)) :
    word bound value index.val = coefficient bound index value := by
  rw [word_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single index]
  · exact Finsupp.single_eq_same
  · intro other _ different
    exact Finsupp.single_eq_of_ne (fun equal => different (Fin.ext equal.symm))
  · simp

theorem word_outside (bound : Nat) (value : Space (historyPMF bound)) (index : Nat)
    (outside : bound + 1 ≤ index) : word bound value index = 0 := by
  rw [word_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro before _
  apply Finsupp.single_eq_of_ne
  have inside := before.isLt
  omega

theorem mass_word (bound : Nat) (value : Space (historyPMF bound)) :
    mass ℂ (word bound value) = ∑ index : Fin (bound + 1),
      (Real.sqrt (historyPMF bound index).toReal : ℂ) * value index := by
  rw [word_sum, map_sum]
  simp only [mass_single, coefficient_value]

end
end SourceHistoryWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
