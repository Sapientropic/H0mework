import H0mework.Probability.HistoryWord.Coherence
import H0mework.Probability.SourceShift.Mean

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryWord

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance SourceSuccessorBoundary
open MeasureTheory
open scoped Classical
noncomputable section

def density (bound : Nat) : Space (historyPMF bound) :=
  taskValue (historyPMF bound) (fun index => (Real.sqrt (historyPMF bound index).toReal : ℂ))

theorem density_at (bound : Nat) (index : Fin (bound + 1)) :
    density bound index = (Real.sqrt (historyPMF bound index).toReal : ℂ) :=
  taskValue_at (historyPMF bound) _ index (source_positive bound index)

theorem density_coefficient (bound : Nat) (index : Fin (bound + 1)) :
    coefficient bound index (density bound) = ((historyPMF bound index).toReal : ℂ) := by
  rw [coefficient_value, density_at, ← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt ENNReal.toReal_nonneg]

theorem density_word (bound : Nat) : word bound (density bound) = meanWord bound := by
  rw [word_sum]
  calc
    _ = ∑ index : Fin (bound + 1), ((bound + 1 : Nat) : ℂ)⁻¹ • Finsupp.single index.val (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [density_coefficient, source_weight, Finsupp.smul_single, smul_eq_mul, mul_one]
      congr 1
      simp [one_div]
    _ = _ := by
      rw [← Finset.smul_sum]
      exact congrArg (fun sourceWord : Nat →₀ ℂ => ((bound + 1 : Nat) : ℂ)⁻¹ • sourceWord)
        (Fin.sum_univ_eq_sum_range (fun index : Nat => Finsupp.single index (1 : ℂ)) (bound + 1))

theorem density_norm_sq (bound : Nat) : ‖density bound‖ ^ 2 = 1 / (bound + 1 : ℝ) := by
  rw [← hilbert_norm_sq, density_word]
  exact mean_norm_sq bound

theorem density_mass (bound : Nat) : SourceMassCompletion.massRead (joint bound (density bound)) = 1 := by
  change SourceMassCompletion.massRead (SourceMassCompletion.jointRead (word bound (density bound))) = 1
  rw [density_word, SourceMassCompletion.massRead_source, mass_meanWord]

variable {old fresh : Nat} (retained : old ≤ fresh)

theorem restrict_density :
    SourceHistoryGrowth.restrict retained (density fresh) =
      Real.sqrt (SourceHistoryGrowth.fraction old fresh) • density old := by
  apply Lp.ext
  apply Filter.Eventually.of_forall
  intro index
  rw [SourceHistoryGrowth.restrict_at, density_at]
  change (Real.sqrt (historyPMF fresh (SourceHistoryGrowth.includeActor retained index)).toReal : ℂ) =
    evalAt (historyPMF old) index (source_positive old index)
      (Real.sqrt (SourceHistoryGrowth.fraction old fresh) • density old)
  rw [LinearMap.map_smul_of_tower]
  change (Real.sqrt (historyPMF fresh (SourceHistoryGrowth.includeActor retained index)).toReal : ℂ) =
    Real.sqrt (SourceHistoryGrowth.fraction old fresh) • density old index
  rw [density_at, SourceHistoryGrowth.mass_relation,
    Real.sqrt_mul (SourceHistoryGrowth.fraction_pos old fresh).le, Complex.ofReal_mul]
  rfl

theorem density_update :
    word fresh (density fresh) = SourceHistoryGrowth.fraction old fresh • word old (density old) +
      word fresh (SourceHistoryGrowth.remainder retained (density fresh)) := by
  rw [word_reconstruction retained, restrict_density, LinearMap.map_smul_of_tower, smul_smul]
  have square := Real.mul_self_sqrt (SourceHistoryGrowth.fraction_pos old fresh).le
  rw [square]

theorem new_density_at (index : Fin (fresh + 1)) (new : old + 1 ≤ index.val) :
    word fresh (SourceHistoryGrowth.remainder retained (density fresh)) index.val =
      ((historyPMF fresh index).toReal : ℂ) := by
  rw [word_at, coefficient_value, SourceHistoryGrowth.remainder_at_new retained _ index new]
  exact density_coefficient fresh index

end
end SourceHistoryWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
