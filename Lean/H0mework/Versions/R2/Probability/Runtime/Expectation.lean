import H0mework.Versions.R2.Probability.Runtime.Transition
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Actual finite-history sampling generates integrability, its scalar integral,
and the update of that integral when the original history grows. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedRuntimeHistoryProbability

open MeasureTheory

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}

variable (runtime : LivingRuntimeState process) (bound : Nat) (read : process.State → ℝ)

def observedPMF : PMF ℝ := (statePMF runtime bound).map read

theorem observedPMF_from_indices :
    observedPMF runtime bound read =
      (historyPMF bound).map (fun index => read (sample runtime bound index)) :=
  PMF.map_comp (sample runtime bound) (historyPMF bound) read

theorem observed_integrable :
    Integrable (fun value : ℝ => value) (observedPMF runtime bound read).toMeasure := by
  rw [observedPMF_from_indices, ← PMF.toMeasure_map _ _ (measurable_of_finite _)]
  exact (integrable_map_measure aestronglyMeasurable_id
    (measurable_of_finite _).aemeasurable).mpr Integrable.of_finite

def mean : ℝ := ∫ value, value ∂(observedPMF runtime bound read).toMeasure

theorem mean_eq_source_sum :
    mean runtime bound read = ((bound + 1 : Nat) : ℝ)⁻¹ *
      ∑ index : Fin (bound + 1), read (sample runtime bound index) := by
  unfold mean
  rw [observedPMF_from_indices, ← PMF.toMeasure_map _ _ (measurable_of_finite _)]
  have transported := integral_map (μ := (historyPMF bound).toMeasure)
    (φ := fun index => read (sample runtime bound index)) (f := fun value : ℝ => value)
    (measurable_of_finite _).aemeasurable aestronglyMeasurable_id
  rw [transported, PMF.integral_eq_sum]
  simp only [historyPMF, PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  exact (Finset.mul_sum _ _ _).symm

theorem count_mul_mean :
    ((bound + 1 : Nat) : ℝ) * mean runtime bound read =
      ∑ index : Fin (bound + 1), read (sample runtime bound index) := by
  rw [mean_eq_source_sum, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

theorem mean_extension :
    ((bound + 2 : Nat) : ℝ) * mean runtime (bound + 1) read =
      ((bound + 1 : Nat) : ℝ) * mean runtime bound read +
        read (history runtime bound).target.state := by
  rw [count_mul_mean, count_mul_mean, Fin.sum_univ_castSucc]
  rfl

theorem mean_successor :
    mean runtime.tick.next bound read =
      mean runtime bound (fun state => read (process.successor state)) := by
  unfold mean observedPMF
  rw [← statePMF_successor, PMF.map_comp]
  rfl

end
end SourceGeneratedRuntimeHistoryProbability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
