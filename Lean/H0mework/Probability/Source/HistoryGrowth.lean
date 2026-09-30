import H0mework.Probability.Recovery.AtomicReader
import H0mework.Probability.Information.Conditional

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryGrowth

open SourceWeightedRecovery SourceGeneratedAtomicObservation SourceGeneratedRuntimeHistoryProbability
open SourceUniformFibreVariance MeasureTheory
open scoped InnerProductSpace Classical
noncomputable section

variable {old fresh : Nat} (retained : old ≤ fresh)

def includeActor : Fin (old + 1) ↪ Fin (fresh + 1) :=
  ⟨Fin.castLE (Nat.succ_le_succ retained), fun _ _ same => Fin.ext (congrArg (fun index : Fin (fresh + 1) => index.val) same)⟩

def fraction (old fresh : Nat) : ℝ := (old + 1 : ℝ) / (fresh + 1 : ℝ)

theorem fraction_pos (old fresh : Nat) : 0 < fraction old fresh := by
  unfold fraction
  positivity

theorem mass_relation (index : Fin (old + 1)) :
    (historyPMF fresh (includeActor retained index)).toReal =
      fraction old fresh * (historyPMF old index).toReal := by
  rw [source_weight, source_weight, fraction]
  field_simp

theorem cotest_value (bound : Nat) (point seen : Fin (bound + 1)) :
    cotest (historyPMF bound) point seen = if seen = point then 1 else 0 := by
  have actual := ae_at_support (historyPMF bound) seen (source_positive bound seen)
    (@indicatorConstLp_coeFn (Fin (bound + 1)) _ _ 2 (historyPMF bound).toMeasure _ {point}
      (measurableSet_singleton point) (measure_ne_top _ _) (1 : ℂ))
  simpa only [cotest, Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply] using actual

def extend : Space (historyPMF old) →L[ℂ] Space (historyPMF fresh) :=
  ∑ index : Fin (old + 1),
    (evalAtContinuous (historyPMF old) index (source_positive old index)).smulRight
      (cotest (historyPMF fresh) (includeActor retained index))

def restrict : Space (historyPMF fresh) →L[ℂ] Space (historyPMF old) :=
  ∑ index : Fin (old + 1),
    (evalAtContinuous (historyPMF fresh) (includeActor retained index)
      (source_positive fresh (includeActor retained index))).smulRight
        (cotest (historyPMF old) index)

theorem restrict_at (value : Space (historyPMF fresh)) (index : Fin (old + 1)) :
    restrict retained value index = value (includeActor retained index) := by
  change evalAt (historyPMF old) index (source_positive old index) (restrict retained value) = _
  simp only [restrict, sum_apply, ContinuousLinearMap.smulRight_apply, map_sum, map_smul]
  change (∑ other : Fin (old + 1), value (includeActor retained other) •
    cotest (historyPMF old) other index) = value (includeActor retained index)
  simp [cotest_value]

theorem extend_at (value : Space (historyPMF old)) (index : Fin (old + 1)) :
    extend retained value (includeActor retained index) = value index := by
  change evalAt (historyPMF fresh) (includeActor retained index)
    (source_positive fresh (includeActor retained index)) (extend retained value) = _
  simp only [extend, sum_apply, ContinuousLinearMap.smulRight_apply, map_sum, map_smul]
  change (∑ other : Fin (old + 1), value other •
    cotest (historyPMF fresh) (includeActor retained other) (includeActor retained index)) = value index
  simp [cotest_value, (includeActor retained).injective.eq_iff]

theorem restrict_extend (value : Space (historyPMF old)) :
    restrict retained (extend retained value) = value := by
  apply Lp.ext
  exact Filter.Eventually.of_forall fun index =>
    (restrict_at retained (extend retained value) index).trans (extend_at retained value index)

theorem inner_extend (left : Space (historyPMF old)) (right : Space (historyPMF fresh)) :
    ⟪extend retained left, right⟫_ℂ = fraction old fresh • ⟪left, restrict retained right⟫_ℂ := by
  rw [extend, sum_apply, sum_inner, inner_source_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [ContinuousLinearMap.smulRight_apply, inner_smul_left, cotest_pairing, mass_relation, restrict_at]
  change star (left index) * ((fraction old fresh * (historyPMF old index).toReal) •
      right (includeActor retained index)) = _
  simp only [RCLike.inner_apply, Complex.real_smul]
  push_cast
  change star (left index) * (↑(fraction old fresh) * ↑(historyPMF old index).toReal * right (includeActor retained index)) =
    ↑(fraction old fresh) * (↑(historyPMF old index).toReal * (right (includeActor retained index) * star (left index)))
  ring

theorem extend_norm_sq (value : Space (historyPMF old)) :
    ‖extend retained value‖ ^ 2 = fraction old fresh * ‖value‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_extend, restrict_extend]
  change (fraction old fresh • ⟪value, value⟫_ℂ).re = _
  rw [Complex.smul_re]
  exact congrArg (fraction old fresh * ·) (norm_sq_eq_re_inner (𝕜 := ℂ) value).symm

end
end SourceHistoryGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
