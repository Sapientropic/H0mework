import H0mework.Versions.X.Fock.CopyGraph.CorrectionUpdate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCorrection

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

theorem direction_mean (bound : Nat) (query : Fin (bound + 1) → Observed) :
    inner ℂ (one bound query) (direction bound query) =
      inner ℂ (one bound query) (clockMean bound query) / (bound + 2 : ℂ) := by
  have unit : inner ℂ (one bound query) (one bound query) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, one_norm]
    norm_num
  unfold direction
  rw [inner_sub_right, inner_smul_right, unit, mul_one]
  unfold ratio
  push_cast
  have denominator : (bound + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : bound + 2 ≠ 0)
  field_simp
  ring

theorem update_mean (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    inner ℂ (one bound query) (update depth bound index query value) =
      coefficient depth bound index query value * inner ℂ (one bound query) (clockMean bound query) / (bound + 2 : ℂ) := by
  unfold update
  rw [inner_smul_right, direction_mean]
  ring

variable [MeasurableSingletonClass Observed]

theorem decoded_residual_mass (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound
      (value - pullback (historyPMF bound) query
        (SourceConditionalGraphDecoder.decode depth bound index query (SourceConditionalGraph.copyRead depth bound index value)))) =
      -(Real.sqrt (bound + 1 : ℝ) : ℂ) *
        (coefficient depth bound index query value * inner ℂ (one bound query) (clockMean bound query) / (bound + 2 : ℂ)) := by
  rw [decoder_formula, map_add]
  have source : value - (pullback (historyPMF bound) query (transfer (historyPMF bound) query value) +
      pullback (historyPMF bound) query (update depth bound index query value)) =
        residual (historyPMF bound) query value - pullback (historyPMF bound) query (update depth bound index query value) := by
    change _ = (value - pullback (historyPMF bound) query (transfer (historyPMF bound) query value)) - _
    abel
  rw [source, map_sub, map_sub, SourceConditionalGraph.residual_mass, zero_sub, mass_pullback, update_mean]
  simp only [Complex.real_smul]
  ring

theorem clock_average (bound : Nat) (query : Fin (bound + 1) → Observed) :
    inner ℂ (one bound query) (clockMean bound query) =
      ∑ actor : Fin (bound + 1), (historyPMF bound actor).toReal • SourceGeneratedJointClock.signal bound actor := by
  change inner ℂ (one bound query) ((pullback (historyPMF bound) query).toContinuousLinearMap.adjoint
    (taskValue (historyPMF bound) (SourceGeneratedJointClock.signal bound))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (pullback (historyPMF bound) query (one bound query))
    (taskValue (historyPMF bound) (SourceGeneratedJointClock.signal bound)) = _
  rw [inner_source_sum]
  simp only [one_at, taskValue_at _ _ _ (SourceUniformFibreVariance.source_positive _ _),
    RCLike.inner_apply, map_one, mul_one]

end
end SourceConditionalCorrection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
