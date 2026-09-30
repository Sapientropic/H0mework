import H0mework.Fock.HistoryCopy.ObservationEffect
import H0mework.Fock.HistoryCopy.ObservationField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyObservation

open SourceWeightedRecovery SourceConditionalInventory SourceUniformFibreVariance
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionMeasure
open SourceGeneratedActionWords.Fock.OriginalHilbert
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open MeasureTheory
open scoped Classical
noncomputable section

local instance recoveryParentMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem after_posterior (actor : Fin 4) :
    SourceConditionalHistory.conditional (historyPMF 3) (after 3 3 twoMaterial)
        (after 3 3 twoMaterial actor)
        (observed_supported (historyPMF 3) (after 3 3 twoMaterial) actor (source_positive 3 actor)) = PMF.pure actor :=
  ObservationRefinement.conditional_injective (historyPMF 3) (after 3 3 twoMaterial)
    copy_snapshot_injective actor (source_positive 3 actor)

theorem after_recovery (task : Fin 4 → ℂ) (actor : Fin 4) :
    SourceWeightedRecovery.transfer (historyPMF 3) (after 3 3 twoMaterial)
      (taskValue (historyPMF 3) task) (after 3 3 twoMaterial actor) = task actor :=
  ObservationRefinement.optimum_injective (historyPMF 3) (after 3 3 twoMaterial)
    copy_snapshot_injective task actor (source_positive 3 actor)

theorem after_residual_zero (value : SourceWeightedRecovery.Space (historyPMF 3)) :
    SourceWeightedRecovery.residual (historyPMF 3) (after 3 3 twoMaterial) value = 0 := by
  have original : taskValue (historyPMF 3) (fun actor => value actor) = value :=
    Lp.toLp_coeFn value (task_memLp (historyPMF 3) (fun actor => value actor))
  have attained := (optimal_attains (historyPMF 3) (after 3 3 twoMaterial) (fun actor => value actor)).symm
  have exactRead (actor : Fin 4) :
      optimalDecoder (historyPMF 3) (after 3 3 twoMaterial) (fun point => value point)
        (after 3 3 twoMaterial actor) = value actor := after_recovery (fun point => value point) actor
  simp only [original, error, exactRead, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero] at attained
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (SourceWeightedRecovery.residual (historyPMF 3) (after 3 3 twoMaterial) value)]

theorem actual_original_recovery (value : FieldSpace 3 3) :
    Actor.currentTransfer 3 3
      (SourceWeightedRecovery.pullback (historyPMF 3) (after 3 3 twoMaterial)
        (SourceWeightedRecovery.transfer (historyPMF 3) (after 3 3 twoMaterial)
          (Actor.currentPullback 3 3 value))) = value := by
  have recovered := IsometricRetainedTransfer.pullback_transfer_add_residual
    (SourceWeightedRecovery.pullback (historyPMF 3) (after 3 3 twoMaterial)) (Actor.currentPullback 3 3 value)
  rw [after_residual_zero, add_zero] at recovered
  exact (congrArg (Actor.currentTransfer 3 3) recovered).trans
    (IsometricRetainedTransfer.transfer_pullback (Actor.currentPullback 3 3) value)

theorem actual_original_decoder_lower (decoder : Fin 4 → ParentCarrier → ℂ) :
    1 ≤ ∑ actor : Fin 4,
      error (historyPMF 3) (Actor.originalRead 3 3)
        (fun point => (unitTask 3 actor point : ℂ)) (decoder actor ∘ inputSnapshot 3) := by
  have generated := original_decoder_lower 3 3 decoder
  rw [before_cost_three] at generated
  exact generated

theorem after_information_zero :
    SourceUniformFibreInformation.conditionalEntropy 3 (after 3 3 twoMaterial) = 0 :=
  SourceUniformFibreInformation.conditional_entropy_zero_of_injective 3 _ copy_snapshot_injective

theorem actual_conditional_information_gain :
    (1 / 4 : ℝ) ≤ SourceUniformFibreInformation.conditionalEntropy 3 (before 3 3) -
      SourceUniformFibreInformation.conditionalEntropy 3 (joint 3 3 twoMaterial) := by
  have lower := information_cost 3 (before 3 3)
  rw [before_cost_three] at lower
  have exactInfo := SourceUniformFibreInformation.conditional_entropy_zero_of_injective 3 _ joint_snapshot_injective
  rw [exactInfo, sub_zero]
  norm_num at lower ⊢
  exact lower

end
end SourceCopyObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
