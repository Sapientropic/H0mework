import H0mework.Versions.R2.Probability.EmpiricalRecovery.ActorCore

/-! Arbitrary actor tasks expose the loss before the old field transfer, while retaining that transfer unchanged. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer MeasureTheory
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

local instance : MeasurableSpace (Field read) := fieldBorel read

def rawError (task : Fin (bound + 1) → ℂ) (decoder : Field read → ℂ) : ℝ :=
  error (historyPMF bound) (nextAtom read runtime bound) task decoder

theorem rawError_eq_norm (task : Fin (bound + 1) → ℂ) (decoder : Field read → ℂ) :
    rawError read runtime bound task decoder =
      ‖taskValue (historyPMF bound) task - nextPullback read runtime bound
        (SourceConditionalRecovery.decoderValue read runtime bound decoder)‖ ^ 2 := by
  rw [rawError, error, norm_source_sq]
  apply Finset.sum_congr rfl
  intro index _
  have supported : index ∈ (historyPMF bound).support := by simp [historyPMF]
  have evaluated := (evalAt (historyPMF bound) index supported).map_sub
    (taskValue (historyPMF bound) task)
    (nextPullback read runtime bound (SourceConditionalRecovery.decoderValue read runtime bound decoder))
  change (taskValue (historyPMF bound) task - nextPullback read runtime bound
      (SourceConditionalRecovery.decoderValue read runtime bound decoder)) index =
    taskValue (historyPMF bound) task index - nextPullback read runtime bound
      (SourceConditionalRecovery.decoderValue read runtime bound decoder) index at evaluated
  rw [evaluated, taskValue_at _ _ _ supported, nextPullback_at, SourceConditionalRecovery.decoderValue_at_next]

theorem actor_error_decomposition (task : Fin (bound + 1) → ℂ) (decoder : Field read → ℂ) :
    let value := taskValue (historyPMF bound) task
    rawError read runtime bound task decoder =
      ‖actorResidual read runtime bound value‖ ^ 2 +
        ‖SourceGeneratedEmpiricalHilbert.residual read runtime bound (actorTransfer read runtime bound value)‖ ^ 2 +
          SourceConditionalRecovery.decoderError read runtime bound
            (SourceGeneratedEmpiricalHilbert.transfer read runtime bound (actorTransfer read runtime bound value)) decoder := by
  dsimp only
  have first := IsometricRetainedTransfer.decoder_error_decomposition (actorPullback read runtime bound)
    (taskValue (historyPMF bound) task)
    (SourceGeneratedEmpiricalHilbert.pullback read runtime bound (SourceConditionalRecovery.decoderValue read runtime bound decoder))
  have second := IsometricRetainedTransfer.decoder_error_decomposition
    (SourceGeneratedEmpiricalHilbert.pullback read runtime bound)
    (actorTransfer read runtime bound (taskValue (historyPMF bound) task))
    (SourceConditionalRecovery.decoderValue read runtime bound decoder)
  exact (rawError_eq_norm read runtime bound task decoder).trans (first.trans
    ((congrArg (‖actorResidual read runtime bound (taskValue (historyPMF bound) task)‖ ^ 2 + ·)
      (second.trans (congrArg (‖SourceGeneratedEmpiricalHilbert.residual read runtime bound
        (actorTransfer read runtime bound (taskValue (historyPMF bound) task))‖ ^ 2 + ·)
        (SourceConditionalRecovery.decoderError_eq_norm read runtime bound _ decoder).symm))).trans
          (add_assoc _ _ _).symm))

theorem rawError_before_field (task : Fin (bound + 1) → ℂ) (decoder : Field read → ℂ) :
    let value := taskValue (historyPMF bound) task
    rawError read runtime bound task decoder = ‖actorResidual read runtime bound value‖ ^ 2 +
      SourceConditionalRecovery.sourceError read runtime bound (actorTransfer read runtime bound value) decoder :=
  (actor_error_decomposition read runtime bound task decoder).trans
    ((add_assoc _ _ _).trans (congrArg (‖actorResidual read runtime bound (taskValue (historyPMF bound) task)‖ ^ 2 + ·)
      (SourceConditionalRecovery.error_decomposition read runtime bound
        (actorTransfer read runtime bound (taskValue (historyPMF bound) task)) decoder).symm))

theorem original_field_task (value : SourceGeneratedEmpiricalHilbert.Space read runtime bound) :
    taskValue (historyPMF bound) (sourceTask read runtime bound value) = actorPullback read runtime bound value := by
  apply Lp.ext
  exact Filter.Eventually.of_forall fun index =>
    (taskValue_at (historyPMF bound) (sourceTask read runtime bound value) index (by simp [historyPMF])).trans
      (actorPullback_at read runtime bound value index).symm

theorem original_field_task_no_actor_residual (value : SourceGeneratedEmpiricalHilbert.Space read runtime bound) :
    actorResidual read runtime bound (taskValue (historyPMF bound) (sourceTask read runtime bound value)) = 0 := by
  rw [original_field_task]
  exact (IsometricRetainedTransfer.residual_zero_iff (actorPullback read runtime bound) _).mpr ⟨value, rfl⟩

theorem rawError_lower_bound (task : Fin (bound + 1) → ℂ) (decoder : Field read → ℂ) :
    let value := taskValue (historyPMF bound) task
    ‖actorResidual read runtime bound value‖ ^ 2 +
        ‖SourceGeneratedEmpiricalHilbert.residual read runtime bound (actorTransfer read runtime bound value)‖ ^ 2 ≤
      rawError read runtime bound task decoder := by
  rw [actor_error_decomposition]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun index _ =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))

theorem rawError_attains (task : Fin (bound + 1) → ℂ) :
    let value := taskValue (historyPMF bound) task
    rawError read runtime bound task (fun atom => SourceGeneratedEmpiricalHilbert.transfer read runtime bound
        (actorTransfer read runtime bound value) atom) =
      ‖actorResidual read runtime bound value‖ ^ 2 +
        ‖SourceGeneratedEmpiricalHilbert.residual read runtime bound (actorTransfer read runtime bound value)‖ ^ 2 := by
  dsimp only
  rw [actor_error_decomposition]
  simp [SourceConditionalRecovery.decoderError]

theorem reconstruct_actor (value : ActorSpace bound) :
    nextPullback read runtime bound (SourceGeneratedEmpiricalHilbert.transfer read runtime bound
        (actorTransfer read runtime bound value)) +
      actorPullback read runtime bound (SourceGeneratedEmpiricalHilbert.residual read runtime bound
        (actorTransfer read runtime bound value)) + actorResidual read runtime bound value = value := by
  have field := SourceGeneratedEmpiricalHilbert.pullback_transfer_add_residual read runtime bound
    (actorTransfer read runtime bound value)
  have whole := congrArg (fun current => actorPullback read runtime bound current + actorResidual read runtime bound value) field
  simp only [map_add] at whole
  exact whole.trans
    (IsometricRetainedTransfer.pullback_transfer_add_residual (actorPullback read runtime bound) value)

end
end SourceWeightedRecovery.Runtime.Actor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
