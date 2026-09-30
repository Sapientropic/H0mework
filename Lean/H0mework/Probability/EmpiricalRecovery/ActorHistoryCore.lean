import H0mework.Probability.EmpiricalRecovery.ActorError
import H0mework.Probability.EmpiricalRecovery.HistoryError

/-! Complete actor tasks enter the already generated retained-history recovery calculation. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.History

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer MeasureTheory
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

local instance : MeasurableSpace (Field read) := fieldBorel read

def rawTerminalError (depth : Nat) (task : Fin (bound + 1) → ℂ) (decoder : Field read → ℂ) : ℝ :=
  error (historyPMF bound) (fieldSample read (runtime.advance (depth + 1)) bound) task decoder

theorem rawTerminalError_eq_norm (depth : Nat) (task : Fin (bound + 1) → ℂ) (decoder : Field read → ℂ) :
    rawTerminalError read runtime bound depth task decoder =
      ‖taskValue (historyPMF bound) task - actorPullback read runtime bound
        (SourceConditionalRecovery.History.liftEstimator read runtime bound (depth + 1)
          (SourceConditionalRecovery.decoderValue read (runtime.advance depth) bound decoder))‖ ^ 2 := by
  rw [rawTerminalError, error, norm_source_sq]
  apply Finset.sum_congr rfl
  intro index _
  have supported : index ∈ (historyPMF bound).support := by simp [historyPMF]
  let estimate := SourceConditionalRecovery.History.liftEstimator read runtime bound (depth + 1)
    (SourceConditionalRecovery.decoderValue read (runtime.advance depth) bound decoder)
  have evaluated := (evalAt (historyPMF bound) index supported).map_sub
    (taskValue (historyPMF bound) task) (actorPullback read runtime bound estimate)
  change (taskValue (historyPMF bound) task - actorPullback read runtime bound estimate) index =
    taskValue (historyPMF bound) task index - actorPullback read runtime bound estimate index at evaluated
  rw [evaluated, taskValue_at _ _ _ supported, actorPullback_at]
  have atSample := SourceConditionalRecovery.History.liftEstimator_at_sample read runtime bound (depth + 1)
    (SourceConditionalRecovery.decoderValue read (runtime.advance depth) bound decoder) index
  have atomEq := nextAtom_eq_next_sample read (runtime.advance depth) bound index
  have readback := (congrArg (SourceConditionalRecovery.decoderValue read (runtime.advance depth) bound decoder) atomEq.symm).trans
    ((SourceConditionalRecovery.decoderValue_at_next read (runtime.advance depth) bound decoder index).trans
      (congrArg decoder atomEq))
  exact congrArg (fun value : ℂ => (historyPMF bound index).toReal * ‖task index - value‖ ^ 2)
    (atSample.trans readback).symm

theorem rawTerminalError_before_field (depth : Nat) (task : Fin (bound + 1) → ℂ) (decoder : Field read → ℂ) :
    let value := taskValue (historyPMF bound) task
    rawTerminalError read runtime bound depth task decoder =
      ‖actorResidual read runtime bound value‖ ^ 2 +
        SourceConditionalRecovery.History.terminalError read runtime bound depth
          (actorTransfer read runtime bound value) decoder :=
  (rawTerminalError_eq_norm read runtime bound depth task decoder).trans
    ((IsometricRetainedTransfer.decoder_error_decomposition (actorPullback read runtime bound)
      (taskValue (historyPMF bound) task) _).trans
        (congrArg (‖actorResidual read runtime bound (taskValue (historyPMF bound) task)‖ ^ 2 + ·)
          (SourceConditionalRecovery.History.terminalError_eq_norm read runtime bound depth
            (actorTransfer read runtime bound (taskValue (historyPMF bound) task)) decoder).symm))

end
end SourceWeightedRecovery.Runtime.Actor.History
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
