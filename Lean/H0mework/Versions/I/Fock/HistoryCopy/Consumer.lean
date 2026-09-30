import H0mework.Fock.HistoryCopy.InformationTrace
import H0mework.Fock.HistoryCopy.ObservationRecovery
import H0mework.Fock.HistoryCopy.Growth
import H0mework.Fock.CopyGraph.ConditionalObservation
import H0mework.Fock.CopyGraph.DecoderObservation
import H0mework.Fock.CopyGraph.CorrectionObservation
import H0mework.Fock.CopyGraph.CostObservation
import H0mework.Fock.CopyGraph.RefinementObservation
import H0mework.Fock.CopyGraph.GrowthObservation
import H0mework.Fock.CopyGraph.BirthObservation
import H0mework.Fock.CopyGraph.LossObservation
import H0mework.Fock.CopyGraph.FibreObservation
import H0mework.Fock.CopyGraph.RecurrenceObservation
import H0mework.Fock.CopyComplete.Observation
import H0mework.Fock.CopyFiniteComplete.Observation
import H0mework.Fock.CopyGraph.NormalInverseObservation
import H0mework.Fock.CopyGraph.ColumnForcingObservation
import H0mework.Fock.CopyGraph.RecordedEvolutionObservation
import H0mework.Fock.CopyGraph.CofinalObservation
import H0mework.Fock.CopyGraph.RecoveryBudgetObservation
import H0mework.Fock.CopyGraph.TimeModelObservation
import H0mework.Fock.CopyGraph.TimeEnergyObservation
import H0mework.Fock.CopyGraph.TimeGramObservation
import H0mework.Fock.CopyGraph.TemporalBoundaryObservation
import H0mework.Fock.CopyGraph.TemporalAcquisitionObservation
import H0mework.Fock.CopyGraph.RecordedRecurrenceObservation
import H0mework.Fock.CopyGraph.FutureAcquisitionObservation
import H0mework.Fock.CopyGraph.FutureCoordinatesObservation
import H0mework.Fock.CopyGraph.FutureUpdateObservation
import H0mework.Versions.I.Fock.CopyGraph.Observation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyObservation

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionMeasure
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

local instance consumerParentMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem actual_current (runtime : LivingRuntimeState process) : runtimeAt (inventoryBound runtime) = runtime := by
  rw [inventory_bound]
  exact (runtime_eq runtime).symm

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    type_of% (inventory_gain depth depth index) ∧ type_of% (recovered_distinctions depth depth index) ∧
      type_of% (joint_improves depth depth index) ∧ type_of% (dynamic_cost_step depth index) ∧ type_of% (written_joint depth index) ∧
      (∀ value : ParentCarrier, ∀ supported : value ∈ (SourceConditionalHistory.observed
        (SourceConditionalHistory.observed (historyPMF depth) (joint depth depth index)) Prod.fst).support,
        type_of% (complete_conditional depth depth index value supported)) ∧
      (∀ value : FieldSpace depth depth,
        type_of% (original_reconstruction depth depth index value) ∧ type_of% (original_energy depth depth index value) ∧
        (∀ atom : ParentCarrier × ParentCarrier,
          ∀ supported : atom ∈ (SourceWeightedRecovery.observed (historyPMF depth) (joint depth depth index)).support,
          type_of% (original_conditional_transfer depth depth index value atom supported)) ∧
        ∀ actor : Fin (depth + 1), type_of% (SourceGeneratedConditionalInventory.full_record_read runtime depth
          (SourceWeightedRecovery.residual (historyPMF depth) (joint depth depth index)
            (Actor.currentPullback depth depth value)) actor)) ∧
      type_of% (original_inventory_cost depth depth index) ∧
      (∀ decoder : Fin (depth + 1) → ParentCarrier × ParentCarrier → ℂ,
        type_of% (original_joint_decoder_error depth depth index decoder)) ∧
      type_of% (NativeCopy.Fock.runtime_copy_factorizes depth index
        (FullProjection.Fock.bridge (SourceOperationNative.point runtime))) ∧
      type_of% (SourceCopyInventory.normal_copy_cost runtime index) ∧
      type_of% (SourceCopyInventory.generated_next_copy_cost runtime index) ∧
      SourceConditionalGraph.ObservationAt runtime index ∧
      SourceConditionalGraphDecoder.ObservationAt runtime index ∧
      SourceConditionalCorrection.ObservationAt runtime index ∧ SourceConditionalCost.ObservationAt runtime index ∧
      SourceGraphRefinement.ObservationAt runtime index ∧ SourceGraphGrowth.ObservationAt runtime index ∧ SourceGraphBirth.ObservationAt runtime index ∧ SourceGraphLoss.ObservationAt runtime index ∧ SourceGraphFibreUpdate.ObservationAt runtime index ∧ SourceGraphRecurrence.ObservationAt runtime index ∧ SourceCompleteGraph.ObservationAt runtime index ∧ SourceFiniteCompleteGraph.ObservationAt runtime index ∧ SourceNormalInverse.ObservationAt runtime index ∧ SourceColumnForcing.ObservationAt runtime index ∧ SourceRecordedEvolution.ObservationAt runtime index ∧ SourceCopyCofinal.ObservationAt runtime index ∧ SourceCopyRecoveryBudget.ObservationAt runtime index ∧ SourceCopyTimeModel.ObservationAt runtime index ∧ SourceCopyTimeEnergy.ObservationAt runtime index ∧ SourceCopyTimeGram.ObservationAt runtime index ∧ SourceCopyTemporalBoundary.ObservationAt runtime index ∧ SourceCopyTemporalAcquisition.ObservationAt runtime index ∧ SourceCopyRecordedRecurrence.ObservationAt runtime index ∧ SourceCopyFutureAcquisition.ObservationAt runtime index ∧ SourceCopyFutureCoordinates.ObservationAt runtime index ∧ SourceCopyFutureUpdate.ObservationAt runtime index ∧ SourceCopyNativeModelStep.ObservationAt runtime index

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  exact ⟨inventory_gain _ _ index, recovered_distinctions _ _ index, joint_improves _ _ index,
    dynamic_cost_step _ index, written_joint _ index, complete_conditional _ _ index,
    (fun value => ⟨original_reconstruction _ _ index value, original_energy _ _ index value,
      original_conditional_transfer _ _ index value,
      SourceGeneratedConditionalInventory.full_record_read runtime _ _⟩),
    original_inventory_cost _ _ index, original_joint_decoder_error _ _ index,
    NativeCopy.Fock.runtime_copy_factorizes _ index (FullProjection.Fock.bridge (SourceOperationNative.point runtime)),
    SourceCopyInventory.normal_copy_cost runtime index, SourceCopyInventory.generated_next_copy_cost runtime index,
    SourceConditionalGraph.observation_consumed runtime index,
    SourceConditionalGraphDecoder.observation_consumed runtime index,
    SourceConditionalCorrection.observation_consumed runtime index, SourceConditionalCost.observation_consumed runtime index,
    SourceGraphRefinement.observation_consumed runtime index, SourceGraphGrowth.observation_consumed runtime index, SourceGraphBirth.observation_consumed runtime index, SourceGraphLoss.observation_consumed runtime index, SourceGraphFibreUpdate.observation_consumed runtime index, SourceGraphRecurrence.observation_consumed runtime index, SourceCompleteGraph.observation_consumed runtime index, SourceFiniteCompleteGraph.observation_consumed runtime index, SourceNormalInverse.observation_consumed runtime index, SourceColumnForcing.observation_consumed runtime index, SourceRecordedEvolution.observation_consumed runtime index, SourceCopyCofinal.observation_consumed runtime index, SourceCopyRecoveryBudget.observation_consumed runtime index, SourceCopyTimeModel.observation_consumed runtime index, SourceCopyTimeEnergy.observation_consumed runtime index, SourceCopyTimeGram.observation_consumed runtime index, SourceCopyTemporalBoundary.observation_consumed runtime index, SourceCopyTemporalAcquisition.observation_consumed runtime index, SourceCopyRecordedRecurrence.observation_consumed runtime index, SourceCopyFutureAcquisition.observation_consumed runtime index, SourceCopyFutureCoordinates.observation_consumed runtime index, SourceCopyFutureUpdate.observation_consumed runtime index, SourceCopyNativeModelStep.observation_consumed runtime index⟩

def CurrentAt (runtime : LivingRuntimeState process) : Prop :=
    let depth := inventoryBound runtime
    type_of% (actual_current runtime) ∧ type_of% (Actor.current_pmf depth depth) ∧
      (∀ index : Index depth, ObservationAt runtime index) ∧
      (∀ actor : Fin (depth + 1),
        type_of% (Actor.originalRead_actual depth depth actor) ∧
        type_of% (SourceOperationNative.point_factorizes (runtimeAt actor.val))) ∧
      (∀ decoder : Fin (depth + 1) → ParentCarrier → ℂ, type_of% (original_decoder_lower depth depth decoder)) ∧
      type_of% (SourceGeneratedConditionalInventory.inventory_consumed runtime depth) ∧
      type_of% (coversAt_factorizes runtime .particleWave) ∧
      type_of% (coversAt_factorizes runtime.tick.next .particleWave) ∧
      type_of% (coversAt_factorizes (normal runtime).targetRuntime.tick.next .particleWave) ∧
      type_of% (SourceCopyNativeModelStep.calculation_consumed runtime)

theorem current_consumed (runtime : LivingRuntimeState process) : CurrentAt runtime := by
  dsimp only [CurrentAt]
  with_reducible exact ⟨actual_current runtime, Actor.current_pmf _ _, observation_consumed runtime,
    (fun actor => ⟨Actor.originalRead_actual _ _ actor, SourceOperationNative.point_factorizes (runtimeAt actor.val)⟩),
    original_decoder_lower _ _, SourceGeneratedConditionalInventory.inventory_consumed runtime _,
    coversAt_factorizes runtime .particleWave, coversAt_factorizes runtime.tick.next .particleWave,
    coversAt_factorizes (normal runtime).targetRuntime.tick.next .particleWave,
    SourceCopyNativeModelStep.calculation_consumed runtime⟩

theorem bound_three : inventoryBound (runtimeAt 3) = 3 :=
  (inventory_bound (runtimeAt 3)).trans (runtimeAt_state 3)

def ActualRecovery : Prop :=
    CurrentAt (runtimeAt 3) ∧ type_of% bound_three ∧ type_of% actual_copy_recovery ∧
      type_of% no_snapshot_copy ∧ type_of% after_information_zero ∧ type_of% actual_conditional_information_gain ∧
      (∀ actor : Fin 4, type_of% (after_posterior actor)) ∧
      (∀ task : Fin 4 → ℂ, ∀ actor : Fin 4, type_of% (after_recovery task actor)) ∧
      (∀ value : FieldSpace 3 3, type_of% (actual_original_recovery value)) ∧
      (∀ decoder : Fin 4 → ParentCarrier → ℂ, type_of% (actual_original_decoder_lower decoder)) ∧
      type_of% (SourceCopyProgram.material_program 3 twoMaterial) ∧
      type_of% (SourceCopyProgram.copy_written_program 3 twoMaterial) ∧
      type_of% SourceConditionalGraph.before_graph_cost_strict ∧
      (∀ value : FieldSpace 3 3,
        type_of% (SourceConditionalGraph.after_graph_error_zero (Actor.currentPullback 3 3 value))) ∧
      SourceConditionalGraphDecoder.ActualRecovery ∧ SourceConditionalCorrection.ActualRecovery ∧ SourceConditionalCost.ActualRecovery ∧
      SourceGraphRefinement.ActualRecovery ∧ SourceGraphGrowth.ActualRecovery ∧ SourceGraphBirth.ActualRecovery ∧ SourceGraphLoss.ActualRecovery ∧ SourceGraphFibreUpdate.ActualRecovery ∧ SourceGraphRecurrence.ActualRecovery ∧ SourceCompleteGraph.ActualRecovery ∧ SourceFiniteCompleteGraph.ActualRecovery ∧ SourceNormalInverse.ActualRecovery ∧ SourceColumnForcing.ActualRecovery ∧ SourceRecordedEvolution.ActualRecovery ∧ SourceCopyCofinal.ActualRecovery ∧ SourceCopyRecoveryBudget.ActualRecovery ∧ SourceCopyTimeModel.ActualRecovery ∧ SourceCopyTimeEnergy.ActualRecovery ∧ SourceCopyTimeGram.ActualRecovery ∧ SourceCopyTemporalBoundary.ActualRecovery ∧ SourceCopyTemporalAcquisition.ActualRecovery ∧ SourceCopyRecordedRecurrence.ActualRecovery ∧ SourceCopyFutureAcquisition.ActualRecovery ∧ SourceCopyFutureCoordinates.ActualRecovery ∧ SourceCopyFutureUpdate.ActualRecovery ∧ SourceCopyNativeModelStep.ActualRecovery

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  exact ⟨current_consumed (runtimeAt 3), bound_three, actual_copy_recovery, no_snapshot_copy,
    after_information_zero, actual_conditional_information_gain, after_posterior, after_recovery,
    actual_original_recovery, actual_original_decoder_lower,
    SourceCopyProgram.material_program 3 twoMaterial, SourceCopyProgram.copy_written_program 3 twoMaterial,
    SourceConditionalGraph.before_graph_cost_strict,
    (fun value => SourceConditionalGraph.after_graph_error_zero (Actor.currentPullback 3 3 value)),
    SourceConditionalGraphDecoder.actual_recovery_consumed, SourceConditionalCorrection.actual_recovery_consumed,
    SourceConditionalCost.actual_recovery_consumed, SourceGraphRefinement.actual_recovery_consumed, SourceGraphGrowth.actual_recovery_consumed, SourceGraphBirth.actual_recovery_consumed, SourceGraphLoss.actual_recovery_consumed, SourceGraphFibreUpdate.actual_recovery_consumed, SourceGraphRecurrence.actual_recovery_consumed, SourceCompleteGraph.actual_recovery_consumed, SourceFiniteCompleteGraph.actual_recovery_consumed, SourceNormalInverse.actual_recovery_consumed, SourceColumnForcing.actual_recovery_consumed, SourceRecordedEvolution.actual_recovery_consumed, SourceCopyCofinal.actual_recovery_consumed, SourceCopyRecoveryBudget.actual_recovery_consumed, SourceCopyTimeModel.actual_recovery_consumed, SourceCopyTimeEnergy.actual_recovery_consumed, SourceCopyTimeGram.actual_recovery_consumed, SourceCopyTemporalBoundary.actual_recovery_consumed, SourceCopyTemporalAcquisition.actual_recovery_consumed, SourceCopyRecordedRecurrence.actual_recovery_consumed, SourceCopyFutureAcquisition.actual_recovery_consumed, SourceCopyFutureCoordinates.actual_recovery_consumed, SourceCopyFutureUpdate.actual_recovery_consumed, SourceCopyNativeModelStep.actual_recovery_consumed⟩

def RecoveryAt (round : Nat) : Prop :=
    CurrentAt (roundRuntime round) ∧ ActualRecovery ∧
      type_of% (SourceCopyProgram.sourceGeneratedCopyRecovery round) ∧
      SourceConditionalGraph.RoundAt round ∧ SourceConditionalGraphDecoder.RoundAt round ∧ SourceConditionalCorrection.RoundAt round ∧
      SourceConditionalCost.RoundAt round ∧ SourceGraphRefinement.RoundAt round ∧ SourceGraphGrowth.RoundAt round ∧ SourceGraphBirth.RoundAt round ∧ SourceGraphLoss.RoundAt round ∧ SourceGraphFibreUpdate.RoundAt round ∧ SourceGraphRecurrence.RoundAt round ∧ SourceCompleteGraph.RoundAt round ∧ SourceFiniteCompleteGraph.RoundAt round ∧ SourceNormalInverse.RoundAt round ∧ SourceColumnForcing.RoundAt round ∧ SourceRecordedEvolution.RoundAt round ∧ SourceCopyCofinal.RoundAt round ∧ SourceCopyRecoveryBudget.RoundAt round ∧ SourceCopyTimeModel.RoundAt round ∧ SourceCopyTimeEnergy.RoundAt round ∧ SourceCopyTimeGram.RoundAt round ∧ SourceCopyTemporalBoundary.RoundAt round ∧ SourceCopyTemporalAcquisition.RoundAt round ∧ SourceCopyRecordedRecurrence.RoundAt round ∧ SourceCopyFutureAcquisition.RoundAt round ∧ SourceCopyFutureCoordinates.RoundAt round ∧ SourceCopyFutureUpdate.RoundAt round ∧ SourceCopyNativeModelStep.RoundAt round

theorem sourceGeneratedCopyObservationRecovery (round : Nat) : RecoveryAt round :=
  ⟨current_consumed (roundRuntime round), actual_recovery_consumed, SourceCopyProgram.sourceGeneratedCopyRecovery round,
    SourceConditionalGraph.round_consumed round, SourceConditionalGraphDecoder.round_consumed round,
    SourceConditionalCorrection.round_consumed round, SourceConditionalCost.round_consumed round, SourceGraphRefinement.round_consumed round,
    SourceGraphGrowth.round_consumed round, SourceGraphBirth.round_consumed round, SourceGraphLoss.round_consumed round, SourceGraphFibreUpdate.round_consumed round, SourceGraphRecurrence.round_consumed round, SourceCompleteGraph.round_consumed round, SourceFiniteCompleteGraph.round_consumed round, SourceNormalInverse.round_consumed round, SourceColumnForcing.round_consumed round, SourceRecordedEvolution.round_consumed round, SourceCopyCofinal.round_consumed round, SourceCopyRecoveryBudget.round_consumed round, SourceCopyTimeModel.round_consumed round, SourceCopyTimeEnergy.round_consumed round, SourceCopyTimeGram.round_consumed round, SourceCopyTemporalBoundary.round_consumed round, SourceCopyTemporalAcquisition.round_consumed round, SourceCopyRecordedRecurrence.round_consumed round, SourceCopyFutureAcquisition.round_consumed round, SourceCopyFutureCoordinates.round_consumed round, SourceCopyFutureUpdate.round_consumed round, SourceCopyNativeModelStep.round_consumed round⟩

end
end SourceCopyObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
