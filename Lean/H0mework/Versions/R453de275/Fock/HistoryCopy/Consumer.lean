import H0mework.Versions.X.Fock.HistoryCopy.InformationTrace
import H0mework.Versions.X.Fock.HistoryCopy.ObservationRecovery
import H0mework.Versions.R453de275.Fock.HistoryCopy.Growth
import H0mework.Versions.X.Fock.CopyGraph.ConditionalObservation
import H0mework.Versions.X.Fock.CopyGraph.DecoderObservation
import H0mework.Versions.X.Fock.CopyGraph.CorrectionObservation
import H0mework.Versions.X.Fock.CopyGraph.CostObservation
import H0mework.Versions.X.Fock.CopyGraph.RefinementObservation
import H0mework.Versions.X.Fock.CopyGraph.GrowthObservation
import H0mework.Versions.X.Fock.CopyGraph.BirthObservation
import H0mework.Versions.X.Fock.CopyGraph.LossObservation
import H0mework.Versions.X.Fock.CopyGraph.FibreObservation
import H0mework.Versions.X.Fock.CopyGraph.RecurrenceObservation
import H0mework.Versions.X.Fock.CopyComplete.Observation
import H0mework.Versions.X.Fock.CopyFiniteComplete.Observation
import H0mework.Versions.X.Fock.CopyGraph.NormalInverseObservation
import H0mework.Versions.X.Fock.CopyGraph.ColumnForcingObservation
import H0mework.Versions.X.Fock.CopyGraph.RecordedEvolutionObservation
import H0mework.Versions.X.Fock.CopyGraph.CofinalObservation
import H0mework.Versions.X.Fock.CopyGraph.RecoveryBudgetObservation
import H0mework.Versions.X.Fock.CopyGraph.TimeModelObservation
import H0mework.Versions.X.Fock.CopyGraph.TimeEnergyObservation
import H0mework.Versions.X.Fock.CopyGraph.TimeGramObservation
import H0mework.Versions.X.Fock.CopyGraph.TemporalBoundaryObservation
import H0mework.Versions.X.Fock.CopyGraph.TemporalAcquisitionObservation
import H0mework.Versions.X.Fock.CopyGraph.RecordedRecurrenceObservation
import H0mework.Versions.X.Fock.CopyGraph.FutureAcquisitionObservation
import H0mework.Versions.X.Fock.CopyGraph.FutureCoordinatesObservation
import H0mework.Versions.X.Fock.CopyGraph.FutureUpdateObservation
import H0mework.Versions.R453de275.Fock.CopyGraph.Observation
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Model.Family.Words.Dynamic.Hilbert.SourceWord.Precision
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.CodeRisk
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Posterior
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.RootAction
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.Consumer
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.ActionLoss
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.ActionRisk
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.NativeBirth
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.BirthRecovery
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.TaskCriterion
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.RiskBirth
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.OptimalRiskControl.Old
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.ActionRefinement
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.ActionRefinementControl
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Controls
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Model.Family.Words.Dynamic.Hilbert.SourceWord.ObservedCode.Future.Growth.Posterior
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Receiver.Controls
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Receiver.FixedErasure

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyObservation

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionMeasure
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalModel (Actors NextModel)
open SourceGeneratedActionWords
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

local instance consumerParentMeasurable : MeasurableSpace ParentCarrier := ⊤
local instance copyConsumerWordsMeasurable (depth : Nat) :
    MeasurableSpace (Fock.Complete.Carrier depth) :=
  Fock.Dynamic.Hilbert.measurable depth

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

theorem actual_birth_g_risk_at_least_four_fifths
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    (4 / 5 : ℝ) ≤ SourceWordCodeRisk.risk (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
      (SourceWordObservedCode.encodeObserved (runtimeAt 4)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])) decoder := by
  have oldRisk := SourceWordFieldCode.actual_copy_original_g_risk_at_least_one decoder
  have birth := SourceWordFieldCode.actual_copy_g_risk_native_birth decoder
  have bornNonneg : 0 ≤ ‖SourceCompiledGWord.image (runtimeAt 4)
      (inventoryBound (runtimeAt 4) + 1)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
      (Fin.last (inventoryBound (runtimeAt 4))) -
    decoder (SourceWordObservedCode.sourceQuery (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
      (Fin.last (inventoryBound (runtimeAt 4))))‖ ^ 2 := sq_nonneg _
  change 1 ≤ SourceWordCodeRisk.risk (runtimeAt 3)
    (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])
    (SourceWordObservedCode.encodeObserved (runtimeAt 3)
      (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])) decoder at oldRisk
  nlinarith

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
      SourceGraphRefinement.ActualRecovery ∧ SourceGraphGrowth.ActualRecovery ∧ SourceGraphBirth.ActualRecovery ∧ SourceGraphLoss.ActualRecovery ∧ SourceGraphFibreUpdate.ActualRecovery ∧ SourceGraphRecurrence.ActualRecovery ∧ SourceCompleteGraph.ActualRecovery ∧ SourceFiniteCompleteGraph.ActualRecovery ∧ SourceNormalInverse.ActualRecovery ∧ SourceColumnForcing.ActualRecovery ∧ SourceRecordedEvolution.ActualRecovery ∧ SourceCopyCofinal.ActualRecovery ∧ SourceCopyRecoveryBudget.ActualRecovery ∧ SourceCopyTimeModel.ActualRecovery ∧ SourceCopyTimeEnergy.ActualRecovery ∧ SourceCopyTimeGram.ActualRecovery ∧ SourceCopyTemporalBoundary.ActualRecovery ∧ SourceCopyTemporalAcquisition.ActualRecovery ∧ SourceCopyRecordedRecurrence.ActualRecovery ∧ SourceCopyFutureAcquisition.ActualRecovery ∧ SourceCopyFutureCoordinates.ActualRecovery ∧ SourceCopyFutureUpdate.ActualRecovery ∧ SourceCopyNativeModelStep.ActualRecovery ∧
      (∀ observationDepth : Nat, ∀ decoder : Field parity → SourceJointClockGraph.Carrier,
        type_of% (SourceWordDynamicNext.actual_copy_word_coarse_strict observationDepth decoder)) ∧
      (∀ (encode : SourceWordMinimalCode.WordImage (runtimeAt 3)
          [SourceWordDynamicNext.copyOne] → Unit)
        (candidateDecoder : Unit → SourceJointClockGraph.Carrier),
        type_of% (SourceWordMinimalCode.actual_copy_word_no_unit_code encode candidateDecoder)) ∧
      (∀ (encode : SourceWordMinimalCode.WordImage (runtimeAt 3)
          [SourceWordDynamicNext.copyOne] → Unit)
        (candidateDecoder : Unit → SourceJointClockGraph.Carrier),
        type_of% (SourceWordCodeRisk.actual_copy_word_no_unit_free_risk encode candidateDecoder)) ∧
      type_of% (SourceWordNativeAlignment.native_word_risk_eq_original_gap (runtimeAt 3)) ∧
      type_of% SourceWordNativeAlignment.original_gap_half_at_three ∧
      type_of% SourceWordNativeAlignment.original_next_gap_three_fifths ∧
      type_of% (SourceWordNativeAlignment.generated_native_observed_law 3) ∧
      type_of% (SourceWordNativeAlignment.installed_face 3) ∧
      type_of% (SourceWordObservedCode.post_word_code_law
        (runtimeAt 3) [SourceWordDynamicNext.copyOne]) ∧
      type_of% (SourceWordActedRow.post_word_row_law
        (runtimeAt 3) [SourceWordDynamicNext.copyOne]) ∧
      (∀ actor : Fin 4,
        type_of% (SourceWordNativeAlignment.installed_root_entry_disposition actor.val)) ∧
      (∀ key : ZMod 2,
        ∀ supported : key ∈ ((historyPMF 3).map
          (fun actor : Fin 4 => SourceWordObservedCode.observe
            (Fock.actualWord 4 [SourceWordDynamicNext.copyOne]
              (runtimePayload actor.val).nativeWrite.target))).support,
          type_of% (SourceWordActedRow.counted_row_posterior (runtimeAt 3)
            SourceWordObservedCode.actual_nonunit [SourceWordDynamicNext.copyOne]
            key supported)) ∧
      (∀ decoder : ZMod 2 → SourceJointClockGraph.Carrier,
        type_of% (SourceWordActedRow.row_information_risk
          (runtimeAt 3) [SourceWordDynamicNext.copyOne] decoder)) ∧
      type_of% (SourceWordActedRow.actual_copy_one_does_not_commute 0) ∧
      type_of% SourceWordActedRow.actual_copy_one_observation_order_clash ∧
      (∀ task : Fin 4 → ℂ, ∀ key : ZMod 2,
        ∀ supported : key ∈ (SourceConditionalHistory.observed
          (SourceConditionalHistory.observed (historyPMF 3)
            (Actor.nextRead 4 3))
          (SourceWordFieldCode.fieldCode 3 [SourceWordDynamicNext.copyOne])).support,
        ∀ value : SourceWeightedRecovery.Space
          (wordLaw 4 CanonicalUnitArithmeticRoot.initialCurrent 3),
          type_of% (SourceWordFieldCode.original_code_time_consumed
            (runtimeAt 3) SourceWordObservedCode.actual_nonunit
            [SourceWordDynamicNext.copyOne] task key supported value)) ∧
      (∀ before after : List (Fock.Letter 4),
        type_of% (SourceWordFieldCode.source_information_tower (runtimeAt 3) before after)) ∧
      (∀ before after : List (Fock.Letter 4),
        type_of% (SourceWordFieldCode.original_native_birth_information_loss 3 before after)) ∧
      type_of% SourceWordFieldCode.actual_copy_native_birth_information_loss ∧
      type_of% SourceWordFieldCode.actual_copy_birth_correction_positive ∧
      type_of% SourceWordFieldCode.actual_birth_copy_information_amount_positive ∧
      type_of% SourceWordFieldCode.actual_birth_copy_full_model_gap_positive ∧
      type_of% SourceWordFieldCode.actual_birth_copy_clock_l2_increment_zero ∧
      type_of% SourceWordFieldCode.actual_birth_copy_clock_residual_unchanged ∧
      (∀ before : List (Fock.Letter 4),
        type_of% (SourceWordFieldCode.original_native_birth_empty_tail_correction 3 before)) ∧
      (∀ before after : List (Fock.Letter 4),
        type_of% (SourceWordFieldCode.source_information_tower (runtimeAt 4)
          (SourceWordFutureBitGrowth.nextWordAt 3 before)
          (SourceWordFutureBitGrowth.nextWordAt 3 after))) ∧
      (∀ before : List (Fock.Letter 4),
        type_of% (SourceWordFieldCode.native_tail_no_information_loss (runtimeAt 3) before)) ∧
      (∀ before after : List (Fock.Letter 4), ∀ task : Fin 4 → ℂ,
        type_of% (SourceWordFieldCode.original_field_residual_tower 3 before after task)) ∧
      (∀ before after : List (Fock.Letter 4), ∀ task : Fin 4 → ℂ,
        type_of% (SourceWordFieldCode.original_task_increment_zero_iff 3 before after task)) ∧
      (∀ before after : List (Fock.Letter 4),
        type_of% (SourceWordFieldCode.all_original_unit_increments_zero_iff 3 before after)) ∧
      (∀ before after : List (Fock.Letter 4),
        type_of% (SourceWordFieldCode.all_original_unit_increments_zero_iff_information_loss_zero
          (runtimeAt 3) before after)) ∧
      (∀ before after : List (Fock.Letter 4),
        ∀ task : Actors (runtimeAt 4) → ℂ,
        type_of% (SourceWordFieldCode.original_field_residual_tower
          (inventoryBound (runtimeAt 4))
          (SourceWordFutureBitGrowth.nextWordAt 3 before)
          (SourceWordFutureBitGrowth.nextWordAt 3 after) task)) ∧
      (∀ before after : List (Fock.Letter 4),
        ∀ task : Actors (runtimeAt 4) → ℂ,
        type_of% (SourceWordFieldCode.original_task_increment_zero_iff
          (inventoryBound (runtimeAt 4))
          (SourceWordFutureBitGrowth.nextWordAt 3 before)
          (SourceWordFutureBitGrowth.nextWordAt 3 after) task)) ∧
      (∀ before after : List (Fock.Letter 4),
        type_of% (SourceWordFieldCode.all_original_unit_increments_zero_iff
          (inventoryBound (runtimeAt 4))
          (SourceWordFutureBitGrowth.nextWordAt 3 before)
          (SourceWordFutureBitGrowth.nextWordAt 3 after))) ∧
      (∀ before after : List (Fock.Letter 4),
        type_of% (SourceWordFieldCode.all_original_unit_increments_zero_iff_information_loss_zero
          (runtimeAt 4) (SourceWordFutureBitGrowth.nextWordAt 3 before)
          (SourceWordFutureBitGrowth.nextWordAt 3 after))) ∧
      type_of% SourceWordFieldCode.actual_copy_information_strict ∧
      type_of% SourceWordFieldCode.actual_copy_l2_increment_strict ∧
      (∀ task : Fin 4 → ℂ,
        type_of% (SourceWordFieldCode.empty_tail_no_l2_increment 3 [] task)) ∧
      (∀ before after : List (Fock.Letter 4),
        ∀ decoder : ZMod 2 → SourceJointClockGraph.Carrier,
        type_of% (SourceWordFieldCode.original_acted_g_risk_tower
          (runtimeAt 3) before after decoder)) ∧
      (∀ before after : List (Fock.Letter 4),
        ∀ decoder : ZMod 2 → SourceJointClockGraph.Carrier,
        type_of% (SourceWordFieldCode.original_acted_g_risk_tower
          (runtimeAt 4) (SourceWordFutureBitGrowth.nextWordAt 3 before)
          (SourceWordFutureBitGrowth.nextWordAt 3 after) decoder)) ∧
      type_of% SourceWordFieldCode.actual_copy_clock_l2_increment ∧
      type_of% SourceWordFieldCode.actual_copy_clock_l2_increment_positive ∧
      (∀ decoder : ZMod 2 → SourceJointClockGraph.Carrier,
        type_of% (SourceWordFieldCode.actual_copy_original_g_risk_account decoder)) ∧
      (∀ decoder : ZMod 2 → SourceJointClockGraph.Carrier,
        type_of% (SourceWordFieldCode.actual_copy_original_g_risk_at_least_one decoder)) ∧
      (∀ decoder : ZMod 2 → SourceJointClockGraph.Carrier,
        type_of% (SourceWordFieldCode.actual_copy_g_risk_native_birth decoder) ∧
        type_of% (actual_birth_g_risk_at_least_four_fifths decoder)) ∧
      type_of% SourceWordFieldCode.actual_copy_optimal_g_total_birth ∧
      type_of% SourceWordFieldCode.actual_copy_old_optimal_g_risk ∧
      type_of% SourceWordFieldCode.actual_copy_next_optimal_g_risk ∧
      type_of% SourceWordFieldCode.actual_copy_born_g_innovation_sq ∧
      type_of% SourceWordFieldCode.actual_copy_optimal_g_total_gain_positive ∧
      (∀ decoder : ZMod 2 → SourceJointClockGraph.Carrier,
        type_of% (SourceWordFieldCode.gBest_risk_le (runtimeAt 4)
          (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) decoder)) ∧
      type_of% (SourceWordFieldCode.gRisk_refinement (runtimeAt 4)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
        (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4))
          (SourceWordFutureBitGrowth.nextWordAt 3 []))
        (SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 4) + 1)
          (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]))) ∧
      type_of% (SourceWordFieldCode.gGap_zero_iff_information_zero (runtimeAt 4)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
        (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4))
          (SourceWordFutureBitGrowth.nextWordAt 3 []))
        (SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 4) + 1)
          (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]))) ∧
      type_of% SourceWordFieldCode.actual_transported_copy_g_gap_positive ∧
      type_of% SourceWordFieldCode.actual_transported_copy_g_gap_exact ∧
      (∀ word : List (Fock.Letter 4), ∀ left right : Fin 4,
        type_of% (SourceWordFutureBit.future_kernel (runtimeAt 3) word left right)) ∧
      (∀ actor : Fin 4,
        type_of% (SourceWordFutureBit.counted_future_posterior
          (runtimeAt 3) SourceWordObservedCode.actual_nonunit
          [SourceWordDynamicNext.copyOne] actor)) ∧
      type_of% (SourceWordFutureBit.future_information
        (runtimeAt 3) [SourceWordDynamicNext.copyOne]) ∧
      (∀ word : List (Fock.Letter 4),
        ∀ decoder : (List (Fock.Letter 4) → ZMod 2) → SourceJointClockGraph.Carrier,
          type_of% (SourceWordFutureBit.actual_future_half_risk word decoder)) ∧
      type_of% SourceWordFutureBit.actual_future_strictly_coarser_than_whole_model ∧
      (∀ bit : ZMod 2, type_of% (SourceWordFutureBit.actual_copyOne_erases_future_bit bit)) ∧
      (∀ word : List (Fock.Letter 4), ∀ key : ZMod 2,
        type_of% (SourceWordFutureBitGrowth.old_new_counted_model 3
          SourceWordObservedCode.actual_nonunit word key)) ∧
      (∀ word : List (Fock.Letter 4), ∀ key : ZMod 2,
        type_of% (SourceWordFutureBitGrowth.old_next_model_eq_new_start 3
          SourceWordObservedCode.actual_nonunit word key)) ∧
      (∀ word : List (Fock.Letter 4), ∀ steps : Nat, ∀ key : ZMod 2,
        ∀ supported : key ∈ ((historyPMF (inventoryBound ((runtimeAt 3).advance steps))).map
          (fun actor : Actors ((runtimeAt 3).advance steps) =>
            SourceWordObservedCode.readAt 4
              (word.map (Fock.Dynamic.oldLetter 4)) actor.val)).support,
          type_of% (SourceWordFutureBitGrowth.counted_old_letter_posterior
            (runtimeAt 3) SourceWordObservedCode.actual_nonunit word steps key supported)) ∧
      (∀ bit : ZMod 2, type_of% (SourceWordFutureBitGrowth.fresh_bit_action 3 bit)) ∧
      type_of% (SourceWordFutureBitGrowth.fresh_complete_action_is_source_step 3) ∧
      type_of% (SourceWordFutureBitGrowth.fresh_read_at_next_material 3) ∧
      type_of% ((SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt 4)).factorizes) ∧
      type_of% (SourceWordFreshReceiver.fresh_read_all 3) ∧
      type_of% (SourceWordFreshReceiver.fresh_post_word_law 2) ∧
      type_of% (SourceWordFreshReceiver.fresh_post_word_law 3) ∧
      type_of% (SourceWordFreshReceiver.fresh_received 3
        SourceWordObservedCode.actual_nonunit) ∧
      type_of% (SourceWordFreshReceiver.fresh_complete_posterior 3
        SourceWordObservedCode.actual_nonunit) ∧
      type_of% (SourceWordFreshReceiver.fresh_next_model 3
        SourceWordObservedCode.actual_nonunit) ∧
      type_of% (SourceWordFreshReceiver.fresh_original_G_full_account 3) ∧
      type_of% SourceWordFreshReceiver.fresh_original_G_half_risk ∧
      type_of% SourceWordFreshReceiver.erased_posterior_at_two ∧
      type_of% SourceWordFreshReceiver.retained_complete_model_at_three ∧
      type_of% (SourceWordFutureBitGrowth.next_runtime 2) ∧
      type_of% ((SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt 2)).factorizes) ∧
      type_of% SourceWordFixedErasure.read_all_zero ∧
      type_of% SourceWordFixedErasure.complete_history_at ∧
      type_of% SourceWordFixedErasure.next_model_is_full_history ∧
      type_of% SourceWordFixedErasure.next_readback_is_full_history ∧
      type_of% SourceWordFixedErasure.received_on_generated_stage ∧
      type_of% (SourceWordFreshReceiver.fresh_original_G_full_account 2) ∧
      (∀ decoder : ZMod 2 → SourceJointClockGraph.Carrier,
        type_of% (SourceWordObservedCode.observed_information_risk
          (runtimeAt 3) [SourceWordDynamicNext.copyOne] decoder) ∧
        type_of% (SourceWordObservedCode.actual_observed_half_risk
          [SourceWordDynamicNext.copyOne] decoder)) ∧
      (∀ steps : Nat,
        type_of% (SourceWordObservedCode.received (runtimeAt 3)
          SourceWordObservedCode.actual_nonunit [SourceWordDynamicNext.copyOne] steps)) ∧
      (∀ key : ZMod 2,
        type_of% (SourceWordObservedCode.observed_mass_received (runtimeAt 3)
          SourceWordObservedCode.actual_nonunit [SourceWordDynamicNext.copyOne] key)) ∧
      (∀ key : ZMod 2, ∀ supported : key ∈ ((historyPMF (inventoryBound (runtimeAt 3))).map
          (SourceWordObservedCode.sourceQuery (runtimeAt 3) [SourceWordDynamicNext.copyOne])).support,
        type_of% (SourceWordObservedCode.counted_complete_posterior (runtimeAt 3)
          SourceWordObservedCode.actual_nonunit [SourceWordDynamicNext.copyOne] key supported)) ∧
      (∀ steps : Nat, ∀ key : ZMod 2,
        ∀ supported : key ∈ ((historyPMF (inventoryBound ((runtimeAt 3).advance steps))).map
          (fun actor : SourceConditionalModel.Actors ((runtimeAt 3).advance steps) =>
            SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
              [SourceWordDynamicNext.copyOne] actor.val)).support,
        type_of% (SourceWordObservedCode.counted_complete_posterior_at (runtimeAt 3)
          SourceWordObservedCode.actual_nonunit [SourceWordDynamicNext.copyOne]
          steps key supported)) ∧
      ∀ steps : Nat, ∀ key : ZMod 2,
        type_of% (SourceWordObservedCode.counted_model (runtimeAt 3)
          SourceWordObservedCode.actual_nonunit [SourceWordDynamicNext.copyOne] steps key) ∧
        type_of% (SourceWordObservedCode.counted_next_model (runtimeAt 3)
          SourceWordObservedCode.actual_nonunit [SourceWordDynamicNext.copyOne] steps key)

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  exact ⟨current_consumed (runtimeAt 3), bound_three, actual_copy_recovery, no_snapshot_copy,
    after_information_zero, actual_conditional_information_gain, after_posterior, after_recovery,
    actual_original_recovery, actual_original_decoder_lower,
    SourceCopyProgram.material_program 3 twoMaterial, SourceCopyProgram.copy_written_program 3 twoMaterial,
    SourceConditionalGraph.before_graph_cost_strict,
    (fun value => SourceConditionalGraph.after_graph_error_zero (Actor.currentPullback 3 3 value)),
    SourceConditionalGraphDecoder.actual_recovery_consumed, SourceConditionalCorrection.actual_recovery_consumed,
    SourceConditionalCost.actual_recovery_consumed, SourceGraphRefinement.actual_recovery_consumed, SourceGraphGrowth.actual_recovery_consumed, SourceGraphBirth.actual_recovery_consumed, SourceGraphLoss.actual_recovery_consumed, SourceGraphFibreUpdate.actual_recovery_consumed, SourceGraphRecurrence.actual_recovery_consumed, SourceCompleteGraph.actual_recovery_consumed, SourceFiniteCompleteGraph.actual_recovery_consumed, SourceNormalInverse.actual_recovery_consumed, SourceColumnForcing.actual_recovery_consumed, SourceRecordedEvolution.actual_recovery_consumed, SourceCopyCofinal.actual_recovery_consumed, SourceCopyRecoveryBudget.actual_recovery_consumed, SourceCopyTimeModel.actual_recovery_consumed, SourceCopyTimeEnergy.actual_recovery_consumed, SourceCopyTimeGram.actual_recovery_consumed, SourceCopyTemporalBoundary.actual_recovery_consumed, SourceCopyTemporalAcquisition.actual_recovery_consumed, SourceCopyRecordedRecurrence.actual_recovery_consumed, SourceCopyFutureAcquisition.actual_recovery_consumed, SourceCopyFutureCoordinates.actual_recovery_consumed, SourceCopyFutureUpdate.actual_recovery_consumed, SourceCopyNativeModelStep.actual_recovery_consumed,
    SourceWordDynamicNext.actual_copy_word_coarse_strict,
    SourceWordMinimalCode.actual_copy_word_no_unit_code,
    SourceWordCodeRisk.actual_copy_word_no_unit_free_risk,
    SourceWordNativeAlignment.native_word_risk_eq_original_gap (runtimeAt 3),
    SourceWordNativeAlignment.original_gap_half_at_three,
    SourceWordNativeAlignment.original_next_gap_three_fifths,
    SourceWordNativeAlignment.generated_native_observed_law 3,
    SourceWordNativeAlignment.installed_face 3,
    SourceWordObservedCode.post_word_code_law (runtimeAt 3) [SourceWordDynamicNext.copyOne],
    SourceWordActedRow.post_word_row_law (runtimeAt 3) [SourceWordDynamicNext.copyOne],
    (fun actor => SourceWordNativeAlignment.installed_root_entry_disposition actor.val),
    (fun key supported => SourceWordActedRow.counted_row_posterior (runtimeAt 3)
      SourceWordObservedCode.actual_nonunit [SourceWordDynamicNext.copyOne] key supported),
    SourceWordActedRow.row_information_risk (runtimeAt 3) [SourceWordDynamicNext.copyOne],
    SourceWordActedRow.actual_copy_one_does_not_commute 0,
    SourceWordActedRow.actual_copy_one_observation_order_clash,
    (fun task key supported value => SourceWordFieldCode.original_code_time_consumed
      (runtimeAt 3) SourceWordObservedCode.actual_nonunit
      [SourceWordDynamicNext.copyOne] task key supported value),
    (fun before after => SourceWordFieldCode.source_information_tower (runtimeAt 3) before after),
    (fun before after => SourceWordFieldCode.original_native_birth_information_loss 3 before after),
    SourceWordFieldCode.actual_copy_native_birth_information_loss,
    SourceWordFieldCode.actual_copy_birth_correction_positive,
    SourceWordFieldCode.actual_birth_copy_information_amount_positive,
    SourceWordFieldCode.actual_birth_copy_full_model_gap_positive,
    SourceWordFieldCode.actual_birth_copy_clock_l2_increment_zero,
    SourceWordFieldCode.actual_birth_copy_clock_residual_unchanged,
    (fun before => SourceWordFieldCode.original_native_birth_empty_tail_correction 3 before),
    (fun before after => SourceWordFieldCode.source_information_tower (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 before)
      (SourceWordFutureBitGrowth.nextWordAt 3 after)),
    (fun before => SourceWordFieldCode.native_tail_no_information_loss (runtimeAt 3) before),
    (fun before after task => SourceWordFieldCode.original_field_residual_tower 3 before after task),
    (fun before after task => SourceWordFieldCode.original_task_increment_zero_iff 3 before after task),
    (fun before after => SourceWordFieldCode.all_original_unit_increments_zero_iff 3 before after),
    (fun before after => SourceWordFieldCode.all_original_unit_increments_zero_iff_information_loss_zero
      (runtimeAt 3) before after),
    (fun before after task => SourceWordFieldCode.original_field_residual_tower
      (inventoryBound (runtimeAt 4))
      (SourceWordFutureBitGrowth.nextWordAt 3 before)
      (SourceWordFutureBitGrowth.nextWordAt 3 after) task),
    (fun before after task => SourceWordFieldCode.original_task_increment_zero_iff
      (inventoryBound (runtimeAt 4))
      (SourceWordFutureBitGrowth.nextWordAt 3 before)
      (SourceWordFutureBitGrowth.nextWordAt 3 after) task),
    (fun before after => SourceWordFieldCode.all_original_unit_increments_zero_iff
      (inventoryBound (runtimeAt 4))
      (SourceWordFutureBitGrowth.nextWordAt 3 before)
      (SourceWordFutureBitGrowth.nextWordAt 3 after)),
    (fun before after => SourceWordFieldCode.all_original_unit_increments_zero_iff_information_loss_zero
      (runtimeAt 4) (SourceWordFutureBitGrowth.nextWordAt 3 before)
      (SourceWordFutureBitGrowth.nextWordAt 3 after)),
    SourceWordFieldCode.actual_copy_information_strict,
    SourceWordFieldCode.actual_copy_l2_increment_strict,
    (fun task => SourceWordFieldCode.empty_tail_no_l2_increment 3 [] task),
    (fun before after decoder => SourceWordFieldCode.original_acted_g_risk_tower
      (runtimeAt 3) before after decoder),
    (fun before after decoder => SourceWordFieldCode.original_acted_g_risk_tower
      (runtimeAt 4) (SourceWordFutureBitGrowth.nextWordAt 3 before)
      (SourceWordFutureBitGrowth.nextWordAt 3 after) decoder),
    SourceWordFieldCode.actual_copy_clock_l2_increment,
    SourceWordFieldCode.actual_copy_clock_l2_increment_positive,
    (fun decoder => SourceWordFieldCode.actual_copy_original_g_risk_account decoder),
    (fun decoder => SourceWordFieldCode.actual_copy_original_g_risk_at_least_one decoder),
    (fun decoder => ⟨SourceWordFieldCode.actual_copy_g_risk_native_birth decoder,
      actual_birth_g_risk_at_least_four_fifths decoder⟩),
    SourceWordFieldCode.actual_copy_optimal_g_total_birth,
    SourceWordFieldCode.actual_copy_old_optimal_g_risk,
    SourceWordFieldCode.actual_copy_next_optimal_g_risk,
    SourceWordFieldCode.actual_copy_born_g_innovation_sq,
    SourceWordFieldCode.actual_copy_optimal_g_total_gain_positive,
    (fun decoder => SourceWordFieldCode.gBest_risk_le (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]) decoder),
    SourceWordFieldCode.gRisk_refinement (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4))
        (SourceWordFutureBitGrowth.nextWordAt 3 []))
      (SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 4) + 1)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])),
    SourceWordFieldCode.gGap_zero_iff_information_zero (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4))
        (SourceWordFutureBitGrowth.nextWordAt 3 []))
      (SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 4) + 1)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])),
    SourceWordFieldCode.actual_transported_copy_g_gap_positive,
    SourceWordFieldCode.actual_transported_copy_g_gap_exact,
    (fun word left right => SourceWordFutureBit.future_kernel (runtimeAt 3) word left right),
    (fun actor => SourceWordFutureBit.counted_future_posterior
      (runtimeAt 3) SourceWordObservedCode.actual_nonunit
      [SourceWordDynamicNext.copyOne] actor),
    SourceWordFutureBit.future_information (runtimeAt 3) [SourceWordDynamicNext.copyOne],
    (fun word decoder => SourceWordFutureBit.actual_future_half_risk word decoder),
    SourceWordFutureBit.actual_future_strictly_coarser_than_whole_model,
    SourceWordFutureBit.actual_copyOne_erases_future_bit,
    (fun word key => SourceWordFutureBitGrowth.old_new_counted_model 3
      SourceWordObservedCode.actual_nonunit word key),
    (fun word key => SourceWordFutureBitGrowth.old_next_model_eq_new_start 3
      SourceWordObservedCode.actual_nonunit word key),
    (fun word steps key supported => SourceWordFutureBitGrowth.counted_old_letter_posterior
      (runtimeAt 3) SourceWordObservedCode.actual_nonunit word steps key supported),
    SourceWordFutureBitGrowth.fresh_bit_action 3,
    SourceWordFutureBitGrowth.fresh_complete_action_is_source_step 3,
    SourceWordFutureBitGrowth.fresh_read_at_next_material 3,
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt 4)).factorizes,
    SourceWordFreshReceiver.fresh_read_all 3,
    SourceWordFreshReceiver.fresh_post_word_law 2,
    SourceWordFreshReceiver.fresh_post_word_law 3,
    SourceWordFreshReceiver.fresh_received 3 SourceWordObservedCode.actual_nonunit,
    SourceWordFreshReceiver.fresh_complete_posterior 3 SourceWordObservedCode.actual_nonunit,
    SourceWordFreshReceiver.fresh_next_model 3 SourceWordObservedCode.actual_nonunit,
    SourceWordFreshReceiver.fresh_original_G_full_account 3,
    SourceWordFreshReceiver.fresh_original_G_half_risk,
    SourceWordFreshReceiver.erased_posterior_at_two,
    SourceWordFreshReceiver.retained_complete_model_at_three,
    SourceWordFutureBitGrowth.next_runtime 2,
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt 2)).factorizes,
    SourceWordFixedErasure.read_all_zero,
    SourceWordFixedErasure.complete_history_at,
    SourceWordFixedErasure.next_model_is_full_history,
    SourceWordFixedErasure.next_readback_is_full_history,
    SourceWordFixedErasure.received_on_generated_stage,
    SourceWordFreshReceiver.fresh_original_G_full_account 2,
    (fun decoder => ⟨SourceWordObservedCode.observed_information_risk
      (runtimeAt 3) [SourceWordDynamicNext.copyOne] decoder,
      SourceWordObservedCode.actual_observed_half_risk [SourceWordDynamicNext.copyOne] decoder⟩),
    SourceWordObservedCode.received (runtimeAt 3) SourceWordObservedCode.actual_nonunit
      [SourceWordDynamicNext.copyOne],
    (fun key => SourceWordObservedCode.observed_mass_received (runtimeAt 3)
      SourceWordObservedCode.actual_nonunit [SourceWordDynamicNext.copyOne] key),
    (fun key supported => SourceWordObservedCode.counted_complete_posterior (runtimeAt 3)
      SourceWordObservedCode.actual_nonunit [SourceWordDynamicNext.copyOne] key supported),
    (fun steps key supported => SourceWordObservedCode.counted_complete_posterior_at
      (runtimeAt 3) SourceWordObservedCode.actual_nonunit
      [SourceWordDynamicNext.copyOne] steps key supported),
    (fun steps key => ⟨SourceWordObservedCode.counted_model (runtimeAt 3)
      SourceWordObservedCode.actual_nonunit [SourceWordDynamicNext.copyOne] steps key,
      SourceWordObservedCode.counted_next_model (runtimeAt 3)
        SourceWordObservedCode.actual_nonunit [SourceWordDynamicNext.copyOne] steps key⟩)⟩

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

theorem fine_word_recovery_consumed (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0) (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime)
          ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime)
      nonunit 0 * SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0
            ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) <
      SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat)
    (word : List (Fock.Letter (inventoryBound (runtime.advance steps) + 1)))
    (actor : Actors (runtime.advance steps)) :
    let advanced := runtime.advance steps
    let material := SourceGeneratedRuntimeMaterialStageAt.generate advanced
    CurrentAt runtime ∧
      HEq material.wholeLedgerWriteBack
        (advanced.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          advanced.current.visit.current) ∧
      material.next.current = material.activated.nextCurrent ∧
      type_of% (SourceWordPrecisionGeneric.word_singleton runtime nonunit
        keys inventory samples budgets steps word actor) := by
  dsimp only
  let advanced := runtime.advance steps
  let material := SourceGeneratedRuntimeMaterialStageAt.generate advanced
  exact ⟨current_consumed runtime, material.factorizes.2.2.1,
    material.factorizes.2.2.2,
    SourceWordPrecisionGeneric.word_singleton runtime nonunit
      keys inventory samples budgets steps word actor⟩

theorem fine_word_g_reader_consumed (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0) (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime)
          ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime)
      nonunit 0 * SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0
            ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) <
      SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat)
    (word : List (Fock.Letter (inventoryBound (runtime.advance steps) + 1)))
    (actor codeActor : Actors (runtime.advance steps))
    (candidate : NextModel (runtime.advance steps))
    (small : ‖SourceConditionalVector.realizeModel (runtime.advance steps) candidate -
      SourceConditionalVector.realizeModel (runtime.advance steps)
        (SourceCountedPosterior.model (runtime.advance steps)
          (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
          (SourceWordPrecisionGeneric.fineTable runtime nonunit keys samples steps)
          (clockRead 0 actor.val))‖ <
      SourcePosteriorStability.threshold (runtime.advance steps))
    (seen : codeActor ∈ SourcePosteriorStability.restoredSupport
      (runtime.advance steps) candidate) :
    let advanced := runtime.advance steps
    let material := SourceGeneratedRuntimeMaterialStageAt.generate advanced
    CurrentAt runtime ∧
      HEq material.wholeLedgerWriteBack
        (advanced.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          advanced.current.visit.current) ∧
      material.next.current = material.activated.nextCurrent ∧
      SourceWordMinimalCode.decode advanced word
          (SourceWordMinimalCode.wordEquiv advanced word codeActor) =
        SourceCompiledGWord.image advanced (inventoryBound advanced + 1) word actor := by
  dsimp only
  let advanced := runtime.advance steps
  let material := SourceGeneratedRuntimeMaterialStageAt.generate advanced
  exact ⟨current_consumed runtime, material.factorizes.2.2.1,
    material.factorizes.2.2.2,
    SourceWordPrecisionGeneric.word_g_reader runtime nonunit keys inventory samples
      budgets steps word actor codeActor candidate small seen⟩

theorem fine_word_budget_consumed (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0) (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime)
          ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime)
      nonunit 0 * SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0
            ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) <
      SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat) (actor : Actors (runtime.advance steps))
    (candidate : NextModel (runtime.advance steps)) :
    let advanced := runtime.advance steps
    let material := SourceGeneratedRuntimeMaterialStageAt.generate advanced
    CurrentAt runtime ∧
      HEq material.wholeLedgerWriteBack
        (advanced.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          advanced.current.visit.current) ∧
      material.next.current = material.activated.nextCurrent ∧
      type_of% (SourceWordPrecisionGeneric.posterior_weight_budget runtime nonunit
        keys inventory samples budgets steps actor candidate) := by
  dsimp only
  let advanced := runtime.advance steps
  let material := SourceGeneratedRuntimeMaterialStageAt.generate advanced
  exact ⟨current_consumed runtime, material.factorizes.2.2.1,
    material.factorizes.2.2.2,
    SourceWordPrecisionGeneric.posterior_weight_budget runtime nonunit
      keys inventory samples budgets steps actor candidate⟩

theorem word_code_information_consumed (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    {Code : Type*} [Fintype Code] [DecidableEq Code]
    [MeasurableSpace Code] [MeasurableSingletonClass Code]
    (encode : SourceWordMinimalCode.WordImage runtime word → Code)
    (decoder : Code → SourceJointClockGraph.Carrier) :
    let material := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    CurrentAt runtime ∧
      HEq material.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      material.next.current = material.activated.nextCurrent ∧
      type_of% (SourceWordCodeRisk.risk_account runtime word encode decoder) ∧
      type_of% (SourceWordCodeRisk.code_information_risk runtime word encode decoder) ∧
      ∀ _short : Fintype.card Code < inventoryBound runtime + 1,
        0 < SourceWordCodeRisk.risk runtime word encode decoder := by
  dsimp only
  let material := SourceGeneratedRuntimeMaterialStageAt.generate runtime
  exact ⟨current_consumed runtime, material.factorizes.2.2.1,
    material.factorizes.2.2.2,
    SourceWordCodeRisk.risk_account runtime word encode decoder,
    SourceWordCodeRisk.code_information_risk runtime word encode decoder,
    SourceWordCodeRisk.deficit_positive runtime word encode decoder⟩

theorem native_gap_account_consumed (runtime : LivingRuntimeState process) :
    let material := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    CurrentAt runtime ∧
      HEq material.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      material.next.current = material.activated.nextCurrent ∧
      type_of% (SourceWordNativeAlignment.native_gap_full_account runtime) := by
  dsimp only
  let material := SourceGeneratedRuntimeMaterialStageAt.generate runtime
  exact ⟨current_consumed runtime, material.factorizes.2.2.1,
    material.factorizes.2.2.2,
    SourceWordNativeAlignment.native_gap_full_account runtime⟩

theorem native_same_row_consumed (depth : Nat) :
    type_of% (SourceWordNativeAlignment.installed_root_entry_disposition depth) ∧
      type_of% (SourceWordNativeAlignment.same_write_observer depth) ∧
      type_of% (SourceWordNativeAlignment.installed_face depth) ∧
      type_of% (native_gap_account_consumed (runtimeAt depth)) :=
  ⟨SourceWordNativeAlignment.installed_root_entry_disposition depth,
    SourceWordNativeAlignment.same_write_observer depth,
    SourceWordNativeAlignment.installed_face depth,
    native_gap_account_consumed (runtimeAt depth)⟩

theorem acted_row_information_consumed (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    type_of% (SourceWordActedRow.post_word_row_law runtime word) ∧
      (∀ actor : Actors runtime,
        type_of% (SourceWordNativeAlignment.installed_root_entry_disposition actor.val) ∧
        type_of% (SourceWordNativeAlignment.installed_face actor.val)) ∧
      (∀ key : ZMod 2,
        ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map
          (fun actor : Actors runtime =>
            SourceWordObservedCode.observe
              (Fock.actualWord (inventoryBound runtime + 1) word
                (runtimePayload actor.val).nativeWrite.target))).support,
          type_of% (SourceWordActedRow.counted_row_posterior runtime nonunit word key supported)) ∧
      (∀ decoder : ZMod 2 → SourceJointClockGraph.Carrier,
        type_of% (SourceWordActedRow.row_information_risk runtime word decoder)) ∧
      (∀ state : Nat,
        type_of% (SourceWordActedRow.word_commutes_native_iff_unit_slope
          (inventoryBound runtime + 1) word state)) ∧
      (∀ steps : Nat, ∀ key : ZMod 2,
        type_of% (SourceWordObservedCode.counted_next_model runtime nonunit word steps key)) ∧
      type_of% ((SourceGeneratedRuntimeMaterialStageAt.generate runtime).factorizes) := by
  exact ⟨SourceWordActedRow.post_word_row_law runtime word,
    (fun actor => ⟨SourceWordNativeAlignment.installed_root_entry_disposition actor.val,
      SourceWordNativeAlignment.installed_face actor.val⟩),
    SourceWordActedRow.counted_row_posterior runtime nonunit word,
    SourceWordActedRow.row_information_risk runtime word,
    SourceWordActedRow.word_commutes_native_iff_unit_slope (inventoryBound runtime + 1) word,
    SourceWordObservedCode.counted_next_model runtime nonunit word,
    (SourceGeneratedRuntimeMaterialStageAt.generate runtime).factorizes⟩

theorem native_word_next_model_consumed (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0) (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime)
          ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime)
      nonunit 0 * SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0
            ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) <
      SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat) (key : ZMod 2) :
    let advanced := runtime.advance steps
    let material := SourceGeneratedRuntimeMaterialStageAt.generate advanced
    CurrentAt advanced ∧
      HEq material.wholeLedgerWriteBack
        (advanced.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          advanced.current.visit.current) ∧
      material.next.current = material.activated.nextCurrent ∧
      type_of% (SourceWordNativeAlignment.next_model_same_as_original_coarse
        runtime nonunit keys inventory samples budgets steps key) := by
  dsimp only
  let advanced := runtime.advance steps
  let material := SourceGeneratedRuntimeMaterialStageAt.generate advanced
  exact ⟨current_consumed advanced, material.factorizes.2.2.1,
    material.factorizes.2.2.2,
    SourceWordNativeAlignment.next_model_same_as_original_coarse
      runtime nonunit keys inventory samples budgets steps key⟩

end
end SourceCopyObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
