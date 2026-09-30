import H0mework.Fock.SourceHistory.CountedObservation.Material
import H0mework.Fock.RetainedCoarsening.Material
import H0mework.Fock.RetainedReceiver.Material
import H0mework.Fock.HistoryConditional.ReceivedKeyInventoryMaterial
import H0mework.Fock.HistoryConditional.ReceivedMergeMaterial
import H0mework.Fock.FibreExactState.Material
import H0mework.Fock.StableReceivedCount.Material
import H0mework.Fock.ReceivedStep.Material
import H0mework.Fock.RationalWindow.Material
import H0mework.Fock.FiniteObserver.Material
import H0mework.Fock.HistoryConditional.WindowPosteriorMaterial
import H0mework.Fock.HistoryConditional.WindowPrecisionMaterial
import H0mework.Fock.HistoryConditional.MinimumWindowErrorMaterial
import H0mework.Fock.HistoryConditional.MinimumSharedNext.Material
import H0mework.Fock.HistoryConditional.FiniteObservationMinimum.Material
import H0mework.Fock.HistoryConditional.OperatorAcquisition.Material
import H0mework.Fock.HistoryConditional.OperatorRecurrence.Material
import H0mework.Fock.SourceHistory.InverseObservationBirth.Material
import H0mework.Fock.SourceHistory.InverseObservationNative.Material
import H0mework.Fock.HistoryConditional.InverseObservationPacket.Material
import H0mework.Fock.HistoryConditional.InverseObservationHistory.Material
import H0mework.Fock.InverseDistribution.Stale.Material
import H0mework.Fock.InverseBirth.Material
import H0mework.Fock.InverseOptimal.Material
import H0mework.Fock.InverseDistribution.Loss.Material
import H0mework.Fock.InverseDistribution.Material
import H0mework.Fock.InverseDistribution.InverseDistribution.Material
import H0mework.Fock.HistoryConditional.NativeInverse.Material
import H0mework.Fock.HistoryConditional.Inverse.Material
import H0mework.Fock.HistoryConditional.GWordMaterial
import H0mework.Fock.HistoryConditional.WordOperator.Material
import H0mework.Fock.HistoryConditional.CopyWord.Material
import H0mework.Fock.HistoryConditional.CopyHistoryMaterial
import H0mework.Fock.HistoryConditional.Material
import H0mework.Fock.HistoryConditional.CopyBirthMaterial
import H0mework.Fock.HistoryConditional.NativeBirthConsumer
import H0mework.Fock.HistoryConditional.InformationLossConsumer
import H0mework.Fock.HistoryConditional.MergeLossConsumer
import H0mework.Fock.HistoryConditional.NativeMergeConsumer
import H0mework.Fock.HistoryConditional.NativePosteriorField
import H0mework.Fock.HistoryConditional.NativeObserversConsumer
import H0mework.Fock.HistoryConditional.NativeKeysConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeKeys

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceConditionalModel (Actors NextModel dynamicRead)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  (∀ depth : Nat, type_of% (generated_embed (inventoryBound runtime) depth) ∧ type_of% (table_current_next runtime depth) ∧
    type_of% (error_next runtime depth) ∧ type_of% (information_cost runtime depth) ∧
    (∀ key : ZMod 2, type_of% (key_count (inventoryBound runtime) depth key) ∧
      ∀ supported : observed depth key ∈ ((historyPMF (inventoryBound runtime)).map (SourceConditionalInventory.observation (inventoryBound runtime) depth)).support,
        ∀ actor : Actors runtime, type_of% (key_posterior (inventoryBound runtime) depth key supported actor)) ∧
    (∀ actor : Actors runtime, type_of% (source_observed (inventoryBound runtime) depth actor)) ∧
    (∀ value : Field parity, ∀ supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime depth)).support,
      type_of% (posterior runtime depth value supported) ∧ ∀ candidate : NextModel runtime,
        type_of% (support_restored runtime depth value supported candidate)) ∧
    (∀ key : ZMod 2, ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support,
      (∀ candidate : SourceJointClockGraph.Carrier, type_of% (SourceConditionalNativePosterior.field_error runtime depth key supported candidate)) ∧
      type_of% (SourceConditionalNativePosterior.field_residual runtime depth key supported)) ∧
    type_of% (SourceConditionalNativeMerge.state_original (inventoryBound runtime)) ∧
    type_of% (SourceConditionalNativeMerge.actual_update runtime) ∧
    type_of% (SourceConditionalNativeMerge.decoder_original runtime depth) ∧
    type_of% (SourceConditionalNativeMerge.compression_loss runtime depth) ∧
    type_of% (SourceConditionalNativeMerge.information_cost runtime depth) ∧
    type_of% (SourceConditionalNativeMerge.table_next runtime depth) ∧
    (∀ enough : 2 ≤ inventoryBound runtime, type_of% (SourceConditionalNativeMerge.compression_positive runtime enough depth)) ∧
    (∀ actor : Actors runtime, type_of% (SourceConditionalNativeMerge.full_source runtime actor)) ∧
    (∀ key : ZMod 2, ∀ supported : key ∈ (SourceConditionalHistory.observed
      (SourceConditionalHistory.observed (historyPMF (inventoryBound runtime)) (SourceConditionalModel.fullRead runtime)) SourceConditionalNativeMerge.forgetClock).support,
      ∀ actor : Actors runtime, type_of% (SourceConditionalNativeMerge.full_mixture runtime key supported actor)) ∧
    type_of% (SourceConditionalMergeLoss.parity_loss runtime depth) ∧
    (∀ enough : 2 ≤ inventoryBound runtime, type_of% (SourceConditionalMergeLoss.parity_strict runtime enough depth)) ∧
    type_of% (SourceConditionalMergeLoss.parity_update (inventoryBound runtime)) ∧
    type_of% (SourceConditionalMergeLoss.lossless_iff runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll) ∧
    type_of% (SourceConditionalMergeLoss.information_of_lossless runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll) ∧
    type_of% (SourceConditionalInformationLoss.parity_budget runtime depth) ∧
    (∀ enough : 1 ≤ inventoryBound runtime, type_of% (SourceConditionalInformationLoss.parity_amount_positive runtime enough)) ∧
    type_of% (SourceConditionalInformationLoss.amount_zero_iff_gap runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll) ∧
    type_of% (SourceConditionalInformationLoss.conditional_is_amount runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll) ∧
    type_of% (SourceConditionalInformationLoss.information_balance runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll) ∧
    type_of% (SourceConditionalInformationLoss.native_ratio runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll) ∧
    (∀ key : ZMod 2, type_of% (SourceConditionalNativeBirth.parity_model_update runtime depth key)) ∧
    type_of% (SourceConditionalNativeBirth.parity_stale runtime depth) ∧
    type_of% (SourceConditionalNativeBirth.stale_loss runtime (fun index : Nat => (index : ZMod 2))) ∧
    type_of% (SourceConditionalNativeBirth.minimum_update runtime (fun index : Nat => (index : ZMod 2))) ∧
    type_of% (SourceConditionalNativeBirth.gap_next runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll) ∧
    type_of% (SourceConditionalNativeBirth.amount_next runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll) ∧
    type_of% (SourceConditionalNativeBirth.next_budget runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll) ∧
    SourceConditionalCopyBirth.StageLaw runtime material ∧ SourceCopyNativeKeys.StageLaw runtime material ∧
    SourceCopyNativeHistory.StageLaw runtime material ∧ SourceCopyNativeWord.StageLaw runtime material ∧
    SourceCompiledWordOperator.StageLaw runtime material ∧ SourceCompiledGWord.StageLaw runtime material ∧
    SourceGWordInverse.StageLaw runtime material ∧ SourceNativeProgramInverse.StageLaw runtime material ∧
    SourceNativeInverseDistribution.StageLaw runtime material ∧ SourceInverseDistributionBirth.StageLaw runtime material ∧
    SourceInverseDistributionLoss.StageLaw runtime material ∧ SourceInverseDistributionOptimal.StageLaw runtime material ∧
    SourceInverseDistributionOptimalBirth.StageLaw runtime material ∧ SourceInverseDistributionStale.StageLaw runtime material ∧ SourceInverseObservationHistory.StageLaw runtime material ∧ SourceInverseObservationPacket.StageLaw runtime material ∧ SourceInverseObservationNative.StageLaw runtime material ∧ SourceInverseObservationBirth.StageLaw runtime material ∧ SourceOperatorObservationRecurrence.StageLaw runtime material ∧ SourceOperatorObservationAcquisition.StageLaw runtime material ∧ SourceFiniteObservationMinimum.StageLaw runtime material ∧ SourceMinimumSharedNext.StageLaw runtime material ∧ SourceMinimumWindowError.StageLaw runtime material ∧ SourceWindowPrecision.StageLaw runtime material ∧ SourceWindowPosterior.StageLaw runtime material ∧ SourceFiniteObserverCalculation.StageLaw runtime material ∧ SourceRationalWindowReadout.StageLaw runtime material ∧ SourceReceivedConditionalStep.StageLaw runtime material ∧ SourceStableReceivedCount.StageLaw runtime material ∧ SourceFibreExactState.StageLaw runtime material ∧ SourceReceivedConditionalMerge.StageLaw runtime material ∧ SourceReceivedKeyInventory.StageLaw runtime material ∧ SourceRetainedReceiver.StageLaw runtime material ∧ SourceRetainedCoarsening.StageLaw runtime material ∧ SourceCountedObservation.StageLaw runtime material) ∧
  (∀ actor : Actors runtime, type_of% (sample_factorizes runtimeSeed (inventoryBound runtime) actor)) ∧
  type_of% material.factorizes ∧
  type_of% (SourceConditionalNativeObservers.parity_generated (inventoryBound runtime)) ∧
  (∀ actor : Actors runtime,
    type_of% (SourceConditionalNativeObservers.full_source runtime actor) ∧
    type_of% (SourceConditionalNativeObservers.model_recovers runtime actor) ∧
    type_of% (SourceConditionalNativeObservers.decoder_recovers runtime actor) ∧
    ∀ candidate : Actors runtime, type_of% (SourceConditionalNativeObservers.clock_posterior runtime actor candidate)) ∧
  type_of% (SourceConditionalNativeObservers.error_zero runtime) ∧
  type_of% (SourceConditionalNativeObservers.state_next runtime) ∧
  ∀ actor : Actors runtime.tick.next, type_of% (SourceConditionalNativeObservers.next_recovers runtime actor)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨(fun depth => ⟨generated_embed (inventoryBound runtime) depth, table_current_next runtime depth,
    error_next runtime depth, information_cost runtime depth,
    (fun key => ⟨key_count (inventoryBound runtime) depth key, fun supported actor => key_posterior (inventoryBound runtime) depth key supported actor⟩),
    (fun actor => source_observed (inventoryBound runtime) depth actor),
    (fun value supported => ⟨posterior runtime depth value supported, fun candidate => support_restored runtime depth value supported candidate⟩),
    (fun key supported => ⟨(fun candidate => SourceConditionalNativePosterior.field_error runtime depth key supported candidate),
      SourceConditionalNativePosterior.field_residual runtime depth key supported⟩),
    SourceConditionalNativeMerge.state_original (inventoryBound runtime), SourceConditionalNativeMerge.actual_update runtime,
    SourceConditionalNativeMerge.decoder_original runtime depth, SourceConditionalNativeMerge.compression_loss runtime depth,
    SourceConditionalNativeMerge.information_cost runtime depth, SourceConditionalNativeMerge.table_next runtime depth,
    (fun enough => SourceConditionalNativeMerge.compression_positive runtime enough depth),
    (fun actor => SourceConditionalNativeMerge.full_source runtime actor),
    (fun key supported actor => SourceConditionalNativeMerge.full_mixture runtime key supported actor),
    SourceConditionalMergeLoss.parity_loss runtime depth,
    (fun enough => SourceConditionalMergeLoss.parity_strict runtime enough depth),
    SourceConditionalMergeLoss.parity_update (inventoryBound runtime),
    SourceConditionalMergeLoss.lossless_iff runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll,
    SourceConditionalMergeLoss.information_of_lossless runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll,
    SourceConditionalInformationLoss.parity_budget runtime depth,
    (fun enough => SourceConditionalInformationLoss.parity_amount_positive runtime enough),
    SourceConditionalInformationLoss.amount_zero_iff_gap runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll,
    SourceConditionalInformationLoss.conditional_is_amount runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll,
    SourceConditionalInformationLoss.information_balance runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll,
    SourceConditionalInformationLoss.native_ratio runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll,
    (fun key => SourceConditionalNativeBirth.parity_model_update runtime depth key),
    SourceConditionalNativeBirth.parity_stale runtime depth,
    SourceConditionalNativeBirth.stale_loss runtime (fun index : Nat => (index : ZMod 2)),
    SourceConditionalNativeBirth.minimum_update runtime (fun index : Nat => (index : ZMod 2)),
    SourceConditionalNativeBirth.gap_next runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll,
    SourceConditionalNativeBirth.amount_next runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll,
    SourceConditionalNativeBirth.next_budget runtime (fun index : Nat => (index : ZMod 2)) SourceConditionalMergeLoss.forgetAll,
    SourceConditionalCopyBirth.stage_law runtime material, SourceCopyNativeKeys.stage_law runtime material,
    SourceCopyNativeHistory.stage_law runtime material, SourceCopyNativeWord.stage_law runtime material,
    SourceCompiledWordOperator.stage_law runtime material, SourceCompiledGWord.stage_law runtime material,
    SourceGWordInverse.stage_law runtime material, SourceNativeProgramInverse.stage_law runtime material,
    SourceNativeInverseDistribution.stage_law runtime material, SourceInverseDistributionBirth.stage_law runtime material,
    SourceInverseDistributionLoss.stage_law runtime material, SourceInverseDistributionOptimal.stage_law runtime material,
    SourceInverseDistributionOptimalBirth.stage_law runtime material, SourceInverseDistributionStale.stage_law runtime material, SourceInverseObservationHistory.stage_law runtime material, SourceInverseObservationPacket.stage_law runtime material, SourceInverseObservationNative.stage_law runtime material, SourceInverseObservationBirth.stage_law runtime material, SourceOperatorObservationRecurrence.stage_law runtime material, SourceOperatorObservationAcquisition.stage_law runtime material, SourceFiniteObservationMinimum.stage_law runtime material, SourceMinimumSharedNext.stage_law runtime material, SourceMinimumWindowError.stage_law runtime material, SourceWindowPrecision.stage_law runtime material, SourceWindowPosterior.stage_law runtime material, SourceFiniteObserverCalculation.stage_law runtime material, SourceRationalWindowReadout.stage_law runtime material, SourceReceivedConditionalStep.stage_law runtime material, SourceStableReceivedCount.stage_law runtime material, SourceFibreExactState.stage_law runtime material, SourceReceivedConditionalMerge.stage_law runtime material, SourceReceivedKeyInventory.stage_law runtime material, SourceRetainedReceiver.stage_law runtime material, SourceRetainedCoarsening.stage_law runtime material, SourceCountedObservation.stage_law runtime material⟩),
    (fun actor => sample_factorizes runtimeSeed (inventoryBound runtime) actor), material.factorizes,
    SourceConditionalNativeObservers.parity_generated (inventoryBound runtime),
    (fun actor => ⟨SourceConditionalNativeObservers.full_source runtime actor,
      SourceConditionalNativeObservers.model_recovers runtime actor, SourceConditionalNativeObservers.decoder_recovers runtime actor,
      fun candidate => SourceConditionalNativeObservers.clock_posterior runtime actor candidate⟩),
    SourceConditionalNativeObservers.error_zero runtime, SourceConditionalNativeObservers.state_next runtime,
    fun actor => SourceConditionalNativeObservers.next_recovers runtime actor⟩

end
end SourceConditionalNativeKeys
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
