import H0mework.Versions.X.Fock.HistoryConditional.GWordConditional
import H0mework.Versions.X.Fock.HistoryConditional.NativeKeysConsumer
import H0mework.Versions.X.Fock.HistoryConditional.CopyHistoryRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledGWord

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceVectorMoment SourceWeightedRecovery
open SourceConditionalInventory (values)
open SourceConditionalModel (Actors dynamicRead dynamicInformation)
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem field_mean (runtime : LivingRuntimeState process) (observationDepth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime observationDepth)).support) :
    SourceConditionalNativeKeys.decoder runtime observationDepth value =
      mean (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (dynamicRead runtime observationDepth)
        value supported) (values (inventoryBound runtime)) := by
  rw [SourceConditionalNativeKeys.decoder_original, SourceConditionalRationalStream.decoder_original,
    SourceConditionalWordStream.decoder_original, SourceConditionalFiniteStream.generated_read,
    SourceConditionalStream.generated_source]
  exact SourceConditionalInnovation.decoder_mean (inventoryBound runtime) observationDepth value supported

theorem field_error_account (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (observationDepth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) :
    (∑ i, (historyPMF (inventoryBound runtime) i).toReal *
      ‖image runtime depth word i - decoder (dynamicRead runtime observationDepth i)‖ ^ 2) =
      SourceConditionalInventory.cost (inventoryBound runtime) (dynamicRead runtime observationDepth) / (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ‖residual (historyPMF (inventoryBound runtime)) (dynamicRead runtime observationDepth)
          (taskValue (historyPMF (inventoryBound runtime)) (SourceJointClockGraph.clock ∘ values (inventoryBound runtime)))‖ ^ 2 +
      ∑ i, (historyPMF (inventoryBound runtime) i).toReal *
        ‖effect depth word (SourceConditionalNativeKeys.decoder runtime observationDepth (dynamicRead runtime observationDepth i)) -
          decoder (dynamicRead runtime observationDepth i)‖ ^ 2 := by
  rw [error_account]
  simp only [field_mean _ _ _ (observed_supported _ _ _ (SourceUniformFibreVariance.source_positive (inventoryBound runtime) _))]

theorem field_optimal (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (observationDepth : Nat) :
    (∑ i, (historyPMF (inventoryBound runtime) i).toReal *
      ‖image runtime depth word i - effect depth word
        (SourceConditionalNativeKeys.decoder runtime observationDepth (dynamicRead runtime observationDepth i))‖ ^ 2) =
      SourceConditionalInventory.cost (inventoryBound runtime) (dynamicRead runtime observationDepth) / (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ‖residual (historyPMF (inventoryBound runtime)) (dynamicRead runtime observationDepth)
          (taskValue (historyPMF (inventoryBound runtime)) (SourceJointClockGraph.clock ∘ values (inventoryBound runtime)))‖ ^ 2 := by
  have paid := field_error_account runtime depth word observationDepth
    (effect depth word ∘ SourceConditionalNativeKeys.decoder runtime observationDepth)
  simpa only [Function.comp_apply, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero, add_zero] using paid

theorem field_information (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (observationDepth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) :
    SourceConditionalInventory.cost (inventoryBound runtime) (dynamicRead runtime observationDepth) / (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ((Real.exp (2 * dynamicInformation runtime observationDepth) - 1) / 12) ≤
      ∑ i, (historyPMF (inventoryBound runtime) i).toReal *
        ‖image runtime depth word i - decoder (dynamicRead runtime observationDepth i)‖ ^ 2 := by
  rw [SourceInformationReadback.dynamic_information]
  exact information_lower runtime depth word (dynamicRead runtime observationDepth) decoder

theorem field_amplification (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (observationDepth : Nat) :
    (∑ i, (historyPMF (inventoryBound runtime) i).toReal *
      ‖image runtime depth word i - effect depth word
        (SourceConditionalNativeKeys.decoder runtime observationDepth (dynamicRead runtime observationDepth i))‖ ^ 2) =
      SourceConditionalVector.dynamicError runtime observationDepth (SourceConditionalNativeKeys.decoder runtime observationDepth) +
      (((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 - 1) *
        ‖residual (historyPMF (inventoryBound runtime)) (dynamicRead runtime observationDepth)
          (taskValue (historyPMF (inventoryBound runtime)) (SourceJointClockGraph.clock ∘ values (inventoryBound runtime)))‖ ^ 2 := by
  have baseline := field_optimal runtime depth [] observationDepth
  rw [image_original, effect_nil] at baseline
  change (∑ i, (historyPMF (inventoryBound runtime) i).toReal *
    ‖values (inventoryBound runtime) i - SourceConditionalNativeKeys.decoder runtime observationDepth (dynamicRead runtime observationDepth i)‖ ^ 2) = _ at baseline
  simp only [SourceConditionalInventory.values_original] at baseline
  change SourceConditionalVector.dynamicError runtime observationDepth (SourceConditionalNativeKeys.decoder runtime observationDepth) = _ at baseline
  rw [field_optimal, baseline]
  norm_num [SourceCopyWordAffine.compile, SourceCopyNativeWord.encode]
  ring

theorem no_free_clock (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime)
    (depth : Nat) (word : List (Fock.Letter depth))
    (slope : 1 < (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1)
    (observationDepth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) :
    SourceConditionalVector.dynamicError runtime observationDepth (SourceConditionalNativeKeys.decoder runtime observationDepth) <
      ∑ i, (historyPMF (inventoryBound runtime) i).toReal *
        ‖image runtime depth word i - decoder (dynamicRead runtime observationDepth i)‖ ^ 2 := by
  have exponential := SourceInformationReadback.dynamic_exponential_lower runtime observationDepth
  have clockLower := SourceGInformationCost.clock_information_lower (inventoryBound runtime) (dynamicRead runtime observationDepth)
  rw [← SourceInformationReadback.dynamic_information] at clockLower
  have size : (2 : ℝ) ≤ (inventoryBound runtime : ℝ) := by exact_mod_cast enough
  have clockPositive : 0 < ‖residual (historyPMF (inventoryBound runtime)) (dynamicRead runtime observationDepth)
    (taskValue (historyPMF (inventoryBound runtime)) (SourceJointClockGraph.clock ∘ values (inventoryBound runtime)))‖ ^ 2 := by
    nlinarith
  have slopeReal : (1 : ℝ) < ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) := by
    exact_mod_cast slope
  have higher := field_amplification runtime depth word observationDepth
  have strict : SourceConditionalVector.dynamicError runtime observationDepth (SourceConditionalNativeKeys.decoder runtime observationDepth) <
    ∑ i, (historyPMF (inventoryBound runtime) i).toReal *
      ‖image runtime depth word i - effect depth word
        (SourceConditionalNativeKeys.decoder runtime observationDepth (dynamicRead runtime observationDepth i))‖ ^ 2 := by
    rw [higher]
    exact lt_add_of_pos_right _ (mul_pos (by nlinarith) clockPositive)
  rw [field_optimal] at strict
  rw [field_error_account]
  exact strict.trans_le (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)))

theorem history_recovers (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (actor : Actors runtime) :
    effect depth word (SourceConditionalNativePosterior.decoder runtime (SourceCopyNativeHistory.read (inventoryBound runtime))
      (SourceCopyNativeHistory.read (inventoryBound runtime) actor.val)) = image runtime depth word actor := by
  rw [SourceCopyNativeHistory.decoder_recovers, image_original]
  rfl

end
end SourceCompiledGWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
