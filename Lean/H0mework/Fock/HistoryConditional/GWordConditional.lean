import H0mework.Fock.HistoryConditional.GWordMoment
import H0mework.Fock.HistoryConditional.GCostInformation
import H0mework.Fock.HistoryConditional.NativePosteriorEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledGWord

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceVectorMoment SourceWeightedRecovery
open SourceConditionalInventory (values)
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def image (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (actor : Actors runtime) : SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.action depth word
    (SourceOperationNative.point ((history runtimeSeed (inventoryBound runtime)).stageAt actor).next)))

theorem image_original (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) :
    image runtime depth word = effect depth word ∘ values (inventoryBound runtime) := by
  funext actor
  exact (source_effect depth word _).symm

theorem conditional_decoder {Key : Type*} [DecidableEq Key]
    (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    mean (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
      (fun actor : Actors runtime => read actor.val) key supported) (image runtime depth word) =
        effect depth word (SourceConditionalNativePosterior.decoder runtime read key) := by
  rw [image_original, mean_effect, SourceConditionalNativePosterior.decoder_mean _ _ _ supported]
  exact congrArg (effect depth word) (congrArg (SourceVectorMoment.mean _) (funext (SourceConditionalInventory.values_original runtime)))

variable {Observed : Type*} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem total_variance (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (query : Actors runtime → Observed) :
    (∑ i, (historyPMF (inventoryBound runtime) i).toReal * variance
      (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query (query i)
        (observed_supported _ _ i (SourceUniformFibreVariance.source_positive (inventoryBound runtime) i))) (image runtime depth word)) =
      SourceConditionalInventory.cost (inventoryBound runtime) query / (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ‖residual (historyPMF (inventoryBound runtime)) query
          (taskValue (historyPMF (inventoryBound runtime)) (SourceJointClockGraph.clock ∘ values (inventoryBound runtime)))‖ ^ 2 := by
  simp only [image_original, constant_mass_variance _ depth word _ 1 (SourceGInformationCost.actual_mass (inventoryBound runtime)),
    mul_add, Finset.sum_add_distrib]
  rw [show (∑ i, (historyPMF (inventoryBound runtime) i).toReal * variance
    (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query (query i)
      (observed_supported _ _ i (SourceUniformFibreVariance.source_positive (inventoryBound runtime) i))) (values (inventoryBound runtime))) =
        SourceGInformationCost.totalVariance (inventoryBound runtime) query from rfl]
  simp_rw [mul_left_comm (a := (historyPMF (inventoryBound runtime) _).toReal)]
  have scalar : (∑ i, (historyPMF (inventoryBound runtime) i).toReal * variance
    (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query (query i)
      (observed_supported _ _ i (SourceUniformFibreVariance.source_positive (inventoryBound runtime) i)))
        (SourceJointClockGraph.clock ∘ values (inventoryBound runtime))) =
      ‖residual (historyPMF (inventoryBound runtime)) query
        (taskValue (historyPMF (inventoryBound runtime)) (SourceJointClockGraph.clock ∘ values (inventoryBound runtime)))‖ ^ 2 :=
    SourceGInformationCost.scalar_variance _ query SourceJointClockGraph.clock.toLinearMap
  rw [← Finset.mul_sum, scalar, SourceGInformationCost.full_variance_cost]
  ring

theorem error_account (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (query : Actors runtime → Observed) (decoder : Observed → SourceJointClockGraph.Carrier) :
    (∑ i, (historyPMF (inventoryBound runtime) i).toReal * ‖image runtime depth word i - decoder (query i)‖ ^ 2) =
      SourceConditionalInventory.cost (inventoryBound runtime) query / (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ‖residual (historyPMF (inventoryBound runtime)) query
          (taskValue (historyPMF (inventoryBound runtime)) (SourceJointClockGraph.clock ∘ values (inventoryBound runtime)))‖ ^ 2 +
      ∑ i, (historyPMF (inventoryBound runtime) i).toReal *
        ‖effect depth word (mean (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query (query i)
          (observed_supported _ _ i (SourceUniformFibreVariance.source_positive (inventoryBound runtime) i)))
            (values (inventoryBound runtime))) - decoder (query i)‖ ^ 2 := by
  rw [conditional_error _ query (SourceUniformFibreVariance.source_positive (inventoryBound runtime)), total_variance]
  simp only [image_original, mean_effect]

theorem information_lower [DecidableEq Observed]
    (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (query : Actors runtime → Observed) (decoder : Observed → SourceJointClockGraph.Carrier) :
    SourceConditionalInventory.cost (inventoryBound runtime) query / (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ((Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy (inventoryBound runtime) query) - 1) / 12) ≤
      ∑ i, (historyPMF (inventoryBound runtime) i).toReal * ‖image runtime depth word i - decoder (query i)‖ ^ 2 := by
  rw [error_account]
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left (SourceGInformationCost.clock_information_lower _ query) (sq_nonneg _))).trans
    (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)))

end
end SourceCompiledGWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
