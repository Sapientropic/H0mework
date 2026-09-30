import H0mework.Versions.X.Fock.HistoryModel.SourceWord.Action

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordDynamicNext

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation SourceConditionalModel
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

variable {Observed : Type*} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

/-- The original acted-word mass pays the existing physical GWord conditional error account. -/
theorem source_word_g_error_account (runtime : LivingRuntimeState process)
    (word : List (SourceGeneratedActionWords.Fock.Letter (inventoryBound runtime + 1)))
    (query : Actors runtime → Observed)
    (decoder : Observed → SourceJointClockGraph.Carrier) :
    (∑ actor : Actors runtime,
      (((((SourceGeneratedActionWords.Fock.sourceLaw (inventoryBound runtime)).map nativeStep).map
        (SourceGeneratedActionWords.Fock.actualWord (inventoryBound runtime + 1) word)).map
          (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)))
            (SourceGeneratedActionWords.run
              (SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1)) word
              (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
                (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.current.visit.current : Current)))).toReal *
        ‖SourceJointClockGraph.read (SourceClockComplex.ofNative
            (SourceOperationNative.statePoint process
              (SourceCopyNativeWord.run (word.map SourceCopyNativeWord.encode)
                (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.state)))) -
          decoder (query actor)‖ ^ 2) =
      SourceConditionalInventory.cost (inventoryBound runtime) query / (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ‖SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime)) query
          (SourceWeightedRecovery.taskValue (historyPMF (inventoryBound runtime))
            (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values (inventoryBound runtime)))‖ ^ 2 +
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceCompiledGWord.effect (inventoryBound runtime + 1) word
          (SourceVectorMoment.mean
            (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query (query actor)
              (SourceWeightedRecovery.observed_supported _ _ actor
                (SourceUniformFibreVariance.source_positive (inventoryBound runtime) actor)))
            (SourceConditionalInventory.values (inventoryBound runtime))) - decoder (query actor)‖ ^ 2 := by
  have paid := SourceCompiledGWord.error_account runtime (inventoryBound runtime + 1)
    word query decoder
  calc
    _ = ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceCompiledGWord.image runtime (inventoryBound runtime + 1) word actor - decoder (query actor)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro actor _
      rw [source_word_mass runtime word actor, actor_word_g runtime word actor]
    _ = _ := paid

/-- An actual coarse Field observer has strictly larger source-word-weighted G error. -/
theorem source_word_no_free_clock (runtime : LivingRuntimeState process)
    (enough : 2 ≤ inventoryBound runtime)
    (word : List (SourceGeneratedActionWords.Fock.Letter (inventoryBound runtime + 1)))
    (slope : 1 < (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1)
    (observationDepth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) :
    SourceConditionalVector.dynamicError runtime observationDepth
      (SourceConditionalNativeKeys.decoder runtime observationDepth) <
    ∑ actor : Actors runtime,
      (((((SourceGeneratedActionWords.Fock.sourceLaw (inventoryBound runtime)).map nativeStep).map
        (SourceGeneratedActionWords.Fock.actualWord (inventoryBound runtime + 1) word)).map
          (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)))
            (SourceGeneratedActionWords.run
              (SourceGeneratedActionWords.Fock.letterAction (inventoryBound runtime + 1)) word
              (SourceGeneratedActionWords.Fock.point (inventoryBound runtime + 1)
                (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.current.visit.current : Current)))).toReal *
        ‖SourceJointClockGraph.read (SourceClockComplex.ofNative
            (SourceOperationNative.statePoint process
              (SourceCopyNativeWord.run (word.map SourceCopyNativeWord.encode)
                (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.state)))) -
          decoder (SourceConditionalModel.dynamicRead runtime observationDepth actor)‖ ^ 2 := by
  have paid := SourceCompiledGWord.no_free_clock runtime enough (inventoryBound runtime + 1)
    word slope observationDepth decoder
  calc
    _ < ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
      ‖SourceCompiledGWord.image runtime (inventoryBound runtime + 1) word actor -
        decoder (SourceConditionalModel.dynamicRead runtime observationDepth actor)‖ ^ 2 := paid
    _ = _ := by
      apply Finset.sum_congr rfl
      intro actor _
      rw [source_word_mass runtime word actor, actor_word_g runtime word actor]

/-- A real inventory copy letter, with no caller-provided slope certificate. -/
def copyOne : SourceGeneratedActionWords.Fock.Letter (inventoryBound (runtimeAt 3) + 1) :=
  .inr ⟨1, by
    rw [SourceOwnedObservationHistory.Installed.runtime_bound,
      inventory_bound, runtimeAt_state]
    decide⟩

theorem copyOne_slope :
    1 < (SourceCopyWordAffine.compile ([copyOne].map SourceCopyNativeWord.encode)).1 := by
  decide

theorem actual_copy_word_coarse_strict (observationDepth : Nat)
    (decoder : Field parity → SourceJointClockGraph.Carrier) :
    SourceConditionalVector.dynamicError (runtimeAt 3) observationDepth
      (SourceConditionalNativeKeys.decoder (runtimeAt 3) observationDepth) <
    ∑ actor : Actors (runtimeAt 3),
      (((((SourceGeneratedActionWords.Fock.sourceLaw (inventoryBound (runtimeAt 3))).map nativeStep).map
        (SourceGeneratedActionWords.Fock.actualWord (inventoryBound (runtimeAt 3) + 1) [copyOne])).map
          (SourceGeneratedActionWords.Fock.point (inventoryBound (runtimeAt 3) + 1)))
            (SourceGeneratedActionWords.run
              (SourceGeneratedActionWords.Fock.letterAction (inventoryBound (runtimeAt 3) + 1)) [copyOne]
              (SourceGeneratedActionWords.Fock.point (inventoryBound (runtimeAt 3) + 1)
                (((history runtimeSeed (inventoryBound (runtimeAt 3))).stageAt actor).next.current.visit.current : Current)))).toReal *
        ‖SourceJointClockGraph.read (SourceClockComplex.ofNative
            (SourceOperationNative.statePoint process
              (SourceCopyNativeWord.run ([copyOne].map SourceCopyNativeWord.encode)
                (((history runtimeSeed (inventoryBound (runtimeAt 3))).stageAt actor).next.state)))) -
          decoder (SourceConditionalModel.dynamicRead (runtimeAt 3) observationDepth actor)‖ ^ 2 := by
  apply source_word_no_free_clock (runtimeAt 3)
  · rw [inventory_bound, runtimeAt_state]
    decide
  · exact copyOne_slope

end
end SourceWordDynamicNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
