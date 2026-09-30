import H0mework.Versions.X.Fock.HistoryModel.OriginalHilbertActor
import H0mework.Probability.Recovery.Conditional

/-! The original time adjoint reads the full conditional law of the same actual actor history. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert.Actor

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed MeasureTheory
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open SourceGeneratedActionObservationHistory SourceGeneratedScalarCofinalTopology

noncomputable section

private theorem transfer_pushforward {Source Observed : Type*} [Fintype Source]
    [MeasurableSpace Source] [MeasurableSingletonClass Source]
    [MeasurableSpace Observed] [MeasurableSingletonClass Observed]
    (source : PMF Source) (reader : Source → Observed) (target : PMF Observed)
    (same : target = observed source reader)
    (preserved : MeasurePreserving reader source.toMeasure target.toMeasure)
    (task : Source → ℂ) (atom : Observed) :
    IsometricRetainedTransfer.transfer (Lp.compMeasurePreservingₗᵢ ℂ reader preserved)
        (taskValue source task) atom = optimalDecoder source reader task atom := by
  subst target
  rfl

local instance conditionalFieldUniform (depth : Nat) : UniformSpace (Field nativeStep (rawWords depth)) :=
  fieldUniform nativeStep (rawWords depth)
local instance conditionalFieldMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)
local instance conditionalFieldBorel (depth : Nat) : BorelSpace (Field nativeStep (rawWords depth)) := ⟨rfl⟩
local instance conditionalFieldT2 (depth : Nat) : T2Space (Field nativeStep (rawWords depth)) := by
  let tower := data (sourceAction nativeStep) (observation (rawWords depth))
  let laws := compatible (sourceAction nativeStep) (observation (rawWords depth))
  let : ∀ stage, UniformSpace (tower.StageQuotient stage) := stageUniform tower
  exact (coordinates_isUniformEmbedding tower laws).isEmbedding.t2Space

theorem completeTransfer_is_conditional (depth bound : Nat) (task : Fin (bound + 1) → ℂ)
    (atom : Field nativeStep (rawWords depth)) :
    IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
        (currentTransfer depth bound (taskValue (historyPMF bound) task)) atom =
      optimalDecoder (historyPMF bound) (nextRead depth bound) task atom := by
  have composition := IsometricRetainedTransfer.transfer_comp (currentPullback depth bound)
    (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
  have source := congrArg IsometricRetainedTransfer.transfer (nextPullback_is_source_map depth bound)
  have readback := congrArg (fun operation : SourceWeightedRecovery.Space (historyPMF bound) →L[ℂ]
      SourceOwnedObservationHistory.Space nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound =>
        operation (taskValue (historyPMF bound) task) atom) (composition.symm.trans source)
  exact readback.trans (transfer_pushforward (historyPMF bound) (nextRead depth bound)
    (fieldPMF nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound)
    (next_pmf depth bound).symm (next_preserving depth bound) task atom)

theorem complete_conditional_formula (depth bound : Nat) (task : Fin (bound + 1) → ℂ)
    (atom : Field nativeStep (rawWords depth))
    (supported : atom ∈ (observed (historyPMF bound) (nextRead depth bound)).support) :
    IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
        (currentTransfer depth bound (taskValue (historyPMF bound) task)) atom =
      ∑ index : Fin (bound + 1),
        (SourceConditionalHistory.conditional (historyPMF bound) (nextRead depth bound) atom supported index).toReal • task index :=
  (completeTransfer_is_conditional depth bound task atom).trans
    (optimal_is_conditional (historyPMF bound) (nextRead depth bound) task atom supported)

theorem currentTransfer_samples (depth bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) :
    currentTransfer depth bound (taskValue (historyPMF bound) (fun index => value (originalRead depth bound index))) = value := by
  have samples : currentPullback depth bound value =
      taskValue (historyPMF bound) (fun index => value (originalRead depth bound index)) := by
    apply Lp.ext
    apply Filter.Eventually.of_forall
    intro index
    exact (currentPullback_at depth bound value index).trans
      (taskValue_at (historyPMF bound) (fun point => value (originalRead depth bound point))
        index (by simp [historyPMF])).symm
  rw [← samples]
  exact IsometricRetainedTransfer.transfer_pullback (currentPullback depth bound) value

theorem original_transfer_formula (depth bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
    (atom : Field nativeStep (rawWords depth))
    (supported : atom ∈ (observed (historyPMF bound) (nextRead depth bound)).support) :
    IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
        value atom =
      ∑ index : Fin (bound + 1),
        (SourceConditionalHistory.conditional (historyPMF bound) (nextRead depth bound) atom supported index).toReal •
          value (originalRead depth bound index) := by
  have complete := complete_conditional_formula depth bound
    (fun index => value (originalRead depth bound index)) atom supported
  rw [currentTransfer_samples] at complete
  exact complete

end
end SourceGeneratedActionWords.Fock.OriginalHilbert.Actor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
