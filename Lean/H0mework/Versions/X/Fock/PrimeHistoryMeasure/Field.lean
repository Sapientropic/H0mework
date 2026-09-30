import H0mework.Probability.HistoryGrowth.Geometry
import H0mework.Versions.X.Fock.PrimeFieldCalculation.ContinuationConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAcquisitionMeasure

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed MeasureTheory
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance measureFieldUniform (depth : Nat) : UniformSpace (Field nativeStep (rawWords depth)) :=
  fieldUniform nativeStep (rawWords depth)
local instance measureFieldMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)
local instance measureFieldBorel (depth : Nat) : BorelSpace (Field nativeStep (rawWords depth)) := ⟨rfl⟩
local instance measureFieldT2 (depth : Nat) : T2Space (Field nativeStep (rawWords depth)) :=
  Actor.conditionalFieldT2 depth

abbrev FieldSpace (depth bound : Nat) :=
  SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound

theorem actor_transfer_samples (depth bound : Nat) (value : SourceWeightedRecovery.Space (historyPMF bound)) :
    Actor.currentPullback depth bound (Actor.currentTransfer depth bound value) = value := by
  have complete : taskValue (historyPMF bound) (fun index => value index) = value := by
    apply Lp.ext
    exact Filter.Eventually.of_forall fun index => taskValue_at (historyPMF bound) _ index
      (SourceUniformFibreVariance.source_positive bound index)
  rw [← complete]
  apply Lp.ext
  apply Filter.Eventually.of_forall
  intro index
  let lifted := Actor.currentTransfer depth bound (taskValue (historyPMF bound) (fun index => value index))
  have query := congrArg (fun point => IsometricRetainedTransfer.transfer
    (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
      lifted point) (Recorded.whole_recorded depth bound index)
  change SourceGeneratedAtomicObservation.Recorded.query depth bound index lifted = _ at query
  calc
    _ = lifted (Actor.originalRead depth bound index) := Actor.currentPullback_at depth bound lifted index
    _ = SourceGeneratedAtomicObservation.Recorded.query depth bound index lifted :=
      (SourceGeneratedRecordFrame.query_sample depth bound index lifted).symm
    _ = value index := query.trans (original_next_recovery depth bound (fun index => value index) index)
    _ = _ := (taskValue_at (historyPMF bound) _ index (SourceUniformFibreVariance.source_positive bound index)).symm

theorem actor_transfer_norm (depth bound : Nat) (value : SourceWeightedRecovery.Space (historyPMF bound)) :
    ‖Actor.currentTransfer depth bound value‖ = ‖value‖ := by
  rw [← (Actor.currentPullback depth bound).norm_map, actor_transfer_samples]

variable (depth : Nat) {old fresh : Nat} (retained : old ≤ fresh)

def extend : FieldSpace depth old →L[ℂ] FieldSpace depth fresh :=
  (Actor.currentTransfer depth fresh).comp ((SourceHistoryGrowth.extend retained).comp
    (Actor.currentPullback depth old).toContinuousLinearMap)

def restrict : FieldSpace depth fresh →L[ℂ] FieldSpace depth old :=
  (Actor.currentTransfer depth old).comp ((SourceHistoryGrowth.restrict retained).comp
    (Actor.currentPullback depth fresh).toContinuousLinearMap)

def remainder : FieldSpace depth fresh →L[ℂ] FieldSpace depth fresh :=
  (Actor.currentTransfer depth fresh).comp ((SourceHistoryGrowth.remainder retained).comp
    (Actor.currentPullback depth fresh).toContinuousLinearMap)

theorem extend_samples (value : FieldSpace depth old) :
    Actor.currentPullback depth fresh (extend depth retained value) =
      SourceHistoryGrowth.extend retained (Actor.currentPullback depth old value) :=
  actor_transfer_samples depth fresh _

theorem restrict_samples (value : FieldSpace depth fresh) :
    Actor.currentPullback depth old (restrict depth retained value) =
      SourceHistoryGrowth.restrict retained (Actor.currentPullback depth fresh value) :=
  actor_transfer_samples depth old _

theorem remainder_samples (value : FieldSpace depth fresh) :
    Actor.currentPullback depth fresh (remainder depth retained value) =
      SourceHistoryGrowth.remainder retained (Actor.currentPullback depth fresh value) :=
  actor_transfer_samples depth fresh _

end
end SourceGeneratedAcquisitionMeasure
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
