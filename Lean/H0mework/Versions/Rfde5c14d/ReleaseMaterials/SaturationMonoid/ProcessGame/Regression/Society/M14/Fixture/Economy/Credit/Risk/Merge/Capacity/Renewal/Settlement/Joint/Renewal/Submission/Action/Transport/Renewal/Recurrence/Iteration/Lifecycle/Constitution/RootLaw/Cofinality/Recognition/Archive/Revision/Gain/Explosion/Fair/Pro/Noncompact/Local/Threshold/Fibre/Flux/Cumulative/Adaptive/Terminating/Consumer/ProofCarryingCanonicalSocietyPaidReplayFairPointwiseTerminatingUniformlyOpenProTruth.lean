import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Consumer.ProofCarryingCanonicalSocietyPaidReplayFairFiniteAdaptiveNoncompactProTruth
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.Search.Source.SourceGeneratedCanonicalSocietyPaidReplayFairPointwiseTerminatingRecognition

/-!
# Proof-carrying pointwise termination with uniform openness

The same fair source now carries the exact boundary: a single archive-only
successor rule terminates on every replay and faithfully recovers occurrence/K,
but no finite fuel works for the whole source family.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyPaidReplayFairPointwiseTerminatingUniformlyOpenProTruth

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteAdaptiveNoncompactProTruth
open M14SourceGeneratedCanonicalSocietyPaidReplayFairObservedCode
open M14SourceGeneratedCanonicalSocietyPaidReplayFairPointwiseTerminatingRecognition

/-- Maximum exact-boundary mouth: negative uniform-fuel noncompactness and
positive source-relative termination are consumed together. -/
theorem canonicalPaidReplayFairPointwiseTerminatingUniformlyOpenProTruth_directConsumer
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    type_of%
        (canonicalPaidReplayFairFiniteAdaptiveNoncompactProTruth_directConsumer
          oldVisit sourceIndex) ∧
      (∀ stage
        (replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex),
        type_of%
            (canonicalPaidReplayFairObservedCode_readout_exact oldVisit
              sourceIndex stage replay) ∧
          type_of%
            (canonicalPaidReplayFairObservedCode_eq_none_iff oldVisit
              sourceIndex stage replay) ∧
          (∀ hot : Fin stage,
            type_of%
              (canonicalPaidReplayFairObservedCode_eq_some_iff oldVisit
                sourceIndex stage replay hot)) ∧
          type_of%
            (canonicalPaidReplayFairObservedInstruction_continue_iff oldVisit
              sourceIndex stage replay)) ∧
      (∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
        Nonempty
          (SourceGeneratedCanonicalPaidReplayFairTerminatingRecognitionAt
            oldVisit sourceIndex replay)) ∧
      (∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
        type_of%
          (canonicalPaidReplayFairTerminatingRecognition_directConsumer
            oldVisit sourceIndex replay)) ∧
      Function.Injective
        (canonicalPaidReplayFairTerminatingRecognizedOccurrence oldVisit
          sourceIndex) ∧
      type_of%
        (canonicalPaidReplayFairRecognition_hasNoUniformFiniteBound oldVisit
          sourceIndex) ∧
      type_of%
        (canonicalPaidReplayFairPointwiseRecognizer_noUniformFiniteHotBound
          oldVisit sourceIndex) ∧
      (∀ fuel,
        type_of%
          (canonicalPaidReplayFairRecognitionBound_generatesCounterexample
            oldVisit sourceIndex fuel)) ∧
      (∀ bound,
        type_of%
          (canonicalPaidReplayFairEveryBound_generatesStillOpenReplay oldVisit
            sourceIndex bound)) := by
  exact
    ⟨canonicalPaidReplayFairFiniteAdaptiveNoncompactProTruth_directConsumer
        oldVisit sourceIndex,
      fun stage replay =>
        ⟨canonicalPaidReplayFairObservedCode_readout_exact oldVisit sourceIndex
            stage replay,
          canonicalPaidReplayFairObservedCode_eq_none_iff oldVisit sourceIndex
            stage replay,
          canonicalPaidReplayFairObservedCode_eq_some_iff oldVisit sourceIndex
            stage replay,
          canonicalPaidReplayFairObservedInstruction_continue_iff oldVisit
            sourceIndex stage replay⟩,
      fun replay =>
        ⟨sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
          sourceIndex replay⟩,
      canonicalPaidReplayFairTerminatingRecognition_directConsumer oldVisit
        sourceIndex,
      canonicalPaidReplayFairTerminatingRecognizer_injective oldVisit
        sourceIndex,
      canonicalPaidReplayFairRecognition_hasNoUniformFiniteBound oldVisit
        sourceIndex,
      canonicalPaidReplayFairPointwiseRecognizer_noUniformFiniteHotBound
        oldVisit sourceIndex,
      canonicalPaidReplayFairRecognitionBound_generatesCounterexample oldVisit
        sourceIndex,
      canonicalPaidReplayFairEveryBound_generatesStillOpenReplay oldVisit
        sourceIndex⟩

/-- The existing constitutional point consumes the exact positive/negative
recognition boundary without adding a search runtime or future archive. -/
theorem canonicalCofinalPaidReplayFairPointwiseTerminatingUniformlyOpenProTruth_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    type_of%
        (canonicalCofinalPaidReplayFairFiniteAdaptiveNoncompactProTruth_directConsumer
          point) ∧
      type_of%
        (canonicalPaidReplayFairPointwiseTerminatingUniformlyOpenProTruth_directConsumer
          oldVisit sourceIndex) :=
  ⟨canonicalCofinalPaidReplayFairFiniteAdaptiveNoncompactProTruth_directConsumer
      point,
    canonicalPaidReplayFairPointwiseTerminatingUniformlyOpenProTruth_directConsumer
      oldVisit sourceIndex⟩

end
end M14ProofCarryingCanonicalSocietyPaidReplayFairPointwiseTerminatingUniformlyOpenProTruth
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairPointwiseTerminatingUniformlyOpenProTruth.canonicalPaidReplayFairPointwiseTerminatingUniformlyOpenProTruth_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairPointwiseTerminatingUniformlyOpenProTruth.canonicalCofinalPaidReplayFairPointwiseTerminatingUniformlyOpenProTruth_directConsumer
