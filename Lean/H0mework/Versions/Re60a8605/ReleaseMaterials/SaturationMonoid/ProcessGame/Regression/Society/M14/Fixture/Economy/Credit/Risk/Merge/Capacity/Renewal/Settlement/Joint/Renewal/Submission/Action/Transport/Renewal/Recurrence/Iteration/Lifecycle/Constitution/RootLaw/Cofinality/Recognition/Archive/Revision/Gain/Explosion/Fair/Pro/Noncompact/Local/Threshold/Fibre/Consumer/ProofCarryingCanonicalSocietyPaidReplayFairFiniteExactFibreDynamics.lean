import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Consumer.ProofCarryingCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold

/-!
# Proof-carrying exact fair-fibre dynamics

This mouth combines the exact fibre normal form at every finite stage with the
unique source-native recognition escape at every successor.  Static
stratification and actual witness-driven transition are consumed together.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteExactFibreDynamics

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux

/-- Maximum state-plus-transition mouth for the fair finite archive. -/
theorem canonicalPaidReplayFairFiniteExactFibreDynamics_directConsumer
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    type_of%
        (canonicalPaidReplayFairFiniteRecognitionThreshold_directConsumer
          oldVisit sourceIndex) ∧
      (∀ stage (hot : Fin stage)
        (candidate :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex),
        type_of%
          (canonicalPaidReplayFairFiniteArchive_hotFibre_exact oldVisit
            sourceIndex stage hot candidate)) ∧
      (∀ stage
        (candidate :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex),
        type_of%
          (canonicalPaidReplayFairFiniteArchive_zeroFibre_exact oldVisit
            sourceIndex stage candidate)) ∧
      (∀ stage
        (left right :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex),
        type_of%
            (canonicalPaidReplayFairFiniteArchive_readout_eq_iff oldVisit
              sourceIndex stage left right) ∧
          type_of%
            (canonicalPaidReplayFairFiniteArchive_readout_eq_iff_authorityK
              oldVisit sourceIndex stage left right)) ∧
      (∀ stage,
        Function.Injective
            (canonicalPaidReplayFairTailOccurrenceAt oldVisit sourceIndex
              stage) ∧
          Function.Injective
            (fun offset =>
              (canonicalPaidReplayFairTailOccurrenceAt oldVisit sourceIndex
                stage offset).1.2.authorityK)) ∧
      (∀ stage,
        type_of%
            (canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit
              sourceIndex stage) ∧
          type_of%
            (canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
              sourceIndex stage) ∧
          type_of%
            (canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
              sourceIndex (stage + 1)) ∧
          @Fintype.card
              (Set.range
                (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit
                  sourceIndex stage))
              (canonicalPaidReplayFairFiniteArchiveImageFintype oldVisit
                sourceIndex stage) =
            stage + 1) := by
  exact
    ⟨canonicalPaidReplayFairFiniteRecognitionThreshold_directConsumer
        oldVisit sourceIndex,
      canonicalPaidReplayFairFiniteArchive_hotFibre_exact oldVisit
        sourceIndex,
      canonicalPaidReplayFairFiniteArchive_zeroFibre_exact oldVisit
        sourceIndex,
      fun stage left right =>
        ⟨canonicalPaidReplayFairFiniteArchive_readout_eq_iff oldVisit
            sourceIndex stage left right,
          canonicalPaidReplayFairFiniteArchive_readout_eq_iff_authorityK
            oldVisit sourceIndex stage left right⟩,
      fun stage =>
        ⟨canonicalPaidReplayFairTailOccurrenceAt_injective oldVisit
            sourceIndex stage,
          canonicalPaidReplayFairTailAuthorityK_injective oldVisit sourceIndex
            stage⟩,
      fun stage =>
        ⟨canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
            stage,
          canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
            sourceIndex stage,
          canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
            sourceIndex (stage + 1),
          canonicalPaidReplayFairFiniteArchiveActualImage_card_exact oldVisit
            sourceIndex stage⟩⟩

/-- The same constitutional point consumes exact fibre state and successor
flux while retaining its complete threshold/noncompact history. -/
theorem canonicalCofinalPaidReplayFairFiniteExactFibreDynamics_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    type_of%
        (canonicalCofinalPaidReplayFairFiniteRecognitionThreshold_directConsumer
          point) ∧
      type_of%
        (canonicalPaidReplayFairFiniteExactFibreDynamics_directConsumer
          oldVisit sourceIndex) :=
  ⟨canonicalCofinalPaidReplayFairFiniteRecognitionThreshold_directConsumer
      point,
    canonicalPaidReplayFairFiniteExactFibreDynamics_directConsumer oldVisit
      sourceIndex⟩

end
end M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteExactFibreDynamics
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteExactFibreDynamics.canonicalPaidReplayFairFiniteExactFibreDynamics_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteExactFibreDynamics.canonicalCofinalPaidReplayFairFiniteExactFibreDynamics_directConsumer
