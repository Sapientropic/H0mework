import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Consumer.ProofCarryingCanonicalSocietyPaidReplayNoFiniteTruthCompletion
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Consumer.ProofCarryingCanonicalSocietyPaidReplayWitnessImageExplosion

/-!
# Proof-carrying fair finite witness tower

Every fair finite stage has a source-backed new bit and remains authority
incomplete.  The finite stages form a coherent directed tower which eventually
separates every fixed pair of distinct paid replays, without constructing an
omega archive or completed truth object.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14SourceGeneratedCanonicalSocietyCofinalPaidReplayWitnessPublication
open M14ProofCarryingCanonicalSocietyPaidReplayNoFiniteTruthCompletion
open M14ProofCarryingCanonicalSocietyPaidReplayWitnessImageExplosion
open M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveKernel
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower

/-- One fair finite stage: its exact current pair is locally repaired by the
new source witness, while the same stage and every finite refinement remain
globally authority-incomplete. -/
theorem canonicalPaidReplayFairFiniteWitnessStage_directConsumer
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    let archive :=
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
    let O := canonicalPaidReplayFiniteArchiveObserverAt oldVisit sourceIndex
      archive
    let pair := canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit
      sourceIndex stage
    let refinement := canonicalPaidReplayFairStageKernelRefinementAt oldVisit
      sourceIndex stage
    type_of%
      (canonicalPaidReplayFiniteArchiveNoTruth_directConsumer oldVisit
          sourceIndex stage (CanonicalPaidReplayFairFiniteArchiveAt stage)
          archive) ∧
      Nonempty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex stage pair.left) ∧
      IsEmpty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex stage pair.right) ∧
      (∀ replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        canonicalPaidReplayFairStagePublicationTag oldVisit sourceIndex stage
              replay = true ↔
          Nonempty
            (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
              sourceIndex stage replay)) ∧
      O.forget pair.left = O.forget pair.right ∧
      O.authorityK pair.left ≠ O.authorityK pair.right ∧
      type_of% pair.noOccurrenceLeftInverse ∧
      ¬ Nonempty (AuthorityFactorization O) ∧
      ¬ Nonempty (FaithfulAuthorityReconstruction O) ∧
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            (stage + 1) pair.left ≠
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          (stage + 1) pair.right ∧
      (∀ replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              (stage + 1) replay ⟨stage, by omega⟩ =
          canonicalPaidReplayFairStagePublicationTag oldVisit sourceIndex
            stage replay) ∧
      (¬ ∃ decode : CanonicalPaidReplayFairFiniteArchiveAt stage → Bool,
        ∀ replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
          decode (archive replay) =
            canonicalPaidReplayFairStagePublicationTag oldVisit sourceIndex
              stage replay) ∧
      @Fintype.card
          (Set.range
            (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              stage))
          (canonicalPaidReplayFairFiniteArchiveImageFintype oldVisit
            sourceIndex stage) =
        stage + 1 ∧
      Nonempty
        (FaithfulAuthorityReconstruction refinement.twoPointObserver) ∧
      Nonempty (AuthorityFactorization refinement.twoPointObserver) := by
  dsimp
  let pair :=
    canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex stage
  let refinement :=
    canonicalPaidReplayFairStageKernelRefinementAt oldVisit sourceIndex stage
  exact
    ⟨canonicalPaidReplayFiniteArchiveNoTruth_directConsumer oldVisit
        sourceIndex stage (CanonicalPaidReplayFairFiniteArchiveAt stage)
          (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            stage),
      ⟨sourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex stage⟩,
      refinement.rightWitnessEmpty,
      canonicalPaidReplayFairStagePublicationTag_true_iff oldVisit sourceIndex
        stage,
      pair.visible_eq,
      pair.authority_ne,
      pair.noOccurrenceLeftInverse,
      pair.noAuthorityFactorization,
      pair.noFaithfulAuthorityReconstruction,
      canonicalPaidReplayFairFiniteArchive_successorSeparatesCurrentPair
        oldVisit sourceIndex stage,
      canonicalPaidReplayFairFiniteArchive_successorNewBit_exact oldVisit
        sourceIndex stage,
      canonicalPaidReplayFairStageTag_notFactorThroughPredecessor oldVisit
        sourceIndex stage,
      canonicalPaidReplayFairFiniteArchiveActualImage_card_exact oldVisit
        sourceIndex stage,
      ⟨refinement.twoPointFaithfulAuthorityReconstruction⟩,
      ⟨refinement.twoPointAuthorityFactorization⟩⟩

/-- Full directed tower: all stages are open, all restriction squares commute,
and every fixed distinct replay pair is separated cofinally. -/
theorem canonicalPaidReplayFairFiniteWitnessTower_directConsumer
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (∀ stage,
      type_of%
        (canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
          sourceIndex stage)) ∧
      (∀ {earlier later : Nat} (earlierLeLater : earlier ≤ later)
        (replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex),
        canonicalPaidReplayFairFiniteArchiveRestriction earlierLeLater
            (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              later replay) =
          canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            earlier replay) ∧
      (∀ {first second third : Nat}
        (firstLeSecond : first ≤ second) (secondLeThird : second ≤ third)
        (archive : CanonicalPaidReplayFairFiniteArchiveAt third),
        canonicalPaidReplayFairFiniteArchiveRestriction firstLeSecond
            (canonicalPaidReplayFairFiniteArchiveRestriction secondLeThird
              archive) =
          canonicalPaidReplayFairFiniteArchiveRestriction
            (firstLeSecond.trans secondLeThird) archive) ∧
      (∀ left right :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        left ≠ right →
          ∃ stage,
            canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
                  stage left ≠
              canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit
                sourceIndex stage right) ∧
      (∀ requestedStage,
        ∀ left right :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        left ≠ right →
          ∃ stage,
            requestedStage < stage ∧
              canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit
                    sourceIndex stage left ≠
                canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit
                  sourceIndex stage right) :=
  ⟨canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
      sourceIndex,
    canonicalPaidReplayFairFiniteArchiveRestriction_exact oldVisit sourceIndex,
    canonicalPaidReplayFairFiniteArchiveRestriction_trans,
    canonicalPaidReplayFairFiniteArchive_eventuallySeparates oldVisit
      sourceIndex,
    canonicalPaidReplayFairFiniteArchive_eventuallySeparatesAfter oldVisit
      sourceIndex⟩

/-- The same constitutional point consumes the fair tower beyond its own `m`;
the prior witness-image explosion remains an exact conjunct. -/
theorem canonicalCofinalPaidReplayFairFiniteWitnessTower_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    type_of%
        (canonicalCofinalPaidReplayWitnessImageExplosion_directConsumer
          point) ∧
      type_of%
        (canonicalPaidReplayFairFiniteWitnessTower_directConsumer oldVisit
          sourceIndex) ∧
      (∀ left right :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        left ≠ right →
          ∃ stage,
            m < stage ∧
              canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit
                    sourceIndex stage left ≠
                canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit
                  sourceIndex stage right) :=
  ⟨canonicalCofinalPaidReplayWitnessImageExplosion_directConsumer point,
    canonicalPaidReplayFairFiniteWitnessTower_directConsumer oldVisit
      sourceIndex,
    canonicalPaidReplayFairFiniteArchive_eventuallySeparatesAfter oldVisit
      sourceIndex m⟩

end
end M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower.canonicalPaidReplayFairFiniteWitnessStage_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower.canonicalPaidReplayFairFiniteWitnessTower_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower.canonicalCofinalPaidReplayFairFiniteWitnessTower_directConsumer
