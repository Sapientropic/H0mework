import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Consumer.ProofCarryingCanonicalSocietyCofinalReadout
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.SourceWitnessRefinement

/-!
# Source witness for the canonical cofinal paid-replay kernel

At one exact canonical-Society cofinal point, the existing self-U8 recurrence
already generates two paid replays with the same pulse and different
authority.  The left replay's actual path, next morphism, paid-target splice
and generated next now produce an honest witness publication for that exact
pair.

The publication reads no authority `K`, and no caller supplies an endpoint,
pair, verdict, decoder, occurrence registry, or future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyCofinalPaidReplayWitnessPublication

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout

/-- Exact pair already carried by the same canonical cofinal point. -/
def canonicalCofinalPaidReplayKernelPairAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    AuthorityKernelPair
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex) where
  left := (nextNovelty (stepAt initial m)).leftReplay
  right := (nextNovelty (stepAt initial m)).rightReplay
  occurrence_ne := by
    intro replayEquality
    exact point.selfU8ActualPathsDistinct
      (congrArg (fun replay => replay.2.actualPath) replayEquality)
  visible_eq := point.selfU8SameNormalDifferentK.1
  authority_ne := point.selfU8SameNormalDifferentK.2

/-- Source-owned witness family at the exact left actual path.  Besides its
path-native support, the witness consumes the same recurrence's next morphism,
paid-target/new-source seam and root-law generated next. -/
structure SourceGeneratedCanonicalCofinalPaidReplayWitnessAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse)
    (replay : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex) : Type where
  private mk ::
  nextMorphismCertificate :
    type_of% point.selfU8Tick.nextMorphismCertificate
  paidTargetIsNextSourceEvent :
    type_of% point.selfU8Tick.paidTargetIsNextSourceEvent
  nextCycleMouthExact : type_of% point.selfU8Tick.nextCycleMouthExact
  exactActualPathLabel :
    replay.2.actualPath =
      (nextNovelty (stepAt initial m)).leftReplay.2.actualPath

/-- Sole source witness at the generated left replay. -/
def sourceGeneratedCanonicalCofinalPaidReplayWitnessAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    SourceGeneratedCanonicalCofinalPaidReplayWitnessAt point
      (nextNovelty (stepAt initial m)).leftReplay where
  nextMorphismCertificate := point.selfU8Tick.nextMorphismCertificate
  paidTargetIsNextSourceEvent := point.selfU8Tick.paidTargetIsNextSourceEvent
  nextCycleMouthExact := point.selfU8Tick.nextCycleMouthExact
  exactActualPathLabel := rfl

/-- Total publication bit reads only the replay's actual-path label relative
to the source-generated left path; it never reads authority `K`. -/
noncomputable def canonicalCofinalPaidReplayPublicationTag
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (_point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse)
    (replay : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex) : Bool := by
  classical
  exact decide
    (replay.2.actualPath =
      (nextNovelty (stepAt initial m)).leftReplay.2.actualPath)

theorem canonicalCofinalPaidReplayPublicationTag_true_iff
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse)
    (replay : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex) :
    canonicalCofinalPaidReplayPublicationTag point replay = true ↔
      Nonempty (SourceGeneratedCanonicalCofinalPaidReplayWitnessAt point
        replay) := by
  constructor
  · intro published
    have exactActualPathLabel :
        replay.2.actualPath =
          (nextNovelty (stepAt initial m)).leftReplay.2.actualPath := by
      simpa [canonicalCofinalPaidReplayPublicationTag] using published
    exact
      ⟨{ nextMorphismCertificate := point.selfU8Tick.nextMorphismCertificate
         paidTargetIsNextSourceEvent :=
           point.selfU8Tick.paidTargetIsNextSourceEvent
         nextCycleMouthExact := point.selfU8Tick.nextCycleMouthExact
         exactActualPathLabel := exactActualPathLabel }⟩
  · rintro ⟨witness⟩
    simpa [canonicalCofinalPaidReplayPublicationTag] using
      witness.exactActualPathLabel

def canonicalCofinalPaidReplayPublicationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    SourceWitnessPublicationAt
      (SourceGeneratedCanonicalCofinalPaidReplayWitnessAt point) where
  publicationTag := canonicalCofinalPaidReplayPublicationTag point
  publicationTag_eq_true_iff :=
    canonicalCofinalPaidReplayPublicationTag_true_iff point

theorem canonicalCofinalPaidReplayKernelPair_rightWitness_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    let pair := canonicalCofinalPaidReplayKernelPairAt point
    IsEmpty
      (SourceGeneratedCanonicalCofinalPaidReplayWitnessAt point pair.right) :=
  ⟨fun witness =>
    point.selfU8ActualPathsDistinct witness.exactActualPathLabel.symm⟩

/-- Generic witness refinement consumes the same point's exact pair and
inhabited/empty witness split. -/
theorem canonicalCofinalPaidReplayKernelRefinementAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    let pair := canonicalCofinalPaidReplayKernelPairAt point
    SourceWitnessKernelRefinementAt
      (canonicalCofinalPaidReplayPublicationAt point) pair := by
  apply sourceWitnessKernelRefinement
  · exact ⟨sourceGeneratedCanonicalCofinalPaidReplayWitnessAt point⟩
  · exact canonicalCofinalPaidReplayKernelPair_rightWitness_isEmpty point

def canonicalCofinalPaidReplayRefinedObserverAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :=
  sourceWitnessRefinedObserver
    (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
      sourceIndex)
    (canonicalCofinalPaidReplayPublicationAt point)

theorem canonicalCofinalPaidReplay_refinedVisible_ne
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    let pair := canonicalCofinalPaidReplayKernelPairAt point
    (canonicalCofinalPaidReplayRefinedObserverAt point).forget pair.left ≠
      (canonicalCofinalPaidReplayRefinedObserverAt point).forget pair.right :=
  (canonicalCofinalPaidReplayKernelRefinementAt point).refinedVisible_ne

end
end M14SourceGeneratedCanonicalSocietyCofinalPaidReplayWitnessPublication
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyCofinalPaidReplayWitnessPublication.canonicalCofinalPaidReplayKernelPairAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyCofinalPaidReplayWitnessPublication.sourceGeneratedCanonicalCofinalPaidReplayWitnessAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyCofinalPaidReplayWitnessPublication.canonicalCofinalPaidReplayPublicationTag_true_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyCofinalPaidReplayWitnessPublication.canonicalCofinalPaidReplayKernelRefinementAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyCofinalPaidReplayWitnessPublication.canonicalCofinalPaidReplay_refinedVisible_ne
