import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Cascade.Proposal.Recourse.Consumer.ProofCarryingCanonicalSocietyFirstRefusalSourceOwnedRecourse
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Cascade.Proposal.Compiler.Constitution.Consumer.ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustionConstitution

/-!
# Constitutional first-refusal source-owned recourse

The existing cofinal point consumes the same-Payment recourse maximum while
preserving finite proposal exhaustion as its literal prior point.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyFirstRefusalSourceOwnedRecourseConstitution

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustionConstitution
open M14ProofCarryingCanonicalSocietyFirstRefusalSourceOwnedRecourse

structure CanonicalCofinalFirstRefusalSourceOwnedRecourseAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) : Prop where
  priorPoint :
    CanonicalCofinalFiniteProposalAcceptanceExhaustionAt point
  sourceOwnedRecourse :
    CanonicalSocietyFirstRefusalSourceOwnedRecourseAt initial

theorem canonicalCofinalFirstRefusalSourceOwnedRecourse_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    CanonicalCofinalFirstRefusalSourceOwnedRecourseAt point where
  priorPoint :=
    canonicalCofinalFiniteProposalAcceptanceExhaustion_directConsumer point
  sourceOwnedRecourse :=
    canonicalSocietyFirstRefusalSourceOwnedRecourse initial

end
end M14ProofCarryingCanonicalSocietyFirstRefusalSourceOwnedRecourseConstitution
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFirstRefusalSourceOwnedRecourseConstitution.canonicalCofinalFirstRefusalSourceOwnedRecourse_directConsumer
