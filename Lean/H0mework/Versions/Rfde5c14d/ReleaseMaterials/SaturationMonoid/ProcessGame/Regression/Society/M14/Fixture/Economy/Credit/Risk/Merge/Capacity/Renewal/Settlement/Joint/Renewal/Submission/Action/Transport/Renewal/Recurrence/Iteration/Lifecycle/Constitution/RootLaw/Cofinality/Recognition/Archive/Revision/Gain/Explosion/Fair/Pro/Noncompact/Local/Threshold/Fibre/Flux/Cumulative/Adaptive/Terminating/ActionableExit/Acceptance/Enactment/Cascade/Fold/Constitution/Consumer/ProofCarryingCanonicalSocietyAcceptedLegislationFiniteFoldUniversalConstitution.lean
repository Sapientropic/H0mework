import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Cascade.Fold.Consumer.ProofCarryingCanonicalSocietyAcceptedLegislationFiniteFoldUniversal
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Cascade.Constitution.Consumer.ProofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascadeConstitution

/-!
# Constitutional accepted-legislation finite-fold universal property

The existing cofinal constitutional point consumes the physical finite-fold
universal property.  The earlier cascade remains its literal prior point;
there is no second Society sink.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyAcceptedLegislationFiniteFoldUniversalConstitution

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascadeConstitution
open M14ProofCarryingCanonicalSocietyAcceptedLegislationFiniteFoldUniversal

structure CanonicalCofinalAcceptedLegislationFiniteFoldUniversalAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) : Prop where
  priorPoint :
    CanonicalCofinalFiniteAcceptedLegislationEnactmentCascadeAt point
  finiteFoldUniversal :
    CanonicalSocietyAcceptedLegislationFiniteFoldUniversalAt initial

theorem canonicalCofinalAcceptedLegislationFiniteFoldUniversal_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    CanonicalCofinalAcceptedLegislationFiniteFoldUniversalAt point where
  priorPoint :=
    canonicalCofinalFiniteAcceptedLegislationEnactmentCascade_directConsumer
      point
  finiteFoldUniversal :=
    canonicalSocietyAcceptedLegislationFiniteFoldUniversal initial

end
end M14ProofCarryingCanonicalSocietyAcceptedLegislationFiniteFoldUniversalConstitution
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyAcceptedLegislationFiniteFoldUniversalConstitution.canonicalCofinalAcceptedLegislationFiniteFoldUniversal_directConsumer
