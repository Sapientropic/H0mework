import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Consumer.ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation

/-!
# Source-indexed external-Payment legislation acceptance seal

The seal is indexed simultaneously by the exact heterogeneous Payment
occurrence and the existing target proof-carrying legislation.  Its sole
constructor is private and accepts only the source-generated legislation span.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation

/-- Existing heterogeneous Payment occurrence carried by the span's exact
right replay authority. -/
def targetAnyPaymentOccurrence
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (_span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary) :
    AnySourceBackedPaymentOccurrence :=
  (rightReplayAt oldVisit sourceIndex boundary).2.authorityK.paymentOccurrence

/-- The heterogeneous occurrence has exactly the dependent Payment payload
used by the existing target legislation span. -/
theorem targetAnyPaymentOccurrence_payload_heq
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary) :
    HEq (targetAnyPaymentOccurrence span).2
      (targetPaymentOccurrence span) := by
  cases span
  change HEq
    ((rightReplayAt oldVisit sourceIndex boundary).2.authorityK.2.actualExit
      |>.paymentOccurrence)
    ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
      |>.paymentOccurrence)
  have exitEquality :=
    (rightReplayAt oldVisit sourceIndex boundary).2
      |>.actualAuthority_isFutureBirthActualExit
  exact heq_of_eq
    (congrArg (fun actualExit => actualExit.paymentOccurrence)
      exitEquality.symm)

/-- The indices themselves seal the exact source Payment and existing target
PCL; there is no equality or legislation argument to the constructor. -/
inductive SourceAcceptedExternalPaymentLegislationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary) :
    AnySourceBackedPaymentOccurrence → TargetLegislationAt span → Type 32
  | private accepted :
      SourceAcceptedExternalPaymentLegislationAt span
        (targetAnyPaymentOccurrence span) (targetLegislation span)

/-- Sole source producer. -/
def sourceAcceptedExternalPaymentLegislationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary) :
    SourceAcceptedExternalPaymentLegislationAt span
      (targetAnyPaymentOccurrence span) (targetLegislation span) :=
  .accepted

/-- Public elimination of the Payment index. -/
theorem SourceAcceptedExternalPaymentLegislationAt.proposalExact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {proposal : AnySourceBackedPaymentOccurrence}
    {legislation : TargetLegislationAt span}
    (acceptance :
      SourceAcceptedExternalPaymentLegislationAt span proposal legislation) :
    proposal = targetAnyPaymentOccurrence span := by
  cases acceptance
  rfl

/-- Public elimination of the PCL index. -/
theorem SourceAcceptedExternalPaymentLegislationAt.legislationExact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {proposal : AnySourceBackedPaymentOccurrence}
    {legislation : TargetLegislationAt span}
    (acceptance :
      SourceAcceptedExternalPaymentLegislationAt span proposal legislation) :
    HEq legislation (targetLegislation span) := by
  cases acceptance
  rfl

end
end M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.targetAnyPaymentOccurrence_payload_heq
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt.proposalExact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt.legislationExact
