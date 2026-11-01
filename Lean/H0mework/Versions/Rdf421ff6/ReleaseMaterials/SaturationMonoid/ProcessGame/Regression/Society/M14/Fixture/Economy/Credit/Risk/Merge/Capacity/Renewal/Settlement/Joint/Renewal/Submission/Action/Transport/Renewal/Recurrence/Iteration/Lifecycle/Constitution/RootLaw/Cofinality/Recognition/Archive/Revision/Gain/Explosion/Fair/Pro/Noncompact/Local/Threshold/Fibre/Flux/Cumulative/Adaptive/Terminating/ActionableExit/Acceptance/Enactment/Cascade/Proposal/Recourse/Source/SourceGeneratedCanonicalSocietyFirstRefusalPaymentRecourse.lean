import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Cascade.Proposal.Compiler.Consumer.ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustion
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Policy.ProofCarryingExitRepairRenewalRegression

/-!
# Source-generated first-refusal Payment recourse

The recourse source is the refused physical node's already existing right
replay and Payment root.  It regenerates the repository's ordinary exit-repair
renewal at that Payment depth; the refusal certificate itself creates no
appeal occurrence or authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyFirstRefusalPaymentRecourse

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open UniversalRootGrammar
open M9ProofCarryingRenewalInquiryRoot
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt
open M14SourceGeneratedCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade
open M14SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler
open M14ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustion
open M14SourceGeneratedCanonicalSocietyPaidReplayPointwiseActionableExitAudit
open M14ProofCarryingExitRepairRenewalRegression

/-- Existing paid replay at the physical node where proposal acceptance was
first refused. -/
abbrev firstRefusalReplayAt
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (_program : FiniteProposalProgramAt initial fuel)
    (node : Fin (fuel + 1)) :=
  rightReplayAt oldVisit sourceIndex (boundary + node.1)

/-- The repair depth is read from the replay's actual-service authority. -/
def firstRefusalRepairDepthAt
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {program : FiniteProposalProgramAt initial fuel}
    (node : Fin (fuel + 1)) : Nat :=
  (firstRefusalReplayAt initial program node).2.authorityK.2.depth

/-- Existing pointwise actionable-exit audit of the refusal bearer. -/
theorem firstRefusalExitAuditAt
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {program : FiniteProposalProgramAt initial fuel}
    (node : Fin (fuel + 1)) :
    type_of%
      (canonicalPaidReplayFairPointwiseActionableExitAudit oldVisit sourceIndex
        (firstRefusalReplayAt initial program node)) :=
  canonicalPaidReplayFairPointwiseActionableExitAudit oldVisit sourceIndex
    (firstRefusalReplayAt initial program node)

/-- Existing ordinary repair renewal regenerated at the bearer's Payment
depth. -/
def firstRefusalRepairRenewalAt
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {program : FiniteProposalProgramAt initial fuel}
    (node : Fin (fuel + 1)) :
    ProofCarryingExitRepairRenewalConsumerAt
      (firstRefusalRepairDepthAt (initial := initial) (program := program)
        node) :=
  proofCarryingExitRepairRenewalConsumerAt
    (firstRefusalRepairDepthAt (initial := initial) (program := program) node)

/-- The ordinary repair is rooted at the exact Payment root already carried
by the refused node's replay. -/
theorem firstRefusalRepairRoot_isReplayPaymentRoot
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {program : FiniteProposalProgramAt initial fuel}
    (node : Fin (fuel + 1)) :
    HEq
      (firstRefusalRepairRenewalAt (initial := initial) (program := program)
        node).renewal.rootOccurrence
      ((firstRefusalReplayAt initial program node).2.authorityK.2.actualExit
        ).paymentOccurrence.rootOccurrence := by
  let replay := firstRefusalReplayAt initial program node
  let depth := firstRefusalRepairDepthAt (initial := initial)
    (program := program) node
  have paymentExact :
      replay.2.authorityK.2.actualExit.paymentOccurrence =
        periodicSourceBackedPaymentAt depth :=
    replay.2.authorityK.2.actualExit.paymentOccurrence_eq
  change HEq (periodicSourceBackedPaymentAt depth).rootOccurrence
    replay.2.authorityK.2.actualExit.paymentOccurrence.rootOccurrence
  exact heq_of_eq
    (congrArg (fun payment => payment.rootOccurrence) paymentExact).symm

/-- The applied bounded reform renews exactly the installed operational
standing; it does not manufacture a replacement identity. -/
theorem firstRefusalRepairStanding_exact
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {program : FiniteProposalProgramAt initial fuel}
    (node : Fin (fuel + 1)) :
    (firstRefusalRepairRenewalAt (initial := initial) (program := program)
      node).renewal.appliedReform.reform.targetEntry =
      (firstRefusalRepairRenewalAt (initial := initial) (program := program)
        node).renewal.source.installed.operationalAuthority.operationalStanding :=
  rfl

/-- Ordinary repair and revolutionary legislation continue as distinct
authority currents.  Their carriers are respectively the existing Unit
current and the post-submission revised Nat current. -/
theorem firstRefusalOrdinaryNext_ne_revolutionaryLawNext
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {program : FiniteProposalProgramAt initial fuel}
    (node : Fin (fuel + 1)) :
    (⟨M9ProofCarryingRenewalInquiryRoot.N,
        (firstRefusalRepairRenewalAt (initial := initial) (program := program)
          node).renewal.generatedNext⟩ :
        AnyAuthoritativeRootCurrent) ≠
      (cyclePointwiseAcceptanceAt initial node.1
        ).independentConsumer.generatedNext := by
  intro collapsed
  rw [(cyclePointwiseAcceptanceAt initial node.1
    ).independentConsumer_generatedNext_isRuntimeNext] at collapsed
  have cardEquality := congrArg
    (fun erased : AnyAuthoritativeRootCurrent =>
      Nat.card erased.current.V.Current) collapsed
  change Nat.card Unit = Nat.card Nat at cardEquality
  simp at cardEquality

end
end M14SourceGeneratedCanonicalSocietyFirstRefusalPaymentRecourse
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyFirstRefusalPaymentRecourse.firstRefusalRepairRoot_isReplayPaymentRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyFirstRefusalPaymentRecourse.firstRefusalRepairStanding_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyFirstRefusalPaymentRecourse.firstRefusalOrdinaryNext_ne_revolutionaryLawNext
