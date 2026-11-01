import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Cascade.Proposal.Recourse.Source.SourceGeneratedCanonicalSocietyFirstRefusalPaymentRecourse

/-!
# Proof-carrying first-refusal source-owned recourse

Every first source-acceptance refusal retains its empty external acceptance
fibre, but the bearer recovered from the same Payment root receives the
existing ordinary standing-repair renewal.  The canonical revolutionary law
step continues independently and its next authority is not collapsed with
the ordinary repair next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyFirstRefusalSourceOwnedRecourse

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade
open M14SourceGeneratedCanonicalSocietyAcceptedLegislationEnactmentStep
open M14SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler
open M14ProofCarryingCanonicalSocietyFiniteProposalAcceptanceExhaustion
open M14ProofCarryingExitRepairRenewalRegression
open M14SourceGeneratedCanonicalSocietyFirstRefusalPaymentRecourse

structure FirstRefusalSourceOwnedRecourseAt
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (program : FiniteProposalProgramAt initial fuel)
    (node : Fin (fuel + 1)) : Prop where
  refusalContinuation :
    FirstRefusedFiniteProposalContinuationAt initial program node
  refusedExternalAcceptanceEmpty :
    IsEmpty (FiniteProposalAcceptedAt initial program node)
  refusedExternalAcceptedConsumerEmpty :
    IsEmpty (FiniteProposalAcceptedConsumerAt initial program node)
  bearerActionableExitAudit :
    type_of% (firstRefusalExitAuditAt (initial := initial)
      (program := program) node)
  ordinaryRepairRenewal :
    Nonempty
      (ProofCarryingExitRepairRenewalConsumerAt
        (firstRefusalRepairDepthAt (initial := initial)
          (program := program) node))
  samePaymentRoot :
    type_of% (firstRefusalRepairRoot_isReplayPaymentRoot
      (initial := initial) (program := program) node)
  renewedStandingExact :
    type_of% (firstRefusalRepairStanding_exact
      (initial := initial) (program := program) node)
  standingResponsibilityConsumer :
    Nonempty
      (type_of%
        (firstRefusalRepairRenewalAt (initial := initial)
          (program := program) node).renewal.appliedReform.rootConsumer)
  ordinaryWholeLedgerWriteBack :
    Nonempty
      (type_of%
        (firstRefusalRepairRenewalAt (initial := initial)
          (program := program) node).renewal.wholeLedgerWriteBack)
  ordinarySelectedWriteCommutes :
    type_of%
      (firstRefusalRepairRenewalAt (initial := initial)
        (program := program) node).selectedWriteCommutes
  ordinaryRootFactorization :
    type_of%
      (firstRefusalRepairRenewalAt (initial := initial)
        (program := program) node).rootFactorization
  repairOutcomeCapacityOne :
    type_of%
      (firstRefusalRepairRenewalAt (initial := initial)
        (program := program) node).outcomeExact
  ordinaryActualRepairNext :
    type_of%
      (firstRefusalRepairRenewalAt (initial := initial)
        (program := program) node).generatedNextExact
  ordinaryLawSurfacePreserved :
    type_of%
      (firstRefusalRepairRenewalAt (initial := initial)
        (program := program) node).lawSurfacePreserved
  nextStandingProtected :
    type_of%
      (firstRefusalRepairRenewalAt (initial := initial)
        (program := program) node).nextRepairedFace
  canonicalLegislationStillGeneratesNext :
    CycleAcceptedLegislationStepFactsAt initial node.1
  ordinaryAndRevolutionaryNextDistinct :
    type_of% (firstRefusalOrdinaryNext_ne_revolutionaryLawNext
      (initial := initial) (program := program) node)

theorem firstRefusal_exposesSourceOwnedRecourse
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (program : FiniteProposalProgramAt initial fuel)
    (node : Fin (fuel + 1))
    (refusal : FirstSourceAcceptanceRefusalAt initial program node) :
    FirstRefusalSourceOwnedRecourseAt initial program node := by
  let continuation :=
    firstRefusedFiniteProposal_preservesSourceEnactment initial program node
      refusal
  let repair := firstRefusalRepairRenewalAt
    (initial := initial) (program := program) node
  exact
    { refusalContinuation := continuation
      refusedExternalAcceptanceEmpty :=
        continuation.refusedProgramAcceptanceEmpty
      refusedExternalAcceptedConsumerEmpty :=
        continuation.refusedProgramAcceptedConsumerEmpty
      bearerActionableExitAudit :=
        firstRefusalExitAuditAt (initial := initial) (program := program) node
      ordinaryRepairRenewal := ⟨repair⟩
      samePaymentRoot :=
        firstRefusalRepairRoot_isReplayPaymentRoot
          (initial := initial) (program := program) node
      renewedStandingExact :=
        firstRefusalRepairStanding_exact
          (initial := initial) (program := program) node
      standingResponsibilityConsumer :=
        ⟨repair.renewal.appliedReform.rootConsumer⟩
      ordinaryWholeLedgerWriteBack :=
        ⟨repair.renewal.wholeLedgerWriteBack⟩
      ordinarySelectedWriteCommutes := repair.selectedWriteCommutes
      ordinaryRootFactorization := repair.rootFactorization
      repairOutcomeCapacityOne := repair.outcomeExact
      ordinaryActualRepairNext := repair.generatedNextExact
      ordinaryLawSurfacePreserved := repair.lawSurfacePreserved
      nextStandingProtected := repair.nextRepairedFace
      canonicalLegislationStillGeneratesNext :=
        continuation.canonicalLawStillGeneratesActualNext
      ordinaryAndRevolutionaryNextDistinct :=
        firstRefusalOrdinaryNext_ne_revolutionaryLawNext
          (initial := initial) (program := program) node }

/-- Premise-free direct recourse on the adjacent actual-Payment refusal. -/
theorem adjacentActualPaymentRefusal_exposesSourceOwnedRecourse
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    FirstRefusalSourceOwnedRecourseAt initial
      (adjacentMismatchFiniteProposalProgramAt initial fuel)
      ⟨0, by omega⟩ :=
  firstRefusal_exposesSourceOwnedRecourse initial
    (adjacentMismatchFiniteProposalProgramAt initial fuel) ⟨0, by omega⟩
    (adjacentMismatchFiniteProposalProgram_firstRefusal initial fuel)

structure CanonicalSocietyFirstRefusalSourceOwnedRecourseAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) : Prop where
  priorProposalAcceptanceExhaustion :
    CanonicalSocietyFiniteProposalAcceptanceExhaustionAt initial
  everyFirstRefusalExposesRecourse : ∀ (fuel : Nat)
      (program : FiniteProposalProgramAt initial fuel)
      (node : Fin (fuel + 1)),
    FirstSourceAcceptanceRefusalAt initial program node →
      FirstRefusalSourceOwnedRecourseAt initial program node
  everyFuelHasActualRefusalRecourse : ∀ fuel,
    FirstRefusalSourceOwnedRecourseAt initial
      (adjacentMismatchFiniteProposalProgramAt initial fuel)
      ⟨0, by omega⟩

theorem canonicalSocietyFirstRefusalSourceOwnedRecourse
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    CanonicalSocietyFirstRefusalSourceOwnedRecourseAt initial where
  priorProposalAcceptanceExhaustion :=
    canonicalSocietyFiniteProposalAcceptanceExhaustion initial
  everyFirstRefusalExposesRecourse :=
    fun _fuel program node refusal =>
      firstRefusal_exposesSourceOwnedRecourse initial program node refusal
  everyFuelHasActualRefusalRecourse := fun fuel =>
    adjacentActualPaymentRefusal_exposesSourceOwnedRecourse initial fuel

end
end M14ProofCarryingCanonicalSocietyFirstRefusalSourceOwnedRecourse
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFirstRefusalSourceOwnedRecourse.firstRefusal_exposesSourceOwnedRecourse
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFirstRefusalSourceOwnedRecourse.adjacentActualPaymentRefusal_exposesSourceOwnedRecourse
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFirstRefusalSourceOwnedRecourse.canonicalSocietyFirstRefusalSourceOwnedRecourse
