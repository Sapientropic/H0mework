import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8Failure
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.Exit.Root.SourceGeneratedMandateExitTargetRoot
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Ordinary.CrossCompiler.Mandate.Standing.Producer.SourceInstalledMandateFiniteConstitutionIncidence

/-!
# Exact generated-next source of the mandate-exit action

The source visit is not selected independently.  It is the finite successor
of the installed standing mandate occurrence at the Constitution-selected
depth, and it coincides with the next cycle's selected mandate/Payment depth.
This file names only that source event, existing entry and recursively
generated causal-entry authority; it creates no action target or receipt.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedMandateExitActionSource

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCycleMaximalCanonicalPaidStep
open M14SourceInstalledMandateFiniteConstitutionIncidence

def mandateExitActionSourceDepthAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Nat :=
  mandateConstitutionDepthAt initial depth + 1

def mandateExitActionSourceVisitAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceNativeTemporalVisitAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot :=
  temporalVisitAt (mandateExitActionSourceDepthAt initial depth)

def mandateExitActionSourceEntryAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (_initial : CycleAt oldVisit sourceIndex boundary) (_depth : Nat) :
    OpenResponsibilityAt M9ProofCarryingRenewalInquiryRoot.N true :=
  M9ProofCarryingRenewalU8Failure.entry

def mandateExitActionSourceAuthorityAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt jointRoot
      (mandateExitActionSourceVisitAt initial depth)
      (mandateExitActionSourceEntryAt initial depth) :=
  M9ProofCarryingRenewalU8Failure.authorityAt
    (rootVisitAt (mandateExitActionSourceDepthAt initial depth))

def mandateExitActionExactSourceEventAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    ExactTemporalCausalRootEventAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot
        (mandateExitActionSourceVisitAt initial depth) :=
  jointRoot.toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt
      (mandateExitActionSourceVisitAt initial depth)

@[simp] theorem jointRoot_generatedNext_eq_temporalVisit_succ (atDepth : Nat) :
    jointRoot.generatedNextCurrentAt (temporalVisitAt atDepth) =
      ⟨M9ProofCarryingRenewalInquiryRoot.V,
        jointRoot.toAuthoritativeRoot, temporalVisitAt (atDepth + 1)⟩ :=
  rfl

/-- The installed standing face's generated next is exactly the action source
current. -/
theorem standingMandate_generatedNext_eq_actionSource
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    let standing :=
      sourceInstalledMandateFiniteConstitutionIncidenceAt initial depth
    standing.mandate.mandate.generatedNext =
      ⟨M9ProofCarryingRenewalInquiryRoot.V,
        jointRoot.toAuthoritativeRoot,
        mandateExitActionSourceVisitAt initial depth⟩ := by
  dsimp only
  rw [(sourceInstalledMandateFiniteConstitutionIncidenceAt initial depth
    ).mandate.mandate.generatedNextExact]
  exact jointRoot_generatedNext_eq_temporalVisit_succ
    (mandateConstitutionDepthAt initial depth)

/-- The source occurrence is also the next cycle's canonical mandate/Payment
depth; no independent scheduler chooses it. -/
theorem actionSourceDepth_eq_nextCycleConstitutionDepth
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    mandateExitActionSourceDepthAt initial depth =
      mandateConstitutionDepthAt initial (depth + 1) := by
  unfold mandateExitActionSourceDepthAt mandateConstitutionDepthAt
  unfold M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution.cycleExitCapacityDepthAt
  unfold M14SourceGeneratedPaidExitLifecycleTemporalSpine.paidExitLifecycleSuccessorDepthAt
  rw [M14SourceGeneratedContributionCapacityPostSettlementExternalLiability.contributionCapacityPostSettlementReachableCurrentAt_exact]
  rw [M14SourceGeneratedContributionCapacityPostSettlementExternalLiability.contributionCapacityPostSettlementReachableCurrentAt_exact]
  rw [cycleMaximalTargetIndex_eq_nextLifecycleIndex]
  omega

theorem actionSourceOccurrence_is_nextCycleMandateOccurrence
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HEq (mandateExitActionExactSourceEventAt initial depth)
      (jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (temporalVisitAt
          (mandateConstitutionDepthAt initial (depth + 1)))) := by
  have depthExact :=
    actionSourceDepth_eq_nextCycleConstitutionDepth initial depth
  cases depthExact
  rfl

theorem mandateExitActionSourceDepthAt_injective
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    Function.Injective (mandateExitActionSourceDepthAt initial) := by
  intro left right equality
  unfold mandateExitActionSourceDepthAt mandateConstitutionDepthAt at equality
  unfold M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution.cycleExitCapacityDepthAt at equality
  unfold M14SourceGeneratedPaidExitLifecycleTemporalSpine.paidExitLifecycleSuccessorDepthAt at equality
  rw [M14SourceGeneratedContributionCapacityPostSettlementExternalLiability.contributionCapacityPostSettlementReachableCurrentAt_exact] at equality
  rw [M14SourceGeneratedContributionCapacityPostSettlementExternalLiability.contributionCapacityPostSettlementReachableCurrentAt_exact] at equality
  rw [M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch.cycleLifecycleIndex_exact] at equality
  rw [M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch.cycleLifecycleIndex_exact] at equality
  omega

abbrev AnyMandateExitActionSourceOccurrenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (_initial : CycleAt oldVisit sourceIndex boundary) :=
  Sigma fun visit : SourceNativeTemporalVisitAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot =>
    ExactTemporalCausalRootEventAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot visit

def mandateExitActionSourceOccurrenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    AnyMandateExitActionSourceOccurrenceAt initial :=
  ⟨mandateExitActionSourceVisitAt initial depth,
    mandateExitActionExactSourceEventAt initial depth⟩

theorem mandateExitActionSourceOccurrenceAt_injective
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    Function.Injective (mandateExitActionSourceOccurrenceAt initial) := by
  intro left right equality
  have visitEquality := congrArg Sigma.fst equality
  have sourceDepthEquality := temporalVisitAt_injective visitEquality
  exact mandateExitActionSourceDepthAt_injective initial sourceDepthEquality

/-- No single occurrence stores the mandate exits of all finite depths. -/
theorem no_single_mandateExitActionSource_occurrence_carries_all_depths
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    ¬ ∃ occurrence : AnyMandateExitActionSourceOccurrenceAt initial,
      ∀ depth : Nat,
        mandateExitActionSourceOccurrenceAt initial depth = occurrence := by
  rintro ⟨occurrence, allDepths⟩
  have equal := (allDepths 0).trans (allDepths 1).symm
  have depthEqual :=
    mandateExitActionSourceOccurrenceAt_injective initial equal
  omega

end
end M14SourceGeneratedMandateExitActionSource
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateExitActionSource.standingMandate_generatedNext_eq_actionSource
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateExitActionSource.actionSourceDepth_eq_nextCycleConstitutionDepth
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateExitActionSource.actionSourceOccurrence_is_nextCycleMandateOccurrence
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateExitActionSource.mandateExitActionSourceOccurrenceAt_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateExitActionSource.no_single_mandateExitActionSource_occurrence_carries_all_depths
