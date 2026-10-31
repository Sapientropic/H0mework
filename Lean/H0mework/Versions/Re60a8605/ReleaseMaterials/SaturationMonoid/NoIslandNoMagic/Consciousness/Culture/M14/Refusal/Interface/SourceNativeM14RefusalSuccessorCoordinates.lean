import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Consumer.IndependentM14InstitutionalAuthorityConsumer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Necessity.Refusal.ProofCarryingPaidSuccessorAfterRefusalAntiRetaliationRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Transport.OldGate.ProofCarryingPlatformGateOldPaidChannelTransport

/-!
# Source-native refusal successor coordinates

The platform gate's exact right-Payment current is the source current of the
existing paid-successor anti-retaliation producer at index `boundary + 2`.
One existing paid channel exposes the lawful next seam into the target
post-settlement outer occurrence.  This is a cross-root successor transport,
not an equality with the institutional U8 root's own next.

The occurrence domain is the disjoint union of the producer's exact source
and target outer-authority singleton restrictions.  The readout keeps actual
service K, current, response-action code, real employment-action code, and
the installed/full-capture capacities.  Its injectivity is proved from the
actual-service K difference, never from the sum constructor.

No refusal consumer system, culture carrier, quotient, U8 revision, root
installation, or successor is accepted as input.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Refusal
namespace Interface

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open ProcessGame.Society.M14UBIExitCapacityFixture
open ProcessGame.Society.M14UBIPeriodicActualServiceCapacity
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14EssentialAccessSectorRegression
open ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open ProcessGame.Society.M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal
open ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation
open ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo
open ProcessGame.Society.M14ProofCarryingPaidSuccessorAfterRefusalAntiRetaliationRegression
open ProcessGame.Society.M14ProofCarryingPlatformGateOldPaidChannelTransport
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Consumer

noncomputable section

def m14RefusalSuccessorIndexAt (boundary : Nat) : Nat :=
  platformGateOldPaidChannelIndexAt boundary

def m14RefusalAntiRetaliationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
      sourceIndex (m14RefusalSuccessorIndexAt boundary) :=
  sourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
    sourceIndex (m14RefusalSuccessorIndexAt boundary)

abbrev M14RefusalOuterAuthorityAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot.AnyContributionCapacityPostSettlementRenewalOccurrenceAt
    oldVisit sourceIndex

abbrev M14RefusalSourceOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { occurrence : M14RefusalOuterAuthorityAt oldVisit sourceIndex //
    occurrence =
      (m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
        ).standingRenewal.sourceOuterAuthority }

abbrev M14RefusalTargetOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { occurrence : M14RefusalOuterAuthorityAt oldVisit sourceIndex //
    occurrence =
      (m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
        ).standingRenewal.targetOuterAuthority }

abbrev M14RefusalOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M14RefusalSourceOccurrenceAt oldVisit sourceIndex boundary ⊕
    M14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary

def m14RefusalSourceOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14RefusalOccurrenceAt oldVisit sourceIndex boundary :=
  .inl ⟨(m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
    ).standingRenewal.sourceOuterAuthority, rfl⟩

def m14RefusalTargetOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14RefusalOccurrenceAt oldVisit sourceIndex boundary :=
  .inr ⟨(m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
    ).standingRenewal.targetOuterAuthority, rfl⟩

def m14RefusalOuterAuthorityRead
    {oldVisit : OldVisit} {sourceIndex boundary : Nat} :
    M14RefusalOccurrenceAt oldVisit sourceIndex boundary →
      M14RefusalOuterAuthorityAt oldVisit sourceIndex
  | .inl source => source.1
  | .inr target => target.1

def m14RefusalActualServiceKRead
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (occurrence : M14RefusalOccurrenceAt oldVisit sourceIndex boundary) :
    AnyPeriodicActualServiceExit :=
  contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt oldVisit
    sourceIndex (m14RefusalOuterAuthorityRead occurrence).1

structure M14RefusalAuthorityReadout : Type where
  authorityCurrent : Nat
  responseAction : ExitFutureCode
  employmentAction : type_of% ProcessGame.Society.M14SourceGeneratedContributionCapacityBirthBearerExit.birthBearerExactEmploymentAction.1
  liveCapacity : Nat
  fullCaptureCapacity : Nat

def m14RefusalAuthorityReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14RefusalOccurrenceAt oldVisit sourceIndex boundary) :
    M14RefusalAuthorityReadout :=
  let anti := m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
  match occurrence with
  | .inl source =>
      { authorityCurrent := source.1.1
        responseAction := anti.sourcePayment.exerciseAction.1
        employmentAction :=
          ProcessGame.Society.M14SourceGeneratedContributionCapacityBirthBearerExit.birthBearerExactEmploymentAction.1
        liveCapacity :=
          ProcessGame.Society.M14SourceGeneratedContributionCapacityBirthBearerExit.birthBearerGeometryCompilerAt
            source.1.1 |>.actionableExitCapacity
        fullCaptureCapacity :=
          ProcessGame.Society.M14SourceGeneratedContributionCapacityBirthBearerExit.birthBearerCapturedGeometryCompilerAt
            source.1.1 |>.actionableExitCapacity }
  | .inr target =>
      { authorityCurrent := target.1.1
        responseAction := anti.targetResponseAction.1
        employmentAction :=
          anti.targetResponseCarrier.employmentLoss.power.action.1
        liveCapacity :=
          ProcessGame.Society.M14SourceGeneratedContributionCapacityBirthBearerExit.birthBearerGeometryCompilerAt
            target.1.1 |>.actionableExitCapacity
        fullCaptureCapacity :=
          ProcessGame.Society.M14SourceGeneratedContributionCapacityBirthBearerExit.birthBearerCapturedGeometryCompilerAt
            target.1.1 |>.actionableExitCapacity }

theorem m14RefusalAuthorityRead_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Function.Injective
      (m14RefusalAuthorityReadAt oldVisit sourceIndex boundary) := by
  intro left right sameRead
  cases left with
  | inl leftSource =>
      cases right with
      | inl rightSource =>
          exact congrArg Sum.inl (Subsingleton.elim leftSource rightSource)
      | inr rightTarget =>
          have sameCurrent := congrArg
            M14RefusalAuthorityReadout.authorityCurrent
            sameRead
          have sourceCurrentExact := congrArg Sigma.fst leftSource.property
          have targetCurrentExact := congrArg Sigma.fst rightTarget.property
          exact (Nat.ne_of_lt
            (m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
              ).standingRenewal.sourceAuthorityCurrent_lt_target (by
                exact sourceCurrentExact.symm.trans
                  (sameCurrent.trans targetCurrentExact))).elim
  | inr leftTarget =>
      cases right with
      | inl rightSource =>
          have sameCurrent := congrArg
            M14RefusalAuthorityReadout.authorityCurrent
            sameRead
          have targetCurrentExact := congrArg Sigma.fst leftTarget.property
          have sourceCurrentExact := congrArg Sigma.fst rightSource.property
          exact (Nat.ne_of_lt
            (m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
              ).standingRenewal.sourceAuthorityCurrent_lt_target (by
                exact sourceCurrentExact.symm.trans
                  (sameCurrent.symm.trans targetCurrentExact))).elim
      | inr rightTarget =>
          exact congrArg Sum.inr (Subsingleton.elim leftTarget rightTarget)

theorem m14Refusal_source_target_difference
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14RefusalAuthorityReadAt oldVisit sourceIndex boundary
        (m14RefusalSourceOccurrenceAt oldVisit sourceIndex boundary) ≠
      m14RefusalAuthorityReadAt oldVisit sourceIndex boundary
        (m14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary) := by
  intro sameRead
  have sameOccurrence := m14RefusalAuthorityRead_injective oldVisit
    sourceIndex boundary sameRead
  cases sameOccurrence

/-! ## Exact right-Payment successor seam -/

theorem m14RefusalSourceCurrent_eq_rightPaymentCurrent
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
      ).standingRenewal.sourceAuthorityCurrent =
      ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.rightCurrentAt
        oldVisit sourceIndex boundary := by
  change
    ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementExternalLiability.contributionCapacityPostSettlementReachableCurrentAt
        oldVisit sourceIndex (platformGateOldPaidChannelIndexAt boundary) = _
  exact platformGateOldPaidChannelCurrent_eq_rightCurrent oldVisit sourceIndex
    boundary

theorem m14RefusalSourcePayment_eq_rightPayment
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary).sourcePayment =
      (ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.rightReplayAt
        oldVisit sourceIndex boundary).2.payment :=
  rfl

theorem m14RefusalSourcePaymentNext_eq_platformChannelNext
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq (m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
      ).sourcePayment.nextPaidBy
      (platformGateOldPaidChannelAt oldVisit sourceIndex boundary
        tenureAuthority).2.actualNext := by
  let anti := m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
  have currentExact :=
    m14RefusalSourceCurrent_eq_rightPaymentCurrent oldVisit sourceIndex
      boundary
  cases currentExact
  apply heq_of_eq
  change anti.standingRenewal.sourcePayment.nextPaidBy = _
  rw [anti.standingRenewal.sourcePayment_exact]
  change
    (sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex (platformGateOldPaidChannelIndexAt boundary)
      ).nextPaidBy = _
  rw [PostSettlementOccurrencePaymentAt.nextPaidBy_occurrence_exact]
  exact (platformGateOldPaidChannel_actualNextExact oldVisit sourceIndex
    boundary tenureAuthority).symm

theorem m14RefusalPlatformChannelNext_isTargetOuterOccurrence
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (platformGateOldPaidChannelAt oldVisit sourceIndex boundary
        tenureAuthority).2.actualNext
      (m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
        ).targetConsequence.outerRootEvent.occurrence := by
  let anti := m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
  have sourceNext :=
    m14RefusalSourcePaymentNext_eq_platformChannelNext oldVisit sourceIndex
      boundary
  exact sourceNext.symm.trans
    anti.sourcePaidNext_isTargetOuterOccurrence

theorem sourceGeneratedM14RefusalSuccessor_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let anti := m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
    type_of% anti.paidSuccessorAfterRefusalAntiRetaliation_exact ∧
      type_of% (paidSuccessorAfterRefusalAntiRetaliationAuditAt oldVisit
        sourceIndex (m14RefusalSuccessorIndexAt boundary)) ∧
      type_of% proofCarryingPaidSuccessorAfterRefusalAntiRetaliationDirectConsumer ∧
      anti.standingRenewal.sourceAuthorityCurrent =
        ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.rightCurrentAt
          oldVisit sourceIndex boundary ∧
      anti.sourcePayment =
        (ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.rightReplayAt
          oldVisit sourceIndex boundary).2.payment ∧
      HEq anti.sourcePayment.nextPaidBy
        (platformGateOldPaidChannelAt oldVisit sourceIndex boundary
          tenureAuthority).2.actualNext ∧
      type_of% (m14RefusalPlatformChannelNext_isTargetOuterOccurrence oldVisit
        sourceIndex boundary) ∧
      Function.Injective
        (m14RefusalAuthorityReadAt oldVisit sourceIndex boundary) ∧
      type_of% (m14Refusal_source_target_difference oldVisit sourceIndex
        boundary) := by
  let anti := m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
  exact ⟨anti.paidSuccessorAfterRefusalAntiRetaliation_exact,
    paidSuccessorAfterRefusalAntiRetaliationAuditAt oldVisit sourceIndex
      (m14RefusalSuccessorIndexAt boundary),
    proofCarryingPaidSuccessorAfterRefusalAntiRetaliationDirectConsumer,
    m14RefusalSourceCurrent_eq_rightPaymentCurrent oldVisit sourceIndex
      boundary,
    m14RefusalSourcePayment_eq_rightPayment oldVisit sourceIndex boundary,
    m14RefusalSourcePaymentNext_eq_platformChannelNext oldVisit sourceIndex
      boundary,
    m14RefusalPlatformChannelNext_isTargetOuterOccurrence oldVisit sourceIndex
      boundary,
    m14RefusalAuthorityRead_injective oldVisit sourceIndex boundary,
    m14Refusal_source_target_difference oldVisit sourceIndex boundary⟩

end
end Interface
end Refusal
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface.m14RefusalAuthorityRead_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface.m14RefusalSourceCurrent_eq_rightPaymentCurrent
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface.m14RefusalSourcePayment_eq_rightPayment
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface.m14RefusalPlatformChannelNext_isTargetOuterOccurrence
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface.sourceGeneratedM14RefusalSuccessor_directConsumer
