import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Identity.Death.Field.Producer.SourceGeneratedContributionCapacityPaidDeathField
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Payment.Terminal.Consumer.ProofCarryingContributionCapacityJointSettlementPaidTail

/-!
# Paid death-field publication response

The installed current-twelve death-field demand and the existing rich
joint-settlement action Payment form one exact publication Payment.  Reading
the pre-action field yields the local time chart `1`; the Payment's own
`NextPaidBy` lands at A14; the A14 complete frontier recomputes the
current-relative locus as `0`.  The separate faithful-terminal handoff then
continues to A15 and its first post Payment generates A16.

The response is downstream data.  The fixed-point fibre is merely the
dependent equality `1 = 0`, hence empty; that emptiness neither removes the
non-fixed publication Payment nor generates any alternative next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityDeathFieldPublication

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14SourceGeneratedContributionCapacityJointSettlementCompiler
open M14SourceGeneratedContributionCapacityJointSettlementRoot
open M14SourceGeneratedContributionCapacityJointSettlementState
open M14SourceGeneratedContributionCapacityJointSettlementCrossRootPayment
open M14SourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceipt
open M14ProofCarryingContributionCapacityJointSettlementPaidTail
open M14SourceGeneratedContributionCapacityJointSettlementGateFrontier
open M14SourceGeneratedContributionCapacityPaidDeathField
open M14SourceGeneratedContributionCapacityPaidDeathField.ExactContributionCapacityPreLocusPaymentAt
open M14SourceGeneratedContributionCapacityPaidDeathField.SourceGeneratedContributionCapacityMinimalDeathLocusAt

/-! ## Target-current recomputation -/

/-- Recompute the death locus at the Payment-generated A14 current.  No target
or death witness is accepted at the producer mouth. -/
structure SourceGeneratedContributionCapacityTargetDeathRecomputationAt
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (payment : ExactContributionCapacityPublicationPaymentAt oldVisit
      sourceIndex) : Type 24 where
  private mk ::
  nextIsTerminalCurrent : payment.nextPaidBy =
    ⟨(generatedContributionCapacityJointSettlementPaidActionAt oldVisit
        sourceIndex).target.TargetV,
      (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
        sourceIndex).target.targetRoot.toAuthoritativeRoot,
      (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
        sourceIndex).target.targetVisit⟩
  targetSubstantiveDeath : Nonempty
    (contributionCapacityJointSettlementTerminalFrontierAt oldVisit
      sourceIndex).SubstantiveDeathAt
  everyTargetRowTerminal : ∀ entryIndex : Fin 2,
    (contributionCapacityJointSettlementTerminalRootEventAt oldVisit
      sourceIndex).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex) =
      .terminal
        ((contributionCapacityJointSettlementTerminalExactAt oldVisit
          sourceIndex).ledgerEvolution.discharge
            (contributionCapacityJointSettlementLiveEntryAt oldVisit
              entryIndex))
  targetNoLocalSuccessor : IsEmpty
    (SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacityJointSettlementTerminalRootEventAt oldVisit
        sourceIndex).occurrence
      (contributionCapacityJointSettlementTerminalRootEventAt oldVisit
        sourceIndex).wholeLedgerWriteBack)

def sourceGeneratedContributionCapacityTargetDeathRecomputationAt
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (payment : ExactContributionCapacityPublicationPaymentAt oldVisit
      sourceIndex) :
    SourceGeneratedContributionCapacityTargetDeathRecomputationAt payment where
  nextIsTerminalCurrent := payment.nextPaidBy_isTerminalCurrent
  targetSubstantiveDeath :=
    contributionCapacityJointSettlementTerminalDeath_substantive oldVisit
      sourceIndex
  everyTargetRowTerminal :=
    contributionCapacityJointSettlementTerminalEveryRow_terminal oldVisit
      sourceIndex
  targetNoLocalSuccessor :=
    contributionCapacityJointSettlementTerminalGate_noLocalSuccessor oldVisit
      sourceIndex

/-! ## Actual paid response -/

/-- Downstream publication response.  Its sole Payment field is the already
sealed exact publication Payment; read, next and target locus are recomputed
and only their equations are retained. -/
structure SourceGeneratedContributionCapacityDeathPublicationResponseAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Type 25 where
  private mk ::
  payment : ExactContributionCapacityPublicationPaymentAt oldVisit sourceIndex
  paymentExact : payment =
    exactContributionCapacityPreLocusPaymentAt oldVisit sourceIndex
  sourceMinimal : SourceGeneratedContributionCapacityMinimalDeathLocusAt
    oldVisit sourceIndex
  sourceMinimalExact : sourceMinimal =
    sourceGeneratedContributionCapacityMinimalDeathLocusAt oldVisit sourceIndex
  targetRecomputation :
    SourceGeneratedContributionCapacityTargetDeathRecomputationAt payment
  readExact : payment.readBy = sourceMinimal.observerTimeChart
  targetLocusExact : payment.targetDeathLocus = 0

def sourceGeneratedContributionCapacityDeathPublicationResponseAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceGeneratedContributionCapacityDeathPublicationResponseAt oldVisit
      sourceIndex :=
  let payment := exactContributionCapacityPreLocusPaymentAt oldVisit sourceIndex
  let minimal :=
    sourceGeneratedContributionCapacityMinimalDeathLocusAt oldVisit sourceIndex
  let recomputation :=
    sourceGeneratedContributionCapacityTargetDeathRecomputationAt payment
  { payment := payment
    paymentExact := rfl
    sourceMinimal := minimal
    sourceMinimalExact := rfl
    targetRecomputation := recomputation
    readExact := rfl
    targetLocusExact := rfl }

namespace SourceGeneratedContributionCapacityDeathPublicationResponseAt

variable {oldVisit : OldVisit} {sourceIndex : Nat}

def readBy
    (response : SourceGeneratedContributionCapacityDeathPublicationResponseAt
      oldVisit sourceIndex) : Nat :=
  response.payment.readBy

def nextPaidBy
    (response : SourceGeneratedContributionCapacityDeathPublicationResponseAt
      oldVisit sourceIndex) :=
  response.payment.nextPaidBy

def recomputedDeathLocus
    (response : SourceGeneratedContributionCapacityDeathPublicationResponseAt
      oldVisit sourceIndex) : Nat :=
  response.payment.targetDeathLocus

@[simp] theorem readBy_eq_one
    (response : SourceGeneratedContributionCapacityDeathPublicationResponseAt
      oldVisit sourceIndex) :
    response.readBy = 1 :=
  response.payment.readBy_eq_one

@[simp] theorem recomputedDeathLocus_eq_zero
    (response : SourceGeneratedContributionCapacityDeathPublicationResponseAt
      oldVisit sourceIndex) :
    response.recomputedDeathLocus = 0 :=
  response.payment.targetDeathLocus_eq_zero

theorem nextPaidBy_isTerminalCurrent
    (response : SourceGeneratedContributionCapacityDeathPublicationResponseAt
      oldVisit sourceIndex) :
    response.nextPaidBy =
      ⟨(generatedContributionCapacityJointSettlementPaidActionAt oldVisit
          sourceIndex).target.TargetV,
        (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
          sourceIndex).target.targetRoot.toAuthoritativeRoot,
        (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
          sourceIndex).target.targetVisit⟩ :=
  response.payment.nextPaidBy_isTerminalCurrent

end SourceGeneratedContributionCapacityDeathPublicationResponseAt

/-! ## Fixed point is readout-only -/

abbrev ContributionCapacityPublicationFixedPointAt
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (response : SourceGeneratedContributionCapacityDeathPublicationResponseAt
      oldVisit sourceIndex) :=
  response.readBy = response.recomputedDeathLocus

theorem contributionCapacityPublicationFixedPoint_isEmpty
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (response : SourceGeneratedContributionCapacityDeathPublicationResponseAt
      oldVisit sourceIndex) :
    IsEmpty (ContributionCapacityPublicationFixedPointAt response) := by
  constructor
  intro fixed
  change response.payment.readBy = response.payment.targetDeathLocus at fixed
  rw [response.payment.readBy_eq_one,
    response.payment.targetDeathLocus_eq_zero] at fixed
  omega

theorem nonFixedPublicationPayment_remainsInhabited
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Nonempty
      (ExactContributionCapacityPublicationPaymentAt oldVisit sourceIndex) :=
  ⟨exactContributionCapacityPreLocusPaymentAt oldVisit sourceIndex⟩

theorem publicationResponse_remainsInhabited_when_fixedPointEmpty
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Nonempty
        (SourceGeneratedContributionCapacityDeathPublicationResponseAt oldVisit
          sourceIndex) ∧
      IsEmpty
        (ContributionCapacityPublicationFixedPointAt
          (sourceGeneratedContributionCapacityDeathPublicationResponseAt
            oldVisit sourceIndex)) :=
  ⟨⟨sourceGeneratedContributionCapacityDeathPublicationResponseAt oldVisit
      sourceIndex⟩,
    contributionCapacityPublicationFixedPoint_isEmpty _⟩

/-! ## Publication does not freeze the world -/

theorem publicationTerminalHandoff_generatesFirstPostCurrent
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    contributionCapacityJointSettlementTerminalNextPaidBy oldVisit sourceIndex =
      contributionCapacityJointSettlementFirstPostRootCurrentAt oldVisit
        sourceIndex :=
  contributionCapacityJointSettlementTerminalNextPaidBy_exact oldVisit
    sourceIndex

theorem publicationFirstPostPayment_generatesNext
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    let consumed :=
      (proofCarryingContributionCapacityJointSettlementPaidTailAt oldVisit
        sourceIndex).2.firstPostPaidStep
    HEq consumed.2.sourcePayment.nextPaidBy
      (M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent.SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
        consumed.2.targetCurrent).occurrence :=
  (proofCarryingContributionCapacityJointSettlementPaidTailAt oldVisit
    sourceIndex).2.firstPostPayment_generatesCanonicalNext

theorem publicationFixedPoint_hasNoPaymentNextOrWorldAuthority
    (oldVisit : OldVisit) (sourceIndex : Nat) : True := by
  let response :=
    sourceGeneratedContributionCapacityDeathPublicationResponseAt oldVisit
      sourceIndex
  fail_if_success exact
    (response.readBy : ExactContributionCapacityPublicationPaymentAt oldVisit
      sourceIndex)
  fail_if_success exact response.fixedPoint.nextPaidBy
  fail_if_success exact response.fixedPoint.wholeLedgerWriteBack
  fail_if_success exact response.fixedPoint.worldAuthority
  fail_if_success exact response.fixedPoint.future
  trivial

end
end M14SourceGeneratedContributionCapacityDeathFieldPublication
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityDeathFieldPublication.sourceGeneratedContributionCapacityDeathPublicationResponseAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityDeathFieldPublication.contributionCapacityPublicationFixedPoint_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityDeathFieldPublication.publicationFirstPostPayment_generatesNext
