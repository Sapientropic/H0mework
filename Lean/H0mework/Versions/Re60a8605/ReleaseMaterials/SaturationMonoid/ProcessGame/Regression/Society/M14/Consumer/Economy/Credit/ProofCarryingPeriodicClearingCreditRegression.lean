import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Credit.PeriodicClearingCreditClaimLifecycle
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Clearing.Backstop.ProofCarryingPeriodicClearingBackstopRegression

/-!
# M14 direct consumer for periodic proof-carrying clearing credit

This certificate consumes the canonical C5 periodic backstop certificate and
the C6 dependent credit child at the same depth.  Credit does not introduce a
second occurrence: periodicity is read directly from the existing C5
backstop occurrence.

The local exchange content and the living-root claim remain separate typed
readouts.  The certificate exports their respective provenance but contains
no content-to-claim equality or transporter.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPeriodicClearingCreditRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Renewal Revision
open Price Money Clearing
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression
open M4AutomaticFullFulfillmentRegression
open M9ProofCarryingRenewalInquiryRoot
open M14ClearingConsumerDeath
open M14SourceGeneratedClearingBackstopActivation
open M14SourceClearingBackstopCreditStanding
open M14UBIPeriodicRootHistory
open M14PeriodicClearingBackstopRenewal
open M14ProofCarryingPeriodicClearingBackstopRegression
open M14PeriodicClearingCreditClaimLifecycle

/-! ## Prop-only direct certificate -/

structure ProofCarryingPeriodicClearingCreditCertificateAt
    (depth : Nat) : Prop where
  priorBackstop : ProofCarryingPeriodicClearingBackstopCertificateAt depth
  actualCredit : Nonempty
    (SourceGeneratedProofCarryingPeriodicClearingCreditAt depth)
  sourceStandingAndInterest :
    let credit :=
      sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
    credit.backstop =
        sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth ∧
      credit.standing = sourceGeneratedClearingBackstopCreditStanding ∧
      credit.standing.tender = backstopTender ∧
      credit.borrower = borrowerActor ∧
      credit.creditor = creditorActor ∧
      credit.borrower ≠ credit.creditor ∧
      credit.relation = creditRelation ∧
      relationCompiler.GeneratedInterestAt credit.borrower credit.relation ∧
      IsEmpty
        (relationCompiler.GeneratedInterestAt credit.creditor credit.relation) ∧
      PurchasingPowerStandingAt.nextGeneratedState credit.standing =
        credit.backstop.localActivation.nextGeneratedState
  standingProvenance :
    let credit :=
      sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
    credit.backstop.installed.payload.sourceSeed =
        sourceGeneratedClearingBackstopExactSeed ∧
      credit.standing.tender = backstopTender ∧
      HEq credit.standing.counterpartyAcceptance
        backstopCounterpartyAcceptedTender ∧
      backstopTender.sourceEvent =
        M3FiniteExchangeFixture.P.boundarySource
          canonicalAClearingFace.counterpartyConsumer.event ∧
      backstopCounterpartyAcceptedTender.reciprocalAssumption =
        BearerAssumption.accepted
          backstopCounterpartyAcceptedTender.acceptanceReceipt ∧
      (exactCounterpartyObligation
          sourceGeneratedClearingBackstopExactSeed).content =
        backstopTender.medium ∧
      (exactCounterpartyObligation
          sourceGeneratedClearingBackstopExactSeed).bearer =
        exchangeLaw.bearerOfActor creditorActor ∧
      partialOpenB.obligation.beneficiary =
        exchangeLaw.protectedInterestOfActor creditorActor ∧
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        partialBResidualConsumerCompiler.activationSeedAt
          Lifecycle.actualEventGame.source state
          (PurchasingPowerStandingAt.renewalEvent credit.standing)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence
        M3FiniteExchangeFixture.V
        (M3FiniteExchangeFixture.P.boundarySource
          canonicalAClearingFace.counterpartyConsumer.event)
        partialOpenB.obligation) ∧
      (PurchasingPowerStandingAt.nextGeneratedState
        credit.standing).generated =
          .step
            (partialOccurrence.generatedState settlementCompiler).generated
            fulfillB ∧
      fulfillB.target.history =
        (partialOccurrence.current settlementCompiler).history ++
          [fulfillB.lifecycleEvent]
  downsideBearer :
    let credit :=
      sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
    credit.downsideBearer = partialOpenB.obligation.bearer ∧
      credit.downsideBearer =
        exchangeLaw.bearerOfActor credit.borrower ∧
      credit.downsideBearer =
        Lifecycle.ActorBearer.target Lifecycle.TargetToken.t1
  separateLocalContentAndRootClaim :
    let credit :=
      sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
    credit.localObligationContent = partialOpenB.obligation.content ∧
      credit.sourceClaim =
        credit.backstop.installed.payload.sourceEntry.claim ∧
      credit.futureClaim = credit.backstop.appliedReform.targetEntry.claim
  sameClaimRestructuring :
    let credit :=
      sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
    credit.debtLineage = credit.backstop.appliedReform.debtLineage ∧
      credit.sourceClaim = credit.futureClaim ∧
      credit.rowEvolution = credit.backstop.appliedReform.rowEvolution ∧
      credit.rowEvolution = LedgerEntryEvolutionAt.carried rfl HEq.rfl ∧
      credit.operationalDisposition = credit.rootConsumer.exactDisposition ∧
      credit.operationalDisposition =
        credit.backstop.installed.operationalAuthority.disposition ∧
      credit.backstop.installed.payload.sourceEntry.progressBudget = 2 ∧
      credit.backstop.appliedReform.targetEntry.progressBudget = 2 ∧
      credit.backstop.appliedReform.targetEntry.progressBudget =
        credit.backstop.installed.payload.sourceEntry.progressBudget ∧
      (¬ (credit.backstop.appliedReform.targetEntry.progressBudget <
        credit.backstop.installed.payload.sourceEntry.progressBudget)) ∧
      credit.generatedRootNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      credit.backstop.appliedReform.generatedNext.visit =
        temporalVisitAt (depth + 1) ∧
      credit.backstop.installed.RootAnswerAndNextFactorizes
  rootWriteAndConsumer :
    let credit :=
      sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
    credit.rootConsumer = credit.backstop.rootConsumer ∧
      credit.operationalDisposition = credit.rootConsumer.exactDisposition ∧
      credit.operationalDisposition =
        credit.backstop.installed.operationalAuthority.disposition ∧
      credit.backstop.appliedReform.residualRow =
        credit.backstop.installed.temporalSelectedRow ∧
      credit.backstop.appliedReform.residualRow.sourceRow.CommutesWithWorld ∧
      credit.backstop.appliedReform.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      credit.backstop.installed.RootAnswerAndNextFactorizes ∧
      credit.generatedRootNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      credit.backstop.appliedReform.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface ∧
      credit.backstop.appliedReform.generatedNext.visit =
        temporalVisitAt (depth + 1)
  defaultAndControls :
    let credit :=
      sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
    credit.downsideBearer = partialOpenB.obligation.bearer ∧
      credit.defaultOccurrence = sourceGeneratedClearingConsumerDeath ∧
      IsEmpty (FulfilledExchangeLegAt settlementCompiler partialOccurrence
        (.b : Leg)) ∧
      Nonempty (AutomaticFullFulfillment.FulfilledSlotAt
        (exchangeLaw := exchangeLaw) exactExchangeSeed
        credit.backstop.localActivation.nextGeneratedState.current
        (.b : Leg)) ∧
      IsEmpty
        { obligation : AdmittedObligation M3FiniteExchangeFixture.V //
          credit.backstop.localActivation.nextGeneratedState.current.slots[
            exactExchangeSeed.obligationSlotIndex exchangeCompiler
              (.b : Leg)]? = some (ObligationSlot.live obligation) } ∧
      Nonempty (RenewalResponsibilityConsumerAt
        credit.backstop.installed.operationalAuthority) ∧
      (¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
        (activation.openSettlement residualConsumerCompiler).leg = .b) ∧
      (¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
        activation.occurrence residualConsumerCompiler = partialOccurrence) ∧
      canonicalAClearingFace.oneSidedEdge = fulfillA ∧
      IsEmpty (AutomaticFullFulfillment.FulfilledSlotAt
        (exchangeLaw := exchangeLaw) exactExchangeSeed
        canonicalAClearingFace.oneSidedEdge.target (.b : Leg)) ∧
      IsEmpty (OpenSettlementAt automaticCompiler automaticOccurrence) ∧
      Nonempty (OpenSettlementAt nilOpenCompiler nilOpenOccurrence) ∧
      IsEmpty (FulfilledExchangeLegAt nilOpenCompiler nilOpenOccurrence
        nilOpenA.leg) ∧
      (¬ Nonempty
        (FullyFulfilledExchangeAt nilOpenCompiler nilOpenOccurrence))
  fixedCarriedNotHaircut :
    let credit :=
      sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
    credit.rowEvolution = LedgerEntryEvolutionAt.carried rfl HEq.rfl ∧
      credit.backstop.appliedReform.targetEntry.progressBudget = 2 ∧
      credit.backstop.installed.payload.sourceEntry.progressBudget = 2 ∧
      (¬ (credit.backstop.appliedReform.targetEntry.progressBudget <
        credit.backstop.installed.payload.sourceEntry.progressBudget))
  occurrenceInjective : Function.Injective
    periodicClearingBackstopOccurrenceAt
  adjacentDistinct : periodicClearingBackstopOccurrenceAt depth ≠
    periodicClearingBackstopOccurrenceAt (depth + 1)
  noSingleEternity :
    ¬ ∃ occurrence : AnyPeriodicClearingBackstopOccurrence,
      ∀ index : Nat,
        periodicClearingBackstopOccurrenceAt index = occurrence

/-- The direct consumer has only the visit depth in its public mouth. -/
theorem proofCarryingPeriodicClearingCreditDirectConsumer (depth : Nat) :
    ProofCarryingPeriodicClearingCreditCertificateAt depth where
  priorBackstop :=
    proofCarryingPeriodicClearingBackstopDirectConsumer depth
  actualCredit := every_generated_period_has_actual_clearing_credit depth
  sourceStandingAndInterest :=
    periodic_clearingCredit_source_standing_and_interest_exact depth
  standingProvenance :=
    periodic_clearingCredit_standing_provenance_exact depth
  downsideBearer := periodic_clearingCredit_downside_bearer_exact depth
  separateLocalContentAndRootClaim :=
    periodic_clearingCredit_separate_local_content_and_root_claim depth
  sameClaimRestructuring :=
    periodic_clearingCredit_same_claim_restructuring_exact depth
  rootWriteAndConsumer :=
    periodic_clearingCredit_root_write_and_consumer_exact depth
  defaultAndControls :=
    periodic_clearingCredit_default_and_controls_exact depth
  fixedCarriedNotHaircut :=
    fixed_row_is_identity_carry_not_strict_haircut depth
  occurrenceInjective := periodicClearingBackstopOccurrenceAt_injective
  adjacentDistinct := adjacentClearingBackstopOccurrences_distinct depth
  noSingleEternity :=
    no_single_clearingBackstop_occurrence_carries_all_depths

theorem periodicClearingCreditDirectConsumerMouthIsDepthOnly
    (depth : Nat) : True := by
  let certificate :=
    proofCarryingPeriodicClearingCreditDirectConsumer depth
  fail_if_success exact certificate.submittedBackstop
  fail_if_success exact certificate.submittedStanding
  fail_if_success exact certificate.submittedTender
  fail_if_success exact certificate.submittedAcceptance
  fail_if_success exact certificate.submittedClaim
  fail_if_success exact certificate.localContentToRootClaimEquality
  fail_if_success exact certificate.noSource
  fail_if_success exact certificate.creditOccurrence
  fail_if_success exact certificate.creditKind
  fail_if_success exact certificate.defaultKind
  fail_if_success exact certificate.riskPool
  fail_if_success exact certificate.haircut
  fail_if_success exact certificate.lossMutualization
  fail_if_success exact certificate.eleventhCoordinate
  fail_if_success exact certificate.secondRoot
  fail_if_success exact certificate.secondOccurrence
  fail_if_success exact certificate.parallelRun
  fail_if_success exact certificate.ledgerCandidate
  fail_if_success exact certificate.coveragePremise
  fail_if_success exact certificate.scheduler
  fail_if_success exact certificate.completedFuture
  trivial

end
end M14ProofCarryingPeriodicClearingCreditRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicClearingCreditRegression.proofCarryingPeriodicClearingCreditDirectConsumer
