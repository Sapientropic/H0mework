import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Producer.SourceGeneratedContributionCapacityNewCompatibleFutureBirth

/-!
# Independent necessity of payment--exit--bearer alignment

At one existing positive reopening occurrence, the installed `.renewal` face
generates the canonical periodic actual-service exit and the installed
`.birthBearerExit` face reindexes that very exit to the residual's existing
bearer.  The outer native Payment, Fin-3 whole-ledger write, residual row,
answer consumer and generated next are therefore shared before the alignment
question is asked.

The negative carrier keeps the original `.t0` exit, its embedded M9 Payment,
route, service, actionable renewal and capacity one.  Its exact payment
counterparty is nevertheless `.t1`, the bearer of the admitted residual, so
the source payment-counterparty / exit-worker / residual-bearer alignment
fibre is empty.  The existing root-installed bearer face is the positive
comparator.  No root, occurrence, ledger, actor selector, registry or future
table is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPaymentExitBearerAlignmentIndependentNecessity

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M9ProofCarryingRenewalInquiryRoot
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M10OccurrenceCapacityDebitedRunFixture
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacityReopeningState
open M14SourceGeneratedContributionCapacityReopeningResidualCarry
open M14SourceGeneratedContributionCapacityReopeningRuntimePayment
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityTargetOriginOrBirth
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth

abbrev AlignmentReopeningRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningRootAt
    oldVisit sourceIndex

abbrev AlignmentReopeningSourceEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
    oldVisit sourceIndex

abbrev CanonicalFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
    sourceIndex index

def canonicalFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalFutureBirthAt oldVisit sourceIndex index :=
  sourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
    sourceIndex index

/-! ## The two existing faces of one outer occurrence -/

/-- The negative face is the existing root-installed renewal at current
`index + 1`; its `rootRead` is the only source of the legacy actual exit. -/
def paymentExitAlignmentRenewalFaceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeRootSemanticFaceAt
      (AlignmentReopeningRootAt oldVisit sourceIndex)
      (contributionCapacityReopenedVisitAt oldVisit sourceIndex index) :=
  contributionCapacityReopeningRenewalFaceAt oldVisit sourceIndex (index + 1)

/-- Read the negative actual exit from the existing `.renewal` face.  The
helper theorem used here is itself exactly that face's `rootRead`. -/
def paymentExitAlignmentLegacyActualExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PeriodicActualServiceExitAt
      (contributionCapacityFutureBirthDepth sourceIndex index) :=
  Classical.choice
    (contributionCapacityReopeningRootGeneratedRenewalAt oldVisit sourceIndex
      (index + 1))

/-- The legacy root read is the unique canonical actual exit at this depth. -/
theorem paymentExitAlignmentLegacyActualExit_eq_canonical
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    paymentExitAlignmentLegacyActualExitAt oldVisit sourceIndex index =
      periodicActualServiceExitAt
        (contributionCapacityFutureBirthDepth sourceIndex index) :=
  periodicActualServiceExitAt_eq_canonical _

/-- Hence the negative root read and the future-birth carrier use one exact
embedded M9 Payment/settlement authority, not two selected witnesses. -/
theorem paymentExitAlignmentLegacyActualExit_eq_futureBirth
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (futureBirth : CanonicalFutureBirthAt oldVisit sourceIndex index) :
    paymentExitAlignmentLegacyActualExitAt oldVisit sourceIndex index =
      futureBirth.actualExit :=
  (paymentExitAlignmentLegacyActualExit_eq_canonical oldVisit sourceIndex
    index).trans (periodicActualServiceExitAt_eq_canonical _).symm

/-- The positive face is already installed in the same reopening root and
at the same visit as the negative renewal face. -/
def paymentExitAlignmentBearerFaceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeRootSemanticFaceAt
      (AlignmentReopeningRootAt oldVisit sourceIndex)
      (contributionCapacityReopenedVisitAt oldVisit sourceIndex index) :=
  contributionCapacityFutureBirthBearerExitFaceAt oldVisit sourceIndex index

/-! ## Exact source-payment incidence -/

/-- Exact alignment of one embedded M9 Payment occurrence, its exit worker,
and the bearer of the residual obligation admitted by the outer birth.  The
worker is an index used only by the two fixed aliases below; the sole public
producer never accepts it from a caller. -/
structure ExactPaymentExitBearerAlignmentAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (futureBirth : CanonicalFutureBirthAt oldVisit sourceIndex index)
    (embeddedPayment : PeriodicSourceBackedPaymentAt
      (contributionCapacityFutureBirthDepth sourceIndex index))
    (exitWorker : exitRelationCompiler.Actor) : Type 20 where
  private mk ::
  installedBearerExit : SourceGeneratedContributionCapacityBirthBearerExitAt
    (contributionCapacityFutureBirthDepth sourceIndex index)
    futureBirth.actualExit
  installedBearerExitFromRootRead : installedBearerExit =
    Classical.choice futureBirth.installedBearerExitAuthority.down
  embeddedPaymentMatchesInstalled : embeddedPayment =
    installedBearerExit.existingPaymentOccurrence
  embeddedPaymentExact :
    embeddedPayment = futureBirth.actualExit.paymentOccurrence
  paymentCounterparty_eq_exitWorker :
    PurchasingPowerStandingAt.counterparty
        exitCapacityProgram.purchasingPowerStanding =
      exitWorker
  exitWorkerBearer_eq_residualBearer :
    exchangeLaw.bearerOfActor exitWorker =
      futureBirth.birthAdmission.obligation.bearer

abbrev LegacyPaymentExitBearerAlignmentAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (futureBirth : CanonicalFutureBirthAt oldVisit sourceIndex index) :=
  ExactPaymentExitBearerAlignmentAt futureBirth
    (paymentExitAlignmentLegacyActualExitAt oldVisit sourceIndex index
      ).paymentOccurrence worker

abbrev PositivePaymentExitBearerAlignmentAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (futureBirth : CanonicalFutureBirthAt oldVisit sourceIndex index) :=
  ExactPaymentExitBearerAlignmentAt futureBirth
    (paymentExitAlignmentLegacyActualExitAt oldVisit sourceIndex index
      ).paymentOccurrence birthBearerWorker

/-- The exact Payment counterparty is `.t1`, while the legacy exit worker is
`.t0`.  This is the sole deleted authority coordinate. -/
theorem paymentCounterparty_ne_legacyExitWorker :
    PurchasingPowerStandingAt.counterparty
        exitCapacityProgram.purchasingPowerStanding ≠
      worker := by
  intro equality
  have values := congrArg Subtype.val equality
  cases values

theorem legacyPaymentExitBearerAlignment_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (futureBirth : CanonicalFutureBirthAt oldVisit sourceIndex index) :
    IsEmpty (LegacyPaymentExitBearerAlignmentAt futureBirth) :=
  ⟨fun alignment =>
    paymentCounterparty_ne_legacyExitWorker
      alignment.paymentCounterparty_eq_exitWorker⟩

/-- Positive comparator generated by the already installed bearer face.  It
uses the negative face's exact embedded Payment occurrence. -/
def positivePaymentExitBearerAlignmentAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (futureBirth : CanonicalFutureBirthAt oldVisit sourceIndex index) :
    PositivePaymentExitBearerAlignmentAt futureBirth := by
  let installedBearerExit :=
    Classical.choice futureBirth.installedBearerExitAuthority.down
  have legacyExact :=
    paymentExitAlignmentLegacyActualExit_eq_futureBirth futureBirth
  have birthBearerIsParent :
      futureBirth.birthAdmission.obligation.bearer =
        sourceGeneratedLossAllocationMaterial.parentBearer :=
    futureBirth.birthAdmission.bearerExisting.trans
      (SourceGeneratedReopeningResidualCarryAt.residual_bearer_is_existing_parent
        (oldVisit := oldVisit))
  exact
    { installedBearerExit := installedBearerExit
      installedBearerExitFromRootRead := rfl
      embeddedPaymentMatchesInstalled :=
        (congrArg (fun actualExit => actualExit.paymentOccurrence)
          legacyExact).trans
          installedBearerExit.existingPaymentOccurrence_eq.symm
      embeddedPaymentExact :=
        congrArg (fun actualExit => actualExit.paymentOccurrence) legacyExact
      paymentCounterparty_eq_exitWorker :=
        installedBearerExit.standingCounterparty_eq_worker
      exitWorkerBearer_eq_residualBearer :=
        installedBearerExit.workerBearer_eq_parent.trans
          birthBearerIsParent.symm }

/-! ## Full source-generated countermodel -/

structure SourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 22 where
  private mk ::
  futureBirth : CanonicalFutureBirthAt oldVisit sourceIndex index
  futureBirthExact : futureBirth =
    canonicalFutureBirthAt oldVisit sourceIndex index
  outerRootEvent : ExactTemporalCausalRootEventAt
    (AlignmentReopeningRootAt oldVisit sourceIndex
      ).toAuthoritativeRoot.toLedgerRoot
    (contributionCapacityReopenedVisitAt oldVisit sourceIndex index)
  outerRootEventExact : outerRootEvent = futureBirth.laterRootEvent
  outerRuntimePayment :
    SourceGeneratedContributionCapacityReopeningRuntimePaymentAt oldVisit
      sourceIndex index
  outerRuntimePaymentExact : outerRuntimePayment = futureBirth.runtimePayment
  renewalFace : SourceNativeRootSemanticFaceAt
    (AlignmentReopeningRootAt oldVisit sourceIndex)
    (contributionCapacityReopenedVisitAt oldVisit sourceIndex index)
  renewalFaceExact : renewalFace =
    paymentExitAlignmentRenewalFaceAt oldVisit sourceIndex index
  legacyRootRead : Nonempty (PeriodicActualServiceExitAt
    (contributionCapacityFutureBirthDepth sourceIndex index))
  legacyRootReadExact : legacyRootRead =
    contributionCapacityReopeningRootGeneratedRenewalAt oldVisit sourceIndex
      (index + 1)
  legacyActualExit : PeriodicActualServiceExitAt
    (contributionCapacityFutureBirthDepth sourceIndex index)
  legacyActualExitExact : legacyActualExit =
    paymentExitAlignmentLegacyActualExitAt oldVisit sourceIndex index
  legacyActualExitSharesFutureBirth :
    legacyActualExit = futureBirth.actualExit
  embeddedM9Payment : PeriodicSourceBackedPaymentAt
    (contributionCapacityFutureBirthDepth sourceIndex index)
  embeddedM9PaymentExact : embeddedM9Payment =
    legacyActualExit.paymentOccurrence
  embeddedM9RootEvent : ExactTemporalCausalRootEventAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot
    (temporalVisitAt
      (contributionCapacityFutureBirthDepth sourceIndex index))
  embeddedM9RootEventExact : embeddedM9RootEvent =
    embeddedM9Payment.rootOccurrence
  birthAdmission :
    ExactGeneratedContributionCapacityResidualBirthAdmissionAt oldVisit
  birthAdmissionExact : birthAdmission = futureBirth.birthAdmission
  birthAdmissionSourceExact : birthAdmission =
    sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
  birthObligationExact : birthAdmission.obligation =
    contributionCapacityU8ObligationAt oldVisit
      exactSourceGeneratedLossAllocationMaterialWitness
      (contributionCapacityU8GeneratedResidual oldVisit)
  birthObligationBearerExact : birthAdmission.obligation.bearer =
    contributionCapacityU8BearerAt oldVisit
      exactSourceGeneratedLossAllocationMaterialWitness
      (contributionCapacityU8GeneratedResidual oldVisit)
  residualCarry : SourceGeneratedReopeningResidualCarryAt oldVisit sourceIndex
    (AlignmentReopeningSourceEventAt oldVisit sourceIndex) index
  residualCarryExact : residualCarry = futureBirth.residualCarry
  residualCarryRuntimeExact : residualCarry =
    contributionCapacityReopeningRuntimeResidualCarryAt oldVisit sourceIndex
      index
  carriedResidualBearerExact :
    contributionCapacityU8BearerAt oldVisit
        exactSourceGeneratedLossAllocationMaterialWitness
        (contributionCapacityU8GeneratedResidual oldVisit) =
      sourceGeneratedLossAllocationMaterial.parentBearer
  birthBearerCarriedParentExact : birthAdmission.obligation.bearer =
    sourceGeneratedLossAllocationMaterial.parentBearer
  residualAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (AlignmentReopeningRootAt oldVisit sourceIndex)
    (contributionCapacityReopenedVisitAt oldVisit sourceIndex index)
    (contributionCapacityReopeningTargetResidual oldVisit)
  residualAuthorityExact : residualAuthority = futureBirth.laterAuthority
  residualConsumer : SourceNativeInquiryAnswerConsumerAt ()
    (contributionCapacityReopenedInquiryEventAt oldVisit sourceIndex index)
    (contributionCapacityReopeningTargetResidual oldVisit)
    (contributionCapacityReopenedAnswerFaceAt oldVisit sourceIndex index)
  residualConsumerExact : residualConsumer = futureBirth.laterConsumer
  bearerFace : SourceNativeRootSemanticFaceAt
    (AlignmentReopeningRootAt oldVisit sourceIndex)
    (contributionCapacityReopenedVisitAt oldVisit sourceIndex index)
  bearerFaceExact : bearerFace =
    paymentExitAlignmentBearerFaceAt oldVisit sourceIndex index
  alignedBearerExit : SourceGeneratedContributionCapacityBirthBearerExitAt
    (contributionCapacityFutureBirthDepth sourceIndex index)
    futureBirth.actualExit
  alignedBearerExitExact : alignedBearerExit = futureBirth.bearerExit
  alignedBearerExitFromRootRead : alignedBearerExit =
    Classical.choice futureBirth.installedBearerExitAuthority.down
  deletedLegacyAlignment :
    IsEmpty (LegacyPaymentExitBearerAlignmentAt futureBirth)
  positiveAlignment : PositivePaymentExitBearerAlignmentAt futureBirth

/-- Sole producer.  The three indices select one already generated reopening
occurrence; no Payment, exit, worker, bearer, row, consumer or next is a
caller premise. -/
def sourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt oldVisit
      sourceIndex index := by
  let futureBirth := canonicalFutureBirthAt oldVisit sourceIndex index
  let legacyRootRead :=
    contributionCapacityReopeningRootGeneratedRenewalAt oldVisit sourceIndex
      (index + 1)
  let legacyActualExit :=
    paymentExitAlignmentLegacyActualExitAt oldVisit sourceIndex index
  exact
    { futureBirth := futureBirth
      futureBirthExact := rfl
      outerRootEvent := futureBirth.laterRootEvent
      outerRootEventExact := rfl
      outerRuntimePayment := futureBirth.runtimePayment
      outerRuntimePaymentExact := rfl
      renewalFace :=
        paymentExitAlignmentRenewalFaceAt oldVisit sourceIndex index
      renewalFaceExact := rfl
      legacyRootRead := legacyRootRead
      legacyRootReadExact := rfl
      legacyActualExit := legacyActualExit
      legacyActualExitExact := rfl
      legacyActualExitSharesFutureBirth :=
        paymentExitAlignmentLegacyActualExit_eq_futureBirth futureBirth
      embeddedM9Payment := legacyActualExit.paymentOccurrence
      embeddedM9PaymentExact := rfl
      embeddedM9RootEvent := legacyActualExit.paymentOccurrence.rootOccurrence
      embeddedM9RootEventExact := rfl
      birthAdmission := futureBirth.birthAdmission
      birthAdmissionExact := rfl
      birthAdmissionSourceExact := rfl
      birthObligationExact := futureBirth.birthAdmission.obligationExact
      birthObligationBearerExact := futureBirth.birthAdmission.bearerExisting
      residualCarry := futureBirth.residualCarry
      residualCarryExact := rfl
      residualCarryRuntimeExact := rfl
      carriedResidualBearerExact :=
        SourceGeneratedReopeningResidualCarryAt.residual_bearer_is_existing_parent
          (oldVisit := oldVisit)
      birthBearerCarriedParentExact :=
        futureBirth.birthAdmission.bearerExisting.trans
          (SourceGeneratedReopeningResidualCarryAt.residual_bearer_is_existing_parent
            (oldVisit := oldVisit))
      residualAuthority := futureBirth.laterAuthority
      residualAuthorityExact := rfl
      residualConsumer := futureBirth.laterConsumer
      residualConsumerExact := rfl
      bearerFace :=
        paymentExitAlignmentBearerFaceAt oldVisit sourceIndex index
      bearerFaceExact := rfl
      alignedBearerExit := futureBirth.bearerExit
      alignedBearerExitExact := rfl
      alignedBearerExitFromRootRead :=
        futureBirth.bearerExit_fromInstalledFace
      deletedLegacyAlignment :=
        legacyPaymentExitBearerAlignment_isEmpty futureBirth
      positiveAlignment :=
        positivePaymentExitBearerAlignmentAt futureBirth }

namespace SourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (countermodel :
    SourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt oldVisit
      sourceIndex index)

include countermodel

/-- Both compared values are dependent restrictions of one exact outer
occurrence.  The projection coordinates remain distinct. -/
theorem sameOuterOccurrenceFaces :
    countermodel.renewalFace.projection =
        ContributionCapacityReopeningProjection.renewal ∧
      countermodel.bearerFace.projection =
        ContributionCapacityReopeningProjection.birthBearerExit ∧
      countermodel.renewalFace.projection ≠
        countermodel.bearerFace.projection := by
  rw [countermodel.renewalFaceExact, countermodel.bearerFaceExact]
  exact ⟨rfl, rfl, by intro equality; cases equality⟩

/-- The outer reopening event and the embedded M9 Payment event are both
explicitly retained, but at their own root types. -/
theorem outerAndEmbeddedOccurrenceLayersExplicit :
    countermodel.outerRootEvent = countermodel.futureBirth.laterRootEvent ∧
      countermodel.embeddedM9RootEvent =
        countermodel.embeddedM9Payment.rootOccurrence ∧
      countermodel.embeddedM9Payment =
        countermodel.legacyActualExit.paymentOccurrence :=
  ⟨countermodel.outerRootEventExact,
    countermodel.embeddedM9RootEventExact,
    countermodel.embeddedM9PaymentExact⟩

/-- Exact bearer provenance: the installed birth obligation fixes the U8
residual bearer, and this occurrence's runtime residual-carry producer proves
that same bearer is the existing parent. -/
theorem birthObligationCarriedResidualParentChain :
    countermodel.birthAdmission =
        sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit ∧
      countermodel.residualCarry =
        contributionCapacityReopeningRuntimeResidualCarryAt oldVisit
          sourceIndex index ∧
      countermodel.birthAdmission.obligation =
        contributionCapacityU8ObligationAt oldVisit
          exactSourceGeneratedLossAllocationMaterialWitness
          (contributionCapacityU8GeneratedResidual oldVisit) ∧
      countermodel.birthAdmission.obligation.bearer =
        contributionCapacityU8BearerAt oldVisit
          exactSourceGeneratedLossAllocationMaterialWitness
          (contributionCapacityU8GeneratedResidual oldVisit) ∧
      contributionCapacityU8BearerAt oldVisit
          exactSourceGeneratedLossAllocationMaterialWitness
          (contributionCapacityU8GeneratedResidual oldVisit) =
        sourceGeneratedLossAllocationMaterial.parentBearer ∧
      countermodel.birthAdmission.obligation.bearer =
        sourceGeneratedLossAllocationMaterial.parentBearer :=
  ⟨countermodel.birthAdmissionSourceExact,
    countermodel.residualCarryRuntimeExact,
    countermodel.birthObligationExact,
    countermodel.birthObligationBearerExact,
    countermodel.carriedResidualBearerExact,
    countermodel.birthBearerCarriedParentExact⟩

/-- The embedded M9 Payment and service are shared literally; they are not
the outer whole-ledger Payment certificate. -/
theorem embeddedPaymentAndServiceRemain :
    countermodel.legacyActualExit.paymentOccurrence =
        countermodel.futureBirth.actualExit.paymentOccurrence ∧
      countermodel.alignedBearerExit.existingPaymentOccurrence =
        countermodel.legacyActualExit.paymentOccurrence ∧
      countermodel.alignedBearerExit.existingActualSettlement =
        countermodel.legacyActualExit.actualSettlement ∧
      countermodel.legacyActualExit.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt
            (contributionCapacityFutureBirthDepth sourceIndex index)) := by
  have legacyExact := countermodel.legacyActualExitSharesFutureBirth
  refine ⟨congrArg (fun actualExit => actualExit.paymentOccurrence) legacyExact,
    ?_, ?_, ?_⟩
  · rw [countermodel.alignedBearerExitExact]
    exact countermodel.futureBirth.actualExitPayment_exact.trans
      (congrArg (fun actualExit => actualExit.paymentOccurrence)
        legacyExact).symm
  · rw [countermodel.alignedBearerExitExact]
    exact countermodel.futureBirth.actualService_exact.trans
      (congrArg (fun actualExit => actualExit.actualSettlement)
        legacyExact).symm
  · rw [countermodel.legacyActualExitExact,
      paymentExitAlignmentLegacyActualExit_eq_canonical]

/-- Exact outer lock.  The runtime-payment certificate contains the root
receipt/native-write equality, the generated next and all Fin-3 row
dispositions; the remaining conjuncts pin its residual row and independent
consumer to the same visit. -/
theorem outerLedgerConsumerNextRemain :
    Nonempty
        (ExactTemporalCausalRootEventAt
          (AlignmentReopeningRootAt oldVisit sourceIndex
            ).toAuthoritativeRoot.toLedgerRoot
          (contributionCapacityReopenedVisitAt oldVisit sourceIndex index)) ∧
      Nonempty
        (SourceGeneratedContributionCapacityReopeningRuntimePaymentAt oldVisit
          sourceIndex index) ∧
      Nonempty (SourceGeneratedReopeningResidualCarryAt oldVisit sourceIndex
        (AlignmentReopeningSourceEventAt oldVisit sourceIndex) index) ∧
      Nonempty (SourceNativeLivingTemporalCausalEntryAuthorityAt
        (AlignmentReopeningRootAt oldVisit sourceIndex)
        (contributionCapacityReopenedVisitAt oldVisit sourceIndex index)
        (contributionCapacityReopeningTargetResidual oldVisit)) ∧
      Nonempty (SourceNativeInquiryAnswerConsumerAt ()
        (contributionCapacityReopenedInquiryEventAt oldVisit sourceIndex index)
        (contributionCapacityReopeningTargetResidual oldVisit)
        (contributionCapacityReopenedAnswerFaceAt oldVisit sourceIndex index)) :=
  ⟨⟨countermodel.outerRootEvent⟩,
    ⟨countermodel.outerRuntimePayment⟩,
    ⟨countermodel.residualCarry⟩,
    ⟨countermodel.residualAuthority⟩,
    ⟨countermodel.residualConsumer⟩⟩

/-- Expanded commuting mouth for the same lock: one outer event supplies the
native Payment, all Fin-3 dispositions and its generated next; row `2` is the
carried residual consumed by the installed `.consumer` face. -/
theorem outerWholeLedgerRowConsumerNextExact :
    (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
        sourceIndex index).wholeLedgerWriteBack =
        (CanonicalReopeningCompilerAt oldVisit sourceIndex).compile
          (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
            sourceIndex index).occurrence ∧
      (∀ entryIndex : Fin 3,
        (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
          sourceIndex index).wholeLedgerWriteBack.entryDisposition
            (contributionCapacityReopeningCurrentEntryAt oldVisit
              (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
                sourceIndex index) entryIndex) =
          .evolved
            (contributionCapacityReopeningRuntimePaymentRowEvolutionAt oldVisit
              sourceIndex index entryIndex)) ∧
      (CanonicalReopeningCompilerAt oldVisit sourceIndex).compile
          (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
            sourceIndex index).occurrence =
        .nativeWrite
          (contributionCapacityReopeningRuntimePaymentAt oldVisit sourceIndex
            index) rfl
          (contributionCapacityReopeningEmitted oldVisit sourceIndex
            (AlignmentReopeningSourceEventAt oldVisit sourceIndex)
            (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
              sourceIndex index + 1))
          (contributionCapacityReopeningEvolution oldVisit sourceIndex
            (AlignmentReopeningSourceEventAt oldVisit sourceIndex)
            (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
              sourceIndex index).occurrence) ∧
      contributionCapacityReopeningCurrentEntryAt oldVisit
          (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
            sourceIndex index) (2 : Fin 3) =
        countermodel.residualCarry.sourceEntry ∧
      countermodel.residualConsumer.projection =
        ContributionCapacityReopeningProjection.consumer := by
  refine ⟨countermodel.outerRuntimePayment.rootReceiptNativeWriteExact,
    countermodel.outerRuntimePayment.everyRowEvolved,
    countermodel.outerRuntimePayment.compilerNativeWriteExact,
    ?_, ?_⟩
  · rw [countermodel.residualCarryExact]
    exact countermodel.futureBirth.laterRootEvent_entry_eq_residualCarry
  · rw [countermodel.residualConsumerExact]
    rfl

/-- Both exits remain fully actionable with capacity one; only the exact
payment/worker/bearer incidence is absent on the legacy face. -/
theorem allOperationalAxesRemain :
    (geometryCompilerAt
        (contributionCapacityFutureBirthDepth sourceIndex index)
        ).actionableExitCapacity = 1 ∧
      (birthBearerGeometryCompilerAt
        (contributionCapacityFutureBirthDepth sourceIndex index)
        ).actionableExitCapacity = 1 ∧
      Nonempty (ExactServedCrossingDebitedRunAt
        (anomiePhaseAt
          (contributionCapacityFutureBirthDepth sourceIndex index)) debited
        (serviceCompilerAt
          (contributionCapacityFutureBirthDepth sourceIndex index))) ∧
      IsEmpty (LegacyPaymentExitBearerAlignmentAt
        countermodel.futureBirth) ∧
      Nonempty (PositivePaymentExitBearerAlignmentAt
        countermodel.futureBirth) :=
  ⟨countermodel.legacyActualExit.exactCapacity,
    countermodel.alignedBearerExit.exactCapacity,
    ⟨countermodel.legacyActualExit.actualSettlement⟩,
    countermodel.deletedLegacyAlignment,
    ⟨countermodel.positiveAlignment⟩⟩

end SourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt

/-! ## No reconstruction and anti-smuggling controls -/

theorem remainingAuthorityCannotReconstructLegacyAlignment
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      ((countermodel :
          SourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt
            oldVisit sourceIndex index) →
        LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth) :=
  ⟨fun reconstruct =>
    let countermodel :=
      sourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt
        oldVisit sourceIndex index
    countermodel.deletedLegacyAlignment.false (reconstruct countermodel)⟩

theorem paymentExitBearerAlignment_negativeControls
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let countermodel :=
    sourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt oldVisit
      sourceIndex index
  fail_if_success exact
    (countermodel.legacyActualExit :
      LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth)
  fail_if_success exact
    (countermodel.legacyActualExit.paymentOccurrence :
      SourceGeneratedContributionCapacityReopeningRuntimePaymentAt oldVisit
        sourceIndex index)
  fail_if_success exact
    (countermodel.outerRuntimePayment :
      PeriodicSourceBackedPaymentAt
        (contributionCapacityFutureBirthDepth sourceIndex index))
  fail_if_success exact
    (countermodel.outerRootEvent :
      ExactTemporalCausalRootEventAt
        jointRoot.toAuthoritativeRoot.toLedgerRoot
        (temporalVisitAt
          (contributionCapacityFutureBirthDepth sourceIndex index)))
  fail_if_success exact
    (countermodel.embeddedM9RootEvent :
      ExactTemporalCausalRootEventAt
        (AlignmentReopeningRootAt oldVisit sourceIndex
          ).toAuthoritativeRoot.toLedgerRoot
        (contributionCapacityReopenedVisitAt oldVisit sourceIndex index))
  fail_if_success exact
    (countermodel.residualCarry :
      LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth)
  fail_if_success exact
    (countermodel.birthAdmission :
      LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth)
  fail_if_success exact
    (countermodel.residualConsumer :
      LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth)
  fail_if_success exact
    (countermodel.alignedBearerExit :
      LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth)
  fail_if_success exact
    (countermodel.positiveAlignment :
      LegacyPaymentExitBearerAlignmentAt countermodel.futureBirth)
  fail_if_success exact countermodel.actor
  fail_if_success exact countermodel.bearer
  fail_if_success exact countermodel.target
  fail_if_success exact countermodel.registry
  fail_if_success exact countermodel.coverage
  fail_if_success exact countermodel.history
  fail_if_success exact countermodel.future
  trivial

end
end M14SourceGeneratedPaymentExitBearerAlignmentIndependentNecessity
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaymentExitBearerAlignmentIndependentNecessity.sourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaymentExitBearerAlignmentIndependentNecessity.SourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt.embeddedPaymentAndServiceRemain
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaymentExitBearerAlignmentIndependentNecessity.SourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt.birthObligationCarriedResidualParentChain
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaymentExitBearerAlignmentIndependentNecessity.SourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt.outerLedgerConsumerNextRemain
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaymentExitBearerAlignmentIndependentNecessity.SourceGeneratedPaymentExitBearerAlignmentIndependentNecessityAt.outerWholeLedgerRowConsumerNextExact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaymentExitBearerAlignmentIndependentNecessity.remainingAuthorityCannotReconstructLegacyAlignment
