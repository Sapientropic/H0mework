import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Identity.Death.Publication.Producer.SourceGeneratedContributionCapacityDeathFieldPublication
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Identity.Death.Producer.SourceGeneratedContributionCapacityEntityRenewalArithmeticDeath
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Gate.Consumer.ProofCarryingContributionCapacityJointSettlementGateFrontier

/-!
# Proof-carrying contribution-capacity death-field publication

This direct consumer closes the complete fixed-instance seam:

* the pre-emitter survivor root owns the finite death-field demand;
* P98/P99 and the unique occurrence fold compute the local first locus;
* the exact current-twelve action Payment consumes that root read and the
  complete Fin-2 source disposition;
* its own `NextPaidBy` lands at A14, where the complete frontier is recomputed
  and every row is terminal;
* the faithful handoff continues to A15 and the first post Payment generates
  the following current; and
* the publication fixed-point fibre is empty while the non-fixed paid response
  remains inhabited.

Arithmetic renewal death and substantive terminal death remain distinct
dependent readouts.  This certificate makes no claim that survivor depth ten
is the first locus of the entire earlier macro history.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityDeathFieldPublication

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementConsumer
open M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14SourceGeneratedContributionCapacityJointSettlementState
open M14SourceGeneratedContributionCapacityJointSettlementCrossRootPayment
open M14SourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceipt
open M14ProofCarryingContributionCapacityJointSettlementPaidTail
open M14ProofCarryingContributionCapacityJointSettlementGateFrontier
open M14SourceGeneratedContributionCapacityJointSettlementGateFrontier
open M14SourceGeneratedContributionCapacityDeathFieldDemand
open M14SourceGeneratedContributionCapacityDeathFieldDemand.SourceGeneratedContributionCapacityDeathFieldDemandAt
open M14SourceGeneratedContributionCapacityPaidDeathField
open M14SourceGeneratedContributionCapacityPaidDeathField.ExactContributionCapacityPreLocusPaymentAt
open M14SourceGeneratedContributionCapacityPaidDeathField.SourceGeneratedContributionCapacityMinimalDeathLocusAt
open M14SourceGeneratedContributionCapacityDeathFieldPublication
open M14SourceGeneratedContributionCapacityDeathFieldPublication.SourceGeneratedContributionCapacityDeathPublicationResponseAt
open M14SourceGeneratedContributionCapacityEntityRenewalArithmeticDeath
open M14SourceGeneratedContributionCapacityPersistentUnsettledEntity

abbrev CanonicalDeathFieldDemandType :=
  SourceGeneratedContributionCapacityDeathFieldDemandAt
    canonicalSettlementOldVisit 1
    (CanonicalContributionCapacitySettlementSourceEventAt
      canonicalSettlementOldVisit 1)
    (ContributionCapacityJointSettlementPaidSourceEventAt
      canonicalSettlementOldVisit 1).occurrence

def canonicalDeathFieldDemand : CanonicalDeathFieldDemandType :=
  contributionCapacityJointSettlementDeathFieldDemandAt
    canonicalSettlementOldVisit 1

abbrev CanonicalDeathFieldPreLocusPayment :=
  ExactContributionCapacityPreLocusPaymentAt canonicalSettlementOldVisit 1

abbrev CanonicalDeathFieldPublicationPayment :=
  ExactContributionCapacityPublicationPaymentAt canonicalSettlementOldVisit 1

abbrev CanonicalDeathFieldPublicationResponse :=
  SourceGeneratedContributionCapacityDeathPublicationResponseAt
    canonicalSettlementOldVisit 1

def canonicalDeathFieldPublicationResponse :
    CanonicalDeathFieldPublicationResponse :=
  sourceGeneratedContributionCapacityDeathPublicationResponseAt
    canonicalSettlementOldVisit 1

def canonicalDeathField_isProperFinite :
    contributionCapacityDeathFieldPresentation.ProperFiniteSections :=
  contributionCapacityDeathFieldProper

theorem canonicalDeathField_sourceRead_false :
    canonicalDeathFieldDemand.finiteSection ⟨0, by decide⟩ = false :=
  contributionCapacityJointSettlementDeathField_sourceRead
    canonicalSettlementOldVisit 1

theorem canonicalDeathField_targetRead_true :
    canonicalDeathFieldDemand.finiteSection ⟨1, by decide⟩ = true :=
  contributionCapacityJointSettlementDeathField_targetRead
    canonicalSettlementOldVisit 1

theorem canonicalDeathField_localMinimalLocus_one :
    canonicalDeathFieldDemand.localMinimalLocus = some 1 :=
  canonicalDeathFieldDemand.localMinimalLocus_eq_one

theorem canonicalDeathField_initial_noSubstantiveDeath :
    IsEmpty
      (ContributionCapacityJointSettlementDeathAt canonicalSettlementOldVisit
        1 (0 : Fin 2)) :=
  contributionCapacityJointSettlementDeathAt_zero_isEmpty
    canonicalSettlementOldVisit 1

theorem canonicalDeathField_terminal_substantiveDeath :
    Nonempty
      (ContributionCapacityJointSettlementDeathAt canonicalSettlementOldVisit
        1 (1 : Fin 2)) :=
  contributionCapacityJointSettlementDeathAt_one_nonempty
    canonicalSettlementOldVisit 1

theorem canonicalPublication_sourceCurrent_isTwelve :
    ContributionCapacityJointSettlementPaidSourceCurrentAt
      canonicalSettlementOldVisit 1 = 12 :=
  rfl

theorem survivorTailArithmeticDeath_atFirstGeneratedIndex :
    IsEmpty
      (ExactContributionEntityRenewalPaymentAt
        (sourceGeneratedPersistentUnsettledContributionEntityAt 0)) :=
  exactContributionEntityRenewalPayment_isEmpty
    (sourceGeneratedPersistentUnsettledContributionEntityAt 0)

theorem publicationSourceArithmeticDeath_stillEmpty :
    IsEmpty
      (ExactContributionEntityRenewalPaymentAt
        (sourceGeneratedPersistentUnsettledContributionEntityAt 2)) :=
  exactContributionEntityRenewalPayment_isEmpty
    (sourceGeneratedPersistentUnsettledContributionEntityAt 2)

/-! ## Whole certificate -/

structure ProofCarryingContributionCapacityDeathFieldPublicationCertificate :
    Prop where
  finiteFieldProper : Nonempty
    contributionCapacityDeathFieldPresentation.ProperFiniteSections
  p99ExactWrite : StatefulGenAlg.repeatEval
    (reflexiveQueryPrimitive contributionCapacityDeathFieldQuery)
    (reflexiveQueryStatefulPlan contributionCapacityDeathFieldQuery)
    1 false [false] true
  rootedFoldLocus : contributionCapacityDeathLocusReadout = some 1
  minimalChartMatchesFold :
    some
        (sourceGeneratedContributionCapacityMinimalDeathLocusAt
          canonicalSettlementOldVisit 1).observerTimeChart =
      contributionCapacityDeathLocusReadout
  installedDemand : Nonempty CanonicalDeathFieldDemandType
  sourceReadFalse :
    canonicalDeathFieldDemand.finiteSection ⟨0, by decide⟩ = false
  targetReadTrue :
    canonicalDeathFieldDemand.finiteSection ⟨1, by decide⟩ = true
  initialNoSubstantiveDeath : IsEmpty
    (ContributionCapacityJointSettlementDeathAt canonicalSettlementOldVisit
      1 (0 : Fin 2))
  terminalSubstantiveDeath : Nonempty
    (ContributionCapacityJointSettlementDeathAt canonicalSettlementOldVisit
      1 (1 : Fin 2))
  completeGateFrontier :
    ProofCarryingContributionCapacityJointSettlementGateFrontier
  sourceCurrentTwelve :
    ContributionCapacityJointSettlementPaidSourceCurrentAt
      canonicalSettlementOldVisit 1 = 12
  preLocusPayment : Nonempty CanonicalDeathFieldPreLocusPayment
  publicationPayment : Nonempty CanonicalDeathFieldPublicationPayment
  publicationNextProofIndependent :
    ∀ left right : CanonicalDeathFieldPublicationPayment,
      left.nextPaidBy = right.nextPaidBy
  sourceRootOccurrenceExact :
    contributionCapacityJointSettlementDeathFieldRootEventAt
        canonicalSettlementOldVisit 1 =
      ContributionCapacityJointSettlementPaidSourceEventAt
        canonicalSettlementOldVisit 1
  demandAndPaymentServiceExact :
    (exactContributionCapacityPreLocusPaymentAt canonicalSettlementOldVisit 1
      ).demand.actualService =
      (exactContributionCapacityPreLocusPaymentAt canonicalSettlementOldVisit 1
        ).actionPayment.sourcePayment.down
  sourceMaterialExact :
    (exactContributionCapacityPreLocusPaymentAt canonicalSettlementOldVisit 1
      ).sourceMaterial =
      ContributionCapacityJointSettlementPaidMaterialAt
        canonicalSettlementOldVisit 1
  sourceActualExitExact :
    (exactContributionCapacityPreLocusPaymentAt canonicalSettlementOldVisit 1
      ).sourceActualExit =
      contributionCapacityJointSettlementSourceActualExitAt
        canonicalSettlementOldVisit 1
  sourceAccountability :
    ContributionCapacitySettlementSurvivorAccountabilityAtCurrent
      canonicalSettlementOldVisit 1
      contributionCapacityJointSettlementSurvivorCurrentIndex
  everySourceRowEvolved : ∀ entryIndex : Fin 2,
    (ContributionCapacityJointSettlementPaidSourceEventAt
      canonicalSettlementOldVisit 1).wholeLedgerWriteBack.entryDisposition
        (contributionCapacitySettlementSurvivorEntryAt
          canonicalSettlementOldVisit entryIndex) =
      .evolved
        (contributionCapacityJointSettlementSourceRowEvolutionAt
          canonicalSettlementOldVisit 1 entryIndex)
  response : Nonempty CanonicalDeathFieldPublicationResponse
  responseReadOne : canonicalDeathFieldPublicationResponse.readBy = 1
  responseNextTerminal : canonicalDeathFieldPublicationResponse.nextPaidBy =
    ⟨(generatedContributionCapacityJointSettlementPaidActionAt
        canonicalSettlementOldVisit 1).target.TargetV,
      (generatedContributionCapacityJointSettlementPaidActionAt
        canonicalSettlementOldVisit 1).target.targetRoot.toAuthoritativeRoot,
      (generatedContributionCapacityJointSettlementPaidActionAt
        canonicalSettlementOldVisit 1).target.targetVisit⟩
  responseTargetLocusZero :
    canonicalDeathFieldPublicationResponse.recomputedDeathLocus = 0
  targetEveryRowTerminal : ∀ entryIndex : Fin 2,
    (contributionCapacityJointSettlementTerminalRootEventAt
      canonicalSettlementOldVisit 1).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityJointSettlementLiveEntryAt
          canonicalSettlementOldVisit entryIndex) =
      .terminal
        ((contributionCapacityJointSettlementTerminalExactAt
          canonicalSettlementOldVisit 1).ledgerEvolution.discharge
            (contributionCapacityJointSettlementLiveEntryAt
              canonicalSettlementOldVisit entryIndex))
  targetNoLocalSuccessor : IsEmpty
    (SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacityJointSettlementTerminalRootEventAt
        canonicalSettlementOldVisit 1).occurrence
      (contributionCapacityJointSettlementTerminalRootEventAt
        canonicalSettlementOldVisit 1).wholeLedgerWriteBack)
  fixedPointEmpty : IsEmpty
    (ContributionCapacityPublicationFixedPointAt
      canonicalDeathFieldPublicationResponse)
  nonFixedPaymentStillExists : Nonempty CanonicalDeathFieldPublicationPayment
  terminalHandoffContinues :
    contributionCapacityJointSettlementTerminalNextPaidBy
        canonicalSettlementOldVisit 1 =
      contributionCapacityJointSettlementFirstPostRootCurrentAt
        canonicalSettlementOldVisit 1
  firstPostPaymentGeneratesNext :
    let consumed :=
      (proofCarryingContributionCapacityJointSettlementPaidTailAt
        canonicalSettlementOldVisit 1).2.firstPostPaidStep
    HEq consumed.2.sourcePayment.nextPaidBy
      (M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent.SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
        consumed.2.targetCurrent).occurrence
  survivorTailFirstGeneratedArithmeticDeath : IsEmpty
    (ExactContributionEntityRenewalPaymentAt
      (sourceGeneratedPersistentUnsettledContributionEntityAt 0))
  publicationSourceArithmeticDeath : IsEmpty
    (ExactContributionEntityRenewalPaymentAt
      (sourceGeneratedPersistentUnsettledContributionEntityAt 2))
  arithmeticDeath :
    ProofCarryingContributionEntityRenewalArithmeticDeathCertificate
  actualPlayNotSearch :
    (contributionCapacityJointSettlementActionStateAt
      canonicalSettlementOldVisit 1).compileInquiry () ≠
      (contributionCapacitySettlementSurvivorStateAt
        canonicalSettlementOldVisit 1 2).compileInquiry ()

theorem proofCarryingContributionCapacityDeathFieldPublication :
    ProofCarryingContributionCapacityDeathFieldPublicationCertificate where
  finiteFieldProper := ⟨canonicalDeathField_isProperFinite⟩
  p99ExactWrite := contributionCapacityDeathField_repeat_one
  rootedFoldLocus := contributionCapacityDeathLocusReadout_eq_one
  minimalChartMatchesFold :=
    (sourceGeneratedContributionCapacityMinimalDeathLocusAt
      canonicalSettlementOldVisit 1).observerTimeChart_matches_generatedFold
  installedDemand := ⟨canonicalDeathFieldDemand⟩
  sourceReadFalse := canonicalDeathField_sourceRead_false
  targetReadTrue := canonicalDeathField_targetRead_true
  initialNoSubstantiveDeath :=
    canonicalDeathField_initial_noSubstantiveDeath
  terminalSubstantiveDeath :=
    canonicalDeathField_terminal_substantiveDeath
  completeGateFrontier :=
    proofCarryingContributionCapacityJointSettlementGateFrontier
  sourceCurrentTwelve := canonicalPublication_sourceCurrent_isTwelve
  preLocusPayment :=
    ⟨exactContributionCapacityPreLocusPaymentAt canonicalSettlementOldVisit 1⟩
  publicationPayment :=
    ⟨exactContributionCapacityPreLocusPaymentAt canonicalSettlementOldVisit 1⟩
  publicationNextProofIndependent := fun left right =>
    left.nextPaidBy_proofIndependent right
  sourceRootOccurrenceExact := rfl
  demandAndPaymentServiceExact :=
    (exactContributionCapacityPreLocusPaymentAt canonicalSettlementOldVisit 1
      ).demandActualServiceExact
  sourceMaterialExact :=
    (exactContributionCapacityPreLocusPaymentAt canonicalSettlementOldVisit 1
      ).sourceMaterialExact
  sourceActualExitExact :=
    (exactContributionCapacityPreLocusPaymentAt canonicalSettlementOldVisit 1
      ).sourceActualExitExact
  sourceAccountability :=
    (exactContributionCapacityPreLocusPaymentAt canonicalSettlementOldVisit 1
      ).sourceMaterial.accountability
  everySourceRowEvolved :=
    (exactContributionCapacityPreLocusPaymentAt canonicalSettlementOldVisit 1
      ).everySourceRowEvolved
  response := ⟨canonicalDeathFieldPublicationResponse⟩
  responseReadOne := canonicalDeathFieldPublicationResponse.readBy_eq_one
  responseNextTerminal :=
    canonicalDeathFieldPublicationResponse.nextPaidBy_isTerminalCurrent
  responseTargetLocusZero :=
    canonicalDeathFieldPublicationResponse.recomputedDeathLocus_eq_zero
  targetEveryRowTerminal :=
    canonicalDeathFieldPublicationResponse.targetRecomputation.everyTargetRowTerminal
  targetNoLocalSuccessor :=
    canonicalDeathFieldPublicationResponse.targetRecomputation.targetNoLocalSuccessor
  fixedPointEmpty :=
    contributionCapacityPublicationFixedPoint_isEmpty
      canonicalDeathFieldPublicationResponse
  nonFixedPaymentStillExists :=
    nonFixedPublicationPayment_remainsInhabited canonicalSettlementOldVisit 1
  terminalHandoffContinues :=
    publicationTerminalHandoff_generatesFirstPostCurrent
      canonicalSettlementOldVisit 1
  firstPostPaymentGeneratesNext :=
    publicationFirstPostPayment_generatesNext canonicalSettlementOldVisit 1
  survivorTailFirstGeneratedArithmeticDeath :=
    survivorTailArithmeticDeath_atFirstGeneratedIndex
  publicationSourceArithmeticDeath :=
    publicationSourceArithmeticDeath_stillEmpty
  arithmeticDeath := proofCarryingContributionEntityRenewalArithmeticDeath
  actualPlayNotSearch :=
    M14SourceGeneratedContributionCapacityJointSettlementConsumer.jointSettlementActualPlay_search_compilations_distinct
      canonicalSettlementOldVisit 1

/-! ## Direct negative controls -/

theorem bareReadReceiptGateSearchOrFixedPointCannotRetypeAsPublication :
    True := by
  let demand : CanonicalDeathFieldDemandType := canonicalDeathFieldDemand
  let actionPayment :=
    sourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
      canonicalSettlementOldVisit 1
  let terminalReceipt :=
    sourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceiptAt
      canonicalSettlementOldVisit 1
  let response := canonicalDeathFieldPublicationResponse
  let gate :=
    contributionCapacityJointSettlementInitialFrontierAt
      canonicalSettlementOldVisit 1
  fail_if_success exact
    (demand : CanonicalDeathFieldPublicationPayment)
  fail_if_success exact
    (actionPayment : CanonicalDeathFieldPublicationPayment)
  fail_if_success exact
    (terminalReceipt : CanonicalDeathFieldPublicationPayment)
  fail_if_success exact
    (gate : CanonicalDeathFieldPublicationPayment)
  fail_if_success exact
    (canonicalContributionCapacityJointSettlementSearchTick :
      CanonicalDeathFieldPublicationPayment)
  fail_if_success exact
    (response.readBy : CanonicalDeathFieldPublicationPayment)
  fail_if_success exact response.fixedPoint.nextPaidBy
  trivial

theorem deathFieldDemand_hasNoWriteNextTargetOrCompletedFuture : True := by
  let demand : CanonicalDeathFieldDemandType := canonicalDeathFieldDemand
  fail_if_success exact demand.write
  fail_if_success exact demand.nextPaidBy
  fail_if_success exact demand.target
  fail_if_success exact demand.history
  fail_if_success exact demand.completedFuture
  trivial

end
end M14ProofCarryingContributionCapacityDeathFieldPublication
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityDeathFieldPublication.proofCarryingContributionCapacityDeathFieldPublication
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityDeathFieldPublication.bareReadReceiptGateSearchOrFixedPointCannotRetypeAsPublication
