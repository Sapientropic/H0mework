import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Face.SourceInstalledContributionCapacityFinitePrefixRepresentation
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Incidence.SourceGeneratedContributionCapacityFinitePrefixResponsibilityDifference

/-!
# Difference-generated finite-prefix representation breaking

The source side is the positive prefix readout generated from the exact
root-installed trace point.  The later replay pair is generated only after
that prefix.  A proof-relevant
independent consumer binds both Payments, all channel witness returns,
source ownership and the Q root consumer before the operational
representation is declared broken.

The failure is not an empty syntax definition: raw expressions are inhabited
and one expression exactly represents the whole prior prefix.  What is empty
is extension of that expression language to every replay in the open paid
tail.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityFinitePrefixRepresentationBreaking

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer UniversalRootGrammar
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityFinitePrefixResponsibilityDifference
open M14SourceGeneratedContributionCapacityFinitePrefixAuthorityObserver
open M14SourceInstalledContributionCapacityFinitePrefixRepresentation
open M14SourceGeneratedUniversalSocietyRootGrammar

def finitePrefixInstalledKernelPairAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (incidence : SourceGeneratedFinitePrefixResponsibilityDifferenceAt oldVisit
      sourceIndex boundary) :
    AuthorityKernelPair
      (finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex
        boundary) where
  left := incidence.leftReplay
  right := incidence.rightReplay
  occurrence_ne := incidence.finiteKernelPair.occurrence_ne
  visible_eq := by
    apply Prod.ext
    · exact incidence.finiteKernelPair.visible_eq
    · rfl
  authority_ne := incidence.finiteKernelPair.authority_ne

abbrev AnyFinitePrefixCompleteRepresentationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { expression :
      FinitePrefixOperationalExpressionAt oldVisit sourceIndex boundary //
    FinitePrefixCompleteRepresentationAt oldVisit sourceIndex boundary
      expression }

def completeRepresentationToAuthorityFactorization
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (complete :
      AnyFinitePrefixCompleteRepresentationAt oldVisit sourceIndex boundary) :
    AuthorityFactorization
      (finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex
        boundary) where
  readAuthority := complete.1
  preservesActualAuthority := complete.2.preservesEveryReplay

/-- The independent consumer is generated from the same incidence and then
becomes an index of the breaking token.  It cannot be replaced by a naked
observer collision. -/
inductive SourceGeneratedFinitePrefixDifferenceConsumerAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (incidence : SourceGeneratedFinitePrefixResponsibilityDifferenceAt oldVisit
      sourceIndex boundary) : Type 31
  | private consumed

def sourceGeneratedFinitePrefixDifferenceConsumerAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (incidence : SourceGeneratedFinitePrefixResponsibilityDifferenceAt oldVisit
      sourceIndex boundary) :
    SourceGeneratedFinitePrefixDifferenceConsumerAt incidence :=
  .consumed

namespace SourceGeneratedFinitePrefixDifferenceConsumerAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  {incidence : SourceGeneratedFinitePrefixResponsibilityDifferenceAt oldVisit
    sourceIndex boundary}
  (consumer : SourceGeneratedFinitePrefixDifferenceConsumerAt incidence)

include consumer in
theorem exactPaymentsConsumed :
    incidence.leftPaidStep.2.sourcePayment = incidence.leftPayment ∧
      incidence.rightPaidStep.2.sourcePayment = incidence.rightPayment := by
  cases consumer
  exact incidence.exactPaymentsConsumed

include consumer in
theorem everyChannelReturns (channel : EssentialAccessChannel) :
    type_of% (incidence.channelWitnessesReturnToEachSource channel) ∧
      type_of% (incidence.channelPaymentsReturnToEachActualExit channel) := by
  cases consumer
  exact
    ⟨incidence.channelWitnessesReturnToEachSource channel,
      incidence.channelPaymentsReturnToEachActualExit channel⟩

include consumer in
theorem sourceOwnedAndRootConsumed :
    Nonempty
        M14SourceGeneratedContributionCapacityPostSettlementExternalLiability.ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (M14SourceGeneratedContributionCapacityPostSettlementExternalLiability.ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          incidence.rightActualExit) := by
  cases consumer
  exact ⟨incidence.sourceOwnedResidual, incidence.rootConsumerIsInstalled⟩

include consumer in
theorem exactQOccurrenceAndEntry :
    incidence.rightActualExit.paymentOccurrence.rootOccurrence =
        incidence.rightExactRootEvent ∧
      incidence.rightActualExit.paymentOccurrence.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry := by
  cases consumer
  exact
    ⟨incidence.rightPaymentRootOccurrence_exact,
      incidence.rightPaymentSourceEntry_exact⟩

end SourceGeneratedFinitePrefixDifferenceConsumerAt

/-- The exact installed-trace-point prefix readout receipt, later difference
and independent consumer are all indices of one private breaking seal. -/
inductive SourceGeneratedFinitePrefixRepresentationBreakingAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (sourceFace :
      SourceInstalledFinitePrefixRepresentationAt oldVisit sourceIndex
        boundary)
    (incidence : SourceGeneratedFinitePrefixResponsibilityDifferenceAt oldVisit
      sourceIndex boundary)
    (consumer : SourceGeneratedFinitePrefixDifferenceConsumerAt incidence) :
    Type 32
  | private generated

def canonicalPrefixAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceInstalledFinitePrefixRepresentationAt oldVisit sourceIndex boundary :=
  sourceInstalledFinitePrefixRepresentationAt oldVisit sourceIndex boundary

def canonicalIncidenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedFinitePrefixResponsibilityDifferenceAt oldVisit sourceIndex
      boundary :=
  sourceGeneratedFinitePrefixResponsibilityDifferenceAt oldVisit sourceIndex
    boundary

def canonicalDifferenceConsumerAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedFinitePrefixDifferenceConsumerAt
      (canonicalIncidenceAt oldVisit sourceIndex boundary) :=
  sourceGeneratedFinitePrefixDifferenceConsumerAt
    (canonicalIncidenceAt oldVisit sourceIndex boundary)

abbrev CanonicalFinitePrefixRepresentationBreakingAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  SourceGeneratedFinitePrefixRepresentationBreakingAt
    (canonicalPrefixAt oldVisit sourceIndex boundary)
    (canonicalIncidenceAt oldVisit sourceIndex boundary)
    (canonicalDifferenceConsumerAt oldVisit sourceIndex boundary)

def sourceGeneratedFinitePrefixRepresentationBreakingAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    CanonicalFinitePrefixRepresentationBreakingAt oldVisit sourceIndex
      boundary :=
  .generated

namespace SourceGeneratedFinitePrefixRepresentationBreakingAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  {sourceFace : SourceInstalledFinitePrefixRepresentationAt oldVisit sourceIndex
    boundary}
  {incidence : SourceGeneratedFinitePrefixResponsibilityDifferenceAt oldVisit
    sourceIndex boundary}
  {consumer : SourceGeneratedFinitePrefixDifferenceConsumerAt incidence}
  (breaking :
    SourceGeneratedFinitePrefixRepresentationBreakingAt sourceFace incidence
      consumer)

include breaking in
theorem prefixOccurredBeforeLeft :
    (show Nat from (prefixVisitAt oldVisit sourceIndex boundary).current) <
      incidence.leftReplay.2.current := by
  cases breaking
  rw [prefixVisit_current_exact, incidence.leftReplay.2.current_exact,
    incidence.leftReplay_index_exact]
  omega

include breaking in
theorem bothPathsStrictlyLater :
    boundary < incidence.leftReplay.2.current ∧
      boundary < incidence.rightReplay.2.current := by
  cases breaking
  exact incidence.bothStrictlyLater

include breaking in
theorem positivePrefixRepresentation :
    FinitePrefixHistoricalRepresentationAt oldVisit sourceIndex boundary
      sourceFace.expression := by
  cases breaking
  exact sourceFace.historicalRepresentation

include breaking in
theorem sourceExpressionCompilerCommutes :
    type_of% sourceFace.expressionCompilerCommutes := by
  cases breaking
  exact sourceFace.expressionCompilerCommutes

include breaking in
theorem sourceActualLedgerPointIsInInstalledTrace :
    type_of% sourceFace.actualLedgerPointMem := by
  cases breaking
  exact sourceFace.actualLedgerPointMem

include breaking in
theorem rawExpressionLanguageNonempty :
    Nonempty
      (FinitePrefixOperationalExpressionAt oldVisit sourceIndex boundary) :=
  by
    cases breaking
    exact
      ⟨SourceInstalledFinitePrefixRepresentationAt.expression sourceFace⟩

include breaking in
theorem completeRepresentationIsEmpty :
    IsEmpty
      (AnyFinitePrefixCompleteRepresentationAt oldVisit sourceIndex
        boundary) := by
  cases breaking
  refine ⟨fun complete => ?_⟩
  exact
    (finitePrefixInstalledKernelPairAt incidence).noAuthorityFactorization
      ⟨completeRepresentationToAuthorityFactorization complete⟩

include breaking in
theorem sameRealNormalDifferentK :
    type_of% incidence.sameRealNormalFormDifferentActualK := by
  cases breaking
  exact incidence.sameRealNormalFormDifferentActualK

include breaking in
theorem sameInstalledVisibleDifferentK :
    let observer :=
      finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex boundary
    observer.forget incidence.leftReplay =
        observer.forget incidence.rightReplay ∧
      observer.authorityK incidence.leftReplay ≠
        observer.authorityK incidence.rightReplay :=
  by
    cases breaking
    exact
      ⟨(finitePrefixInstalledKernelPairAt incidence).visible_eq,
        (finitePrefixInstalledKernelPairAt incidence).authority_ne⟩

include breaking in
theorem actualPathsDifferent :
    incidence.leftReplay.2.actualPath ≠
      incidence.rightReplay.2.actualPath := by
  cases breaking
  exact incidence.actualPathsDifferent

include breaking in
theorem prefixTraceRootInstalled :
    type_of% sourceFace.traceAuthorityFactorizes := by
  cases breaking
  exact sourceFace.traceAuthorityFactorizes

include breaking in
theorem rightTraceRootInstalled :
    type_of%
      ((universalSocietyRecognitionAt oldVisit sourceIndex
        ).installedTraceAuthority_factorizes
          (contributionCapacityPostSettlementRenewalVisitAt oldVisit
            sourceIndex (boundary + 2))) := by
  cases breaking
  exact
    (universalSocietyRecognitionAt oldVisit sourceIndex
      ).installedTraceAuthority_factorizes
        (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
          (boundary + 2))

include breaking in
theorem rightTraceOccurrenceIsRightReplayEvent :
    ((UniversalSocietyRootAt oldVisit sourceIndex).toAuthoritativeRoot
      ).toLedgerRoot.exactTemporalCausalEventAt
        (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
          (boundary + 2)) =
      incidence.rightReplay.2.rootEvent := by
  cases breaking
  cases incidence
  rfl

include breaking in
theorem rightPaidWholeLedgerIsRightReplayWholeLedger :
    incidence.rightPaidStep.2.sourceCurrent.rootEvent.wholeLedgerWriteBack =
      incidence.rightReplay.2.rootEvent.wholeLedgerWriteBack := by
  cases breaking
  cases incidence
  rfl

include breaking in
theorem rightPaidSuccessorIsExactPaymentSuccessor :
    incidence.rightPaidStep.2.sourceSuccessor =
      incidence.rightPaidStep.2.sourcePayment.successor := by
  cases breaking
  rfl

include breaking in
theorem independentConsumerReturnsEveryChannel
    (channel : EssentialAccessChannel) :
    type_of% (consumer.everyChannelReturns channel) := by
  cases breaking
  exact consumer.everyChannelReturns channel

include breaking in
theorem independentConsumerOwnsAndConsumes :
    type_of% consumer.sourceOwnedAndRootConsumed := by
  cases breaking
  exact consumer.sourceOwnedAndRootConsumed

include breaking in
theorem exactPaymentsConsumed :
    type_of% consumer.exactPaymentsConsumed := by
  cases breaking
  exact consumer.exactPaymentsConsumed

include breaking in
theorem exactQOccurrenceAndEntry :
    type_of% consumer.exactQOccurrenceAndEntry := by
  cases breaking
  exact consumer.exactQOccurrenceAndEntry

include breaking in
theorem ordinaryRightPaymentGeneratesCanonicalNext :
    HEq incidence.rightPaidStep.2.sourcePayment.nextPaidBy
      (M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent.SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
        incidence.rightPaidStep.2.targetCurrent).occurrence := by
  cases breaking
  exact incidence.rightPaidStep.2.paidNext_isTargetCanonicalOccurrence

end SourceGeneratedFinitePrefixRepresentationBreakingAt

theorem finitePrefixRepresentationBreaking_cofinal
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ∀ boundary : Nat,
      Nonempty
        (CanonicalFinitePrefixRepresentationBreakingAt oldVisit sourceIndex
          boundary) :=
  fun boundary =>
    ⟨sourceGeneratedFinitePrefixRepresentationBreakingAt oldVisit sourceIndex
      boundary⟩

theorem finitePrefixRepresentationBreaking_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let breaking :=
      sourceGeneratedFinitePrefixRepresentationBreakingAt oldVisit sourceIndex
        boundary
    Nonempty
        (CanonicalFinitePrefixRepresentationBreakingAt oldVisit sourceIndex
          boundary) ∧
      type_of% breaking.positivePrefixRepresentation ∧
      type_of% breaking.sourceExpressionCompilerCommutes ∧
      type_of% breaking.sourceActualLedgerPointIsInInstalledTrace ∧
      type_of% breaking.rawExpressionLanguageNonempty ∧
      type_of% breaking.completeRepresentationIsEmpty ∧
      type_of% breaking.sameRealNormalDifferentK ∧
      type_of% breaking.sameInstalledVisibleDifferentK ∧
      type_of% breaking.prefixTraceRootInstalled ∧
      type_of% breaking.rightTraceRootInstalled ∧
      type_of% breaking.rightTraceOccurrenceIsRightReplayEvent ∧
      type_of% breaking.rightPaidWholeLedgerIsRightReplayWholeLedger ∧
      type_of% breaking.rightPaidSuccessorIsExactPaymentSuccessor ∧
      type_of% breaking.exactPaymentsConsumed ∧
      (∀ channel : EssentialAccessChannel,
        type_of% (breaking.independentConsumerReturnsEveryChannel channel)) ∧
      type_of% breaking.independentConsumerOwnsAndConsumes ∧
      type_of% breaking.ordinaryRightPaymentGeneratesCanonicalNext := by
  dsimp
  let breaking :=
    sourceGeneratedFinitePrefixRepresentationBreakingAt oldVisit sourceIndex
      boundary
  exact
    ⟨⟨breaking⟩, breaking.positivePrefixRepresentation,
      breaking.sourceExpressionCompilerCommutes,
      breaking.sourceActualLedgerPointIsInInstalledTrace,
      breaking.rawExpressionLanguageNonempty,
      breaking.completeRepresentationIsEmpty,
      breaking.sameRealNormalDifferentK,
      breaking.sameInstalledVisibleDifferentK,
      breaking.prefixTraceRootInstalled, breaking.rightTraceRootInstalled,
      breaking.rightTraceOccurrenceIsRightReplayEvent,
      breaking.rightPaidWholeLedgerIsRightReplayWholeLedger,
      breaking.rightPaidSuccessorIsExactPaymentSuccessor,
      breaking.exactPaymentsConsumed,
      breaking.independentConsumerReturnsEveryChannel,
      breaking.independentConsumerOwnsAndConsumes,
      breaking.ordinaryRightPaymentGeneratesCanonicalNext⟩

set_option linter.unusedVariables false in
theorem nakedFragmentsCannotRetypeAsRepresentationBreaking
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : True := by
  let sourceFace := canonicalPrefixAt oldVisit sourceIndex boundary
  let incidence := canonicalIncidenceAt oldVisit sourceIndex boundary
  let consumer := canonicalDifferenceConsumerAt oldVisit sourceIndex boundary
  fail_if_success exact
    (sourceFace :
      SourceGeneratedFinitePrefixRepresentationBreakingAt sourceFace incidence
        consumer)
  fail_if_success exact
    (incidence.finiteKernelPair :
      SourceGeneratedFinitePrefixRepresentationBreakingAt sourceFace incidence
        consumer)
  fail_if_success exact
    (consumer :
      SourceGeneratedFinitePrefixRepresentationBreakingAt sourceFace incidence
        consumer)
  trivial

end
end M14SourceGeneratedContributionCapacityFinitePrefixRepresentationBreaking
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFinitePrefixRepresentationBreaking.sourceGeneratedFinitePrefixRepresentationBreakingAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFinitePrefixRepresentationBreaking.finitePrefixRepresentationBreaking_cofinal
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFinitePrefixRepresentationBreaking.finitePrefixRepresentationBreaking_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFinitePrefixRepresentationBreaking.nakedFragmentsCannotRetypeAsRepresentationBreaking
