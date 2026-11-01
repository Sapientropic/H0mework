import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Consumer.ProofCarryingPostSettlementObserverFiniteExitCapacityConstitution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Preservation.NoGo.SourceGeneratedCycleMaximalCanonicalPaidStepNoGo

/-!
# Proof-carrying finite canonical paid-step preservation

At every edge of one requested finite prefix, the exact lifecycle Payment and
every other Payment proof at that same source index are consumed by the
existing proof-carrying canonical paid step.  The audit retains the complete
target channel incidence, macro future-birth seams, external residual
consumers, successor constitution and the exact negative controls against
divergent or deleted targets.

The source at `fuel + 1` is regenerated on demand and audited by the same
mouth.  This file stores only a `Prop` audit: no edge list, Payment table,
occurrence registry, history, schedule or completed future is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost
open M14EssentialAccessRelationFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent
open M14ProofCarryingContributionCapacityPostSettlementCanonicalPaidStep
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14ProofCarryingPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedCycleMaximalCanonicalPaidStep
open M14SourceGeneratedCycleMaximalCanonicalPaidStepNoGo
open M14SourceGeneratedFiniteExitCapacityCaptureJobNoGo
open M14SourceGeneratedFiniteExitCapacityObserverNoGo
open M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo
open M14SourceGeneratedPaidExitLifecycleMaximumNoGo
open M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition

/-! ## Payment-indexed subordinate audits -/

/-- Existing target-channel consumer audited at its exact actor, relation,
Payment, settlement, root factorization and generated next. -/
def TargetPreservationChannelAuditAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth)) (channel : EssentialAccessChannel) :
    Prop :=
  let preserved :=
    sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth
      payment
  let consumed := preserved.consumedStep.2.targetChannel channel
  (consumed.2.relationWitnessReturn).1.actor
        essentialAccessRelationCompiler = channelActor channel ∧
    essentialAccessRelationCompiler.relationOf
        (consumed.2.relationWitnessReturn).1 = channelRelation channel ∧
    consumed.2.rootReadCarrier.existingPaymentOccurrence =
      consumed.1.actualExit.paymentOccurrence ∧
    consumed.2.rootReadCarrier.existingActualSettlement =
      consumed.1.actualExit.actualSettlement ∧
    consumed.1.actualExit.paymentOccurrence.installed.RootAnswerAndNextFactorizes ∧
    consumed.2.actualNext =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (contributionCapacityPostSettlementCanonicalCurrentDepthAt oldVisit
            sourceIndex (cycleLifecycleIndex initial depth + 1) +
          1)

theorem targetPreservationChannelAuditAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth)) (channel : EssentialAccessChannel) :
    TargetPreservationChannelAuditAt initial depth payment channel :=
  (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth
    payment).consumedStep.2.targetChannelAudit channel

/-- The complete arbitrary-Payment producer plus all nine exact false-report
no-gos. -/
def InputPaymentPreservationAuditAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth)) : Prop :=
  Nonempty (CycleMaximalCanonicalPaidStepForPaymentAt initial depth payment) ∧
    IsEmpty (ClaimedPaidNextDivergenceAt initial depth payment) ∧
    IsEmpty (ClaimedTargetCurrentDivergenceAt initial depth payment) ∧
    IsEmpty (ClaimedTargetPaymentDivergenceAt initial depth payment) ∧
    IsEmpty (ClaimedTargetRootEventDivergenceAt initial depth payment) ∧
    IsEmpty (TargetConstitutionDeletionAt initial depth payment) ∧
    IsEmpty (TargetFutureBirthDeletionAt initial depth payment) ∧
    (∀ channel : EssentialAccessChannel,
      IsEmpty
        (TargetChannelConsumerDeletionAt initial depth payment channel)) ∧
    IsEmpty (TargetExternalSourceOwnershipDeletionAt initial depth payment) ∧
    IsEmpty (TargetExternalRootConsumerDeletionAt initial depth payment)

theorem inputPaymentPreservationAuditAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth)) :
    InputPaymentPreservationAuditAt initial depth payment :=
  ⟨⟨sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth
      payment⟩,
    sourceGeneratedCycleMaximalCanonicalPaidStepNoGo initial depth payment⟩

/-- Rich target audit extracted from the same input-indexed consumed step. -/
def InputPaymentTargetRichAuditAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth)) : Prop :=
  let preserved :=
    sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth
      payment
  (∀ channel : EssentialAccessChannel,
      TargetPreservationChannelAuditAt initial depth payment channel) ∧
    HEq preserved.consumedStep.2.targetFutureBirth.postRootEvent
      (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
        preserved.consumedStep.2.targetCurrent) ∧
    HEq preserved.consumedStep.2.targetFutureBirth.postPayment
      preserved.consumedStep.2.targetPayment ∧
    (Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.actualExit
            preserved.consumedStep.2.targetCurrent))) ∧
    FiniteExitCapacityConstitutionAt initial (depth + 1) ∧
    FiniteExitCapacityCaptureJobNoGoAt initial (depth + 1) ∧
    (∀ label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
        Bool,
      (¬ Nonempty
        (FaithfulAuthorityReconstruction
          (absoluteLifecyclePriceObserverAt (fuel := observerFuel) initial))) ∧
      (¬ Nonempty
        (FaithfulAuthorityReconstruction
          (absoluteLifecycleActionObserverAt (fuel := observerFuel) initial))) ∧
      (¬ Nonempty
        (FaithfulAuthorityReconstruction
          (administrativeRetaliationObserver oldVisit sourceIndex label))))

theorem inputPaymentTargetRichAuditAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth)) :
    InputPaymentTargetRichAuditAt initial observerFuel depth payment := by
  let preserved :=
    sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth
      payment
  exact
    ⟨targetPreservationChannelAuditAt initial depth payment,
      preserved.targetFutureBirthRootEventExact,
      preserved.targetFutureBirthPaymentExact,
      preserved.targetExternalPaymentAndConsumer,
      preserved.targetConstitution,
      targetCaptureJobNoGo_exact initial depth,
      fun label =>
        targetObserverNoGos_exact (fuel := observerFuel) initial depth label⟩

/-! ## Target lifecycle negative controls -/

def TargetLifecyclePreservationNoGoAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (targetDepth : Nat) :
    Prop :=
  IsEmpty
      (ExactFullCaptureReportedPaidExitLifecycleMaximumAt
        (cycleFullCaptureCounterlifeAt initial targetDepth)) ∧
    IsEmpty
      (ExactPostContinuationSourceOwnershipDeletionAt
        (cycleLifecycleMaximum initial targetDepth).disposition) ∧
    IsEmpty
      (ExactPostContinuationRootConsumerDeletionAt
        (cycleLifecycleMaximum initial targetDepth).disposition) ∧
    IsEmpty
      (ExactPostContinuationLocalEmptyErasesExternalLiabilityAt
        (cycleLifecycleMaximum initial targetDepth).disposition)

theorem targetLifecyclePreservationNoGoAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (targetDepth : Nat) :
    TargetLifecyclePreservationNoGoAt initial targetDepth :=
  ⟨cycleFullCaptureReportedMaximum_isEmpty initial targetDepth,
    cycleSourceOwnershipDeletion_isEmpty initial targetDepth,
    cycleRootConsumerDeletion_isEmpty initial targetDepth,
    cycleLocalEmptyErasure_isEmpty initial targetDepth⟩

/-! ## Finite every-edge consumer -/

structure ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) : Prop where
  private mk ::
  priorConstitutionAudit :
    ProofCarryingPostSettlementObserverFiniteExitCapacityConstitutionAt initial
      fuel
  everyCanonicalLifecyclePaymentPreservation : ∀ edge : Fin (fuel + 1),
    Nonempty (CycleMaximalCanonicalPaidStepPreservationAt initial edge.1)
  everyInputPaymentPreservationAndNoGo : ∀ edge : Fin (fuel + 1),
    ∀ payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleLifecycleIndex initial edge.1),
      InputPaymentPreservationAuditAt initial edge.1 payment
  everyInputPaymentTargetRichAudit : ∀ edge : Fin (fuel + 1),
    ∀ payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleLifecycleIndex initial edge.1),
      InputPaymentTargetRichAuditAt initial (fuel + 1) edge.1 payment
  everyTargetLifecycleNoGo : ∀ edge : Fin (fuel + 1),
    TargetLifecyclePreservationNoGoAt initial (edge.1 + 1)
  finalOneMoreCanonicalLifecyclePaymentPreservation :
    Nonempty
      (CycleMaximalCanonicalPaidStepPreservationAt initial (fuel + 1))
  finalOneMoreInputPaymentPreservationAndNoGo :
    ∀ payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleLifecycleIndex initial (fuel + 1)),
      InputPaymentPreservationAuditAt initial (fuel + 1) payment
  finalOneMoreInputPaymentTargetRichAudit :
    ∀ payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleLifecycleIndex initial (fuel + 1)),
      InputPaymentTargetRichAuditAt initial (fuel + 2) (fuel + 1) payment
  finalOneMoreTargetLifecycleNoGo :
    TargetLifecyclePreservationNoGoAt initial (fuel + 1 + 1)

theorem proofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservationAt initial
      fuel where
  priorConstitutionAudit :=
    proofCarryingPostSettlementObserverFiniteExitCapacityConstitution initial
      fuel
  everyCanonicalLifecyclePaymentPreservation := fun edge =>
    ⟨sourceGeneratedCycleMaximalCanonicalPaidStep initial edge.1⟩
  everyInputPaymentPreservationAndNoGo := fun edge payment =>
    inputPaymentPreservationAuditAt initial edge.1 payment
  everyInputPaymentTargetRichAudit := fun edge payment =>
    inputPaymentTargetRichAuditAt initial (fuel + 1) edge.1 payment
  everyTargetLifecycleNoGo := fun edge =>
    targetLifecyclePreservationNoGoAt initial (edge.1 + 1)
  finalOneMoreCanonicalLifecyclePaymentPreservation :=
    ⟨sourceGeneratedCycleMaximalCanonicalPaidStep initial (fuel + 1)⟩
  finalOneMoreInputPaymentPreservationAndNoGo := fun payment =>
    inputPaymentPreservationAuditAt initial (fuel + 1) payment
  finalOneMoreInputPaymentTargetRichAudit := fun payment =>
    inputPaymentTargetRichAuditAt initial (fuel + 2) (fuel + 1) payment
  finalOneMoreTargetLifecycleNoGo :=
    targetLifecyclePreservationNoGoAt initial (fuel + 1 + 1)

abbrev AnyProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservationAt
    (oldVisit : OldVisit) (sourceIndex boundary fuel : Nat) :=
  { initial : CycleAt oldVisit sourceIndex boundary //
    ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservationAt initial
      fuel }

def canonicalProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservationAt
    (oldVisit : OldVisit) (sourceIndex boundary fuel : Nat) :
    AnyProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservationAt oldVisit
      sourceIndex boundary fuel :=
  let prior :=
    canonicalProofCarryingPostSettlementObserverFiniteExitCapacityConstitutionAt
      oldVisit sourceIndex boundary fuel
  ⟨prior.1,
    proofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation prior.1 fuel⟩

end
end M14ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation.proofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation.canonicalProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservationAt
