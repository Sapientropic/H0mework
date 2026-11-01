import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Producer.SourceGeneratedCanonicalSocietyCofinalReadout

/-!
# No-go controls for the canonical Society renewal pulse

The exact self-U8 recurrence and the paid-target compatible FutureBirth are
generated at one canonical cycle.  This file rejects deletion of either face,
collapse of the adjacent Payment occurrences, replay of a pulse at another
depth, deletion of all pulses above a bound and deletion of the generated
runtime successor law.

Every false-report carrier has a private constructor.  No Boolean report,
`False` premise, alternative target, history, schedule or completed future is
introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyCofinalReadoutNoGo

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost
open M14EssentialAccessRelationFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14ProofCarryingContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
open M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo
open M14SourceGeneratedCycleMaximalCanonicalPaidStep
open M14SourceGeneratedCycleMaximalCanonicalPaidStepNoGo
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14SourceGeneratedCycleCanonicalRootLawStepNoGo
open M14SourceGeneratedCanonicalSocietyCofinalReadout

/-! ## Pointwise deletion and collapse -/

structure ExactCanonicalSelfU8TickDeletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Type 32 where
  private mk ::
  deleted : IsEmpty (ExactCanonicalSelfU8TickAt initial depth)

theorem exactCanonicalSelfU8TickDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (ExactCanonicalSelfU8TickDeletionAt initial depth) :=
  ⟨fun claim => claim.deleted.false
    (everyExactCanonicalSelfU8Tick initial depth)⟩

structure ExactCanonicalCompatibleFutureBirthDeletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) : Type 32 where
  private mk ::
  deleted : ¬ ExactCanonicalCompatibleFutureBirthAt initial observerFuel depth

theorem exactCanonicalCompatibleFutureBirthDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) :
    IsEmpty
      (ExactCanonicalCompatibleFutureBirthDeletionAt initial observerFuel
        depth) :=
  ⟨fun claim => claim.deleted
    (everyExactCanonicalCompatibleFutureBirth initial observerFuel depth)⟩

/-- Stronger raw-token deletion at the exact paid target index. -/
structure ExactCanonicalPaidTargetFutureBirthDeletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Type 32 where
  private mk ::
  deleted : IsEmpty
    (SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex (cycleLifecycleIndex initial (depth + 1)))

theorem exactCanonicalPaidTargetFutureBirthDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (ExactCanonicalPaidTargetFutureBirthDeletionAt initial depth) := by
  let pulse := exactCanonicalSocietyRenewalPulseAt initial 0 depth
  exact ⟨fun claim => pulse.canonicalMacroFutureBirthAudit.futureBirth.elim
    claim.deleted.false⟩

/-- The self-U8 source Payment and the compatible FutureBirth paid target are
adjacent exact occurrences, not one occurrence. -/
structure ExactCanonicalPulseSelfU8FutureBirthOccurrenceCollapseAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel depth) :
    Type 32 where
  private mk ::
  collapsed :
    currentSelfU8PaymentOccurrence (stepAt initial depth) =
      nextSelfU8PaymentOccurrence (stepAt initial depth)

/-- The recurrence's next Payment occurrence is definitionally the actual
exit occurrence carried by this pulse's paid-target FutureBirth. -/
theorem exactCanonicalPulseNextSelfU8Payment_isFutureBirthPayment
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (_pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel depth) :
    HEq (nextSelfU8PaymentOccurrence (stepAt initial depth))
      (contributionCapacityPostSettlementPaymentOccurrenceOfExitAt oldVisit
        sourceIndex (cycleLifecycleIndex initial depth + 1)
        (sourceGeneratedCycleMaximalCanonicalPaidStep initial depth
          ).consumedStep.2.targetFutureBirth.actualExit) :=
  by
    unfold nextSelfU8PaymentOccurrence currentPaidRenewal
    rw [cycleMorphismPaidRenewal_eq_cycleLifecycle initial depth]
    rfl

theorem exactCanonicalPulseSelfU8FutureBirthOccurrenceCollapse_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel depth) :
    IsEmpty
      (ExactCanonicalPulseSelfU8FutureBirthOccurrenceCollapseAt pulse) :=
  ⟨fun claim =>
    pulse.selfU8Tick.currentAndNextPaymentOccurrencesDistinct claim.collapsed⟩

structure ExactCanonicalPulseNextU8CoreDivergenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel depth) :
    Type 32 where
  private mk ::
  divergence : targetCore (nextMorphism (stepAt initial depth)) ≠
    generatedU8CoreAt oldVisit sourceIndex (boundary + depth + 1)

structure ExactCanonicalPulseNextRootFactorizationDeletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel depth) :
    Type 32 where
  private mk ::
  deleted : IsEmpty
    ((activatedSubmissionAt oldVisit sourceIndex (boundary + depth + 1)
      ).RootAnswerAndNextFactorizes)

structure ExactCanonicalPulseNextMacroNextDivergenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel depth) :
    Type 32 where
  private mk ::
  divergence :
    ((runtimeAt oldVisit sourceIndex (boundary + depth + 1)).stateAt 1
      ).engine.node.erase ≠
      (firstTickAt oldVisit sourceIndex
        (boundary + depth + 1)).next.node.erase

theorem exactCanonicalPulseNextU8CoreDivergence_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel depth) :
    IsEmpty (ExactCanonicalPulseNextU8CoreDivergenceAt pulse) :=
  ⟨fun claim => claim.divergence
    pulse.selfU8Tick.nextMorphismCertificate.targetCoreExact⟩

theorem exactCanonicalPulseNextRootFactorizationDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel depth) :
    IsEmpty (ExactCanonicalPulseNextRootFactorizationDeletionAt pulse) :=
  ⟨fun claim => claim.deleted.false
    pulse.selfU8Tick.nextMorphismCertificate.targetRootFactorization⟩

theorem exactCanonicalPulseNextMacroNextDivergence_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel depth) :
    IsEmpty (ExactCanonicalPulseNextMacroNextDivergenceAt pulse) :=
  ⟨fun claim => claim.divergence
    pulse.selfU8Tick.nextMorphismCertificate.targetMacroNextExact⟩

/-! ## Cross-depth replay controls -/

structure ExactCanonicalPulsePaymentReplayAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (left right : Nat) : Type 32 where
  private mk ::
  leftPulse : ExactCanonicalSocietyRenewalPulseAt initial 0 left
  rightPulse : ExactCanonicalSocietyRenewalPulseAt initial 0 right
  depthsDifferent : left ≠ right
  replayed : cyclePaymentOccurrenceAt initial left =
    cyclePaymentOccurrenceAt initial right

structure ExactCanonicalPulseKReplayAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (left right : Nat) : Type 32 where
  private mk ::
  leftPulse : ExactCanonicalSocietyRenewalPulseAt initial 0 left
  rightPulse : ExactCanonicalSocietyRenewalPulseAt initial 0 right
  depthsDifferent : left ≠ right
  replayed :
    (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex).authorityK (cycleReplayAt initial left) =
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex).authorityK (cycleReplayAt initial right)

structure ExactCanonicalPulsePathReplayAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (left right : Nat) : Type 32 where
  private mk ::
  leftPulse : ExactCanonicalSocietyRenewalPulseAt initial 0 left
  rightPulse : ExactCanonicalSocietyRenewalPulseAt initial 0 right
  depthsDifferent : left ≠ right
  replayed : (cycleReplayAt initial left).2.actualPath =
    (cycleReplayAt initial right).2.actualPath

theorem exactCanonicalPulsePaymentReplay_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (left right : Nat) :
    IsEmpty (ExactCanonicalPulsePaymentReplayAt initial left right) :=
  ⟨fun replay =>
    (cyclePairwiseStrongKernel initial replay.depthsDifferent).2.2.2
      replay.replayed⟩

theorem exactCanonicalPulseKReplay_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (left right : Nat) :
    IsEmpty (ExactCanonicalPulseKReplayAt initial left right) :=
  ⟨fun replay =>
    (cyclePairwiseStrongKernel initial replay.depthsDifferent).2.2.1
      replay.replayed⟩

theorem exactCanonicalPulsePathReplay_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (left right : Nat) :
    IsEmpty (ExactCanonicalPulsePathReplayAt initial left right) :=
  ⟨fun replay =>
    (cyclePairwiseStrongKernel initial replay.depthsDifferent).1
      replay.replayed⟩

/-- Positive cross-depth observer counterexample: visible normal form agrees
while path, K and event-selected Payment remain different. -/
theorem exactCanonicalPulsePair_strongKernel
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    {left right : Nat} (different : left ≠ right) :
    ExactCanonicalSocietyRenewalPulseAt initial 0 left ∧
      ExactCanonicalSocietyRenewalPulseAt initial 0 right ∧
      (cycleReplayAt initial left).2.actualPath ≠
        (cycleReplayAt initial right).2.actualPath ∧
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget (cycleReplayAt initial left) =
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget (cycleReplayAt initial right) ∧
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).authorityK (cycleReplayAt initial left) ≠
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).authorityK (cycleReplayAt initial right) ∧
      cyclePaymentOccurrenceAt initial left ≠
        cyclePaymentOccurrenceAt initial right :=
  ⟨exactCanonicalSocietyRenewalPulseAt initial 0 left,
    exactCanonicalSocietyRenewalPulseAt initial 0 right,
    cyclePairwiseStrongKernel initial different⟩

/-! ## Cofinal-gap deletion -/

structure ExactCanonicalCofinalPulseDeletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (readout : SourceGeneratedCanonicalSocietyCofinalReadoutAt initial)
    (n observerFuel : Nat) : Type 32 where
  private mk ::
  allLaterDeleted : ∀ m, n < m →
    ¬ ExactCanonicalSocietyRenewalPulseAt initial observerFuel m

theorem exactCanonicalCofinalPulseDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (readout : SourceGeneratedCanonicalSocietyCofinalReadoutAt initial)
    (n observerFuel : Nat) :
    IsEmpty (ExactCanonicalCofinalPulseDeletionAt readout n observerFuel) :=
  ⟨fun claim => by
    rcases readout.jointCofinal n observerFuel with ⟨m, later, pulse⟩
    exact claim.allLaterDeleted m later pulse⟩

/-! ## Direct no-go audit -/

structure CanonicalSocietyCofinalReadoutNoGoAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) : Prop where
  private mk ::
  everySelfU8TickDeletionEmpty : ∀ depth,
    IsEmpty (ExactCanonicalSelfU8TickDeletionAt initial depth)
  everyCompatibleFutureBirthDeletionEmpty : ∀ observerFuel depth,
    IsEmpty
      (ExactCanonicalCompatibleFutureBirthDeletionAt initial observerFuel
        depth)
  everyPaidTargetFutureBirthDeletionEmpty : ∀ depth,
    IsEmpty (ExactCanonicalPaidTargetFutureBirthDeletionAt initial depth)
  everyPulseOccurrenceCollapseEmpty : ∀ observerFuel depth,
    let pulse := exactCanonicalSocietyRenewalPulseAt initial observerFuel depth
    IsEmpty
      (ExactCanonicalPulseSelfU8FutureBirthOccurrenceCollapseAt pulse)
  everyPulseNextPaymentIsFutureBirthPayment : ∀ depth,
    HEq (nextSelfU8PaymentOccurrence (stepAt initial depth))
      (contributionCapacityPostSettlementPaymentOccurrenceOfExitAt oldVisit
        sourceIndex (cycleLifecycleIndex initial depth + 1)
        (sourceGeneratedCycleMaximalCanonicalPaidStep initial depth
          ).consumedStep.2.targetFutureBirth.actualExit)
  everyNextU8CoreDivergenceEmpty : ∀ observerFuel depth,
    let pulse := exactCanonicalSocietyRenewalPulseAt initial observerFuel depth
    IsEmpty (ExactCanonicalPulseNextU8CoreDivergenceAt pulse)
  everyNextRootFactorizationDeletionEmpty : ∀ observerFuel depth,
    let pulse := exactCanonicalSocietyRenewalPulseAt initial observerFuel depth
    IsEmpty (ExactCanonicalPulseNextRootFactorizationDeletionAt pulse)
  everyNextMacroNextDivergenceEmpty : ∀ observerFuel depth,
    let pulse := exactCanonicalSocietyRenewalPulseAt initial observerFuel depth
    IsEmpty (ExactCanonicalPulseNextMacroNextDivergenceAt pulse)
  everyPaymentReplayEmpty : ∀ left right,
    IsEmpty (ExactCanonicalPulsePaymentReplayAt initial left right)
  everyKReplayEmpty : ∀ left right,
    IsEmpty (ExactCanonicalPulseKReplayAt initial left right)
  everyPathReplayEmpty : ∀ left right,
    IsEmpty (ExactCanonicalPulsePathReplayAt initial left right)
  everyDifferentPairStrongKernel : ∀ {left right}, left ≠ right →
    ExactCanonicalSocietyRenewalPulseAt initial 0 left ∧
      ExactCanonicalSocietyRenewalPulseAt initial 0 right ∧
      (cycleReplayAt initial left).2.actualPath ≠
        (cycleReplayAt initial right).2.actualPath ∧
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget (cycleReplayAt initial left) =
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget (cycleReplayAt initial right) ∧
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).authorityK (cycleReplayAt initial left) ≠
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).authorityK (cycleReplayAt initial right) ∧
      cyclePaymentOccurrenceAt initial left ≠
        cyclePaymentOccurrenceAt initial right
  everyCofinalGapEmpty : ∀ n observerFuel,
    let readout := sourceGeneratedCanonicalSocietyCofinalReadout initial
    IsEmpty (ExactCanonicalCofinalPulseDeletionAt readout n observerFuel)
  everyRuntimeFinalityReportEmpty : ∀ depth,
    let step := sourceGeneratedCycleCanonicalRootLawStep initial depth
    IsEmpty (FinalUnrevisableRuntimeConstitutionAt step)
  everyRootLawNoGo : ∀ depth,
    CycleCanonicalRootLawStepNoGoAt initial depth
  everyCanonicalPaymentTargetDeletionNoGo : ∀ depth,
    let payment := cycleMaximalSourcePaymentAt initial depth
    IsEmpty (TargetFutureBirthDeletionAt initial depth payment) ∧
      (∀ channel : EssentialAccessChannel,
        IsEmpty
          (TargetChannelConsumerDeletionAt initial depth payment channel)) ∧
      IsEmpty (TargetExternalSourceOwnershipDeletionAt initial depth payment) ∧
      IsEmpty (TargetExternalRootConsumerDeletionAt initial depth payment)

theorem sourceGeneratedCanonicalSocietyCofinalReadoutNoGo
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    CanonicalSocietyCofinalReadoutNoGoAt initial where
  everySelfU8TickDeletionEmpty :=
    exactCanonicalSelfU8TickDeletion_isEmpty initial
  everyCompatibleFutureBirthDeletionEmpty :=
    exactCanonicalCompatibleFutureBirthDeletion_isEmpty initial
  everyPaidTargetFutureBirthDeletionEmpty :=
    exactCanonicalPaidTargetFutureBirthDeletion_isEmpty initial
  everyPulseOccurrenceCollapseEmpty := fun observerFuel depth =>
    exactCanonicalPulseSelfU8FutureBirthOccurrenceCollapse_isEmpty
      (exactCanonicalSocietyRenewalPulseAt initial observerFuel depth)
  everyPulseNextPaymentIsFutureBirthPayment := fun depth =>
    exactCanonicalPulseNextSelfU8Payment_isFutureBirthPayment
      (exactCanonicalSocietyRenewalPulseAt initial 0 depth)
  everyNextU8CoreDivergenceEmpty := fun observerFuel depth =>
    exactCanonicalPulseNextU8CoreDivergence_isEmpty
      (exactCanonicalSocietyRenewalPulseAt initial observerFuel depth)
  everyNextRootFactorizationDeletionEmpty := fun observerFuel depth =>
    exactCanonicalPulseNextRootFactorizationDeletion_isEmpty
      (exactCanonicalSocietyRenewalPulseAt initial observerFuel depth)
  everyNextMacroNextDivergenceEmpty := fun observerFuel depth =>
    exactCanonicalPulseNextMacroNextDivergence_isEmpty
      (exactCanonicalSocietyRenewalPulseAt initial observerFuel depth)
  everyPaymentReplayEmpty := exactCanonicalPulsePaymentReplay_isEmpty initial
  everyKReplayEmpty := exactCanonicalPulseKReplay_isEmpty initial
  everyPathReplayEmpty := exactCanonicalPulsePathReplay_isEmpty initial
  everyDifferentPairStrongKernel := exactCanonicalPulsePair_strongKernel initial
  everyCofinalGapEmpty := fun n observerFuel =>
    exactCanonicalCofinalPulseDeletion_isEmpty
      (sourceGeneratedCanonicalSocietyCofinalReadout initial) n observerFuel
  everyRuntimeFinalityReportEmpty :=
    (sourceGeneratedCanonicalSocietyCofinalReadout initial
      ).everyRuntimeFinalityReportEmpty
  everyRootLawNoGo := sourceGeneratedCycleCanonicalRootLawStepNoGo initial
  everyCanonicalPaymentTargetDeletionNoGo := fun depth =>
    let payment := cycleMaximalSourcePaymentAt initial depth
    ⟨targetFutureBirthDeletion_isEmpty initial depth payment,
      targetChannelConsumerDeletion_isEmpty initial depth payment,
      targetExternalSourceOwnershipDeletion_isEmpty initial depth payment,
      targetExternalRootConsumerDeletion_isEmpty initial depth payment⟩

end
end M14SourceGeneratedCanonicalSocietyCofinalReadoutNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyCofinalReadoutNoGo.exactCanonicalPulseSelfU8FutureBirthOccurrenceCollapse_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyCofinalReadoutNoGo.exactCanonicalPulsePair_strongKernel
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyCofinalReadoutNoGo.exactCanonicalCofinalPulseDeletion_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyCofinalReadoutNoGo.sourceGeneratedCanonicalSocietyCofinalReadoutNoGo
