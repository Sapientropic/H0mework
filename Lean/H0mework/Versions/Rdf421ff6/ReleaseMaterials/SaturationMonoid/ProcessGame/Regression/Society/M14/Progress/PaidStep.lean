import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Progress.Frontier
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Progress.SameEdgeNovelty
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Celebration.Consumer.ProofCarryingContributionCapacityMacroFutureBirth
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Consumer.ProofCarryingFiniteCycleCanonicalRootLaw

/-!
# Canonical preservation and strict productive progress

The comparison keeps the source and target exit constitutions and orders the
images of their already generated, paid FutureBirth prefixes. The exact caller
Payment supplies the transition; the target native birth supplies strictness.
The root-law consumer retains its real lifecycle `+2` offset.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14ProofCarryingContributionCapacityMacroFutureBirth
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedCycleMaximalCanonicalPaidStep
open M14ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14ProofCarryingFiniteCycleCanonicalRootLaw

/-- Canonical structure at both ends and strict growth of paid actionable
occurrences. This is an explicit structural order, not an observer utility. -/
def StrictCanonicalProgressAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (before after : Nat) : Prop :=
  FiniteExitCapacityConstitutionAt initial before ∧
    FiniteExitCapacityConstitutionAt initial after ∧
    authoritySupport oldVisit sourceIndex 0 (cycleLifecycleIndex initial before + 1) ⊂
      authoritySupport oldVisit sourceIndex 0 (cycleLifecycleIndex initial after + 1)

/-- Every later canonical cycle strictly extends the earlier paid frontier;
the converse excludes a disguised return to an old state. -/
theorem strictCanonicalProgress_iff_lt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (before after : Nat) :
    StrictCanonicalProgressAt initial before after ↔ before < after := by
  constructor
  · rintro ⟨_, _, h⟩
    have hlt := (authoritySupport_strict_iff oldVisit sourceIndex 0 _ _).mp h
    rw [cycleLifecycleIndex_exact, cycleLifecycleIndex_exact] at hlt
    omega
  · intro h
    refine ⟨sourceGeneratedFiniteExitCapacityConstitutionAt initial before,
      sourceGeneratedFiniteExitCapacityConstitutionAt initial after, ?_⟩
    apply authoritySupport_strictMono oldVisit sourceIndex 0
    rw [cycleLifecycleIndex_exact, cycleLifecycleIndex_exact]
    omega

theorem strictCanonicalProgress_irrefl
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    ¬ StrictCanonicalProgressAt initial depth depth := by
  rw [strictCanonicalProgress_iff_lt]
  exact Nat.lt_irrefl depth

theorem strictCanonicalProgress_trans
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {a b c : Nat}
    (ab : StrictCanonicalProgressAt initial a b)
    (bc : StrictCanonicalProgressAt initial b c) :
    StrictCanonicalProgressAt initial a c :=
  ⟨ab.1, bc.2.1, lt_trans ab.2.2 bc.2.2⟩

/-- One exact paid transition: full prior preservation, a fresh authority
outside the entire old prefix, actual service/exit and independent residual
consumption, and the original root-law/whole-ledger/next audit together. -/
structure StrictCanonicalPaidStepAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (observerFuel depth : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth)) : Prop where
  private mk ::
  paymentPreservation : InputPaymentPreservationAuditAt initial depth payment
  targetPreservation : InputPaymentTargetRichAuditAt initial observerFuel depth payment
  strictProgress : StrictCanonicalProgressAt initial depth (depth + 1)
  oldFrontierRetained :
    frontier oldVisit sourceIndex 0 (cycleLifecycleIndex initial depth + 1 + 1) =
      frontier oldVisit sourceIndex 0 (cycleLifecycleIndex initial depth + 1) ++
        [contributionCapacityPostSettlementFutureBirthOccurrenceAt oldVisit sourceIndex
            (cycleLifecycleIndex initial depth + 1)]
  newAuthority :
    let difference := sameEdgeResponsibilityDifference initial depth
    difference.rightReplay.2.authorityK ∈
        authoritySupport oldVisit sourceIndex 0 (cycleLifecycleIndex initial depth + 1 + 1) ∧
      difference.rightReplay.2.authorityK ∉
        authoritySupport oldVisit sourceIndex 0 (cycleLifecycleIndex initial depth + 1)
  noveltyFollowsPayment :
    HEq payment.nextPaidBy
      (sameEdgeResponsibilityDifference initial depth).rightReplay.2.rootEvent.occurrence
  sameOriginalWholeLedger :
    HEq (sameEdgeResponsibilityDifference initial depth).leftReplay.2.rootEvent.wholeLedgerWriteBack
      (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth payment).consumedStep.1.sourceWholeLedgerWriteBack
  visibleResidualConsumer :
    let difference := sameEdgeResponsibilityDifference initial depth
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
        difference.rightActualExit) ∧
      difference.rightActualExit.paymentOccurrence.rootOccurrence = difference.rightExactRootEvent ∧
      difference.rightActualExit.paymentOccurrence.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry
  channelsRetainOriginalIdentity : ∀ channel : EssentialAccessChannel,
    let difference := sameEdgeResponsibilityDifference initial depth
    ((difference.consumed).2.leftWitnessReturn channel).1.actor
        M14EssentialAccessRelationFixture.essentialAccessRelationCompiler = channelActor channel ∧
      M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationOf
        ((difference.consumed).2.leftWitnessReturn channel).1 = channelRelation channel ∧
      ((difference.consumed).2.rightWitnessReturn channel).1.actor
        M14EssentialAccessRelationFixture.essentialAccessRelationCompiler = channelActor channel ∧
      M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationOf
        ((difference.consumed).2.rightWitnessReturn channel).1 = channelRelation channel
  sourceBirthAudit : CanonicalContributionCapacityMacroFutureBirthAuditAt
    oldVisit sourceIndex (cycleLifecycleIndex initial depth)
  targetBirthAudit : CanonicalContributionCapacityMacroFutureBirthAuditAt
    oldVisit sourceIndex (cycleLifecycleIndex initial depth + 1)
  exactPaidTargetBirth :
    HEq payment.nextPaidBy
      (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt
        oldVisit sourceIndex (cycleLifecycleIndex initial depth + 1)).postRootEvent.occurrence
  rootLawTransition :
    ProofCarryingCycleCanonicalRootLawTransitionAt initial observerFuel depth
      (sourceGeneratedCycleCanonicalRootLawStep initial depth)

/-- Neither preservation nor novelty is a caller hypothesis. Both are
produced from the original source, cycle and exact Payment. -/
theorem preservation_and_novelty_strictlyBetter
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (observerFuel depth : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth)) :
    StrictCanonicalPaidStepAt initial observerFuel depth payment where
  paymentPreservation := inputPaymentPreservationAuditAt initial depth payment
  targetPreservation := inputPaymentTargetRichAuditAt initial observerFuel depth payment
  strictProgress := (strictCanonicalProgress_iff_lt initial depth (depth + 1)).mpr
    (Nat.lt_succ_self depth)
  oldFrontierRetained := by
    simpa only [Nat.zero_add] using frontier_succ oldVisit sourceIndex 0
      (cycleLifecycleIndex initial depth + 1)
  newAuthority := by
    dsimp only
    rw [(sameEdge_authorityK_exact initial depth).2]
    simpa only [Nat.zero_add, authorityAt,
      contributionCapacityPostSettlementFutureBirthCurrentAt,
      contributionCapacityPostSettlementCanonicalCurrentDepthAt] using
      freshAuthority oldVisit sourceIndex 0 (cycleLifecycleIndex initial depth + 1)
  noveltyFollowsPayment := (sameEdge_callerPayment_nextPaidBy initial depth payment).2
  sameOriginalWholeLedger := sameEdge_wholeLedger_is_original initial depth payment
  visibleResidualConsumer := sameEdge_independentConsumer_and_originalEntry initial depth
  channelsRetainOriginalIdentity := sameEdge_channels_return_to_original_sources initial depth
  sourceBirthAudit := canonicalContributionCapacityMacroFutureBirthAuditAt oldVisit
    sourceIndex (cycleLifecycleIndex initial depth)
  targetBirthAudit := canonicalContributionCapacityMacroFutureBirthAuditAt oldVisit
    sourceIndex (cycleLifecycleIndex initial depth + 1)
  exactPaidTargetBirth :=
    (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth payment).paidNextExact
  rootLawTransition := proofCarryingCycleCanonicalRootLawTransition observerFuel
    (sourceGeneratedCycleCanonicalRootLawStep initial depth)

/-- Every edge in a requested finite prefix, plus its generated next edge.
No list of future currents, payments or novelties is stored. -/
structure FiniteStrictCanonicalProgressAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) : Prop where
  private mk ::
  rootLaw : ProofCarryingFiniteCycleCanonicalRootLawAt initial fuel
  everyPayment : ∀ edge : Fin (fuel + 1), ∀ payment :
    CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleLifecycleIndex initial edge.1),
    StrictCanonicalPaidStepAt initial (fuel + 1) edge.1 payment
  generatedNext : ∀ payment : CanonicalPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex (cycleLifecycleIndex initial (fuel + 1)),
    StrictCanonicalPaidStepAt initial (fuel + 2) (fuel + 1) payment
  allEarlierLater : ∀ before after : Nat, before < after → after ≤ fuel + 1 →
    StrictCanonicalProgressAt initial before after

theorem finiteStrictCanonicalProgressFromRootLaw
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat)
    (law : ProofCarryingFiniteCycleCanonicalRootLawAt initial fuel) :
    FiniteStrictCanonicalProgressAt initial fuel where
  rootLaw := law
  everyPayment := fun edge payment =>
    preservation_and_novelty_strictlyBetter initial (fuel + 1) edge.1 payment
  generatedNext := preservation_and_novelty_strictlyBetter initial (fuel + 2) (fuel + 1)
  allEarlierLater := fun before after h _ =>
    (strictCanonicalProgress_iff_lt initial before after).mpr h

theorem finiteStrictCanonicalProgress
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    FiniteStrictCanonicalProgressAt initial fuel :=
  finiteStrictCanonicalProgressFromRootLaw initial fuel
    (proofCarryingFiniteCycleCanonicalRootLaw initial fuel)

end
end SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress

#print axioms SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress.preservation_and_novelty_strictlyBetter
#print axioms SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress.finiteStrictCanonicalProgress
