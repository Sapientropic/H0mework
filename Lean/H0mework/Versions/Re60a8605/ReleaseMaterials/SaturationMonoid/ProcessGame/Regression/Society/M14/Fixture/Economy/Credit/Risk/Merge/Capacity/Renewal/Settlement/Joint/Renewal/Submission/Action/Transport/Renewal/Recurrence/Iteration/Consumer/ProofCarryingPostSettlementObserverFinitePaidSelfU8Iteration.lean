import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.NoGo.SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Consumer.ProofCarryingPostSettlementObserverPaidSelfU8Recurrence

/-!
# Proof-carrying finite causal iteration of paid self-U8 cycles

For one explicit `fuel`, this audit consumes exactly `fuel + 1` on-demand
cycles and `fuel` recurrence edges.  Every successor is the preceding edge's
literal `nextCycle`; every node retains the complete authority-incidence,
PCL/self-U8, runtime and macro-next certificate; every edge retains the four
occurrence bridges and arbitrary worthiness no-gos.

All arbitrary node pairs are compared directly through exact temporal
indices.  The audit is a `Prop` indexed by the requested fuel.  It stores no
node list, schedule, registry, runtime, root, ledger or completed future, and
it exposes one further generated cycle beyond the audited prefix.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPostSettlementObserverFinitePaidSelfU8Iteration

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14UBIProofCarryingRootRestriction
open M14SourceGeneratedContributionCapacityFutureBirthPulse
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14ProofCarryingPostSettlementObserverPaidSuccessorRenewal
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo
open M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation
open M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo

/-- Bounded audit of a pointwise-generated recurrence prefix.  `Fin fuel`
indexes its paid edges and `Fin (fuel + 1)` its already generated nodes. -/
structure ProofCarryingPostSettlementObserverFinitePaidSelfU8IterationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) : Prop where
  private mk ::
  baseExact : cycleAt initial 0 = initial
  everyEdgeConsumesPrevious : ∀ edge : Fin fuel,
    cycleAt initial (edge.1 + 1) = (stepAt initial edge.1).nextCycle
  everySuccessorMorphismMouth : ∀ edge : Fin fuel,
    cycleMorphism (cycleAt initial (edge.1 + 1)) =
      (stepAt initial edge.1).nextMorphism
  everySuccessorPaidCertificateRegenerated : ∀ edge : Fin fuel,
    HEq (stepAt initial (edge.1 + 1)).currentCertificate
      (proofCarryingPostSettlementObserverPaidSuccessorRenewal
        (stepAt initial edge.1).nextMorphism)
  everyNodeMorphismCertificate : ∀ node : Fin (fuel + 1),
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      (cycleMorphism (cycleAt initial node.1))
  everyEdgeRecurrenceCertificate : ∀ edge : Fin fuel,
    ProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
      (stepAt initial edge.1)
  everyEdgeAntiRetaliationExact : ∀ edge : Fin fuel,
    (antiRetaliationAt (stepAt initial edge.1)).standingRenewal =
      (stepAt initial edge.1).currentPaidRenewal
  everyEdgeNoOccurrenceReconstruction : ∀ _edge : Fin fuel,
    ¬ ∃ reconstruct : ContributionCapacityFutureBirthPulse →
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
      Function.LeftInverse reconstruct
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget
  everyEdgeNoAuthorityFactorization : ∀ _edge : Fin fuel,
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex))
  everyEdgeNoFaithfulReconstruction : ∀ _edge : Fin fuel,
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex))
  everyEdgeAdministrativeNoAuthority : ∀ _edge : Fin fuel,
    ∀ label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
        Bool,
      ¬ Nonempty
        (AuthorityFactorization
          (administrativeRetaliationObserver oldVisit sourceIndex label))
  everyEdgeAdministrativeNoOccurrenceReconstruction : ∀ _edge : Fin fuel,
    ∀ label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
        Bool,
      ¬ ∃ reconstruct : AdministrativeRetaliationVisible →
          AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex,
        Function.LeftInverse reconstruct
          (administrativeRetaliationObserver oldVisit sourceIndex label
            ).forget
  everyEdgeAdministrativeNoFaithfulReconstruction : ∀ _edge : Fin fuel,
    ∀ label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
        Bool,
      ¬ Nonempty
        (FaithfulAuthorityReconstruction
          (administrativeRetaliationObserver oldVisit sourceIndex label))
  administrativeLabelsDoNotChangeRestriction :
    administrativeEligibilityReadout false =
      administrativeEligibilityReadout true
  everyNodeReplayExact : ∀ node : Fin (fuel + 1),
    cycleReplayAt initial node.1 =
      contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        (boundary + node.1 + 2)
  everyPairVisibleNormalFormEqual : ∀ left right : Fin (fuel + 1),
    (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex).forget (cycleReplayAt initial left.1) =
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex).forget (cycleReplayAt initial right.1)
  everyDifferentPairStrongKernel : ∀ left right : Fin (fuel + 1),
    left ≠ right →
      (cycleReplayAt initial left.1).2.actualPath ≠
          (cycleReplayAt initial right.1).2.actualPath ∧
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
            sourceIndex).forget (cycleReplayAt initial left.1) =
          (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
            sourceIndex).forget (cycleReplayAt initial right.1) ∧
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
            sourceIndex).authorityK (cycleReplayAt initial left.1) ≠
          (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
            sourceIndex).authorityK (cycleReplayAt initial right.1) ∧
        cyclePaymentOccurrenceAt initial left.1 ≠
          cyclePaymentOccurrenceAt initial right.1
  everyPairPaymentReplayEmpty : ∀ left right : Fin (fuel + 1),
    IsEmpty (ExactFiniteCyclePaymentReplaysAt initial left.1 right.1)
  finalCycleExact : finalCycleAt initial fuel = cycleAt initial fuel
  finalMorphismCertificate :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      (finalMorphismAt initial fuel)
  finalStepRecurrenceCertificate :
    ProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
      (extendableNextStepAt initial fuel)
  finalNextCycleMouth :
    generatedFinalNextCycleAt initial fuel = cycleAt initial (fuel + 1)
  finalNextMorphismMouth :
    cycleMorphism (generatedFinalNextCycleAt initial fuel) =
      (extendableNextStepAt initial fuel).nextMorphism
  finalNextMorphismCertificate :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      (cycleMorphism (generatedFinalNextCycleAt initial fuel))
  finalToNextStrongKernel :
    (cycleReplayAt initial fuel).2.actualPath ≠
        (cycleReplayAt initial (fuel + 1)).2.actualPath ∧
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget (cycleReplayAt initial fuel) =
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget (cycleReplayAt initial (fuel + 1)) ∧
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).authorityK (cycleReplayAt initial fuel) ≠
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).authorityK (cycleReplayAt initial (fuel + 1)) ∧
      cyclePaymentOccurrenceAt initial fuel ≠
        cyclePaymentOccurrenceAt initial (fuel + 1)

/-- Direct consumer of one explicitly requested finite recurrence prefix. -/
theorem proofCarryingPostSettlementObserverFinitePaidSelfU8Iteration
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    ProofCarryingPostSettlementObserverFinitePaidSelfU8IterationAt initial
      fuel where
  baseExact := cycleAt_zero initial
  everyEdgeConsumesPrevious := fun edge => cycleAt_succ initial edge.1
  everySuccessorMorphismMouth := fun edge => by
    rfl
  everySuccessorPaidCertificateRegenerated := fun edge =>
    stepAt_succ_currentCertificate initial edge.1
  everyNodeMorphismCertificate := fun node =>
    cycleMorphismCertificate (cycleAt initial node.1)
  everyEdgeRecurrenceCertificate := fun edge =>
    proofCarryingPostSettlementObserverPaidSelfU8Recurrence
      (stepAt initial edge.1)
  everyEdgeAntiRetaliationExact := fun edge =>
    stepAntiRetaliationStandingRenewal_isCurrentPaidRenewal initial edge.1
  everyEdgeNoOccurrenceReconstruction := fun edge =>
    stepNext_noOccurrenceReconstruction initial edge.1
  everyEdgeNoAuthorityFactorization := fun edge =>
    stepNext_noAuthorityFactorization initial edge.1
  everyEdgeNoFaithfulReconstruction := fun edge =>
    stepNext_noFaithfulReconstruction initial edge.1
  everyEdgeAdministrativeNoAuthority := fun edge label =>
    stepAdministrativeLabel_noAuthorityFactorization initial edge.1 label
  everyEdgeAdministrativeNoOccurrenceReconstruction := fun edge label =>
    stepAdministrativeLabel_noOccurrenceLeftInverse initial edge.1 label
  everyEdgeAdministrativeNoFaithfulReconstruction := fun edge label =>
    stepAdministrativeLabel_noFaithfulReconstruction initial edge.1 label
  administrativeLabelsDoNotChangeRestriction :=
    administrativeLabels_doNotChangeIterationRestriction
  everyNodeReplayExact := fun node => cycleReplayAt_exact initial node.1
  everyPairVisibleNormalFormEqual := fun left right =>
    cycleVisibleNormalForm_eq initial left.1 right.1
  everyDifferentPairStrongKernel := fun left right different =>
    cyclePairwiseStrongKernel initial (by
      intro valuesEqual
      exact different (Fin.ext valuesEqual))
  everyPairPaymentReplayEmpty := fun left right =>
    exactFiniteCyclePaymentReplays_isEmpty initial left.1 right.1
  finalCycleExact := rfl
  finalMorphismCertificate := finalMorphismCertificate initial fuel
  finalStepRecurrenceCertificate :=
    proofCarryingPostSettlementObserverPaidSelfU8Recurrence
      (extendableNextStepAt initial fuel)
  finalNextCycleMouth := generatedFinalNextCycle_eq_cycleAt_succ initial fuel
  finalNextMorphismMouth := generatedFinalNextCycle_morphism initial fuel
  finalNextMorphismCertificate :=
    cycleMorphismCertificate (generatedFinalNextCycleAt initial fuel)
  finalToNextStrongKernel := cyclePairwiseStrongKernel initial (by omega)

/-- One starting cycle and its bounded proof-carrying audit.  Only the initial
cycle is selected once; all successors come from its previous outputs. -/
abbrev AnyProofCarryingPostSettlementObserverFinitePaidSelfU8IterationAt
    (oldVisit : OldVisit) (sourceIndex boundary fuel : Nat) :=
  { initial : CycleAt oldVisit sourceIndex boundary //
    ProofCarryingPostSettlementObserverFinitePaidSelfU8IterationAt initial fuel }

def canonicalProofCarryingPostSettlementObserverFinitePaidSelfU8IterationAt
    (oldVisit : OldVisit) (sourceIndex boundary fuel : Nat) :
    AnyProofCarryingPostSettlementObserverFinitePaidSelfU8IterationAt oldVisit
      sourceIndex boundary fuel :=
  let initial :=
    canonicalProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      oldVisit sourceIndex boundary
  ⟨initial,
    proofCarryingPostSettlementObserverFinitePaidSelfU8Iteration initial fuel⟩

end
end M14ProofCarryingPostSettlementObserverFinitePaidSelfU8Iteration
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPostSettlementObserverFinitePaidSelfU8Iteration.proofCarryingPostSettlementObserverFinitePaidSelfU8Iteration
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPostSettlementObserverFinitePaidSelfU8Iteration.canonicalProofCarryingPostSettlementObserverFinitePaidSelfU8IterationAt
