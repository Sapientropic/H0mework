import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.NoGo.SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Lifecycle.Producer.SourceGeneratedProofCarryingPaidExitLifecycleMaximum

/-!
# Paid-exit lifecycle stitch on the finite self-U8 iteration

Each recursively generated self-U8 cycle already carries one exact paid replay.
That replay index regenerates the existing four-stage paid-exit lifecycle and
its proof-carrying maximum.  The cycle morphism's paid renewal and lifecycle
stage zero are the same source producer, not parallel certificates.

At adjacent cycles, the previous lifecycle's stage one and the next
lifecycle's stage zero are the same actual renewal occurrence.  Only the
initial cycle and an explicitly requested finite depth enter this file; no
lifecycle, authority, continuation, history, root, ledger, registry or future
is accepted or stored.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
open M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum

/-- Absolute paid-replay index physically carried by this generated cycle. -/
def cycleLifecycleIndex
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Nat :=
  (cycleReplayAt initial depth).1

@[simp] theorem cycleLifecycleIndex_exact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    cycleLifecycleIndex initial depth = boundary + depth + 2 :=
  cycleReplayAt_index initial depth

/-- Lifecycle stage zero regenerated at the cycle's exact paid index. -/
def cycleLifecycle
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  paidExitLifecycleStandingRenewalAt oldVisit sourceIndex
    (cycleLifecycleIndex initial depth)

/-- Full existing lifecycle maximum regenerated at that same exact index. -/
def cycleLifecycleMaximum
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth) :=
  sourceGeneratedProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
    (cycleLifecycleIndex initial depth)

/-- The regenerated maximum's first paid edge is carried by this exact cycle
lifecycle, not by an independently selected standing renewal. -/
theorem cycleLifecycleMaximum_firstPaidNext
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HEq (cycleLifecycle initial depth).sourcePayment.nextPaidBy
      (cycleLifecycle initial depth).targetConsequence.outerRootEvent.occurrence :=
  (cycleLifecycleMaximum initial depth).rooted.occurrenceSpine.firstPaidNext

/-- The morphism-side paid renewal and lifecycle stage zero are literally the
same source-generated producer at the span-carried replay index. -/
theorem cycleMorphismPaidRenewal_eq_cycleLifecycle
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    paidRenewalAt (cycleMorphism (cycleAt initial depth)) =
      cycleLifecycle initial depth := by
  unfold cycleLifecycle cycleLifecycleIndex
  rcases cycleAt initial depth with
    ⟨span, authority, ⟨morphism, certificate⟩⟩
  cases morphism
  cases span
  rfl

/-- The lifecycle's first event is the exact source event retained by this
cycle's span. -/
theorem cycleLifecycle_sourceEvent_isCycleSpanSourceEvent
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (cycleLifecycle initial depth).sourceConsequence.outerRootEvent =
      (sourceSubmission
        (legislationSpan
          (cycleMorphism (cycleAt initial depth)))).exactEvent := by
  rw [← cycleMorphismPaidRenewal_eq_cycleLifecycle initial depth]
  exact paidRenewal_sourceEvent_isSpanSourceEvent
    (cycleMorphism (cycleAt initial depth))

/-- Its embedded Payment is likewise the exact external Payment retained by
the same cycle span. -/
theorem cycleLifecycle_sourcePayment_isCycleSpanPayment
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (cycleLifecycle initial depth).sourceConsequence.actualExit.paymentOccurrence =
      targetPaymentOccurrence
        (legislationSpan
          (cycleMorphism (cycleAt initial depth))) := by
  rw [← cycleMorphismPaidRenewal_eq_cycleLifecycle initial depth]
  exact paidRenewal_sourcePayment_isSpanTargetPayment
    (cycleMorphism (cycleAt initial depth))

/-- Stage indices are inherited from the existing four-stage lifecycle. -/
def cycleLifecycleStageZero : PaidExitLifecycleStage := ⟨0, by decide⟩
def cycleLifecycleStageOne : PaidExitLifecycleStage := ⟨1, by decide⟩

def cycleLifecycleStageRenewalAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (stage : PaidExitLifecycleStage) :=
  paidExitLifecycleStageRenewalAt oldVisit sourceIndex
    (cycleLifecycleIndex initial depth) stage

/-- Absolute paid index of one lifecycle stage in the finite iteration. -/
def cycleLifecycleAbsoluteStageIndexAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (stage : PaidExitLifecycleStage) : Nat :=
  cycleLifecycleIndex initial depth + stage.1

@[simp] theorem cycleLifecycleAbsoluteStageIndex_exact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (stage : PaidExitLifecycleStage) :
    cycleLifecycleAbsoluteStageIndexAt initial depth stage =
      boundary + depth + 2 + stage.1 := by
  rw [cycleLifecycleAbsoluteStageIndexAt, cycleLifecycleIndex_exact]

@[simp] theorem cycleLifecycleStageZero_eq_cycleLifecycle
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    cycleLifecycleStageRenewalAt initial depth cycleLifecycleStageZero =
      cycleLifecycle initial depth :=
  rfl

/-- The preceding lifecycle's stage one and the successor lifecycle's stage
zero are one producer occurrence; this stitch introduces no parallel overlap
certificate. -/
@[simp] theorem cycleLifecycleStageOne_eq_nextStageZero
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    cycleLifecycleStageRenewalAt initial depth cycleLifecycleStageOne =
      cycleLifecycleStageRenewalAt initial (depth + 1)
        cycleLifecycleStageZero := by
  unfold cycleLifecycleStageRenewalAt cycleLifecycleIndex
  rfl

/-- Direct endpoint readouts of the same overlap token.  These are exposed so
downstream consumers never need to reconstruct incidence from arithmetic. -/
@[simp] theorem cycleLifecycleTargetEvent_eq_nextSourceEvent
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (cycleLifecycle initial depth).targetConsequence.outerRootEvent =
      (cycleLifecycle initial (depth + 1)).sourceConsequence.outerRootEvent := by
  unfold cycleLifecycle cycleLifecycleIndex
  rfl

@[simp] theorem cycleLifecycleTargetPayment_eq_nextSourcePayment
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (cycleLifecycle initial depth).targetConsequence.actualExit.paymentOccurrence =
      (cycleLifecycle initial
        (depth + 1)).sourceConsequence.actualExit.paymentOccurrence := by
  unfold cycleLifecycle cycleLifecycleIndex
  rfl

@[simp] theorem cycleLifecycleTargetAuthority_eq_nextSourceAuthority
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (cycleLifecycle initial depth).targetOuterAuthority =
      (cycleLifecycle initial (depth + 1)).sourceOuterAuthority := by
  unfold cycleLifecycle cycleLifecycleIndex
  rfl

@[simp] theorem cycleLifecycleTargetK_eq_nextSourceK
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (cycleLifecycle initial depth).targetActualServiceK =
      (cycleLifecycle initial (depth + 1)).sourceActualServiceK := by
  unfold cycleLifecycle cycleLifecycleIndex
  rfl

@[simp] theorem cycleLifecycleAbsoluteStage_overlap
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    cycleLifecycleAbsoluteStageIndexAt initial depth cycleLifecycleStageOne =
      cycleLifecycleAbsoluteStageIndexAt initial (depth + 1)
        cycleLifecycleStageZero := by
  unfold cycleLifecycleAbsoluteStageIndexAt
  rw [cycleLifecycleIndex_exact, cycleLifecycleIndex_exact]
  change boundary + depth + 2 + 1 = boundary + (depth + 1) + 2 + 0
  omega

/-- Combined overlap seal: the arithmetic slot and actual renewal producer
both coincide. -/
theorem cycleLifecycleOverlap_exact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    cycleLifecycleAbsoluteStageIndexAt initial depth cycleLifecycleStageOne =
        cycleLifecycleAbsoluteStageIndexAt initial (depth + 1)
          cycleLifecycleStageZero ∧
      cycleLifecycleStageRenewalAt initial depth cycleLifecycleStageOne =
        cycleLifecycleStageRenewalAt initial (depth + 1)
          cycleLifecycleStageZero :=
  ⟨cycleLifecycleAbsoluteStage_overlap initial depth,
    cycleLifecycleStageOne_eq_nextStageZero initial depth⟩

end
end M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch.cycleMorphismPaidRenewal_eq_cycleLifecycle
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch.cycleLifecycleMaximum_firstPaidNext
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch.cycleLifecycle_sourceEvent_isCycleSpanSourceEvent
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch.cycleLifecycle_sourcePayment_isCycleSpanPayment
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch.cycleLifecycleStageOne_eq_nextStageZero
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch.cycleLifecycleTargetEvent_eq_nextSourceEvent
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch.cycleLifecycleTargetPayment_eq_nextSourcePayment
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch.cycleLifecycleTargetAuthority_eq_nextSourceAuthority
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch.cycleLifecycleTargetK_eq_nextSourceK
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch.cycleLifecycleOverlap_exact
