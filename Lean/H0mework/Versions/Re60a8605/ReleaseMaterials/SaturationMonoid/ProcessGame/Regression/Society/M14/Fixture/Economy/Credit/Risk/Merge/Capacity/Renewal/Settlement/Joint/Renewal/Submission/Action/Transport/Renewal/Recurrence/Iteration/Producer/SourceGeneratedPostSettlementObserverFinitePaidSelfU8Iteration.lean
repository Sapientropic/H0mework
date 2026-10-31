import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Producer.SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence

/-!
# Pointwise finite iteration of the paid self-U8 recurrence

One proof-carrying authority-incidence cycle generates its paid-successor
certificate and feeds that exact certificate to the existing one-step
recurrence producer.  At a requested finite depth, the next cycle is always
the preceding step's literal `nextCycle`; no boundary-indexed canonical cycle
is selected again.

The recursion stores no list, registry, schedule, root, ledger, runtime or
completed future.  Every later step regenerates its paid certificate from the
previously generated morphism when that finite depth is requested.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14ProofCarryingPostSettlementObserverPaidSuccessorRenewal
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt

/-- Stable recurrence mouth.  It is the existing proof-relevant span,
authority, morphism and morphism consumer; no iteration registry is added. -/
abbrev CycleAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  AnyProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
    oldVisit sourceIndex boundary

/-- Exact morphism carried by one recurrence mouth. -/
def cycleMorphism
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (cycle : CycleAt oldVisit sourceIndex boundary) :=
  cycle.2.2.1

/-- The mouth already carries the independent morphism consumer. -/
theorem cycleMorphismCertificate
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (cycle : CycleAt oldVisit sourceIndex boundary) :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      (cycleMorphism cycle) :=
  cycle.2.2.2

/-- Paid renewal is regenerated from this exact morphism when the step is
requested.  It is not carried forward from an earlier step. -/
theorem currentPaidCertificate
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (cycle : CycleAt oldVisit sourceIndex boundary) :
    ProofCarryingPostSettlementObserverPaidSuccessorRenewalAt
      (cycleMorphism cycle) :=
  proofCarryingPostSettlementObserverPaidSuccessorRenewal
    (cycleMorphism cycle)

/-- One on-demand recurrence step.  Its only mouth is the exact input cycle;
the paid certificate and recurrence token are generated internally. -/
def oneStepAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (cycle : CycleAt oldVisit sourceIndex boundary) :
    SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
      (cycleMorphism cycle) (currentPaidCertificate cycle) :=
  sourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
    (cycleMorphism cycle) (currentPaidCertificate cycle)

@[simp] theorem oneStepAt_currentMorphism
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (cycle : CycleAt oldVisit sourceIndex boundary) :
    (oneStepAt cycle).currentMorphism = cycleMorphism cycle :=
  rfl

theorem oneStepAt_currentCertificate
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (cycle : CycleAt oldVisit sourceIndex boundary) :
    HEq (oneStepAt cycle).currentCertificate
      (currentPaidCertificate cycle) :=
  HEq.rfl

/-- Literal output mouth of one recurrence step. -/
def generatedNextCycleAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (cycle : CycleAt oldVisit sourceIndex boundary) :
    CycleAt oldVisit sourceIndex (boundary + 1) :=
  (oneStepAt cycle).nextCycle

@[simp] theorem generatedNextCycleAt_morphism
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (cycle : CycleAt oldVisit sourceIndex boundary) :
    cycleMorphism (generatedNextCycleAt cycle) =
      (oneStepAt cycle).nextMorphism :=
  rfl

/-- Pointwise finite producer.  The successor clause consumes only the
preceding step's generated `nextCycle`; it never calls a canonical
boundary-indexed constructor. -/
def cycleAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    (depth : Nat) → CycleAt oldVisit sourceIndex (boundary + depth)
  | 0 => initial
  | depth + 1 => generatedNextCycleAt (cycleAt initial depth)

/-- On-demand view of the exact step beginning at a requested finite depth. -/
def stepAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  oneStepAt (cycleAt initial depth)

@[simp] theorem cycleAt_zero
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    cycleAt initial 0 = initial :=
  rfl

@[simp] theorem cycleAt_succ
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    cycleAt initial (depth + 1) = (stepAt initial depth).nextCycle :=
  rfl

/-- At every depth the one-step mouth is the morphism carried by the cycle
generated at that depth. -/
@[simp] theorem stepAt_currentMorphism
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (stepAt initial depth).currentMorphism =
      cycleMorphism (cycleAt initial depth) :=
  rfl

/-- The next step is definitionally run on the preceding step's generated
cycle.  This is the non-reselection contract of the finite iteration. -/
@[simp] theorem stepAt_succ
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    stepAt initial (depth + 1) =
      oneStepAt ((stepAt initial depth).nextCycle) :=
  rfl

/-- In particular, the morphism mouth of step `depth + 1` is the exact fresh
morphism generated by step `depth`. -/
@[simp] theorem stepAt_succ_morphismMouth
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (stepAt initial (depth + 1)).currentMorphism =
      (stepAt initial depth).nextMorphism :=
  rfl

/-- The paid certificate at the successor mouth is regenerated from the
preceding generated morphism rather than transported from the old step. -/
theorem stepAt_succ_currentCertificate
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HEq (stepAt initial (depth + 1)).currentCertificate
      (proofCarryingPostSettlementObserverPaidSuccessorRenewal
        (stepAt initial depth).nextMorphism) :=
  HEq.rfl

/-- Final cycle produced at exactly the requested finite depth. -/
def finalCycleAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    CycleAt oldVisit sourceIndex (boundary + depth) :=
  cycleAt initial depth

def finalMorphismAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  cycleMorphism (finalCycleAt initial depth)

theorem finalMorphismCertificate
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      (finalMorphismAt initial depth) :=
  cycleMorphismCertificate (finalCycleAt initial depth)

/-- The final cycle is never an endpoint: requesting one further step
regenerates its paid certificate and recurrence from that final morphism. -/
def extendableNextStepAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  oneStepAt (finalCycleAt initial depth)

@[simp] theorem extendableNextStep_currentMorphism
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (extendableNextStepAt initial depth).currentMorphism =
      finalMorphismAt initial depth :=
  rfl

/-- Generated next cycle beyond the requested finite prefix. -/
def generatedFinalNextCycleAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    CycleAt oldVisit sourceIndex (boundary + depth + 1) :=
  (extendableNextStepAt initial depth).nextCycle

@[simp] theorem generatedFinalNextCycle_eq_cycleAt_succ
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    generatedFinalNextCycleAt initial depth =
      cycleAt initial (depth + 1) :=
  rfl

@[simp] theorem generatedFinalNextCycle_morphism
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    cycleMorphism (generatedFinalNextCycleAt initial depth) =
      (extendableNextStepAt initial depth).nextMorphism :=
  rfl

end
end M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration.oneStepAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration.cycleAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration.stepAt_succ_morphismMouth
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration.finalMorphismCertificate
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration.generatedFinalNextCycle_eq_cycleAt_succ
