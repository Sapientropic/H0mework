import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Stratification.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification

/-!
# Finite adaptive fair-stage observer policy

A policy may choose its next finite fair stage from the readout returned by
the preceding query.  Fuel makes every execution finite.  This syntax is a
post-emission diagnostic program, not a world process, runtime or stored
future schedule.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification

universe u

/-- A finite-depth adaptive observer.  `stop` may end early; `query` chooses a
stage and lets that finite archive select the remaining policy. -/
inductive CanonicalPaidReplayFairFiniteAdaptivePolicy
    (Answer : Type u) : Nat → Type (u + 1)
  | stop {fuel : Nat} (answer : Answer) :
      CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel
  | query {fuel : Nat} (stage : Nat)
      (next : CanonicalPaidReplayFairFiniteArchiveAt stage →
        CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel) :
      CanonicalPaidReplayFairFiniteAdaptivePolicy Answer (fuel + 1)

namespace CanonicalPaidReplayFairFiniteAdaptivePolicy

/-- Execute only the finitely many queries encoded by the policy. -/
def run
    {oldVisit : OldVisit} {sourceIndex : Nat} {Answer : Type u} :
    {fuel : Nat} →
      CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel →
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex →
      Answer
  | _, .stop answer, _ => answer
  | _, .query stage next, replay =>
      run
        (next
          (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            stage replay)) replay

/-- Largest stage encountered on the one finite branch selected by all-zero
tail readouts. -/
def zeroBranchBound {Answer : Type u} :
    {fuel : Nat} →
      CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel → Nat
  | _, .stop _ => 0
  | _, .query stage next =>
      max stage
        (zeroBranchBound
          (next (canonicalPaidReplayFairFiniteArchiveCode stage none)))

/-- Leaf answer reached on the same finite all-zero branch. -/
def zeroBranchAnswer {Answer : Type u} :
    {fuel : Nat} →
      CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel → Answer
  | _, .stop answer => answer
  | _, .query stage next =>
      zeroBranchAnswer
        (next (canonicalPaidReplayFairFiniteArchiveCode stage none))

/-- A replay later than the zero-branch bound follows exactly that branch and
returns its leaf answer. -/
theorem run_eq_zeroBranchAnswer_of_bound_lt
    {oldVisit : OldVisit} {sourceIndex : Nat} {Answer : Type u} {fuel : Nat}
    (policy : CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
    (late : zeroBranchBound policy < replay.1) :
    run policy replay = zeroBranchAnswer policy := by
  induction policy with
  | stop answer =>
      rfl
  | @query fuel stage next inductionHypothesis =>
      have stageLt : stage < replay.1 := by
        simp only [zeroBranchBound] at late
        omega
      have readoutZero :
          canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
                stage replay =
            canonicalPaidReplayFairFiniteArchiveCode stage none :=
        (canonicalPaidReplayFairFiniteArchive_zeroFibre_exact oldVisit
          sourceIndex stage replay).2 (by
            unfold CanonicalPaidReplayFairTailAt
            omega)
      rw [show run (.query stage next) replay =
          run (next
            (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit
              sourceIndex stage replay)) replay by rfl]
      rw [readoutZero]
      apply inductionHypothesis
      simp only [zeroBranchBound] at late
      omega

/-- The cutoff is computed solely from a requested lower bound and the
finite zero branch of the supplied policy. -/
def adaptivePolicyCutoff {Answer : Type u} {fuel : Nat}
    (requestedStage : Nat)
    (policy : CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel) : Nat :=
  max requestedStage (zeroBranchBound policy) + 1

theorem requestedStage_lt_adaptivePolicyCutoff
    {Answer : Type u} {fuel : Nat} (requestedStage : Nat)
    (policy : CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel) :
    requestedStage < adaptivePolicyCutoff requestedStage policy := by
  unfold adaptivePolicyCutoff
  omega

theorem zeroBranchBound_lt_adaptivePolicyCutoff
    {Answer : Type u} {fuel : Nat} (requestedStage : Nat)
    (policy : CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel) :
    zeroBranchBound policy < adaptivePolicyCutoff requestedStage policy := by
  unfold adaptivePolicyCutoff
  omega

end CanonicalPaidReplayFairFiniteAdaptivePolicy

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy.CanonicalPaidReplayFairFiniteAdaptivePolicy.run_eq_zeroBranchAnswer_of_bound_lt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy.CanonicalPaidReplayFairFiniteAdaptivePolicy.requestedStage_lt_adaptivePolicyCutoff
