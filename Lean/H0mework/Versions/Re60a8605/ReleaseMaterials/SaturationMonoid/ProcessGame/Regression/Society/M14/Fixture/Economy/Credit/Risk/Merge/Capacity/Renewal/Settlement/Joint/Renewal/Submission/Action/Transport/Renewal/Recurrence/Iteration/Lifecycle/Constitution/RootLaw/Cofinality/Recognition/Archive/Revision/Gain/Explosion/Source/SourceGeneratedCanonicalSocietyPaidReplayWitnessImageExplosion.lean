import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Source.SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveStrictGain

/-!
# Cofinal witness-image explosion

The actual range of the recursively generated finite archive readout grows
strictly at every revision.  Its cardinal sequence is strictly monotone,
has a linear lower bound, never stabilizes, and exceeds every requested
finite capacity after a later generated depth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayWitnessImageExplosion

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision
open M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveStrictGain

/-- Actual image cardinal at one recursively generated revision depth. -/
noncomputable def canonicalPaidReplayFiniteArchiveActualImageCardAt
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive)
    (depth : Nat) : Nat :=
  let state :=
    canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
      sourceIndex lowerBound archive depth
  @Fintype.card (Set.range state.archiveReadout)
    (canonicalPaidReplayFiniteArchiveImageFintype state)

theorem canonicalPaidReplayFiniteArchiveActualImageCard_succ_lt
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive)
    (depth : Nat) :
    canonicalPaidReplayFiniteArchiveActualImageCardAt oldVisit sourceIndex
        lowerBound archive depth <
      canonicalPaidReplayFiniteArchiveActualImageCardAt oldVisit sourceIndex
        lowerBound archive (depth + 1) := by
  exact
    canonicalPaidReplayFiniteArchiveActualImage_card_strictlyGrows
      (canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex lowerBound archive depth)

theorem canonicalPaidReplayFiniteArchiveActualImageCard_strictMono
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    StrictMono
      (canonicalPaidReplayFiniteArchiveActualImageCardAt oldVisit sourceIndex
        lowerBound archive) := by
  apply strictMono_nat_of_lt_succ
  exact
    canonicalPaidReplayFiniteArchiveActualImageCard_succ_lt oldVisit
      sourceIndex lowerBound archive

theorem canonicalPaidReplayFiniteArchiveActualImageCard_injective
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    Function.Injective
      (canonicalPaidReplayFiniteArchiveActualImageCardAt oldVisit sourceIndex
        lowerBound archive) :=
  (canonicalPaidReplayFiniteArchiveActualImageCard_strictMono oldVisit
    sourceIndex lowerBound archive).injective

/-- Every interval of revisions contributes at least its length in newly
attained archive values. -/
theorem canonicalPaidReplayFiniteArchiveActualImageCard_intervalLowerBound
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    ∀ start steps,
      canonicalPaidReplayFiniteArchiveActualImageCardAt oldVisit sourceIndex
          lowerBound archive start + steps ≤
        canonicalPaidReplayFiniteArchiveActualImageCardAt oldVisit sourceIndex
          lowerBound archive (start + steps) := by
  intro start steps
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
      have step :=
        canonicalPaidReplayFiniteArchiveActualImageCard_succ_lt oldVisit
          sourceIndex lowerBound archive (start + steps)
      simp only [Nat.add_assoc] at step ⊢
      omega

theorem canonicalPaidReplayFiniteArchiveActualImageCard_linearLowerBound
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    ∀ depth,
      canonicalPaidReplayFiniteArchiveActualImageCardAt oldVisit sourceIndex
          lowerBound archive 0 + depth ≤
        canonicalPaidReplayFiniteArchiveActualImageCardAt oldVisit sourceIndex
          lowerBound archive depth := by
  intro depth
  simpa using
    canonicalPaidReplayFiniteArchiveActualImageCard_intervalLowerBound oldVisit
      sourceIndex lowerBound archive 0 depth

/-- Cofinal explosion: one explicit later depth simultaneously exceeds a
requested revision depth and a requested actual-image capacity. -/
theorem canonicalPaidReplayFiniteArchiveActualImageCard_cofinal
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive)
    (requestedDepth capacityBound : Nat) :
    ∃ depth,
      requestedDepth < depth ∧
        capacityBound <
          canonicalPaidReplayFiniteArchiveActualImageCardAt oldVisit
            sourceIndex lowerBound archive depth := by
  let steps := capacityBound + 1
  let depth := requestedDepth + steps
  refine ⟨depth, by omega, ?_⟩
  have lower :=
    canonicalPaidReplayFiniteArchiveActualImageCard_intervalLowerBound oldVisit
      sourceIndex lowerBound archive requestedDepth steps
  change
    capacityBound <
      canonicalPaidReplayFiniteArchiveActualImageCardAt oldVisit sourceIndex
        lowerBound archive (requestedDepth + steps)
  exact lt_of_lt_of_le (by omega) lower

theorem canonicalPaidReplayFiniteArchiveActualImageCard_positivePeriod
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive)
    (depth period : Nat) (periodPositive : 0 < period) :
    canonicalPaidReplayFiniteArchiveActualImageCardAt oldVisit sourceIndex
        lowerBound archive depth <
      canonicalPaidReplayFiniteArchiveActualImageCardAt oldVisit sourceIndex
        lowerBound archive (depth + period) := by
  apply
    canonicalPaidReplayFiniteArchiveActualImageCard_strictMono oldVisit
      sourceIndex lowerBound archive
  omega

/-- No finite revision horizon can make the actual image-card tail constant. -/
theorem canonicalPaidReplayFiniteArchiveActualImageCard_notEventuallyConstant
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    ¬ ∃ stabilizationDepth stabilizedCard : Nat,
      ∀ depth, stabilizationDepth ≤ depth →
        canonicalPaidReplayFiniteArchiveActualImageCardAt oldVisit sourceIndex
          lowerBound archive depth = stabilizedCard := by
  rintro ⟨stabilizationDepth, stabilizedCard, stable⟩
  have current := stable stabilizationDepth (by rfl)
  have next := stable (stabilizationDepth + 1) (by omega)
  have strict :=
    canonicalPaidReplayFiniteArchiveActualImageCard_succ_lt oldVisit
      sourceIndex lowerBound archive stabilizationDepth
  omega

end
end M14SourceGeneratedCanonicalSocietyPaidReplayWitnessImageExplosion
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayWitnessImageExplosion.canonicalPaidReplayFiniteArchiveActualImageCard_succ_lt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayWitnessImageExplosion.canonicalPaidReplayFiniteArchiveActualImageCard_strictMono
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayWitnessImageExplosion.canonicalPaidReplayFiniteArchiveActualImageCard_intervalLowerBound
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayWitnessImageExplosion.canonicalPaidReplayFiniteArchiveActualImageCard_linearLowerBound
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayWitnessImageExplosion.canonicalPaidReplayFiniteArchiveActualImageCard_cofinal
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayWitnessImageExplosion.canonicalPaidReplayFiniteArchiveActualImageCard_notEventuallyConstant
