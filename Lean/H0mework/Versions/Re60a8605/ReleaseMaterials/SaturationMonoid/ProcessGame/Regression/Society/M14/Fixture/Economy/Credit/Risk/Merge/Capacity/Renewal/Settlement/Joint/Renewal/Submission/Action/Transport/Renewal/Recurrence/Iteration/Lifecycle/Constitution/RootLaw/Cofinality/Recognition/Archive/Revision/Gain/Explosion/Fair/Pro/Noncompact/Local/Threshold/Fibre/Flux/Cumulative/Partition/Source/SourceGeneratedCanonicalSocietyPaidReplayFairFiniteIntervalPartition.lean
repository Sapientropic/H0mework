import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux

/-!
# Exact finite-interval recognition partition

For every finite horizon, the unresolved tail at its start is the disjoint
union of the paid replays emitted inside that interval and the unresolved tail
at its endpoint.  The finite block is derived from the existing replay source;
it is not a stored schedule or a second occurrence family.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteIntervalPartition

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux

/-- The paid replay at one offset of a caller-requested finite interval. -/
def canonicalPaidReplayFairIntervalEscapingAt
    (oldVisit : OldVisit) (sourceIndex start steps : Nat)
    (offset : Fin steps) :
    AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex :=
  contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
    (start + offset.1)

@[simp]
theorem canonicalPaidReplayFairIntervalEscapingAt_depth
    (oldVisit : OldVisit) (sourceIndex start steps : Nat)
    (offset : Fin steps) :
    (canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex start
      steps offset).1 = start + offset.1 :=
  rfl

theorem canonicalPaidReplayFairIntervalEscapingAt_injective
    (oldVisit : OldVisit) (sourceIndex start steps : Nat) :
    Function.Injective
      (canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex start
        steps) := by
  intro left right occurrenceEquality
  have depthEquality := congrArg Sigma.fst occurrenceEquality
  simp only [canonicalPaidReplayFairIntervalEscapingAt_depth] at depthEquality
  apply Fin.ext
  omega

theorem canonicalPaidReplayFairIntervalEscapingAuthorityK_injective
    (oldVisit : OldVisit) (sourceIndex start steps : Nat) :
    Function.Injective
      (fun offset =>
        (canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex start
          steps offset).2.authorityK) := by
  intro left right authorityEquality
  apply canonicalPaidReplayFairIntervalEscapingAt_injective oldVisit
    sourceIndex start steps
  exact canonicalPaidReplay_authorityK_injective oldVisit sourceIndex
    authorityEquality

theorem canonicalPaidReplayFairIntervalEscaping_startTail
    (oldVisit : OldVisit) (sourceIndex start steps : Nat)
    (offset : Fin steps) :
    CanonicalPaidReplayFairTailAt start
      (canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex start
        steps offset) := by
  unfold CanonicalPaidReplayFairTailAt
  simp

theorem canonicalPaidReplayFairIntervalEscaping_notTerminalTail
    (oldVisit : OldVisit) (sourceIndex start steps : Nat)
    (offset : Fin steps) :
    ¬ CanonicalPaidReplayFairTailAt (start + steps)
      (canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex start
        steps offset) := by
  unfold CanonicalPaidReplayFairTailAt
  simp only [canonicalPaidReplayFairIntervalEscapingAt_depth]
  omega

/-- Exact cumulative conservation: the starting tail consists of the unique
finite emitted block and the terminal tail. -/
theorem canonicalPaidReplayFairTail_interval_split
    (oldVisit : OldVisit) (sourceIndex start steps : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    CanonicalPaidReplayFairTailAt start replay ↔
      (∃ offset : Fin steps,
        replay =
          canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex
            start steps offset) ∨
        CanonicalPaidReplayFairTailAt (start + steps) replay := by
  constructor
  · intro startTail
    by_cases terminalTail :
        CanonicalPaidReplayFairTailAt (start + steps) replay
    · exact Or.inr terminalTail
    · left
      have startLe : start ≤ replay.1 := startTail
      have depthLt : replay.1 < start + steps := by
        unfold CanonicalPaidReplayFairTailAt at terminalTail
        omega
      let offset : Fin steps := ⟨replay.1 - start, by omega⟩
      refine ⟨offset, ?_⟩
      apply canonicalPaidReplay_eq_of_depth_eq
      change replay.1 = start + (replay.1 - start)
      omega
  · rintro (⟨offset, occurrenceEquality⟩ | terminalTail)
    · subst replay
      exact canonicalPaidReplayFairIntervalEscaping_startTail oldVisit
        sourceIndex start steps offset
    · unfold CanonicalPaidReplayFairTailAt at terminalTail ⊢
      omega

/-- The interval branch and the terminal tail are disjoint. -/
theorem canonicalPaidReplayFairTail_interval_branches_disjoint
    (oldVisit : OldVisit) (sourceIndex start steps : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    ¬ ((∃ offset : Fin steps,
          replay =
            canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex
              start steps offset) ∧
        CanonicalPaidReplayFairTailAt (start + steps) replay) := by
  rintro ⟨⟨offset, occurrenceEquality⟩, terminalTail⟩
  subst replay
  exact
    canonicalPaidReplayFairIntervalEscaping_notTerminalTail oldVisit
      sourceIndex start steps offset terminalTail

/-- Exact crossing-set normal form, including uniqueness of the interval
offset. -/
theorem canonicalPaidReplayFairTail_interval_uniqueEscape
    (oldVisit : OldVisit) (sourceIndex start steps : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    (CanonicalPaidReplayFairTailAt start replay ∧
        ¬ CanonicalPaidReplayFairTailAt (start + steps) replay) ↔
      ∃! offset : Fin steps,
        replay =
          canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex
            start steps offset := by
  constructor
  · rintro ⟨startTail, terminalNot⟩
    rcases
        (canonicalPaidReplayFairTail_interval_split oldVisit sourceIndex start
          steps replay).1 startTail with ⟨offset, occurrenceEquality⟩ |
          terminalTail
    · refine ⟨offset, occurrenceEquality, ?_⟩
      intro other otherEquality
      apply canonicalPaidReplayFairIntervalEscapingAt_injective oldVisit
        sourceIndex start steps
      exact otherEquality.symm.trans occurrenceEquality
    · exact (terminalNot terminalTail).elim
  · rintro ⟨offset, occurrenceEquality, _⟩
    subst replay
    exact
      ⟨canonicalPaidReplayFairIntervalEscaping_startTail oldVisit sourceIndex
          start steps offset,
        canonicalPaidReplayFairIntervalEscaping_notTerminalTail oldVisit
          sourceIndex start steps offset⟩

/-- Crossing occurrences are a subtype of the existing paid-replay family,
not a new occurrence ontology. -/
def CanonicalPaidReplayFairIntervalCrossingAt
    (oldVisit : OldVisit) (sourceIndex start steps : Nat) :=
  { replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex //
    CanonicalPaidReplayFairTailAt start replay ∧
      ¬ CanonicalPaidReplayFairTailAt (start + steps) replay }

def canonicalPaidReplayFairIntervalCrossingAt
    (oldVisit : OldVisit) (sourceIndex start steps : Nat)
    (offset : Fin steps) :
    CanonicalPaidReplayFairIntervalCrossingAt oldVisit sourceIndex start
      steps :=
  ⟨canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex start steps
      offset,
    canonicalPaidReplayFairIntervalEscaping_startTail oldVisit sourceIndex
      start steps offset,
    canonicalPaidReplayFairIntervalEscaping_notTerminalTail oldVisit
      sourceIndex start steps offset⟩

/-- Exactly `steps` source occurrences cross the unresolved-fibre frontier. -/
theorem canonicalPaidReplayFairIntervalCrossingAt_bijective
    (oldVisit : OldVisit) (sourceIndex start steps : Nat) :
    Function.Bijective
      (canonicalPaidReplayFairIntervalCrossingAt oldVisit sourceIndex start
        steps) := by
  constructor
  · intro left right crossingEquality
    apply canonicalPaidReplayFairIntervalEscapingAt_injective oldVisit
      sourceIndex start steps
    exact congrArg Subtype.val crossingEquality
  · intro crossing
    rcases
        (canonicalPaidReplayFairTail_interval_uniqueEscape oldVisit
          sourceIndex start steps crossing.1).1 crossing.2 with
      ⟨offset, occurrenceEquality, _⟩
    refine ⟨offset, ?_⟩
    apply Subtype.ext
    exact occurrenceEquality.symm

/-- Zero horizon has no crossing occurrence and leaves the tail unchanged. -/
theorem canonicalPaidReplayFairTail_interval_split_zero
    (oldVisit : OldVisit) (sourceIndex start : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    CanonicalPaidReplayFairTailAt start replay ↔
      CanonicalPaidReplayFairTailAt (start + 0) replay := by
  simp

/-- Zero-horizon regression: the tail is unchanged and no occurrence crosses. -/
theorem canonicalPaidReplayFairCumulativeRecognitionFlux_zero
    (oldVisit : OldVisit) (sourceIndex start : Nat) :
    (∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
      CanonicalPaidReplayFairTailAt start replay ↔
        CanonicalPaidReplayFairTailAt (start + 0) replay) ∧
      (∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
        ¬ ∃! offset : Fin 0,
          replay =
            canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex
              start 0 offset) ∧
      (∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
        ¬ (CanonicalPaidReplayFairTailAt start replay ∧
          ¬ CanonicalPaidReplayFairTailAt (start + 0) replay)) := by
  constructor
  · intro replay
    simp
  · constructor
    · intro replay block
      rcases block with ⟨offset, _, _⟩
      exact Fin.elim0 offset
    · intro replay crossing
      exact crossing.2 crossing.1

/-- The prefix block is literally the prefix of a concatenated interval. -/
theorem canonicalPaidReplayFairIntervalEscaping_concat_prefix
    (oldVisit : OldVisit) (sourceIndex start first second : Nat)
    (offset : Fin first) :
    canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex start
          (first + second) ⟨offset.1, by omega⟩ =
      canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex start
        first offset := by
  rfl

/-- The suffix block is literally the shifted block of a concatenated
interval. -/
theorem canonicalPaidReplayFairIntervalEscaping_concat_suffix
    (oldVisit : OldVisit) (sourceIndex start first second : Nat)
    (offset : Fin second) :
    canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex start
          (first + second) ⟨first + offset.1, by omega⟩ =
      canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex
        (start + first) second offset := by
  simp [canonicalPaidReplayFairIntervalEscapingAt, Nat.add_assoc]

/-- Cumulative crossing is coherent under interval concatenation. -/
theorem canonicalPaidReplayFairTail_interval_crossing_concat
    (oldVisit : OldVisit) (sourceIndex start first second : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    (CanonicalPaidReplayFairTailAt start replay ∧
        ¬ CanonicalPaidReplayFairTailAt (start + (first + second)) replay) ↔
      (CanonicalPaidReplayFairTailAt start replay ∧
          ¬ CanonicalPaidReplayFairTailAt (start + first) replay) ∨
        (CanonicalPaidReplayFairTailAt (start + first) replay ∧
          ¬ CanonicalPaidReplayFairTailAt ((start + first) + second)
            replay) := by
  unfold CanonicalPaidReplayFairTailAt
  omega

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteIntervalPartition
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteIntervalPartition.canonicalPaidReplayFairTail_interval_split
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteIntervalPartition.canonicalPaidReplayFairTail_interval_uniqueEscape
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteIntervalPartition.canonicalPaidReplayFairIntervalCrossingAt_bijective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteIntervalPartition.canonicalPaidReplayFairCumulativeRecognitionFlux_zero
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteIntervalPartition.canonicalPaidReplayFairTail_interval_crossing_concat
