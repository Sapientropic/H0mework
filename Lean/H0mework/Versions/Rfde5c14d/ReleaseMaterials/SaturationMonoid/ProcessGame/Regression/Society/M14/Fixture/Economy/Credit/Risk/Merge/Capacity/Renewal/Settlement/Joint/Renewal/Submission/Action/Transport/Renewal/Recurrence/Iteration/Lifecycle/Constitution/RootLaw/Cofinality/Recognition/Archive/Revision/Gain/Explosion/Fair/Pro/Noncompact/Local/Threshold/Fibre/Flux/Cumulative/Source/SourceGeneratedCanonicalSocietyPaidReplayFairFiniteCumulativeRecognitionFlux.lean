import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Partition.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteIntervalPartition

/-!
# Source-generated cumulative recognition flux

The one-step recognition flux is accumulated across any caller-requested
finite interval.  Every crossing occurrence keeps its own source witness,
Payment and canonical next; the terminal tail remains K-diverse and generates
the next one-step flux.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteCumulativeRecognitionFlux

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteLocalRecognition
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteIntervalPartition

/-- Every interval entry carries its two recognition transitions, exact source
witness, paid seams and committed one-step flux. -/
theorem canonicalPaidReplayFairIntervalEscaping_entryToTerminal
    (oldVisit : OldVisit) (sourceIndex start steps : Nat)
    (offset : Fin steps) :
    let entryStage := start + offset.1
    let terminalStage := start + steps
    let escaping :=
      canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex start
        steps offset
    ¬ CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex
          entryStage escaping ∧
      ¬ CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex
          entryStage escaping ∧
      CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex
          terminalStage escaping ∧
      CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex
          terminalStage escaping ∧
      Nonempty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex entryStage escaping) ∧
      type_of% escaping.2.paidStep_consumes_exactPayment ∧
      type_of% escaping.2.paymentNext_isCanonicalTarget ∧
      type_of%
        (canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
          entryStage) := by
  dsimp only
  let entryStage := start + offset.1
  let terminalStage := start + steps
  let escaping :=
    canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex start steps
      offset
  have entryNotRecognized :=
    canonicalPaidReplayFairBeforeThreshold_notRecognizes oldVisit sourceIndex
      entryStage escaping (by
        change start + offset.1 ≤ start + offset.1
        omega)
  have terminalDepthLt : escaping.1 < terminalStage := by
    change start + offset.1 < start + steps
    omega
  have terminalOccurrenceRecognized :=
    (canonicalPaidReplayFairOccurrenceRecognitionThreshold_exact oldVisit
      sourceIndex terminalStage escaping).2 terminalDepthLt
  have terminalAuthorityRecognized :=
    (canonicalPaidReplayFairAuthorityRecognitionThreshold_exact oldVisit
      sourceIndex terminalStage escaping).2 terminalDepthLt
  have ownWitness :
      Nonempty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex entryStage escaping) := by
    dsimp [entryStage, escaping,
      canonicalPaidReplayFairIntervalEscapingAt]
    exact
      ⟨sourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex (start + offset.1)⟩
  exact
    ⟨entryNotRecognized.1,
      entryNotRecognized.2,
      terminalOccurrenceRecognized,
      terminalAuthorityRecognized,
      ownWitness,
      escaping.2.paidStep_consumes_exactPayment,
      escaping.2.paymentNext_isCanonicalTarget,
      canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
        entryStage⟩

/-- The terminal archive retains a concrete later kernel pair and a
source-injective family of distinct actual-service K values. -/
theorem canonicalPaidReplayFairInterval_terminalTail_open
    (oldVisit : OldVisit) (sourceIndex start steps : Nat) :
    let terminalStage := start + steps
    let remainingPair :=
      canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
        terminalStage
    CanonicalPaidReplayFairTailAt terminalStage remainingPair.left ∧
      CanonicalPaidReplayFairTailAt terminalStage remainingPair.right ∧
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            terminalStage remainingPair.left =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          terminalStage remainingPair.right ∧
      remainingPair.left ≠ remainingPair.right ∧
      remainingPair.left.2.authorityK ≠
        remainingPair.right.2.authorityK ∧
      Function.Injective
        (canonicalPaidReplayFairTailOccurrenceAt oldVisit sourceIndex
          terminalStage) ∧
      Function.Injective
        (fun offset =>
          (canonicalPaidReplayFairTailOccurrenceAt oldVisit sourceIndex
            terminalStage offset).1.2.authorityK) := by
  dsimp only
  let terminalStage := start + steps
  let remainingPair :=
    canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
      terminalStage
  have leftTail :
      CanonicalPaidReplayFairTailAt terminalStage remainingPair.left := by
    unfold CanonicalPaidReplayFairTailAt
    change terminalStage ≤ terminalStage
    omega
  have rightTail :
      CanonicalPaidReplayFairTailAt terminalStage remainingPair.right := by
    unfold CanonicalPaidReplayFairTailAt
    change terminalStage ≤ terminalStage + 1
    omega
  exact
    ⟨leftTail,
      rightTail,
      canonicalPaidReplayFairFiniteArchive_currentPair_visible_eq oldVisit
        sourceIndex terminalStage,
      remainingPair.occurrence_ne,
      remainingPair.authority_ne,
      canonicalPaidReplayFairTailOccurrenceAt_injective oldVisit sourceIndex
        terminalStage,
      canonicalPaidReplayFairTailAuthorityK_injective oldVisit sourceIndex
        terminalStage⟩

/-- The actual readout image gains exactly one value per crossing occurrence,
independently of the exponentially larger archive carrier. -/
theorem canonicalPaidReplayFairFiniteArchive_intervalImageGain_exact
    (oldVisit : OldVisit) (sourceIndex start steps : Nat) :
    @Fintype.card
          (Set.range
            (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit
              sourceIndex (start + steps)))
          (canonicalPaidReplayFairFiniteArchiveImageFintype oldVisit
            sourceIndex (start + steps)) =
        @Fintype.card
            (Set.range
              (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit
                sourceIndex start))
            (canonicalPaidReplayFairFiniteArchiveImageFintype oldVisit
              sourceIndex start) +
          steps := by
  rw [canonicalPaidReplayFairFiniteArchiveActualImage_card_exact,
    canonicalPaidReplayFairFiniteArchiveActualImage_card_exact]
  omega

/-- Maximum occurrence-level cumulative conservation package. -/
theorem canonicalPaidReplayFairFiniteCumulativeRecognitionFlux
    (oldVisit : OldVisit) (sourceIndex start steps : Nat) :
    let terminalStage := start + steps
    (∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
      type_of%
          (canonicalPaidReplayFairTail_interval_split oldVisit sourceIndex
            start steps replay) ∧
        type_of%
          (canonicalPaidReplayFairTail_interval_branches_disjoint oldVisit
            sourceIndex start steps replay) ∧
        type_of%
          (canonicalPaidReplayFairTail_interval_uniqueEscape oldVisit
            sourceIndex start steps replay)) ∧
      Function.Injective
        (canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex start
          steps) ∧
      Function.Injective
        (fun offset : Fin steps =>
          (canonicalPaidReplayFairIntervalEscapingAt oldVisit sourceIndex
            start steps offset).2.authorityK) ∧
      Function.Bijective
        (canonicalPaidReplayFairIntervalCrossingAt oldVisit sourceIndex start
          steps) ∧
      (∀ offset : Fin steps,
        type_of%
          (canonicalPaidReplayFairIntervalEscaping_entryToTerminal oldVisit
            sourceIndex start steps offset)) ∧
      type_of%
        (canonicalPaidReplayFairInterval_terminalTail_open oldVisit
          sourceIndex start steps) ∧
      type_of%
        (canonicalPaidReplayFairFiniteArchive_intervalImageGain_exact oldVisit
          sourceIndex start steps) ∧
      type_of%
        (canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
          terminalStage) := by
  dsimp only
  exact
    ⟨fun replay =>
        ⟨canonicalPaidReplayFairTail_interval_split oldVisit sourceIndex
            start steps replay,
          canonicalPaidReplayFairTail_interval_branches_disjoint oldVisit
            sourceIndex start steps replay,
          canonicalPaidReplayFairTail_interval_uniqueEscape oldVisit
            sourceIndex start steps replay⟩,
      canonicalPaidReplayFairIntervalEscapingAt_injective oldVisit sourceIndex
        start steps,
      canonicalPaidReplayFairIntervalEscapingAuthorityK_injective oldVisit
        sourceIndex start steps,
      canonicalPaidReplayFairIntervalCrossingAt_bijective oldVisit sourceIndex
        start steps,
      canonicalPaidReplayFairIntervalEscaping_entryToTerminal oldVisit
        sourceIndex start steps,
      canonicalPaidReplayFairInterval_terminalTail_open oldVisit sourceIndex
        start steps,
      canonicalPaidReplayFairFiniteArchive_intervalImageGain_exact oldVisit
        sourceIndex start steps,
      canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
        (start + steps)⟩

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteCumulativeRecognitionFlux
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteCumulativeRecognitionFlux.canonicalPaidReplayFairIntervalEscaping_entryToTerminal
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteCumulativeRecognitionFlux.canonicalPaidReplayFairInterval_terminalTail_open
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteCumulativeRecognitionFlux.canonicalPaidReplayFairFiniteArchive_intervalImageGain_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteCumulativeRecognitionFlux.canonicalPaidReplayFairFiniteCumulativeRecognitionFlux
