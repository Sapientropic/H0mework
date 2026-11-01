import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Consumer.ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.Code.Source.SourceGeneratedCanonicalSocietyPaidReplayFairObservedCode

/-!
# Pointwise-terminating uniform fair recognizer

One archive-only transition rule queries successor stages until it sees a hot
code.  Every emitted replay generates a finite certificate of this execution,
recovers its exact occurrence and authority, and retains its paid seams.  The
pointwise stopping stages have no uniform finite bound.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFairPointwiseTerminatingRecognition

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteLocalRecognition
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux
open M14SourceGeneratedCanonicalSocietyPaidReplayFairObservedCode

/-- A finite proof trace for the uniform none-to-successor/some-to-stop rule.
It is indexed by one already emitted replay and is not a future schedule. -/
structure SourceGeneratedCanonicalPaidReplayFairTerminatingRecognitionAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    Type 27 where
  private mk ::
  stopStage : Nat
  stopStageExact : stopStage = replay.1 + 1
  priorStagesContinue :
    ∀ stage, stage < stopStage →
      canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stage replay =
        none
  priorInstructionsContinue :
    ∀ stage, stage < stopStage →
      canonicalPaidReplayFairObservedRecognitionInstructionAt oldVisit
          sourceIndex stage replay =
        .continueAt (stage + 1)
  stopHot : Fin stopStage
  stopCodeExact :
    canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stopStage
        replay = some stopHot
  stopHotUnique :
    ∀ hot : Fin stopStage,
      canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stopStage
          replay = some hot →
        hot = stopHot
  stopInstructionExact :
    canonicalPaidReplayFairObservedRecognitionInstructionAt oldVisit
          sourceIndex stopStage replay =
      .stopAt
        (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
          stopHot.1)
  recoveredOccurrence :
    contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        stopHot.1 = replay
  recoveredAuthorityK :
    (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        stopHot.1).2.authorityK = replay.2.authorityK
  ownWitness :
    Nonempty
      (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex replay.1 replay)
  paymentExact : type_of% replay.2.paidStep_consumes_exactPayment
  nextExact : type_of% replay.2.paymentNext_isCanonicalTarget

/-- Zero-choice source producer for the finite trace of one emitted replay. -/
def sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    SourceGeneratedCanonicalPaidReplayFairTerminatingRecognitionAt oldVisit
      sourceIndex replay := by
  let stopStage := replay.1 + 1
  let stopHot : Fin stopStage := ⟨replay.1, by omega⟩
  have replayEquality :
      replay =
        contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
          replay.1 := by
    apply canonicalPaidReplay_eq_of_depth_eq
    rfl
  have priorCode :
      ∀ stage, stage < stopStage →
        canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stage
            replay = none := by
    intro stage stageLt
    apply
      (canonicalPaidReplayFairObservedCode_eq_none_iff oldVisit sourceIndex
        stage replay).2
    unfold CanonicalPaidReplayFairTailAt
    dsimp [stopStage] at stageLt
    omega
  have stopCode :
      canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stopStage
          replay = some stopHot := by
    apply
      (canonicalPaidReplayFairObservedCode_eq_some_iff oldVisit sourceIndex
        stopStage replay stopHot).2
    exact replayEquality
  have ownWitness :
      Nonempty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex replay.1 replay) := by
    rw [replayEquality]
    exact
      ⟨sourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex replay.1⟩
  refine
    { stopStage := stopStage
      stopStageExact := rfl
      priorStagesContinue := priorCode
      priorInstructionsContinue := ?_
      stopHot := stopHot
      stopCodeExact := stopCode
      stopHotUnique := ?_
      stopInstructionExact := ?_
      recoveredOccurrence := replayEquality.symm
      recoveredAuthorityK :=
        congrArg (fun paidReplay => paidReplay.2.authorityK)
          replayEquality.symm
      ownWitness := ownWitness
      paymentExact := replay.2.paidStep_consumes_exactPayment
      nextExact := replay.2.paymentNext_isCanonicalTarget }
  · intro stage stageLt
    exact
      (canonicalPaidReplayFairObservedInstruction_continue_iff oldVisit
        sourceIndex stage replay).2 (by
          unfold CanonicalPaidReplayFairTailAt
          dsimp [stopStage] at stageLt
          omega)
  · intro hot hotCode
    rw [stopCode] at hotCode
    exact (Option.some.inj hotCode).symm
  · unfold canonicalPaidReplayFairObservedRecognitionInstructionAt
    rw [stopCode]
    rfl

/-- Read the source-produced hot result as the recovered occurrence. -/
def canonicalPaidReplayFairTerminatingRecognizedOccurrence
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex :=
  let search :=
    sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
      sourceIndex replay
  contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
    search.stopHot.1

theorem canonicalPaidReplayFairTerminatingRecognizedOccurrence_exact
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    canonicalPaidReplayFairTerminatingRecognizedOccurrence oldVisit sourceIndex
        replay = replay := by
  exact
    (sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
      sourceIndex replay).recoveredOccurrence

theorem canonicalPaidReplayFairTerminatingRecognizer_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (canonicalPaidReplayFairTerminatingRecognizedOccurrence oldVisit
        sourceIndex) := by
  intro left right recoveredEquality
  rw [canonicalPaidReplayFairTerminatingRecognizedOccurrence_exact,
    canonicalPaidReplayFairTerminatingRecognizedOccurrence_exact] at recoveredEquality
  exact recoveredEquality

/-- Maximum finite trace consumer for one replay, including the still-open
stage immediately after its successful stop. -/
theorem canonicalPaidReplayFairTerminatingRecognition_directConsumer
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    let search :=
      sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
        sourceIndex replay
    search.stopStage = replay.1 + 1 ∧
      (∀ stage, stage < search.stopStage →
        canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stage
            replay = none) ∧
      (∀ stage, stage < search.stopStage →
        canonicalPaidReplayFairObservedRecognitionInstructionAt oldVisit
              sourceIndex stage replay =
          .continueAt (stage + 1)) ∧
      canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex
          search.stopStage replay = some search.stopHot ∧
      (∀ hot : Fin search.stopStage,
        canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex
            search.stopStage replay = some hot →
          hot = search.stopHot) ∧
      canonicalPaidReplayFairObservedRecognitionInstructionAt oldVisit
            sourceIndex search.stopStage replay =
        .stopAt
          (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
            search.stopHot.1) ∧
      canonicalPaidReplayFairTerminatingRecognizedOccurrence oldVisit
          sourceIndex replay = replay ∧
      (canonicalPaidReplayFairTerminatingRecognizedOccurrence oldVisit
          sourceIndex replay).2.authorityK = replay.2.authorityK ∧
      Nonempty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex replay.1 replay) ∧
      type_of% replay.2.paidStep_consumes_exactPayment ∧
      type_of% replay.2.paymentNext_isCanonicalTarget ∧
      type_of%
        (canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
          sourceIndex search.stopStage) ∧
      type_of%
        (canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
          search.stopStage) := by
  dsimp only
  let search :=
    sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
      sourceIndex replay
  exact
    ⟨search.stopStageExact,
      search.priorStagesContinue,
      search.priorInstructionsContinue,
      search.stopCodeExact,
      search.stopHotUnique,
      search.stopInstructionExact,
      search.recoveredOccurrence,
      search.recoveredAuthorityK,
      search.ownWitness,
      search.paymentExact,
      search.nextExact,
      canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
        sourceIndex search.stopStage,
      canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
        search.stopStage⟩

/-- Every proposed uniform stopping bound generates a paid replay whose exact
stop lies strictly beyond it, together with a still-open successor stage. -/
theorem canonicalPaidReplayFairRecognitionBound_generatesCounterexample
    (oldVisit : OldVisit) (sourceIndex fuel : Nat) :
    let replay :=
      contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex fuel
    let search :=
      sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
        sourceIndex replay
    fuel < search.stopStage ∧
      ¬ search.stopStage ≤ fuel ∧
      type_of% replay.2.paidStep_consumes_exactPayment ∧
      type_of% replay.2.paymentNext_isCanonicalTarget ∧
      type_of%
        (canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
          sourceIndex search.stopStage) ∧
      type_of%
        (canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
          search.stopStage) := by
  dsimp only
  let replay :=
    contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex fuel
  let search :=
    sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
      sourceIndex replay
  have stopExact : search.stopStage = fuel + 1 := by
    rw [search.stopStageExact]
    rfl
  exact
    ⟨by
        rw [stopExact]
        omega,
      by
        rw [stopExact]
        omega,
      replay.2.paidStep_consumes_exactPayment,
      replay.2.paymentNext_isCanonicalTarget,
      canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
        sourceIndex search.stopStage,
      canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
        search.stopStage⟩

/-- Every proposed observation bound emits a paid replay whose decoded codes
remain `none` throughout that bound and whose occurrence/K remain unresolved at
the boundary. -/
theorem canonicalPaidReplayFairEveryBound_generatesStillOpenReplay
    (oldVisit : OldVisit) (sourceIndex bound : Nat) :
    let replay :=
      canonicalPaidReplayFairEscapingReplayAt oldVisit sourceIndex bound
    (∀ stage, stage ≤ bound →
      canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stage replay =
        none) ∧
      ¬ CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex
          bound replay ∧
      ¬ CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex
          bound replay ∧
      Nonempty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex bound replay) ∧
      type_of% replay.2.paidStep_consumes_exactPayment ∧
      type_of% replay.2.paymentNext_isCanonicalTarget ∧
      type_of%
        (canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
          sourceIndex bound) ∧
      type_of%
        (canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
          bound) := by
  dsimp only
  let replay :=
    canonicalPaidReplayFairEscapingReplayAt oldVisit sourceIndex bound
  have notRecognized :=
    canonicalPaidReplayFairBeforeThreshold_notRecognizes oldVisit sourceIndex
      bound replay (by
        change bound ≤ bound
        omega)
  exact
    ⟨fun stage stageLe =>
        (canonicalPaidReplayFairObservedCode_eq_none_iff oldVisit sourceIndex
          stage replay).2 (by
            unfold CanonicalPaidReplayFairTailAt
            change stage ≤ bound
            exact stageLe),
      notRecognized.1,
      notRecognized.2,
      ⟨sourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex bound⟩,
      replay.2.paidStep_consumes_exactPayment,
      replay.2.paymentNext_isCanonicalTarget,
      canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
        sourceIndex bound,
      canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
        bound⟩

/-- There is no finite stage bound by which every replay has produced some hot
observer code. -/
theorem canonicalPaidReplayFairPointwiseRecognizer_noUniformFiniteHotBound
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ¬ ∃ bound : Nat,
      ∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
        ∃ stage, stage ≤ bound ∧
          ∃ hot : Fin stage,
            canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stage
              replay = some hot := by
  rintro ⟨bound, uniformlyHot⟩
  let replay :=
    canonicalPaidReplayFairEscapingReplayAt oldVisit sourceIndex bound
  have stillOpen :=
    canonicalPaidReplayFairEveryBound_generatesStillOpenReplay oldVisit
      sourceIndex bound
  rcases uniformlyHot replay with ⟨stage, stageLe, hot, hotCode⟩
  have noneCode := stillOpen.1 stage stageLe
  rw [noneCode] at hotCode
  cases hotCode

/-- Pointwise termination has no uniform finite stopping bound. -/
theorem canonicalPaidReplayFairRecognition_hasNoUniformFiniteBound
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ¬ ∃ fuel : Nat,
      ∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
        (sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
          sourceIndex replay).stopStage ≤ fuel := by
  rintro ⟨fuel, uniformBound⟩
  let replay :=
    contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex fuel
  have counterexample :=
    canonicalPaidReplayFairRecognitionBound_generatesCounterexample oldVisit
      sourceIndex fuel
  exact counterexample.2.1 (uniformBound replay)

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFairPointwiseTerminatingRecognition
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairPointwiseTerminatingRecognition.sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairPointwiseTerminatingRecognition.canonicalPaidReplayFairTerminatingRecognition_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairPointwiseTerminatingRecognition.canonicalPaidReplayFairRecognitionBound_generatesCounterexample
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairPointwiseTerminatingRecognition.canonicalPaidReplayFairEveryBound_generatesStillOpenReplay
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairPointwiseTerminatingRecognition.canonicalPaidReplayFairPointwiseRecognizer_noUniformFiniteHotBound
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairPointwiseTerminatingRecognition.canonicalPaidReplayFairRecognition_hasNoUniformFiniteBound
