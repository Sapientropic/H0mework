import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Source.SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveKernel
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.SourceWitnessRefinement

/-!
# Fair coherent finite witness tower

Stage `n` publishes only the exact source-backed replay-depth witnesses indexed
by `Fin n`.  Successor stages restrict exactly to predecessors, every stage
still has an explicit authority kernel, and every fixed pair of distinct paid
replays is separated by one explicitly generated finite later stage.

No omega archive, stage schedule, witness registry or completed future is
constructed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityFutureBirthPulse
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveKernel

/-- Finite stage carrier only.  There is deliberately no completed
`Nat → Bool` archive. -/
abbrev CanonicalPaidReplayFairFiniteArchiveAt (stage : Nat) :=
  Fin stage → Bool

/-- One-hot finite readout of already generated replay depths below `stage`. -/
def canonicalPaidReplayFairFiniteArchiveReadoutAt
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex →
      CanonicalPaidReplayFairFiniteArchiveAt stage :=
  fun replay bit => decide (replay.1 = bit.1)

/-- Direct restriction from any later finite stage to any earlier one. -/
def canonicalPaidReplayFairFiniteArchiveRestriction
    {earlier later : Nat} (earlierLeLater : earlier ≤ later) :
    CanonicalPaidReplayFairFiniteArchiveAt later →
      CanonicalPaidReplayFairFiniteArchiveAt earlier :=
  fun archive bit =>
    archive ⟨bit.1, bit.2.trans_le earlierLeLater⟩

/-- Full coherence square, not only the adjacent case. -/
theorem canonicalPaidReplayFairFiniteArchiveRestriction_exact
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {earlier later : Nat} (earlierLeLater : earlier ≤ later)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    canonicalPaidReplayFairFiniteArchiveRestriction earlierLeLater
        (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          later replay) =
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
        earlier replay := by
  rfl

theorem canonicalPaidReplayFairFiniteArchiveRestriction_trans
    {first second third : Nat}
    (firstLeSecond : first ≤ second) (secondLeThird : second ≤ third)
    (archive : CanonicalPaidReplayFairFiniteArchiveAt third) :
    canonicalPaidReplayFairFiniteArchiveRestriction firstLeSecond
        (canonicalPaidReplayFairFiniteArchiveRestriction secondLeThird
          archive) =
      canonicalPaidReplayFairFiniteArchiveRestriction
        (firstLeSecond.trans secondLeThird) archive := by
  rfl

/-- At stage `n`, depths `n` and `n+1` still have the same finite archive. -/
theorem canonicalPaidReplayFairFiniteArchive_currentPair_visible_eq
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
        (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
          stage) =
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
        (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
          (stage + 1)) := by
  funext bit
  have stageNe : stage ≠ bit.1 := by omega
  have successorNe : stage + 1 ≠ bit.1 := by omega
  simp [canonicalPaidReplayFairFiniteArchiveReadoutAt,
    contributionCapacityPostSettlementPaidReplayAt, stageNe, successorNe]

/-- The new successor bit witnesses depth `stage` and separates the same pair. -/
theorem canonicalPaidReplayFairFiniteArchive_successorSeparatesCurrentPair
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          (stage + 1)
          (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
            stage) ≠
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
        (stage + 1)
        (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
          (stage + 1)) := by
  intro archiveEquality
  have bitEquality := congrFun archiveEquality ⟨stage, by omega⟩
  simp [canonicalPaidReplayFairFiniteArchiveReadoutAt,
    contributionCapacityPostSettlementPaidReplayAt] at bitEquality

/-- Exact authority kernel at every fair finite stage. -/
def canonicalPaidReplayFairFiniteArchiveKernelPairAt
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    AuthorityKernelPair
      (canonicalPaidReplayFiniteArchiveObserverAt oldVisit sourceIndex
        (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage)) where
  left :=
    contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex stage
  right :=
    contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
      (stage + 1)
  occurrence_ne := by
    intro replayEquality
    have depthEquality := congrArg Sigma.fst replayEquality
    simp [contributionCapacityPostSettlementPaidReplayAt] at depthEquality
  visible_eq := by
    apply Prod.ext
    · simp [canonicalPaidReplayFiniteArchiveObserverAt]
    · exact
        canonicalPaidReplayFairFiniteArchive_currentPair_visible_eq oldVisit
          sourceIndex stage
  authority_ne := by
    intro authorityEquality
    have currentEquality :=
      periodicActualServiceExitOccurrenceAt_injective authorityEquality
    change
      contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
          sourceIndex stage =
        contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
          sourceIndex (stage + 1) at currentEquality
    unfold contributionCapacityPostSettlementFutureBirthCurrentAt at currentEquality
    rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
      contributionCapacityPostSettlementReachableCurrentAt_exact] at currentEquality
    omega

/-- Source witness for the unique new bit at fair successor stage. -/
structure SourceGeneratedCanonicalPaidReplayFairStageWitnessAt
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    Type where
  private mk ::
  exactReplayLabel :
    replay =
      contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex stage
  exactActualPathLabel :
    replay.2.actualPath =
      (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        stage).2.actualPath
  anchorPaidStepConsumesExactPayment :
    type_of%
      ((contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        stage).2.paidStep_consumes_exactPayment)
  anchorPaymentNextIsCanonicalTarget :
    type_of%
      ((contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        stage).2.paymentNext_isCanonicalTarget)

def sourceGeneratedCanonicalPaidReplayFairStageWitnessAt
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit sourceIndex
      stage
      (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        stage) where
  exactReplayLabel := rfl
  exactActualPathLabel := rfl
  anchorPaidStepConsumesExactPayment :=
    (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
      stage).2.paidStep_consumes_exactPayment
  anchorPaymentNextIsCanonicalTarget :=
    (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
      stage).2.paymentNext_isCanonicalTarget

/-- K-free public bit added at the fair successor stage. -/
def canonicalPaidReplayFairStagePublicationTag
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    Bool :=
  decide (replay.1 = stage)

@[simp] theorem canonicalPaidReplayFairFiniteArchive_successorNewBit_exact
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          (stage + 1) replay ⟨stage, by omega⟩ =
      canonicalPaidReplayFairStagePublicationTag oldVisit sourceIndex stage
        replay := by
  rfl

theorem canonicalPaidReplayFairStagePublicationTag_true_iff
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    canonicalPaidReplayFairStagePublicationTag oldVisit sourceIndex stage
          replay = true ↔
      Nonempty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex stage replay) := by
  constructor
  · intro published
    have depthEquality : replay.1 = stage := by
      simpa [canonicalPaidReplayFairStagePublicationTag] using published
    have replayEquality :
        replay =
          contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
            stage := by
      cases replay with
      | mk replayDepth replayProof =>
          simp only at depthEquality
          subst replayDepth
          cases replayProof
          rfl
    subst replay
    exact
      ⟨sourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex stage⟩
  · rintro ⟨witness⟩
    rw [witness.exactReplayLabel]
    simp [canonicalPaidReplayFairStagePublicationTag,
      contributionCapacityPostSettlementPaidReplayAt]

def canonicalPaidReplayFairStagePublicationAt
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    SourceWitnessPublicationAt
      (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex stage) where
  publicationTag :=
    canonicalPaidReplayFairStagePublicationTag oldVisit sourceIndex stage
  publicationTag_eq_true_iff :=
    canonicalPaidReplayFairStagePublicationTag_true_iff oldVisit sourceIndex
      stage

theorem canonicalPaidReplayFairStageKernelRefinementAt
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    SourceWitnessKernelRefinementAt
      (canonicalPaidReplayFairStagePublicationAt oldVisit sourceIndex stage)
      (canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
        stage) := by
  apply sourceWitnessKernelRefinement
  · exact
      ⟨sourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex stage⟩
  · exact
      ⟨fun witness =>
        (canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
          stage).occurrence_ne witness.exactReplayLabel.symm⟩

/-- The new bit cannot be decoded from the preceding fair stage. -/
theorem canonicalPaidReplayFairStageTag_notFactorThroughPredecessor
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    ¬ ∃ decode : CanonicalPaidReplayFairFiniteArchiveAt stage → Bool,
      ∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
        decode
            (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              stage replay) =
          canonicalPaidReplayFairStagePublicationTag oldVisit sourceIndex stage
            replay := by
  rintro ⟨decode, factorizes⟩
  let pair :=
    canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex stage
  have oldVisibleEquality :=
    canonicalPaidReplayFairFiniteArchive_currentPair_visible_eq oldVisit
      sourceIndex stage
  have tagEquality :
      canonicalPaidReplayFairStagePublicationTag oldVisit sourceIndex stage
          pair.left =
        canonicalPaidReplayFairStagePublicationTag oldVisit sourceIndex stage
          pair.right := by
    calc
      _ = decode
          (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            stage pair.left) := (factorizes pair.left).symm
      _ = decode
          (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            stage pair.right) := congrArg decode oldVisibleEquality
      _ = _ := factorizes pair.right
  exact
    (canonicalPaidReplayFairStageKernelRefinementAt oldVisit sourceIndex stage
      ).publicationTag_ne tagEquality

/-- Fair point separation without an omega object: every fixed distinct pair
is separated by one explicitly generated finite stage. -/
theorem canonicalPaidReplayFairFiniteArchive_eventuallySeparates
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (left right :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
    (occurrenceNe : left ≠ right) :
    ∃ stage : Nat,
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
          left ≠
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage right := by
  have depthNe : left.1 ≠ right.1 := by
    intro depthEquality
    apply occurrenceNe
    cases left with
    | mk leftDepth leftReplay =>
        cases right with
        | mk rightDepth rightReplay =>
            simp only at depthEquality
            subst rightDepth
            cases leftReplay
            cases rightReplay
            rfl
  let stage := max left.1 right.1 + 1
  refine ⟨stage, ?_⟩
  intro archiveEquality
  have bitEquality := congrFun archiveEquality ⟨left.1, by omega⟩
  simp [canonicalPaidReplayFairFiniteArchiveReadoutAt] at bitEquality
  exact depthNe bitEquality.symm

/-- The separating finite stage can be required to lie beyond any requested
stage, so a constitutional point can consume the fair tower cofinally. -/
theorem canonicalPaidReplayFairFiniteArchive_eventuallySeparatesAfter
    (oldVisit : OldVisit) (sourceIndex requestedStage : Nat)
    (left right :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
    (occurrenceNe : left ≠ right) :
    ∃ stage : Nat,
      requestedStage < stage ∧
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              stage left ≠
          canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            stage right := by
  have depthNe : left.1 ≠ right.1 := by
    intro depthEquality
    apply occurrenceNe
    cases left with
    | mk leftDepth leftReplay =>
        cases right with
        | mk rightDepth rightReplay =>
            simp only at depthEquality
            subst rightDepth
            cases leftReplay
            cases rightReplay
            rfl
  let stage := max requestedStage (max left.1 right.1) + 1
  refine ⟨stage, by omega, ?_⟩
  intro archiveEquality
  have bitEquality := congrFun archiveEquality ⟨left.1, by omega⟩
  simp [canonicalPaidReplayFairFiniteArchiveReadoutAt] at bitEquality
  exact depthNe bitEquality.symm

/-! ## Exact actual finite-stage image -/

/-- Finite code of all attained fair-stage values: `some i` is the one-hot
value at `i`; `none` is the zero value shared by the later tail. -/
def canonicalPaidReplayFairFiniteArchiveCode
    (stage : Nat) : Option (Fin stage) →
      CanonicalPaidReplayFairFiniteArchiveAt stage
  | none => fun _bit => false
  | some hot => fun bit => decide (hot.1 = bit.1)

theorem canonicalPaidReplayFairFiniteArchiveCode_injective
    (stage : Nat) :
    Function.Injective (canonicalPaidReplayFairFiniteArchiveCode stage) := by
  intro left right codeEquality
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right =>
          have bitEquality := congrFun codeEquality right
          simp [canonicalPaidReplayFairFiniteArchiveCode] at bitEquality
  | some left =>
      cases right with
      | none =>
          have bitEquality := congrFun codeEquality left
          simp [canonicalPaidReplayFairFiniteArchiveCode] at bitEquality
      | some right =>
          have rightEquality : right = left := by
            by_contra rightNe
            have valueNe : right.1 ≠ left.1 := by
              intro valueEquality
              exact rightNe (Fin.ext valueEquality)
            have bitEquality := congrFun codeEquality left
            simp [canonicalPaidReplayFairFiniteArchiveCode, valueNe] at bitEquality
          exact congrArg some rightEquality.symm

/-- Every finite code is realized by an existing paid replay. -/
def canonicalPaidReplayFairFiniteArchiveCodeInRange
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    Option (Fin stage) →
      Set.range
        (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage)
  | none =>
      ⟨canonicalPaidReplayFairFiniteArchiveCode stage none,
        ⟨contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
            stage,
          by
            funext bit
            change decide (stage = bit.1) = false
            simp only [decide_eq_false_iff_not]
            omega⟩⟩
  | some hot =>
      ⟨canonicalPaidReplayFairFiniteArchiveCode stage (some hot),
        ⟨contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
            hot.1,
          rfl⟩⟩

theorem canonicalPaidReplayFairFiniteArchiveCodeInRange_injective
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    Function.Injective
      (canonicalPaidReplayFairFiniteArchiveCodeInRange oldVisit sourceIndex
        stage) := by
  intro left right rangeEquality
  apply canonicalPaidReplayFairFiniteArchiveCode_injective stage
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right =>
          exact congrArg Subtype.val rangeEquality
  | some left =>
      cases right with
      | none =>
          exact congrArg Subtype.val rangeEquality
      | some right =>
          exact congrArg Subtype.val rangeEquality

theorem canonicalPaidReplayFairFiniteArchiveCodeInRange_surjective
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    Function.Surjective
      (canonicalPaidReplayFairFiniteArchiveCodeInRange oldVisit sourceIndex
        stage) := by
  rintro ⟨_archive, replay, rfl⟩
  by_cases inside : replay.1 < stage
  · refine ⟨some ⟨replay.1, inside⟩, ?_⟩
    apply Subtype.ext
    funext bit
    rfl
  · refine ⟨none, ?_⟩
    apply Subtype.ext
    funext bit
    dsimp [canonicalPaidReplayFairFiniteArchiveCodeInRange,
      canonicalPaidReplayFairFiniteArchiveCode]
    change false = decide (replay.1 = bit.1)
    symm
    simp only [decide_eq_false_iff_not]
    omega

noncomputable def canonicalPaidReplayFairFiniteArchiveImageEquiv
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    Option (Fin stage) ≃
      Set.range
        (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage) :=
  Equiv.ofBijective
    (canonicalPaidReplayFairFiniteArchiveCodeInRange oldVisit sourceIndex
      stage)
    ⟨canonicalPaidReplayFairFiniteArchiveCodeInRange_injective oldVisit
        sourceIndex stage,
      canonicalPaidReplayFairFiniteArchiveCodeInRange_surjective oldVisit
        sourceIndex stage⟩

@[instance_reducible] noncomputable def canonicalPaidReplayFairFiniteArchiveImageFintype
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    Fintype
      (Set.range
        (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage)) := by
  let _ : Fintype (CanonicalPaidReplayFairFiniteArchiveAt stage) :=
    inferInstance
  exact Fintype.ofFinite _

/-- Exact actual image cardinal: `stage` one-hot values plus one zero-tail
value.  This remains distinct from carrier cardinal `2^stage`. -/
theorem canonicalPaidReplayFairFiniteArchiveActualImage_card_exact
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    @Fintype.card
        (Set.range
          (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            stage))
        (canonicalPaidReplayFairFiniteArchiveImageFintype oldVisit sourceIndex
          stage) =
      stage + 1 := by
  let _ : Fintype
      (Set.range
        (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage)) :=
    canonicalPaidReplayFairFiniteArchiveImageFintype oldVisit sourceIndex stage
  change Fintype.card
      (Set.range
        (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage)) =
    stage + 1
  rw [Fintype.card_congr
    (canonicalPaidReplayFairFiniteArchiveImageEquiv oldVisit sourceIndex
      stage).symm]
  simp

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower.canonicalPaidReplayFairFiniteArchiveRestriction_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower.canonicalPaidReplayFairFiniteArchiveKernelPairAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower.canonicalPaidReplayFairStagePublicationTag_true_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower.canonicalPaidReplayFairStageKernelRefinementAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower.canonicalPaidReplayFairStageTag_notFactorThroughPredecessor
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower.canonicalPaidReplayFairFiniteArchive_eventuallySeparates
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower.canonicalPaidReplayFairFiniteArchive_eventuallySeparatesAfter
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower.canonicalPaidReplayFairFiniteArchiveActualImage_card_exact
