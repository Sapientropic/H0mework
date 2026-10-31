import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Stratification.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification

/-!
# Observer-only fair archive code

The actual-image equivalence decodes one finite fair-stage readout into either
the unresolved zero code or one exact hot source index.  The decoder consumes
only the archive and its actual-range witness; it does not project replay depth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFairObservedCode

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification

/-- Decode the actual finite-stage archive through its already proved image
equivalence. -/
def canonicalPaidReplayFairObservedCodeAt
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    Option (Fin stage) :=
  (canonicalPaidReplayFairFiniteArchiveImageEquiv oldVisit sourceIndex stage).symm
    ⟨canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
        replay,
      ⟨replay, rfl⟩⟩

/-- Re-encoding the observed code returns the exact actual readout. -/
theorem canonicalPaidReplayFairObservedCode_readout_exact
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    canonicalPaidReplayFairFiniteArchiveCodeInRange oldVisit sourceIndex stage
          (canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stage
            replay) =
      ⟨canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
          replay,
        ⟨replay, rfl⟩⟩ := by
  exact
    (canonicalPaidReplayFairFiniteArchiveImageEquiv oldVisit sourceIndex
      stage).apply_symm_apply _

/-- General exact bridge from decoded code equality to archive equality. -/
theorem canonicalPaidReplayFairObservedCode_eq_iff_readout_eq_code
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
    (code : Option (Fin stage)) :
    canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stage replay =
          code ↔
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
            replay =
        canonicalPaidReplayFairFiniteArchiveCode stage code := by
  constructor
  · intro codeEquality
    have rangeEquality :=
      canonicalPaidReplayFairObservedCode_readout_exact oldVisit sourceIndex
        stage replay
    rw [codeEquality] at rangeEquality
    cases code with
    | none =>
        simpa [canonicalPaidReplayFairFiniteArchiveCodeInRange] using
          congrArg Subtype.val rangeEquality.symm
    | some hot =>
        simpa [canonicalPaidReplayFairFiniteArchiveCodeInRange] using
          congrArg Subtype.val rangeEquality.symm
  · intro readoutEquality
    apply
      canonicalPaidReplayFairFiniteArchiveCodeInRange_injective oldVisit
        sourceIndex stage
    rw [canonicalPaidReplayFairObservedCode_readout_exact oldVisit sourceIndex
      stage replay]
    apply Subtype.ext
    cases code with
    | none =>
        simpa [canonicalPaidReplayFairFiniteArchiveCodeInRange] using
          readoutEquality
    | some hot =>
        simpa [canonicalPaidReplayFairFiniteArchiveCodeInRange] using
          readoutEquality

/-- Observer code is `none` exactly on the unresolved tail. -/
theorem canonicalPaidReplayFairObservedCode_eq_none_iff
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stage replay =
          none ↔
      CanonicalPaidReplayFairTailAt stage replay := by
  rw [canonicalPaidReplayFairObservedCode_eq_iff_readout_eq_code]
  exact
    canonicalPaidReplayFairFiniteArchive_zeroFibre_exact oldVisit sourceIndex
      stage replay

/-- A hot observer code is equivalent to the exact corresponding paid replay. -/
theorem canonicalPaidReplayFairObservedCode_eq_some_iff
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
    (hot : Fin stage) :
    canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stage replay =
          some hot ↔
      replay =
        contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
          hot.1 := by
  rw [canonicalPaidReplayFairObservedCode_eq_iff_readout_eq_code]
  exact
    canonicalPaidReplayFairFiniteArchive_hotFibre_exact oldVisit sourceIndex
      stage hot replay

/-- Uniform recognition instruction produced from an observed code alone. -/
inductive CanonicalPaidReplayFairRecognitionInstructionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Type 27
  | continueAt (nextStage : Nat) :
      CanonicalPaidReplayFairRecognitionInstructionAt oldVisit sourceIndex
  | stopAt
      (recovered :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
      CanonicalPaidReplayFairRecognitionInstructionAt oldVisit sourceIndex

/-- The sole transition rule: zero continues at the successor; a hot code
stops with the source replay indexed by that code. -/
def canonicalPaidReplayFairRecognitionInstruction
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    Option (Fin stage) →
      CanonicalPaidReplayFairRecognitionInstructionAt oldVisit sourceIndex
  | none => .continueAt (stage + 1)
  | some hot =>
      .stopAt
        (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
          hot.1)

/-- Apply the uniform instruction only after observer-side decoding. -/
def canonicalPaidReplayFairObservedRecognitionInstructionAt
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    CanonicalPaidReplayFairRecognitionInstructionAt oldVisit sourceIndex :=
  canonicalPaidReplayFairRecognitionInstruction oldVisit sourceIndex stage
    (canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stage replay)

theorem canonicalPaidReplayFairObservedInstruction_continue_iff
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    canonicalPaidReplayFairObservedRecognitionInstructionAt oldVisit
          sourceIndex stage replay =
        .continueAt (stage + 1) ↔
      CanonicalPaidReplayFairTailAt stage replay := by
  unfold canonicalPaidReplayFairObservedRecognitionInstructionAt
  cases codeEquality :
      canonicalPaidReplayFairObservedCodeAt oldVisit sourceIndex stage replay
    with
  | none =>
      simp [canonicalPaidReplayFairRecognitionInstruction,
        (canonicalPaidReplayFairObservedCode_eq_none_iff oldVisit sourceIndex
          stage replay).1 codeEquality]
  | some hot =>
      have notTail : ¬ CanonicalPaidReplayFairTailAt stage replay := by
        intro tail
        have noneEquality :=
          (canonicalPaidReplayFairObservedCode_eq_none_iff oldVisit
            sourceIndex stage replay).2 tail
        rw [codeEquality] at noneEquality
        contradiction
      simp [canonicalPaidReplayFairRecognitionInstruction, notTail]

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFairObservedCode
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairObservedCode.canonicalPaidReplayFairObservedCode_readout_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairObservedCode.canonicalPaidReplayFairObservedCode_eq_none_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairObservedCode.canonicalPaidReplayFairObservedCode_eq_some_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairObservedCode.canonicalPaidReplayFairObservedInstruction_continue_iff
