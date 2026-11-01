import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold

/-!
# Exact fair finite-stage fibre stratification

At stage `n`, the actual readout fibres are exactly `n` singleton hot fibres
and one unresolved tail fibre.  The tail is not an abstract remainder: it has
a source-generated injection from every later paid replay and carries
injectively distinct actual-service authorities.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold

/-- The unresolved fibre at one fair stage. -/
def CanonicalPaidReplayFairTailAt
    {oldVisit : OldVisit} {sourceIndex : Nat} (stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    Prop :=
  stage ≤ replay.1

/-- Every hot code has exactly one paid-replay occurrence in its fibre. -/
theorem canonicalPaidReplayFairFiniteArchive_hotFibre_exact
    (oldVisit : OldVisit) (sourceIndex stage : Nat) (hot : Fin stage)
    (candidate :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
          candidate =
        canonicalPaidReplayFairFiniteArchiveCode stage (some hot) ↔
      candidate =
        contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
          hot.1 := by
  constructor
  · intro archiveEquality
    have bitEquality := congrFun archiveEquality hot
    have depthEquality : candidate.1 = hot.1 := by
      simpa [canonicalPaidReplayFairFiniteArchiveReadoutAt,
        canonicalPaidReplayFairFiniteArchiveCode] using bitEquality
    apply canonicalPaidReplay_eq_of_depth_eq
    simpa [contributionCapacityPostSettlementPaidReplayAt] using depthEquality
  · intro occurrenceEquality
    subst candidate
    rfl

/-- The zero code fibre is exactly the unresolved future tail. -/
theorem canonicalPaidReplayFairFiniteArchive_zeroFibre_exact
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (candidate :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
          candidate =
        canonicalPaidReplayFairFiniteArchiveCode stage none ↔
      CanonicalPaidReplayFairTailAt stage candidate := by
  constructor
  · intro archiveEquality
    by_contra tailNot
    have depthLt : candidate.1 < stage := by
      unfold CanonicalPaidReplayFairTailAt at tailNot
      omega
    have bitEquality := congrFun archiveEquality ⟨candidate.1, depthLt⟩
    simp [canonicalPaidReplayFairFiniteArchiveReadoutAt,
      canonicalPaidReplayFairFiniteArchiveCode] at bitEquality
  · intro tail
    funext bit
    have depthNe : candidate.1 ≠ bit.1 := by
      unfold CanonicalPaidReplayFairTailAt at tail
      omega
    simp [canonicalPaidReplayFairFiniteArchiveReadoutAt,
      canonicalPaidReplayFairFiniteArchiveCode, depthNe]

/-- Complete pairwise readout normal form: identical recognized occurrence or
two members of the single unresolved tail. -/
theorem canonicalPaidReplayFairFiniteArchive_readout_eq_iff
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (left right :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
          left =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage right ↔
      (left = right ∧ left.1 < stage) ∨
        (CanonicalPaidReplayFairTailAt stage left ∧
          CanonicalPaidReplayFairTailAt stage right) := by
  constructor
  · intro archiveEquality
    by_cases leftInside : left.1 < stage
    · have recognizes :=
        (canonicalPaidReplayFairOccurrenceRecognitionThreshold_exact oldVisit
          sourceIndex stage left).2 leftInside
      have rightEquality := recognizes right archiveEquality.symm
      exact Or.inl ⟨rightEquality.symm, leftInside⟩
    · have leftTail : CanonicalPaidReplayFairTailAt stage left := by
        unfold CanonicalPaidReplayFairTailAt
        omega
      have leftZero :=
        (canonicalPaidReplayFairFiniteArchive_zeroFibre_exact oldVisit
          sourceIndex stage left).2 leftTail
      have rightZero :
          canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
                stage right =
            canonicalPaidReplayFairFiniteArchiveCode stage none :=
        archiveEquality.symm.trans leftZero
      have rightTail :=
        (canonicalPaidReplayFairFiniteArchive_zeroFibre_exact oldVisit
          sourceIndex stage right).1 rightZero
      exact Or.inr ⟨leftTail, rightTail⟩
  · rintro (⟨rfl, _⟩ | ⟨leftTail, rightTail⟩)
    · rfl
    · exact
        ((canonicalPaidReplayFairFiniteArchive_zeroFibre_exact oldVisit
            sourceIndex stage left).2 leftTail).trans
          ((canonicalPaidReplayFairFiniteArchive_zeroFibre_exact oldVisit
            sourceIndex stage right).2 rightTail).symm

/-- The same normal form expressed through actual-service K. -/
theorem canonicalPaidReplayFairFiniteArchive_readout_eq_iff_authorityK
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (left right :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
          left =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage right ↔
      (left.2.authorityK = right.2.authorityK ∧ left.1 < stage) ∨
        (CanonicalPaidReplayFairTailAt stage left ∧
          CanonicalPaidReplayFairTailAt stage right) := by
  constructor
  · intro archiveEquality
    rcases
        (canonicalPaidReplayFairFiniteArchive_readout_eq_iff oldVisit
          sourceIndex stage left right).1 archiveEquality with
      ⟨occurrenceEquality, leftInside⟩ | tails
    · exact Or.inl
        ⟨congrArg (fun replay => replay.2.authorityK) occurrenceEquality,
          leftInside⟩
    · exact Or.inr tails
  · rintro (⟨authorityEquality, leftInside⟩ | tails)
    · have occurrenceEquality :=
        canonicalPaidReplay_authorityK_injective oldVisit sourceIndex
          authorityEquality
      subst right
      rfl
    · exact
        (canonicalPaidReplayFairFiniteArchive_readout_eq_iff oldVisit
          sourceIndex stage left right).2 (Or.inr tails)

/-- Source enumeration of the unresolved tail.  This is a theorem-level map,
not a registry. -/
def canonicalPaidReplayFairTailOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex stage offset : Nat) :
    { replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex //
      CanonicalPaidReplayFairTailAt stage replay } :=
  ⟨contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
      (stage + offset),
    by
      unfold CanonicalPaidReplayFairTailAt
      simp [contributionCapacityPostSettlementPaidReplayAt]⟩

theorem canonicalPaidReplayFairTailOccurrenceAt_injective
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    Function.Injective
      (canonicalPaidReplayFairTailOccurrenceAt oldVisit sourceIndex stage) := by
  intro left right tailEquality
  have replayEquality := congrArg Subtype.val tailEquality
  have depthEquality := congrArg Sigma.fst replayEquality
  change stage + left = stage + right at depthEquality
  omega

theorem canonicalPaidReplayFairTailAuthorityK_injective
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    Function.Injective
      (fun offset =>
        (canonicalPaidReplayFairTailOccurrenceAt oldVisit sourceIndex stage
          offset).1.2.authorityK) := by
  intro left right authorityEquality
  apply
    canonicalPaidReplayFairTailOccurrenceAt_injective oldVisit sourceIndex
      stage
  apply Subtype.ext
  exact
    canonicalPaidReplay_authorityK_injective oldVisit sourceIndex
      authorityEquality

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification.canonicalPaidReplayFairFiniteArchive_hotFibre_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification.canonicalPaidReplayFairFiniteArchive_zeroFibre_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification.canonicalPaidReplayFairFiniteArchive_readout_eq_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification.canonicalPaidReplayFairFiniteArchive_readout_eq_iff_authorityK
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification.canonicalPaidReplayFairTailOccurrenceAt_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification.canonicalPaidReplayFairTailAuthorityK_injective
