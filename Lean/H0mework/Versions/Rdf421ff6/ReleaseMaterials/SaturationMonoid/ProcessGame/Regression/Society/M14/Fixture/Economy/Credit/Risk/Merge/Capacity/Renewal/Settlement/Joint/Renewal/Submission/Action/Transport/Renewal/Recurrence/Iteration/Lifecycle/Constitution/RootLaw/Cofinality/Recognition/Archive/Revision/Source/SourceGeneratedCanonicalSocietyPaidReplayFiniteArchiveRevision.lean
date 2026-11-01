import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Source.SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveKernel
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.SourceWitnessRefinement

/-!
# Source-generated finite-archive witness revision

Every finite archive calculation carries a cofinal paid-replay authority
kernel.  The left replay's exact depth, paid-step incidence and canonical
payment next generate an honest Boolean witness publication.  Adding that
bit separates the current pair, while finiteness of the refined archive
generates a strictly later pair.

The recursive calculation is computed from its predecessor.  It stores no
authority value, endpoint schedule, occurrence registry or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveKernel

/-- Post-emission finite-archive calculation at one revision depth.  Its
kernel is generated after `lowerBound`; neither the pair nor its authority is
an input to the calculation. -/
structure CanonicalPaidReplayFiniteArchiveRevisionCalculationAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Type 27 where
  private mk ::
  Archive : Type
  archiveFintype : Fintype Archive
  archiveReadout :
    AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex →
      Archive
  lowerBound : Nat

namespace CanonicalPaidReplayFiniteArchiveRevisionCalculationAt

variable {oldVisit : OldVisit} {sourceIndex : Nat}

def observer
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :=
  canonicalPaidReplayFiniteArchiveObserverAt oldVisit sourceIndex
    calculation.archiveReadout

/-- The current kernel is regenerated on demand from the exact stored finite
archive instance, readout and bound; it is not a state field or registry. -/
noncomputable def cofinalKernel
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :=
  @canonicalPaidReplayFiniteArchiveCofinalKernelPairAt calculation.Archive
    calculation.archiveFintype oldVisit sourceIndex calculation.lowerBound
      calculation.archiveReadout

noncomputable def currentPair
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    AuthorityKernelPair calculation.observer :=
  calculation.cofinalKernel.1

theorem currentPair_left_later
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    calculation.lowerBound < calculation.currentPair.left.1 :=
  calculation.cofinalKernel.2.1

theorem currentPair_right_later
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    calculation.lowerBound < calculation.currentPair.right.1 :=
  calculation.cofinalKernel.2.2

end CanonicalPaidReplayFiniteArchiveRevisionCalculationAt

open CanonicalPaidReplayFiniteArchiveRevisionCalculationAt

/-- Generated paid replays are determined by their temporal depth. -/
theorem paidReplay_eq_of_depth_eq
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (left right :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
    (depthEquality : left.1 = right.1) :
    left = right := by
  cases left with
  | mk leftDepth leftReplay =>
      cases right with
      | mk rightDepth rightReplay =>
          simp only at depthEquality
          subst rightDepth
          cases leftReplay
          cases rightReplay
          rfl

/-- Every exact kernel pair in this paid-replay family has different depths. -/
theorem paidReplayKernelPair_depths_ne
    {oldVisit : OldVisit} {sourceIndex : Nat}
    {Archive : Type}
    (archive :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex →
        Archive)
    (pair : AuthorityKernelPair
      (canonicalPaidReplayFiniteArchiveObserverAt oldVisit sourceIndex
        archive)) :
    pair.left.1 ≠ pair.right.1 := by
  intro depthEquality
  exact pair.occurrence_ne
    (paidReplay_eq_of_depth_eq pair.left pair.right depthEquality)

/-- Initial calculation generated from the caller's finite readout only. -/
noncomputable def canonicalPaidReplayFiniteArchiveInitialCalculationAt
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
      sourceIndex where
  Archive := Archive
  archiveFintype := inferInstance
  archiveReadout := archive
  lowerBound := lowerBound

/-- Private source witness at the current generated left replay.  The
publication support is an exact replay-depth label; the witness also consumes
the anchor's existing paid-step and canonical payment-next seams. -/
structure SourceGeneratedCanonicalPaidReplayArchiveWitnessAt
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    Type where
  private mk ::
  exactReplayLabel : replay = calculation.currentPair.left
  exactReplayDepthLabel : replay.1 = calculation.currentPair.left.1
  exactActualPathLabel :
    replay.2.actualPath = calculation.currentPair.left.2.actualPath
  anchorPaidStepConsumesExactPayment :
    type_of% calculation.currentPair.left.2.paidStep_consumes_exactPayment
  anchorPaymentNextIsCanonicalTarget :
    type_of% calculation.currentPair.left.2.paymentNext_isCanonicalTarget

/-- Sole witness producer at the exact source-generated left endpoint. -/
def sourceGeneratedCanonicalPaidReplayArchiveWitnessAt
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    SourceGeneratedCanonicalPaidReplayArchiveWitnessAt calculation
      calculation.currentPair.left where
  exactReplayLabel := rfl
  exactReplayDepthLabel := rfl
  exactActualPathLabel := rfl
  anchorPaidStepConsumesExactPayment :=
    calculation.currentPair.left.2.paidStep_consumes_exactPayment
  anchorPaymentNextIsCanonicalTarget :=
    calculation.currentPair.left.2.paymentNext_isCanonicalTarget

/-- Honest publication reads only replay-depth equality, never authority K. -/
noncomputable def canonicalPaidReplayArchiveWitnessPublicationTag
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    Bool := by
  classical
  exact decide (replay.1 = calculation.currentPair.left.1)

theorem canonicalPaidReplayArchiveWitnessPublicationTag_true_iff
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    canonicalPaidReplayArchiveWitnessPublicationTag calculation replay =
        true ↔
      Nonempty
        (SourceGeneratedCanonicalPaidReplayArchiveWitnessAt calculation
          replay) := by
  constructor
  · intro published
    have exactReplayDepthLabel :
        replay.1 = calculation.currentPair.left.1 := by
      simpa [canonicalPaidReplayArchiveWitnessPublicationTag] using published
    have exactReplayLabel :=
      paidReplay_eq_of_depth_eq replay calculation.currentPair.left
        exactReplayDepthLabel
    subst replay
    exact
      ⟨{ exactReplayLabel := rfl
         exactReplayDepthLabel := rfl
         exactActualPathLabel := rfl
         anchorPaidStepConsumesExactPayment :=
           calculation.currentPair.left.2.paidStep_consumes_exactPayment
         anchorPaymentNextIsCanonicalTarget :=
           calculation.currentPair.left.2.paymentNext_isCanonicalTarget }⟩
  · rintro ⟨witness⟩
    simpa [canonicalPaidReplayArchiveWitnessPublicationTag] using
      witness.exactReplayDepthLabel

def canonicalPaidReplayArchiveWitnessPublicationAt
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    SourceWitnessPublicationAt
      (SourceGeneratedCanonicalPaidReplayArchiveWitnessAt calculation) where
  publicationTag :=
    canonicalPaidReplayArchiveWitnessPublicationTag calculation
  publicationTag_eq_true_iff :=
    canonicalPaidReplayArchiveWitnessPublicationTag_true_iff calculation

theorem canonicalPaidReplayArchiveCurrentPair_rightWitness_isEmpty
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    IsEmpty
      (SourceGeneratedCanonicalPaidReplayArchiveWitnessAt calculation
        calculation.currentPair.right) :=
  ⟨fun witness =>
    calculation.currentPair.occurrence_ne witness.exactReplayLabel.symm⟩

/-- Generic source-witness refinement of the current exact pair. -/
theorem canonicalPaidReplayArchiveCurrentKernelRefinementAt
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    SourceWitnessKernelRefinementAt
      (canonicalPaidReplayArchiveWitnessPublicationAt calculation)
      calculation.currentPair := by
  apply sourceWitnessKernelRefinement
  · exact ⟨sourceGeneratedCanonicalPaidReplayArchiveWitnessAt calculation⟩
  · exact
      canonicalPaidReplayArchiveCurrentPair_rightWitness_isEmpty calculation

/-- The next finite archive is the old archive plus exactly the honest
publication bit. -/
def canonicalPaidReplayRefinedArchiveReadout
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    calculation.Archive × Bool :=
  (calculation.archiveReadout replay,
    canonicalPaidReplayArchiveWitnessPublicationTag calculation replay)

/-- The honest bit separates the current pair in the refined finite archive. -/
theorem canonicalPaidReplayRefinedArchive_separatesCurrentPair
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    canonicalPaidReplayRefinedArchiveReadout calculation
          calculation.currentPair.left ≠
      canonicalPaidReplayRefinedArchiveReadout calculation
        calculation.currentPair.right := by
  intro archiveEquality
  exact
    (canonicalPaidReplayArchiveCurrentKernelRefinementAt calculation
      ).publicationTag_ne
      (congrArg Prod.snd archiveEquality)

/-- Source-generated next calculation.  Its lower bound is the larger current
endpoint and its next pair is generated internally from the refined archive. -/
noncomputable def canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
      sourceIndex := by
  letI : Fintype calculation.Archive := calculation.archiveFintype
  let nextReadout := canonicalPaidReplayRefinedArchiveReadout calculation
  let nextLowerBound :=
    max calculation.currentPair.left.1 calculation.currentPair.right.1
  exact
    { Archive := calculation.Archive × Bool
      archiveFintype := inferInstance
      archiveReadout := nextReadout
      lowerBound := nextLowerBound }

@[simp] theorem canonicalPaidReplayFiniteArchiveGeneratedNext_lowerBound
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt calculation
        ).lowerBound =
      max calculation.currentPair.left.1
        calculation.currentPair.right.1 := by
  rfl

@[simp] theorem canonicalPaidReplayFiniteArchiveGeneratedNext_archiveReadout
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt calculation
        ).archiveReadout replay =
      canonicalPaidReplayRefinedArchiveReadout calculation replay := by
  rfl

theorem canonicalPaidReplayFiniteArchiveGeneratedNext_left_strictlyLater
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    calculation.currentPair.left.1 <
      (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt calculation
        ).currentPair.left.1 := by
  have later :=
    (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt calculation
      ).currentPair_left_later
  rw [canonicalPaidReplayFiniteArchiveGeneratedNext_lowerBound] at later
  exact (Nat.le_max_left _ _).trans_lt later

theorem canonicalPaidReplayFiniteArchiveGeneratedNext_right_strictlyLater
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    calculation.currentPair.right.1 <
      (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt calculation
        ).currentPair.right.1 := by
  have later :=
    (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt calculation
      ).currentPair_right_later
  rw [canonicalPaidReplayFiniteArchiveGeneratedNext_lowerBound] at later
  exact (Nat.le_max_right _ _).trans_lt later

theorem canonicalPaidReplayFiniteArchiveGeneratedNext_bound_strictlyLater
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    calculation.lowerBound <
      (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt calculation
        ).lowerBound := by
  rw [canonicalPaidReplayFiniteArchiveGeneratedNext_lowerBound]
  exact calculation.currentPair_left_later.trans_le
    (Nat.le_max_left _ _)

/-- All-depth post-emission revision calculation, recursively generated from
its predecessor rather than read from a stored depth schedule. -/
noncomputable def canonicalPaidReplayFiniteArchiveRevisionCalculationAt
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    Nat → CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
      sourceIndex
  | 0 =>
      canonicalPaidReplayFiniteArchiveInitialCalculationAt oldVisit sourceIndex
        lowerBound archive
  | depth + 1 =>
      canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
        (canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
          sourceIndex lowerBound archive depth)

@[simp] theorem canonicalPaidReplayFiniteArchiveRevisionCalculationAt_succ
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound depth : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit sourceIndex
        lowerBound archive (depth + 1) =
      canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
        (canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
          sourceIndex lowerBound archive depth) :=
  rfl

theorem canonicalPaidReplayFiniteArchiveRevisionBounds_strictMono
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    StrictMono
      (fun depth =>
        (canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
          sourceIndex lowerBound archive depth).lowerBound) := by
  apply strictMono_nat_of_lt_succ
  intro depth
  rw [canonicalPaidReplayFiniteArchiveRevisionCalculationAt_succ]
  exact
    canonicalPaidReplayFiniteArchiveGeneratedNext_bound_strictlyLater
      (canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex lowerBound archive depth)

theorem canonicalPaidReplayFiniteArchiveRevisionBounds_injective
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    Function.Injective
      (fun depth =>
        (canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
          sourceIndex lowerBound archive depth).lowerBound) :=
  (canonicalPaidReplayFiniteArchiveRevisionBounds_strictMono oldVisit
    sourceIndex lowerBound archive).injective

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision.paidReplayKernelPair_depths_ne
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision.canonicalPaidReplayArchiveWitnessPublicationTag_true_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision.canonicalPaidReplayArchiveCurrentKernelRefinementAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision.canonicalPaidReplayFiniteArchiveGeneratedNext_left_strictlyLater
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision.canonicalPaidReplayFiniteArchiveRevisionBounds_strictMono
