import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Source.SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision

/-!
# Strict information gain of every finite-archive revision

The generated successor archive projects exactly to its predecessor, but its
new honest witness bit cannot be decoded from the predecessor archive.  Its
finite carrier therefore grows by an exact factor of two at every requested
revision depth.  Carrier capacity is kept distinct from actual image coverage.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveStrictGain

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision
open M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision.CanonicalPaidReplayFiniteArchiveRevisionCalculationAt

/-- Forget exactly the newest witness bit.  This is a readout projection, not
a reverse authority map. -/
def canonicalPaidReplayFiniteArchiveRevisionProjection
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt calculation
      ).Archive → calculation.Archive :=
  Prod.fst

/-- The successor readout projects definitionally to the predecessor readout. -/
theorem canonicalPaidReplayFiniteArchiveRevisionProjection_exact
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    canonicalPaidReplayFiniteArchiveRevisionProjection calculation
        ((canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
          calculation).archiveReadout replay) =
      calculation.archiveReadout replay := by
  rfl

/-- The new witness bit is genuinely new relative to the predecessor archive:
no decoder from old archive values can reproduce it on every actual replay. -/
theorem canonicalPaidReplayArchiveWitnessTag_notFactorThroughCurrentArchive
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    ¬ ∃ decode : calculation.Archive → Bool,
      ∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
        decode (calculation.archiveReadout replay) =
          canonicalPaidReplayArchiveWitnessPublicationTag calculation
            replay := by
  rintro ⟨decode, factorizes⟩
  let pair := calculation.currentPair
  have archiveEquality :
      calculation.archiveReadout pair.left =
        calculation.archiveReadout pair.right := by
    exact congrArg Prod.snd pair.visible_eq
  have tagEquality :
      canonicalPaidReplayArchiveWitnessPublicationTag calculation pair.left =
        canonicalPaidReplayArchiveWitnessPublicationTag calculation
          pair.right := by
    calc
      canonicalPaidReplayArchiveWitnessPublicationTag calculation pair.left =
          decode (calculation.archiveReadout pair.left) :=
        (factorizes pair.left).symm
      _ = decode (calculation.archiveReadout pair.right) :=
        congrArg decode archiveEquality
      _ = canonicalPaidReplayArchiveWitnessPublicationTag calculation
          pair.right := factorizes pair.right
  exact
    (canonicalPaidReplayArchiveCurrentKernelRefinementAt calculation
      ).publicationTag_ne tagEquality

/-- Exact one-step carrier-capacity law.  This says nothing by itself about
the cardinality of the actual readout image. -/
theorem canonicalPaidReplayFiniteArchiveGeneratedNext_card
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    @Fintype.card
        (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
          calculation).Archive
        (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
          calculation).archiveFintype =
      @Fintype.card calculation.Archive calculation.archiveFintype * 2 := by
  let _ : Fintype calculation.Archive := calculation.archiveFintype
  change Fintype.card (calculation.Archive × Bool) =
    Fintype.card calculation.Archive * 2
  simp

/-- Exact all-depth carrier-capacity law for the predecessor-generated
revision calculation. -/
theorem canonicalPaidReplayFiniteArchiveRevision_card_exact
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    ∀ depth : Nat,
      let state :=
        canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
          sourceIndex lowerBound archive depth
      @Fintype.card state.Archive state.archiveFintype =
        Fintype.card Archive * 2 ^ depth := by
  intro depth
  induction depth with
  | zero =>
      change Fintype.card Archive = Fintype.card Archive * 1
      omega
  | succ depth inductionHypothesis =>
      change
        @Fintype.card
            (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
              (canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
                sourceIndex lowerBound archive depth)).Archive
            (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
              (canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
                sourceIndex lowerBound archive depth)).archiveFintype =
          Fintype.card Archive * 2 ^ (depth + 1)
      rw [canonicalPaidReplayFiniteArchiveGeneratedNext_card]
      change
        @Fintype.card
            (canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
              sourceIndex lowerBound archive depth).Archive
            (canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
              sourceIndex lowerBound archive depth).archiveFintype =
          Fintype.card Archive * 2 ^ depth at inductionHypothesis
      rw [inductionHypothesis]
      simp [pow_succ, Nat.mul_assoc]

/-! ## Actual readout-image growth -/

/-- Finite image of the current actual replay readout, using the exact finite
archive instance stored by the calculation. -/
@[instance_reducible] noncomputable def canonicalPaidReplayFiniteArchiveImageFintype
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    Fintype (Set.range calculation.archiveReadout) := by
  letI : Fintype calculation.Archive := calculation.archiveFintype
  exact Fintype.ofFinite _

/-- Projection restricted to the actual successor image. -/
def canonicalPaidReplayFiniteArchiveImageProjection
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    Set.range
          (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
            calculation).archiveReadout →
      Set.range calculation.archiveReadout :=
  fun revised =>
    ⟨canonicalPaidReplayFiniteArchiveRevisionProjection calculation revised.1,
      by
        rcases revised.2 with ⟨replay, replayEquality⟩
        refine ⟨replay, ?_⟩
        rw [← replayEquality]
        exact
          canonicalPaidReplayFiniteArchiveRevisionProjection_exact
            calculation replay⟩

theorem canonicalPaidReplayFiniteArchiveImageProjection_surjective
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    Function.Surjective
      (canonicalPaidReplayFiniteArchiveImageProjection calculation) := by
  rintro ⟨oldValue, replay, rfl⟩
  refine
    ⟨⟨(canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt calculation
          ).archiveReadout replay,
        ⟨replay, rfl⟩⟩,
      ?_⟩
  apply Subtype.ext
  exact
    canonicalPaidReplayFiniteArchiveRevisionProjection_exact calculation
      replay

theorem canonicalPaidReplayFiniteArchiveImageProjection_notInjective
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    ¬ Function.Injective
      (canonicalPaidReplayFiniteArchiveImageProjection calculation) := by
  let pair := calculation.currentPair
  let next :=
    canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt calculation
  let leftImage : Set.range next.archiveReadout :=
    ⟨next.archiveReadout pair.left, ⟨pair.left, rfl⟩⟩
  let rightImage : Set.range next.archiveReadout :=
    ⟨next.archiveReadout pair.right, ⟨pair.right, rfl⟩⟩
  intro projectionInjective
  have projectedEquality :
      canonicalPaidReplayFiniteArchiveImageProjection calculation leftImage =
        canonicalPaidReplayFiniteArchiveImageProjection calculation
          rightImage := by
    apply Subtype.ext
    exact congrArg Prod.snd pair.visible_eq
  have imageEquality := projectionInjective projectedEquality
  exact
    canonicalPaidReplayRefinedArchive_separatesCurrentPair calculation
      (congrArg Subtype.val imageEquality)

/-- Strongest image statement: the set of archive values actually attained
by generated paid replays grows strictly at every revision step. -/
theorem canonicalPaidReplayFiniteArchiveActualImage_card_strictlyGrows
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    @Fintype.card (Set.range calculation.archiveReadout)
        (canonicalPaidReplayFiniteArchiveImageFintype calculation) <
      @Fintype.card
        (Set.range
          (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
            calculation).archiveReadout)
        (canonicalPaidReplayFiniteArchiveImageFintype
          (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
            calculation)) := by
  exact
    @Fintype.card_lt_of_surjective_not_injective
      (Set.range
        (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
          calculation).archiveReadout)
      (Set.range calculation.archiveReadout)
      (canonicalPaidReplayFiniteArchiveImageFintype
        (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
          calculation))
      (canonicalPaidReplayFiniteArchiveImageFintype calculation)
      (canonicalPaidReplayFiniteArchiveImageProjection calculation)
      (canonicalPaidReplayFiniteArchiveImageProjection_surjective calculation)
      (canonicalPaidReplayFiniteArchiveImageProjection_notInjective
        calculation)

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveStrictGain
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveStrictGain.canonicalPaidReplayFiniteArchiveRevisionProjection_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveStrictGain.canonicalPaidReplayArchiveWitnessTag_notFactorThroughCurrentArchive
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveStrictGain.canonicalPaidReplayFiniteArchiveGeneratedNext_card
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveStrictGain.canonicalPaidReplayFiniteArchiveRevision_card_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveStrictGain.canonicalPaidReplayFiniteArchiveActualImage_card_strictlyGrows
