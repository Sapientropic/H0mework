import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Observer.Refinement.Source.SourceGeneratedContributionCapacityPairIntentNoninjectiveObserverWitnessPublication

/-!
# Proof-carrying PairIntent noninjective-observer kernel escape

Every noninjective observer of the named runtime generates its own exact
kernel pair and honest runtime-label witness.  Refinement restores faithful
authority reconstruction only on that generated two-point restriction; the
whole coarse observer remains non-faithful.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityPairIntentNoninjectiveObserverKernelEscape

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime
open M14SourceGeneratedContributionCapacityPairIntentOpenRuntimeClassicalNoSection
open M14SourceGeneratedContributionCapacityPairIntentFiniteObserverNoSection
open M14SourceGeneratedContributionCapacityPairIntentNoninjectiveObserverWitnessPublication

theorem pairIntentNoninjectiveObserver_twoPointPosteriorReconstruction
    {Visible : Type}
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (observe : Nat → Visible)
    (notInjective : ¬ Function.Injective observe) :
    let refinement := pairIntentNoninjectiveObserverKernelRefinementAt oldVisit
      sourceIndex boundary observe notInjective
    Nonempty
        (FaithfulAuthorityReconstruction refinement.twoPointObserver) ∧
      Nonempty (AuthorityFactorization refinement.twoPointObserver) := by
  dsimp
  let refinement := pairIntentNoninjectiveObserverKernelRefinementAt oldVisit
    sourceIndex boundary observe notInjective
  exact
    ⟨⟨refinement.twoPointFaithfulAuthorityReconstruction⟩,
      ⟨refinement.twoPointAuthorityFactorization⟩⟩

/-- Exact generic consumer.  It receives only a proof that the supplied
observer is noninjective; endpoints, collision equality and witness data are
all generated internally. -/
theorem pairIntentNoninjectiveObserverKernelEscapeAt_directConsumer
    {Visible : Type}
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (observe : Nat → Visible)
    (notInjective : ¬ Function.Injective observe) :
    let O := pairIntentAuthorityObserverAt oldVisit sourceIndex boundary
      observe
    let pair := pairIntentNoninjectiveObserverKernelPairAt oldVisit sourceIndex
      boundary observe notInjective
    let refinement := pairIntentNoninjectiveObserverKernelRefinementAt oldVisit
      sourceIndex boundary observe notInjective
    type_of%
        (pairIntentObserverNoSection_directConsumer oldVisit sourceIndex
          boundary) ∧
      Nonempty (AuthorityKernelPair O) ∧
      Nonempty
        (SourceGeneratedPairIntentRuntimeLabelWitnessAt oldVisit sourceIndex
          boundary pair.left pair.left) ∧
      IsEmpty
        (SourceGeneratedPairIntentRuntimeLabelWitnessAt oldVisit sourceIndex
          boundary pair.left pair.right) ∧
      (∀ depth : Nat,
        pairIntentRuntimeLabelPublicationTag oldVisit sourceIndex boundary
              pair.left depth = true ↔
          Nonempty
            (SourceGeneratedPairIntentRuntimeLabelWitnessAt oldVisit
              sourceIndex boundary pair.left depth)) ∧
      O.forget pair.left = O.forget pair.right ∧
      O.authorityK pair.left ≠ O.authorityK pair.right ∧
      type_of% pair.noOccurrenceLeftInverse ∧
      ¬ Nonempty (AuthorityFactorization O) ∧
      ¬ Nonempty (FaithfulAuthorityReconstruction O) ∧
      (pairIntentNoninjectiveObserverRefinedObserverAt oldVisit sourceIndex
          boundary observe notInjective).forget pair.left ≠
        (pairIntentNoninjectiveObserverRefinedObserverAt oldVisit sourceIndex
          boundary observe notInjective).forget pair.right ∧
      Nonempty
        (FaithfulAuthorityReconstruction refinement.twoPointObserver) ∧
      Nonempty (AuthorityFactorization refinement.twoPointObserver) ∧
      (∀ depth : Nat,
        type_of%
          (representationIntentU8EveryRevisedTick_generatesNext oldVisit
            sourceIndex boundary depth)) := by
  dsimp
  let O := pairIntentAuthorityObserverAt oldVisit sourceIndex boundary observe
  let pair := pairIntentNoninjectiveObserverKernelPairAt oldVisit sourceIndex
    boundary observe notInjective
  let refinement := pairIntentNoninjectiveObserverKernelRefinementAt oldVisit
    sourceIndex boundary observe notInjective
  exact
    ⟨pairIntentObserverNoSection_directConsumer oldVisit sourceIndex boundary,
      ⟨pair⟩,
      ⟨sourceGeneratedPairIntentRuntimeLabelWitnessAt oldVisit sourceIndex
        boundary pair.left⟩,
      pairIntentNoninjectiveObserverKernelPair_rightWitness_isEmpty oldVisit
        sourceIndex boundary observe notInjective,
      pairIntentRuntimeLabelPublicationTag_true_iff oldVisit sourceIndex
        boundary pair.left,
      pair.visible_eq,
      pair.authority_ne,
      pair.noOccurrenceLeftInverse,
      pair.noAuthorityFactorization,
      pair.noFaithfulAuthorityReconstruction,
      pairIntentNoninjectiveObserver_refinedVisible_ne oldVisit sourceIndex
        boundary observe notInjective,
      (pairIntentNoninjectiveObserver_twoPointPosteriorReconstruction oldVisit
        sourceIndex boundary observe notInjective).1,
      (pairIntentNoninjectiveObserver_twoPointPosteriorReconstruction oldVisit
        sourceIndex boundary observe notInjective).2,
      representationIntentU8EveryRevisedTick_generatesNext oldVisit sourceIndex
        boundary⟩

end
end M14ProofCarryingContributionCapacityPairIntentNoninjectiveObserverKernelEscape
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPairIntentNoninjectiveObserverKernelEscape.pairIntentNoninjectiveObserver_twoPointPosteriorReconstruction
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPairIntentNoninjectiveObserverKernelEscape.pairIntentNoninjectiveObserverKernelEscapeAt_directConsumer
