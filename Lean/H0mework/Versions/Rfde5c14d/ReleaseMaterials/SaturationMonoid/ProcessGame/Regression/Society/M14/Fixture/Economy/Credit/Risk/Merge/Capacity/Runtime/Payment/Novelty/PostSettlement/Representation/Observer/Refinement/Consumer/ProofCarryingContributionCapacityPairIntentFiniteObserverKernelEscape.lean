import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Observer.Refinement.Source.SourceGeneratedContributionCapacityPairIntentFiniteObserverWitnessPublication
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Observer.Refinement.Consumer.ProofCarryingContributionCapacityPairIntentNoninjectiveObserverKernelEscape

/-!
# Finite PairIntent kernel escape as the exact generic instance

Finite cardinality supplies the only extra fact required by the generic
noninjective-observer consumer.  No finite-specific pair, witness,
publication, refinement, or reconstruction is rebuilt here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityPairIntentFiniteObserverKernelEscape

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPairIntentFiniteObserverWitnessPublication
open M14ProofCarryingContributionCapacityPairIntentNoninjectiveObserverKernelEscape

theorem pairIntentFiniteObserver_twoPointPosteriorReconstruction
    {Visible : Type} [Fintype Visible]
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (observe : Nat → Visible) :
    type_of%
      (pairIntentNoninjectiveObserver_twoPointPosteriorReconstruction oldVisit
        sourceIndex boundary observe
          (pairIntentFiniteObserver_notInjective oldVisit sourceIndex boundary
            observe)) :=
  pairIntentNoninjectiveObserver_twoPointPosteriorReconstruction oldVisit
    sourceIndex boundary observe
      (pairIntentFiniteObserver_notInjective oldVisit sourceIndex boundary
        observe)

/-- Premise-free finite instance of the unique generic positive escape. -/
theorem pairIntentFiniteObserverKernelEscape_directConsumer
    {Visible : Type} [Fintype Visible]
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (observe : Nat → Visible) :
    type_of%
      (pairIntentNoninjectiveObserverKernelEscapeAt_directConsumer oldVisit
        sourceIndex boundary observe
          (pairIntentFiniteObserver_notInjective oldVisit sourceIndex boundary
            observe)) :=
  pairIntentNoninjectiveObserverKernelEscapeAt_directConsumer oldVisit
    sourceIndex boundary observe
      (pairIntentFiniteObserver_notInjective oldVisit sourceIndex boundary
        observe)

end
end M14ProofCarryingContributionCapacityPairIntentFiniteObserverKernelEscape
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPairIntentFiniteObserverKernelEscape.pairIntentFiniteObserver_twoPointPosteriorReconstruction
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPairIntentFiniteObserverKernelEscape.pairIntentFiniteObserverKernelEscape_directConsumer
