import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Observer.Refinement.Consumer.ProofCarryingContributionCapacityPairIntentFiniteObserverKernelEscape

/-!
# Unified PairIntent observer kernel escape

One mouth exposes the generic positive escape for every noninjective observer
and its premise-free finite-cardinality instance.  The finite branch delegates
to the same pair, witness, publication and refinement producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityPairIntentObserverKernelEscape

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14ProofCarryingContributionCapacityPairIntentNoninjectiveObserverKernelEscape
open M14ProofCarryingContributionCapacityPairIntentFiniteObserverKernelEscape

/-- Complete positive observer consumer: arbitrary noninjective readouts and
all finite readouts share the same source-witness kernel-escape mechanism. -/
theorem pairIntentObserverKernelEscape_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (∀ (Visible : Type) (observe : Nat → Visible),
      (notInjective : ¬ Function.Injective observe) →
        type_of%
          (pairIntentNoninjectiveObserverKernelEscapeAt_directConsumer oldVisit
            sourceIndex boundary observe notInjective)) ∧
      (∀ (Visible : Type) [Fintype Visible] (observe : Nat → Visible),
        type_of%
          (pairIntentFiniteObserverKernelEscape_directConsumer oldVisit
            sourceIndex boundary observe)) := by
  constructor
  · intro Visible observe notInjective
    exact pairIntentNoninjectiveObserverKernelEscapeAt_directConsumer oldVisit
      sourceIndex boundary observe notInjective
  · intro Visible _inst observe
    exact pairIntentFiniteObserverKernelEscape_directConsumer oldVisit
      sourceIndex boundary observe

end
end M14ProofCarryingContributionCapacityPairIntentObserverKernelEscape
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPairIntentObserverKernelEscape.pairIntentObserverKernelEscape_directConsumer
