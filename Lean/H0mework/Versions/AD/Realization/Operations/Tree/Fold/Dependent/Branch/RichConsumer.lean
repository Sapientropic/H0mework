import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Rich
import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Readback
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (count : Nat)
variable (word : SourceHistoryCommon.Root.G root recognition →₀ ℤ)
theorem actual_word_generated : actualWordEvaluation root visit recognition U7 calculus count word =
    Side.packetWordEvaluation root recognition (outcome root visit recognition).2.2 word := rfl

theorem actual_next_word_generated : actualNextWordEvaluation root visit recognition U7 calculus count word =
    Side.packetWordEvaluation root recognition (nextOutcome root visit recognition).2.2 word := rfl

theorem actual_inverse_generated : actualInverse root visit recognition U7 calculus count =
    Side.packetInverse root recognition (outcome root visit recognition).2.2 := rfl

theorem actual_next_inverse_generated : actualNextInverse root visit recognition U7 calculus count =
    Side.packetInverse root recognition (nextOutcome root visit recognition).2.2 := rfl

theorem actual_maps_generated : actualMaps root visit recognition U7 calculus count =
    Side.packetMaps root recognition (outcome root visit recognition).2.2 := rfl

theorem actual_next_maps_generated : actualNextMaps root visit recognition U7 calculus count =
    Side.packetMaps root recognition (nextOutcome root visit recognition).2.2 := rfl
end SourceOperationNative.Tree.Fold.Dependent.Branch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
