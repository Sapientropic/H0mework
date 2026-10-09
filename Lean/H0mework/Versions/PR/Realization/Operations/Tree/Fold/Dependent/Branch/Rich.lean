import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Inverse
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Maps
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
abbrev actualInverse := Side.packetInverse root recognition (actualSide root visit recognition U7 calculus count)
abbrev actualNextInverse := Side.packetInverse root recognition (actualNextSide root visit recognition U7 calculus count)
abbrev actualWordEvaluation (word : SourceHistoryCommon.Root.G root recognition →₀ ℤ) :=
  Side.packetWordEvaluation root recognition (actualSide root visit recognition U7 calculus count) word
abbrev actualNextWordEvaluation (word : SourceHistoryCommon.Root.G root recognition →₀ ℤ) :=
  Side.packetWordEvaluation root recognition (actualNextSide root visit recognition U7 calculus count) word
abbrev actualMaps := Side.packetMaps root recognition (actualSide root visit recognition U7 calculus count)
abbrev actualNextMaps := Side.packetMaps root recognition (actualNextSide root visit recognition U7 calculus count)
abbrev richRuntime :=
  ((runtime root visit recognition U7 calculus,
      actualInverse root visit recognition U7 calculus 0,actualNextInverse root visit recognition U7 calculus 0,
      actualWordEvaluation root visit recognition U7 calculus 0,actualNextWordEvaluation root visit recognition U7 calculus 0,
      actualMaps root visit recognition U7 calculus 0,actualNextMaps root visit recognition U7 calculus 0),
    actualSideOutput root visit recognition U7 calculus 0,actualNextSideOutput root visit recognition U7 calculus 0)
end SourceOperationNative.Tree.Fold.Dependent.Branch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
