import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Incoming.Continuation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request
open RootLawDependentJointStateController CofinalHistorySettlement SourceOperationEffects SourceOperationExecution
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (count : Nat)
def kernelWord (sound : GeneratedRelationSoundnessAt (face root visit recognition count))
    (coordinate : GeneratedKernelResidualCoordinateAt (face root visit recognition count) sound) :
    (combined root visit recognition count).generatorClosure :=
  Classical.choose (Submodule.Quotient.mk_surjective (combined root visit recognition count).relationInGeneratorClosure
    coordinate.coordinate.val)

abbrev coverageWord (sound : GeneratedRelationSoundnessAt (face root visit recognition count))
    (coordinate : GeneratedCoverageResidualCoordinateAt (face root visit recognition count) sound) : Word root visit recognition :=
  Finsupp.single (.const coordinate.representative) 1

def rawOfWord (word : Word root visit recognition) : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root visit recognition) (Var:=ChangedVar (Variable root visit recognition))
    (sort:=SourceOperationNative.Tree.Fold.Slot.result) :=
  ⟨mixed root visit recognition,SourceOperationExecution.Coefficients.expression word⟩
end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
