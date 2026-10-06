import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace D
export SourceOperationNative.Tree.Fold.Dependent (FeedAt sourceFeed)
end D
namespace F
export SourceOperationNative.Tree.Fold (Value Var environment program program_value program_budget)
end F
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
open RootInquiryCompletion
abbrev Material := Node root visit recognition ×
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue (Value root visit recognition))
    (Var:=Variable root visit recognition) (sort:=.result) ×
  Side.Packet root recognition × Side.Packet root recognition
def material : Material root visit recognition := ⟨node root visit recognition,raw root visit recognition,
    Side.packet root recognition (node root visit recognition).2,
    Side.packet root recognition (nextNode root visit recognition (node root visit recognition)).2⟩
def component : SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit.{u+1}
  ActiveAt := fun _ {_current} _ => PUnit.{u+1}
  InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => Material root visit recognition
  project := fun _ {_current} _ _ => material root visit recognition
abbrev sourceRoot := root.withProjectionCoface (component root visit recognition)
abbrev sourceVisit : SourceNativeTemporalVisitAt (sourceRoot root visit recognition).toAuthoritativeRoot.toLedgerRoot := visit
def installedReader (occurrence : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) :=
  ((component root visit recognition).project PUnit.unit occurrence PUnit.unit).2.1
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
namespace C
export SourceTemporalMaterial.Calculation (runtime sourceRoot sourceVisit)
end C
abbrev runtime := C.runtime (sourceRoot root visit recognition) (sourceVisit root visit recognition) U7 calculus
  (installedReader root visit recognition)
def face (count : Nat) : SourceNativeRootSemanticFaceAt
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.root
      (C.sourceRoot (sourceRoot root visit recognition) (sourceVisit root visit recognition)) visit U7 calculus
      (installedReader root visit recognition) count)
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.visit
      (C.sourceRoot (sourceRoot root visit recognition) (sourceVisit root visit recognition)) visit
      (installedReader root visit recognition) count) where
  projection := .inherited (.inherited (.inherited
    ((RootGeneratedDebtActivationJointSource.OwnerFree.baseInstallation
      (C.sourceRoot (sourceRoot root visit recognition) (sourceVisit root visit recognition)).toAuthoritativeRoot
      visit.current (installedReader root visit recognition)).embed (.inl (.inherited (.component PUnit.unit))))))
  active := PUnit.unit
  classifier_eq := rfl
end SourceOperationNative.Tree.Fold.Dependent.Branch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
