import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.Laws
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint
open SourceOperationEffects SourceOperationExecution
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace T
export SourceTemporalMaterial.Action (Result actual receipt nextCode residualRaw materialRoot materialVisit)
end T
namespace D
export SourceOperationNative.Tree.Fold.Dependent (nativeTree nativeRaw nativeReader)
end D
namespace F
export SourceOperationNative.Tree.Fold (Value Var environment program program_value program_budget budget)
end F
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
variable (transition : GeneratedStepJointTransitionAt (step root visit recognition) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (step root visit recognition))
  (stepTargetPairingOccurrence (step root visit recognition) successor))
open RootInquiryCompletion
abbrev Material := RootedAccountedUnfolding (Node root visit recognition successor transition) ×
  Expr (Value root visit recognition successor transition) (Variable root visit recognition successor transition) .result ×
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=SourceOperationScalarInventoryLift.PairValue (Value root visit recognition successor transition))
    (Var:=Variable root visit recognition successor transition) (sort:=.result) ×
  SourceOperationLogic.Fibre (SourceOperationScalarRelations.evaluation (R:=ℤ)
    (F.environment + delta root visit recognition successor transition))
    (SourceOperationLogic.q (SourceOperationScalarRelations.evaluation (R:=ℤ)
      (F.environment + delta root visit recognition successor transition)) (oldWord root visit recognition successor transition alignment)) ×
  SourceOperationLogic.FibreLift.LiftingResidual (morphism root visit recognition successor transition)
def material : Material root visit recognition successor transition alignment :=
  ⟨tree root visit recognition successor transition alignment,
    programme root visit recognition successor transition alignment,
    raw root visit recognition successor transition alignment,
    target root visit recognition successor transition alignment,
    reverse root visit recognition successor transition alignment⟩
def component : SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit.{u+1}
  ActiveAt := fun _ {_current} _ => PUnit.{u+1}
  InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => Material root visit recognition successor transition alignment
  project := fun _ {_current} _ _ => material root visit recognition successor transition alignment
abbrev sourceRoot := root.withProjectionCoface (component root visit recognition successor transition alignment)
abbrev sourceVisit : SourceNativeTemporalVisitAt (sourceRoot root visit recognition successor transition alignment).toAuthoritativeRoot.toLedgerRoot := visit
def installedReader (occurrence : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) :=
  ((component root visit recognition successor transition alignment).project PUnit.unit occurrence PUnit.unit).2.2.1
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
namespace C
export SourceTemporalMaterial.Calculation (runtime sourceRoot sourceVisit)
end C
abbrev runtime := C.runtime (sourceRoot root visit recognition successor transition alignment)
  (sourceVisit root visit recognition successor transition alignment) U7 calculus
  (installedReader root visit recognition successor transition alignment)
def face (count : Nat) : SourceNativeRootSemanticFaceAt
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.root
      (C.sourceRoot (sourceRoot root visit recognition successor transition alignment)
        (sourceVisit root visit recognition successor transition alignment)) visit U7 calculus
      (installedReader root visit recognition successor transition alignment) count)
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.visit
      (C.sourceRoot (sourceRoot root visit recognition successor transition alignment)
        (sourceVisit root visit recognition successor transition alignment)) visit
      (installedReader root visit recognition successor transition alignment) count) where
  projection := .inherited (.inherited (.inherited
    ((RootGeneratedDebtActivationJointSource.OwnerFree.baseInstallation
      (C.sourceRoot (sourceRoot root visit recognition successor transition alignment)
        (sourceVisit root visit recognition successor transition alignment)).toAuthoritativeRoot
      visit.current (installedReader root visit recognition successor transition alignment)).embed
        (.inl (.inherited (.component PUnit.unit))))))
  active := PUnit.unit
  classifier_eq := rfl
end SourceOperationNative.Tree.Fold.Dependent.Joint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
