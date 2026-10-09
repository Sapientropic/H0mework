import H0mework.Versions.PR.Realization.Perfectification.Occurrence.Temporal.History.Common.Action.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryCommon.Root.Action
open RootLawDependentJointStateController RootLawDependentJointTransition
open CofinalHistoryTransition SourceGeneratedObservationAction SourceGeneratedActionObservationHistory
namespace R
export SourceHistoryCommon.Root (step sourceHistory targetHistory common left right)
end R
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (R.step root visit recognition))
open RootInquiryCompletion
abbrev Material := Plan root visit recognition successor ×
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value root visit recognition successor)
    (Var:=Variables root visit recognition successor) (sort:=ULift.up .result)
def material : Material root visit recognition successor := ⟨actualPlan root visit recognition successor,raw root visit recognition successor⟩
def component : SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit.{u+1}
  ActiveAt := fun _ {_current} _ => PUnit.{u+1}
  InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => Material root visit recognition successor
  project := fun _ {_current} _ _ => material root visit recognition successor
abbrev sourceRoot := root.withProjectionCoface (component root visit recognition successor)
abbrev sourceVisit : SourceNativeTemporalVisitAt (sourceRoot root visit recognition successor).toAuthoritativeRoot.toLedgerRoot := visit
def installedReader (occurrence : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) :=
  ((component root visit recognition successor).project PUnit.unit occurrence PUnit.unit).2
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
namespace F
export SourceTemporalMaterial.Calculation (runtime sourceRoot sourceVisit)
end F
abbrev actualRoot := F.sourceRoot (sourceRoot root visit recognition successor) (sourceVisit root visit recognition successor)
abbrev runtime := F.runtime (sourceRoot root visit recognition successor) (sourceVisit root visit recognition successor) U7 calculus
  (installedReader root visit recognition successor)
def face (count : Nat) : SourceNativeRootSemanticFaceAt
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.root
      (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) count)
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.visit
      (actualRoot root visit recognition successor) visit (installedReader root visit recognition successor) count) where
  projection := .inherited (.inherited (.inherited
    ((RootGeneratedDebtActivationJointSource.OwnerFree.baseInstallation (actualRoot root visit recognition successor).toAuthoritativeRoot
      visit.current (installedReader root visit recognition successor)).embed (.inl (.inherited (.component PUnit.unit))))))
  active := PUnit.unit
  classifier_eq := rfl

def recoveredAction (count : Nat) : Joint root visit recognition successor →ₗ[ℤ] Joint root visit recognition successor :=
  (face root visit recognition successor U7 calculus count).rootRead.1.source.sourceAction.carrierAction.prodMap
    (face root visit recognition successor U7 calculus count).rootRead.1.target.sourceAction.carrierAction
def recoveredMeasurement (count : Nat) : Joint root visit recognition successor →ₗ[ℤ] Measured H :=
  (WithLp.linearEquiv 2 ℤ (H × H)).symm.toLinearMap.comp
    ((face root visit recognition successor U7 calculus count).rootRead.1.source.measurement.prodMap
      (face root visit recognition successor U7 calculus count).rootRead.1.target.measurement)
def recoveredEvolution (count : Nat) : Measured H →ₗᵢ[ℂ] Measured H :=
  (face root visit recognition successor U7 calculus count).rootRead.1.source.hilbertEvolution.withLpProdMap 2
    (face root visit recognition successor U7 calculus count).rootRead.1.target.hilbertEvolution
abbrev recoveredDefect (count : Nat) := SourceGeneratedObservationAction.actionDefect
  (recoveredAction root visit recognition successor U7 calculus count) (observation root visit recognition successor)
def recoveredPairing (count : Nat) : Joint root visit recognition successor →ₗ[ℤ] Module.Dual ℤ (Joint root visit recognition successor) :=
  (((face root visit recognition successor U7 calculus count).rootRead.1.sourcePairing).comp (LinearMap.fst ℤ _ _)).compl₂ (LinearMap.fst ℤ _ _) +
    (((face root visit recognition successor U7 calculus count).rootRead.1.targetPairing).comp (LinearMap.snd ℤ _ _)).compl₂ (LinearMap.snd ℤ _ _)
def recoveredResidual (count : Nat) (value : Joint root visit recognition successor) : Measured H :=
  recoveredEvolution root visit recognition successor U7 calculus count
    (recoveredMeasurement root visit recognition successor U7 calculus count value) -
  recoveredMeasurement root visit recognition successor U7 calculus count
    (recoveredAction root visit recognition successor U7 calculus count value)
def RunAt (selected : Option (StepLedgerSuccessorAt (R.step root visit recognition))) : Type (u+15) :=
  match selected with
  | none => ULift.{u+15} (type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.runtime root visit recognition U7 calculus))
  | some successor => ULift.{u+15} (type_of% (runtime root visit recognition successor U7 calculus))
def generated : RunAt root visit recognition U7 calculus (stepSuccessor? (R.step root visit recognition)) := by
  generalize selected_eq : stepSuccessor? (R.step root visit recognition) = selected
  cases selected with
  | none => exact ⟨SourceOperationNative.Tree.Fold.Dependent.Branch.runtime root visit recognition U7 calculus⟩
  | some successor => exact ⟨runtime root visit recognition successor U7 calculus⟩
end SourceHistoryCommon.Root.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
