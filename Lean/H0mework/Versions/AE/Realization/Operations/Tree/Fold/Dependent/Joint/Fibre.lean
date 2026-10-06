import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.CalculationConsumer
import H0mework.Realization.Logic.FibreLift
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceGeneratedScalarDifferentialResidual SourceOperationLogic SourceOperationLogic.FibreLift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (node : GeneratedNodeAt (recognition.generateStepAt visit) successor transition.history)
def sourceDifferential : C root visit recognition →ₗ[ℤ] H :=
  (((sourceRaw root visit recognition successor transition node).hilbertEvolution.toLinearMap.restrictScalars ℤ).comp
    (sourceRaw root visit recognition successor transition node).measurement) -
  ((sourceRaw root visit recognition successor transition node).measurement.comp
    (sourceRaw root visit recognition successor transition node).sourceAction.carrierAction)
def targetDifferential : D root visit recognition successor →ₗ[ℤ] H :=
  (((targetRaw root visit recognition successor transition node).hilbertEvolution.toLinearMap.restrictScalars ℤ).comp
    (targetRaw root visit recognition successor transition node).measurement) -
  ((targetRaw root visit recognition successor transition node).measurement.comp
    (targetRaw root visit recognition successor transition node).sourceAction.carrierAction)
def residualMorphism : Morphism (sourceDifferential root visit recognition successor transition node)
    (targetDifferential root visit recognition successor transition node) where
  sourceMap := RootLawDependentJointTransition.carrierMap transition.history
  targetMap := LinearMap.id
  commutes := by
    apply LinearMap.ext
    intro value
    exact (vector_transport root visit recognition successor transition node value).symm
abbrev residualKernelMap := kernelMap (residualMorphism root visit recognition successor transition node)
abbrev residualFibreMap (value : C root visit recognition) :=
  mapFibre (residualMorphism root visit recognition successor transition node) value
abbrev residualLift (value : C root visit recognition)
    (target : Fibre (targetDifferential root visit recognition successor transition node)
      (q (targetDifferential root visit recognition successor transition node) (RootLawDependentJointTransition.carrierMap transition.history value))) :=
  liftingResidual (residualMorphism root visit recognition successor transition node) value target

theorem residual_kernel_read (coordinate : LinearMap.ker (sourceDifferential root visit recognition successor transition node)) :
    (residualKernelMap root visit recognition successor transition node coordinate).val =
      RootLawDependentJointTransition.carrierMap transition.history coordinate.val := rfl

theorem residual_lift_exact (value : C root visit recognition)
    (target : Fibre (targetDifferential root visit recognition successor transition node)
      (q (targetDifferential root visit recognition successor transition node) (RootLawDependentJointTransition.carrierMap transition.history value))) :
    residualLift root visit recognition successor transition node value target = 0 ↔
      ∃ representative : Fibre (sourceDifferential root visit recognition successor transition node)
        (q (sourceDifferential root visit recognition successor transition node) value),
        residualFibreMap root visit recognition successor transition node value representative = target :=
  liftingResidual_eq_zero_iff _ _ _
end SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
