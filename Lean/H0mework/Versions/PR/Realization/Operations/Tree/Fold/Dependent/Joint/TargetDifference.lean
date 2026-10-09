import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.Fibre
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceGeneratedSubfaceFactorization SourceOperationLogic SourceOperationLogic.FibreLift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (node : GeneratedNodeAt (recognition.generateStepAt visit) successor transition.history)
variable (sourceValue : C root visit recognition) (targetValue : D root visit recognition successor)
abbrev targetActionValue := (targetRaw root visit recognition successor transition node).sourceAction.carrierAction targetValue
abbrev sourceActionValue := (sourceRaw root visit recognition successor transition node).sourceAction.carrierAction sourceValue
def targetDifference : D root visit recognition successor :=
  targetActionValue root visit recognition successor transition node targetValue -
    RootLawDependentJointTransition.carrierMap transition.history (sourceActionValue root visit recognition successor transition node sourceValue)
def targetRangeResidual := SourceGeneratedSubfaceFactorization.residualMap (LinearMap.id : D root visit recognition successor →ₗ[ℤ] D root visit recognition successor)
  (RootLawDependentJointTransition.carrierMap transition.history)
  (targetDifference root visit recognition successor transition node sourceValue targetValue)
def targetObservationResidual : H := targetDifferential root visit recognition successor transition node
  (targetDifference root visit recognition successor transition node sourceValue targetValue)

theorem target_observation_equation : targetObservationResidual root visit recognition successor transition node sourceValue targetValue =
    targetResidual root visit recognition successor transition node (targetActionValue root visit recognition successor transition node targetValue) -
      sourceResidual root visit recognition successor transition node (sourceActionValue root visit recognition successor transition node sourceValue) := by
  unfold targetObservationResidual targetDifference
  rw [map_sub]
  exact congrArg₂ (· - ·) rfl (vector_transport root visit recognition successor transition node _)

theorem range_residual_exact : targetRangeResidual root visit recognition successor transition node sourceValue targetValue = 0 ↔
    ∃ representative : C root visit recognition, RootLawDependentJointTransition.carrierMap transition.history representative =
      targetActionValue root visit recognition successor transition node targetValue := by
  change Submodule.Quotient.mk (targetDifference root visit recognition successor transition node sourceValue targetValue) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨direction, same⟩
    refine ⟨direction + sourceActionValue root visit recognition successor transition node sourceValue,?_⟩
    rw [map_add,same]
    exact sub_add_cancel _ _
  · rintro ⟨representative,same⟩
    refine ⟨representative - sourceActionValue root visit recognition successor transition node sourceValue,?_⟩
    rw [map_sub,same]
    rfl

theorem fibre_preimage_exact :
    (∃ representative : Fibre (sourceDifferential root visit recognition successor transition node)
      (q (sourceDifferential root visit recognition successor transition node) (sourceActionValue root visit recognition successor transition node sourceValue)),
      RootLawDependentJointTransition.carrierMap transition.history representative.val = targetActionValue root visit recognition successor transition node targetValue) ↔
    targetObservationResidual root visit recognition successor transition node sourceValue targetValue = 0 ∧
      targetRangeResidual root visit recognition successor transition node sourceValue targetValue = 0 := by
  constructor
  · rintro ⟨representative,same⟩
    constructor
    · have sourceZero := (q_eq_iff (sourceDifferential root visit recognition successor transition node) _ _).mp representative.property
      change sourceDifferential root visit recognition successor transition node
        (representative.val-sourceActionValue root visit recognition successor transition node sourceValue) = 0 at sourceZero
      unfold targetObservationResidual targetDifference
      rw [← same, ← map_sub]
      have square := LinearMap.congr_fun (residualMorphism root visit recognition successor transition node).commutes
        (representative.val-sourceActionValue root visit recognition successor transition node sourceValue)
      exact square.symm.trans sourceZero
    · exact (range_residual_exact root visit recognition successor transition node sourceValue targetValue).mpr ⟨representative.val,same⟩
  · rintro ⟨observationZero,rangeZero⟩
    obtain ⟨representative,same⟩ := (range_residual_exact root visit recognition successor transition node sourceValue targetValue).mp rangeZero
    refine ⟨⟨representative,?_⟩,same⟩
    apply (q_eq_iff (sourceDifferential root visit recognition successor transition node) _ _).mpr
    change sourceDifferential root visit recognition successor transition node
      (representative-sourceActionValue root visit recognition successor transition node sourceValue) = 0
    have square := LinearMap.congr_fun (residualMorphism root visit recognition successor transition node).commutes
      (representative-sourceActionValue root visit recognition successor transition node sourceValue)
    have sameDifference : RootLawDependentJointTransition.carrierMap transition.history
        (representative-sourceActionValue root visit recognition successor transition node sourceValue) =
      targetDifference root visit recognition successor transition node sourceValue targetValue := by rw [map_sub,same]; rfl
    exact square.trans ((congrArg (targetDifferential root visit recognition successor transition node) sameDifference).trans observationZero)
end SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
