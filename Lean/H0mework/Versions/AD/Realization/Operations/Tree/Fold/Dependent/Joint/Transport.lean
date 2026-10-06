import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.Action
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open CofinalHistoryTransition
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (node : GeneratedNodeAt (recognition.generateStepAt visit) successor transition.history)
abbrev sourceRaw := stepSourceExposureAt (recognition.generateStepAt visit) node.pair.1
abbrev targetRaw := stepTargetExposureAt (recognition.generateStepAt visit) successor node.pair.2
abbrev sourceResidual (value : (StepSourceHistory (recognition.generateStepAt visit)).CompletionCarrier) : H :=
  (sourceRaw root visit recognition successor transition node).hilbertEvolution
    ((sourceRaw root visit recognition successor transition node).measurement value) -
  (sourceRaw root visit recognition successor transition node).measurement
    ((sourceRaw root visit recognition successor transition node).sourceAction.carrierAction value)
abbrev targetResidual (value : (StepTargetHistory (recognition.generateStepAt visit) successor).CompletionCarrier) : H :=
  (targetRaw root visit recognition successor transition node).hilbertEvolution
    ((targetRaw root visit recognition successor transition node).measurement value) -
  (targetRaw root visit recognition successor transition node).measurement
    ((targetRaw root visit recognition successor transition node).sourceAction.carrierAction value)
theorem vector_transport (value : (StepSourceHistory (recognition.generateStepAt visit)).CompletionCarrier) :
    targetResidual root visit recognition successor transition node (carrierMap transition.history value) =
      sourceResidual root visit recognition successor transition node value := by
  unfold targetResidual sourceResidual
  rw [← node.joint.measurementNatural value, ← node.joint.actionNatural value,
    ← node.joint.measurementNatural ((sourceRaw root visit recognition successor transition node).sourceAction.carrierAction value),
    ← node.joint.evolutionNatural]

theorem vector_zero_iff (value : (StepSourceHistory (recognition.generateStepAt visit)).CompletionCarrier) :
    targetResidual root visit recognition successor transition node (carrierMap transition.history value) = 0 ↔
      sourceResidual root visit recognition successor transition node value = 0 := by
  rw [vector_transport]

theorem vector_norm (value : (StepSourceHistory (recognition.generateStepAt visit)).CompletionCarrier) :
    ‖targetResidual root visit recognition successor transition node (carrierMap transition.history value)‖ =
      ‖sourceResidual root visit recognition successor transition node value‖ :=
  congrArg norm (vector_transport root visit recognition successor transition node value)

abbrev C := (StepSourceHistory (recognition.generateStepAt visit)).CompletionCarrier
abbrev D := (StepTargetHistory (recognition.generateStepAt visit) successor).CompletionCarrier
abbrev Update := C root visit recognition × D root visit recognition successor × D root visit recognition successor × H × H

def update (value : C root visit recognition) : Update root visit recognition successor :=
  (value, carrierMap transition.history value,
    (targetRaw root visit recognition successor transition node).sourceAction.carrierAction (carrierMap transition.history value),
    sourceResidual root visit recognition successor transition node value,
    targetResidual root visit recognition successor transition node (carrierMap transition.history value))

theorem update_action (value : C root visit recognition) :
    (update root visit recognition successor transition node value).2.2.1 =
      carrierMap transition.history ((sourceRaw root visit recognition successor transition node).sourceAction.carrierAction value) :=
  (node.joint.actionNatural value).symm

theorem update_equation (value : C root visit recognition) :
    (update root visit recognition successor transition node value).2.2.2.2 =
      (update root visit recognition successor transition node value).2.2.2.1 :=
  vector_transport root visit recognition successor transition node value

abbrev UpdateEquations (value : C root visit recognition) :=
  (update root visit recognition successor transition node value).2.2.1 =
    carrierMap transition.history ((sourceRaw root visit recognition successor transition node).sourceAction.carrierAction value) ∧
  (update root visit recognition successor transition node value).2.2.2.2 =
    (update root visit recognition successor transition node value).2.2.2.1

structure GeneratedUpdate (value : C root visit recognition) where
  inventory : Update root visit recognition successor
  inventory_exact : inventory = update root visit recognition successor transition node value
  action_equation : inventory.2.2.1 = carrierMap transition.history
    ((sourceRaw root visit recognition successor transition node).sourceAction.carrierAction value)
  residual_equation : inventory.2.2.2.2 = inventory.2.2.2.1

def generateUpdate (value : C root visit recognition) : GeneratedUpdate root visit recognition successor transition node value where
  inventory := update root visit recognition successor transition node value
  inventory_exact := rfl
  action_equation := update_action root visit recognition successor transition node value
  residual_equation := update_equation root visit recognition successor transition node value
end SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
