import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.TargetDifference
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (node : GeneratedNodeAt (recognition.generateStepAt visit) successor transition.history)
abbrev SourceWord := (StepSourceHistory (recognition.generateStepAt visit)).generatorClosure
abbrev TargetWord := (StepTargetHistory (recognition.generateStepAt visit) successor).generatorClosure
abbrev ImageResidual := SourceGeneratedSubfaceFactorization.ResidualCarrier (RootLawDependentJointTransition.carrierMap transition.history)
inductive TargetSlot : Type u | original (slot : Slot.{u}) | image | full
abbrev TargetValue : TargetSlot.{u} → Type u
  | .original slot => Value root visit recognition successor (H:=H) slot
  | .image => ImageResidual root visit recognition successor transition
  | .full => D root visit recognition successor × H × ImageResidual root visit recognition successor transition
abbrev TargetVar : TargetSlot.{u} → Type u
  | .original slot => Var slot
  | .image => PEmpty.{u+1}
  | .full => PEmpty.{u+1}
instance : (slot : TargetSlot.{u}) → AddCommGroup (TargetValue root visit recognition successor transition (H:=H) slot)
  | .original _slot => inferInstance
  | .image => inferInstance
  | .full => inferInstance

def targetEnvironment (sourceWord : SourceWord root visit recognition) (targetWord : TargetWord root visit recognition successor) :
    Env (TargetValue root visit recognition successor transition (H:=H)) TargetVar :=
  fun slot => match slot with
  | .original .source => fun _ => (StepSourceHistory (recognition.generateStepAt visit)).completionProjection sourceWord
  | .original .target => fun _ => (StepTargetHistory (recognition.generateStepAt visit) successor).completionProjection targetWord
  | .original .measured => fun _ => 0
  | .image => PEmpty.elim
  | .full => PEmpty.elim

def differenceExpression : Expr (TargetValue root visit recognition successor transition (H:=H)) TargetVar (.original .target) :=
  .add (.linear (s:=TargetSlot.original Slot.target) (targetRaw root visit recognition successor transition node).sourceAction.carrierAction.toAddMonoidHom (.var PUnit.unit))
    (.linear (s:=TargetSlot.original Slot.source) (-(RootLawDependentJointTransition.carrierMap transition.history).toAddMonoidHom)
      (.linear (s:=TargetSlot.original Slot.source) (t:=TargetSlot.original Slot.source)
        (sourceRaw root visit recognition successor transition node).sourceAction.carrierAction.toAddMonoidHom (.var PUnit.unit)))

def observationExpression : Expr (TargetValue root visit recognition successor transition (H:=H)) TargetVar (.original .measured) :=
  .linear (s:=TargetSlot.original Slot.target) (targetDifferential root visit recognition successor transition node).toAddMonoidHom
    (differenceExpression root visit recognition successor transition node)
def imageExpression : Expr (TargetValue root visit recognition successor transition (H:=H)) TargetVar .image :=
  .linear (s:=TargetSlot.original Slot.target) (Submodule.mkQ (LinearMap.range (RootLawDependentJointTransition.carrierMap transition.history))).toAddMonoidHom
    (differenceExpression root visit recognition successor transition node)

def fullTargetProgramme : Expr (TargetValue root visit recognition successor transition (H:=H)) TargetVar .full :=
  .add (.add
    (.linear (s:=TargetSlot.original Slot.target) ((AddMonoidHom.id (D root visit recognition successor)).prod (0 : D root visit recognition successor →+ H × ImageResidual root visit recognition successor transition))
      (differenceExpression root visit recognition successor transition node))
    (.linear (s:=TargetSlot.original Slot.measured) ((0 : H →+ D root visit recognition successor).prod ((AddMonoidHom.id H).prod 0))
      (observationExpression root visit recognition successor transition node)))
    (.linear (s:=TargetSlot.image) ((0 : ImageResidual root visit recognition successor transition →+ D root visit recognition successor).prod
      ((0 : ImageResidual root visit recognition successor transition →+ H).prod (AddMonoidHom.id _)))
      (imageExpression root visit recognition successor transition node))
end SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
