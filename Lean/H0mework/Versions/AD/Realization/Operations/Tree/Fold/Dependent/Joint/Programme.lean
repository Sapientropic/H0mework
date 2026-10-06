import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.Transport
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect CofinalHistoryTransition
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (node : GeneratedNodeAt (recognition.generateStepAt visit) successor transition.history)
inductive Slot : Type u | source | target | measured
abbrev Value : Slot.{u} → Type u
  | .source => C root visit recognition
  | .target => D root visit recognition successor
  | .measured => H
abbrev Var : Slot.{u} → Type u := fun _ => PUnit.{u+1}
instance : (sort : Slot.{u}) → AddCommGroup (Value root visit recognition successor (H:=H) sort)
  | .source => inferInstance
  | .target => inferInstance
  | .measured => inferInstance

def environment (value : C root visit recognition) : Env (Value root visit recognition successor (H:=H)) Var :=
  fun sort _ => match sort with | .source => value | .target => 0 | .measured => 0

def nextExpression : Expr (Value root visit recognition successor (H:=H)) Var .target :=
  .linear (s:=Slot.source) (carrierMap transition.history).toAddMonoidHom (.var PUnit.unit)
def actionAfter : Expr (Value root visit recognition successor (H:=H)) Var .target :=
  .linear (targetRaw root visit recognition successor transition node).sourceAction.carrierAction.toAddMonoidHom
    (nextExpression root visit recognition successor transition)
def actionBefore : Expr (Value root visit recognition successor (H:=H)) Var .target :=
  .linear (s:=Slot.source) (carrierMap transition.history).toAddMonoidHom
    (.linear (s:=Slot.source) (t:=Slot.source) (sourceRaw root visit recognition successor transition node).sourceAction.carrierAction.toAddMonoidHom (.var PUnit.unit))
def sourceMeasured : Expr (Value root visit recognition successor (H:=H)) Var .measured :=
  .linear (s:=Slot.source) (sourceRaw root visit recognition successor transition node).measurement.toAddMonoidHom (.var PUnit.unit)
def targetMeasured : Expr (Value root visit recognition successor (H:=H)) Var .measured :=
  .linear (s:=Slot.target) (targetRaw root visit recognition successor transition node).measurement.toAddMonoidHom
    (nextExpression root visit recognition successor transition)
def sourceCoupling : Expr (Value root visit recognition successor (H:=H)) Var .measured :=
  .add (.linear (sourceRaw root visit recognition successor transition node).hilbertEvolution.toLinearMap.toAddMonoidHom
      (sourceMeasured root visit recognition successor transition node))
    (.linear (-(sourceRaw root visit recognition successor transition node).measurement.toAddMonoidHom)
      (.linear (s:=Slot.source) (t:=Slot.source) (sourceRaw root visit recognition successor transition node).sourceAction.carrierAction.toAddMonoidHom (.var PUnit.unit)))
def targetCoupling : Expr (Value root visit recognition successor (H:=H)) Var .measured :=
  .add (.linear (targetRaw root visit recognition successor transition node).hilbertEvolution.toLinearMap.toAddMonoidHom
      (targetMeasured root visit recognition successor transition node))
    (.linear (-(targetRaw root visit recognition successor transition node).measurement.toAddMonoidHom)
      (actionAfter root visit recognition successor transition node))
theorem action_square (value : C root visit recognition) :
    (actionAfter root visit recognition successor transition node).eval (environment root visit recognition successor value) =
      (actionBefore root visit recognition successor transition node).eval (environment root visit recognition successor value) :=
  (node.joint.actionNatural value).symm

theorem coupling_square (value : C root visit recognition) :
    (targetCoupling root visit recognition successor transition node).eval (environment root visit recognition successor value) =
      (sourceCoupling root visit recognition successor transition node).eval (environment root visit recognition successor value) := by
  simpa only [targetCoupling, sourceCoupling, targetMeasured, sourceMeasured, actionAfter,
    nextExpression, environment, Expr.eval, AddMonoidHom.neg_apply, sub_eq_add_neg, LinearMap.toAddMonoidHom_coe, LinearIsometry.coe_toLinearMap] using
      vector_transport root visit recognition successor transition node value

def sourceCouplingTrace (value : C root visit recognition) :=
  execution (environment root visit recognition successor value) (sourceCoupling root visit recognition successor transition node)
def targetCouplingTrace (value : C root visit recognition) :=
  execution (environment root visit recognition successor value) (targetCoupling root visit recognition successor transition node)

theorem source_cost (value : C root visit recognition) : (sourceCouplingTrace root visit recognition successor transition node value).length = 7 :=
  (execution_length _ _).trans (by rfl)
theorem target_cost (value : C root visit recognition) : (targetCouplingTrace root visit recognition successor transition node value).length = 9 :=
  (execution_length _ _).trans (by rfl)
end SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
