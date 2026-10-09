import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Source
import H0mework.Realization.Operations.Execution.Cochain.Inventory
import H0mework.Realization.Operations.Execution.Substitution.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Mixed
namespace CI
export SaturationMonoid.SourceOperationExecution.Cochain.Inventory
 (Index term terms query trace written coordinate updatedIndex oldIndex mixedIndex mixed_injective complete_equation charge)
end CI
section Small
variable {S : Type u} {U X : S → Type u} [∀ t, AddCommGroup (U t)] {s : S}
def splitHom (t : S) (part : UpdatePart) : PairValue U t →+ PairValue U t :=
 match part with
 | .old => (AddMonoidHom.fst (U t) (U t)).prod 0
 | .increment => (AddMonoidHom.snd (U t) (U t)).prod 0
def splitBinding (t : S) (name : ChangedVar X t) : Expr (PairValue U) X t :=
 .linear (splitHom t name.2) (.var name.1)

theorem split_environment (old increment : Env U X) :
 (fun t name => (splitBinding (U:=U) (X:=X) t name).eval (pairEnvironment old increment))=
 pairEnvironment (mixedEnvironment old increment) 0 := by
 funext t name
 rcases name with ⟨name,part⟩
 cases part <;> rfl

def nativeTerm (term : Expr U (ChangedVar X) s) := (liftExpr term).subst (splitBinding (U:=U) (X:=X))
theorem native_term_value (term : Expr U (ChangedVar X) s) (old increment : Env U X) :
 (nativeTerm term).eval (pairEnvironment old increment)=(term.eval (mixedEnvironment old increment),0) := by
 unfold nativeTerm
 rw [Expr.eval_subst,split_environment,eval_liftExpr,Expr.effect_zero]

def residualExpression (before after : Expr U X s) :=
 Expr.add before (Expr.linear (-AddMonoidHom.id _) after)
variable (old : Env U X) {before after : Expr U X s} (source : Trace old before after)
def boundary := relationMap (R:=ℤ) old (source.relationWords (R:=ℤ))
include source in
theorem residual_old : (residualExpression before after).eval old=0 := by
 change before.eval old + -(after.eval old)=0
 rw [source.sound,add_neg_cancel]

theorem residual_effect (increment : Env U X) :
 (residualExpression before after).effect old increment=effectEvaluator (R:=ℤ) old increment (boundary old source) := by
 rw [boundary,source.relation_boundary,map_sub]
 simp only [effectEvaluator,Finsupp.linearCombination_single,one_smul]
 simp only [residualExpression,Expr.effect,AddMonoidHom.neg_apply,AddMonoidHom.id_apply,sub_eq_add_neg]

variable (binding : ∀ t,X t → Expr U X t)
def actedIncrement := SourceSubstitution.sourceEnvironment binding old-old

theorem feedback_value : ((residualExpression before after).subst binding).eval old =
 effectEvaluator (R:=ℤ) old (actedIncrement old binding) (boundary old source) := by
 rw [Expr.eval_subst]
 change (residualExpression before after).eval (SourceSubstitution.sourceEnvironment binding old)=_
 have environment : SourceSubstitution.sourceEnvironment binding old=old+actedIncrement old binding :=
  (add_sub_cancel old (SourceSubstitution.sourceEnvironment binding old)).symm
 rw [environment,Expr.eval_update,residual_old old source,zero_add]
 exact residual_effect old source _

include source in
theorem ordered_feedback :
 ((residualExpression before after).mixedTerms.map
   (fun term => (nativeTerm term).eval (pairEnvironment old (actedIncrement old binding)) |>.1)).sum =
 ((residualExpression before after).subst binding).eval old := by
 have generated := Expr.mixedTerms_sum (residualExpression before after) old (actedIncrement old binding)
 simp only [native_term_value] at ⊢
 exact generated.trans ((residual_effect old source _).trans (feedback_value old source binding).symm)

theorem actual_updated_term (expression : Expr U X s) (increment : Env U X) :
 (nativeTerm (CI.term expression (CI.updatedIndex expression))).eval (pairEnvironment old increment)=
 (expression.eval (old+increment),0) :=
 (native_term_value _ _ _).trans (congrArg (fun value => (value,0)) (SourceOperationScalarCochain.eval_updated expression old increment))
end Small
end Lower.SourceFamily.Foresight.Contextual.Mixed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
