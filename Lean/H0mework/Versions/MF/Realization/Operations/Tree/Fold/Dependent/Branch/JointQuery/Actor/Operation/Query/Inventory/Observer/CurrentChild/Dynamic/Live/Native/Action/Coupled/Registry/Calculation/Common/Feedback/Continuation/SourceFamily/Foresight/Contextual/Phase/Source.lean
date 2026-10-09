import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Mixed.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
namespace Lower.SourceFamily.Foresight.Contextual.Phase
namespace M
export Lower.SourceFamily.Foresight.Contextual.Mixed (boundary residualExpression residual_old)
end M
section Small
variable {S : Type u} {U X : S → Type u} [∀ t, AddCommGroup (U t)] {s : S}
theorem single_fee (argument : Expr U X s) :
 remaining (Coefficients.expression (Finsupp.single argument (1:ℤ)))=remaining argument+2 := by
 classical
 simp [Coefficients.expression,Coefficients.sourceItems,Coefficients.terms,Coefficients.integerExpansion,
  Coefficients.naturalExpansion,remaining]

variable (old : Env U X) {before after : Expr U X s} (source : Trace old before after)
variable (decoder increment : Env U X)
def beta := M.boundary old source
abbrev residual := M.residualExpression before after

theorem phase_value : (residual (before:=before) (after:=after)).eval decoder=
 effectEvaluator (R:=ℤ) old (decoder-old) (beta old source) := by
 have environment : old+(decoder-old)=decoder :=add_sub_cancel _ _
 have generated := (residual (before:=before) (after:=after)).eval_update old (decoder-old)
 have origin := M.residual_old old source
 have native : (residual (before:=before) (after:=after)).eval decoder=
  (residual (before:=before) (after:=after)).effect old (decoder-old) :=
  (congrArg (residual (before:=before) (after:=after)).eval environment).symm.trans
   (generated.trans ((congrArg₂ (·+·) origin rfl).trans (zero_add _)))
 apply native.trans
 rw [beta,M.boundary,source.relation_boundary,map_sub]
 simp only [effectEvaluator,Finsupp.linearCombination_single,one_smul]
 simp only [M.residualExpression,Expr.effect,AddMonoidHom.neg_apply,AddMonoidHom.id_apply,sub_eq_add_neg]

theorem action_value : (residual (before:=before) (after:=after)).effect decoder increment=
 effectEvaluator (R:=ℤ) decoder increment (beta old source) := by
 rw [beta,M.boundary,source.relation_boundary,map_sub]
 simp only [effectEvaluator,Finsupp.linearCombination_single,one_smul]
 simp only [M.residualExpression,Expr.effect,AddMonoidHom.neg_apply,AddMonoidHom.id_apply,sub_eq_add_neg]

theorem single_pair : updateInventory (R:=ℤ) decoder increment
 (Finsupp.single (residual (before:=before) (after:=after)) 1)=
 (effectEvaluator (R:=ℤ) old (decoder-old) (beta old source),
  effectEvaluator (R:=ℤ) decoder increment (beta old source)) := by
 change (evaluation (R:=ℤ) decoder (Finsupp.single (residual (before:=before) (after:=after)) 1),
  effectEvaluator (R:=ℤ) decoder increment (Finsupp.single (residual (before:=before) (after:=after)) 1))=_
 simp only [evaluation,effectEvaluator,Finsupp.linearCombination_single,one_smul]
 exact Prod.ext (phase_value old source decoder) (action_value old source decoder increment)
end Small
end Lower.SourceFamily.Foresight.Contextual.Phase
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
