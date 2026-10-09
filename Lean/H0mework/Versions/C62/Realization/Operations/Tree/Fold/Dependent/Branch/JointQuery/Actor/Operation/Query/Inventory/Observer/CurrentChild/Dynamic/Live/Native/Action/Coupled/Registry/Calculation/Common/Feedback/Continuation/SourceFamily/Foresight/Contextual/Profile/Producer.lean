import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Reader.Core
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Forecast.Dispatch
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Mixed.Source
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Source.Core
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Binding.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Producer
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation (Cursor cursorAt)
end O
namespace D
export Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch (face queryRaw written free_evaluation)
end D
namespace R
export Lower.SourceFamily.Foresight.Contextual.Reader.Core (raw result pairWritten material)
end R
namespace C
export Lower.SourceFamily.Foresight.Contextual (sourceEnvironment projection_environment low request)
end C
namespace I
export Lower.SourceFamily.Foresight.Installed (nativeState sourceHigh epochIndex OccurrenceIndex)
end I
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base)
end Q
export Lower.SourceFamily.Foresight.Contextual.Profile.SourceCore
 (physical pair carry read source source_fibre source_effect sigma nativeCursor profile nativeSource sourceTags profile_head actionBinding)
namespace B
export Lower.SourceFamily.Foresight.Contextual.Profile.BindingSource
 (source operator restriction scopeOperator scopeRestriction semantic renderer scope_source)
end B
variable {S : Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (seed:Lower.SourceFamily.Seed W X s n)
variable (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
variable (index:I.OccurrenceIndex n frame)
abbrev sourceTarget:=Lower.SourceFamily.Foresight.Contextual.Profile.BindingSource.Model binding n seed frame index
-- The actual query consumes the complete same-phase action-word source.
def jointSource:=B.source binding n seed frame index
abbrev rawOldSource:=Lower.SourceFamily.Foresight.Contextual.Profile.SourceCore.jointSource binding n seed frame index
abbrev bindingOperator:=B.operator binding n seed frame index
abbrev scopeOperator : SourceOperationLogic.Scope (jointSource binding n seed frame index)→ₗ[ℤ]
 SourceOperationLogic.Scope (jointSource binding n seed frame index):=B.scopeOperator binding n seed frame index
abbrev sourceRestriction:=B.restriction binding n seed frame index
abbrev scopeRestriction:=B.scopeRestriction binding n seed frame index
theorem joint_semantic (left right:Formal ℤ (PairValue (Lower.Value W n)) X s)
 (same:Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.SemanticEq left right):
 jointSource binding n seed frame index left=jointSource binding n seed frame index right :=
 B.semantic binding n seed frame index left right same
theorem joint_scope_semantic (left right:Formal ℤ (PairValue (Lower.Value W n)) X s)
 (same:Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.SemanticEq left right):
 SourceOperationLogic.q (jointSource binding n seed frame index) left=
 SourceOperationLogic.q (jointSource binding n seed frame index) right :=by
 apply (SourceOperationLogic.q_eq_iff _ _ _).mpr
 rw [LinearMap.mem_ker,map_sub]
 exact sub_eq_zero.mpr (joint_semantic binding n seed frame index left right same)
theorem joint_renderer (word:Formal ℤ (PairValue (Lower.Value W n)) X s):
 jointSource binding n seed frame index (Finsupp.single (Coefficients.expression word) 1)=
 jointSource binding n seed frame index word :=B.renderer binding n seed frame index word
theorem joint_scope_renderer (word:Formal ℤ (PairValue (Lower.Value W n)) X s):
 SourceOperationLogic.q (jointSource binding n seed frame index) (Finsupp.single (Coefficients.expression word) 1)=
 SourceOperationLogic.q (jointSource binding n seed frame index) word :=
 joint_scope_semantic binding n seed frame index _ _
  (Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.rendered_semantics word)
def face:=D.face seed frame index.2 (jointSource binding n seed frame index)
def disposition:=(face binding n seed frame index).settleWithResidual
def query:=D.queryRaw seed frame index.2 (R.raw binding n seed frame index)
 (jointSource binding n seed frame index) (disposition binding n seed frame index)
def queryReader {current:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied:SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) :=query binding n seed frame ⟨current,supplied⟩
def queryResult:=RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (Q.base frame).root.toAuthoritativeRoot (queryReader binding n seed frame) index.2
abbrev queryTrace:=(queryResult binding n seed frame index).2.1.2
def residual:=Expr.add (query binding n seed frame index).expression
 (Expr.linear (-AddMonoidHom.id _) (queryResult binding n seed frame index).2.1.1)
def beta:=relationMap (R:=ℤ) (query binding n seed frame index).environment (queryTrace binding n seed frame index).relationWords
def feedback:=(residual binding n seed frame index).subst (actionBinding binding n)
def expression:=Expr.add (residual binding n seed frame index) (feedback binding n seed frame index)
def raw:RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue (Lower.Value W n)) (Var:=X) (sort:=s):=
 ⟨C.sourceEnvironment binding n seed frame index,expression binding n seed frame index⟩
def reader {current:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied:SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)):=raw binding n seed frame ⟨current,supplied⟩
def result:=RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (Q.base frame).root.toAuthoritativeRoot (reader binding n seed frame) index.2
def queryWritten:=SourceHistoryCommon.seed
 (D.written seed frame index.2 (jointSource binding n seed frame index) (disposition binding n seed frame index))
 (SourceOperationPaidRelations.exposure (queryTrace binding n seed frame index))
def pairWritten:=SourceHistoryCommon.seed (R.pairWritten binding n seed frame index)
 (SourceHistoryCommon.seed (queryWritten binding n seed frame index)
  (SourceOperationPaidRelations.exposure (result binding n seed frame index).2.1.2))
def material:=(R.material binding n seed frame index,C.request binding n seed frame index,sourceTags n frame index,
 profile binding n frame index,nativeSource binding n seed frame,jointSource binding n seed frame index,
 face binding n seed frame index,disposition binding n seed frame index,query binding n seed frame index,
 queryResult binding n seed frame index,queryWritten binding n seed frame index,
 raw binding n seed frame index,result binding n seed frame index)
theorem query_environment:(query binding n seed frame index).environment=C.sourceEnvironment binding n seed frame index :=
 (Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch.query_environment _ _ _ _ _ _).trans
 ((Lower.SourceFamily.Foresight.Contextual.Reader.Core.raw_environment binding n seed frame index).trans
  (C.projection_environment binding n seed frame index).symm)
theorem residual_old:(residual binding n seed frame index).eval (C.sourceEnvironment binding n seed frame index)=0 :=by
 have sameEnv:=query_environment binding n seed frame index
 exact (congrArg (fun env=>(residual binding n seed frame index).eval env) sameEnv.symm).trans
  (Lower.SourceFamily.Foresight.Contextual.Mixed.residual_old _ (queryTrace binding n seed frame index))
theorem residual_fee:2≤remaining (residual binding n seed frame index) :=by
 change 2≤remaining (query binding n seed frame index).expression+
  (remaining (queryResult binding n seed frame index).2.1.1+1)+1
 omega
theorem source_fee:3≤remaining (expression binding n seed frame index) :=by
 change 3≤remaining (residual binding n seed frame index)+remaining (feedback binding n seed frame index)+1
 have paid:=residual_fee binding n seed frame index
 omega
theorem result_value:(result binding n seed frame index).2.2.1=
 (raw binding n seed frame index).expression.eval (raw binding n seed frame index).environment :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _
def actedIncrement := Lower.SourceFamily.Foresight.Contextual.Mixed.actedIncrement
 (query binding n seed frame index).environment (actionBinding binding n)
theorem feedback_generated :
 (feedback binding n seed frame index).eval (query binding n seed frame index).environment=
 effectEvaluator (R:=ℤ) (query binding n seed frame index).environment
  (actedIncrement binding n seed frame index) (beta binding n seed frame index) :=
 Lower.SourceFamily.Foresight.Contextual.Mixed.feedback_value _
  (queryTrace binding n seed frame index) (actionBinding binding n)
theorem result_effect : (result binding n seed frame index).2.2.1=
 effectEvaluator (R:=ℤ) (query binding n seed frame index).environment
  (actedIncrement binding n seed frame index) (beta binding n seed frame index) :=by
 apply (result_value binding n seed frame index).trans
 change (residual binding n seed frame index).eval (C.sourceEnvironment binding n seed frame index)+
  (feedback binding n seed frame index).eval (C.sourceEnvironment binding n seed frame index)=_
 have same: C.sourceEnvironment binding n seed frame index=(query binding n seed frame index).environment :=
  (query_environment binding n seed frame index).symm
 rw [same]
 exact (congrArg₂ (·+·) (Lower.SourceFamily.Foresight.Contextual.Mixed.residual_old _
  (queryTrace binding n seed frame index)) (feedback_generated binding n seed frame index)).trans (zero_add _)
theorem actual_residual :
 (residualEquivRange (evaluation (R:=ℤ) ((query binding n seed frame index).environment+
   actedIncrement binding n seed frame index))
  (canonicalResidual (evaluation (R:=ℤ) ((query binding n seed frame index).environment+
    actedIncrement binding n seed frame index)) (beta binding n seed frame index))).val=
 (result binding n seed frame index).2.2.1 :=
 ((queryTrace binding n seed frame index).updated_residual (R:=ℤ) (actedIncrement binding n seed frame index)).trans
  (result_effect binding n seed frame index).symm
theorem complete_fee:(result binding n seed frame index).2.1.2.length=remaining (expression binding n seed frame index):=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem old_inventory (event) (present:event∈(R.pairWritten binding n seed frame index).trace):
 event∈(pairWritten binding n seed frame index).trace :=(SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem new_query_paid (event) (present:event∈(SourceOperationPaidRelations.exposure (queryTrace binding n seed frame index)).trace):
 event∈(pairWritten binding n seed frame index).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event ((SourceHistoryCommon.parallel_left _ _ _).1 event
  ((SourceHistoryCommon.parallel_right _ _ _).1 event present))
theorem new_reader_paid (event) (present:event∈(SourceOperationPaidRelations.exposure (result binding n seed frame index).2.1.2).trace):
 event∈(pairWritten binding n seed frame index).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event ((SourceHistoryCommon.parallel_right _ _ _).1 event present)

private theorem trace_residual_semantic {S:Type u} {U X:S→Type u} [∀t,AddCommGroup (U t)] {s:S}
 {old:Env U X} {before after:Expr U X s} (trace:Trace old before after):
 Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.SemanticEq
  (Finsupp.single (Lower.SourceFamily.Foresight.Contextual.Mixed.residualExpression before after) 1)
  (relationMap (R:=ℤ) old (trace.relationWords (R:=ℤ))) :=by
 intro env
 rw [trace.relation_boundary,map_sub]
 simp only [evaluation,Finsupp.linearCombination_single,one_smul,
  Lower.SourceFamily.Foresight.Contextual.Mixed.residualExpression,Expr.eval,
  AddMonoidHom.neg_apply,AddMonoidHom.id_apply,sub_eq_add_neg]
private theorem trace_raw_semantic {S:Type u} {U X:S→Type u} [∀t,AddCommGroup (U t)] {s:S}
 {old:Env U X} {before after:Expr U X s} (trace:Trace old before after) (sigma:∀t,X t→Expr U X t):
 Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.SemanticEq
  (Finsupp.single (Expr.add (Lower.SourceFamily.Foresight.Contextual.Mixed.residualExpression before after)
   ((Lower.SourceFamily.Foresight.Contextual.Mixed.residualExpression before after).subst sigma)) 1)
  (relationMap (R:=ℤ) old (trace.relationWords (R:=ℤ))+
   substitution (R:=ℤ) sigma (relationMap (R:=ℤ) old (trace.relationWords (R:=ℤ)))) :=by
 intro env
 have left:=trace_residual_semantic trace env
 have right:=trace_residual_semantic trace (SourceSubstitution.sourceEnvironment sigma env)
 simp only [evaluation,Finsupp.linearCombination_single,one_smul] at left right
 simp only [evaluation,Finsupp.linearCombination_single,one_smul,Expr.eval]
 rw [map_add,Expr.eval_subst]
 exact congrArg₂ (·+·) left (right.trans
  (LinearMap.congr_fun (evaluation_substitution (R:=ℤ) sigma env)
   (relationMap (R:=ℤ) old (trace.relationWords (R:=ℤ)))).symm)

theorem raw_scope:
 SourceOperationLogic.q (jointSource binding n seed frame index)
  (Finsupp.single (raw binding n seed frame index).expression 1)=
 SourceOperationLogic.q (jointSource binding n seed frame index) (beta binding n seed frame index)+
 scopeOperator binding n seed frame index
  (SourceOperationLogic.q (jointSource binding n seed frame index) (beta binding n seed frame index)) :=by
 have semantic:=trace_raw_semantic (queryTrace binding n seed frame index) (actionBinding binding n)
 apply (joint_scope_semantic binding n seed frame index _ _ semantic).trans
 apply (map_add _ _ _).trans
 exact congrArg (fun value=>SourceOperationLogic.q (jointSource binding n seed frame index)
  (beta binding n seed frame index)+value) (B.scope_source binding n seed frame index _).symm
end Lower.SourceFamily.Foresight.Contextual.Profile.Producer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
