import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Reader.Source
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Affine.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.Scope
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly (beforeFrame beforeIndex beforeSource nextPacket)
end A
namespace T
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine (beforeq afterq actor rebase constant writerValue writerBoundary writer_affine writer_rebase)
end T
private theorem expression_semantic {S:Type u} {U X:S→Type u} [∀t,AddCommGroup (U t)] {s:S}
 {N:WorldRelationNetwork.{u}} {V:Vocabulary.{u}}
 {lower:SourceNativeLedgerRootClosure N V} {current:V.Current}
 {occ:lower.source.source.toRootSource.actual.OccurrenceAt current}
 (mat:RootGeneratedDebtActivationJointSource.Native.ResidualRequest.MaterialAt (Value:=U) (Var:=X) (sort:=s) occ):
 Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.SemanticEq
  (Finsupp.single (Req.expression mat) 1)
  (relationMap (R:=ℤ) mat.environment (Req.relations (R:=ℤ) mat)):=by
 intro env
 rw [RootGeneratedDebtActivationJointSource.Native.ResidualRequest.relation_boundary]
 rw [map_sub]
 simp only [Req.expression,evaluation,Finsupp.linearCombination_single,one_smul,Expr.eval,
  AddMonoidHom.neg_apply,AddMonoidHom.id_apply,sub_eq_add_neg]
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat)
variable (data:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
variable (native:data.1.depth=0)

def requestWord:=Finsupp.single (expression binding n data) (1:ℤ)

theorem before_request_scope:T.beforeq binding n data (requestWord binding n data)=
 T.beforeq binding n data (beta binding n data):=
 Lower.SourceFamily.Foresight.Contextual.Profile.Producer.joint_scope_semantic
  binding n data.2 (A.beforeFrame n data) (A.beforeIndex n data) _ _
  (expression_semantic (material binding n data))

include native in
theorem generated_actor_equation:
 T.afterq binding n data (T.writerBoundary binding n data (requestWord binding n data))=
 T.actor binding n data native (T.beforeq binding n data (beta binding n data))-
 T.constant binding n data (T.writerValue binding n data (requestWord binding n data)):=
 (T.writer_affine binding n data native (requestWord binding n data)).trans
 (congrArg (fun coordinate=>T.actor binding n data native coordinate-
  T.constant binding n data (T.writerValue binding n data (requestWord binding n data)))
  (before_request_scope binding n data))

include native in
theorem generated_rebase_equation:
 T.afterq binding n data (T.writerBoundary binding n data (requestWord binding n data))=
 T.rebase binding n data (T.actor binding n data native (T.beforeq binding n data (beta binding n data))):=
 (T.writer_rebase binding n data native (requestWord binding n data)).trans
 (congrArg (fun coordinate=>T.rebase binding n data (T.actor binding n data native coordinate))
  (before_request_scope binding n data))
end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.Scope
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
