import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.FourFace.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Source
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Factory
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Payment
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly (nextPacket beforeFrame afterFrame afterIndex afterState BeforeTarget AfterTarget beforeJointModule afterJointModule afterSource)
end A
namespace Af
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine (AfterScope afterq constant rawWord writerValue writerBoundary writer_affine writer_rebase head_source raw_scope)
end Af
namespace Wr
export Lower.SourceFamily.Foresight.Contextual.Written (receiver nextSeed stock)
end Wr
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query datum baseRoot resultAt actualOccurrence query_generated)
end Q
namespace Receipt
export SourceGeneratedInquiryReceiptAction
 (actualMaterial registered occurrence current afterEnvironment generatedAction actionReader actionResultAt actual_raw)
end Receipt
namespace Req
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression input updated_value residual_value)
end Req
namespace Pay
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment (debtCurrent debt_current_actual payment no_refill)
end Pay
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (sigma nativeCursor source_fibre jointSource joint_semantic)
end P
namespace R
export Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering (SemanticEq semantic_advance)
end R
namespace F
export Lower.SourceFamily.Foresight (source_fibre sourceMap)
end F
namespace ResultProjection
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)
variable {S : Type u} {U Y : S → Type u} [∀t,AddCommGroup (U t)] {s : S}
variable (reader : {current : V.Current} → old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current →
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=U) (Var:=Y) (sort:=s))
variable {current : V.Current}
variable (occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current)
theorem endpoint :
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt old reader occurrence).2.1.1=
 Expr.const (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt old reader occurrence).2.2.1 :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression old current (fun _=>reader occurrence)
end ResultProjection
namespace CalleeProjection
variable {S : Type u} {U Y : S → Type u} [∀t,AddCommGroup (U t)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=U) (Var:=Y) (sort:=s))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=U) (PhysicalVar:=Y) (sort:=s))
theorem endpoint : (Receipt.actualMaterial frame configuration).state.1=Expr.const
 (Receipt.actionResultAt frame configuration (Receipt.occurrence frame configuration)).2.2.1 :=
 ResultProjection.endpoint (Q.baseRoot frame configuration).toAuthoritativeRoot
 (fun {_current} supplied => Receipt.actionReader frame configuration supplied)
 (Receipt.occurrence frame configuration)
variable (scalar : RootedAccountedUnfolding (PresentedRelationEventAt
 (Expr (PairValue U) configuration.LowVar s)))
variable (pair : RootedAccountedUnfolding (PresentedRelationEventAt
 (Expr (PairValue (PairValue U)) configuration.LowVar s)))
theorem owner :
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap.initial
  frame configuration scalar pair).registered.input.owner=
 (Receipt.actualMaterial frame configuration).owner := rfl
end CalleeProjection
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (packet:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
local instance beforeModule:Module ℤ (A.BeforeTarget binding n packet):=A.beforeJointModule binding n packet
local instance afterModule:Module ℤ (A.AfterTarget binding n packet):=A.afterJointModule binding n packet
abbrev cfg:=Lower.SourceFamily.cfg (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) binding) n packet.2
abbrev material:=Receipt.actualMaterial packet.1 (cfg binding n packet)
abbrev readerValue:=(Receipt.actionResultAt packet.1 (cfg binding n packet)
  (Receipt.occurrence packet.1 (cfg binding n packet))).2.2.1
abbrev activeExpression:=(Wr.receiver binding n packet).registered.input.expression
abbrev activeEnv:=(Wr.receiver binding n packet).registered.input.environment
def activeWord:=Finsupp.single (activeExpression binding n packet) (1:ℤ)
def actionWord:=Finsupp.single
  (Receipt.actionReader packet.1 (cfg binding n packet)
    (Receipt.occurrence packet.1 (cfg binding n packet))).expression (1:ℤ)
def endpointCorrection : PairValue (Lower.Value W (n+1)) s :=
 Af.writerValue binding n packet (actionWord binding n packet)-
 (show PairValue (Lower.Value W (n+1)) s from (readerValue binding n packet,(0 : PairValue (Lower.Value W n) s)))

theorem input_expression:activeExpression binding n packet=Req.expression (material binding n packet):=rfl
theorem input_environment:activeEnv binding n packet=Receipt.afterEnvironment packet.1 (cfg binding n packet):=
 SourceGeneratedInquiryReceiptAction.actual_updated_environment packet.1 (cfg binding n packet)

theorem input_owner : type_of% (CalleeProjection.owner packet.1 (cfg binding n packet)
 (Lower.SourceFamily.scalar (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) binding) n packet)
 (Lower.SourceFamily.pair (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) binding) n packet)) :=
 CalleeProjection.owner packet.1 (cfg binding n packet)
 (Lower.SourceFamily.scalar (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) binding) n packet)
 (Lower.SourceFamily.pair (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) binding) n packet)
theorem raw_source:(material binding n packet).raw=
 (Receipt.actionReader packet.1 (cfg binding n packet)
  (Receipt.occurrence packet.1 (cfg binding n packet))).expression :=
 Receipt.actual_raw _ _
theorem reader_endpoint : type_of% (CalleeProjection.endpoint packet.1 (cfg binding n packet)) :=
 CalleeProjection.endpoint packet.1 (cfg binding n packet)
private theorem residual_syntax:
 R.SemanticEq (liftMap (activeWord binding n packet))
  (liftMap (actionWord binding n packet)-Finsupp.single (.const (readerValue binding n packet,0)) 1):=by
 intro env
 rw [map_sub]
 change evaluation (R:=ℤ) env (liftMap (Finsupp.single (activeExpression binding n packet) 1))=
  evaluation (R:=ℤ) env (liftMap (actionWord binding n packet))-
   evaluation (R:=ℤ) env (Finsupp.single (.const (readerValue binding n packet,0)) 1)
 have input:=input_expression binding n packet
 have endpoint:=reader_endpoint binding n packet
 simp only [actionWord,
  liftMap,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,evaluation,Finsupp.linearCombination_single,one_smul]
 rw [input]
 unfold Req.expression
 rw [endpoint,raw_source]
 simp only [liftExpr,Expr.eval,pairLinear,AddMonoidHom.coe_prodMap,Prod.map_apply,
  AddMonoidHom.neg_apply,AddMonoidHom.id_apply,neg_zero,sub_eq_add_neg,Prod.neg_mk]
private theorem scope_semantic (left right:Formal ℤ (PairValue (Lower.Value W (n+1))) X s) (same:R.SemanticEq left right):
 Af.afterq binding n packet left=Af.afterq binding n packet right:=by
 apply (SourceOperationLogic.q_eq_iff _ _ _).mpr
 rw [LinearMap.mem_ker,map_sub]
 apply sub_eq_zero.mpr
 exact P.joint_semantic binding (n+1) (A.nextPacket binding n packet).2
  (A.afterFrame binding n packet) (A.afterIndex binding n packet) left right same
variable (native:packet.1.depth=0)
include native in
theorem actual_claim_equation:
 Af.afterq binding n packet (liftMap (activeWord binding n packet))=
 Af.afterq binding n packet (Af.writerBoundary binding n packet (actionWord binding n packet))+
  Af.constant binding n packet (endpointCorrection binding n packet):=by
 let endpointValue:PairValue (Lower.Value W (n+1)) s:=
  (readerValue binding n packet,(0:PairValue (Lower.Value W n) s))
 let rootPoint:Af.AfterScope binding n packet:=Af.afterq binding n packet (liftMap (actionWord binding n packet))
 let valuePoint:Af.AfterScope binding n packet:=Af.constant binding n packet
  (Af.writerValue binding n packet (actionWord binding n packet))
 let readerPoint:Af.AfterScope binding n packet:=Af.constant binding n packet endpointValue
 have semantic:=scope_semantic binding n packet _ _ (residual_syntax binding n packet)
 have subtract := (Af.afterq binding n packet).map_sub (liftMap (actionWord binding n packet))
  (Finsupp.single (.const endpointValue) 1)
 have semantic':Af.afterq binding n packet (liftMap (activeWord binding n packet))=rootPoint-readerPoint :=
  semantic.trans subtract
 have action:=Lower.SourceFamily.Foresight.Contextual.Profile.Generated.source_scope_action
  binding n packet native (actionWord binding n packet)
 have writer:Af.afterq binding n packet (Af.writerBoundary binding n packet (actionWord binding n packet))=
  rootPoint-valuePoint :=
  (Af.writer_affine binding n packet native (actionWord binding n packet)).trans
   (congrArg (fun point:Af.AfterScope binding n packet=>point-valuePoint) action)
 have correction:Af.constant binding n packet (endpointCorrection binding n packet)=valuePoint-readerPoint :=
  (Af.constant binding n packet).map_sub (Af.writerValue binding n packet (actionWord binding n packet)) endpointValue
 exact (semantic'.trans (sub_add_sub_cancel rootPoint valuePoint readerPoint).symm).trans
  (congrArg₂ (·+·) writer.symm correction.symm)

theorem source_charge:2≤remaining (Future.actionRaw packet.1 (cfg binding n packet)).expression := by
 exact Lower.SourceFamily.Foresight.Contextual.factory_action_charge binding n packet

def paidSource:Σ paid:DebtActivationWorld.GeneratedStepAt
 (RootGeneratedDebtActivationJointSource.Idle.law (activeEnv binding n packet) (activeExpression binding n packet))
 (Wr.receiver binding n packet).event.state,PLift ((Wr.receiver binding n packet).action=.inr paid):=by
 have charged:=Future.receiver_budget packet.1 (cfg binding n packet)
  (Lower.SourceFamily.scalar (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) binding) n packet)
  (Lower.SourceFamily.pair (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) binding) n packet)
  (source_charge binding n packet)
 cases selected:(Wr.receiver binding n packet).action with
 | inr paid=>exact ⟨paid,⟨rfl⟩⟩
 | inl settled=>
  have zero:=(SourceOperationExecutionDebt.law (activeEnv binding n packet) (activeExpression binding n packet)).settlement_budget_zero settled
  change remaining (Wr.receiver binding n packet).event.state.1=0 at zero
  change 3≤remaining (Wr.receiver binding n packet).event.state.1 at charged
  omega

def payment:=Pay.payment (Wr.receiver binding n packet) (paidSource binding n packet).1 (paidSource binding n packet).2.down
theorem strict_debit:type_of% (payment binding n packet).strictDebit:=(payment binding n packet).strictDebit
theorem debt_current:type_of% (Pay.debt_current_actual (Wr.receiver binding n packet)):=Pay.debt_current_actual (Wr.receiver binding n packet)
end Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
