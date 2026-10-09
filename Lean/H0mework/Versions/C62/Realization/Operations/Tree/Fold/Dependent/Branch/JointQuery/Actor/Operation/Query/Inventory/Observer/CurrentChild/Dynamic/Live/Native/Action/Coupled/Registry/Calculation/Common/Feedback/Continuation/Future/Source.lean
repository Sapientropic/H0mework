import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Source
import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation (Cursor ofFrame)
end O
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query datum actualOccurrence)
end Q
namespace R
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted (programme)
end R
namespace Receipt
export SourceGeneratedInquiryReceiptAction (actualMaterial actual_raw actual_environment actionReader actionResultAt old registered packetAt afterEnvironment firstStep first_action actual_updated_environment)
end Receipt
namespace B
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap (initial)
end B
variable {S : Type u} {W X : S → Type u} [∀ s,AddCommGroup (W s)] {s : S}
private theorem debit {e : Env W X} {raw : Expr W X s} {state : SourceOperationExecutionDebt.State e raw}
 (paid : DebtActivationWorld.GeneratedStepAt (SourceOperationExecutionDebt.law e raw) state) :
 remaining state.1=remaining paid.1.1+1 := by
 rcases paid with ⟨target,step⟩
 cases step with
 | paid actual => exact actual.remaining_eq
namespace CursorLaw
variable (cursor : O.Cursor (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
def budget := remaining cursor.current.2.state.1

theorem paid_source (positive : 0<budget cursor) :
 cursor.next.raw.environment=cursor.raw.environment ∧ budget cursor=budget cursor.next+1 := by
 unfold SourceOperationInquiry.Context.Native.Orbit.Installation.Cursor.next
 cases selected : cursor.action with
 | inl settled =>
   have zero := (SourceOperationExecutionDebt.law cursor.registered.input.environment cursor.registered.input.expression).settlement_budget_zero settled
   change remaining cursor.current.2.state.1=0 at zero
   change 0<remaining cursor.current.2.state.1 at positive
   omega
 | inr paid =>
   constructor
   · rfl
   · change remaining cursor.current.2.state.1=remaining (RootGeneratedDebtActivationJointSource.mathTarget cursor.current.2).1+1
     unfold RootGeneratedDebtActivationJointSource.mathTarget
     change RootGeneratedDebtActivationJointSource.mathAction cursor.current.2=.inr paid at selected
     rw [selected]
     exact debit paid

theorem three_paid (sourceBudget : 3≤budget cursor) :
 pairEnvironment cursor.next.next.raw.environment
 (cursor.next.next.next.raw.environment-cursor.next.next.raw.environment)=pairEnvironment cursor.raw.environment 0 := by
 have one := paid_source cursor (by omega)
 have two := paid_source cursor.next (by omega)
 have three := paid_source cursor.next.next (by omega)
 have twoEnv := two.1.trans one.1
 have threeEnv := three.1.trans twoEnv
 rw [twoEnv,threeEnv,sub_self]

theorem settled_source (settled : SourceOperationExecutionDebt.Settlement cursor.current.2.state)
 (selected : cursor.action=.inl settled) :
 cursor.next.raw.environment=cursor.environment (cursor.old.emitted cursor.current.1) := by
 unfold SourceOperationInquiry.Context.Native.Orbit.Installation.Cursor.next
 rw [selected]
 change cursor.registered.input.environment+
  (cursor.environment (cursor.old.emitted cursor.current.1)-cursor.registered.input.environment)=_
 exact add_sub_cancel _ _
end CursorLaw

variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (scalar : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) cfg.LowVar s)))
variable (pair : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (PairValue W)) cfg.LowVar s)))
def receiver := B.initial frame cfg scalar pair
abbrev actionRaw:=Receipt.actionReader frame cfg (Q.actualOccurrence frame)

theorem receiver_registered_environment : (receiver frame cfg scalar pair).registered.input.environment=Receipt.afterEnvironment frame cfg :=
 Receipt.actual_updated_environment frame cfg

theorem receiver_decoder {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) :
 (receiver frame cfg scalar pair).environment supplied=((Q.datum frame cfg).reader supplied).environment := rfl

theorem receiver_state : (receiver frame cfg scalar pair).event.state=(Receipt.firstStep frame cfg).1 := by
 change RootGeneratedDebtActivationJointSource.mathTarget (RootGeneratedDebtActivationJointSource.initialEvent (Receipt.registered frame cfg))=_
 unfold RootGeneratedDebtActivationJointSource.mathTarget
 have selected := (RootGeneratedDebtActivationJointSource.Successor.Inquiry.sourceAction_eq (Receipt.old frame cfg)
  (Receipt.registered frame cfg) (Receipt.packetAt frame cfg)).symm.trans (Receipt.first_action frame cfg)
 rw [selected]

theorem receiver_budget (queryCharge : 2≤remaining (actionRaw frame cfg).expression) :
 3≤CursorLaw.budget (O.ofFrame (receiver frame cfg scalar pair)) := by
 have fee := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget (Receipt.actualMaterial frame cfg)
 have consumed := debit (Receipt.firstStep frame cfg)
 change remaining (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression (Receipt.actualMaterial frame cfg))=
  remaining (Receipt.actualMaterial frame cfg).raw+remaining (Receipt.actualMaterial frame cfg).state.1+2 at fee
 have actualRaw : (Receipt.actualMaterial frame cfg).raw=(actionRaw frame cfg).expression := Receipt.actual_raw _ _
 change 3≤remaining (receiver frame cfg scalar pair).event.state.1
 rw [receiver_state]
 have rawFee := congrArg remaining actualRaw
 have sourceFee : remaining (RootGeneratedDebtActivationJointSource.initialEvent (Receipt.registered frame cfg)).state.1=
  remaining (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression (Receipt.actualMaterial frame cfg)) := rfl
 omega

theorem native_query_environment (nativeSeed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr W X s))) :
 (Q.query frame (R.programme nativeSeed)).raw.environment=
 pairEnvironment (O.ofFrame frame).next.next.raw.environment
  ((O.ofFrame frame).next.next.next.raw.environment-(O.ofFrame frame).next.next.raw.environment) := rfl

def nextRaw (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) cfg.LowVar s))) :=
 (Q.query (receiver frame cfg scalar pair) (R.programme seed)).raw

theorem actual_future_square (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) cfg.LowVar s)))
 (queryCharge : 2≤remaining (actionRaw frame cfg).expression) :
 (nextRaw frame cfg scalar pair seed).environment=pairEnvironment (Receipt.afterEnvironment frame cfg) 0 := by
 have env := CursorLaw.three_paid (O.ofFrame (receiver frame cfg scalar pair)) (receiver_budget frame cfg scalar pair queryCharge)
 have literal : (nextRaw frame cfg scalar pair seed).environment=
  pairEnvironment (O.ofFrame (receiver frame cfg scalar pair)).next.next.raw.environment
   ((O.ofFrame (receiver frame cfg scalar pair)).next.next.next.raw.environment-
    (O.ofFrame (receiver frame cfg scalar pair)).next.next.raw.environment) :=
   native_query_environment (receiver frame cfg scalar pair) seed
 rw [literal]
 rw [env]
 change pairEnvironment (receiver frame cfg scalar pair).registered.input.environment 0=_
 rw [receiver_registered_environment]

-- The required charge comes from the actual R reader's syntax, not a target premise.
theorem native_query_charge (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr W X s))) :
 2≤remaining (Receipt.actionReader frame (R.programme seed) (Q.actualOccurrence frame)).expression := by
 change 2≤remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.queryReader seed
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (Q.actualOccurrence frame)).expression+
  remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.queryResult seed
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (Q.actualOccurrence frame)).2.1.1+2
 omega

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
