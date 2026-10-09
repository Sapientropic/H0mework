import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Effect
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
variable (binding : ∀ t,X t → Expr W X t)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr W X s)))
variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (scalar : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) X s)))
variable (pair : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (PairValue W)) X s)))
theorem decoder_after_when_paid
 (paid : DebtActivationWorld.GeneratedStepAt
  (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment frame.registered.input.expression)
  frame.event.state) (actual : frame.action=.inr paid) :
 decoder binding seed frame scalar pair=after binding seed frame := by
 unfold after SourceGeneratedInquiryReceiptAction.afterEnvironment
 unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
 rw [actual]
 rfl

variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
theorem three_ast_fee (left paid feedback : Expr (PairValue W) X s) :
 3≤remaining (Expr.add (Expr.add left (Expr.linear (-AddMonoidHom.id _) paid)) feedback) := by
 change 3≤remaining left+(remaining paid+1)+1+remaining feedback+1
 omega

theorem source_fee : 3≤remaining (Future.Replay.Source.raw binding seed frame supplied).expression :=
 three_ast_fee
  (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.queryReader seed frame supplied).expression
  (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.occurrenceResult seed frame supplied).2.1.1
  (Future.Replay.Source.feedbackExpression binding seed frame supplied)

theorem actual_fee : 3≤remaining (Q.query frame (cfg binding seed)).raw.expression := by
 have generated := congrArg (fun query => remaining query.raw.expression)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_generated frame (cfg binding seed))
 rw [generated]
 exact source_fee binding seed (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (Q.actualOccurrence frame)

theorem receiver_paid : ∃ paid : DebtActivationWorld.GeneratedStepAt
 (RootGeneratedDebtActivationJointSource.Idle.law (receiver binding seed frame scalar pair).registered.input.environment
  (receiver binding seed frame scalar pair).registered.input.expression)
 (receiver binding seed frame scalar pair).event.state,
 (receiver binding seed frame scalar pair).action=.inr paid := by
 have charged := Future.receiver_budget frame (cfg binding seed) scalar pair (by
  have fee := actual_fee binding seed frame
  omega)
 cases selected : (receiver binding seed frame scalar pair).action with
 | inr paid => exact ⟨paid,rfl⟩
 | inl settled =>
  have zero := (SourceOperationExecutionDebt.law
   (receiver binding seed frame scalar pair).registered.input.environment
   (receiver binding seed frame scalar pair).registered.input.expression).settlement_budget_zero settled
  change remaining (receiver binding seed frame scalar pair).event.state.1=0 at zero
  change 3≤remaining (receiver binding seed frame scalar pair).event.state.1 at charged
  omega

end Lower.SourceFamily.Effect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
