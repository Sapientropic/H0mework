import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Feedback.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Future.Replay
namespace Read
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
variable (binding : ∀ t,X t → Expr W X t)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr W X s)))
variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
theorem boundary_generated : Source.boundary seed frame supplied=
 Finsupp.single (Source.inverseRaw seed frame supplied).expression 1-
 Finsupp.single (Source.inverseResult seed frame supplied).2.1.1 1 :=
 (Source.inverseResult seed frame supplied).2.1.2.relation_boundary

theorem feedback_value : (Source.feedbackExpression binding seed frame supplied).eval
 (Source.pairEnvironment binding frame supplied)=
 evaluation (R:=ℤ) (Source.actedEnvironment binding frame supplied) (Source.boundary seed frame supplied) := by
 change ((Source.sourceExpression seed frame supplied).subst (Source.pairBinding binding)).eval
  (Source.pairEnvironment binding frame supplied)=_
 rw [Expr.eval_subst]
 exact Coefficients.expression_eval _ _

theorem source_value : (Source.result binding seed frame supplied).2.2.1=
 (Original.Request.occurrenceRaw seed frame supplied).expression.eval (Source.pairEnvironment binding frame supplied)+
 evaluation (R:=ℤ) (Source.actedEnvironment binding frame supplied) (Source.boundary seed frame supplied) := by
 have generated := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot
  (Source.reader binding seed frame) supplied
 apply generated.trans
 exact congrArg ((Original.Request.occurrenceRaw seed frame supplied).expression.eval
  (Source.pairEnvironment binding frame supplied)+·) (feedback_value binding seed frame supplied)

theorem source_cost : (Source.result binding seed frame supplied).2.1.2.length=
 remaining (Source.expression binding seed frame supplied) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _

theorem source_inverse :
 (residualEquivRange (evaluation (R:=ℤ) (Source.actedEnvironment binding frame supplied))
 (canonicalResidual (evaluation (R:=ℤ) (Source.actedEnvironment binding frame supplied))
  (Source.boundary seed frame supplied))).val=
 (Source.feedbackExpression binding seed frame supplied).eval (Source.pairEnvironment binding frame supplied) := by
 change evaluation (R:=ℤ) (Source.actedEnvironment binding frame supplied) (Source.boundary seed frame supplied)=_
 exact (feedback_value binding seed frame supplied).symm

theorem original_events (event : PresentedRelationEventAt (Expr (PairValue W) X s))
 (present : event ∈ (Original.Request.Inverse.paidWritten seed frame supplied).trace) :
 event ∈ (Source.pairWritten binding seed frame supplied).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 _ present

theorem paid_events (event : PresentedRelationEventAt (Expr (PairValue W) X s))
 (present : event ∈ (SourceOperationPaidRelations.exposure (Source.result binding seed frame supplied).2.1.2).trace) :
 event ∈ (Source.pairWritten binding seed frame supplied).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 _ ((SourceHistoryCommon.parallel_left _ _ _).1 _ present)

theorem replay_events (event : PresentedRelationEventAt (Expr (PairValue W) X s))
 (present : event ∈ (SourceOperationPaidRelations.exposure (Source.replayTrace binding seed frame supplied)).trace) :
 event ∈ (Source.pairWritten binding seed frame supplied).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 _ ((SourceHistoryCommon.parallel_right _ _ _).1 _ present)

theorem actual_raw : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame (Installed.programme binding seed)).raw=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame (Installed.programme binding seed)).reader
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame) :=
 congrArg (fun query => query.raw)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_generated frame (Installed.programme binding seed))

theorem installed_material : (Installed.face binding seed frame).rootRead=
 Source.material binding seed (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
  (Installed.Q.actualOccurrence frame) := rfl

theorem actual_born_environment
 {nextCurrent : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame
  (Installed.programme binding seed)).V.Current}
 (nextOccurrence : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame
  (Installed.programme binding seed)).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt nextCurrent) :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame (Installed.programme binding seed)).environment nextOccurrence=
 Source.physicalNext binding (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
  (Installed.Q.actualOccurrence frame) := rfl

theorem actual_scalar_stock :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame (Installed.programme binding seed)).inventory=
 some (Installed.scalarStock binding seed frame) := rfl

theorem actual_pair_stock :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame (Installed.programme binding seed)).pairInventory=
 some (Installed.pairStock binding seed frame) := rfl
end Read
end Future.Replay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
