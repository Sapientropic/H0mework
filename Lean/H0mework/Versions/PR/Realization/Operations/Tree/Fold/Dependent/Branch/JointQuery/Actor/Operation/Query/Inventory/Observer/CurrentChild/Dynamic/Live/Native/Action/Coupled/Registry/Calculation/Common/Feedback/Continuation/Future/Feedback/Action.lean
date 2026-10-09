import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Transport.Source
import H0mework.Realization.Operations.Execution.Substitution.Source
import H0mework.Realization.Operations.Execution.Coefficients.Words
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace Future.Replay
variable {S : Type u} {W X : S → Type u} [∀ slot,AddCommGroup (W slot)] {slot : S}
variable (binding : ∀ target,X target → Expr W X target)
variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=slot))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
def physicalEnvironment := frame.environment
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence frame.registered frame.packetAt supplied)
def physicalNext := SourceSubstitution.sourceEnvironment binding (physicalEnvironment frame supplied)
def actionPairEnvironment := pairEnvironment (physicalEnvironment frame supplied)
 (physicalNext binding frame supplied-physicalEnvironment frame supplied)
def pairBinding (target : S) (name : X target) := liftExpr (binding target name)
def readNext := SourceSubstitution.sourceEnvironment (pairBinding binding) (actionPairEnvironment binding frame supplied)
theorem generated_environment : readNext binding frame supplied=
 pairEnvironment (physicalNext binding frame supplied)
 (SourceSubstitution.sourceEnvironment binding (physicalNext binding frame supplied)-physicalNext binding frame supplied) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Transport.Square.generated binding (physicalEnvironment frame supplied)
variable (word : Formal ℤ (PairValue W) X slot)
def sourceExpression := Coefficients.expression word
def actedExpression := (sourceExpression word).subst (pairBinding binding)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue W) (Var:=X) (sort:=slot) :=
 ⟨actionPairEnvironment binding frame supplied,actedExpression binding word⟩
def sourceTrace := execution (readNext binding frame supplied) (sourceExpression word)
def replayTrace := (sourceTrace binding frame supplied word).substitutedTrace
 (pairBinding binding) (actionPairEnvironment binding frame supplied)
def paidTrace := execution (actionPairEnvironment binding frame supplied) (actedExpression binding word)
def written := SourceHistoryCommon.seed (SourceOperationPaidRelations.exposure (paidTrace binding frame supplied word))
 (SourceOperationPaidRelations.exposure (replayTrace binding frame supplied word))
theorem raw_value : (raw binding frame supplied word).expression.eval (raw binding frame supplied word).environment=
 evaluation (R:=ℤ) (readNext binding frame supplied) word :=
 (Expr.eval_subst _ _ _).trans (Coefficients.expression_eval _ _)
theorem replay_fee : (replayTrace binding frame supplied word).length=remaining (actedExpression binding word) :=
 substituted_charge _ _ _
theorem paid_fee : (paidTrace binding frame supplied word).length=remaining (actedExpression binding word) :=
 (paidTrace binding frame supplied word).length_to_const

theorem source_boundary : type_of% ((sourceTrace binding frame supplied word).relation_boundary (R:=ℤ)) :=
 (sourceTrace binding frame supplied word).relation_boundary (R:=ℤ)
theorem replay_boundary : type_of% ((replayTrace binding frame supplied word).relation_boundary (R:=ℤ)) :=
 (replayTrace binding frame supplied word).relation_boundary (R:=ℤ)
theorem paid_boundary : type_of% ((paidTrace binding frame supplied word).relation_boundary (R:=ℤ)) :=
 (paidTrace binding frame supplied word).relation_boundary (R:=ℤ)
theorem source_cochain : type_of% ((sourceTrace binding frame supplied word).relation_cochain (R:=ℤ)
 (readNext binding frame supplied-actionPairEnvironment binding frame supplied)) :=
 (sourceTrace binding frame supplied word).relation_cochain (R:=ℤ) _
theorem action_boundary_square : type_of% (SourceSubstitution.boundary_square (R:=ℤ) (s:=slot)
 (pairBinding binding) (actionPairEnvironment binding frame supplied)) := SourceSubstitution.boundary_square _ _
theorem all_paid_events (event : PresentedRelationEventAt (Expr (PairValue W) X slot))
 (present : event ∈ (SourceOperationPaidRelations.exposure (paidTrace binding frame supplied word)).trace) :
 event ∈ (written binding frame supplied word).trace := (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem all_replay_events (event : PresentedRelationEventAt (Expr (PairValue W) X slot))
 (present : event ∈ (SourceOperationPaidRelations.exposure (replayTrace binding frame supplied word)).trace) :
 event ∈ (written binding frame supplied word).trace := (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem all_paid_relations : (SourceOperationPaidRelations.words (paidTrace binding frame supplied word)).length=
 (paidTrace binding frame supplied word).length := SourceOperationPaidRelations.complete_steps _
theorem all_replay_relations : (SourceOperationPaidRelations.words (replayTrace binding frame supplied word)).length=
 (replayTrace binding frame supplied word).length := SourceOperationPaidRelations.complete_steps _
end Future.Replay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
