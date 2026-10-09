import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Reader
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Mixed.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Mixed
namespace R
export Lower.SourceFamily.Foresight.Contextual.Reader
 (query completed residualExpression sourceBinding feedbackExpression expression raw result reader query_environment)
end R
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (residual residual_old feedback_generated)
end P
namespace C
export Lower.SourceFamily.Foresight.Contextual (sourceEnvironment)
end C
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base)
end Q
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t,X t→Expr W X t) (n:Nat) (seed:Lower.SourceFamily.Seed W X s n)
variable (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
variable (index:Lower.SourceFamily.Foresight.Installed.OccurrenceIndex n frame)
def ownEnv := (R.query binding n seed frame index).environment
abbrev ownTrace := (R.completed binding n seed frame index).2.1.2
def sourceBoundary := boundary (ownEnv binding n seed frame index) (ownTrace binding n seed frame index)
def sourceIncrement := actedIncrement (ownEnv binding n seed frame index) (R.sourceBinding binding n)

theorem feedback_generated : (R.feedbackExpression binding n seed frame index).eval (ownEnv binding n seed frame index)=
 effectEvaluator (R:=ℤ) (ownEnv binding n seed frame index) (sourceIncrement binding n seed frame index)
  (sourceBoundary binding n seed frame index) :=
 P.feedback_generated binding n seed frame index

theorem source_result_effect : (R.result binding n seed frame index).2.2.1=
 effectEvaluator (R:=ℤ) (ownEnv binding n seed frame index) (sourceIncrement binding n seed frame index)
  (sourceBoundary binding n seed frame index) := by
 have paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (Q.base frame).root.toAuthoritativeRoot (R.reader binding n seed frame) index.2
 have same : C.sourceEnvironment binding n seed frame index=ownEnv binding n seed frame index :=
  (R.query_environment binding n seed frame index).symm
 apply paid.trans
 change (R.residualExpression binding n seed frame index).eval (C.sourceEnvironment binding n seed frame index)+
  (R.feedbackExpression binding n seed frame index).eval (C.sourceEnvironment binding n seed frame index)=_
 rw [same]
 have oldZeroP : (P.residual binding n seed frame index).eval
  (C.sourceEnvironment binding n seed frame index)=0 :=
  P.residual_old _ _ _ _ _
 have oldZero : (R.residualExpression binding n seed frame index).eval
  (ownEnv binding n seed frame index)=0 := by
  exact ((congrArg (fun env=>(R.residualExpression binding n seed frame index).eval env) same).symm).trans oldZeroP
 exact (congrArg₂ (· + ·) oldZero (feedback_generated binding n seed frame index)).trans (zero_add _)

theorem actual_next_residual :
 (residualEquivRange (evaluation (R:=ℤ) ((ownEnv binding n seed frame index)+(sourceIncrement binding n seed frame index)))
  (canonicalResidual (evaluation (R:=ℤ) ((ownEnv binding n seed frame index)+(sourceIncrement binding n seed frame index)))
   (sourceBoundary binding n seed frame index))).val = (R.result binding n seed frame index).2.2.1 :=
 ((ownTrace binding n seed frame index).updated_residual (R:=ℤ)
  (sourceIncrement binding n seed frame index)).trans (source_result_effect binding n seed frame index).symm

theorem complete_ordered_effect :
 ((R.residualExpression binding n seed frame index).mixedTerms.map
  (fun term=> (nativeTerm term).eval (pairEnvironment (ownEnv binding n seed frame index)
   (sourceIncrement binding n seed frame index)) |>.1)).sum = (R.result binding n seed frame index).2.2.1 :=
 (ordered_feedback (ownEnv binding n seed frame index) (ownTrace binding n seed frame index)
  (R.sourceBinding binding n)).trans
 ((feedback_generated binding n seed frame index).trans (source_result_effect binding n seed frame index).symm)
end Lower.SourceFamily.Foresight.Contextual.Mixed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
