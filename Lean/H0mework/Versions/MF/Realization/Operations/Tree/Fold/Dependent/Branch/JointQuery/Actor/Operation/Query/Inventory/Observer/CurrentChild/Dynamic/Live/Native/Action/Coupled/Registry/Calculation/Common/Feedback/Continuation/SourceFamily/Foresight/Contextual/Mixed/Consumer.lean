import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Mixed.Receipt
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Paid.Consumer
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Whole.Consumer
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Lower.SourceFamily.Foresight.Contextual.Mixed.Consumed
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance physicalGroups : ∀ t, AddCommGroup (Act.PhysicalValue root visit rec t) := inferInstance
local instance currentGroups (n : Nat) (t : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Slot root rec) :
    AddCommGroup (Lower.Value (Act.LowValue root visit rec) n t) := Lower.groups (Act.LowValue root visit rec) n t
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage count : Nat)
abbrev binding := Lower.SourceFamily.Replay.Activated.OriginalBinding.lowBinding root visit rec
abbrev data (n : Nat) := Lower.SourceFamily.Replay.Activated.dataAt root visit rec U7 calculus anchor sourceStage stage count n

abbrev Word (n : Nat) (t) := Paid.Word (W:=Act.LowValue root visit rec) (X:=Act.LowVar root visit rec) (n+1) t
abbrev Event (n : Nat) := Paid.Ledger.SourceEvent (W:=Act.LowValue root visit rec) (X:=Act.LowVar root visit rec) (s:=Act.sort root rec) (n+1)
abbrev frame (n:Nat) := (data root visit rec U7 calculus anchor sourceStage stage count n).1
abbrev seed (n:Nat) := (data root visit rec U7 calculus anchor sourceStage stage count n).2

theorem actual_effect (n:Nat) : type_of% (Mixed.actual_result_effect (binding root visit rec) (n+1)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)) := Mixed.actual_result_effect _ _ _ _
theorem actual_residual (n:Nat) : type_of% (Mixed.actual_result_residual (binding root visit rec) (n+1)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)) := Mixed.actual_result_residual _ _ _ _
theorem actual_terms (n:Nat) : type_of% (Mixed.actual_ordered_effect (binding root visit rec) (n+1)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)) := Mixed.actual_ordered_effect _ _ _ _
theorem actual_registered_expression (n:Nat) : type_of% (Mixed.registered_source_expression (binding root visit rec) (n+1)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)) := Mixed.registered_source_expression _ _ _ _
theorem actual_registered_effect (n:Nat) : type_of% (Mixed.registered_source_effect (binding root visit rec) (n+1)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)) := Mixed.registered_source_effect _ _ _ _
theorem actual_registered_next (n:Nat) : type_of% (Mixed.registered_source_next (binding root visit rec) (n+1)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)) := Mixed.registered_source_next _ _ _ _

theorem actual_consumption (n:Nat) (word:Word root visit rec n (Act.sort root rec)) :
 type_of% (actual_effect root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_residual root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_terms root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_registered_expression root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_registered_effect root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_registered_next root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (Lower.SourceFamily.Foresight.Contextual.Consumed.actual_consumption root visit rec U7 calculus anchor sourceStage stage count n word) :=
 ⟨actual_effect _ _ _ _ _ _ _ _ _ n,actual_residual _ _ _ _ _ _ _ _ _ n,actual_terms _ _ _ _ _ _ _ _ _ n,
 actual_registered_expression _ _ _ _ _ _ _ _ _ n,actual_registered_effect _ _ _ _ _ _ _ _ _ n,
 actual_registered_next _ _ _ _ _ _ _ _ _ n,Lower.SourceFamily.Foresight.Contextual.Consumed.actual_consumption _ _ _ _ _ _ _ _ _ n word⟩
end Lower.SourceFamily.Foresight.Contextual.Mixed.Consumed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
