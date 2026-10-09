import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Engine
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Runtime
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
namespace Lower.Run
variable {S : Type u} {W X : S → Type u} [∀ s,AddCommGroup (W s)] {s : S}
local instance runtimeGroup (n : Nat) (t : S) : AddCommGroup (Value W n t) := groups W n t
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)

abbrev process := SourceFamily.processWithSourceFamily (SourceFamily.defaultFactory W X s) initial firstCfg language
abbrev nextQuery := SourceFamily.nextQuery (SourceFamily.defaultFactory W X s) initial firstCfg language

theorem nextQuery_unique (count : (process initial firstCfg language).State)
 (candidate : ((process initial firstCfg language).stateAt count).Query)
 (nextCandidate : ((process initial firstCfg language).stateAt ((process initial firstCfg language).successorAt count candidate).val).Query) :
 nextCandidate=nextQuery initial firstCfg language count candidate :=
 SourceFamily.nextQuery_unique (SourceFamily.defaultFactory W X s) initial firstCfg language count candidate nextCandidate

abbrev runtime := SourceFamily.runtime (SourceFamily.defaultFactory W X s) initial firstCfg language

theorem actual_node (count : Nat) : ((runtime initial firstCfg language).stateAt count).engine.node=
 .active (SourceFamily.Actual.presentationAt (SourceFamily.defaultFactory W X s) initial firstCfg language count) := SourceFamily.actual_node (SourceFamily.defaultFactory W X s) initial firstCfg language count

theorem actual_next (count : Nat) : ((runtime initial firstCfg language).tickAt count).next.node=
 .active (SourceFamily.Actual.presentationAt (SourceFamily.defaultFactory W X s) initial firstCfg language (count+1)) := SourceFamily.actual_next (SourceFamily.defaultFactory W X s) initial firstCfg language count

theorem actual_receipt (count : Nat) : type_of% (SourceFamily.actual_receipt (SourceFamily.defaultFactory W X s) initial firstCfg language count) :=
 SourceFamily.actual_receipt (SourceFamily.defaultFactory W X s) initial firstCfg language count
end Lower.Run
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
