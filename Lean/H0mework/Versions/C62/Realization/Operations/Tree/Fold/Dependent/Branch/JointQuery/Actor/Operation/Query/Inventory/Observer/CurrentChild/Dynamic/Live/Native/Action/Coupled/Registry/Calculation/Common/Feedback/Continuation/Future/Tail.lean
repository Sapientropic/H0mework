import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Actual
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Future.Tail
variable {S : Type u} {W X : S → Type u} [∀ s,AddCommGroup (W s)] {s : S}
local instance tailGroup (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)
abbrev frameAt := Lower.frameAt initial firstCfg language
abbrev cfgAt := Lower.cfgAt initial firstCfg language

theorem envSquare (n : Nat) : type_of% (Future.Actual.next_raw_environment
 (frameAt initial firstCfg language (n+1)) (Lower.tailData initial firstCfg language n).2
 (Lower.scalarAt initial firstCfg language (n+1)) (Lower.pairAt initial firstCfg language (n+1))
 (Lower.Stock.seed (frameAt initial firstCfg language (n+1)) (cfgAt initial firstCfg language (n+1)) (Lower.languageAt initial firstCfg language (n+1)))) :=
 Future.Actual.next_raw_environment
 (frameAt initial firstCfg language (n+1)) (Lower.tailData initial firstCfg language n).2
 (Lower.scalarAt initial firstCfg language (n+1)) (Lower.pairAt initial firstCfg language (n+1))
 (Lower.Stock.seed (frameAt initial firstCfg language (n+1)) (cfgAt initial firstCfg language (n+1)) (Lower.languageAt initial firstCfg language (n+1)))

theorem actual_tail_environment (n : Nat) :
 (Future.Actual.Q.query (frameAt initial firstCfg language (n+2)) (cfgAt initial firstCfg language (n+2))).raw.environment=
 pairEnvironment (SourceGeneratedInquiryReceiptAction.afterEnvironment (frameAt initial firstCfg language (n+1))
  (cfgAt initial firstCfg language (n+1))) 0 := by
 exact envSquare initial firstCfg language n
end Future.Tail
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
