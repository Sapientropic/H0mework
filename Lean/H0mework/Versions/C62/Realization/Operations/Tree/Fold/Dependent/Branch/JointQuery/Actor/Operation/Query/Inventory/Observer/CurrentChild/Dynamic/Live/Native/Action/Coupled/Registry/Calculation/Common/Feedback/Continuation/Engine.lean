import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stage
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Engine
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Admission
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission
 (presentation generatedAction query compiles target_root sourceRoot sourceEvent)
end Admission
namespace StockObservation
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation
 (current current_observation read root)
end StockObservation
namespace Lower.Run
variable {S : Type u} (W : S → Type u) [∀ s,AddCommGroup (W s)]
local instance runningGroup (n : Nat) (s : S) : AddCommGroup (Lower.Value W n s) := Lower.groups W n s
variable {W} {X : S → Type u} {s : S}
namespace Transport
variable {Y Z : S → Type u}
abbrev Data (Y : S → Type u) := M.Frame (Value:=PairValue W) (Var:=Y) (sort:=s) ×
 RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) Y s))
theorem current_eq (same : Y=Z) (data : Data (W:=W) (s:=s) Y) :
 StockObservation.current data.1 (R.programme data.2)=
 StockObservation.current (same ▸ data : Data (W:=W) (s:=s) Z).1
   (R.programme (same ▸ data : Data (W:=W) (s:=s) Z).2) := by
 cases same; rfl

theorem root_heq (same : Y=Z) (data : Data (W:=W) (s:=s) Y) :
 HEq (StockObservation.root data.1 (R.programme data.2))
 (StockObservation.root (same ▸ data : Data (W:=W) (s:=s) Z).1
  (R.programme (same ▸ data : Data (W:=W) (s:=s) Z).2)) := by
 cases same; rfl
end Transport
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)
abbrev frameAt := Lower.frameAt initial firstCfg language
abbrev cfgAt := Lower.cfgAt initial firstCfg language
abbrev scalarAt := Lower.scalarAt initial firstCfg language
abbrev pairAt := Lower.pairAt initial firstCfg language
abbrev nextCfg := Lower.nextCfg initial firstCfg language

abbrev presentationAt := Lower.SourceFamily.presentationAt (Lower.SourceFamily.defaultFactory W X s) initial firstCfg language
abbrev generated := Lower.SourceFamily.generated (Lower.SourceFamily.defaultFactory W X s) initial firstCfg language
abbrev queryAt := Lower.SourceFamily.queryAt (Lower.SourceFamily.defaultFactory W X s) initial firstCfg language

theorem presentation_current (n : Nat) : (presentationAt initial firstCfg language n).erase=
 StockObservation.current (frameAt initial firstCfg language n) (cfgAt initial firstCfg language n) := rfl

theorem target_current (n : Nat) :
 StockObservation.current (Stock.receiver (frameAt initial firstCfg language n) (cfgAt initial firstCfg language n) (Lower.languageAt initial firstCfg language n))
 (nextCfg initial firstCfg language n)=
 StockObservation.current (frameAt initial firstCfg language (n+1)) (cfgAt initial firstCfg language (n+1)) := by
 cases n <;> exact Lower.SourceFamily.target_current (Lower.SourceFamily.defaultFactory W X s) initial firstCfg language _

theorem next_full_root (n : Nat) : HEq (StockObservation.root (frameAt initial firstCfg language (n+1)) (cfgAt initial firstCfg language (n+1)))
 (generated initial firstCfg language n).target.targetRoot := Lower.SourceFamily.next_full_root (Lower.SourceFamily.defaultFactory W X s) initial firstCfg language n

theorem canonical_erasure (n : Nat) : (presentationAt initial firstCfg language (n+1)).erase=
 ⟨(generated initial firstCfg language n).target.TargetN,(generated initial firstCfg language n).target.targetAnswerAndNext.nextCurrent⟩ := Lower.SourceFamily.canonical_erasure (Lower.SourceFamily.defaultFactory W X s) initial firstCfg language n

theorem query_unique (n : Nat) (candidate : (presentationAt initial firstCfg language n).Query) : candidate=queryAt initial firstCfg language n := Lower.SourceFamily.query_unique (Lower.SourceFamily.defaultFactory W X s) initial firstCfg language n candidate

theorem successor_valid (n : Nat) (candidate : (presentationAt initial firstCfg language n).Query) :
 (presentationAt initial firstCfg language (n+1)).erase=(RootInquiryProcessNode.answered (presentationAt initial firstCfg language n) candidate).erase ∧
 (.active (presentationAt initial firstCfg language n) : RootInquiryProcessNode).PreservesGeneratedLivingLawAt candidate (.active (presentationAt initial firstCfg language (n+1))) := Lower.SourceFamily.successor_valid (Lower.SourceFamily.defaultFactory W X s) initial firstCfg language n candidate

variable {T : Type u} {V Z : T → Type u} [∀ t,AddCommGroup (V t)] {t : T}
variable (other : M.Frame (Value:=V) (Var:=Z) (sort:=t))
variable (otherCfg : A.Programme (PhysicalValue:=V) (PhysicalVar:=Z) (sort:=t))
theorem stock_eq_of_current (n : Nat)
 (same : StockObservation.current (frameAt initial firstCfg language n) (cfgAt initial firstCfg language n)=StockObservation.current other otherCfg) :
 Stock.size (frameAt initial firstCfg language n)=Stock.size other := Lower.SourceFamily.stock_eq_of_current (Lower.SourceFamily.defaultFactory W X s) initial firstCfg language other otherCfg n same

theorem erasure_injective : Function.Injective (fun n => (presentationAt initial firstCfg language n).erase) := Lower.SourceFamily.erasure_injective (Lower.SourceFamily.defaultFactory W X s) initial firstCfg language
end Lower.Run
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
