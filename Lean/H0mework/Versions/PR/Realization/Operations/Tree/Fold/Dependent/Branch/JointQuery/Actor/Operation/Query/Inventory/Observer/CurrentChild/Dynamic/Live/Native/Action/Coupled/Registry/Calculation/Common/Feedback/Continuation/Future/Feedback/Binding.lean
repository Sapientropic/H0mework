import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open SourceOperationEffects SourceOperationScalarInventoryLift
namespace Future.Replay.Binding
variable {S : Type u} {W X : S → Type u} [∀ slot,AddCommGroup (W slot)]
local instance stageGroups (n : Nat) (slot : S) : AddCommGroup (Lower.Value W n slot) := Lower.groups W n slot
variable (original : ∀ slot,X slot → Expr W X slot)
def «at» (n : Nat) : ∀ slot,X slot → Expr (Lower.Value W n) X slot :=
 Nat.rec (motive:=fun k => ∀ slot,X slot → @Expr S (Lower.Value W k) X (Lower.groups W k) slot)
  original (fun k previous slot name => @liftExpr S (Lower.Value W k) X (Lower.groups W k) slot (previous slot name)) n
@[simp] theorem at_zero : «at» original 0=original := rfl
@[simp] theorem at_succ (n : Nat) (slot : S) (name : X slot) :
 «at» original (n+1) slot name=liftExpr («at» original n slot name) := rfl
end Future.Replay.Binding
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
