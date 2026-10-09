import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Source
set_option autoImplicit false
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
variable {α : Type u} {β : Type v}
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationExecution CofinalHistorySettlement
mutual
theorem mapped_trace (f : α → β) (tree : RootedAccountedUnfolding α) :
 (tree.map f).trace=tree.trace.map f := by
 cases tree with
 | occur root branches =>
  change f root::RootedAccountedUnfolding.traceBranches (RootedAccountedUnfolding.mapBranches f branches)=
   (root::RootedAccountedUnfolding.traceBranches branches).map f
  rw [mapped_branches]
  rfl
theorem mapped_branches (f : α → β) (branches : AccountedBranches α) :
 RootedAccountedUnfolding.traceBranches (RootedAccountedUnfolding.mapBranches f branches)=
 (RootedAccountedUnfolding.traceBranches branches).map f := by
 cases branches with
 | nil => rfl
 | cons head tail =>
  change (head.map f).trace++RootedAccountedUnfolding.traceBranches (RootedAccountedUnfolding.mapBranches f tail)=
   (head.trace++RootedAccountedUnfolding.traceBranches tail).map f
  rw [mapped_trace,mapped_branches,List.map_append]
end
theorem mapped_length (f : α → β) (tree : RootedAccountedUnfolding α) : (tree.map f).trace.length=tree.trace.length := by
 rw [mapped_trace,List.length_map]
theorem seed_length (first second : RootedAccountedUnfolding α) :
 (SourceHistoryCommon.seed first second).trace.length=first.trace.length+second.trace.length+1 := by
 change (first.root::(first.trace++(second.trace++[]))).length=_
 simp only [List.length_cons,List.length_append,List.length_nil,Nat.add_zero]
variable {S : Type u} {W X : S → Type u} [∀ slot,AddCommGroup (W slot)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=W) (Var:=X) (sort:=s))
abbrev liftEvent := SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftEvent
 (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s)
def physicalPrior : Option (RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) X s))) :=
 frame.inventory.map (fun carried => carried.map liftEvent)
def pairPrior : Option (RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (PairValue W)) X s))) :=
 frame.pairInventory.map (fun carried => carried.map
  (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftEvent
   (PhysicalValue:=PairValue W) (PhysicalVar:=X) (sort:=s)))
def preserve (prior : Option (RootedAccountedUnfolding α)) (generated : RootedAccountedUnfolding α) :=
 match prior with | none => generated | some carried => SourceHistoryCommon.seed carried generated
theorem preserves_length (carried generated : RootedAccountedUnfolding α) :
 carried.trace.length<(preserve (some carried) generated).trace.length := by
 change carried.trace.length<(SourceHistoryCommon.seed carried generated).trace.length
 rw [seed_length]
 omega
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
