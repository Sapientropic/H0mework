import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Trace
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Emitter
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace InventoryAS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (stockCfg)
end InventoryAS

private theorem preserved_generated {α : Type u} (prior : Option (RootedAccountedUnfolding α))
 (generated : RootedAccountedUnfolding α) (event : α) (present : event∈generated.trace) :
 event∈(Stock.preserve prior generated).trace := by
 cases prior with
 | none => exact present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

private theorem preserved_prior {α : Type u} (prior generated : RootedAccountedUnfolding α)
 (event : α) (present : event∈prior.trace) : event∈(Stock.preserve (some prior) generated).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event present

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ target, AddCommGroup (Value target)] {sort : Sorts}
local instance inventoryGroups (grade : Nat) (target : Sorts) : AddCommGroup
 (L.Value Value grade target) := L.groups Value grade target
variable (binding : ∀ target, Var target → Expr Value Var target) (name : Var sort)
variable (factory : Mother.SF.Factory Value Var sort)
variable (grade : Nat) (seed : Mother.SF.Seed Value Var sort grade)
variable (frame : Mother.M.Frame (Value:=L.Value Value grade) (Var:=Var) (sort:=sort))

def sourceBornConfiguration := InventoryAS.stockCfg (Mother.SF.cfg (installedTraceFactory binding name factory) grade seed)
def sourceBornCurrent := SlotSource.Shared.nextBorn frame (sourceBornConfiguration binding name factory grade seed)

theorem actual_source_scalar_trace_in_born (event)
 (present : event∈(SourceOperationPaidRelations.exposure (sourceActualTrace binding name grade frame)).trace) :
 event∈((sourceBornCurrent binding name factory grade seed frame).inventory.get (by rfl)).trace := by
 apply SourceInventoryExecutionFeed.original_preserved
 change event∈(Stock.preserve frame.inventory
  (Stock.preserve (some (Stock.preserve (factory.nextInventory grade seed frame)
   (SourceOperationPaidRelations.exposure (sourceActualTrace binding name grade frame))))
   (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.generatedStock frame))).trace
 apply preserved_generated
 apply preserved_prior
 exact preserved_generated _ _ _ present

theorem actual_source_pair_trace_in_born (event)
 (present : event∈(SourceOperationPaidRelations.exposure (sourceActualScalarTrace binding name grade frame)).trace) :
 event∈((sourceBornCurrent binding name factory grade seed frame).pairInventory.get (by rfl)).trace := by
 change event∈(Stock.preserve frame.pairInventory
  (Stock.preserve (some (Stock.preserve (factory.nextPairInventory grade seed frame)
   (SourceOperationPaidRelations.exposure (sourceActualScalarTrace binding name grade frame))))
   (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.generatedPairStock frame))).trace
 apply preserved_generated
 apply preserved_prior
 exact preserved_generated _ _ _ present

/-- Every original scalar word stays in the same actual born inventory, including inherited, old raw fields, mean and odd source records. -/
theorem actual_source_old_scalar_in_born (prior)
 (actual : frame.inventory=some prior) (event) (present : event∈prior.trace) :
 event∈((sourceBornCurrent binding name factory grade seed frame).inventory.get (by rfl)).trace := by
 apply SourceInventoryExecutionFeed.original_preserved
 change event∈(Stock.preserve frame.inventory _).trace
 rw [actual]
 exact preserved_prior _ _ _ present

theorem actual_source_old_pair_in_born (prior)
 (actual : frame.pairInventory=some prior) (event) (present : event∈prior.trace) :
 event∈((sourceBornCurrent binding name factory grade seed frame).pairInventory.get (by rfl)).trace := by
 change event∈(Stock.preserve frame.pairInventory _).trace
 rw [actual]
 exact preserved_prior _ _ _ present
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
