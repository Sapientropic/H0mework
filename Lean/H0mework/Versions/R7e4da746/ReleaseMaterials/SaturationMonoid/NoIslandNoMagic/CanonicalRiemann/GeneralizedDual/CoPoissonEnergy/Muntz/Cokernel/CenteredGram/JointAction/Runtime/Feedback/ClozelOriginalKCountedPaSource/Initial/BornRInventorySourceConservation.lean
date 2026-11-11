import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRActualHistoryConsumer
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRInventorySourceConservation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end Shared
end S
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (seed physicalRaw binding binding_value)
end I
namespace Inventory
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
 (supplied_seed_preserved actual_updated_seed updatedSeed)
end Inventory
namespace Res
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
 (liftEvent liftedInventory priorPairInventory pairInventory)
end Res
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (completeWrittenInventory complete_written_preserves disposition queryRaw queryReader)
end J
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
 (mapped_trace)
end Stock
namespace Generic
variable {Sorts:Type} {U X:Sorts→Type} [∀s,AddCommGroup (U s)] {s:Sorts}
variable (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=U) (Var:=X) (sort:=s))
local notation "seed"=>I.seed frame
local notation "point"=>S.Shared.actualOccurrence frame
local notation "event"=>PresentedRelationEventAt.generator frame.registered.input.expression

theorem registered_in_pair_source :
 PresentedRelationEventAt.generator (liftExpr frame.registered.input.expression) ∈
 (Res.pairInventory seed (S.epoch frame) point).trace := by
 have initial:event∈(seed).trace:=RootedAccountedUnfolding.root_mem_trace seed
 have carried:=Inventory.supplied_seed_preserved seed frame event initial
 have updated:event∈(Inventory.updatedSeed seed (S.epoch frame) point).trace:=by
  simpa only [Inventory.actual_updated_seed] using carried
 have lifted:Res.liftEvent event∈(Res.liftedInventory seed (S.epoch frame) point).trace:=by
  rw [Res.liftedInventory,Stock.mapped_trace]
  exact List.mem_map_of_mem updated
 have prior:Res.liftEvent event∈(Res.priorPairInventory seed (S.epoch frame) point).trace:=by
  unfold Res.priorPairInventory
  cases supplied:(S.epoch frame).pairInventory with
  | none=>exact lifted
  | some previous=>
   exact (SourceHistoryCommon.parallel_right _ _ _).1 _ lifted
 exact (SourceHistoryCommon.parallel_left _ _ _).1 _ prior

/-- All four generated query dispositions conserve this actual registered source word. -/
theorem registered_in_query_source :
 PresentedRelationEventAt.generator (liftExpr frame.registered.input.expression) ∈
 (J.completeWrittenInventory seed (S.epoch frame) point).trace :=
 J.complete_written_preserves seed (S.epoch frame) point _ (registered_in_pair_source frame)

theorem physical_query_generated : I.physicalRaw (S.epoch frame) point=
 J.queryRaw seed (S.epoch frame) point (J.disposition seed (S.epoch frame) point) := rfl
end Generic
end CountedPaInitial.BornRInventorySourceConservation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
