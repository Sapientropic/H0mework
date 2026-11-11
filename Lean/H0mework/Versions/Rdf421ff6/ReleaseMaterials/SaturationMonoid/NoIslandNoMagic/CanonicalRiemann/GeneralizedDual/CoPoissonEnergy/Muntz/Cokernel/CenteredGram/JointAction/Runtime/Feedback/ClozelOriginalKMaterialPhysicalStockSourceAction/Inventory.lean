import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Received
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Whole
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace NT
export ActualNativeRelationTransport (bornStock born_stock stockMaterial stock_material_source)
end NT
local instance inventoryGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var) (N : ℕ)

def actualPhysicalBornStock := NT.bornStock (physicalStockSelected factory grade data sourceCfg language N)
  (physicalStockEmitter factory grade data sourceCfg language N)

/-- The actual born stock retains its complete old source and all registered stock/tail/fullProjection/writer Trace inventory. -/
theorem actual_physical_born_inventory :
 (physicalStockBorn factory grade data sourceCfg language N).inventory =
 some (actualPhysicalBornStock factory grade data sourceCfg language N) :=
 NT.born_stock _ _

theorem physical_source_trace_is_in_actual_born (event)
    (present : event ∈ (physicalSourceInventory factory grade data sourceCfg language N
      (physicalStockSelected factory grade data sourceCfg language N)).trace) :
    event ∈ (actualPhysicalBornStock factory grade data sourceCfg language N).trace := by
 unfold actualPhysicalBornStock NT.bornStock
 have source : event ∈ (T.preserve
     ((physicalStockEmitterBase factory grade data sourceCfg language N).nextInventory
       (physicalStockSelected factory grade data sourceCfg language N))
     (physicalSourceInventory factory grade data sourceCfg language N
       (physicalStockSelected factory grade data sourceCfg language N))).trace := by
   cases (physicalStockEmitterBase factory grade data sourceCfg language N).nextInventory
     (physicalStockSelected factory grade data sourceCfg language N) with
   | none => exact present
   | some old => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
 apply SourceInventoryExecutionFeed.original_preserved
 change event ∈ (T.preserve (physicalStockSelected factory grade data sourceCfg language N).inventory
   (T.preserve
    (some (T.preserve
      ((physicalStockEmitterBase factory grade data sourceCfg language N).nextInventory
        (physicalStockSelected factory grade data sourceCfg language N))
      (physicalSourceInventory factory grade data sourceCfg language N
        (physicalStockSelected factory grade data sourceCfg language N))))
    (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.generatedStock
      (physicalStockSelected factory grade data sourceCfg language N)))).trace
 have next : event ∈ (T.preserve
    (some (T.preserve
      ((physicalStockEmitterBase factory grade data sourceCfg language N).nextInventory
        (physicalStockSelected factory grade data sourceCfg language N))
      (physicalSourceInventory factory grade data sourceCfg language N
        (physicalStockSelected factory grade data sourceCfg language N))))
    (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.generatedStock
      (physicalStockSelected factory grade data sourceCfg language N))).trace :=
    (SourceHistoryCommon.parallel_left _ _ _).1 event source
 cases (physicalStockSelected factory grade data sourceCfg language N).inventory with
 | none => exact next
 | some old => exact (SourceHistoryCommon.parallel_right _ _ _).1 event next

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
